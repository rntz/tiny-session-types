#lang racket

(require "util.rkt")

;; ---------- GRAMMAR ----------

;; tags N                   are symbols
;; channel variables C, D   are symbols
;; variables X, Y           are symbols
;;
;; expressions E            are racket expressions

;; process expressions are lists of process statements.
;;
;;   P  ::= (S ...)

;; process statements are complicated:
;;  S   ::= (spawn C <- P)          -- spawning a process (cut)
;;          (forward C to D)        -- forwarding a channel (identity)
;;
;;          -- tensor and -o ("lolli") rules for channels
;;          (C <- chan D)           -- sends C to D
;;          (chan D <- C)           -- receives D from C
;;          -- tensor and -o ("lolli") for values
;;          (C <- val E)            -- sending a value
;;          (val X <- C)            -- receiving a value
;;
;;          -- & ("with") and ⊕ ("oplus") rules.
;;          (C <- tag N)            -- sends tag N to C
;;          -- receives a tag on C then dispatches to the matching case
;;          (case C (N => . P) ...)
;;
;;          -- unit rules
;;          (wait C)                -- waits on another channel to close
;;          (close C)               -- closes the channel we own, C
;;
;; NB. A process expression body must be terminated by either (close) or a
;; case-statement. Moreover, case- & close-statements may *only* appear in
;; terminal position. The typechecker enforces this.

;; types are like so (yes, the dot notation means dotted lists!):
;;  A,B ::= (send A . B)                   -- tensor, ⊗
;;          (recv A . B)                   -- lolli,  -o
;;          (send value . A)               -- tensor, ⊗  (but for racket values)
;;          (recv value . A)               -- lolli,  -o (but for racket values)
;;          (recv one of (N => . A) ...)   -- with, &
;;          (send one of (N => . A) ...)   -- sum,  ⊕
;;           -- NB. in with and sum, all tags must be distinct.
;;          ()                             -- unit, 1, meaning "done"
;;
;; for example, the type
;; >    (recv value send value)
;; describes a process which receives a value, then sends one, then is done!

;; how am I gonna typecheck this?
;; bidirectionally. with subtyping for cases.

;; WHAT DO I NEED TO INFER ANYWAY?
;; - which channels we use
;;   easy enough in theory.
;;
;; - what the type of the channel we own is.
;;
;; WHAT DO I NEED TO CHECK?
;; - that we always terminate by closing our own channel
;;
;; - that we wait on all channels we use and haven't given away
;;
;; - that we don't give away channels multiply, or use channels after giving
;;   them away
;;
;; - that (close) & (case ...) appear only in terminal position
;;
;; - that we don't use free variables


;;; ---------- TYPE OPERATIONS & TYPE CHECKING ----------
;;;
;;; You can skip reading this unless you care about type inference details.

(define (type-error-lub a b)
  (error (format "type error: could not unify ~a with ~a" a b)))

;; this is a neat hack, but can produce the confusing error message:
;;  "type error: could not unify FOO with FOO"
(define (type-ok x) (type-lub x x))

;; least upper bound under subtyping. "unions" or "unifies" two types to find
;; the smallest one that includes both.
(define (type-lub a b)
  (match* (a b)
    [('() '()) '()]
    [(`(recv . ,as) `(recv . ,bs)) `(recv . ,(type-lub-rest 'recv as bs))]
    [(`(send . ,as) `(send . ,bs)) `(send . ,(type-lub-rest 'send as bs))]
    [(_ _) (type-error-lub a b)]))

(define (type-lub-rest send-or-recv a b)
  (define (err) (type-error-lub (cons send-or-recv a) (cons send-or-recv b)))
  (match* (a b)
    ;; the interesting case - sorry, this is pretty inscrutable
    [(`(one of (,akeys => ,avals) ...) `(one of (,bkeys => ,bvals) ...))
      (define a-map (for/hash ([k akeys] [v avals]) (values k v)))
      (define b-map (for/hash ([k bkeys] [v bvals]) (values k v)))
      (define keys
        ;; ⊕(x: A) ≤ ⊕(x: A, y: B)
        ;; &(x: A, y: B) ≤ &(x: A)
        ((match send-or-recv ['send set-union] ['recv set-intersect])
          (list->set akeys) (list->set bkeys)))
      `(one of
         ,@(for/list ([k keys])
             (cons k
               ;; if A ≤ B then ⊕(x: A) ≤ ⊕(x: B)
               ;; if A ≤ B then &(x: A) ≤ &(x: B)
               (match* ((hash-ref a-map k #f) (hash-ref b-map k #f))
                 [(#f x) (type-ok x)]
                 [(x #f) (type-ok x)]
                 [(x y) (type-lub x y)]))))]
    [(`(value . ,as) `(value . ,bs)) `(value . ,(type-lub as bs))]
    ;; error cases
    [(`(value . ,_) _) (err)]
    [(_ `(value . ,_)) (err)]
    [(`(one of . ,as) _) (err)]
    [(_ `(one of . ,as)) (err)]
    ;; has to go last b/c it has no keywords
    [((cons a as) (cons b bs))
      ;; check for inappropriate keywords. TODO: better error message here.
      (when (or (member a '(one value)) (member b '(one value))) (err))
      (cons (type-lub a b) (type-lub as bs))]))

;; infers the type of a program in a context
;; (define (synth G c x)
;;   )


;; ---------- STATE STRUCTURES ----------
;; A world-state is a hash from channel IDs to channel info structures.
(struct world-state (channel-map) #:transparent)

;; A channel info structure has three fields:
;;
;; proc: The state-structure for the process owning the channel.
;;
;; readers: List of processes waiting to input on the channel, identified by the
;; channel they own (so that we can look them up in the channel-map).
;;
;; writers: Likewise, a list of processes waiting to output on the channel.
;;
;; It is an error for either `readers' or `writers' to have >1 member; the type
;; system guarantees this will not happen. In other systems this might cause
;; nondeterministic behavior (a "race").
(struct channel-info (proc readers writers) #:transparent)

;; A process state structure has two fields:
;;
;; env: Hash mapping (either regular or channel) variables to their values.
;; expr: The current process expression.
(struct process-state (env expr) #:transparent)
