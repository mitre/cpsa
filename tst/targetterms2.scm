;;; Target terms experiment
;  The aim of this "experiment" was to try to create an instance
; where we would want to do an augmentation where (1) the critical
; term is to appear in a variable of sort mesg in the transforming
; node and moreover (2) the target term we'd like to use is a
; subterm of what is currently a variable of sort mesg in the
; escape set.
;  This was not wholly successful.  However, targetterms2 did
; illustrate something interesting: a lack of factoring all homomorphisms
; through members of the cohort.  We could have the init2 strand and a
; mostly generic trans strand, and there are two trans strands in the
; shape.  There are two homomorphisms, then, but only one factored through
; what happened next, because the only next step was a contraction that
; effectively fixed our idea of which trans strand we had.

(defprotocol targetterms2 basic
  (defrole init (vars (a name) (n text))
    (trace
	(send (enc n (pubk a)))
      (recv (enc n (enc n (enc n (pubk a)) (pubk a)) (pubk a)))
    )
    (uniq-orig n)
    (non-orig (privk a))
)
  (defrole trans (vars (a name) (n text) (m mesg))
    (trace
     (recv (enc n (pubk a)))
     (recv m)
     (send (enc n m (pubk a)))
    ))
)

(defskeleton targetterms2
  (vars (a name) (n text))
  (defstrand init 2 (a a) (n n))
)
