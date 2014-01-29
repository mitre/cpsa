;;; Target terms experiment
;
;  After a series of other experiments on target terms
; this example arose, and it demonstrated two serious bugs
; in CPSA.
;  First, before this example, CPSA was looking for contractions
; that would completely realize a test node (at least, with respect
; to one critical message).  In this example, the unrealized node
; is the second node of the init strand, and the only critical
; message is the nonce n.  Only if TWO instances of trans were
; available, both with variable m unbound, could we completely
; solve the reception with a single substitution.  However, we can't
; have two instances of trans that are so generic, if we are
; to terminate in circumstances like these (similar to the pruning
; necessary to make Needham-Schroeder terminate).  The fix is to
; make contractions solve only one *position* of the critical
; message at a time.
;  The other problem arose when we added that fix - CPSA was still
; unable to find the shape.  This time, the problem was that pruning
; was overly aggressive: we had an instance of trans in which m had
; been bound, and another version in which m had not.  There was a
; homomorphism and all other conditions were satisfied but the pruning
; was not justified, because the new copy of the trans strand retained
; the freedom to have m map to something not unifiable with the binding
; of m in the other strand.

(defprotocol targetterms6 basic
  (defrole init (vars (a name) (n text) (m mesg))
    (trace
	(send (enc n (pubk a)))
      (recv (cat (enc n (enc n (enc n (pubk a)) (pubk a)) (pubk a))
         (enc n (enc n (pubk a)) (pubk a)) ))
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

(defskeleton targetterms6
  (vars (a name) (n text))
  (defstrand init 2 (a a) (n n))
)

(defskeleton targetterms6
  (vars (n text) (a name))
  (defstrand init 2 (n n) (a a))
  (defstrand trans 3 (m (enc n (pubk a))) (n n) (a a))
  (defstrand trans 3 (m (enc n (enc n (pubk a)) (pubk a))) (n n) (a a))
  (precedes ((0 0) (1 0)) ((0 0) (2 0)) ((1 2) (2 1)) ((2 2) (0 1)))
)
