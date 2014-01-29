; pruning1
;   Demonstrates a flaw in CPSA due to overly aggressive pruning.
; Specifically, the shape requires two instances of trans, one
; with k = pubk b and the other with k = privk b.  CPSA would
; form one of these instances and then refuse to augment with another
; because the new one would prune.  This pruning was overly aggressive
; because leaving k unbound gives the new strand greater freedom.
;   This flaw was discovered previously in targetterms6, but
; this example illustrates that the flaw does not depend on variables
; of sort mesg; here it is done with a variable of sort akey.

(defprotocol prune basic
  (defrole init (vars (a b name) (n text))
    (trace
	(send (enc n (pubk a)))
      (recv (enc n (pubk b) (pubk a)))
      (recv (enc n (privk b) (pubk a)))
	)
    (uniq-orig n)
    (non-orig (privk a))
  )
  (defrole trans (vars (a name) (n text) (k akey))
     (trace
        (recv (enc n (pubk a)))
	(recv k )
        (send (enc n k (pubk a)))
     )
  )
  (comment "Shows a failure with generalization"
	   "Run this with a step count of 4"))

(defskeleton prune
  (vars (a name) (n text) (k akey))
  (defstrand init 3))

(defskeleton prune
  (vars (n text) (a b name))
  (defstrand init 3 (n n) (a a) (b b))
  (defstrand trans 3 (n n) (a a) (k (pubk b)))
  (defstrand trans 3 (n n) (a a) (k (privk b)))
  (precedes ((0 0) (1 0)) ((0 0) (2 0)) ((1 2) (0 1)) ((2 2) (0 2)))
)
