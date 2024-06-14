(herald "Signed group DH exchange (improved version)"
	(algebra diffie-hellman)
	(limit 100))



(defprotocol dh_sig diffie-hellman
  (defrole group-init
    (vars (alpha rndx) (group text) (group-dist chan))
    (trace
     (send group-dist (cat "Group id" group
			   (exp (gen) alpha))))
    (uniq-gen alpha)
    (conf group-dist))
  
  (defrole init
    (vars (x rndx) (y expt) (alpha expt) (group na nb text)
	  (a b name) (group-dist chan))
    (trace
     (recv group-dist (cat "Group id" group
			   (exp (gen) alpha)))
     (send (enc (exp (exp (gen) alpha) x)
		(privk a)))
     (recv (enc a (exp (exp (gen) alpha) y)
		(exp (exp (gen) alpha) x)
		(privk b)))
     (send (enc "final" b na
		(exp (exp (gen) alpha) y)
		(exp (exp (gen) alpha) x)
		(privk a)))
     (recv (enc na nb
		(exp (exp (exp (gen) alpha) y)
		     x)))
     (send nb))
    (uniq-gen na x)
    (auth group-dist))

  (defrole resp
    (vars (y rndx) (x expt) (alpha expt) (group na nb text)
	  (a b name) (group-dist chan))
    (trace
     (recv group-dist (cat "Group id" group
			   (exp (gen) alpha)))
     (recv (enc (exp (exp (gen) alpha) x)
		(privk a)))
     (send (enc a (exp (exp (gen) alpha) y)
		(exp (exp (gen) alpha) x)
		(privk b)))
     (recv (enc "final" b na
		(exp (exp (gen) alpha) y)
		(exp (exp (gen) alpha) x)
		(privk a)))
     (send (enc na nb
		(exp (exp (exp (gen) alpha) x)
		     y)))
     (recv nb))
    (uniq-gen nb y)
    (auth group-dist)))

(defskeleton dh_sig
  (vars (a b name))
  (defstrand init 6 (a a) (b b))
  (non-orig (privk b) (privk a)))

(defskeleton dh_sig
  (vars (a b name))
  (defstrand resp 6 (a a) (b b))
  (non-orig (privk a) (privk b)))


