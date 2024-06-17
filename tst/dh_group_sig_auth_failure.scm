(herald "Signed group DH exchange (version with auth failure)"
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
    (vars (x rndx) (y expt) (alpha expt) (group text)
	  (a b name) (group-dist chan))
    (trace
     (recv group-dist (cat "Group id" group
			   (exp (gen) alpha)))
     (send (enc (exp (exp (gen) alpha) x)
		(privk a)))
     (recv (enc (exp (exp (gen) alpha) y)
		(exp (exp (gen) alpha) x)
		(privk b)))
     (send (enc "final" (exp (exp (gen) alpha) y)
		(exp (exp (gen) alpha) x)
		(privk a))))
    (uniq-gen x)
    (auth group-dist))

  (defrole resp
    (vars (y rndx) (x expt) (alpha expt) (group text)
	  (a b name) (group-dist chan))
    (trace
     (recv group-dist (cat "Group id" group
			   (exp (gen) alpha)))
     (recv (enc (exp (exp (gen) alpha) x)
		(privk a)))
     (send (enc (exp (exp (gen) alpha) y)
		(exp (exp (gen) alpha) x)
		(privk b)))
     (recv (enc "final" (exp (exp (gen) alpha) y)
		(exp (exp (gen) alpha) x)
		(privk a))))
    (uniq-gen y)
    (auth group-dist)))

(defskeleton dh_sig
  (vars (a b name))
  (defstrand init 4 (a a) (b b))
  (non-orig (privk b) (privk a))
)

(defskeleton dh_sig
  (vars (a b name))
  (defstrand resp 4 (a a) (b b))
  (non-orig (privk a) (privk b))
)

