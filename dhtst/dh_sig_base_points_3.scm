(herald "Signed group DH exchange 3"
	(algebra diffie-hellman)
	(limit 200)
	(bound 25))

(defprotocol dh_sig2 diffie-hellman
  (defrole group-init
    (vars (alpha rndx) (k-magic skey) (group text))
    (trace
     (send (enc "Group id" group (exp (gen) alpha) k-magic)))
    (uniq-gen alpha))
  (defrole init
    (vars (x rndx) (y expt) (g base) (k-magic skey) (n group text) (a b name))
    (trace
     (recv (enc "Group id" group g k-magic))
     (send (enc a b group (exp g x) (privk a)))
     (recv (enc a b group (exp g y) (exp g x) (privk b)))
     (send (enc n (exp g (mul x y))))
     (recv n))    
    (non-orig k-magic)
    (uniq-gen x n))
  (defrole resp
    (vars (y rndx) (x expt) (g base) (k-magic skey) (n group text) (a b name))
    (trace
     (recv (enc "Group id" group g k-magic))
     (recv (enc a b group (exp g x) (privk a)))
     (send (enc a b group (exp g y) (exp g x) (privk b))) 
     (recv (enc n (exp g (mul x y))))
     (send n))
    (non-orig k-magic)
    (uniq-gen y))
)


(defskeleton dh_sig2
  (vars (a b name))
  (defstrand init 5 (a a) (b b))
  (non-orig (privk b) (privk a))
)

(defskeleton dh_sig2
  (vars (a b name))
  (defstrand resp 5 (a a) (b b))
  (non-orig (privk a) (privk b))
)

