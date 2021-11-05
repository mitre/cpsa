(herald "Static DH key exchange"
  (algebra diffie-hellman))

(defprotocol staticdh diffie-hellman
  (defrole init
    (vars (b ca name) (h base) (x rndx) (n text))
    (trace
     (recv (enc "cert" h b (privk ca)))
     (send (enc n (exp h x)))
     (recv n))
    (uniq-orig n)
    (non-orig (privk ca) x))
  (defrole resp
    (vars (a ca name) (h base) (y rndx) (n text))
    (trace
     (recv (enc "cert" h a (privk ca)))
     (recv (enc n (exp h y)))
     (send n))
    (non-orig (privk ca) y))
  (defrole ca
    (vars (p ca name) (x rndx))
    (trace
     (send (enc "cert" (exp (gen) x) p (privk ca))))
    (non-orig x)
    (fn-of (owner-of (p x)))))

(comment
(defskeleton staticdh
  (vars)
  (defstrand init 3)))

(defprotocol staticdh1 diffie-hellman
  (defrole init
    (vars (a b ca name) (h base) (x rndx) (n text))
    (trace
     (recv (enc "cert" (exp (gen) x) a (privk ca)))
     (recv (enc "cert" h b (privk ca)))
     (send (enc n (exp h x)))
     (recv n))
    (uniq-orig n)
    (neq (a b))
    (non-orig (privk ca)))
  (defrole resp
    (vars (a b ca name) (h base) (y rndx) (n text))
    (trace
     (recv (enc "cert" h a (privk ca)))
     (recv (enc "cert" (exp (gen) y) b (privk ca)))
     (recv (enc n (exp h y)))
     (send n))
    (neq (a b))
    (non-orig (privk ca)))
  (defrole ca
    (vars (p ca name) (x rndx) (n text))
    (trace
     (send (enc "cert" (exp (gen) x) p (privk ca))))
    (non-orig x)
    (fn-of (owner-of (p x))))
  (defrule init-neq
    (forall ((z strd) (a name))
	    (implies
	     (and (p "init" "a" z a)
		  (p "init" "b" z a))
	     (false))))
  (defrule resp-neq
    (forall ((z strd) (a name))
	    (implies
	     (and (p "resp" "a" z a)
		  (p "resp" "b" z a))
	     (false))))
  (defrule owner-of
    (forall ((z1 z2 strd) (p1 p2 name) (x rndx))
	    (implies
	     (and (p "ca" "x" z1 x)
		  (p "ca" "x" z2 x)
		  (p "ca" "p" z1 p1)
		  (p "ca" "p" z2 p2))
	     (= p1 p2)))))

(defskeleton staticdh1
  (vars)
  (defstrand init 4))
