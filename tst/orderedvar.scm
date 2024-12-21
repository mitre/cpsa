(herald ordered)

(defprotocol ordered basic

  (defrole dec
    (vars (t text) (k akey))
    (trace (recv (enc t k)) (send t)))

;;     (defrule neq
;;       (forall ((x mesg))
;;   	    (implies (fact neq x x) (false))))

  (defrule order
    (forall ((y z strd))
	    (implies
	     (and (strand dec y 2)
		  (strand dec z 2))
	     (or (prec y 1 z 0)
		 (prec z 1 y 0)
		 (= y z))))))

(defskeleton ordered
  (vars (a b text))
  (defstrand dec 2 (t a))
  (defstrand dec 2 (t b))
  (facts (neq a b)))

(defskeleton ordered
  (vars (b text) (k akey))
  (defstrand dec 2 (t b) (k k))
  (facts (neq b b))
  (rule order)
  (traces ((recv (enc b k)) (send b)))
  (label 3)
  (parent 0)
  (unrealized)
  (shape)
  (maps ((0 0) ((a b) (b b) (k k) (k-0 k))))
  (origs))
