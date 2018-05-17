(herald ordered)

(comment "CPSA 4.1.1")
(comment "All input read from ordered.scm")

(defprotocol ordered basic
  (defrole dec
    (vars (t text) (k akey))
    (trace (recv (enc t k)) (send t)))
  (defrule neq (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defrule order
    (forall ((y z strd))
      (implies (and (p "dec" y 2) (p "dec" z 2))
        (or (prec y 1 z 0) (prec z 1 y 0))))))

(defskeleton ordered
  (vars (a b text) (k k-0 akey))
  (defstrand dec 2 (t a) (k k))
  (defstrand dec 2 (t b) (k k-0))
  (precedes ((0 1) (1 0)))
  (facts (neq a b))
  (traces ((recv (enc a k)) (send a)) ((recv (enc b k-0)) (send b)))
  (label 0)
  (unrealized)
  (origs)
  (comment "Not in theory"))

(comment "Nothing left to do")
