(herald ordered)

(comment "CPSA 4.4.2")
(comment "All input read from tst/ordered.scm")

(defprotocol ordered basic
  (defrole dec
    (vars (t text) (k akey))
    (trace (recv (enc t k)) (send t)))
  (defrule order
    (forall ((y z strd))
      (implies
        (and (p "dec" y (idx 2)) (p "dec" z (idx 2)))
        (or
          (prec y (idx 1) z (idx 0))
          (prec z (idx 1) y (idx 0))
          (= y z)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton ordered
  (vars (a b text) (k k-0 akey))
  (defstrand dec 2 (t a) (k k))
  (defstrand dec 2 (t b) (k k-0))
  (facts (neq a b))
  (traces ((recv (enc a k)) (send a)) ((recv (enc b k-0)) (send b)))
  (label 0)
  (realized)
  (origs)
  (comment "Not closed under rules"))

(defskeleton ordered
  (vars (a b text) (k k-0 akey))
  (defstrand dec 2 (t a) (k k))
  (defstrand dec 2 (t b) (k k-0))
  (precedes ((1 1) (0 0)))
  (facts (neq a b))
  (rule order)
  (traces ((recv (enc a k)) (send a)) ((recv (enc b k-0)) (send b)))
  (label 1)
  (parent 0)
  (seen 2)
  (realized)
  (origs)
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton ordered
  (vars (a b text) (k k-0 akey))
  (defstrand dec 2 (t a) (k k))
  (defstrand dec 2 (t b) (k k-0))
  (precedes ((0 1) (1 0)))
  (facts (neq a b))
  (rule order)
  (traces ((recv (enc a k)) (send a)) ((recv (enc b k-0)) (send b)))
  (label 2)
  (parent 0)
  (seen 1)
  (realized)
  (origs)
  (comment "1 in cohort - 0 not yet seen"))

(comment "Nothing left to do")

(defprotocol ordered basic
  (defrole dec
    (vars (t text) (k akey))
    (trace (recv (enc t k)) (send t)))
  (defrule order
    (forall ((y z strd))
      (implies
        (and (p "dec" y (idx 2)) (p "dec" z (idx 2)))
        (or
          (prec y (idx 1) z (idx 0))
          (prec z (idx 1) y (idx 0))
          (= y z)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton ordered
  (vars (b text) (k akey))
  (defstrand dec 2 (t b) (k k))
  (facts (neq b b))
  (traces ((recv (enc b k)) (send b)))
  (label 3)
  (realized)
  (origs)
  (comment "Not closed under rules"))

(comment "Nothing left to do")
