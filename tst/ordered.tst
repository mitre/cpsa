(herald ordered)

(comment "CPSA 4.3.0")
(comment "All input read from tst/ordered.scm")

(defprotocol ordered basic
  (defrole dec
    (vars (t text) (k akey))
    (trace (recv (enc t k)) (send t)))
  (defrule order
    (forall ((y z strd))
      (implies
        (and (p "dec" y 2) (p "dec" z 2))
        (or (prec y 1 z 0) (prec z 1 y 0) (= y z)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defgenrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2)) (false))))
  (defgenrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defgenrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1)))))
  (defgenrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2))))))

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
  (precedes ((0 1) (1 0)))
  (facts (neq a b))
  (rule order)
  (traces ((recv (enc a k)) (send a)) ((recv (enc b k-0)) (send b)))
  (label 1)
  (parent 0)
  (realized)
  (shape)
  (maps ((0 1) ((a a) (b b) (k k) (k-0 k-0))))
  (origs))

(defskeleton ordered
  (vars (a b text) (k k-0 akey))
  (defstrand dec 2 (t a) (k k))
  (defstrand dec 2 (t b) (k k-0))
  (precedes ((1 1) (0 0)))
  (facts (neq a b))
  (rule order)
  (traces ((recv (enc a k)) (send a)) ((recv (enc b k-0)) (send b)))
  (label 2)
  (parent 0)
  (realized)
  (shape)
  (maps ((0 1) ((a a) (b b) (k k) (k-0 k-0))))
  (origs))

(comment "Nothing left to do")

(defprotocol ordered basic
  (defrole dec
    (vars (t text) (k akey))
    (trace (recv (enc t k)) (send t)))
  (defrule order
    (forall ((y z strd))
      (implies
        (and (p "dec" y 2) (p "dec" z 2))
        (or (prec y 1 z 0) (prec z 1 y 0) (= y z)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defgenrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2)) (false))))
  (defgenrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defgenrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1)))))
  (defgenrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2))))))

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
