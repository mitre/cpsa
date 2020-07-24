(herald rule-order)

(comment "CPSA 4.2.3")
(comment "All input read from tst/rule-order.scm")

(defprotocol rule-order basic
  (defrole init (vars (s t text)) (trace (send (cat s t))))
  (defrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2))
        (false))))
  (defrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1)))))
  (defrule ge
    (forall ((x y text))
      (implies (fact le x y) (or (= x y) (fact lt x y))))))

(defskeleton rule-order
  (vars (s t text))
  (defstrand init 1 (s s) (t t))
  (facts (le s t))
  (traces ((send (cat s t))))
  (label 0)
  (unrealized)
  (origs)
  (comment "Not closed under rules"))

(defskeleton rule-order
  (vars (t text))
  (defstrand init 1 (s t) (t t))
  (facts (le t t))
  (rule ge)
  (traces ((send (cat t t))))
  (label 1)
  (parent 0)
  (unrealized)
  (shape)
  (maps ((0) ((s t) (t t))))
  (origs))

(defskeleton rule-order
  (vars (s t text))
  (defstrand init 1 (s s) (t t))
  (facts (lt s t) (le s t))
  (rule ge)
  (traces ((send (cat s t))))
  (label 2)
  (parent 0)
  (unrealized)
  (shape)
  (maps ((0) ((s s) (t t))))
  (origs))

(comment "Nothing left to do")
