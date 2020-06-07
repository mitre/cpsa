(herald rule-node)

(comment "CPSA 4.2.3")
(comment "All input read from tst/rule-node.scm")

(defprotocol rule-order basic
  (defrole init
    (vars (s t text))
    (trace (send (cat s t)) (recv (cat t s))))
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
  (defrule neq-false
    (forall ((s mesg)) (implies (fact neq s s) (false))))
  (defrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defrule prec-lt
    (forall ((z1 z2 strd) (i1 i2 indx))
      (implies (prec z1 i1 z2 i2) (fact lt z1 i1 z2 i2))))
  (defrule lt-le
    (forall ((z1 z2 strd) (i1 i2 indx))
      (implies (fact lt z1 i1 z2 i2) (fact le z1 i1 z2 i2))))
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
  (defrule le-lt
    (forall ((z1 z2 strd) (i1 i2 indx))
      (implies
        (fact le z1 i1 z2 i2)
        (or (and (= z1 z2) (= i1 i2)) (fact lt z1 i1 z2 i2))))))

(defskeleton rule-order
  (vars (s t text))
  (defstrand init 2 (s s) (t t))
  (defstrand init 2 (s t) (t s))
  (precedes ((1 0) (0 1)))
  (facts (neq s t) (le 0 0 0 1))
  (traces ((send (cat s t)) (recv (cat t s)))
    ((send (cat t s)) (recv (cat s t))))
  (label 0)
  (unrealized)
  (origs)
  (comment "Not closed under rules"))

(defskeleton rule-order
  (vars (s t text))
  (defstrand init 2 (s s) (t t))
  (defstrand init 2 (s t) (t s))
  (precedes ((1 0) (0 1)))
  (facts (lt 0 0 0 1) (le 0 0 0 1) (le 1 0 0 1) (le 1 0 1 1)
    (lt 1 0 1 1) (lt 1 0 0 1) (lt 0 0 0 1) (neq s t) (le 0 0 0 1))
  (rule le-lt lt-le prec-lt)
  (traces ((send (cat s t)) (recv (cat t s)))
    ((send (cat t s)) (recv (cat s t))))
  (label 1)
  (parent 0)
  (unrealized)
  (shape)
  (maps ((0 1) ((s s) (t t))))
  (origs))

(comment "Nothing left to do")

(defprotocol rule-order basic
  (defrole init
    (vars (s t text))
    (trace (send (cat s t)) (recv (cat t s))))
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
  (defrule neq-false
    (forall ((s mesg)) (implies (fact neq s s) (false))))
  (defrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defrule prec-lt
    (forall ((z1 z2 strd) (i1 i2 indx))
      (implies (prec z1 i1 z2 i2) (fact lt z1 i1 z2 i2))))
  (defrule lt-le
    (forall ((z1 z2 strd) (i1 i2 indx))
      (implies (fact lt z1 i1 z2 i2) (fact le z1 i1 z2 i2))))
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
  (defrule le-lt
    (forall ((z1 z2 strd) (i1 i2 indx))
      (implies
        (fact le z1 i1 z2 i2)
        (or (and (= z1 z2) (= i1 i2)) (fact lt z1 i1 z2 i2))))))

(defskeleton rule-order
  (vars (s t text))
  (defstrand init 2 (s s) (t t))
  (defstrand init 2 (s t) (t s))
  (precedes ((1 0) (0 1)))
  (facts (le 1 0 0 1) (le 0 0 0 1))
  (traces ((send (cat s t)) (recv (cat t s)))
    ((send (cat t s)) (recv (cat s t))))
  (label 2)
  (unrealized)
  (origs)
  (comment "Not closed under rules"))

(defskeleton rule-order
  (vars (s t text))
  (defstrand init 2 (s s) (t t))
  (defstrand init 2 (s t) (t s))
  (precedes ((1 0) (0 1)))
  (facts (lt 1 0 0 1) (lt 0 0 0 1) (le 0 0 0 1) (le 1 0 0 1)
    (le 1 0 1 1) (lt 1 0 1 1) (lt 1 0 0 1) (lt 0 0 0 1) (le 1 0 0 1)
    (le 0 0 0 1))
  (rule le-lt lt-le prec-lt)
  (traces ((send (cat s t)) (recv (cat t s)))
    ((send (cat t s)) (recv (cat s t))))
  (label 3)
  (parent 2)
  (unrealized)
  (shape)
  (maps ((0 1) ((s s) (t t))))
  (origs))

(defskeleton rule-order
  (vars (s text))
  (defstrand init 2 (s s) (t s))
  (facts (lt 0 0 0 1) (le 0 0 0 1) (lt 0 0 0 1) (le 0 0 0 0))
  (rule le-lt lt-le prec-lt)
  (traces ((send (cat s s)) (recv (cat s s))))
  (label 4)
  (parent 2)
  (unrealized)
  (shape)
  (maps)
  (origs))

(defskeleton rule-order
  (vars (s text))
  (defstrand init 2 (s s) (t s))
  (facts (le 0 0 0 1) (lt 0 0 0 1) (le 0 0 0 0))
  (rule le-lt lt-le prec-lt)
  (traces ((send (cat s s)) (recv (cat s s))))
  (label 5)
  (parent 2)
  (unrealized)
  (shape)
  (maps)
  (origs))

(comment "Nothing left to do")

(defprotocol rule-order-prec basic
  (defrole init
    (vars (s t text))
    (trace (send (cat s t)) (recv (cat t s))))
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
  (defrule prec-tell-me
    (forall ((z1 z2 strd) (i1 i2 indx))
      (implies (prec z1 i1 z2 i2) (fact tell-me z1 i1 z2 i2))))
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
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1))))))

(defskeleton rule-order-prec
  (vars (s t text))
  (defstrand init 2 (s s) (t t))
  (traces ((send (cat s t)) (recv (cat t s))))
  (label 6)
  (unrealized)
  (origs)
  (comment "Not closed under rules"))

(defskeleton rule-order-prec
  (vars (s t text))
  (defstrand init 2 (s s) (t t))
  (facts (tell-me 0 0 0 1))
  (rule prec-tell-me)
  (traces ((send (cat s t)) (recv (cat t s))))
  (label 7)
  (parent 6)
  (unrealized)
  (shape)
  (maps ((0) ((s s) (t t))))
  (origs))

(comment "Nothing left to do")

(defprotocol rule-order-prec basic
  (defrole init
    (vars (s t text))
    (trace (send (cat s t)) (recv (cat t s))))
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
  (defrule prec-tell-me
    (forall ((z1 z2 strd) (i1 i2 indx))
      (implies (prec z1 i1 z2 i2) (fact tell-me z1 i1 z2 i2))))
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
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1))))))

(defskeleton rule-order-prec
  (vars (s t text))
  (defstrand init 2 (s s) (t t))
  (defstrand init 2 (s t) (t s))
  (precedes ((1 0) (0 1)))
  (traces ((send (cat s t)) (recv (cat t s)))
    ((send (cat t s)) (recv (cat s t))))
  (label 8)
  (unrealized)
  (origs)
  (comment "Not closed under rules"))

(defskeleton rule-order-prec
  (vars (s t text))
  (defstrand init 2 (s s) (t t))
  (defstrand init 2 (s t) (t s))
  (precedes ((1 0) (0 1)))
  (facts (tell-me 1 0 1 1) (tell-me 1 0 0 1) (tell-me 0 0 0 1))
  (rule prec-tell-me)
  (traces ((send (cat s t)) (recv (cat t s)))
    ((send (cat t s)) (recv (cat s t))))
  (label 9)
  (parent 8)
  (unrealized)
  (shape)
  (maps ((0 1) ((s s) (t t))))
  (origs))

(defskeleton rule-order-prec
  (vars (s text))
  (defstrand init 2 (s s) (t s))
  (facts (tell-me 0 0 0 1))
  (operation collapsed 1 0)
  (traces ((send (cat s s)) (recv (cat s s))))
  (label 10)
  (parent 9)
  (unrealized)
  (shape)
  (maps)
  (origs))

(comment "Nothing left to do")

(defprotocol rule-order-prec basic
  (defrole init
    (vars (s t text))
    (trace (send (cat s t)) (recv (cat t s))))
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
  (defrule prec-tell-me
    (forall ((z1 z2 strd) (i1 i2 indx))
      (implies (prec z1 i1 z2 i2) (fact tell-me z1 i1 z2 i2))))
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
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1))))))

(defskeleton rule-order-prec
  (vars (s t text))
  (defstrand init 2 (s s) (t t))
  (defstrand init 2 (s s) (t t))
  (precedes ((1 0) (0 1)))
  (traces ((send (cat s t)) (recv (cat t s)))
    ((send (cat s t)) (recv (cat t s))))
  (label 11)
  (unrealized)
  (origs)
  (comment "Not closed under rules"))

(defskeleton rule-order-prec
  (vars (s t text))
  (defstrand init 2 (s s) (t t))
  (defstrand init 2 (s s) (t t))
  (precedes ((1 0) (0 1)))
  (facts (tell-me 1 0 1 1) (tell-me 1 0 0 1) (tell-me 0 0 0 1))
  (rule prec-tell-me)
  (traces ((send (cat s t)) (recv (cat t s)))
    ((send (cat s t)) (recv (cat t s))))
  (label 12)
  (parent 11)
  (unrealized)
  (shape)
  (maps ((0 1) ((s s) (t t))))
  (origs))

(defskeleton rule-order-prec
  (vars (s t text))
  (defstrand init 2 (s s) (t t))
  (facts (tell-me 0 0 0 1))
  (operation collapsed 1 0)
  (traces ((send (cat s t)) (recv (cat t s))))
  (label 13)
  (parent 12)
  (unrealized)
  (shape)
  (maps)
  (origs))

(comment "Nothing left to do")
