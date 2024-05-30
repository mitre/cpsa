(herald rule-node)

(comment "CPSA 4.4.3")
(comment "All input read from tst/rule-node.scm")

(defprotocol rule-order basic
  (defrole init
    (vars (s t text))
    (trace (send (cat s t)) (recv (cat t s))))
  (defrule le-lt
    (forall ((z1 z2 strd) (i1 i2 indx))
      (implies
        (fact le z1 i1 z2 i2)
        (or (and (= z1 z2) (= i1 i2)) (fact lt z1 i1 z2 i2)))))
  (defrule lt-le
    (forall ((z1 z2 strd) (i1 i2 indx))
      (implies (fact lt z1 i1 z2 i2) (fact le z1 i1 z2 i2))))
  (defrule prec-lt
    (forall ((z1 z2 strd) (i1 i2 indx))
      (implies (prec z1 i1 z2 i2) (fact lt z1 i1 z2 i2))))
  (defrule neq-false
    (forall ((s mesg)) (implies (fact neq s s) (false))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton rule-order
  (vars (s t text))
  (defstrand init 2 (s s) (t t))
  (defstrand init 2 (s t) (t s))
  (precedes ((1 0) (0 1)))
  (facts (neq s t) (le 0 (idx 0) 0 (idx 1)))
  (traces ((send (cat s t)) (recv (cat t s)))
    ((send (cat t s)) (recv (cat s t))))
  (label 0)
  (realized)
  (origs)
  (comment "Not closed under rules"))

(defskeleton rule-order
  (vars (s t text))
  (defstrand init 2 (s s) (t t))
  (defstrand init 2 (s t) (t s))
  (precedes ((1 0) (0 1)))
  (facts (le 1 (idx 0) 0 (idx 1)) (le 1 (idx 0) 1 (idx 1))
    (lt 1 (idx 0) 1 (idx 1)) (lt 1 (idx 0) 0 (idx 1))
    (lt 0 (idx 0) 0 (idx 1)) (neq s t) (le 0 (idx 0) 0 (idx 1)))
  (rule lt-le prec-lt)
  (traces ((send (cat s t)) (recv (cat t s)))
    ((send (cat t s)) (recv (cat s t))))
  (label 1)
  (parent 0)
  (realized)
  (shape)
  (maps ((0 1) ((s s) (t t))))
  (origs))

(comment "Nothing left to do")

(defprotocol rule-order basic
  (defrole init
    (vars (s t text))
    (trace (send (cat s t)) (recv (cat t s))))
  (defrule le-lt
    (forall ((z1 z2 strd) (i1 i2 indx))
      (implies
        (fact le z1 i1 z2 i2)
        (or (and (= z1 z2) (= i1 i2)) (fact lt z1 i1 z2 i2)))))
  (defrule lt-le
    (forall ((z1 z2 strd) (i1 i2 indx))
      (implies (fact lt z1 i1 z2 i2) (fact le z1 i1 z2 i2))))
  (defrule prec-lt
    (forall ((z1 z2 strd) (i1 i2 indx))
      (implies (prec z1 i1 z2 i2) (fact lt z1 i1 z2 i2))))
  (defrule neq-false
    (forall ((s mesg)) (implies (fact neq s s) (false))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton rule-order
  (vars (s t text))
  (defstrand init 2 (s s) (t t))
  (defstrand init 2 (s t) (t s))
  (precedes ((1 0) (0 1)))
  (facts (le 1 (idx 0) 0 (idx 1)) (le 0 (idx 0) 0 (idx 1)))
  (traces ((send (cat s t)) (recv (cat t s)))
    ((send (cat t s)) (recv (cat s t))))
  (label 2)
  (realized)
  (origs)
  (comment "Not closed under rules"))

(defskeleton rule-order
  (vars (s t text))
  (defstrand init 2 (s s) (t t))
  (defstrand init 2 (s t) (t s))
  (precedes ((1 0) (0 1)))
  (facts (le 1 (idx 0) 1 (idx 1)) (lt 1 (idx 0) 1 (idx 1))
    (lt 1 (idx 0) 0 (idx 1)) (lt 0 (idx 0) 0 (idx 1))
    (le 1 (idx 0) 0 (idx 1)) (le 0 (idx 0) 0 (idx 1)))
  (rule lt-le prec-lt)
  (traces ((send (cat s t)) (recv (cat t s)))
    ((send (cat t s)) (recv (cat s t))))
  (label 3)
  (parent 2)
  (realized)
  (shape)
  (maps ((0 1) ((s s) (t t))))
  (origs))

(defskeleton rule-order
  (vars (s text))
  (defstrand init 2 (s s) (t s))
  (facts (le 0 (idx 0) 0 (idx 1)) (lt 0 (idx 0) 0 (idx 1)))
  (operation collapsed 1 0)
  (strand-map 0 0)
  (traces ((send (cat s s)) (recv (cat s s))))
  (label 4)
  (parent 3)
  (realized)
  (shape)
  (maps)
  (origs))

(comment "Nothing left to do")

(defprotocol rule-order-prec basic
  (defrole init
    (vars (s t text))
    (trace (send (cat s t)) (recv (cat t s))))
  (defrule prec-tell-me
    (forall ((z1 z2 strd) (i1 i2 indx))
      (implies (prec z1 i1 z2 i2) (fact tell-me z1 i1 z2 i2))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton rule-order-prec
  (vars (s t text))
  (defstrand init 2 (s s) (t t))
  (traces ((send (cat s t)) (recv (cat t s))))
  (label 5)
  (realized)
  (origs)
  (comment "Not closed under rules"))

(defskeleton rule-order-prec
  (vars (s t text))
  (defstrand init 2 (s s) (t t))
  (facts (tell-me 0 (idx 0) 0 (idx 1)))
  (rule prec-tell-me)
  (traces ((send (cat s t)) (recv (cat t s))))
  (label 6)
  (parent 5)
  (realized)
  (shape)
  (maps ((0) ((s s) (t t))))
  (origs))

(comment "Nothing left to do")

(defprotocol rule-order-prec basic
  (defrole init
    (vars (s t text))
    (trace (send (cat s t)) (recv (cat t s))))
  (defrule prec-tell-me
    (forall ((z1 z2 strd) (i1 i2 indx))
      (implies (prec z1 i1 z2 i2) (fact tell-me z1 i1 z2 i2))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton rule-order-prec
  (vars (s t text))
  (defstrand init 2 (s s) (t t))
  (defstrand init 2 (s t) (t s))
  (precedes ((1 0) (0 1)))
  (traces ((send (cat s t)) (recv (cat t s)))
    ((send (cat t s)) (recv (cat s t))))
  (label 7)
  (realized)
  (origs)
  (comment "Not closed under rules"))

(defskeleton rule-order-prec
  (vars (s t text))
  (defstrand init 2 (s s) (t t))
  (defstrand init 2 (s t) (t s))
  (precedes ((1 0) (0 1)))
  (facts (tell-me 1 (idx 0) 1 (idx 1)) (tell-me 1 (idx 0) 0 (idx 1))
    (tell-me 0 (idx 0) 0 (idx 1)))
  (rule prec-tell-me)
  (traces ((send (cat s t)) (recv (cat t s)))
    ((send (cat t s)) (recv (cat s t))))
  (label 8)
  (parent 7)
  (realized)
  (shape)
  (maps ((0 1) ((s s) (t t))))
  (origs))

(defskeleton rule-order-prec
  (vars (s text))
  (defstrand init 2 (s s) (t s))
  (facts (tell-me 0 (idx 0) 0 (idx 1)))
  (operation collapsed 1 0)
  (strand-map 0 0)
  (traces ((send (cat s s)) (recv (cat s s))))
  (label 9)
  (parent 8)
  (realized)
  (shape)
  (maps)
  (origs))

(comment "Nothing left to do")

(defprotocol rule-order-prec basic
  (defrole init
    (vars (s t text))
    (trace (send (cat s t)) (recv (cat t s))))
  (defrule prec-tell-me
    (forall ((z1 z2 strd) (i1 i2 indx))
      (implies (prec z1 i1 z2 i2) (fact tell-me z1 i1 z2 i2))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton rule-order-prec
  (vars (s t text))
  (defstrand init 2 (s s) (t t))
  (defstrand init 2 (s s) (t t))
  (precedes ((1 0) (0 1)))
  (traces ((send (cat s t)) (recv (cat t s)))
    ((send (cat s t)) (recv (cat t s))))
  (label 10)
  (realized)
  (origs)
  (comment "Not closed under rules"))

(defskeleton rule-order-prec
  (vars (s t text))
  (defstrand init 2 (s s) (t t))
  (defstrand init 2 (s s) (t t))
  (precedes ((1 0) (0 1)))
  (facts (tell-me 1 (idx 0) 1 (idx 1)) (tell-me 1 (idx 0) 0 (idx 1))
    (tell-me 0 (idx 0) 0 (idx 1)))
  (rule prec-tell-me)
  (traces ((send (cat s t)) (recv (cat t s)))
    ((send (cat s t)) (recv (cat t s))))
  (label 11)
  (parent 10)
  (realized)
  (shape)
  (maps ((0 1) ((s s) (t t))))
  (origs))

(defskeleton rule-order-prec
  (vars (s t text))
  (defstrand init 2 (s s) (t t))
  (facts (tell-me 0 (idx 0) 0 (idx 1)))
  (operation collapsed 1 0)
  (strand-map 0 0)
  (traces ((send (cat s t)) (recv (cat t s))))
  (label 12)
  (parent 11)
  (realized)
  (shape)
  (maps)
  (origs))

(comment "Nothing left to do")
