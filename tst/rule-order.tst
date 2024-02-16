(herald rule-order)

(comment "CPSA 4.4.3")
(comment "All input read from tst/rule-order.scm")

(defprotocol rule-order basic
  (defrole init (vars (s t text)) (trace (send (cat s t))))
  (defrule ge
    (forall ((x y text))
      (implies (fact le x y) (or (= x y) (fact lt x y)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton rule-order
  (vars (s t text))
  (defstrand init 1 (s s) (t t))
  (facts (le s t))
  (traces ((send (cat s t))))
  (label 0)
  (realized)
  (origs)
  (ugens)
  (comment "Not closed under rules"))

(defskeleton rule-order
  (vars (t text))
  (defstrand init 1 (s t) (t t))
  (facts (le t t))
  (rule ge)
  (traces ((send (cat t t))))
  (label 1)
  (parent 0)
  (realized)
  (shape)
  (maps ((0) ((s t) (t t))))
  (origs)
  (ugens))

(defskeleton rule-order
  (vars (s t text))
  (defstrand init 1 (s s) (t t))
  (facts (lt s t) (le s t))
  (rule ge)
  (traces ((send (cat s t))))
  (label 2)
  (parent 0)
  (seen 1)
  (seen-opts (1))
  (realized)
  (origs)
  (ugens)
  (comment "1 in cohort - 0 not yet seen"))

(comment "Nothing left to do")
