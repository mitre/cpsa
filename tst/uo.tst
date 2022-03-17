(comment "CPSA 4.3.1")
(comment "All input read from tst/uo.scm")

(defprotocol uniq-orig basic
  (defrole init (vars (n text)) (trace (send n)) (uniq-orig n))
  (defrole resp (vars (m n text)) (trace (send (enc m n)) (recv n)))
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

(defskeleton uniq-orig
  (vars (n m text))
  (defstrand init 1 (n n))
  (defstrand resp 2 (m m) (n n))
  (uniq-orig n)
  (traces ((send n)) ((send (enc m n)) (recv n)))
  (label 0)
  (unrealized (1 1))
  (preskeleton)
  (origs (n (0 0)))
  (comment "Not a skeleton"))

(defskeleton uniq-orig
  (vars (n m text))
  (defstrand init 1 (n n))
  (defstrand resp 2 (m m) (n n))
  (precedes ((0 0) (1 1)))
  (uniq-orig n)
  (traces ((send n)) ((send (enc m n)) (recv n)))
  (label 1)
  (parent 0)
  (realized)
  (shape)
  (maps ((0 1) ((n n) (m m))))
  (origs (n (0 0))))

(comment "Nothing left to do")
