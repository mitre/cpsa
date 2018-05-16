(herald doorsep (comment "Door Simple Example Protocol"))

(comment "CPSA 4.1.1")
(comment "All input read from doorsep.scm")

(defprotocol doorsep basic
  (defrole person
    (vars (d p akey) (k skey) (t text))
    (trace (send (enc (enc k (invk p)) d)) (recv (enc t k)) (send t)))
  (defrole door
    (vars (d p akey) (k skey) (t text))
    (trace (recv (enc (enc k (invk p)) d)) (send (enc t k)) (recv t)))
  (defrule trust
    (forall ((z strd) (p d akey))
      (implies
        (and (p "person" z 1) (p "person" "p" z p) (p "person" "d" z d)
          (non (invk p))) (non (invk d)))) (comment "The trust rule"))
  (comment "Doorsep protocol using unnamed asymmetric keys"))

(defskeleton doorsep
  (vars (t text) (k skey) (p d akey))
  (defstrand door 3 (t t) (k k) (d d) (p p))
  (non-orig (invk p))
  (comment "Analyze from the doors's perspective")
  (traces ((recv (enc (enc k (invk p)) d)) (send (enc t k)) (recv t)))
  (label 0)
  (unrealized (0 0))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton doorsep
  (vars (t text) (k skey) (p d d-0 akey))
  (defstrand door 3 (t t) (k k) (d d) (p p))
  (defstrand person 1 (k k) (d d-0) (p p))
  (precedes ((1 0) (0 0)))
  (non-orig (invk p) (invk d-0))
  (rule trust)
  (operation encryption-test (added-strand person 1) (enc k (invk p))
    (0 0))
  (traces ((recv (enc (enc k (invk p)) d)) (send (enc t k)) (recv t))
    ((send (enc (enc k (invk p)) d-0))))
  (label 1)
  (parent 0)
  (unrealized (0 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton doorsep
  (vars (t text) (k skey) (p d akey))
  (defstrand door 3 (t t) (k k) (d d) (p p))
  (defstrand person 1 (k k) (d d) (p p))
  (precedes ((1 0) (0 0)))
  (non-orig (invk p) (invk d))
  (operation encryption-test (contracted (d-0 d)) (enc k (invk p)) (0 0)
    (enc (enc k (invk p)) d))
  (traces ((recv (enc (enc k (invk p)) d)) (send (enc t k)) (recv t))
    ((send (enc (enc k (invk p)) d))))
  (label 2)
  (parent 1)
  (unrealized)
  (shape)
  (maps ((0) ((p p) (d d) (k k) (t t))))
  (origs))

(comment "Nothing left to do")
