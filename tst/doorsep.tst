(herald doorsep (comment "Door Simple Example Protocol"))

(comment "CPSA 4.4.0")
(comment "All input read from tst/doorsep.scm")

(defprotocol doorsep basic
  (defrole person
    (vars (d p akey) (k skey) (t text))
    (trace (send (enc (enc k (invk p)) d)) (recv (enc t k)) (send t))
    (uniq-orig k))
  (defrole door
    (vars (d p akey) (k skey) (t text))
    (trace (recv (enc (enc k (invk p)) d)) (send (enc t k)) (recv t))
    (uniq-orig t))
  (defrule trust
    (forall ((z strd) (p d akey))
      (implies
        (and (p "person" z (idx 1)) (p "person" "p" z p)
          (p "person" "d" z d) (non (invk p)))
        (non (invk d))))
    (comment "The trust rule"))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (comment "Doorsep protocol using unnamed asymmetric keys"))

(defskeleton doorsep
  (vars (k skey) (t text) (p d akey))
  (defstrand door 3 (k k) (t t) (d d) (p p))
  (non-orig (invk p))
  (uniq-orig t)
  (comment "Analyze from the doors's perspective")
  (traces ((recv (enc (enc k (invk p)) d)) (send (enc t k)) (recv t)))
  (label 0)
  (unrealized (0 0))
  (origs (t (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton doorsep
  (vars (k skey) (t text) (p d d-0 akey))
  (defstrand door 3 (k k) (t t) (d d) (p p))
  (defstrand person 1 (k k) (d d-0) (p p))
  (precedes ((1 0) (0 0)))
  (non-orig (invk p) (invk d-0))
  (uniq-orig k t)
  (rule trust)
  (operation encryption-test (added-strand person 1) (enc k (invk p))
    (0 0))
  (traces ((recv (enc (enc k (invk p)) d)) (send (enc t k)) (recv t))
    ((send (enc (enc k (invk p)) d-0))))
  (label 1)
  (parent 0)
  (unrealized (0 0) (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton doorsep
  (vars (k skey) (t text) (p d akey))
  (defstrand door 3 (k k) (t t) (d d) (p p))
  (defstrand person 1 (k k) (d d) (p p))
  (precedes ((1 0) (0 0)))
  (non-orig (invk p) (invk d))
  (uniq-orig k t)
  (operation encryption-test (contracted (d-0 d)) (enc k (invk p)) (0 0)
    (enc (enc k (invk p)) d))
  (traces ((recv (enc (enc k (invk p)) d)) (send (enc t k)) (recv t))
    ((send (enc (enc k (invk p)) d))))
  (label 2)
  (parent 1)
  (unrealized (0 2))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton doorsep
  (vars (k skey) (t text) (d p akey))
  (defstrand door 3 (k k) (t t) (d d) (p p))
  (defstrand person 3 (k k) (t t) (d d) (p p))
  (precedes ((0 1) (1 1)) ((1 0) (0 0)) ((1 2) (0 2)))
  (non-orig (invk d) (invk p))
  (uniq-orig k t)
  (operation nonce-test (displaced 1 2 person 3) t (0 2) (enc t k))
  (traces ((recv (enc (enc k (invk p)) d)) (send (enc t k)) (recv t))
    ((send (enc (enc k (invk p)) d)) (recv (enc t k)) (send t)))
  (label 3)
  (parent 2)
  (realized)
  (shape)
  (maps ((0) ((p p) (d d) (k k) (t t))))
  (origs (k (1 0)) (t (0 1))))

(defskeleton doorsep
  (vars (k skey) (t text) (p d akey))
  (defstrand door 3 (k k) (t t) (d d) (p p))
  (defstrand person 1 (k k) (d d) (p p))
  (deflistener k)
  (precedes ((1 0) (0 0)) ((1 0) (2 0)) ((2 1) (0 2)))
  (non-orig (invk p) (invk d))
  (uniq-orig k t)
  (operation nonce-test (added-listener k) t (0 2) (enc t k))
  (traces ((recv (enc (enc k (invk p)) d)) (send (enc t k)) (recv t))
    ((send (enc (enc k (invk p)) d))) ((recv k) (send k)))
  (label 4)
  (parent 2)
  (unrealized (2 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")
