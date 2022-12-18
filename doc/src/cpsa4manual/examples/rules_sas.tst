(herald "Rules and Facts")

(comment "CPSA 4.4.0")
(comment "All input read from rules_sas.scm")

(defprotocol neq-test basic
  (defrole init
    (vars (n1 n2 text) (k skey))
    (trace (send (cat n1 (enc n1 n2 k))) (recv n2))
    (non-orig k)
    (uniq-orig n1 n2))
  (defrule neq (forall ((a mesg)) (implies (fact neq a a) (false))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (comment "Impose an nequality constraint using facts and rules"))

(defskeleton neq-test
  (vars (k skey) (n1 n2 text))
  (defstrand init 2 (k k) (n1 n1) (n2 n2))
  (non-orig k)
  (uniq-orig n1 n2)
  (goals
    (forall ((k skey) (n1 n2 text) (z strd))
      (implies
        (and (p "init" z 2) (p "init" "k" z k) (p "init" "n1" z n1)
          (p "init" "n2" z n2) (non k) (uniq-at n2 z 0)
          (uniq-at n1 z 0)) (and (= n2 n1) (p "init" "n2" z n1)))))
  (traces ((send (cat n1 (enc n1 n2 k))) (recv n2)))
  (label 0)
  (unrealized (0 1))
  (origs (n2 (0 0)) (n1 (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton neq-test
  (vars (k skey) (n1 text))
  (defstrand init 2 (k k) (n1 n1) (n2 n1))
  (non-orig k)
  (uniq-orig n1)
  (operation nonce-test (displaced 1 0 init 1) n2 (0 1) (enc n1 n2 k))
  (traces ((send (cat n1 (enc n1 n1 k))) (recv n1)))
  (label 1)
  (parent 0)
  (realized)
  (shape)
  (satisfies yes)
  (maps ((0) ((k k) (n1 n1) (n2 n1))))
  (origs (n1 (0 0))))

(comment "Nothing left to do")

(defprotocol neq-test basic
  (defrole init
    (vars (n1 n2 text) (k skey))
    (trace (send (cat n1 (enc n1 n2 k))) (recv n2))
    (non-orig k)
    (uniq-orig n1 n2))
  (defrule neq (forall ((a mesg)) (implies (fact neq a a) (false))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (comment "Impose an nequality constraint using facts and rules"))

(defskeleton neq-test
  (vars (k skey) (n1 n2 text))
  (defstrand init 2 (k k) (n1 n1) (n2 n2))
  (non-orig k)
  (uniq-orig n1 n2)
  (facts (neq n1 n2))
  (goals
    (forall ((k skey) (n1 n2 text) (z strd))
      (implies
        (and (p "init" z 2) (p "init" "k" z k) (p "init" "n1" z n1)
          (p "init" "n2" z n2) (non k) (uniq-at n2 z 0) (uniq-at n1 z 0)
          (fact neq n1 n2)) (false))))
  (traces ((send (cat n1 (enc n1 n2 k))) (recv n2)))
  (label 2)
  (unrealized (0 1))
  (dead)
  (origs (n2 (0 0)) (n1 (0 0)))
  (comment "empty cohort"))

(comment "Nothing left to do")

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
  (goals
    (forall ((k skey) (t text) (p d akey) (z strd))
      (implies
        (and (p "door" z 3) (p "door" "k" z k) (p "door" "t" z t)
          (p "door" "d" z d) (p "door" "p" z p) (non (invk p))
          (uniq-at t z 1))
        (exists ((z-0 strd))
          (and (p "person" z-0 3) (p "person" "k" z-0 k)
            (p "person" "t" z-0 t) (p "person" "d" z-0 d)
            (p "person" "p" z-0 p) (prec z 1 z-0 1) (prec z-0 0 z 0)
            (prec z-0 2 z 2) (non (invk d)) (uniq-at k z-0 0))))))
  (traces ((recv (enc (enc k (invk p)) d)) (send (enc t k)) (recv t)))
  (label 3)
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
  (label 4)
  (parent 3)
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
  (label 5)
  (parent 4)
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
  (label 6)
  (parent 5)
  (realized)
  (shape)
  (satisfies yes)
  (maps ((0) ((k k) (t t) (p p) (d d))))
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
  (label 7)
  (parent 5)
  (unrealized (2 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")
