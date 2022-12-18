(herald "Rules and Facts")

(comment "CPSA 4.4.0")
(comment "Coherent logic")

(comment "CPSA 4.4.0")

(comment "All input read from rules.scm")

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
  (comment "Impose an nequality constraint using facts and rules"))

(defgoal neq-test
  (forall ((k skey) (n1 n2 text) (z strd))
    (implies
      (and (p "init" z 2) (p "init" "k" z k) (p "init" "n1" z n1)
        (p "init" "n2" z n2) (non k) (uniq-at n2 z 0) (uniq-at n1 z 0))
      (and (= n2 n1) (p "init" "n2" z n1)))))

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
  (comment "Impose an nequality constraint using facts and rules"))

(defgoal neq-test
  (forall ((k skey) (n1 n2 text) (z strd))
    (implies
      (and (p "init" z 2) (p "init" "k" z k) (p "init" "n1" z n1)
        (p "init" "n2" z n2) (non k) (uniq-at n2 z 0) (uniq-at n1 z 0)
        (fact neq n1 n2))
      (false))))

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

(defgoal doorsep
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
