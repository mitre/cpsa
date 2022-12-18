(herald "Needham-Schroeder Public-Key Protocol"
  (comment "This protocol contains a man-in-the-middle"
    "attack discovered by Galvin Lowe."))

(comment "CPSA 4.4.0")
(comment "Coherent logic")

(comment "CPSA 4.4.0")

(comment "All input read from ns.scm")

(defprotocol ns basic
  (defrole init
    (vars (a b name) (n1 n2 text))
    (trace (send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b)))))
  (defrole resp
    (vars (b a name) (n2 n1 text))
    (trace (recv (enc n1 a (pubk b))) (send (enc n1 n2 (pubk a)))
      (recv (enc n2 (pubk b)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (comment "Needham-Schroeder"))

(defgoal ns
  (forall ((n1 n2 text) (a b name) (z strd))
    (implies
      (and (p "init" z 3) (p "init" "n1" z n1) (p "init" "n2" z n2)
        (p "init" "a" z a) (p "init" "b" z b) (non (privk a))
        (non (privk b)) (uniq-at n1 z 0))
      (exists ((z-0 strd))
        (and (p "resp" z-0 2) (p "resp" "n2" z-0 n2)
          (p "resp" "n1" z-0 n1) (p "resp" "b" z-0 b)
          (p "resp" "a" z-0 a) (prec z 0 z-0 0) (prec z-0 1 z 1))))))

(defprotocol ns basic
  (defrole init
    (vars (a b name) (n1 n2 text))
    (trace (send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b)))))
  (defrole resp
    (vars (b a name) (n2 n1 text))
    (trace (recv (enc n1 a (pubk b))) (send (enc n1 n2 (pubk a)))
      (recv (enc n2 (pubk b)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (comment "Needham-Schroeder"))

(defgoal ns
  (forall ((n2 n1 text) (a b name) (z strd))
    (implies
      (and (p "resp" z 3) (p "resp" "n2" z n2) (p "resp" "n1" z n1)
        (p "resp" "b" z b) (p "resp" "a" z a) (non (privk a))
        (non (privk b)) (uniq-at n2 z 1))
      (exists ((b-0 name) (z-0 strd))
        (and (p "init" z-0 3) (p "init" "n1" z-0 n1)
          (p "init" "n2" z-0 n2) (p "init" "a" z-0 a)
          (p "init" "b" z-0 b-0) (prec z 1 z-0 1) (prec z-0 2 z 2))))))
