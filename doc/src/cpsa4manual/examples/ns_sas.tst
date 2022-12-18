(herald "Needham-Schroeder Public-Key Protocol"
  (comment "This protocol contains a man-in-the-middle"
    "attack discovered by Galvin Lowe."))

(comment "CPSA 4.4.0")
(comment "All input read from ns_sas.scm")

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
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (comment "Needham-Schroeder"))

(defskeleton ns
  (vars (n1 n2 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (non-orig (privk a) (privk b))
  (uniq-orig n1)
  (goals
    (forall ((n1 n2 text) (a b name) (z strd))
      (implies
        (and (p "init" z 3) (p "init" "n1" z n1) (p "init" "n2" z n2)
          (p "init" "a" z a) (p "init" "b" z b) (non (privk a))
          (non (privk b)) (uniq-at n1 z 0))
        (exists ((z-0 strd))
          (and (p "resp" z-0 2) (p "resp" "n2" z-0 n2)
            (p "resp" "n1" z-0 n1) (p "resp" "b" z-0 b)
            (p "resp" "a" z-0 a) (prec z 0 z-0 0) (prec z-0 1 z 1))))))
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b)))))
  (label 0)
  (unrealized (0 1))
  (origs (n1 (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (n1 n2 n2-0 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (defstrand resp 2 (n2 n2-0) (n1 n1) (b b) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a) (privk b))
  (uniq-orig n1)
  (operation nonce-test (added-strand resp 2) n1 (0 1)
    (enc n1 a (pubk b)))
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b))))
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2-0 (pubk a)))))
  (label 1)
  (parent 0)
  (unrealized (0 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (n1 n2 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (defstrand resp 2 (n2 n2) (n1 n1) (b b) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a) (privk b))
  (uniq-orig n1)
  (operation nonce-test (contracted (n2-0 n2)) n1 (0 1)
    (enc n1 n2 (pubk a)) (enc n1 a (pubk b)))
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b))))
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2 (pubk a)))))
  (label 2)
  (parent 1)
  (realized)
  (shape)
  (satisfies yes)
  (maps ((0) ((n1 n1) (n2 n2) (a a) (b b))))
  (origs (n1 (0 0))))

(comment "Nothing left to do")

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
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (comment "Needham-Schroeder"))

(defskeleton ns
  (vars (n2 n1 text) (a b name))
  (defstrand resp 3 (n2 n2) (n1 n1) (b b) (a a))
  (non-orig (privk a) (privk b))
  (uniq-orig n2)
  (goals
    (forall ((n2 n1 text) (a b name) (z strd))
      (implies
        (and (p "resp" z 3) (p "resp" "n2" z n2) (p "resp" "n1" z n1)
          (p "resp" "b" z b) (p "resp" "a" z a) (non (privk a))
          (non (privk b)) (uniq-at n2 z 1))
        (exists ((b-0 name) (z-0 strd))
          (and (p "init" z-0 3) (p "init" "n1" z-0 n1)
            (p "init" "n2" z-0 n2) (p "init" "a" z-0 a)
            (p "init" "b" z-0 b-0) (prec z 1 z-0 1)
            (prec z-0 2 z 2))))))
  (traces
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2 (pubk a)))
      (recv (enc n2 (pubk b)))))
  (label 3)
  (unrealized (0 2))
  (origs (n2 (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (n2 n1 text) (a b b-0 name))
  (defstrand resp 3 (n2 n2) (n1 n1) (b b) (a a))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b-0))
  (precedes ((0 1) (1 1)) ((1 2) (0 2)))
  (non-orig (privk a) (privk b))
  (uniq-orig n2)
  (operation nonce-test (added-strand init 3) n2 (0 2)
    (enc n1 n2 (pubk a)))
  (traces
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2 (pubk a)))
      (recv (enc n2 (pubk b))))
    ((send (enc n1 a (pubk b-0))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b-0)))))
  (label 4)
  (parent 3)
  (realized)
  (shape)
  (satisfies yes)
  (maps ((0) ((n2 n2) (n1 n1) (a a) (b b))))
  (origs (n2 (0 1))))

(comment "Nothing left to do")
