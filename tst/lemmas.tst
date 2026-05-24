(herald goalsvar)

(comment "CPSA 4.4.9")
(comment "All input read from lemmas.scm")

(defprotocol ns basic
  (defrole init
    (vars (a b name) (n1 n2 text))
    (trace (send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b)))))
  (defrole resp
    (vars (b a name) (n2 n1 text))
    (trace (recv (enc n1 a (pubk b))) (send (enc n1 n2 (pubk a)))
      (recv (enc n2 (pubk b)))))
  (defrule lemma1
    (forall ((b name) (n1 text) (z0 strd))
      (implies
        (and (p "init" z0 (idx 3)) (p "init" "n1" z0 n1)
          (p "init" "b" z0 b) (non (privk b)) (uniq n1))
        (exists ((z1 strd))
          (and (p "resp" z1 (idx 2))
            (p "resp" "b" z1 b))))) (comment Lemma not checked)
    (comment "Skeleton 1")
    (comment "Authentication goal: agreement on name b"))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (comment "Needham-Schroeder with no role origination assumptions"))

(defskeleton ns
  (vars (n1 n2 text) (b a name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (non-orig (privk b))
  (uniq-orig n1)
  (goals
    (forall ((b name) (n1 text) (z0 strd))
      (implies
        (and (strand init z0 3 (n1 n1) (b b)) (non (privk b)) (uniq n1))
        (exists ((z1 strd))
          (and (strand resp z1 2 (b b)) (prec z1 1 z0 2))))))
  (comment "Prec example. Skeleton 2" Lemma: lemma2)
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b)))))
  (label 0)
  (unrealized (0 1))
  (maps ((0) ((b b) (n1 n1) (a a) (n2 n2))))
  (origs (n1 (0 0)))
  (comment "Not closed under rules"))

(defskeleton ns
  (vars (n1 n2 n2-0 n1-0 text) (a b a-0 name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (defstrand resp 2 (n2 n2-0) (n1 n1-0) (b b) (a a-0))
  (non-orig (privk b))
  (uniq-orig n1)
  (goals
    (forall ((b name) (n1 text) (z0 strd))
      (implies
        (and (strand init z0 3 (n1 n1) (b b)) (non (privk b)) (uniq n1))
        (exists ((z1 strd))
          (and (strand resp z1 2 (b b)) (prec z1 1 z0 2))))))
  (comment "Prec example. Skeleton 2" Lemma: lemma2)
  (rule lemma1)
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b))))
    ((recv (enc n1-0 a-0 (pubk b))) (send (enc n1-0 n2-0 (pubk a-0)))))
  (label 1)
  (parent 0)
  (unrealized (0 1))
  (maps ((0) ((b b) (n1 n1) (a a) (n2 n2))))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton ns
  (vars (n2 n2-0 n1 text) (b a name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (defstrand resp 2 (n2 n2-0) (n1 n1) (b b) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk b))
  (uniq-orig n1)
  (goals
    (forall ((b name) (n1 text) (z0 strd))
      (implies
        (and (strand init z0 3 (n1 n1) (b b)) (non (privk b)) (uniq n1))
        (exists ((z1 strd))
          (and (strand resp z1 2 (b b)) (prec z1 1 z0 2))))))
  (comment "Prec example. Skeleton 2" Lemma: lemma2)
  (operation nonce-test (displaced 2 1 resp 2) n1-0 (0 1)
    (enc n1-0 a-0 (pubk b)))
  (strand-map 0 1)
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b))))
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2-0 (pubk a)))))
  (label 2)
  (parent 1)
  (realized)
  (shape)
  (satisfies yes)
  (maps ((0) ((b b) (n1 n1) (a a) (n2 n2))))
  (origs (n1 (0 0))))

(defskeleton ns
  (vars (n1 n2 n2-0 n1-0 n2-1 text) (a b a-0 name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (defstrand resp 2 (n2 n2-0) (n1 n1-0) (b b) (a a-0))
  (defstrand resp 2 (n2 n2-1) (n1 n1) (b b) (a a))
  (precedes ((0 0) (2 0)) ((2 1) (0 1)))
  (non-orig (privk b))
  (uniq-orig n1)
  (goals
    (forall ((b name) (n1 text) (z0 strd))
      (implies
        (and (strand init z0 3 (n1 n1) (b b)) (non (privk b)) (uniq n1))
        (exists ((z1 strd))
          (and (strand resp z1 2 (b b)) (prec z1 1 z0 2))))))
  (comment "Prec example. Skeleton 2" Lemma: lemma2)
  (operation nonce-test (added-strand resp 2) n1 (0 1)
    (enc n1 a (pubk b)))
  (strand-map 0 1)
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b))))
    ((recv (enc n1-0 a-0 (pubk b))) (send (enc n1-0 n2-0 (pubk a-0))))
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2-1 (pubk a)))))
  (label 3)
  (parent 1)
  (seen 2)
  (seen-ops
    (2 (operation generalization deleted (1 0)) (strand-map 0 2)))
  (realized)
  (maps ((0) ((b b) (n1 n1) (a a) (n2 n2))))
  (comment "1 in cohort - 0 not yet seen"))

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
  (defrule lemma2
    (forall ((b name) (n1 text) (z0 strd))
      (implies
        (and (p "init" z0 (idx 3)) (p "init" "n1" z0 n1)
          (p "init" "b" z0 b) (non (privk b)) (uniq n1))
        (exists ((z1 strd))
          (and (p "resp" z1 (idx 2)) (p "resp" "b" z1 b)
            (prec z1 (idx 1) z0
              (idx 2)))))) (comment Lemma has associated query)
    (comment "Prec example. Skeleton 2"))
  (defrule lemma1
    (forall ((b name) (n1 text) (z0 strd))
      (implies
        (and (p "init" z0 (idx 3)) (p "init" "n1" z0 n1)
          (p "init" "b" z0 b) (non (privk b)) (uniq n1))
        (exists ((z1 strd))
          (and (p "resp" z1 (idx 2))
            (p "resp" "b" z1 b))))) (comment Lemma not checked)
    (comment "Skeleton 1")
    (comment "Authentication goal: agreement on name b"))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (comment "Needham-Schroeder with no role origination assumptions"))

(defskeleton ns
  (vars (n2 n1 text) (a b name))
  (defstrand resp 3 (n2 n2) (n1 n1) (b b) (a a))
  (non-orig (privk a))
  (uniq-orig n2)
  (goals
    (forall ((a b name) (n2 text) (z0 strd))
      (implies
        (and (strand resp z0 3 (n2 n2) (a a) (b b)) (non (privk a))
          (uniq n2)) (exists ((z1 strd)) (strand init z1 2 (b b))))))
  (comment "Skeleton 3"
    "Failed authentication goal: agreement on name b" Lemma: lemma3)
  (traces
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2 (pubk a)))
      (recv (enc n2 (pubk b)))))
  (label 4)
  (unrealized (0 2))
  (maps ((0) ((a a) (b b) (n2 n2) (n1 n1))))
  (origs (n2 (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (n2 n1 text) (a b b-0 name))
  (defstrand resp 3 (n2 n2) (n1 n1) (b b) (a a))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b-0))
  (precedes ((0 1) (1 1)) ((1 2) (0 2)))
  (non-orig (privk a))
  (uniq-orig n2)
  (goals
    (forall ((a b name) (n2 text) (z0 strd))
      (implies
        (and (strand resp z0 3 (n2 n2) (a a) (b b)) (non (privk a))
          (uniq n2)) (exists ((z1 strd)) (strand init z1 2 (b b))))))
  (comment "Skeleton 3"
    "Failed authentication goal: agreement on name b" Lemma: lemma3)
  (operation nonce-test (added-strand init 3) n2 (0 2)
    (enc n1 n2 (pubk a)))
  (strand-map 0)
  (traces
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2 (pubk a)))
      (recv (enc n2 (pubk b))))
    ((send (enc n1 a (pubk b-0))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b-0)))))
  (label 5)
  (parent 4)
  (realized)
  (shape)
  (satisfies (no (p "init" "b" z1 b) (a a) (b b) (n2 n2) (z0 0)))
  (maps ((0) ((a a) (b b) (n2 n2) (n1 n1))))
  (origs (n2 (0 1))))

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
  (defrule lemma2
    (forall ((b name) (n1 text) (z0 strd))
      (implies
        (and (p "init" z0 (idx 3)) (p "init" "n1" z0 n1)
          (p "init" "b" z0 b) (non (privk b)) (uniq n1))
        (exists ((z1 strd))
          (and (p "resp" z1 (idx 2)) (p "resp" "b" z1 b)
            (prec z1 (idx 1) z0
              (idx 2)))))) (comment Lemma has associated query)
    (comment "Prec example. Skeleton 2"))
  (defrule lemma1
    (forall ((b name) (n1 text) (z0 strd))
      (implies
        (and (p "init" z0 (idx 3)) (p "init" "n1" z0 n1)
          (p "init" "b" z0 b) (non (privk b)) (uniq n1))
        (exists ((z1 strd))
          (and (p "resp" z1 (idx 2))
            (p "resp" "b" z1 b))))) (comment Lemma not checked)
    (comment "Skeleton 1")
    (comment "Authentication goal: agreement on name b"))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (comment "Needham-Schroeder with no role origination assumptions"))

(defskeleton ns
  (vars (n2 n1 text) (a b name))
  (defstrand resp 3 (n2 n2) (n1 n1) (b b) (a a))
  (non-orig (privk a))
  (uniq-orig n2)
  (goals
    (forall ((a b name) (n2 text) (z0 strd))
      (implies
        (and (strand resp z0 3 (n2 n2) (a a) (b b)) (non (privk a))
          (uniq n2)) (exists ((z1 strd)) (strand init z1 2 (b b))))))
  (comment "Skeleton 4")
  (traces
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2 (pubk a)))
      (recv (enc n2 (pubk b)))))
  (label 6)
  (unrealized (0 2))
  (maps ((0) ((a a) (b b) (n2 n2) (n1 n1))))
  (origs (n2 (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (n2 n1 text) (a b b-0 name))
  (defstrand resp 3 (n2 n2) (n1 n1) (b b) (a a))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b-0))
  (precedes ((0 1) (1 1)) ((1 2) (0 2)))
  (non-orig (privk a))
  (uniq-orig n2)
  (goals
    (forall ((a b name) (n2 text) (z0 strd))
      (implies
        (and (strand resp z0 3 (n2 n2) (a a) (b b)) (non (privk a))
          (uniq n2)) (exists ((z1 strd)) (strand init z1 2 (b b))))))
  (comment "Skeleton 4")
  (operation nonce-test (added-strand init 3) n2 (0 2)
    (enc n1 n2 (pubk a)))
  (strand-map 0)
  (traces
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2 (pubk a)))
      (recv (enc n2 (pubk b))))
    ((send (enc n1 a (pubk b-0))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b-0)))))
  (label 7)
  (parent 6)
  (realized)
  (shape)
  (satisfies (no (p "init" "b" z1 b) (a a) (b b) (n2 n2) (z0 0)))
  (maps ((0) ((a a) (b b) (n2 n2) (n1 n1))))
  (origs (n2 (0 1))))

(comment "Nothing left to do")
