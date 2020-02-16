(herald "Inequality constraint using facts and rules"
  (comment "First skeleton should have a shape,"
    "second should be dead."))

(comment "CPSA 4.2.3")
(comment "All input read from tst/neq_test.scm")

(defprotocol neq-test basic
  (defrole init
    (vars (n1 n2 text) (k skey))
    (trace (send (cat n1 (enc n1 n2 k))) (recv n2))
    (non-orig k)
    (uniq-orig n1 n2))
  (defrule neq (forall ((a mesg)) (implies (fact neq a a) (false)))))

(defskeleton neq-test
  (vars (n1 n2 text) (k skey))
  (defstrand init 2 (n1 n1) (n2 n2) (k k))
  (non-orig k)
  (uniq-orig n1 n2)
  (traces ((send (cat n1 (enc n1 n2 k))) (recv n2)))
  (label 0)
  (unrealized (0 1))
  (origs (n2 (0 0)) (n1 (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton neq-test
  (vars (n1 text) (k skey))
  (defstrand init 2 (n1 n1) (n2 n1) (k k))
  (non-orig k)
  (uniq-orig n1)
  (operation nonce-test (displaced 1 0 init 1) n2 (0 1) (enc n1 n2 k))
  (traces ((send (cat n1 (enc n1 n1 k))) (recv n1)))
  (label 1)
  (parent 0)
  (unrealized)
  (shape)
  (maps ((0) ((n1 n1) (n2 n1) (k k))))
  (origs (n1 (0 0))))

(comment "Nothing left to do")

(defprotocol neq-test basic
  (defrole init
    (vars (n1 n2 text) (k skey))
    (trace (send (cat n1 (enc n1 n2 k))) (recv n2))
    (non-orig k)
    (uniq-orig n1 n2))
  (defrule neq (forall ((a mesg)) (implies (fact neq a a) (false)))))

(defskeleton neq-test
  (vars (n1 n2 text) (k skey))
  (defstrand init 2 (n1 n1) (n2 n2) (k k))
  (non-orig k)
  (uniq-orig n1 n2)
  (facts (neq n1 n2))
  (traces ((send (cat n1 (enc n1 n2 k))) (recv n2)))
  (label 2)
  (unrealized (0 1))
  (dead)
  (origs (n2 (0 0)) (n1 (0 0)))
  (comment "empty cohort"))

(comment "Nothing left to do")
