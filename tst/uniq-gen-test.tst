(herald "Unique generation test protocols."
  (comment "Skeletons 2, 4, and 7 should have no shapes."))

(comment "CPSA 4.4.5")
(comment "All input read from tst/uniq-gen-test.scm")

(defprotocol uniqgentest basic
  (defrole init
    (vars (a name) (k skey))
    (trace (send (enc a k)) (recv (enc a a k))))
  (defrole doubler (vars (a name) (k skey)) (trace (send (enc a a k))))
  (defrole resp
    (vars (a name) (k skey))
    (trace (recv (enc a k)) (send (enc a a k))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton uniqgentest
  (vars (k skey) (a name))
  (defstrand init 2 (k k) (a a))
  (uniq-gen k)
  (traces ((send (enc a k)) (recv (enc a a k))))
  (label 0)
  (unrealized (0 1))
  (origs)
  (ugens (k (0 0)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton uniqgentest
  (vars (k skey) (a name))
  (defstrand init 2 (k k) (a a))
  (defstrand resp 2 (k k) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (uniq-gen k)
  (operation encryption-test (added-strand resp 2) (enc a a k) (0 1))
  (strand-map 0)
  (traces ((send (enc a k)) (recv (enc a a k)))
    ((recv (enc a k)) (send (enc a a k))))
  (label 1)
  (parent 0)
  (realized)
  (shape)
  (maps ((0) ((k k) (a a))))
  (origs)
  (ugens (k (0 0))))

(defskeleton uniqgentest
  (vars (k skey) (a name))
  (defstrand init 2 (k k) (a a))
  (deflistener k)
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (uniq-gen k)
  (operation encryption-test (added-listener k) (enc a a k) (0 1))
  (strand-map 0)
  (traces ((send (enc a k)) (recv (enc a a k))) ((recv k) (send k)))
  (label 2)
  (parent 0)
  (unrealized (1 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol uniqgentest basic
  (defrole init
    (vars (a name) (k skey))
    (trace (send (enc a k)) (recv (enc a a k))))
  (defrole doubler (vars (a name) (k skey)) (trace (send (enc a a k))))
  (defrole resp
    (vars (a name) (k skey))
    (trace (recv (enc a k)) (send (enc a a k))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton uniqgentest
  (vars (k skey) (a name))
  (defstrand init 2 (k k) (a a))
  (non-orig k)
  (traces ((send (enc a k)) (recv (enc a a k))))
  (label 3)
  (unrealized (0 1))
  (origs)
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton uniqgentest
  (vars (k skey) (a name))
  (defstrand init 2 (k k) (a a))
  (defstrand doubler 1 (k k) (a a))
  (precedes ((1 0) (0 1)))
  (non-orig k)
  (operation encryption-test (added-strand doubler 1) (enc a a k) (0 1))
  (strand-map 0)
  (traces ((send (enc a k)) (recv (enc a a k))) ((send (enc a a k))))
  (label 4)
  (parent 3)
  (realized)
  (shape)
  (maps ((0) ((k k) (a a))))
  (origs))

(defskeleton uniqgentest
  (vars (k skey) (a name))
  (defstrand init 2 (k k) (a a))
  (defstrand resp 2 (k k) (a a))
  (precedes ((1 1) (0 1)))
  (non-orig k)
  (operation encryption-test (added-strand resp 2) (enc a a k) (0 1))
  (strand-map 0)
  (traces ((send (enc a k)) (recv (enc a a k)))
    ((recv (enc a k)) (send (enc a a k))))
  (label 5)
  (parent 3)
  (unrealized (1 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton uniqgentest
  (vars (k skey) (a name))
  (defstrand init 2 (k k) (a a))
  (defstrand resp 2 (k k) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig k)
  (operation encryption-test (displaced 2 0 init 1) (enc a k) (1 0))
  (strand-map 0 1)
  (traces ((send (enc a k)) (recv (enc a a k)))
    ((recv (enc a k)) (send (enc a a k))))
  (label 6)
  (parent 5)
  (realized)
  (shape)
  (maps ((0) ((k k) (a a))))
  (origs))

(defskeleton uniqgentest
  (vars (k skey) (a name))
  (defstrand init 2 (k k) (a a))
  (defstrand resp 2 (k k) (a a))
  (defstrand init 1 (k k) (a a))
  (precedes ((1 1) (0 1)) ((2 0) (1 0)))
  (non-orig k)
  (operation encryption-test (added-strand init 1) (enc a k) (1 0))
  (strand-map 0 1)
  (traces ((send (enc a k)) (recv (enc a a k)))
    ((recv (enc a k)) (send (enc a a k))) ((send (enc a k))))
  (label 7)
  (parent 5)
  (realized)
  (shape)
  (maps ((0) ((k k) (a a))))
  (origs))

(comment "Nothing left to do")
