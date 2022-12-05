(herald "Needham-Schroeder-Low Public-Key Protocol"
  (comment "With deflistener's"))

(comment "CPSA 4.4.0")
(comment "All input read from tst/ns-l.scm")

(defprotocol ns basic
  (defrole init
    (vars (a b name) (n1 n2 text))
    (trace (send (enc n1 a (pubk b))) (recv (enc b n1 n2 (pubk a)))
      (send (enc n2 (pubk b)))))
  (defrole resp
    (vars (b a name) (n2 n1 text))
    (trace (recv (enc n1 a (pubk b))) (send (enc b n1 n2 (pubk a)))
      (recv (enc n2 (pubk b)))))
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
  (deflistener n1)
  (non-orig (privk a) (privk b))
  (uniq-orig n1)
  (comment "Initiator point-of-view with a listener")
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc b n1 n2 (pubk a)))
      (send (enc n2 (pubk b)))) ((recv n1) (send n1)))
  (label 0)
  (unrealized (0 1) (1 0))
  (preskeleton)
  (origs (n1 (0 0)))
  (comment "Not a skeleton"))

(defskeleton ns
  (vars (n1 n2 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (deflistener n1)
  (precedes ((0 0) (1 0)))
  (non-orig (privk a) (privk b))
  (uniq-orig n1)
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc b n1 n2 (pubk a)))
      (send (enc n2 (pubk b)))) ((recv n1) (send n1)))
  (label 1)
  (parent 0)
  (unrealized (0 1) (1 0))
  (origs (n1 (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (n1 n2 n2-0 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (deflistener n1)
  (defstrand resp 2 (n2 n2-0) (n1 n1) (b b) (a a))
  (precedes ((0 0) (2 0)) ((2 1) (1 0)))
  (non-orig (privk a) (privk b))
  (uniq-orig n1)
  (operation nonce-test (added-strand resp 2) n1 (1 0)
    (enc n1 a (pubk b)))
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc b n1 n2 (pubk a)))
      (send (enc n2 (pubk b)))) ((recv n1) (send n1))
    ((recv (enc n1 a (pubk b))) (send (enc b n1 n2-0 (pubk a)))))
  (label 2)
  (parent 1)
  (unrealized (0 1) (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (n2 text) (a b name))
  (defstrand init 3 (n1 n2) (n2 n2) (a a) (b b))
  (deflistener n2)
  (defstrand resp 2 (n2 n2) (n1 n2) (b b) (a a))
  (precedes ((0 0) (2 0)) ((0 2) (1 0)) ((2 1) (1 0)))
  (non-orig (privk a) (privk b))
  (uniq-orig n2)
  (operation nonce-test (displaced 3 0 init 3) n2-0 (1 0)
    (enc n2-0 a (pubk b)) (enc b n2-0 n2-0 (pubk a)))
  (traces
    ((send (enc n2 a (pubk b))) (recv (enc b n2 n2 (pubk a)))
      (send (enc n2 (pubk b)))) ((recv n2) (send n2))
    ((recv (enc n2 a (pubk b))) (send (enc b n2 n2 (pubk a)))))
  (label 3)
  (parent 2)
  (unrealized (0 1) (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (n2 n2-0 text) (a b name))
  (defstrand init 3 (n1 n2) (n2 n2) (a a) (b b))
  (deflistener n2)
  (defstrand resp 2 (n2 n2) (n1 n2) (b b) (a a))
  (defstrand resp 2 (n2 n2-0) (n1 n2) (b b) (a a))
  (precedes ((0 0) (2 0)) ((0 0) (3 0)) ((0 2) (1 0)) ((2 1) (1 0))
    ((3 1) (1 0)))
  (non-orig (privk a) (privk b))
  (uniq-orig n2)
  (operation nonce-test (added-strand resp 2) n2 (1 0) (enc n2 (pubk b))
    (enc n2 a (pubk b)) (enc b n2 n2 (pubk a)))
  (traces
    ((send (enc n2 a (pubk b))) (recv (enc b n2 n2 (pubk a)))
      (send (enc n2 (pubk b)))) ((recv n2) (send n2))
    ((recv (enc n2 a (pubk b))) (send (enc b n2 n2 (pubk a))))
    ((recv (enc n2 a (pubk b))) (send (enc b n2 n2-0 (pubk a)))))
  (label 4)
  (parent 3)
  (unrealized (0 1) (1 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol ns basic
  (defrole init
    (vars (a b name) (n1 n2 text))
    (trace (send (enc n1 a (pubk b))) (recv (enc b n1 n2 (pubk a)))
      (send (enc n2 (pubk b)))))
  (defrole resp
    (vars (b a name) (n2 n1 text))
    (trace (recv (enc n1 a (pubk b))) (send (enc b n1 n2 (pubk a)))
      (recv (enc n2 (pubk b)))))
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
  (deflistener n2)
  (non-orig (privk a))
  (uniq-orig n2)
  (comment "Responder point-of-view with a listener")
  (traces
    ((recv (enc n1 a (pubk b))) (send (enc b n1 n2 (pubk a)))
      (recv (enc n2 (pubk b)))) ((recv n2) (send n2)))
  (label 5)
  (unrealized (0 2) (1 0))
  (preskeleton)
  (origs (n2 (0 1)))
  (comment "Not a skeleton"))

(defskeleton ns
  (vars (n2 n1 text) (a b name))
  (defstrand resp 3 (n2 n2) (n1 n1) (b b) (a a))
  (deflistener n2)
  (precedes ((0 1) (1 0)))
  (non-orig (privk a))
  (uniq-orig n2)
  (traces
    ((recv (enc n1 a (pubk b))) (send (enc b n1 n2 (pubk a)))
      (recv (enc n2 (pubk b)))) ((recv n2) (send n2)))
  (label 6)
  (parent 5)
  (unrealized (0 2) (1 0))
  (origs (n2 (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (n2 n1 text) (a b name))
  (defstrand resp 3 (n2 n2) (n1 n1) (b b) (a a))
  (deflistener n2)
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (precedes ((0 1) (2 1)) ((2 2) (1 0)))
  (non-orig (privk a))
  (uniq-orig n2)
  (operation nonce-test (added-strand init 3) n2 (1 0)
    (enc b n1 n2 (pubk a)))
  (traces
    ((recv (enc n1 a (pubk b))) (send (enc b n1 n2 (pubk a)))
      (recv (enc n2 (pubk b)))) ((recv n2) (send n2))
    ((send (enc n1 a (pubk b))) (recv (enc b n1 n2 (pubk a)))
      (send (enc n2 (pubk b)))))
  (label 7)
  (parent 6)
  (unrealized (0 2))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton ns
  (vars (n2 n1 text) (a b name))
  (defstrand resp 3 (n2 n2) (n1 n1) (b b) (a a))
  (deflistener n2)
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (precedes ((0 1) (2 1)) ((2 2) (0 2)) ((2 2) (1 0)))
  (non-orig (privk a))
  (uniq-orig n2)
  (operation nonce-test (displaced 3 2 init 3) n2 (0 2)
    (enc b n1 n2 (pubk a)))
  (traces
    ((recv (enc n1 a (pubk b))) (send (enc b n1 n2 (pubk a)))
      (recv (enc n2 (pubk b)))) ((recv n2) (send n2))
    ((send (enc n1 a (pubk b))) (recv (enc b n1 n2 (pubk a)))
      (send (enc n2 (pubk b)))))
  (label 8)
  (parent 7)
  (realized)
  (shape)
  (maps ((0 1) ((a a) (n2 n2) (b b) (n1 n1))))
  (origs (n2 (0 1))))

(defskeleton ns
  (vars (n2 n1 text) (a b name))
  (defstrand resp 3 (n2 n2) (n1 n1) (b b) (a a))
  (deflistener n2)
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (precedes ((0 1) (2 1)) ((0 1) (3 1)) ((2 2) (1 0)) ((3 2) (0 2)))
  (non-orig (privk a))
  (uniq-orig n2)
  (operation nonce-test (added-strand init 3) n2 (0 2)
    (enc b n1 n2 (pubk a)))
  (traces
    ((recv (enc n1 a (pubk b))) (send (enc b n1 n2 (pubk a)))
      (recv (enc n2 (pubk b)))) ((recv n2) (send n2))
    ((send (enc n1 a (pubk b))) (recv (enc b n1 n2 (pubk a)))
      (send (enc n2 (pubk b))))
    ((send (enc n1 a (pubk b))) (recv (enc b n1 n2 (pubk a)))
      (send (enc n2 (pubk b)))))
  (label 9)
  (parent 7)
  (realized)
  (shape)
  (maps ((0 1) ((a a) (n2 n2) (b b) (n1 n1))))
  (origs (n2 (0 1))))

(comment "Nothing left to do")
