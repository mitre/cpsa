(herald "Pre-processing test example: modified NS with two responders")

(comment "CPSA 4.4.2")
(comment "All input read from tst/preprocess.scm")

(defprotocol ns basic
  (defrole init
    (vars (a b name) (n1 n2 n3 text))
    (trace (send (enc n1 a (pubk b))) (recv (enc n1 n2 n3 (pubk a)))
      (send (enc n2 n3 (pubk b))))
    (uniq-orig n1))
  (defrole resp
    (vars (a b name) (n1 n2 n3 text))
    (trace (recv (enc n1 a (pubk b))) (send (enc n1 n2 n3 (pubk a)))
      (recv (enc n2 n3 (pubk b))))
    (uniq-orig n2 n3))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (comment
    "modified Needham-Schroeder with role origination assumptions"))

(defskeleton ns
  (vars (n1 n2 n3 n2p n3p text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (n3 n3) (a a) (b b))
  (defstrand resp 3 (n1 n1) (n2 n2) (n3 n3p) (a a) (b b))
  (defstrand resp 3 (n1 n1) (n2 n2p) (n3 n3) (a a) (b b))
  (non-orig (privk a) (privk b))
  (uniq-orig n1 n2 n3 n2p n3p)
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 n3 (pubk a)))
      (send (enc n2 n3 (pubk b))))
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2 n3p (pubk a)))
      (recv (enc n2 n3p (pubk b))))
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2p n3 (pubk a)))
      (recv (enc n2p n3 (pubk b)))))
  (label 0)
  (unrealized (0 1) (1 0) (1 2) (2 0) (2 2))
  (preskeleton)
  (origs (n3 (2 1)) (n2p (2 1)) (n3p (1 1)) (n2 (1 1)) (n1 (0 0)))
  (comment "Not a skeleton"))

(defskeleton ns
  (vars (n1 n2 n3 n2p n3p text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (n3 n3) (a a) (b b))
  (defstrand resp 3 (n1 n1) (n2 n2) (n3 n3p) (a a) (b b))
  (defstrand resp 3 (n1 n1) (n2 n2p) (n3 n3) (a a) (b b))
  (precedes ((0 0) (1 0)) ((0 0) (2 0)) ((1 1) (0 1)) ((2 1) (0 1)))
  (non-orig (privk a) (privk b))
  (uniq-orig n1 n2 n3 n2p n3p)
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 n3 (pubk a)))
      (send (enc n2 n3 (pubk b))))
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2 n3p (pubk a)))
      (recv (enc n2 n3p (pubk b))))
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2p n3 (pubk a)))
      (recv (enc n2p n3 (pubk b)))))
  (label 1)
  (parent 0)
  (unrealized (0 1) (1 2) (2 2))
  (dead)
  (origs (n3 (2 1)) (n2p (2 1)) (n3p (1 1)) (n2 (1 1)) (n1 (0 0)))
  (comment "empty cohort"))

(defskeleton ns
  (vars (n1 n2 n3p text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (n3 n3p) (a a) (b b))
  (defstrand resp 3 (n1 n1) (n2 n2) (n3 n3p) (a a) (b b))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a) (privk b))
  (uniq-orig n1 n2 n3p)
  (operation collapsed 2 1)
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 n3p (pubk a)))
      (send (enc n2 n3p (pubk b))))
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2 n3p (pubk a)))
      (recv (enc n2 n3p (pubk b)))))
  (label 2)
  (parent 1)
  (unrealized (1 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (n1 n2 n3p text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (n3 n3p) (a a) (b b))
  (defstrand resp 3 (n1 n1) (n2 n2) (n3 n3p) (a a) (b b))
  (precedes ((0 0) (1 0)) ((0 2) (1 2)) ((1 1) (0 1)))
  (non-orig (privk a) (privk b))
  (uniq-orig n1 n2 n3p)
  (operation nonce-test (displaced 2 0 init 3) n2 (1 2)
    (enc n1 n2 n3p (pubk a)))
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 n3p (pubk a)))
      (send (enc n2 n3p (pubk b))))
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2 n3p (pubk a)))
      (recv (enc n2 n3p (pubk b)))))
  (label 3)
  (parent 2)
  (realized)
  (shape)
  (maps
    ((0 1 1) ((a a) (b b) (n1 n1) (n2 n2) (n3 n3p) (n2p n2) (n3p n3p))))
  (origs (n1 (0 0)) (n3p (1 1)) (n2 (1 1))))

(comment "Nothing left to do")
