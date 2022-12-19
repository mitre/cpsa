(herald "Needham-Schroeder-Lowe Protocol with symmetric encryption")

(comment "CPSA 4.4.1")
(comment "All input read from tst/nslsk.scm")

(defprotocol nslsk basic
  (defrole init
    (vars (a b name) (n text) (k skey) (t text))
    (trace (send (enc n a (pubk b))) (recv (enc n k b (pubk a)))
      (send (enc t k))))
  (defrole resp
    (vars (b a name) (n text) (k skey) (t text))
    (trace (recv (enc n a (pubk b))) (send (enc n k b (pubk a)))
      (recv (enc t k))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton nslsk
  (vars (k skey) (n t text) (a b name))
  (defstrand resp 3 (k k) (n n) (t t) (b b) (a a))
  (non-orig (privk a))
  (uniq-orig k)
  (traces
    ((recv (enc n a (pubk b))) (send (enc n k b (pubk a)))
      (recv (enc t k))))
  (label 0)
  (unrealized (0 2))
  (origs (k (0 1)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton nslsk
  (vars (k skey) (n t n-0 text) (a b a-0 b-0 name))
  (defstrand resp 3 (k k) (n n) (t t) (b b) (a a))
  (defstrand init 3 (k k) (n n-0) (t t) (a a-0) (b b-0))
  (precedes ((0 1) (1 1)) ((1 2) (0 2)))
  (non-orig (privk a))
  (uniq-orig k)
  (operation encryption-test (added-strand init 3) (enc t k) (0 2))
  (traces
    ((recv (enc n a (pubk b))) (send (enc n k b (pubk a)))
      (recv (enc t k)))
    ((send (enc n-0 a-0 (pubk b-0))) (recv (enc n-0 k b-0 (pubk a-0)))
      (send (enc t k))))
  (label 1)
  (parent 0)
  (unrealized (1 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton nslsk
  (vars (k skey) (n t text) (a b name))
  (defstrand resp 3 (k k) (n n) (t t) (b b) (a a))
  (deflistener k)
  (precedes ((0 1) (1 0)) ((1 1) (0 2)))
  (non-orig (privk a))
  (uniq-orig k)
  (operation encryption-test (added-listener k) (enc t k) (0 2))
  (traces
    ((recv (enc n a (pubk b))) (send (enc n k b (pubk a)))
      (recv (enc t k))) ((recv k) (send k)))
  (label 2)
  (parent 0)
  (unrealized (1 0))
  (dead)
  (comment "empty cohort"))

(defskeleton nslsk
  (vars (k skey) (n t text) (a b name))
  (defstrand resp 3 (k k) (n n) (t t) (b b) (a a))
  (defstrand init 3 (k k) (n n) (t t) (a a) (b b))
  (precedes ((0 1) (1 1)) ((1 2) (0 2)))
  (non-orig (privk a))
  (uniq-orig k)
  (operation nonce-test (contracted (a-0 a) (b-0 b) (n-0 n)) k (1 1)
    (enc n k b (pubk a)))
  (traces
    ((recv (enc n a (pubk b))) (send (enc n k b (pubk a)))
      (recv (enc t k)))
    ((send (enc n a (pubk b))) (recv (enc n k b (pubk a)))
      (send (enc t k))))
  (label 3)
  (parent 1)
  (realized)
  (shape)
  (maps ((0) ((a a) (k k) (b b) (n n) (t t))))
  (origs (k (0 1))))

(comment "Nothing left to do")

(defprotocol nslsk basic
  (defrole init
    (vars (a b name) (n text) (k skey) (t text))
    (trace (send (enc n a (pubk b))) (recv (enc n k b (pubk a)))
      (send (enc t k))))
  (defrole resp
    (vars (b a name) (n text) (k skey) (t text))
    (trace (recv (enc n a (pubk b))) (send (enc n k b (pubk a)))
      (recv (enc t k))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton nslsk
  (vars (k skey) (n t text) (b a name))
  (defstrand init 3 (k k) (n n) (t t) (a a) (b b))
  (non-orig (privk b))
  (uniq-orig n)
  (traces
    ((send (enc n a (pubk b))) (recv (enc n k b (pubk a)))
      (send (enc t k))))
  (label 4)
  (unrealized (0 1))
  (origs (n (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton nslsk
  (vars (k k-0 skey) (n t text) (b a name))
  (defstrand init 3 (k k) (n n) (t t) (a a) (b b))
  (defstrand resp 2 (k k-0) (n n) (b b) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk b))
  (uniq-orig n)
  (operation nonce-test (added-strand resp 2) n (0 1)
    (enc n a (pubk b)))
  (traces
    ((send (enc n a (pubk b))) (recv (enc n k b (pubk a)))
      (send (enc t k)))
    ((recv (enc n a (pubk b))) (send (enc n k-0 b (pubk a)))))
  (label 5)
  (parent 4)
  (realized)
  (shape)
  (maps ((0) ((b b) (n n) (a a) (k k) (t t))))
  (origs (n (0 0))))

(comment "Nothing left to do")

(defprotocol nslsk-tag-term basic
  (defrole init
    (vars (a b name) (n text) (k skey))
    (trace (send (enc n a (pubk b))) (recv (enc n k b (pubk a)))
      (send (enc "t" k))))
  (defrole resp
    (vars (b a name) (n text) (k skey))
    (trace (recv (enc n a (pubk b))) (send (enc n k b (pubk a)))
      (recv (enc "t" k))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton nslsk-tag-term
  (vars (k skey) (n text) (a b name))
  (defstrand resp 3 (k k) (n n) (b b) (a a))
  (non-orig (privk a))
  (uniq-orig k)
  (traces
    ((recv (enc n a (pubk b))) (send (enc n k b (pubk a)))
      (recv (enc "t" k))))
  (label 6)
  (unrealized (0 2))
  (origs (k (0 1)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton nslsk-tag-term
  (vars (k skey) (n n-0 text) (a b a-0 b-0 name))
  (defstrand resp 3 (k k) (n n) (b b) (a a))
  (defstrand init 3 (k k) (n n-0) (a a-0) (b b-0))
  (precedes ((0 1) (1 1)) ((1 2) (0 2)))
  (non-orig (privk a))
  (uniq-orig k)
  (operation encryption-test (added-strand init 3) (enc "t" k) (0 2))
  (traces
    ((recv (enc n a (pubk b))) (send (enc n k b (pubk a)))
      (recv (enc "t" k)))
    ((send (enc n-0 a-0 (pubk b-0))) (recv (enc n-0 k b-0 (pubk a-0)))
      (send (enc "t" k))))
  (label 7)
  (parent 6)
  (unrealized (1 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton nslsk-tag-term
  (vars (k skey) (n text) (a b name))
  (defstrand resp 3 (k k) (n n) (b b) (a a))
  (deflistener k)
  (precedes ((0 1) (1 0)) ((1 1) (0 2)))
  (non-orig (privk a))
  (uniq-orig k)
  (operation encryption-test (added-listener k) (enc "t" k) (0 2))
  (traces
    ((recv (enc n a (pubk b))) (send (enc n k b (pubk a)))
      (recv (enc "t" k))) ((recv k) (send k)))
  (label 8)
  (parent 6)
  (unrealized (1 0))
  (dead)
  (comment "empty cohort"))

(defskeleton nslsk-tag-term
  (vars (k skey) (n text) (a b name))
  (defstrand resp 3 (k k) (n n) (b b) (a a))
  (defstrand init 3 (k k) (n n) (a a) (b b))
  (precedes ((0 1) (1 1)) ((1 2) (0 2)))
  (non-orig (privk a))
  (uniq-orig k)
  (operation nonce-test (contracted (a-0 a) (b-0 b) (n-0 n)) k (1 1)
    (enc n k b (pubk a)))
  (traces
    ((recv (enc n a (pubk b))) (send (enc n k b (pubk a)))
      (recv (enc "t" k)))
    ((send (enc n a (pubk b))) (recv (enc n k b (pubk a)))
      (send (enc "t" k))))
  (label 9)
  (parent 7)
  (realized)
  (shape)
  (maps ((0) ((a a) (k k) (b b) (n n))))
  (origs (k (0 1))))

(comment "Nothing left to do")

(defprotocol nslsk-tag-term basic
  (defrole init
    (vars (a b name) (n text) (k skey))
    (trace (send (enc n a (pubk b))) (recv (enc n k b (pubk a)))
      (send (enc "t" k))))
  (defrole resp
    (vars (b a name) (n text) (k skey))
    (trace (recv (enc n a (pubk b))) (send (enc n k b (pubk a)))
      (recv (enc "t" k))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton nslsk-tag-term
  (vars (k skey) (n text) (b a name))
  (defstrand init 3 (k k) (n n) (a a) (b b))
  (non-orig (privk b))
  (uniq-orig n)
  (traces
    ((send (enc n a (pubk b))) (recv (enc n k b (pubk a)))
      (send (enc "t" k))))
  (label 10)
  (unrealized (0 1))
  (origs (n (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton nslsk-tag-term
  (vars (k k-0 skey) (n text) (b a name))
  (defstrand init 3 (k k) (n n) (a a) (b b))
  (defstrand resp 2 (k k-0) (n n) (b b) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk b))
  (uniq-orig n)
  (operation nonce-test (added-strand resp 2) n (0 1)
    (enc n a (pubk b)))
  (traces
    ((send (enc n a (pubk b))) (recv (enc n k b (pubk a)))
      (send (enc "t" k)))
    ((recv (enc n a (pubk b))) (send (enc n k-0 b (pubk a)))))
  (label 11)
  (parent 10)
  (realized)
  (shape)
  (maps ((0) ((b b) (n n) (a a) (k k))))
  (origs (n (0 0))))

(comment "Nothing left to do")
