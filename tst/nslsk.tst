(herald "Needham-Schroeder-Lowe Protocol with symmetric encryption")

(comment "CPSA 2.3.1")
(comment "All input read from nslsk.scm")

(defprotocol nslsk basic
  (defrole init
    (vars (a b name) (n text) (k skey) (t text))
    (trace (send (enc n a (pubk b))) (recv (enc n k b (pubk a)))
      (send (enc t k))))
  (defrole resp
    (vars (b a name) (n text) (k skey) (t text))
    (trace (recv (enc n a (pubk b))) (send (enc n k b (pubk a)))
      (recv (enc t k)))))

(defskeleton nslsk
  (vars (n t text) (a b name) (k skey))
  (defstrand resp 3 (n n) (t t) (b b) (a a) (k k))
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
  (vars (n t n-0 text) (a b a-0 b-0 name) (k skey))
  (defstrand resp 3 (n n) (t t) (b b) (a a) (k k))
  (defstrand init 3 (n n-0) (t t) (a a-0) (b b-0) (k k))
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
  (vars (n t text) (a b name) (k skey))
  (defstrand resp 3 (n n) (t t) (b b) (a a) (k k))
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
  (comment "empty cohort"))

(defskeleton nslsk
  (vars (n t text) (a b name) (k skey))
  (defstrand resp 3 (n n) (t t) (b b) (a a) (k k))
  (defstrand init 3 (n n) (t t) (a a) (b b) (k k))
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
  (unrealized)
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
      (recv (enc t k)))))

(defskeleton nslsk
  (vars (n t text) (b a name) (k skey))
  (defstrand init 3 (n n) (t t) (a a) (b b) (k k))
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
  (vars (n t text) (b a name) (k k-0 skey))
  (defstrand init 3 (n n) (t t) (a a) (b b) (k k))
  (defstrand resp 2 (n n) (b b) (a a) (k k-0))
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
  (unrealized)
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
      (recv (enc "t" k)))))

(defskeleton nslsk-tag-term
  (vars (n text) (a b name) (k skey))
  (defstrand resp 3 (n n) (b b) (a a) (k k))
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
  (vars (n n-0 text) (a b a-0 b-0 name) (k skey))
  (defstrand resp 3 (n n) (b b) (a a) (k k))
  (defstrand init 3 (n n-0) (a a-0) (b b-0) (k k))
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
  (vars (n text) (a b name) (k skey))
  (defstrand resp 3 (n n) (b b) (a a) (k k))
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
  (comment "empty cohort"))

(defskeleton nslsk-tag-term
  (vars (n text) (a b name) (k skey))
  (defstrand resp 3 (n n) (b b) (a a) (k k))
  (defstrand init 3 (n n) (a a) (b b) (k k))
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
  (unrealized)
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
      (recv (enc "t" k)))))

(defskeleton nslsk-tag-term
  (vars (n text) (b a name) (k skey))
  (defstrand init 3 (n n) (a a) (b b) (k k))
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
  (vars (n text) (b a name) (k k-0 skey))
  (defstrand init 3 (n n) (a a) (b b) (k k))
  (defstrand resp 2 (n n) (b b) (a a) (k k-0))
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
  (unrealized)
  (shape)
  (maps ((0) ((b b) (n n) (a a) (k k))))
  (origs (n (0 0))))

(comment "Nothing left to do")
