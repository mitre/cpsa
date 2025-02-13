(herald uniq-at)

(comment "CPSA 4.4.5")
(comment "All input read from tst/uniq-at.scm")

(defprotocol yahalom-plus-uniq-at basic
  (defrole init
    (vars (a b c name) (n-a n-b text) (k skey))
    (trace (send (cat a n-a)) (recv (enc b k n-a n-b (ltk a c)))
      (send (enc n-b k))))
  (defrole resp
    (vars (b a c name) (n-a n-b text) (rest mesg) (k skey))
    (trace (recv (cat a n-a)) (send (cat b (enc a n-a n-b (ltk b c))))
      (recv (cat (enc a k (ltk b c)) rest)) (send rest)
      (recv (enc n-b k))))
  (defrole serv
    (vars (c a b name) (n-a n-b text) (k skey))
    (trace (recv (cat b (enc a n-a n-b (ltk b c))))
      (send (cat (enc a k (ltk b c)) (enc b k n-a n-b (ltk a c)))))
    (uniq-orig k))
  (defrule uniq-at
    (forall ((z strd) (i indx) (v mesg))
      (implies (uniq-at v z i) (fact remember v z))))
  (defrule ugen-at
    (forall ((z strd) (i indx) (v mesg))
      (implies (ugen-at v z i) (fact remember-gen v z))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton yahalom-plus-uniq-at
  (vars (rest mesg) (k skey) (n-b n-a text) (a b c name))
  (defstrand resp 5 (rest rest) (k k) (n-a n-a) (n-b n-b) (b b) (a a)
    (c c))
  (deflistener k)
  (non-orig (ltk a c) (ltk b c))
  (uniq-orig n-b)
  (traces
    ((recv (cat a n-a)) (send (cat b (enc a n-a n-b (ltk b c))))
      (recv (cat (enc a k (ltk b c)) rest)) (send rest)
      (recv (enc n-b k))) ((recv k) (send k)))
  (label 0)
  (unrealized (0 2) (0 4))
  (origs (n-b (0 1)))
  (comment "Not closed under rules"))

(defskeleton yahalom-plus-uniq-at
  (vars (rest mesg) (k skey) (n-b n-a text) (a b c name))
  (defstrand resp 5 (rest rest) (k k) (n-a n-a) (n-b n-b) (b b) (a a)
    (c c))
  (deflistener k)
  (non-orig (ltk a c) (ltk b c))
  (uniq-orig n-b)
  (facts (remember n-b 0))
  (rule uniq-at)
  (traces
    ((recv (cat a n-a)) (send (cat b (enc a n-a n-b (ltk b c))))
      (recv (cat (enc a k (ltk b c)) rest)) (send rest)
      (recv (enc n-b k))) ((recv k) (send k)))
  (label 1)
  (parent 0)
  (unrealized (0 2) (0 4))
  (origs (n-b (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton yahalom-plus-uniq-at
  (vars (rest mesg) (k skey) (n-b n-a n-a-0 n-b-0 text) (a b c name))
  (defstrand resp 5 (rest rest) (k k) (n-a n-a) (n-b n-b) (b b) (a a)
    (c c))
  (deflistener k)
  (defstrand serv 2 (k k) (n-a n-a-0) (n-b n-b-0) (c c) (a a) (b b))
  (precedes ((2 1) (0 2)) ((2 1) (1 0)))
  (non-orig (ltk a c) (ltk b c))
  (uniq-orig k n-b)
  (facts (remember k 2) (remember n-b 0))
  (rule uniq-at)
  (operation encryption-test (added-strand serv 2) (enc a k (ltk b c))
    (0 2))
  (strand-map 0 1)
  (traces
    ((recv (cat a n-a)) (send (cat b (enc a n-a n-b (ltk b c))))
      (recv (cat (enc a k (ltk b c)) rest)) (send rest)
      (recv (enc n-b k))) ((recv k) (send k))
    ((recv (cat b (enc a n-a-0 n-b-0 (ltk b c))))
      (send (cat (enc a k (ltk b c)) (enc b k n-a-0 n-b-0 (ltk a c))))))
  (label 2)
  (parent 1)
  (unrealized (0 4) (1 0) (2 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton yahalom-plus-uniq-at
  (vars (rest mesg) (k skey) (n-b n-a text) (a b c name))
  (defstrand resp 5 (rest rest) (k k) (n-a n-a) (n-b n-b) (b b) (a a)
    (c c))
  (deflistener k)
  (defstrand serv 2 (k k) (n-a n-a) (n-b n-b) (c c) (a a) (b b))
  (precedes ((0 1) (2 0)) ((2 1) (0 2)) ((2 1) (1 0)))
  (non-orig (ltk a c) (ltk b c))
  (uniq-orig k n-b)
  (facts (remember k 2) (remember n-b 0))
  (operation encryption-test (displaced 3 0 resp 2)
    (enc a n-a-0 n-b-0 (ltk b c)) (2 0))
  (strand-map 0 1 2)
  (traces
    ((recv (cat a n-a)) (send (cat b (enc a n-a n-b (ltk b c))))
      (recv (cat (enc a k (ltk b c)) rest)) (send rest)
      (recv (enc n-b k))) ((recv k) (send k))
    ((recv (cat b (enc a n-a n-b (ltk b c))))
      (send (cat (enc a k (ltk b c)) (enc b k n-a n-b (ltk a c))))))
  (label 3)
  (parent 2)
  (unrealized (0 4) (1 0))
  (dead)
  (comment "empty cohort"))

(defskeleton yahalom-plus-uniq-at
  (vars (rest mesg) (k skey) (n-b n-a n-a-0 n-b-0 text) (a b c name))
  (defstrand resp 5 (rest rest) (k k) (n-a n-a) (n-b n-b) (b b) (a a)
    (c c))
  (deflistener k)
  (defstrand serv 2 (k k) (n-a n-a-0) (n-b n-b-0) (c c) (a a) (b b))
  (defstrand resp 2 (n-a n-a-0) (n-b n-b-0) (b b) (a a) (c c))
  (precedes ((2 1) (0 2)) ((2 1) (1 0)) ((3 1) (2 0)))
  (non-orig (ltk a c) (ltk b c))
  (uniq-orig k n-b)
  (facts (remember k 2) (remember n-b 0))
  (operation encryption-test (added-strand resp 2)
    (enc a n-a-0 n-b-0 (ltk b c)) (2 0))
  (strand-map 0 1 2)
  (traces
    ((recv (cat a n-a)) (send (cat b (enc a n-a n-b (ltk b c))))
      (recv (cat (enc a k (ltk b c)) rest)) (send rest)
      (recv (enc n-b k))) ((recv k) (send k))
    ((recv (cat b (enc a n-a-0 n-b-0 (ltk b c))))
      (send (cat (enc a k (ltk b c)) (enc b k n-a-0 n-b-0 (ltk a c)))))
    ((recv (cat a n-a-0)) (send (cat b (enc a n-a-0 n-b-0 (ltk b c))))))
  (label 4)
  (parent 2)
  (unrealized (0 4) (1 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol yahalom-plus-uniq-at basic
  (defrole init
    (vars (a b c name) (n-a n-b text) (k skey))
    (trace (send (cat a n-a)) (recv (enc b k n-a n-b (ltk a c)))
      (send (enc n-b k))))
  (defrole resp
    (vars (b a c name) (n-a n-b text) (rest mesg) (k skey))
    (trace (recv (cat a n-a)) (send (cat b (enc a n-a n-b (ltk b c))))
      (recv (cat (enc a k (ltk b c)) rest)) (send rest)
      (recv (enc n-b k))))
  (defrole serv
    (vars (c a b name) (n-a n-b text) (k skey))
    (trace (recv (cat b (enc a n-a n-b (ltk b c))))
      (send (cat (enc a k (ltk b c)) (enc b k n-a n-b (ltk a c)))))
    (uniq-orig k))
  (defrule uniq-at
    (forall ((z strd) (i indx) (v mesg))
      (implies (uniq-at v z i) (fact remember v z))))
  (defrule ugen-at
    (forall ((z strd) (i indx) (v mesg))
      (implies (ugen-at v z i) (fact remember-gen v z))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton yahalom-plus-uniq-at
  (vars (k skey) (n-a n-b text) (a b c name))
  (defstrand init 3 (k k) (n-a n-a) (n-b n-b) (a a) (b b) (c c))
  (non-orig (ltk a c) (ltk b c))
  (uniq-orig n-a)
  (traces
    ((send (cat a n-a)) (recv (enc b k n-a n-b (ltk a c)))
      (send (enc n-b k))))
  (label 5)
  (unrealized (0 1))
  (origs (n-a (0 0)))
  (comment "Not closed under rules"))

(defskeleton yahalom-plus-uniq-at
  (vars (k skey) (n-a n-b text) (a b c name))
  (defstrand init 3 (k k) (n-a n-a) (n-b n-b) (a a) (b b) (c c))
  (non-orig (ltk a c) (ltk b c))
  (uniq-orig n-a)
  (facts (remember n-a 0))
  (rule uniq-at)
  (traces
    ((send (cat a n-a)) (recv (enc b k n-a n-b (ltk a c)))
      (send (enc n-b k))))
  (label 6)
  (parent 5)
  (unrealized (0 1))
  (origs (n-a (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton yahalom-plus-uniq-at
  (vars (k skey) (n-a n-b text) (a b c name))
  (defstrand init 3 (k k) (n-a n-a) (n-b n-b) (a a) (b b) (c c))
  (defstrand serv 2 (k k) (n-a n-a) (n-b n-b) (c c) (a a) (b b))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (ltk a c) (ltk b c))
  (uniq-orig k n-a)
  (facts (remember k 1) (remember n-a 0))
  (rule uniq-at)
  (operation encryption-test (added-strand serv 2)
    (enc b k n-a n-b (ltk a c)) (0 1))
  (strand-map 0)
  (traces
    ((send (cat a n-a)) (recv (enc b k n-a n-b (ltk a c)))
      (send (enc n-b k)))
    ((recv (cat b (enc a n-a n-b (ltk b c))))
      (send (cat (enc a k (ltk b c)) (enc b k n-a n-b (ltk a c))))))
  (label 7)
  (parent 6)
  (unrealized (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton yahalom-plus-uniq-at
  (vars (k skey) (n-a n-b text) (a b c name))
  (defstrand init 3 (k k) (n-a n-a) (n-b n-b) (a a) (b b) (c c))
  (defstrand serv 2 (k k) (n-a n-a) (n-b n-b) (c c) (a a) (b b))
  (defstrand resp 2 (n-a n-a) (n-b n-b) (b b) (a a) (c c))
  (precedes ((0 0) (2 0)) ((1 1) (0 1)) ((2 1) (1 0)))
  (non-orig (ltk a c) (ltk b c))
  (uniq-orig k n-a)
  (facts (remember k 1) (remember n-a 0))
  (operation encryption-test (added-strand resp 2)
    (enc a n-a n-b (ltk b c)) (1 0))
  (strand-map 0 1)
  (traces
    ((send (cat a n-a)) (recv (enc b k n-a n-b (ltk a c)))
      (send (enc n-b k)))
    ((recv (cat b (enc a n-a n-b (ltk b c))))
      (send (cat (enc a k (ltk b c)) (enc b k n-a n-b (ltk a c)))))
    ((recv (cat a n-a)) (send (cat b (enc a n-a n-b (ltk b c))))))
  (label 8)
  (parent 7)
  (realized)
  (shape)
  (maps ((0) ((a a) (b b) (c c) (n-a n-a) (n-b n-b) (k k))))
  (origs (k (1 1)) (n-a (0 0))))

(comment "Nothing left to do")
