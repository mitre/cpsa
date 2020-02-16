(herald "Three Party Needham-Schroeder-Lowe Protocol")

(comment "CPSA 4.2.3")
(comment "All input read from tst/nsl3.scm")

(defprotocol nsl3 basic
  (defrole init
    (vars (a b c name) (na0 na1 nb0 nb1 nc0 nc1 text))
    (trace (send (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    (uniq-orig na0 na1))
  (defrole mid
    (vars (a b c name) (na0 na1 nb0 nb1 nc0 nc1 text))
    (trace (recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
          (pubk c)))
      (recv
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))) (send (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    (uniq-orig nb0 nb1))
  (defrole resp
    (vars (a b c name) (na0 na1 nb0 nb1 nc0 nc1 text))
    (trace
      (recv
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
          (pubk c)))
      (send
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    (uniq-orig nc0 nc1)))

(defskeleton nsl3
  (vars (na0 na1 nb0 nb1 nc0 nc1 text) (a b c name))
  (defstrand init 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig na0 na1)
  (traces
    ((send (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b)))))
  (label 0)
  (unrealized (0 1))
  (origs (na1 (0 0)) (na0 (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton nsl3
  (vars (na0 na1 nb0 nb1 nc0 nc1 nb0-0 nb1-0 text) (a b c name))
  (defstrand init 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na0) (na1 na1) (nb0 nb0-0) (nb1 nb1-0) (a a)
    (b b) (c c))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig na0 na1 nb0-0 nb1-0)
  (operation nonce-test (added-strand mid 2) na0 (0 1)
    (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
  (traces
    ((send (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-0 b a (enc na1 a b (pubk c))
          (enc na0 nb0-0 b c (pubk a)) (pubk c)))))
  (label 1)
  (parent 0)
  (unrealized (0 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton nsl3
  (vars (na0 na1 nb0 nb1 nc0 nc1 nb0-0 nb1-0 nc0-0 nc1-0 text)
    (a b c name))
  (defstrand init 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na0) (na1 na1) (nb0 nb0-0) (nb1 nb1-0) (a a)
    (b b) (c c))
  (defstrand resp 2 (na0 na0) (na1 na1) (nb0 nb0-0) (nb1 nb1-0)
    (nc0 nc0-0) (nc1 nc1-0) (a a) (b b) (c c))
  (precedes ((0 0) (1 0)) ((1 1) (2 0)) ((2 1) (0 1)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig na0 na1 nb0-0 nb1-0 nc0-0 nc1-0)
  (operation nonce-test (added-strand resp 2) na0 (0 1)
    (enc na0 a c (enc na1 a b (pubk c)) (pubk b))
    (enc nb1-0 b a (enc na1 a b (pubk c)) (enc na0 nb0-0 b c (pubk a))
      (pubk c)))
  (traces
    ((send (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-0 b a (enc na1 a b (pubk c))
          (enc na0 nb0-0 b c (pubk a)) (pubk c))))
    ((recv
       (enc nb1-0 b a (enc na1 a b (pubk c))
         (enc na0 nb0-0 b c (pubk a)) (pubk c)))
      (send
        (enc na1 nc1-0 c b (enc na0 nb0-0 b c (pubk a))
          (enc nb1-0 nc0-0 c a (pubk b)) (pubk a)))))
  (label 2)
  (parent 1)
  (unrealized (0 1))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton nsl3
  (vars (na0 na1 nb0 nb1 nc0 nc1 text) (a b c name))
  (defstrand init 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (a a) (b b)
    (c c))
  (defstrand resp 2 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (precedes ((0 0) (1 0)) ((1 1) (2 0)) ((2 1) (0 1)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig na0 na1 nb0 nb1 nc0 nc1)
  (operation nonce-test
    (contracted (nb0-0 nb0) (nb1-0 nb1) (nc0-0 nc0) (nc1-0 nc1)) na0
    (0 1) (enc na0 a c (enc na1 a b (pubk c)) (pubk b))
    (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
      (enc nb1 nc0 c a (pubk b)) (pubk a))
    (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
      (pubk c)))
  (traces
    ((send (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
          (pubk c))))
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))))
  (label 3)
  (parent 2)
  (unrealized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (c c) (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1)
        (nc0 nc0) (nc1 nc1))))
  (origs (nc0 (2 1)) (nc1 (2 1)) (nb0 (1 1)) (nb1 (1 1)) (na1 (0 0))
    (na0 (0 0))))

(defskeleton nsl3
  (vars
    (na0 na1 nb0 nb1 nc0 nc1 nb0-0 nb1-0 nc0-0 nc1-0 nb0-1 nb1-1 text)
    (a b c name))
  (defstrand init 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na0) (na1 na1) (nb0 nb0-0) (nb1 nb1-0) (a a)
    (b b) (c c))
  (defstrand resp 2 (na0 na0) (na1 na1) (nb0 nb0-0) (nb1 nb1-0)
    (nc0 nc0-0) (nc1 nc1-0) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na0) (na1 na1) (nb0 nb0-1) (nb1 nb1-1) (a a)
    (b b) (c c))
  (precedes ((0 0) (1 0)) ((0 0) (3 0)) ((1 1) (2 0)) ((2 1) (0 1))
    ((3 1) (0 1)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig na0 na1 nb0-0 nb1-0 nc0-0 nc1-0 nb0-1 nb1-1)
  (operation nonce-test (added-strand mid 2) na0 (0 1)
    (enc na0 a c (enc na1 a b (pubk c)) (pubk b))
    (enc na1 nc1-0 c b (enc na0 nb0-0 b c (pubk a))
      (enc nb1-0 nc0-0 c a (pubk b)) (pubk a))
    (enc nb1-0 b a (enc na1 a b (pubk c)) (enc na0 nb0-0 b c (pubk a))
      (pubk c)))
  (traces
    ((send (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-0 b a (enc na1 a b (pubk c))
          (enc na0 nb0-0 b c (pubk a)) (pubk c))))
    ((recv
       (enc nb1-0 b a (enc na1 a b (pubk c))
         (enc na0 nb0-0 b c (pubk a)) (pubk c)))
      (send
        (enc na1 nc1-0 c b (enc na0 nb0-0 b c (pubk a))
          (enc nb1-0 nc0-0 c a (pubk b)) (pubk a))))
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-1 b a (enc na1 a b (pubk c))
          (enc na0 nb0-1 b c (pubk a)) (pubk c)))))
  (label 4)
  (parent 2)
  (unrealized (0 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton nsl3
  (vars (na0 na1 nb0 nb1 nc0 nc1 nb0-0 nb1-0 text) (a b c name))
  (defstrand init 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (a a) (b b)
    (c c))
  (defstrand resp 2 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na0) (na1 na1) (nb0 nb0-0) (nb1 nb1-0) (a a)
    (b b) (c c))
  (precedes ((0 0) (1 0)) ((0 0) (3 0)) ((1 1) (2 0)) ((2 1) (0 1))
    ((3 1) (0 1)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig na0 na1 nb0 nb1 nc0 nc1 nb0-0 nb1-0)
  (operation nonce-test
    (contracted (nb0-1 nb0) (nb1-1 nb1) (nc0-0 nc0) (nc1-0 nc1)) na0
    (0 1) (enc na0 a c (enc na1 a b (pubk c)) (pubk b))
    (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
      (enc nb1 nc0 c a (pubk b)) (pubk a))
    (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
      (pubk c))
    (enc nb1-0 b a (enc na1 a b (pubk c)) (enc na0 nb0-0 b c (pubk a))
      (pubk c)))
  (traces
    ((send (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
          (pubk c))))
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a))))
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-0 b a (enc na1 a b (pubk c))
          (enc na0 nb0-0 b c (pubk a)) (pubk c)))))
  (label 5)
  (parent 4)
  (seen 3)
  (unrealized)
  (comment "1 in cohort - 0 not yet seen"))

(comment "Nothing left to do")

(defprotocol nsl3 basic
  (defrole init
    (vars (a b c name) (na0 na1 nb0 nb1 nc0 nc1 text))
    (trace (send (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    (uniq-orig na0 na1))
  (defrole mid
    (vars (a b c name) (na0 na1 nb0 nb1 nc0 nc1 text))
    (trace (recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
          (pubk c)))
      (recv
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))) (send (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    (uniq-orig nb0 nb1))
  (defrole resp
    (vars (a b c name) (na0 na1 nb0 nb1 nc0 nc1 text))
    (trace
      (recv
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
          (pubk c)))
      (send
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    (uniq-orig nc0 nc1)))

(defskeleton nsl3
  (vars (na0 na1 nb0 nb1 nc0 nc1 text) (a b c name))
  (defstrand mid 4 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig nb0 nb1)
  (traces
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
          (pubk c)))
      (recv
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))) (send (enc nc0 (enc nc1 (pubk c)) (pubk c)))))
  (label 6)
  (unrealized (0 2))
  (origs (nb1 (0 1)) (nb0 (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton nsl3
  (vars (na0 na1 nb0 nb1 nc0 nc1 nc0-0 nc1-0 text) (a b c name))
  (defstrand mid 4 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand resp 2 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0-0)
    (nc1 nc1-0) (a a) (b b) (c c))
  (precedes ((0 1) (1 0)) ((1 1) (0 2)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig nb0 nb1 nc0-0 nc1-0)
  (operation nonce-test (added-strand resp 2) nb0 (0 2)
    (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
      (pubk c)))
  (traces
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
          (pubk c)))
      (recv
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))) (send (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1-0 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0-0 c a (pubk b)) (pubk a)))))
  (label 7)
  (parent 6)
  (unrealized (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton nsl3
  (vars (na0 na1 nb0 nb1 nc0 nc1 nc0-0 nc1-0 text) (a b c name))
  (defstrand mid 4 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand resp 2 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0-0)
    (nc1 nc1-0) (a a) (b b) (c c))
  (defstrand init 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0-0)
    (nc1 nc1-0) (a a) (b b) (c c))
  (precedes ((0 1) (1 0)) ((1 1) (2 1)) ((2 0) (0 0)) ((2 2) (0 2)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig na0 na1 nb0 nb1 nc0-0 nc1-0)
  (operation nonce-test (added-strand init 3) nb0 (0 2)
    (enc na1 nc1-0 c b (enc na0 nb0 b c (pubk a))
      (enc nb1 nc0-0 c a (pubk b)) (pubk a))
    (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
      (pubk c)))
  (traces
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
          (pubk c)))
      (recv
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))) (send (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1-0 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0-0 c a (pubk b)) (pubk a))))
    ((send (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1-0 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0-0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0-0 c a (pubk b)) (enc nc1-0 (pubk c))
          (pubk b)))))
  (label 8)
  (parent 7)
  (unrealized (0 2))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton nsl3
  (vars (na0 na1 nb0 nb1 nc0 nc1 text) (a b c name))
  (defstrand mid 4 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand resp 2 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand init 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (precedes ((0 1) (1 0)) ((1 1) (2 1)) ((2 0) (0 0)) ((2 2) (0 2)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig na0 na1 nb0 nb1 nc0 nc1)
  (operation nonce-test (contracted (nc0-0 nc0) (nc1-0 nc1)) nb0 (0 2)
    (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
      (enc nb1 nc0 c a (pubk b)) (pubk a))
    (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c)) (pubk b))
    (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
      (pubk c)))
  (traces
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
          (pubk c)))
      (recv
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))) (send (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a))))
    ((send (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b)))))
  (label 9)
  (parent 8)
  (unrealized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (c c) (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1)
        (nc0 nc0) (nc1 nc1))))
  (origs (na0 (2 0)) (na1 (2 0)) (nc0 (1 1)) (nc1 (1 1)) (nb1 (0 1))
    (nb0 (0 1))))

(defskeleton nsl3
  (vars (na0 na1 nb0 nb1 nc0 nc1 nc0-0 nc1-0 nc0-1 nc1-1 text)
    (a b c name))
  (defstrand mid 4 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand resp 2 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0-0)
    (nc1 nc1-0) (a a) (b b) (c c))
  (defstrand init 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0-0)
    (nc1 nc1-0) (a a) (b b) (c c))
  (defstrand resp 2 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0-1)
    (nc1 nc1-1) (a a) (b b) (c c))
  (precedes ((0 1) (1 0)) ((0 1) (3 0)) ((1 1) (2 1)) ((2 0) (0 0))
    ((2 2) (0 2)) ((3 1) (0 2)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig na0 na1 nb0 nb1 nc0-0 nc1-0 nc0-1 nc1-1)
  (operation nonce-test (added-strand resp 2) nb0 (0 2)
    (enc na1 nc1-0 c b (enc na0 nb0 b c (pubk a))
      (enc nb1 nc0-0 c a (pubk b)) (pubk a))
    (enc nb0 (enc nb1 nc0-0 c a (pubk b)) (enc nc1-0 (pubk c)) (pubk b))
    (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
      (pubk c)))
  (traces
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
          (pubk c)))
      (recv
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))) (send (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1-0 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0-0 c a (pubk b)) (pubk a))))
    ((send (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1-0 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0-0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0-0 c a (pubk b)) (enc nc1-0 (pubk c))
          (pubk b))))
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1-1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0-1 c a (pubk b)) (pubk a)))))
  (label 10)
  (parent 8)
  (unrealized (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton nsl3
  (vars (na0 na1 nb0 nb1 nc0 nc1 nc0-0 nc1-0 text) (a b c name))
  (defstrand mid 4 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand resp 2 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand init 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand resp 2 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0-0)
    (nc1 nc1-0) (a a) (b b) (c c))
  (precedes ((0 1) (1 0)) ((0 1) (3 0)) ((1 1) (2 1)) ((2 0) (0 0))
    ((2 2) (0 2)) ((3 1) (0 2)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig na0 na1 nb0 nb1 nc0 nc1 nc0-0 nc1-0)
  (operation nonce-test (contracted (nc0-1 nc0) (nc1-1 nc1)) nb0 (0 2)
    (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
      (enc nb1 nc0 c a (pubk b)) (pubk a))
    (enc na1 nc1-0 c b (enc na0 nb0 b c (pubk a))
      (enc nb1 nc0-0 c a (pubk b)) (pubk a))
    (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c)) (pubk b))
    (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
      (pubk c)))
  (traces
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
          (pubk c)))
      (recv
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))) (send (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a))))
    ((send (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1-0 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0-0 c a (pubk b)) (pubk a)))))
  (label 11)
  (parent 10)
  (seen 9)
  (unrealized)
  (comment "1 in cohort - 0 not yet seen"))

(comment "Nothing left to do")

(defprotocol nsl3 basic
  (defrole init
    (vars (a b c name) (na0 na1 nb0 nb1 nc0 nc1 text))
    (trace (send (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    (uniq-orig na0 na1))
  (defrole mid
    (vars (a b c name) (na0 na1 nb0 nb1 nc0 nc1 text))
    (trace (recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
          (pubk c)))
      (recv
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))) (send (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    (uniq-orig nb0 nb1))
  (defrole resp
    (vars (a b c name) (na0 na1 nb0 nb1 nc0 nc1 text))
    (trace
      (recv
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
          (pubk c)))
      (send
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    (uniq-orig nc0 nc1)))

(defskeleton nsl3
  (vars (na0 na1 nb0 nb1 nc0 nc1 text) (a b c name))
  (defstrand resp 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig nc0 nc1)
  (traces
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c)))))
  (label 12)
  (unrealized (0 2))
  (origs (nc1 (0 1)) (nc0 (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton nsl3
  (vars (na0 na1 nb0 nb1 nc0 nc1 text) (a b c name))
  (defstrand resp 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand init 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (precedes ((0 1) (1 1)) ((1 0) (0 0)) ((1 2) (0 2)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig na0 na1 nc0 nc1)
  (operation nonce-test (added-strand init 3) nc0 (0 2)
    (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
      (enc nb1 nc0 c a (pubk b)) (pubk a)))
  (traces
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((send (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b)))))
  (label 13)
  (parent 12)
  (unrealized (0 0) (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton nsl3
  (vars (na0 na1 nb0 nb1 nc0 nc1 nb0-0 nb1-0 text) (a b c name))
  (defstrand resp 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand init 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na0) (na1 na1) (nb0 nb0-0) (nb1 nb1-0) (a a)
    (b b) (c c))
  (precedes ((0 1) (1 1)) ((1 0) (2 0)) ((1 2) (0 2)) ((2 1) (0 0)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig na0 na1 nc0 nc1 nb0-0 nb1-0)
  (operation nonce-test (added-strand mid 2) na1 (0 0)
    (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
  (traces
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((send (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-0 b a (enc na1 a b (pubk c))
          (enc na0 nb0-0 b c (pubk a)) (pubk c)))))
  (label 14)
  (parent 13)
  (unrealized (0 0) (0 2))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton nsl3
  (vars (na0 na1 nc0 nc1 nb0 nb1 text) (a b c name))
  (defstrand resp 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand init 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (a a) (b b)
    (c c))
  (precedes ((0 1) (1 1)) ((1 0) (2 0)) ((1 2) (0 2)) ((2 1) (0 0)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig na0 na1 nc0 nc1 nb0 nb1)
  (operation nonce-test (contracted (nb0-0 nb0) (nb1-0 nb1)) na1 (0 0)
    (enc na0 a c (enc na1 a b (pubk c)) (pubk b))
    (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
      (pubk c)))
  (traces
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((send (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
          (pubk c)))))
  (label 15)
  (parent 14)
  (unrealized (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton nsl3
  (vars (na0 na1 nb0 nb1 nc0 nc1 nb0-0 nb1-0 nc0-0 nc1-0 text)
    (a b c name))
  (defstrand resp 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand init 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na0) (na1 na1) (nb0 nb0-0) (nb1 nb1-0) (a a)
    (b b) (c c))
  (defstrand resp 2 (na0 na0) (na1 na1) (nb0 nb0-0) (nb1 nb1-0)
    (nc0 nc0-0) (nc1 nc1-0) (a a) (b b) (c c))
  (precedes ((0 1) (1 1)) ((1 0) (2 0)) ((1 2) (0 2)) ((2 1) (3 0))
    ((3 1) (0 0)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig na0 na1 nc0 nc1 nb0-0 nb1-0 nc0-0 nc1-0)
  (operation nonce-test (added-strand resp 2) na1 (0 0)
    (enc na0 a c (enc na1 a b (pubk c)) (pubk b))
    (enc nb1-0 b a (enc na1 a b (pubk c)) (enc na0 nb0-0 b c (pubk a))
      (pubk c)))
  (traces
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((send (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-0 b a (enc na1 a b (pubk c))
          (enc na0 nb0-0 b c (pubk a)) (pubk c))))
    ((recv
       (enc nb1-0 b a (enc na1 a b (pubk c))
         (enc na0 nb0-0 b c (pubk a)) (pubk c)))
      (send
        (enc na1 nc1-0 c b (enc na0 nb0-0 b c (pubk a))
          (enc nb1-0 nc0-0 c a (pubk b)) (pubk a)))))
  (label 16)
  (parent 14)
  (unrealized (0 0) (0 2))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton nsl3
  (vars (nc0 nc1 nb0 nb1 na0 na1 text) (a b c name))
  (defstrand resp 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand init 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 4 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (precedes ((0 1) (1 1)) ((0 1) (2 2)) ((1 0) (2 0)) ((1 2) (0 2))
    ((2 1) (0 0)) ((2 3) (0 2)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig nc0 nc1 nb0 nb1 na0 na1)
  (operation nonce-test (displaced 2 3 mid 4) nc0 (0 2)
    (enc na1-0 nc1 c b (enc na0-0 nb0 b c (pubk a))
      (enc nb1 nc0 c a (pubk b)) (pubk a))
    (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c)) (pubk b)))
  (traces
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((send (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
          (pubk c)))
      (recv
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))) (send (enc nc0 (enc nc1 (pubk c)) (pubk c)))))
  (label 17)
  (parent 15)
  (unrealized (2 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton nsl3
  (vars (na0 na1 nc0 nc1 nb0 nb1 nc0-0 nc1-0 text) (a b c name))
  (defstrand resp 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand init 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (a a) (b b)
    (c c))
  (defstrand resp 2 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0-0)
    (nc1 nc1-0) (a a) (b b) (c c))
  (precedes ((0 1) (1 1)) ((1 0) (2 0)) ((1 2) (0 2)) ((2 1) (3 0))
    ((3 1) (0 0)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig na0 na1 nc0 nc1 nb0 nb1 nc0-0 nc1-0)
  (operation nonce-test (contracted (nb0-0 nb0) (nb1-0 nb1)) na1 (0 0)
    (enc na0 a c (enc na1 a b (pubk c)) (pubk b))
    (enc na1 nc1-0 c b (enc na0 nb0 b c (pubk a))
      (enc nb1 nc0-0 c a (pubk b)) (pubk a))
    (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
      (pubk c)))
  (traces
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((send (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
          (pubk c))))
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1-0 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0-0 c a (pubk b)) (pubk a)))))
  (label 18)
  (parent 16)
  (unrealized (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton nsl3
  (vars
    (na0 na1 nb0 nb1 nc0 nc1 nb0-0 nb1-0 nc0-0 nc1-0 nb0-1 nb1-1 text)
    (a b c name))
  (defstrand resp 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand init 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na0) (na1 na1) (nb0 nb0-0) (nb1 nb1-0) (a a)
    (b b) (c c))
  (defstrand resp 2 (na0 na0) (na1 na1) (nb0 nb0-0) (nb1 nb1-0)
    (nc0 nc0-0) (nc1 nc1-0) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na0) (na1 na1) (nb0 nb0-1) (nb1 nb1-1) (a a)
    (b b) (c c))
  (precedes ((0 1) (1 1)) ((1 0) (2 0)) ((1 0) (4 0)) ((1 2) (0 2))
    ((2 1) (3 0)) ((3 1) (0 0)) ((4 1) (0 0)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig na0 na1 nc0 nc1 nb0-0 nb1-0 nc0-0 nc1-0 nb0-1 nb1-1)
  (operation nonce-test (added-strand mid 2) na1 (0 0)
    (enc na0 a c (enc na1 a b (pubk c)) (pubk b))
    (enc na1 nc1-0 c b (enc na0 nb0-0 b c (pubk a))
      (enc nb1-0 nc0-0 c a (pubk b)) (pubk a))
    (enc nb1-0 b a (enc na1 a b (pubk c)) (enc na0 nb0-0 b c (pubk a))
      (pubk c)))
  (traces
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((send (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-0 b a (enc na1 a b (pubk c))
          (enc na0 nb0-0 b c (pubk a)) (pubk c))))
    ((recv
       (enc nb1-0 b a (enc na1 a b (pubk c))
         (enc na0 nb0-0 b c (pubk a)) (pubk c)))
      (send
        (enc na1 nc1-0 c b (enc na0 nb0-0 b c (pubk a))
          (enc nb1-0 nc0-0 c a (pubk b)) (pubk a))))
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-1 b a (enc na1 a b (pubk c))
          (enc na0 nb0-1 b c (pubk a)) (pubk c)))))
  (label 19)
  (parent 16)
  (unrealized (0 0) (0 2))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton nsl3
  (vars (nc0 nc1 nb0 nb1 na0 na1 text) (a b c name))
  (defstrand resp 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand init 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 4 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (precedes ((0 1) (1 1)) ((1 0) (2 0)) ((1 2) (2 2)) ((2 1) (0 0))
    ((2 3) (0 2)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig nc0 nc1 nb0 nb1 na0 na1)
  (operation nonce-test (displaced 3 1 init 3) nc0 (2 2)
    (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
      (enc nb1 nc0 c a (pubk b)) (pubk a)))
  (traces
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((send (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
          (pubk c)))
      (recv
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))) (send (enc nc0 (enc nc1 (pubk c)) (pubk c)))))
  (label 20)
  (parent 17)
  (unrealized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (c c) (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1)
        (nc0 nc0) (nc1 nc1))))
  (origs (na0 (1 0)) (na1 (1 0)) (nb0 (2 1)) (nb1 (2 1)) (nc1 (0 1))
    (nc0 (0 1))))

(defskeleton nsl3
  (vars (nc0 nc1 nb0 nb1 nc0-0 nc1-0 na0 na1 text) (a b c name))
  (defstrand resp 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand init 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand resp 2 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0-0)
    (nc1 nc1-0) (a a) (b b) (c c))
  (defstrand mid 4 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (precedes ((0 1) (1 1)) ((0 1) (3 2)) ((1 0) (3 0)) ((1 2) (0 2))
    ((2 1) (0 0)) ((3 1) (2 0)) ((3 3) (0 2)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig nc0 nc1 nb0 nb1 nc0-0 nc1-0 na0 na1)
  (operation nonce-test (displaced 2 4 mid 4) nc0 (0 2)
    (enc na1-0 nc1 c b (enc na0-0 nb0 b c (pubk a))
      (enc nb1 nc0 c a (pubk b)) (pubk a))
    (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c)) (pubk b)))
  (traces
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((send (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1-0 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0-0 c a (pubk b)) (pubk a))))
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
          (pubk c)))
      (recv
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))) (send (enc nc0 (enc nc1 (pubk c)) (pubk c)))))
  (label 21)
  (parent 18)
  (unrealized (3 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton nsl3
  (vars (na0 na1 nc0 nc1 nb0 nb1 nc0-0 nc1-0 nb0-0 nb1-0 text)
    (a b c name))
  (defstrand resp 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand init 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (a a) (b b)
    (c c))
  (defstrand resp 2 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0-0)
    (nc1 nc1-0) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na0) (na1 na1) (nb0 nb0-0) (nb1 nb1-0) (a a)
    (b b) (c c))
  (precedes ((0 1) (1 1)) ((1 0) (2 0)) ((1 0) (4 0)) ((1 2) (0 2))
    ((2 1) (3 0)) ((3 1) (0 0)) ((4 1) (0 0)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig na0 na1 nc0 nc1 nb0 nb1 nc0-0 nc1-0 nb0-0 nb1-0)
  (operation nonce-test (contracted (nb0-1 nb0) (nb1-1 nb1)) na1 (0 0)
    (enc na0 a c (enc na1 a b (pubk c)) (pubk b))
    (enc na1 nc1-0 c b (enc na0 nb0 b c (pubk a))
      (enc nb1 nc0-0 c a (pubk b)) (pubk a))
    (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
      (pubk c))
    (enc nb1-0 b a (enc na1 a b (pubk c)) (enc na0 nb0-0 b c (pubk a))
      (pubk c)))
  (traces
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((send (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
          (pubk c))))
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1-0 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0-0 c a (pubk b)) (pubk a))))
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-0 b a (enc na1 a b (pubk c))
          (enc na0 nb0-0 b c (pubk a)) (pubk c)))))
  (label 22)
  (parent 19)
  (unrealized (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton nsl3
  (vars (na0 na1 nc0 nc1 nb0 nb1 nc0-0 nc1-0 nb0-0 nb1-0 text)
    (a b c name))
  (defstrand resp 3 (na0 na0) (na1 na1) (nb0 nb0-0) (nb1 nb1-0)
    (nc0 nc0) (nc1 nc1) (a a) (b b) (c c))
  (defstrand init 3 (na0 na0) (na1 na1) (nb0 nb0-0) (nb1 nb1-0)
    (nc0 nc0) (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (a a) (b b)
    (c c))
  (defstrand resp 2 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0-0)
    (nc1 nc1-0) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na0) (na1 na1) (nb0 nb0-0) (nb1 nb1-0) (a a)
    (b b) (c c))
  (precedes ((0 1) (1 1)) ((1 0) (2 0)) ((1 0) (4 0)) ((1 2) (0 2))
    ((2 1) (3 0)) ((3 1) (0 0)) ((4 1) (0 0)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig na0 na1 nc0 nc1 nb0 nb1 nc0-0 nc1-0 nb0-0 nb1-0)
  (operation nonce-test (contracted (nb0-1 nb0-0) (nb1-1 nb1-0)) na1
    (0 0) (enc na0 a c (enc na1 a b (pubk c)) (pubk b))
    (enc na1 nc1-0 c b (enc na0 nb0 b c (pubk a))
      (enc nb1 nc0-0 c a (pubk b)) (pubk a))
    (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
      (pubk c))
    (enc nb1-0 b a (enc na1 a b (pubk c)) (enc na0 nb0-0 b c (pubk a))
      (pubk c)))
  (traces
    ((recv
       (enc nb1-0 b a (enc na1 a b (pubk c))
         (enc na0 nb0-0 b c (pubk a)) (pubk c)))
      (send
        (enc na1 nc1 c b (enc na0 nb0-0 b c (pubk a))
          (enc nb1-0 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((send (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na0 nb0-0 b c (pubk a))
          (enc nb1-0 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0-0 (enc nb1-0 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
          (pubk c))))
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1-0 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0-0 c a (pubk b)) (pubk a))))
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-0 b a (enc na1 a b (pubk c))
          (enc na0 nb0-0 b c (pubk a)) (pubk c)))))
  (label 23)
  (parent 19)
  (unrealized (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton nsl3
  (vars (nc0 nc1 nb0 nb1 nc0-0 nc1-0 na0 na1 text) (a b c name))
  (defstrand resp 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand init 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand resp 2 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0-0)
    (nc1 nc1-0) (a a) (b b) (c c))
  (defstrand mid 4 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (precedes ((0 1) (1 1)) ((1 0) (3 0)) ((1 2) (3 2)) ((2 1) (0 0))
    ((3 1) (2 0)) ((3 3) (0 2)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig nc0 nc1 nb0 nb1 nc0-0 nc1-0 na0 na1)
  (operation nonce-test (displaced 4 1 init 3) nc0 (3 2)
    (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
      (enc nb1 nc0 c a (pubk b)) (pubk a)))
  (traces
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((send (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1-0 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0-0 c a (pubk b)) (pubk a))))
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
          (pubk c)))
      (recv
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))) (send (enc nc0 (enc nc1 (pubk c)) (pubk c)))))
  (label 24)
  (parent 21)
  (seen 20)
  (unrealized)
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton nsl3
  (vars (nc0 nc1 nb0 nb1 nc0-0 nc1-0 nb0-0 nb1-0 na0 na1 text)
    (a b c name))
  (defstrand resp 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand init 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand resp 2 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0-0)
    (nc1 nc1-0) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na0) (na1 na1) (nb0 nb0-0) (nb1 nb1-0) (a a)
    (b b) (c c))
  (defstrand mid 4 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (precedes ((0 1) (1 1)) ((0 1) (4 2)) ((1 0) (3 0)) ((1 0) (4 0))
    ((1 2) (0 2)) ((2 1) (0 0)) ((3 1) (0 0)) ((4 1) (2 0))
    ((4 3) (0 2)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig nc0 nc1 nb0 nb1 nc0-0 nc1-0 nb0-0 nb1-0 na0 na1)
  (operation nonce-test (displaced 2 5 mid 4) nc0 (0 2)
    (enc na1-0 nc1 c b (enc na0-0 nb0 b c (pubk a))
      (enc nb1 nc0 c a (pubk b)) (pubk a))
    (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c)) (pubk b)))
  (traces
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((send (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1-0 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0-0 c a (pubk b)) (pubk a))))
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-0 b a (enc na1 a b (pubk c))
          (enc na0 nb0-0 b c (pubk a)) (pubk c))))
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
          (pubk c)))
      (recv
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))) (send (enc nc0 (enc nc1 (pubk c)) (pubk c)))))
  (label 25)
  (parent 22)
  (unrealized (4 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton nsl3
  (vars (nc0 nc1 nb0 nb1 nc0-0 nc1-0 nb0-0 nb1-0 na0 na1 text)
    (a b c name))
  (defstrand resp 3 (na0 na0) (na1 na1) (nb0 nb0-0) (nb1 nb1-0)
    (nc0 nc0) (nc1 nc1) (a a) (b b) (c c))
  (defstrand init 3 (na0 na0) (na1 na1) (nb0 nb0-0) (nb1 nb1-0)
    (nc0 nc0) (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (a a) (b b)
    (c c))
  (defstrand resp 2 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0-0)
    (nc1 nc1-0) (a a) (b b) (c c))
  (defstrand mid 4 (na0 na0) (na1 na1) (nb0 nb0-0) (nb1 nb1-0) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (precedes ((0 1) (1 1)) ((0 1) (4 2)) ((1 0) (2 0)) ((1 0) (4 0))
    ((1 2) (0 2)) ((2 1) (3 0)) ((3 1) (0 0)) ((4 1) (0 0))
    ((4 3) (0 2)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig nc0 nc1 nb0 nb1 nc0-0 nc1-0 nb0-0 nb1-0 na0 na1)
  (operation nonce-test (displaced 4 5 mid 4) nc0 (0 2)
    (enc na1-0 nc1 c b (enc na0-0 nb0-0 b c (pubk a))
      (enc nb1-0 nc0 c a (pubk b)) (pubk a))
    (enc nb0-0 (enc nb1-0 nc0 c a (pubk b)) (enc nc1 (pubk c))
      (pubk b)))
  (traces
    ((recv
       (enc nb1-0 b a (enc na1 a b (pubk c))
         (enc na0 nb0-0 b c (pubk a)) (pubk c)))
      (send
        (enc na1 nc1 c b (enc na0 nb0-0 b c (pubk a))
          (enc nb1-0 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((send (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na0 nb0-0 b c (pubk a))
          (enc nb1-0 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0-0 (enc nb1-0 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
          (pubk c))))
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1-0 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0-0 c a (pubk b)) (pubk a))))
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-0 b a (enc na1 a b (pubk c))
          (enc na0 nb0-0 b c (pubk a)) (pubk c)))
      (recv
        (enc nb0-0 (enc nb1-0 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))) (send (enc nc0 (enc nc1 (pubk c)) (pubk c)))))
  (label 26)
  (parent 23)
  (unrealized (4 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton nsl3
  (vars (nc0 nc1 nb0 nb1 nc0-0 nc1-0 nb0-0 nb1-0 na0 na1 text)
    (a b c name))
  (defstrand resp 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand init 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand resp 2 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0-0)
    (nc1 nc1-0) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na0) (na1 na1) (nb0 nb0-0) (nb1 nb1-0) (a a)
    (b b) (c c))
  (defstrand mid 4 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (precedes ((0 1) (1 1)) ((1 0) (3 0)) ((1 0) (4 0)) ((1 2) (4 2))
    ((2 1) (0 0)) ((3 1) (0 0)) ((4 1) (2 0)) ((4 3) (0 2)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig nc0 nc1 nb0 nb1 nc0-0 nc1-0 nb0-0 nb1-0 na0 na1)
  (operation nonce-test (displaced 5 1 init 3) nc0 (4 2)
    (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
      (enc nb1 nc0 c a (pubk b)) (pubk a)))
  (traces
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((send (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1-0 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0-0 c a (pubk b)) (pubk a))))
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-0 b a (enc na1 a b (pubk c))
          (enc na0 nb0-0 b c (pubk a)) (pubk c))))
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
          (pubk c)))
      (recv
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))) (send (enc nc0 (enc nc1 (pubk c)) (pubk c)))))
  (label 27)
  (parent 25)
  (unrealized)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton nsl3
  (vars (nc0 nc1 nb0 nb1 nc0-0 nc1-0 nb0-0 nb1-0 na0 na1 text)
    (a b c name))
  (defstrand resp 3 (na0 na0) (na1 na1) (nb0 nb0-0) (nb1 nb1-0)
    (nc0 nc0) (nc1 nc1) (a a) (b b) (c c))
  (defstrand init 3 (na0 na0) (na1 na1) (nb0 nb0-0) (nb1 nb1-0)
    (nc0 nc0) (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (a a) (b b)
    (c c))
  (defstrand resp 2 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0-0)
    (nc1 nc1-0) (a a) (b b) (c c))
  (defstrand mid 4 (na0 na0) (na1 na1) (nb0 nb0-0) (nb1 nb1-0) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (precedes ((0 1) (1 1)) ((1 0) (2 0)) ((1 0) (4 0)) ((1 2) (4 2))
    ((2 1) (3 0)) ((3 1) (0 0)) ((4 1) (0 0)) ((4 3) (0 2)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig nc0 nc1 nb0 nb1 nc0-0 nc1-0 nb0-0 nb1-0 na0 na1)
  (operation nonce-test (displaced 5 1 init 3) nc0 (4 2)
    (enc na1 nc1 c b (enc na0 nb0-0 b c (pubk a))
      (enc nb1-0 nc0 c a (pubk b)) (pubk a)))
  (traces
    ((recv
       (enc nb1-0 b a (enc na1 a b (pubk c))
         (enc na0 nb0-0 b c (pubk a)) (pubk c)))
      (send
        (enc na1 nc1 c b (enc na0 nb0-0 b c (pubk a))
          (enc nb1-0 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((send (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na0 nb0-0 b c (pubk a))
          (enc nb1-0 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0-0 (enc nb1-0 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
          (pubk c))))
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1-0 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0-0 c a (pubk b)) (pubk a))))
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-0 b a (enc na1 a b (pubk c))
          (enc na0 nb0-0 b c (pubk a)) (pubk c)))
      (recv
        (enc nb0-0 (enc nb1-0 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))) (send (enc nc0 (enc nc1 (pubk c)) (pubk c)))))
  (label 28)
  (parent 26)
  (seen 29)
  (unrealized)
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton nsl3
  (vars (nc0 nc1 nb0 nb1 nb0-0 nb1-0 na0 na1 text) (a b c name))
  (defstrand resp 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand init 3 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na0) (na1 na1) (nb0 nb0-0) (nb1 nb1-0) (a a)
    (b b) (c c))
  (defstrand mid 4 (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (precedes ((0 1) (1 1)) ((1 0) (2 0)) ((1 0) (3 0)) ((1 2) (3 2))
    ((2 1) (0 0)) ((3 1) (0 0)) ((3 3) (0 2)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig nc0 nc1 nb0 nb1 nb0-0 nb1-0 na0 na1)
  (operation generalization deleted (2 0))
  (traces
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((send (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-0 b a (enc na1 a b (pubk c))
          (enc na0 nb0-0 b c (pubk a)) (pubk c))))
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb0 b c (pubk a))
          (pubk c)))
      (recv
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))) (send (enc nc0 (enc nc1 (pubk c)) (pubk c)))))
  (label 29)
  (parent 27)
  (seen 20)
  (unrealized)
  (comment "1 in cohort - 0 not yet seen"))

(comment "Nothing left to do")
