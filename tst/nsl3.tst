(herald "Three Party Needham-Schroeder-Lowe Protocol")

(comment "CPSA 2.3.1")
(comment "All input read from nsl3.scm")

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
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton nsl3
  (vars (na1 nb0 nb1 nc0 nc1 nb0-0 nb1-0 nb0-1 nb1-1 text) (a b c name))
  (defstrand init 3 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na1) (na1 na1) (nb0 nb0-0) (nb1 nb1-0) (a a)
    (b b) (c c))
  (defstrand mid 2 (na0 na1) (na1 na1) (nb0 nb0-1) (nb1 nb1-1) (a a)
    (b b) (c c))
  (precedes ((0 0) (1 0)) ((0 0) (2 0)) ((1 1) (0 1)) ((2 1) (0 1)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig na1 nb0-0 nb1-0 nb0-1 nb1-1)
  (operation nonce-test (added-strand mid 2) na1 (0 1)
    (enc na1 a c (enc na1 a b (pubk c)) (pubk b))
    (enc nb1-0 b a (enc na1 a b (pubk c)) (enc na1 nb0-0 b c (pubk a))
      (pubk c)))
  (traces
    ((send (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na1 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-0 b a (enc na1 a b (pubk c))
          (enc na1 nb0-0 b c (pubk a)) (pubk c))))
    ((recv (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-1 b a (enc na1 a b (pubk c))
          (enc na1 nb0-1 b c (pubk a)) (pubk c)))))
  (label 2)
  (parent 1)
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
  (label 3)
  (parent 1)
  (unrealized (0 1))
  (comment "3 in cohort - 3 not yet seen"))

(defskeleton nsl3
  (vars (na1 nb0 nb1 nc0 nc1 nb0-0 nb1-0 nc0-0 nc1-0 text) (a b c name))
  (defstrand init 3 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na1) (na1 na1) (nb0 nb0-0) (nb1 nb1-0) (a a)
    (b b) (c c))
  (defstrand resp 2 (na0 na1) (na1 na1) (nb0 nb0-0) (nb1 nb1-0)
    (nc0 nc0-0) (nc1 nc1-0) (a a) (b b) (c c))
  (precedes ((0 0) (1 0)) ((1 1) (2 0)) ((2 1) (0 1)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig na1 nb0-0 nb1-0 nc0-0 nc1-0)
  (operation nonce-test (added-strand resp 2) na1 (0 1)
    (enc na1 a c (enc na1 a b (pubk c)) (pubk b))
    (enc nb1-0 b a (enc na1 a b (pubk c)) (enc na1 nb0-0 b c (pubk a))
      (pubk c)))
  (traces
    ((send (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na1 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-0 b a (enc na1 a b (pubk c))
          (enc na1 nb0-0 b c (pubk a)) (pubk c))))
    ((recv
       (enc nb1-0 b a (enc na1 a b (pubk c))
         (enc na1 nb0-0 b c (pubk a)) (pubk c)))
      (send
        (enc na1 nc1-0 c b (enc na1 nb0-0 b c (pubk a))
          (enc nb1-0 nc0-0 c a (pubk b)) (pubk a)))))
  (label 4)
  (parent 2)
  (unrealized (0 1))
  (comment "1 in cohort - 1 not yet seen"))

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
  (label 5)
  (parent 3)
  (unrealized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (c c) (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1)
        (nc0 nc0) (nc1 nc1))))
  (origs (nc0 (2 1)) (nc1 (2 1)) (nb0 (1 1)) (nb1 (1 1)) (na1 (0 0))
    (na0 (0 0))))

(defskeleton nsl3
  (vars (na1 nb0 nb1 nc0 nc1 nb0-0 nb1-0 nc0-0 nc1-0 nb0-1 nb1-1 text)
    (a b c name))
  (defstrand init 3 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na1) (na1 na1) (nb0 nb0-0) (nb1 nb1-0) (a a)
    (b b) (c c))
  (defstrand resp 2 (na0 na1) (na1 na1) (nb0 nb0-0) (nb1 nb1-0)
    (nc0 nc0-0) (nc1 nc1-0) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na1) (na1 na1) (nb0 nb0-1) (nb1 nb1-1) (a a)
    (b b) (c c))
  (precedes ((0 0) (1 0)) ((0 0) (3 0)) ((1 1) (2 0)) ((2 1) (0 1))
    ((3 1) (0 1)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig na1 nb0-0 nb1-0 nc0-0 nc1-0 nb0-1 nb1-1)
  (operation nonce-test (added-strand mid 2) na1 (0 1)
    (enc na1 nc1-0 c b (enc na1 nb0-0 b c (pubk a))
      (enc nb1-0 nc0-0 c a (pubk b)) (pubk a))
    (enc na1 a c (enc na1 a b (pubk c)) (pubk b))
    (enc nb1-0 b a (enc na1 a b (pubk c)) (enc na1 nb0-0 b c (pubk a))
      (pubk c)))
  (traces
    ((send (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na1 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-0 b a (enc na1 a b (pubk c))
          (enc na1 nb0-0 b c (pubk a)) (pubk c))))
    ((recv
       (enc nb1-0 b a (enc na1 a b (pubk c))
         (enc na1 nb0-0 b c (pubk a)) (pubk c)))
      (send
        (enc na1 nc1-0 c b (enc na1 nb0-0 b c (pubk a))
          (enc nb1-0 nc0-0 c a (pubk b)) (pubk a))))
    ((recv (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-1 b a (enc na1 a b (pubk c))
          (enc na1 nb0-1 b c (pubk a)) (pubk c)))))
  (label 6)
  (parent 3)
  (seen 8)
  (unrealized (0 1))
  (comment "2 in cohort - 1 not yet seen"))

(defskeleton nsl3
  (vars (na1 nb0 nb1 nc0 nc1 nb0-0 nb1-0 nc0-0 nc1-0 nc0-1 nc1-1 text)
    (a b c name))
  (defstrand init 3 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na1) (na1 na1) (nb0 nb0-0) (nb1 nb1-0) (a a)
    (b b) (c c))
  (defstrand resp 2 (na0 na1) (na1 na1) (nb0 nb0-0) (nb1 nb1-0)
    (nc0 nc0-0) (nc1 nc1-0) (a a) (b b) (c c))
  (defstrand resp 2 (na0 na1) (na1 na1) (nb0 nb0-0) (nb1 nb1-0)
    (nc0 nc0-1) (nc1 nc1-1) (a a) (b b) (c c))
  (precedes ((0 0) (1 0)) ((1 1) (2 0)) ((1 1) (3 0)) ((2 1) (0 1))
    ((3 1) (0 1)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig na1 nb0-0 nb1-0 nc0-0 nc1-0 nc0-1 nc1-1)
  (operation nonce-test (added-strand resp 2) na1 (0 1)
    (enc na1 nc1-0 c b (enc na1 nb0-0 b c (pubk a))
      (enc nb1-0 nc0-0 c a (pubk b)) (pubk a))
    (enc na1 a c (enc na1 a b (pubk c)) (pubk b))
    (enc nb1-0 b a (enc na1 a b (pubk c)) (enc na1 nb0-0 b c (pubk a))
      (pubk c)))
  (traces
    ((send (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na1 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-0 b a (enc na1 a b (pubk c))
          (enc na1 nb0-0 b c (pubk a)) (pubk c))))
    ((recv
       (enc nb1-0 b a (enc na1 a b (pubk c))
         (enc na1 nb0-0 b c (pubk a)) (pubk c)))
      (send
        (enc na1 nc1-0 c b (enc na1 nb0-0 b c (pubk a))
          (enc nb1-0 nc0-0 c a (pubk b)) (pubk a))))
    ((recv
       (enc nb1-0 b a (enc na1 a b (pubk c))
         (enc na1 nb0-0 b c (pubk a)) (pubk c)))
      (send
        (enc na1 nc1-1 c b (enc na1 nb0-0 b c (pubk a))
          (enc nb1-0 nc0-1 c a (pubk b)) (pubk a)))))
  (label 7)
  (parent 3)
  (seen 8)
  (unrealized (0 1))
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton nsl3
  (vars (na1 nb0 nb1 nc0 nc1 text) (a b c name))
  (defstrand init 3 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (a a) (b b)
    (c c))
  (defstrand resp 2 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (precedes ((0 0) (1 0)) ((1 1) (2 0)) ((2 1) (0 1)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig na1 nb0 nb1 nc0 nc1)
  (operation nonce-test
    (contracted (nb0-0 nb0) (nb1-0 nb1) (nc0-0 nc0) (nc1-0 nc1)) na1
    (0 1)
    (enc na1 nc1 c b (enc na1 nb0 b c (pubk a))
      (enc nb1 nc0 c a (pubk b)) (pubk a))
    (enc na1 a c (enc na1 a b (pubk c)) (pubk b))
    (enc nb1 b a (enc na1 a b (pubk c)) (enc na1 nb0 b c (pubk a))
      (pubk c)))
  (traces
    ((send (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na1 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na1 nb0 b c (pubk a))
          (pubk c))))
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na1 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1 c b (enc na1 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))))
  (label 8)
  (parent 4)
  (seen 5)
  (unrealized)
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton nsl3
  (vars
    (na1 nb0 nb1 nc0 nc1 nb0-0 nb1-0 nc0-0 nc1-0 nb0-1 nb1-1 nc0-1 nc1-1
      text) (a b c name))
  (defstrand init 3 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na1) (na1 na1) (nb0 nb0-0) (nb1 nb1-0) (a a)
    (b b) (c c))
  (defstrand resp 2 (na0 na1) (na1 na1) (nb0 nb0-0) (nb1 nb1-0)
    (nc0 nc0-0) (nc1 nc1-0) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na1) (na1 na1) (nb0 nb0-1) (nb1 nb1-1) (a a)
    (b b) (c c))
  (defstrand resp 2 (na0 na1) (na1 na1) (nb0 nb0-1) (nb1 nb1-1)
    (nc0 nc0-1) (nc1 nc1-1) (a a) (b b) (c c))
  (precedes ((0 0) (1 0)) ((0 0) (3 0)) ((1 1) (2 0)) ((2 1) (0 1))
    ((3 1) (4 0)) ((4 1) (0 1)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig na1 nb0-0 nb1-0 nc0-0 nc1-0 nb0-1 nb1-1 nc0-1 nc1-1)
  (operation nonce-test (added-strand resp 2) na1 (0 1)
    (enc na1 nc1-0 c b (enc na1 nb0-0 b c (pubk a))
      (enc nb1-0 nc0-0 c a (pubk b)) (pubk a))
    (enc na1 a c (enc na1 a b (pubk c)) (pubk b))
    (enc nb1-0 b a (enc na1 a b (pubk c)) (enc na1 nb0-0 b c (pubk a))
      (pubk c))
    (enc nb1-1 b a (enc na1 a b (pubk c)) (enc na1 nb0-1 b c (pubk a))
      (pubk c)))
  (traces
    ((send (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na1 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-0 b a (enc na1 a b (pubk c))
          (enc na1 nb0-0 b c (pubk a)) (pubk c))))
    ((recv
       (enc nb1-0 b a (enc na1 a b (pubk c))
         (enc na1 nb0-0 b c (pubk a)) (pubk c)))
      (send
        (enc na1 nc1-0 c b (enc na1 nb0-0 b c (pubk a))
          (enc nb1-0 nc0-0 c a (pubk b)) (pubk a))))
    ((recv (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-1 b a (enc na1 a b (pubk c))
          (enc na1 nb0-1 b c (pubk a)) (pubk c))))
    ((recv
       (enc nb1-1 b a (enc na1 a b (pubk c))
         (enc na1 nb0-1 b c (pubk a)) (pubk c)))
      (send
        (enc na1 nc1-1 c b (enc na1 nb0-1 b c (pubk a))
          (enc nb1-1 nc0-1 c a (pubk b)) (pubk a)))))
  (label 9)
  (parent 6)
  (seen 10)
  (unrealized (0 1))
  (comment "2 in cohort - 1 not yet seen"))

(defskeleton nsl3
  (vars (na1 nb0 nb1 nc0 nc1 nb0-0 nb1-0 nc0-0 nc1-0 text) (a b c name))
  (defstrand init 3 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (a a) (b b)
    (c c))
  (defstrand resp 2 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na1) (na1 na1) (nb0 nb0-0) (nb1 nb1-0) (a a)
    (b b) (c c))
  (defstrand resp 2 (na0 na1) (na1 na1) (nb0 nb0-0) (nb1 nb1-0)
    (nc0 nc0-0) (nc1 nc1-0) (a a) (b b) (c c))
  (precedes ((0 0) (1 0)) ((0 0) (3 0)) ((1 1) (2 0)) ((2 1) (0 1))
    ((3 1) (4 0)) ((4 1) (0 1)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig na1 nb0 nb1 nc0 nc1 nb0-0 nb1-0 nc0-0 nc1-0)
  (operation nonce-test
    (contracted (nb0-1 nb0) (nb1-1 nb1) (nc0-1 nc0) (nc1-1 nc1)) na1
    (0 1)
    (enc na1 nc1 c b (enc na1 nb0 b c (pubk a))
      (enc nb1 nc0 c a (pubk b)) (pubk a))
    (enc na1 nc1-0 c b (enc na1 nb0-0 b c (pubk a))
      (enc nb1-0 nc0-0 c a (pubk b)) (pubk a))
    (enc na1 a c (enc na1 a b (pubk c)) (pubk b))
    (enc nb1 b a (enc na1 a b (pubk c)) (enc na1 nb0 b c (pubk a))
      (pubk c))
    (enc nb1-0 b a (enc na1 a b (pubk c)) (enc na1 nb0-0 b c (pubk a))
      (pubk c)))
  (traces
    ((send (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na1 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na1 nb0 b c (pubk a))
          (pubk c))))
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na1 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1 c b (enc na1 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a))))
    ((recv (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-0 b a (enc na1 a b (pubk c))
          (enc na1 nb0-0 b c (pubk a)) (pubk c))))
    ((recv
       (enc nb1-0 b a (enc na1 a b (pubk c))
         (enc na1 nb0-0 b c (pubk a)) (pubk c)))
      (send
        (enc na1 nc1-0 c b (enc na1 nb0-0 b c (pubk a))
          (enc nb1-0 nc0-0 c a (pubk b)) (pubk a)))))
  (label 10)
  (parent 9)
  (unrealized)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton nsl3
  (vars (na1 nb0 nb1 nc0 nc1 nb0-0 nb1-0 text) (a b c name))
  (defstrand init 3 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (a a) (b b)
    (c c))
  (defstrand resp 2 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na1) (na1 na1) (nb0 nb0-0) (nb1 nb1-0) (a a)
    (b b) (c c))
  (precedes ((0 0) (1 0)) ((0 0) (3 0)) ((1 1) (2 0)) ((2 1) (0 1))
    ((3 1) (0 1)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig na1 nb0 nb1 nc0 nc1 nb0-0 nb1-0)
  (operation generalization deleted (4 0))
  (traces
    ((send (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na1 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na1 nb0 b c (pubk a))
          (pubk c))))
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na1 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1 c b (enc na1 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a))))
    ((recv (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-0 b a (enc na1 a b (pubk c))
          (enc na1 nb0-0 b c (pubk a)) (pubk c)))))
  (label 11)
  (parent 10)
  (seen 8)
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
  (label 12)
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
  (label 13)
  (parent 12)
  (unrealized (0 2))
  (comment "2 in cohort - 2 not yet seen"))

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
  (label 14)
  (parent 13)
  (unrealized (0 2))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton nsl3
  (vars (na0 na1 nb1 nc0 nc1 nc0-0 nc1-0 nc0-1 nc1-1 text) (a b c name))
  (defstrand mid 4 (na0 na0) (na1 na1) (nb0 nb1) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand resp 2 (na0 na0) (na1 na1) (nb0 nb1) (nb1 nb1) (nc0 nc0-0)
    (nc1 nc1-0) (a a) (b b) (c c))
  (defstrand resp 2 (na0 na0) (na1 na1) (nb0 nb1) (nb1 nb1) (nc0 nc0-1)
    (nc1 nc1-1) (a a) (b b) (c c))
  (precedes ((0 1) (1 0)) ((0 1) (2 0)) ((1 1) (0 2)) ((2 1) (0 2)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig nb1 nc0-0 nc1-0 nc0-1 nc1-1)
  (operation nonce-test (added-strand resp 2) nb1 (0 2)
    (enc na1 nc1-0 c b (enc na0 nb1 b c (pubk a))
      (enc nb1 nc0-0 c a (pubk b)) (pubk a))
    (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb1 b c (pubk a))
      (pubk c)))
  (traces
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb1 b c (pubk a))
          (pubk c)))
      (recv
        (enc nb1 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))) (send (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb1 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1-0 c b (enc na0 nb1 b c (pubk a))
          (enc nb1 nc0-0 c a (pubk b)) (pubk a))))
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb1 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1-1 c b (enc na0 nb1 b c (pubk a))
          (enc nb1 nc0-1 c a (pubk b)) (pubk a)))))
  (label 15)
  (parent 13)
  (unrealized (0 2))
  (comment "1 in cohort - 1 not yet seen"))

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
  (label 16)
  (parent 14)
  (unrealized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (c c) (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1)
        (nc0 nc0) (nc1 nc1))))
  (origs (na0 (2 0)) (na1 (2 0)) (nc0 (1 1)) (nc1 (1 1)) (nb1 (0 1))
    (nb0 (0 1))))

(defskeleton nsl3
  (vars (na0 na1 nb1 nc0 nc1 nc0-0 nc1-0 nc0-1 nc1-1 text) (a b c name))
  (defstrand mid 4 (na0 na0) (na1 na1) (nb0 nb1) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand resp 2 (na0 na0) (na1 na1) (nb0 nb1) (nb1 nb1) (nc0 nc0-0)
    (nc1 nc1-0) (a a) (b b) (c c))
  (defstrand init 3 (na0 na0) (na1 na1) (nb0 nb1) (nb1 nb1) (nc0 nc0-0)
    (nc1 nc1-0) (a a) (b b) (c c))
  (defstrand resp 2 (na0 na0) (na1 na1) (nb0 nb1) (nb1 nb1) (nc0 nc0-1)
    (nc1 nc1-1) (a a) (b b) (c c))
  (precedes ((0 1) (1 0)) ((0 1) (3 0)) ((1 1) (2 1)) ((2 0) (0 0))
    ((2 2) (0 2)) ((3 1) (0 2)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig na0 na1 nb1 nc0-0 nc1-0 nc0-1 nc1-1)
  (operation nonce-test (added-strand resp 2) nb1 (0 2)
    (enc na1 nc1-0 c b (enc na0 nb1 b c (pubk a))
      (enc nb1 nc0-0 c a (pubk b)) (pubk a))
    (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb1 b c (pubk a))
      (pubk c))
    (enc nb1 (enc nb1 nc0-0 c a (pubk b)) (enc nc1-0 (pubk c))
      (pubk b)))
  (traces
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb1 b c (pubk a))
          (pubk c)))
      (recv
        (enc nb1 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))) (send (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb1 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1-0 c b (enc na0 nb1 b c (pubk a))
          (enc nb1 nc0-0 c a (pubk b)) (pubk a))))
    ((send (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1-0 c b (enc na0 nb1 b c (pubk a))
          (enc nb1 nc0-0 c a (pubk b)) (pubk a)))
      (send
        (enc nb1 (enc nb1 nc0-0 c a (pubk b)) (enc nc1-0 (pubk c))
          (pubk b))))
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb1 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1-1 c b (enc na0 nb1 b c (pubk a))
          (enc nb1 nc0-1 c a (pubk b)) (pubk a)))))
  (label 17)
  (parent 14)
  (unrealized (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton nsl3
  (vars (na0 na1 nb1 nc0 nc1 nc0-0 nc1-0 text) (a b c name))
  (defstrand mid 4 (na0 na0) (na1 na1) (nb0 nb1) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand resp 2 (na0 na0) (na1 na1) (nb0 nb1) (nb1 nb1) (nc0 nc0-0)
    (nc1 nc1-0) (a a) (b b) (c c))
  (defstrand init 3 (na0 na0) (na1 na1) (nb0 nb1) (nb1 nb1) (nc0 nc0-0)
    (nc1 nc1-0) (a a) (b b) (c c))
  (precedes ((0 1) (1 0)) ((1 1) (2 1)) ((2 0) (0 0)) ((2 2) (0 2)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig na0 na1 nb1 nc0-0 nc1-0)
  (operation nonce-test (added-strand init 3) nb1 (0 2)
    (enc na1 nc1-0 c b (enc na0 nb1 b c (pubk a))
      (enc nb1 nc0-0 c a (pubk b)) (pubk a))
    (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb1 b c (pubk a))
      (pubk c)))
  (traces
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb1 b c (pubk a))
          (pubk c)))
      (recv
        (enc nb1 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))) (send (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb1 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1-0 c b (enc na0 nb1 b c (pubk a))
          (enc nb1 nc0-0 c a (pubk b)) (pubk a))))
    ((send (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1-0 c b (enc na0 nb1 b c (pubk a))
          (enc nb1 nc0-0 c a (pubk b)) (pubk a)))
      (send
        (enc nb1 (enc nb1 nc0-0 c a (pubk b)) (enc nc1-0 (pubk c))
          (pubk b)))))
  (label 18)
  (parent 15)
  (seen 19)
  (unrealized (0 2))
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton nsl3
  (vars (na0 na1 nb1 nc0 nc1 text) (a b c name))
  (defstrand mid 4 (na0 na0) (na1 na1) (nb0 nb1) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand resp 2 (na0 na0) (na1 na1) (nb0 nb1) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand init 3 (na0 na0) (na1 na1) (nb0 nb1) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (precedes ((0 1) (1 0)) ((1 1) (2 1)) ((2 0) (0 0)) ((2 2) (0 2)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig na0 na1 nb1 nc0 nc1)
  (operation nonce-test
    (contracted (nc0-0 nc0) (nc1-0 nc1) (nc0-1 nc0) (nc1-1 nc1)) nb1
    (0 2)
    (enc na1 nc1 c b (enc na0 nb1 b c (pubk a))
      (enc nb1 nc0 c a (pubk b)) (pubk a))
    (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb1 b c (pubk a))
      (pubk c))
    (enc nb1 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c)) (pubk b)))
  (traces
    ((recv (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb1 b c (pubk a))
          (pubk c)))
      (recv
        (enc nb1 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))) (send (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na0 nb1 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1 c b (enc na0 nb1 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a))))
    ((send (enc na0 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na0 nb1 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb1 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b)))))
  (label 19)
  (parent 17)
  (seen 16)
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
  (label 20)
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
  (label 21)
  (parent 20)
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
  (label 22)
  (parent 21)
  (unrealized (0 0) (0 2))
  (comment "3 in cohort - 3 not yet seen"))

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
  (label 23)
  (parent 22)
  (unrealized (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton nsl3
  (vars (na0 nb0 nb1 nc0 nc1 nb0-0 nb1-0 nb0-1 nb1-1 text) (a b c name))
  (defstrand resp 3 (na0 na0) (na1 na0) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand init 3 (na0 na0) (na1 na0) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na0) (na1 na0) (nb0 nb0-0) (nb1 nb1-0) (a a)
    (b b) (c c))
  (defstrand mid 2 (na0 na0) (na1 na0) (nb0 nb0-1) (nb1 nb1-1) (a a)
    (b b) (c c))
  (precedes ((0 1) (1 1)) ((1 0) (2 0)) ((1 0) (3 0)) ((1 2) (0 2))
    ((2 1) (0 0)) ((3 1) (0 0)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig na0 nc0 nc1 nb0-0 nb1-0 nb0-1 nb1-1)
  (operation nonce-test (added-strand mid 2) na0 (0 0)
    (enc na0 a c (enc na0 a b (pubk c)) (pubk b))
    (enc nb1-0 b a (enc na0 a b (pubk c)) (enc na0 nb0-0 b c (pubk a))
      (pubk c)))
  (traces
    ((recv
       (enc nb1 b a (enc na0 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na0 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((send (enc na0 a c (enc na0 a b (pubk c)) (pubk b)))
      (recv
        (enc na0 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na0 a c (enc na0 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-0 b a (enc na0 a b (pubk c))
          (enc na0 nb0-0 b c (pubk a)) (pubk c))))
    ((recv (enc na0 a c (enc na0 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-1 b a (enc na0 a b (pubk c))
          (enc na0 nb0-1 b c (pubk a)) (pubk c)))))
  (label 24)
  (parent 22)
  (unrealized (0 0) (0 2))
  (comment "2 in cohort - 2 not yet seen"))

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
  (label 25)
  (parent 22)
  (unrealized (0 0) (0 2))
  (comment "3 in cohort - 3 not yet seen"))

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
  (label 26)
  (parent 23)
  (unrealized (2 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton nsl3
  (vars (na0 nc0 nc1 nb0 nb1 text) (a b c name))
  (defstrand resp 3 (na0 na0) (na1 na0) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand init 3 (na0 na0) (na1 na0) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na0) (na1 na0) (nb0 nb0) (nb1 nb1) (a a) (b b)
    (c c))
  (precedes ((0 1) (1 1)) ((1 0) (2 0)) ((1 2) (0 2)) ((2 1) (0 0)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig na0 nc0 nc1 nb0 nb1)
  (operation nonce-test
    (contracted (nb0-0 nb0) (nb1-0 nb1) (nb0-1 nb0) (nb1-1 nb1)) na0
    (0 0) (enc na0 a c (enc na0 a b (pubk c)) (pubk b))
    (enc nb1 b a (enc na0 a b (pubk c)) (enc na0 nb0 b c (pubk a))
      (pubk c)))
  (traces
    ((recv
       (enc nb1 b a (enc na0 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na0 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((send (enc na0 a c (enc na0 a b (pubk c)) (pubk b)))
      (recv
        (enc na0 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na0 a c (enc na0 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na0 a b (pubk c)) (enc na0 nb0 b c (pubk a))
          (pubk c)))))
  (label 27)
  (parent 24)
  (unrealized (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton nsl3
  (vars (na0 nb0 nb1 nc0 nc1 nb0-0 nb1-0 nc0-0 nc1-0 text) (a b c name))
  (defstrand resp 3 (na0 na0) (na1 na0) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand init 3 (na0 na0) (na1 na0) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na0) (na1 na0) (nb0 nb0-0) (nb1 nb1-0) (a a)
    (b b) (c c))
  (defstrand resp 2 (na0 na0) (na1 na0) (nb0 nb0-0) (nb1 nb1-0)
    (nc0 nc0-0) (nc1 nc1-0) (a a) (b b) (c c))
  (precedes ((0 1) (1 1)) ((1 0) (2 0)) ((1 2) (0 2)) ((2 1) (3 0))
    ((3 1) (0 0)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig na0 nc0 nc1 nb0-0 nb1-0 nc0-0 nc1-0)
  (operation nonce-test (added-strand resp 2) na0 (0 0)
    (enc na0 a c (enc na0 a b (pubk c)) (pubk b))
    (enc nb1-0 b a (enc na0 a b (pubk c)) (enc na0 nb0-0 b c (pubk a))
      (pubk c)))
  (traces
    ((recv
       (enc nb1 b a (enc na0 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na0 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((send (enc na0 a c (enc na0 a b (pubk c)) (pubk b)))
      (recv
        (enc na0 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na0 a c (enc na0 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-0 b a (enc na0 a b (pubk c))
          (enc na0 nb0-0 b c (pubk a)) (pubk c))))
    ((recv
       (enc nb1-0 b a (enc na0 a b (pubk c))
         (enc na0 nb0-0 b c (pubk a)) (pubk c)))
      (send
        (enc na0 nc1-0 c b (enc na0 nb0-0 b c (pubk a))
          (enc nb1-0 nc0-0 c a (pubk b)) (pubk a)))))
  (label 28)
  (parent 24)
  (unrealized (0 0) (0 2))
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
  (label 29)
  (parent 25)
  (unrealized (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton nsl3
  (vars (na0 nb0 nb1 nc0 nc1 nb0-0 nb1-0 nc0-0 nc1-0 nb0-1 nb1-1 text)
    (a b c name))
  (defstrand resp 3 (na0 na0) (na1 na0) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand init 3 (na0 na0) (na1 na0) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na0) (na1 na0) (nb0 nb0-0) (nb1 nb1-0) (a a)
    (b b) (c c))
  (defstrand resp 2 (na0 na0) (na1 na0) (nb0 nb0-0) (nb1 nb1-0)
    (nc0 nc0-0) (nc1 nc1-0) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na0) (na1 na0) (nb0 nb0-1) (nb1 nb1-1) (a a)
    (b b) (c c))
  (precedes ((0 1) (1 1)) ((1 0) (2 0)) ((1 0) (4 0)) ((1 2) (0 2))
    ((2 1) (3 0)) ((3 1) (0 0)) ((4 1) (0 0)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig na0 nc0 nc1 nb0-0 nb1-0 nc0-0 nc1-0 nb0-1 nb1-1)
  (operation nonce-test (added-strand mid 2) na0 (0 0)
    (enc na0 nc1-0 c b (enc na0 nb0-0 b c (pubk a))
      (enc nb1-0 nc0-0 c a (pubk b)) (pubk a))
    (enc na0 a c (enc na0 a b (pubk c)) (pubk b))
    (enc nb1-0 b a (enc na0 a b (pubk c)) (enc na0 nb0-0 b c (pubk a))
      (pubk c)))
  (traces
    ((recv
       (enc nb1 b a (enc na0 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na0 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((send (enc na0 a c (enc na0 a b (pubk c)) (pubk b)))
      (recv
        (enc na0 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na0 a c (enc na0 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-0 b a (enc na0 a b (pubk c))
          (enc na0 nb0-0 b c (pubk a)) (pubk c))))
    ((recv
       (enc nb1-0 b a (enc na0 a b (pubk c))
         (enc na0 nb0-0 b c (pubk a)) (pubk c)))
      (send
        (enc na0 nc1-0 c b (enc na0 nb0-0 b c (pubk a))
          (enc nb1-0 nc0-0 c a (pubk b)) (pubk a))))
    ((recv (enc na0 a c (enc na0 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-1 b a (enc na0 a b (pubk c))
          (enc na0 nb0-1 b c (pubk a)) (pubk c)))))
  (label 30)
  (parent 25)
  (unrealized (0 0) (0 2))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton nsl3
  (vars (na0 nb0 nb1 nc0 nc1 nb0-0 nb1-0 nc0-0 nc1-0 nc0-1 nc1-1 text)
    (a b c name))
  (defstrand resp 3 (na0 na0) (na1 na0) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand init 3 (na0 na0) (na1 na0) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na0) (na1 na0) (nb0 nb0-0) (nb1 nb1-0) (a a)
    (b b) (c c))
  (defstrand resp 2 (na0 na0) (na1 na0) (nb0 nb0-0) (nb1 nb1-0)
    (nc0 nc0-0) (nc1 nc1-0) (a a) (b b) (c c))
  (defstrand resp 2 (na0 na0) (na1 na0) (nb0 nb0-0) (nb1 nb1-0)
    (nc0 nc0-1) (nc1 nc1-1) (a a) (b b) (c c))
  (precedes ((0 1) (1 1)) ((1 0) (2 0)) ((1 2) (0 2)) ((2 1) (3 0))
    ((2 1) (4 0)) ((3 1) (0 0)) ((4 1) (0 0)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig na0 nc0 nc1 nb0-0 nb1-0 nc0-0 nc1-0 nc0-1 nc1-1)
  (operation nonce-test (added-strand resp 2) na0 (0 0)
    (enc na0 nc1-0 c b (enc na0 nb0-0 b c (pubk a))
      (enc nb1-0 nc0-0 c a (pubk b)) (pubk a))
    (enc na0 a c (enc na0 a b (pubk c)) (pubk b))
    (enc nb1-0 b a (enc na0 a b (pubk c)) (enc na0 nb0-0 b c (pubk a))
      (pubk c)))
  (traces
    ((recv
       (enc nb1 b a (enc na0 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na0 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((send (enc na0 a c (enc na0 a b (pubk c)) (pubk b)))
      (recv
        (enc na0 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na0 a c (enc na0 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-0 b a (enc na0 a b (pubk c))
          (enc na0 nb0-0 b c (pubk a)) (pubk c))))
    ((recv
       (enc nb1-0 b a (enc na0 a b (pubk c))
         (enc na0 nb0-0 b c (pubk a)) (pubk c)))
      (send
        (enc na0 nc1-0 c b (enc na0 nb0-0 b c (pubk a))
          (enc nb1-0 nc0-0 c a (pubk b)) (pubk a))))
    ((recv
       (enc nb1-0 b a (enc na0 a b (pubk c))
         (enc na0 nb0-0 b c (pubk a)) (pubk c)))
      (send
        (enc na0 nc1-1 c b (enc na0 nb0-0 b c (pubk a))
          (enc nb1-0 nc0-1 c a (pubk b)) (pubk a)))))
  (label 31)
  (parent 25)
  (seen 34)
  (unrealized (0 0) (0 2))
  (comment "1 in cohort - 0 not yet seen"))

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
  (label 32)
  (parent 26)
  (unrealized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (c c) (na0 na0) (na1 na1) (nb0 nb0) (nb1 nb1)
        (nc0 nc0) (nc1 nc1))))
  (origs (na0 (1 0)) (na1 (1 0)) (nb0 (2 1)) (nb1 (2 1)) (nc1 (0 1))
    (nc0 (0 1))))

(defskeleton nsl3
  (vars (nc0 nc1 nb0 nb1 na1 text) (a b c name))
  (defstrand resp 3 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand init 3 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 4 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (precedes ((0 1) (1 1)) ((0 1) (2 2)) ((1 0) (2 0)) ((1 2) (0 2))
    ((2 1) (0 0)) ((2 3) (0 2)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig nc0 nc1 nb0 nb1 na1)
  (operation nonce-test (displaced 2 3 mid 4) nc0 (0 2)
    (enc na0 nc1 c b (enc na0 nb0 b c (pubk a))
      (enc nb1 nc0 c a (pubk b)) (pubk a))
    (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c)) (pubk b)))
  (traces
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na1 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1 c b (enc na1 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((send (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na1 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na1 nb0 b c (pubk a))
          (pubk c)))
      (recv
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))) (send (enc nc0 (enc nc1 (pubk c)) (pubk c)))))
  (label 33)
  (parent 27)
  (unrealized (2 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton nsl3
  (vars (na0 nc0 nc1 nb0 nb1 nc0-0 nc1-0 text) (a b c name))
  (defstrand resp 3 (na0 na0) (na1 na0) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand init 3 (na0 na0) (na1 na0) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na0) (na1 na0) (nb0 nb0) (nb1 nb1) (a a) (b b)
    (c c))
  (defstrand resp 2 (na0 na0) (na1 na0) (nb0 nb0) (nb1 nb1) (nc0 nc0-0)
    (nc1 nc1-0) (a a) (b b) (c c))
  (precedes ((0 1) (1 1)) ((1 0) (2 0)) ((1 2) (0 2)) ((2 1) (3 0))
    ((3 1) (0 0)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig na0 nc0 nc1 nb0 nb1 nc0-0 nc1-0)
  (operation nonce-test (contracted (nb0-0 nb0) (nb1-0 nb1)) na0 (0 0)
    (enc na0 nc1-0 c b (enc na0 nb0 b c (pubk a))
      (enc nb1 nc0-0 c a (pubk b)) (pubk a))
    (enc na0 a c (enc na0 a b (pubk c)) (pubk b))
    (enc nb1 b a (enc na0 a b (pubk c)) (enc na0 nb0 b c (pubk a))
      (pubk c)))
  (traces
    ((recv
       (enc nb1 b a (enc na0 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na0 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((send (enc na0 a c (enc na0 a b (pubk c)) (pubk b)))
      (recv
        (enc na0 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na0 a c (enc na0 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na0 a b (pubk c)) (enc na0 nb0 b c (pubk a))
          (pubk c))))
    ((recv
       (enc nb1 b a (enc na0 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na0 nc1-0 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0-0 c a (pubk b)) (pubk a)))))
  (label 34)
  (parent 28)
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
  (label 35)
  (parent 29)
  (unrealized (3 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton nsl3
  (vars (na0 nc0 nc1 nb0 nb1 nc0-0 nc1-0 nb0-0 nb1-0 text) (a b c name))
  (defstrand resp 3 (na0 na0) (na1 na0) (nb0 nb0-0) (nb1 nb1-0)
    (nc0 nc0) (nc1 nc1) (a a) (b b) (c c))
  (defstrand init 3 (na0 na0) (na1 na0) (nb0 nb0-0) (nb1 nb1-0)
    (nc0 nc0) (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na0) (na1 na0) (nb0 nb0) (nb1 nb1) (a a) (b b)
    (c c))
  (defstrand resp 2 (na0 na0) (na1 na0) (nb0 nb0) (nb1 nb1) (nc0 nc0-0)
    (nc1 nc1-0) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na0) (na1 na0) (nb0 nb0-0) (nb1 nb1-0) (a a)
    (b b) (c c))
  (precedes ((0 1) (1 1)) ((1 0) (2 0)) ((1 0) (4 0)) ((1 2) (0 2))
    ((2 1) (3 0)) ((3 1) (0 0)) ((4 1) (0 0)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig na0 nc0 nc1 nb0 nb1 nc0-0 nc1-0 nb0-0 nb1-0)
  (operation nonce-test (contracted (nb0-1 nb0-0) (nb1-1 nb1-0)) na0
    (0 0)
    (enc na0 nc1-0 c b (enc na0 nb0 b c (pubk a))
      (enc nb1 nc0-0 c a (pubk b)) (pubk a))
    (enc na0 a c (enc na0 a b (pubk c)) (pubk b))
    (enc nb1 b a (enc na0 a b (pubk c)) (enc na0 nb0 b c (pubk a))
      (pubk c))
    (enc nb1-0 b a (enc na0 a b (pubk c)) (enc na0 nb0-0 b c (pubk a))
      (pubk c)))
  (traces
    ((recv
       (enc nb1-0 b a (enc na0 a b (pubk c))
         (enc na0 nb0-0 b c (pubk a)) (pubk c)))
      (send
        (enc na0 nc1 c b (enc na0 nb0-0 b c (pubk a))
          (enc nb1-0 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((send (enc na0 a c (enc na0 a b (pubk c)) (pubk b)))
      (recv
        (enc na0 nc1 c b (enc na0 nb0-0 b c (pubk a))
          (enc nb1-0 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0-0 (enc nb1-0 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na0 a c (enc na0 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na0 a b (pubk c)) (enc na0 nb0 b c (pubk a))
          (pubk c))))
    ((recv
       (enc nb1 b a (enc na0 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na0 nc1-0 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0-0 c a (pubk b)) (pubk a))))
    ((recv (enc na0 a c (enc na0 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-0 b a (enc na0 a b (pubk c))
          (enc na0 nb0-0 b c (pubk a)) (pubk c)))))
  (label 36)
  (parent 30)
  (unrealized (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton nsl3
  (vars
    (na0 nb0 nb1 nc0 nc1 nb0-0 nb1-0 nc0-0 nc1-0 nb0-1 nb1-1 nc0-1 nc1-1
      text) (a b c name))
  (defstrand resp 3 (na0 na0) (na1 na0) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand init 3 (na0 na0) (na1 na0) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na0) (na1 na0) (nb0 nb0-0) (nb1 nb1-0) (a a)
    (b b) (c c))
  (defstrand resp 2 (na0 na0) (na1 na0) (nb0 nb0-0) (nb1 nb1-0)
    (nc0 nc0-0) (nc1 nc1-0) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na0) (na1 na0) (nb0 nb0-1) (nb1 nb1-1) (a a)
    (b b) (c c))
  (defstrand resp 2 (na0 na0) (na1 na0) (nb0 nb0-1) (nb1 nb1-1)
    (nc0 nc0-1) (nc1 nc1-1) (a a) (b b) (c c))
  (precedes ((0 1) (1 1)) ((1 0) (2 0)) ((1 0) (4 0)) ((1 2) (0 2))
    ((2 1) (3 0)) ((3 1) (0 0)) ((4 1) (5 0)) ((5 1) (0 0)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig na0 nc0 nc1 nb0-0 nb1-0 nc0-0 nc1-0 nb0-1 nb1-1 nc0-1
    nc1-1)
  (operation nonce-test (added-strand resp 2) na0 (0 0)
    (enc na0 nc1-0 c b (enc na0 nb0-0 b c (pubk a))
      (enc nb1-0 nc0-0 c a (pubk b)) (pubk a))
    (enc na0 a c (enc na0 a b (pubk c)) (pubk b))
    (enc nb1-0 b a (enc na0 a b (pubk c)) (enc na0 nb0-0 b c (pubk a))
      (pubk c))
    (enc nb1-1 b a (enc na0 a b (pubk c)) (enc na0 nb0-1 b c (pubk a))
      (pubk c)))
  (traces
    ((recv
       (enc nb1 b a (enc na0 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na0 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((send (enc na0 a c (enc na0 a b (pubk c)) (pubk b)))
      (recv
        (enc na0 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na0 a c (enc na0 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-0 b a (enc na0 a b (pubk c))
          (enc na0 nb0-0 b c (pubk a)) (pubk c))))
    ((recv
       (enc nb1-0 b a (enc na0 a b (pubk c))
         (enc na0 nb0-0 b c (pubk a)) (pubk c)))
      (send
        (enc na0 nc1-0 c b (enc na0 nb0-0 b c (pubk a))
          (enc nb1-0 nc0-0 c a (pubk b)) (pubk a))))
    ((recv (enc na0 a c (enc na0 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-1 b a (enc na0 a b (pubk c))
          (enc na0 nb0-1 b c (pubk a)) (pubk c))))
    ((recv
       (enc nb1-1 b a (enc na0 a b (pubk c))
         (enc na0 nb0-1 b c (pubk a)) (pubk c)))
      (send
        (enc na0 nc1-1 c b (enc na0 nb0-1 b c (pubk a))
          (enc nb1-1 nc0-1 c a (pubk b)) (pubk a)))))
  (label 37)
  (parent 30)
  (seen 42)
  (unrealized (0 0) (0 2))
  (comment "2 in cohort - 1 not yet seen"))

(defskeleton nsl3
  (vars (nc0 nc1 nb0 nb1 na1 text) (a b c name))
  (defstrand resp 3 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand init 3 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 4 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (precedes ((0 1) (1 1)) ((1 0) (2 0)) ((1 2) (2 2)) ((2 1) (0 0))
    ((2 3) (0 2)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig nc0 nc1 nb0 nb1 na1)
  (operation nonce-test (displaced 3 1 init 3) nc0 (2 2)
    (enc na1 nc1 c b (enc na1 nb0 b c (pubk a))
      (enc nb1 nc0 c a (pubk b)) (pubk a)))
  (traces
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na1 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1 c b (enc na1 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((send (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na1 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na1 nb0 b c (pubk a))
          (pubk c)))
      (recv
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))) (send (enc nc0 (enc nc1 (pubk c)) (pubk c)))))
  (label 38)
  (parent 33)
  (seen 32)
  (unrealized)
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton nsl3
  (vars (nc0 nc1 nb0 nb1 nc0-0 nc1-0 na1 text) (a b c name))
  (defstrand resp 3 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand init 3 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand resp 2 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0-0)
    (nc1 nc1-0) (a a) (b b) (c c))
  (defstrand mid 4 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (precedes ((0 1) (1 1)) ((0 1) (3 2)) ((1 0) (3 0)) ((1 2) (0 2))
    ((2 1) (0 0)) ((3 1) (2 0)) ((3 3) (0 2)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig nc0 nc1 nb0 nb1 nc0-0 nc1-0 na1)
  (operation nonce-test (displaced 2 4 mid 4) nc0 (0 2)
    (enc na0 nc1 c b (enc na0 nb0 b c (pubk a))
      (enc nb1 nc0 c a (pubk b)) (pubk a))
    (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c)) (pubk b)))
  (traces
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na1 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1 c b (enc na1 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((send (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na1 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na1 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1-0 c b (enc na1 nb0 b c (pubk a))
          (enc nb1 nc0-0 c a (pubk b)) (pubk a))))
    ((recv (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na1 nb0 b c (pubk a))
          (pubk c)))
      (recv
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))) (send (enc nc0 (enc nc1 (pubk c)) (pubk c)))))
  (label 39)
  (parent 34)
  (unrealized (3 2))
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
  (label 40)
  (parent 35)
  (seen 32)
  (unrealized)
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton nsl3
  (vars (nc0 nc1 nb0 nb1 nc0-0 nc1-0 nb0-0 nb1-0 na1 text) (a b c name))
  (defstrand resp 3 (na0 na1) (na1 na1) (nb0 nb0-0) (nb1 nb1-0)
    (nc0 nc0) (nc1 nc1) (a a) (b b) (c c))
  (defstrand init 3 (na0 na1) (na1 na1) (nb0 nb0-0) (nb1 nb1-0)
    (nc0 nc0) (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (a a) (b b)
    (c c))
  (defstrand resp 2 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0-0)
    (nc1 nc1-0) (a a) (b b) (c c))
  (defstrand mid 4 (na0 na1) (na1 na1) (nb0 nb0-0) (nb1 nb1-0) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (precedes ((0 1) (1 1)) ((0 1) (4 2)) ((1 0) (2 0)) ((1 0) (4 0))
    ((1 2) (0 2)) ((2 1) (3 0)) ((3 1) (0 0)) ((4 1) (0 0))
    ((4 3) (0 2)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig nc0 nc1 nb0 nb1 nc0-0 nc1-0 nb0-0 nb1-0 na1)
  (operation nonce-test (displaced 4 5 mid 4) nc0 (0 2)
    (enc na0 nc1 c b (enc na0 nb0-0 b c (pubk a))
      (enc nb1-0 nc0 c a (pubk b)) (pubk a))
    (enc nb0-0 (enc nb1-0 nc0 c a (pubk b)) (enc nc1 (pubk c))
      (pubk b)))
  (traces
    ((recv
       (enc nb1-0 b a (enc na1 a b (pubk c))
         (enc na1 nb0-0 b c (pubk a)) (pubk c)))
      (send
        (enc na1 nc1 c b (enc na1 nb0-0 b c (pubk a))
          (enc nb1-0 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((send (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na1 nb0-0 b c (pubk a))
          (enc nb1-0 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0-0 (enc nb1-0 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na1 nb0 b c (pubk a))
          (pubk c))))
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na1 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1-0 c b (enc na1 nb0 b c (pubk a))
          (enc nb1 nc0-0 c a (pubk b)) (pubk a))))
    ((recv (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-0 b a (enc na1 a b (pubk c))
          (enc na1 nb0-0 b c (pubk a)) (pubk c)))
      (recv
        (enc nb0-0 (enc nb1-0 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))) (send (enc nc0 (enc nc1 (pubk c)) (pubk c)))))
  (label 41)
  (parent 36)
  (unrealized (4 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton nsl3
  (vars (na0 nc0 nc1 nb0 nb1 nc0-0 nc1-0 nb0-0 nb1-0 nc0-1 nc1-1 text)
    (a b c name))
  (defstrand resp 3 (na0 na0) (na1 na0) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand init 3 (na0 na0) (na1 na0) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na0) (na1 na0) (nb0 nb0) (nb1 nb1) (a a) (b b)
    (c c))
  (defstrand resp 2 (na0 na0) (na1 na0) (nb0 nb0) (nb1 nb1) (nc0 nc0-0)
    (nc1 nc1-0) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na0) (na1 na0) (nb0 nb0-0) (nb1 nb1-0) (a a)
    (b b) (c c))
  (defstrand resp 2 (na0 na0) (na1 na0) (nb0 nb0-0) (nb1 nb1-0)
    (nc0 nc0-1) (nc1 nc1-1) (a a) (b b) (c c))
  (precedes ((0 1) (1 1)) ((1 0) (2 0)) ((1 0) (4 0)) ((1 2) (0 2))
    ((2 1) (3 0)) ((3 1) (0 0)) ((4 1) (5 0)) ((5 1) (0 0)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig na0 nc0 nc1 nb0 nb1 nc0-0 nc1-0 nb0-0 nb1-0 nc0-1 nc1-1)
  (operation nonce-test (contracted (nb0-1 nb0) (nb1-1 nb1)) na0 (0 0)
    (enc na0 nc1-0 c b (enc na0 nb0 b c (pubk a))
      (enc nb1 nc0-0 c a (pubk b)) (pubk a))
    (enc na0 nc1-1 c b (enc na0 nb0-0 b c (pubk a))
      (enc nb1-0 nc0-1 c a (pubk b)) (pubk a))
    (enc na0 a c (enc na0 a b (pubk c)) (pubk b))
    (enc nb1 b a (enc na0 a b (pubk c)) (enc na0 nb0 b c (pubk a))
      (pubk c))
    (enc nb1-0 b a (enc na0 a b (pubk c)) (enc na0 nb0-0 b c (pubk a))
      (pubk c)))
  (traces
    ((recv
       (enc nb1 b a (enc na0 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na0 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((send (enc na0 a c (enc na0 a b (pubk c)) (pubk b)))
      (recv
        (enc na0 nc1 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na0 a c (enc na0 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na0 a b (pubk c)) (enc na0 nb0 b c (pubk a))
          (pubk c))))
    ((recv
       (enc nb1 b a (enc na0 a b (pubk c)) (enc na0 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na0 nc1-0 c b (enc na0 nb0 b c (pubk a))
          (enc nb1 nc0-0 c a (pubk b)) (pubk a))))
    ((recv (enc na0 a c (enc na0 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-0 b a (enc na0 a b (pubk c))
          (enc na0 nb0-0 b c (pubk a)) (pubk c))))
    ((recv
       (enc nb1-0 b a (enc na0 a b (pubk c))
         (enc na0 nb0-0 b c (pubk a)) (pubk c)))
      (send
        (enc na0 nc1-1 c b (enc na0 nb0-0 b c (pubk a))
          (enc nb1-0 nc0-1 c a (pubk b)) (pubk a)))))
  (label 42)
  (parent 37)
  (unrealized (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton nsl3
  (vars (nc0 nc1 nb0 nb1 nc0-0 nc1-0 na1 text) (a b c name))
  (defstrand resp 3 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand init 3 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand resp 2 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0-0)
    (nc1 nc1-0) (a a) (b b) (c c))
  (defstrand mid 4 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (precedes ((0 1) (1 1)) ((1 0) (3 0)) ((1 2) (3 2)) ((2 1) (0 0))
    ((3 1) (2 0)) ((3 3) (0 2)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig nc0 nc1 nb0 nb1 nc0-0 nc1-0 na1)
  (operation nonce-test (displaced 4 1 init 3) nc0 (3 2)
    (enc na1 nc1 c b (enc na1 nb0 b c (pubk a))
      (enc nb1 nc0 c a (pubk b)) (pubk a)))
  (traces
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na1 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1 c b (enc na1 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((send (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na1 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na1 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1-0 c b (enc na1 nb0 b c (pubk a))
          (enc nb1 nc0-0 c a (pubk b)) (pubk a))))
    ((recv (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na1 nb0 b c (pubk a))
          (pubk c)))
      (recv
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))) (send (enc nc0 (enc nc1 (pubk c)) (pubk c)))))
  (label 43)
  (parent 39)
  (seen 38)
  (unrealized)
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton nsl3
  (vars (nc0 nc1 nb0 nb1 nc0-0 nc1-0 nb0-0 nb1-0 na1 text) (a b c name))
  (defstrand resp 3 (na0 na1) (na1 na1) (nb0 nb0-0) (nb1 nb1-0)
    (nc0 nc0) (nc1 nc1) (a a) (b b) (c c))
  (defstrand init 3 (na0 na1) (na1 na1) (nb0 nb0-0) (nb1 nb1-0)
    (nc0 nc0) (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (a a) (b b)
    (c c))
  (defstrand resp 2 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0-0)
    (nc1 nc1-0) (a a) (b b) (c c))
  (defstrand mid 4 (na0 na1) (na1 na1) (nb0 nb0-0) (nb1 nb1-0) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (precedes ((0 1) (1 1)) ((1 0) (2 0)) ((1 0) (4 0)) ((1 2) (4 2))
    ((2 1) (3 0)) ((3 1) (0 0)) ((4 1) (0 0)) ((4 3) (0 2)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig nc0 nc1 nb0 nb1 nc0-0 nc1-0 nb0-0 nb1-0 na1)
  (operation nonce-test (displaced 5 1 init 3) nc0 (4 2)
    (enc na1 nc1 c b (enc na1 nb0-0 b c (pubk a))
      (enc nb1-0 nc0 c a (pubk b)) (pubk a)))
  (traces
    ((recv
       (enc nb1-0 b a (enc na1 a b (pubk c))
         (enc na1 nb0-0 b c (pubk a)) (pubk c)))
      (send
        (enc na1 nc1 c b (enc na1 nb0-0 b c (pubk a))
          (enc nb1-0 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((send (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na1 nb0-0 b c (pubk a))
          (enc nb1-0 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0-0 (enc nb1-0 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na1 nb0 b c (pubk a))
          (pubk c))))
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na1 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1-0 c b (enc na1 nb0 b c (pubk a))
          (enc nb1 nc0-0 c a (pubk b)) (pubk a))))
    ((recv (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-0 b a (enc na1 a b (pubk c))
          (enc na1 nb0-0 b c (pubk a)) (pubk c)))
      (recv
        (enc nb0-0 (enc nb1-0 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))) (send (enc nc0 (enc nc1 (pubk c)) (pubk c)))))
  (label 44)
  (parent 41)
  (unrealized)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton nsl3
  (vars (nc0 nc1 nb0 nb1 nc0-0 nc1-0 nb0-0 nb1-0 nc0-1 nc1-1 na1 text)
    (a b c name))
  (defstrand resp 3 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand init 3 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand resp 2 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0-0)
    (nc1 nc1-0) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na1) (na1 na1) (nb0 nb0-0) (nb1 nb1-0) (a a)
    (b b) (c c))
  (defstrand resp 2 (na0 na1) (na1 na1) (nb0 nb0-0) (nb1 nb1-0)
    (nc0 nc0-1) (nc1 nc1-1) (a a) (b b) (c c))
  (defstrand mid 4 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (precedes ((0 1) (1 1)) ((0 1) (5 2)) ((1 0) (3 0)) ((1 0) (5 0))
    ((1 2) (0 2)) ((2 1) (0 0)) ((3 1) (4 0)) ((4 1) (0 0))
    ((5 1) (2 0)) ((5 3) (0 2)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig nc0 nc1 nb0 nb1 nc0-0 nc1-0 nb0-0 nb1-0 nc0-1 nc1-1 na1)
  (operation nonce-test (displaced 2 6 mid 4) nc0 (0 2)
    (enc na0 nc1 c b (enc na0 nb0 b c (pubk a))
      (enc nb1 nc0 c a (pubk b)) (pubk a))
    (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c)) (pubk b)))
  (traces
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na1 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1 c b (enc na1 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((send (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na1 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na1 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1-0 c b (enc na1 nb0 b c (pubk a))
          (enc nb1 nc0-0 c a (pubk b)) (pubk a))))
    ((recv (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-0 b a (enc na1 a b (pubk c))
          (enc na1 nb0-0 b c (pubk a)) (pubk c))))
    ((recv
       (enc nb1-0 b a (enc na1 a b (pubk c))
         (enc na1 nb0-0 b c (pubk a)) (pubk c)))
      (send
        (enc na1 nc1-1 c b (enc na1 nb0-0 b c (pubk a))
          (enc nb1-0 nc0-1 c a (pubk b)) (pubk a))))
    ((recv (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na1 nb0 b c (pubk a))
          (pubk c)))
      (recv
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))) (send (enc nc0 (enc nc1 (pubk c)) (pubk c)))))
  (label 45)
  (parent 42)
  (unrealized (5 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton nsl3
  (vars (nc0 nc1 nb0 nb1 nb0-0 nb1-0 na1 text) (a b c name))
  (defstrand resp 3 (na0 na1) (na1 na1) (nb0 nb0-0) (nb1 nb1-0)
    (nc0 nc0) (nc1 nc1) (a a) (b b) (c c))
  (defstrand init 3 (na0 na1) (na1 na1) (nb0 nb0-0) (nb1 nb1-0)
    (nc0 nc0) (nc1 nc1) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (a a) (b b)
    (c c))
  (defstrand mid 4 (na0 na1) (na1 na1) (nb0 nb0-0) (nb1 nb1-0) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (precedes ((0 1) (1 1)) ((1 0) (2 0)) ((1 0) (3 0)) ((1 2) (3 2))
    ((2 1) (0 0)) ((3 1) (0 0)) ((3 3) (0 2)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig nc0 nc1 nb0 nb1 nb0-0 nb1-0 na1)
  (operation generalization deleted (3 0))
  (traces
    ((recv
       (enc nb1-0 b a (enc na1 a b (pubk c))
         (enc na1 nb0-0 b c (pubk a)) (pubk c)))
      (send
        (enc na1 nc1 c b (enc na1 nb0-0 b c (pubk a))
          (enc nb1-0 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((send (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na1 nb0-0 b c (pubk a))
          (enc nb1-0 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0-0 (enc nb1-0 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na1 nb0 b c (pubk a))
          (pubk c))))
    ((recv (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-0 b a (enc na1 a b (pubk c))
          (enc na1 nb0-0 b c (pubk a)) (pubk c)))
      (recv
        (enc nb0-0 (enc nb1-0 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))) (send (enc nc0 (enc nc1 (pubk c)) (pubk c)))))
  (label 46)
  (parent 44)
  (seen 38)
  (unrealized)
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton nsl3
  (vars (nc0 nc1 nb0 nb1 nc0-0 nc1-0 nb0-0 nb1-0 nc0-1 nc1-1 na1 text)
    (a b c name))
  (defstrand resp 3 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand init 3 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (defstrand resp 2 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0-0)
    (nc1 nc1-0) (a a) (b b) (c c))
  (defstrand mid 2 (na0 na1) (na1 na1) (nb0 nb0-0) (nb1 nb1-0) (a a)
    (b b) (c c))
  (defstrand resp 2 (na0 na1) (na1 na1) (nb0 nb0-0) (nb1 nb1-0)
    (nc0 nc0-1) (nc1 nc1-1) (a a) (b b) (c c))
  (defstrand mid 4 (na0 na1) (na1 na1) (nb0 nb0) (nb1 nb1) (nc0 nc0)
    (nc1 nc1) (a a) (b b) (c c))
  (precedes ((0 1) (1 1)) ((1 0) (3 0)) ((1 0) (5 0)) ((1 2) (5 2))
    ((2 1) (0 0)) ((3 1) (4 0)) ((4 1) (0 0)) ((5 1) (2 0))
    ((5 3) (0 2)))
  (non-orig (privk a) (privk b) (privk c))
  (uniq-orig nc0 nc1 nb0 nb1 nc0-0 nc1-0 nb0-0 nb1-0 nc0-1 nc1-1 na1)
  (operation nonce-test (displaced 6 1 init 3) nc0 (5 2)
    (enc na1 nc1 c b (enc na1 nb0 b c (pubk a))
      (enc nb1 nc0 c a (pubk b)) (pubk a)))
  (traces
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na1 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1 c b (enc na1 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (recv (enc nc0 (enc nc1 (pubk c)) (pubk c))))
    ((send (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (recv
        (enc na1 nc1 c b (enc na1 nb0 b c (pubk a))
          (enc nb1 nc0 c a (pubk b)) (pubk a)))
      (send
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))))
    ((recv
       (enc nb1 b a (enc na1 a b (pubk c)) (enc na1 nb0 b c (pubk a))
         (pubk c)))
      (send
        (enc na1 nc1-0 c b (enc na1 nb0 b c (pubk a))
          (enc nb1 nc0-0 c a (pubk b)) (pubk a))))
    ((recv (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1-0 b a (enc na1 a b (pubk c))
          (enc na1 nb0-0 b c (pubk a)) (pubk c))))
    ((recv
       (enc nb1-0 b a (enc na1 a b (pubk c))
         (enc na1 nb0-0 b c (pubk a)) (pubk c)))
      (send
        (enc na1 nc1-1 c b (enc na1 nb0-0 b c (pubk a))
          (enc nb1-0 nc0-1 c a (pubk b)) (pubk a))))
    ((recv (enc na1 a c (enc na1 a b (pubk c)) (pubk b)))
      (send
        (enc nb1 b a (enc na1 a b (pubk c)) (enc na1 nb0 b c (pubk a))
          (pubk c)))
      (recv
        (enc nb0 (enc nb1 nc0 c a (pubk b)) (enc nc1 (pubk c))
          (pubk b))) (send (enc nc0 (enc nc1 (pubk c)) (pubk c)))))
  (label 47)
  (parent 45)
  (seen 44)
  (unrealized)
  (comment "1 in cohort - 0 not yet seen"))

(comment "Nothing left to do")
