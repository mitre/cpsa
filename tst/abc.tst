(comment "CPSA 4.2.3")
(comment "All input read from tst/abc.scm")

(defprotocol abc basic
  (defrole init
    (vars (x text) (k skey))
    (trace (send (enc x k)) (recv (enc x x k)))
    (non-orig k)
    (uniq-orig x))
  (defrole A
    (vars (x text) (k skey))
    (trace (recv (enc "A" x k)) (send (enc x x k))))
  (defrole B
    (vars (x text) (k skey))
    (trace (recv (enc "B" x k)) (send (enc x x k))))
  (defrole C
    (vars (x text) (k skey))
    (trace (recv (enc "C" x k)) (send (enc x x k)))))

(defskeleton abc
  (vars (x text) (k skey))
  (defstrand init 2 (x x) (k k))
  (non-orig k)
  (uniq-orig x)
  (traces ((send (enc x k)) (recv (enc x x k))))
  (label 0)
  (unrealized (0 1))
  (origs (x (0 0)))
  (comment "3 in cohort - 3 not yet seen"))

(defskeleton abc
  (vars (x text) (k skey))
  (defstrand init 2 (x x) (k k))
  (defstrand A 2 (x x) (k k))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig k)
  (uniq-orig x)
  (operation encryption-test (added-strand A 2) (enc x x k) (0 1))
  (traces ((send (enc x k)) (recv (enc x x k)))
    ((recv (enc "A" x k)) (send (enc x x k))))
  (label 1)
  (parent 0)
  (unrealized (1 0))
  (dead)
  (comment "empty cohort"))

(defskeleton abc
  (vars (x text) (k skey))
  (defstrand init 2 (x x) (k k))
  (defstrand B 2 (x x) (k k))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig k)
  (uniq-orig x)
  (operation encryption-test (added-strand B 2) (enc x x k) (0 1))
  (traces ((send (enc x k)) (recv (enc x x k)))
    ((recv (enc "B" x k)) (send (enc x x k))))
  (label 2)
  (parent 0)
  (unrealized (1 0))
  (dead)
  (comment "empty cohort"))

(defskeleton abc
  (vars (x text) (k skey))
  (defstrand init 2 (x x) (k k))
  (defstrand C 2 (x x) (k k))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig k)
  (uniq-orig x)
  (operation encryption-test (added-strand C 2) (enc x x k) (0 1))
  (traces ((send (enc x k)) (recv (enc x x k)))
    ((recv (enc "C" x k)) (send (enc x x k))))
  (label 3)
  (parent 0)
  (unrealized (1 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")
