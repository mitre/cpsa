(comment "CPSA 4.4.5")
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
    (trace (recv (enc "C" x k)) (send (enc x x k))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton abc
  (vars (k skey) (x text))
  (defstrand init 2 (k k) (x x))
  (non-orig k)
  (uniq-orig x)
  (traces ((send (enc x k)) (recv (enc x x k))))
  (label 0)
  (unrealized (0 1))
  (origs (x (0 0)))
  (comment "3 in cohort - 3 not yet seen"))

(defskeleton abc
  (vars (k skey) (x text))
  (defstrand init 2 (k k) (x x))
  (defstrand A 2 (k k) (x x))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig k)
  (uniq-orig x)
  (operation encryption-test (added-strand A 2) (enc x x k) (0 1))
  (strand-map 0)
  (traces ((send (enc x k)) (recv (enc x x k)))
    ((recv (enc "A" x k)) (send (enc x x k))))
  (label 1)
  (parent 0)
  (unrealized (1 0))
  (dead)
  (comment "empty cohort"))

(defskeleton abc
  (vars (k skey) (x text))
  (defstrand init 2 (k k) (x x))
  (defstrand B 2 (k k) (x x))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig k)
  (uniq-orig x)
  (operation encryption-test (added-strand B 2) (enc x x k) (0 1))
  (strand-map 0)
  (traces ((send (enc x k)) (recv (enc x x k)))
    ((recv (enc "B" x k)) (send (enc x x k))))
  (label 2)
  (parent 0)
  (unrealized (1 0))
  (dead)
  (comment "empty cohort"))

(defskeleton abc
  (vars (k skey) (x text))
  (defstrand init 2 (k k) (x x))
  (defstrand C 2 (k k) (x x))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig k)
  (uniq-orig x)
  (operation encryption-test (added-strand C 2) (enc x x k) (0 1))
  (strand-map 0)
  (traces ((send (enc x k)) (recv (enc x x k)))
    ((recv (enc "C" x k)) (send (enc x x k))))
  (label 3)
  (parent 0)
  (unrealized (1 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")
