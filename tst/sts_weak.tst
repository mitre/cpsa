(herald "Station-to-station protocol:  Weakened version"
  (algebra diffie-hellman))

(comment "CPSA 4.4.3")
(comment "All input read from tst/sts_weak.scm")

(defprotocol station-weak diffie-hellman
  (defrole init
    (vars (x rndx) (h base) (a b name))
    (trace (send (exp (gen) x))
      (recv (cat h (enc (enc h (exp (gen) x) (privk b)) (exp h x))))
      (send (enc (enc (exp (gen) x) h (privk a)) (exp h x)))
      (send (privk a))))
  (defrole resp
    (vars (y rndx) (h base) (a b name))
    (trace (recv h)
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) h (privk b)) (exp h y))))
      (recv (enc (enc h (exp (gen) y) (privk a)) (exp h y)))
      (send (privk b))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton station-weak
  (vars (a b name) (x y rndx))
  (defstrand init 3 (a a) (b b) (h (exp (gen) y)) (x x))
  (non-orig (privk a) (privk b))
  (uniq-gen x y)
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) y) (privk a))
          (exp (gen) (mul x y))))))
  (label 0)
  (unrealized (0 1))
  (origs)
  (ugens (x (0 0)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-weak
  (vars (a b b-0 name) (x x-0 rndx))
  (defstrand init 3 (a a) (b b) (h (exp (gen) x-0)) (x x))
  (defstrand init 3 (a b) (b b-0) (h (exp (gen) x)) (x x-0))
  (precedes ((0 0) (1 1)) ((1 2) (0 1)))
  (non-orig (privk a) (privk b))
  (uniq-gen x x-0)
  (operation encryption-test (added-strand init 3)
    (enc (exp (gen) x-0) (exp (gen) x) (privk b)) (0 1))
  (strand-map 0)
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) x-0)
          (enc (enc (exp (gen) x-0) (exp (gen) x) (privk b))
            (exp (gen) (mul x x-0)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) x-0) (privk a))
          (exp (gen) (mul x x-0)))))
    ((send (exp (gen) x-0))
      (recv
        (cat (exp (gen) x)
          (enc (enc (exp (gen) x) (exp (gen) x-0) (privk b-0))
            (exp (gen) (mul x x-0)))))
      (send
        (enc (enc (exp (gen) x-0) (exp (gen) x) (privk b))
          (exp (gen) (mul x x-0))))))
  (label 1)
  (parent 0)
  (unrealized (1 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton station-weak
  (vars (a b name) (x y rndx))
  (defstrand init 3 (a a) (b b) (h (exp (gen) y)) (x x))
  (defstrand resp 2 (b b) (h (exp (gen) x)) (y y))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a) (privk b))
  (uniq-gen x y)
  (operation encryption-test (added-strand resp 2)
    (enc (exp (gen) y) (exp (gen) x) (privk b)) (0 1))
  (strand-map 0)
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) y) (privk a))
          (exp (gen) (mul x y)))))
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))))
  (label 2)
  (parent 0)
  (realized)
  (shape)
  (maps ((0) ((a a) (b b) (x x) (y y))))
  (origs)
  (ugens (x (0 0)) (y (1 1))))

(defskeleton station-weak
  (vars (a b b-0 name) (x x-0 rndx))
  (defstrand init 3 (a a) (b b) (h (exp (gen) x-0)) (x x))
  (defstrand init 3 (a b) (b b-0) (h (exp (gen) x)) (x x-0))
  (deflistener (exp (gen) (mul x x-0)))
  (precedes ((0 0) (2 0)) ((1 0) (2 0)) ((1 2) (0 1)) ((2 1) (1 1)))
  (non-orig (privk a) (privk b))
  (uniq-gen x x-0)
  (operation encryption-test (added-listener (exp (gen) (mul x x-0)))
    (enc (enc (exp (gen) x) (exp (gen) x-0) (privk b-0))
      (exp (gen) (mul x x-0))) (1 1))
  (strand-map 0 1)
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) x-0)
          (enc (enc (exp (gen) x-0) (exp (gen) x) (privk b))
            (exp (gen) (mul x x-0)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) x-0) (privk a))
          (exp (gen) (mul x x-0)))))
    ((send (exp (gen) x-0))
      (recv
        (cat (exp (gen) x)
          (enc (enc (exp (gen) x) (exp (gen) x-0) (privk b-0))
            (exp (gen) (mul x x-0)))))
      (send
        (enc (enc (exp (gen) x-0) (exp (gen) x) (privk b))
          (exp (gen) (mul x x-0)))))
    ((recv (exp (gen) (mul x x-0))) (send (exp (gen) (mul x x-0)))))
  (label 3)
  (parent 1)
  (unrealized (2 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-weak
  (vars (a b b-0 name) (x x-0 rndx))
  (defstrand init 3 (a a) (b b) (h (exp (gen) x-0)) (x x))
  (defstrand init 3 (a b) (b b-0) (h (exp (gen) x)) (x x-0))
  (deflistener (exp (gen) (mul x x-0)))
  (deflistener (cat (exp (gen) x) x-0))
  (precedes ((0 0) (3 0)) ((1 0) (3 0)) ((1 2) (0 1)) ((2 1) (1 1))
    ((3 1) (2 0)))
  (non-orig (privk a) (privk b))
  (uniq-gen x x-0)
  (operation nonce-test (added-listener (cat (exp (gen) x) x-0))
    (exp (gen) (mul x x-0)) (2 0))
  (strand-map 0 1 2)
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) x-0)
          (enc (enc (exp (gen) x-0) (exp (gen) x) (privk b))
            (exp (gen) (mul x x-0)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) x-0) (privk a))
          (exp (gen) (mul x x-0)))))
    ((send (exp (gen) x-0))
      (recv
        (cat (exp (gen) x)
          (enc (enc (exp (gen) x) (exp (gen) x-0) (privk b-0))
            (exp (gen) (mul x x-0)))))
      (send
        (enc (enc (exp (gen) x-0) (exp (gen) x) (privk b))
          (exp (gen) (mul x x-0)))))
    ((recv (exp (gen) (mul x x-0))) (send (exp (gen) (mul x x-0))))
    ((recv (cat (exp (gen) x) x-0)) (send (cat (exp (gen) x) x-0))))
  (label 4)
  (parent 3)
  (unrealized (3 0))
  (dead)
  (comment "empty cohort"))

(defskeleton station-weak
  (vars (a b b-0 name) (x x-0 rndx))
  (defstrand init 3 (a a) (b b) (h (exp (gen) x-0)) (x x))
  (defstrand init 3 (a b) (b b-0) (h (exp (gen) x)) (x x-0))
  (deflistener (exp (gen) (mul x x-0)))
  (deflistener (cat (exp (gen) x-0) x))
  (precedes ((0 0) (3 0)) ((1 0) (3 0)) ((1 2) (0 1)) ((2 1) (1 1))
    ((3 1) (2 0)))
  (non-orig (privk a) (privk b))
  (uniq-gen x x-0)
  (operation nonce-test (added-listener (cat (exp (gen) x-0) x))
    (exp (gen) (mul x x-0)) (2 0))
  (strand-map 0 1 2)
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) x-0)
          (enc (enc (exp (gen) x-0) (exp (gen) x) (privk b))
            (exp (gen) (mul x x-0)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) x-0) (privk a))
          (exp (gen) (mul x x-0)))))
    ((send (exp (gen) x-0))
      (recv
        (cat (exp (gen) x)
          (enc (enc (exp (gen) x) (exp (gen) x-0) (privk b-0))
            (exp (gen) (mul x x-0)))))
      (send
        (enc (enc (exp (gen) x-0) (exp (gen) x) (privk b))
          (exp (gen) (mul x x-0)))))
    ((recv (exp (gen) (mul x x-0))) (send (exp (gen) (mul x x-0))))
    ((recv (cat (exp (gen) x-0) x)) (send (cat (exp (gen) x-0) x))))
  (label 5)
  (parent 3)
  (unrealized (3 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol station-weak diffie-hellman
  (defrole init
    (vars (x rndx) (h base) (a b name))
    (trace (send (exp (gen) x))
      (recv (cat h (enc (enc h (exp (gen) x) (privk b)) (exp h x))))
      (send (enc (enc (exp (gen) x) h (privk a)) (exp h x)))
      (send (privk a))))
  (defrole resp
    (vars (y rndx) (h base) (a b name))
    (trace (recv h)
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) h (privk b)) (exp h y))))
      (recv (enc (enc h (exp (gen) y) (privk a)) (exp h y)))
      (send (privk b))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton station-weak
  (vars (a b name) (y x rndx))
  (defstrand resp 3 (a a) (b b) (h (exp (gen) x)) (y y))
  (non-orig (privk a) (privk b))
  (uniq-gen y x)
  (traces
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x)))))
      (recv
        (enc (enc (exp (gen) x) (exp (gen) y) (privk a))
          (exp (gen) (mul y x))))))
  (label 6)
  (unrealized (0 2))
  (origs)
  (ugens (y (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton station-weak
  (vars (a b b-0 name) (y x rndx))
  (defstrand resp 3 (a a) (b b) (h (exp (gen) x)) (y y))
  (defstrand init 3 (a a) (b b-0) (h (exp (gen) y)) (x x))
  (precedes ((0 1) (1 1)) ((1 0) (0 0)) ((1 2) (0 2)))
  (non-orig (privk a) (privk b))
  (uniq-gen y x)
  (operation encryption-test (added-strand init 3)
    (enc (exp (gen) x) (exp (gen) y) (privk a)) (0 2))
  (strand-map 0)
  (traces
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x)))))
      (recv
        (enc (enc (exp (gen) x) (exp (gen) y) (privk a))
          (exp (gen) (mul y x)))))
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b-0))
            (exp (gen) (mul y x)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) y) (privk a))
          (exp (gen) (mul y x))))))
  (label 7)
  (parent 6)
  (unrealized (1 1))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-weak
  (vars (a b name) (x y rndx))
  (defstrand resp 3 (a a) (b b) (h (exp (gen) x)) (y y))
  (defstrand init 3 (a a) (b b) (h (exp (gen) y)) (x x))
  (precedes ((0 1) (1 1)) ((1 0) (0 0)) ((1 2) (0 2)))
  (non-orig (privk a) (privk b))
  (uniq-gen x y)
  (operation encryption-test (displaced 2 0 resp 2)
    (enc (enc (exp (gen) y) (exp (gen) x) (privk b-0))
      (exp (gen) (mul x y))) (1 1))
  (strand-map 0 1)
  (traces
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (recv
        (enc (enc (exp (gen) x) (exp (gen) y) (privk a))
          (exp (gen) (mul x y)))))
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) y) (privk a))
          (exp (gen) (mul x y))))))
  (label 8)
  (parent 7)
  (realized)
  (shape)
  (maps ((0) ((a a) (b b) (y y) (x x))))
  (origs)
  (ugens (y (0 1)) (x (1 0))))

(defskeleton station-weak
  (vars (a b b-0 name) (y x rndx))
  (defstrand resp 3 (a a) (b b) (h (exp (gen) x)) (y y))
  (defstrand init 3 (a a) (b b-0) (h (exp (gen) y)) (x x))
  (deflistener (exp (gen) (mul y x)))
  (precedes ((0 1) (2 0)) ((1 0) (0 0)) ((1 2) (0 2)) ((2 1) (1 1)))
  (non-orig (privk a) (privk b))
  (uniq-gen y x)
  (operation encryption-test (added-listener (exp (gen) (mul y x)))
    (enc (enc (exp (gen) y) (exp (gen) x) (privk b-0))
      (exp (gen) (mul y x))) (1 1))
  (strand-map 0 1)
  (traces
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x)))))
      (recv
        (enc (enc (exp (gen) x) (exp (gen) y) (privk a))
          (exp (gen) (mul y x)))))
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b-0))
            (exp (gen) (mul y x)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) y) (privk a))
          (exp (gen) (mul y x)))))
    ((recv (exp (gen) (mul y x))) (send (exp (gen) (mul y x)))))
  (label 9)
  (parent 7)
  (unrealized (2 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-weak
  (vars (a b b-0 name) (y x rndx))
  (defstrand resp 3 (a a) (b b) (h (exp (gen) x)) (y y))
  (defstrand init 3 (a a) (b b-0) (h (exp (gen) y)) (x x))
  (deflistener (exp (gen) (mul y x)))
  (deflistener (cat (exp (gen) y) x))
  (precedes ((0 1) (3 0)) ((1 0) (0 0)) ((1 2) (0 2)) ((2 1) (1 1))
    ((3 1) (2 0)))
  (non-orig (privk a) (privk b))
  (uniq-gen y x)
  (operation nonce-test (added-listener (cat (exp (gen) y) x))
    (exp (gen) (mul y x)) (2 0))
  (strand-map 0 1 2)
  (traces
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x)))))
      (recv
        (enc (enc (exp (gen) x) (exp (gen) y) (privk a))
          (exp (gen) (mul y x)))))
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b-0))
            (exp (gen) (mul y x)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) y) (privk a))
          (exp (gen) (mul y x)))))
    ((recv (exp (gen) (mul y x))) (send (exp (gen) (mul y x))))
    ((recv (cat (exp (gen) y) x)) (send (cat (exp (gen) y) x))))
  (label 10)
  (parent 9)
  (unrealized (3 0))
  (dead)
  (comment "empty cohort"))

(defskeleton station-weak
  (vars (a b b-0 name) (y x rndx))
  (defstrand resp 3 (a a) (b b) (h (exp (gen) x)) (y y))
  (defstrand init 3 (a a) (b b-0) (h (exp (gen) y)) (x x))
  (deflistener (exp (gen) (mul y x)))
  (deflistener (cat (exp (gen) x) y))
  (precedes ((0 1) (3 0)) ((1 0) (0 0)) ((1 2) (0 2)) ((2 1) (1 1))
    ((3 1) (2 0)))
  (non-orig (privk a) (privk b))
  (uniq-gen y x)
  (operation nonce-test (added-listener (cat (exp (gen) x) y))
    (exp (gen) (mul y x)) (2 0))
  (strand-map 0 1 2)
  (traces
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x)))))
      (recv
        (enc (enc (exp (gen) x) (exp (gen) y) (privk a))
          (exp (gen) (mul y x)))))
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b-0))
            (exp (gen) (mul y x)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) y) (privk a))
          (exp (gen) (mul y x)))))
    ((recv (exp (gen) (mul y x))) (send (exp (gen) (mul y x))))
    ((recv (cat (exp (gen) x) y)) (send (cat (exp (gen) x) y))))
  (label 11)
  (parent 9)
  (unrealized (3 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol station-weak diffie-hellman
  (defrole init
    (vars (x rndx) (h base) (a b name))
    (trace (send (exp (gen) x))
      (recv (cat h (enc (enc h (exp (gen) x) (privk b)) (exp h x))))
      (send (enc (enc (exp (gen) x) h (privk a)) (exp h x)))
      (send (privk a))))
  (defrole resp
    (vars (y rndx) (h base) (a b name))
    (trace (recv h)
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) h (privk b)) (exp h y))))
      (recv (enc (enc h (exp (gen) y) (privk a)) (exp h y)))
      (send (privk b))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton station-weak
  (vars (a b name) (h base) (x rndx))
  (defstrand init 3 (a a) (b b) (h h) (x x))
  (deflistener (exp h x))
  (non-orig (privk a) (privk b))
  (traces
    ((send (exp (gen) x))
      (recv (cat h (enc (enc h (exp (gen) x) (privk b)) (exp h x))))
      (send (enc (enc (exp (gen) x) h (privk a)) (exp h x))))
    ((recv (exp h x)) (send (exp h x))))
  (label 12)
  (unrealized (0 1))
  (origs)
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-weak
  (vars (a b b-0 name) (x x-0 rndx))
  (defstrand init 3 (a a) (b b) (h (exp (gen) x-0)) (x x))
  (deflistener (exp (gen) (mul x x-0)))
  (defstrand init 3 (a b) (b b-0) (h (exp (gen) x)) (x x-0))
  (precedes ((2 2) (0 1)))
  (non-orig (privk a) (privk b))
  (operation encryption-test (added-strand init 3)
    (enc (exp (gen) x-0) (exp (gen) x) (privk b)) (0 1))
  (strand-map 0 1)
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) x-0)
          (enc (enc (exp (gen) x-0) (exp (gen) x) (privk b))
            (exp (gen) (mul x x-0)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) x-0) (privk a))
          (exp (gen) (mul x x-0)))))
    ((recv (exp (gen) (mul x x-0))) (send (exp (gen) (mul x x-0))))
    ((send (exp (gen) x-0))
      (recv
        (cat (exp (gen) x)
          (enc (enc (exp (gen) x) (exp (gen) x-0) (privk b-0))
            (exp (gen) (mul x x-0)))))
      (send
        (enc (enc (exp (gen) x-0) (exp (gen) x) (privk b))
          (exp (gen) (mul x x-0))))))
  (label 13)
  (parent 12)
  (realized)
  (shape)
  (maps ((0 1) ((a a) (b b) (x x) (h (exp (gen) x-0)))))
  (origs))

(defskeleton station-weak
  (vars (a b name) (x y rndx))
  (defstrand init 3 (a a) (b b) (h (exp (gen) y)) (x x))
  (deflistener (exp (gen) (mul x y)))
  (defstrand resp 2 (b b) (h (exp (gen) x)) (y y))
  (precedes ((2 1) (0 1)))
  (non-orig (privk a) (privk b))
  (operation encryption-test (added-strand resp 2)
    (enc (exp (gen) y) (exp (gen) x) (privk b)) (0 1))
  (strand-map 0 1)
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) y) (privk a))
          (exp (gen) (mul x y)))))
    ((recv (exp (gen) (mul x y))) (send (exp (gen) (mul x y))))
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))))
  (label 14)
  (parent 12)
  (realized)
  (shape)
  (maps ((0 1) ((a a) (b b) (x x) (h (exp (gen) y)))))
  (origs))

(comment "Nothing left to do")

(defprotocol station-weak diffie-hellman
  (defrole init
    (vars (x rndx) (h base) (a b name))
    (trace (send (exp (gen) x))
      (recv (cat h (enc (enc h (exp (gen) x) (privk b)) (exp h x))))
      (send (enc (enc (exp (gen) x) h (privk a)) (exp h x)))
      (send (privk a))))
  (defrole resp
    (vars (y rndx) (h base) (a b name))
    (trace (recv h)
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) h (privk b)) (exp h y))))
      (recv (enc (enc h (exp (gen) y) (privk a)) (exp h y)))
      (send (privk b))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton station-weak
  (vars (a b name) (h base) (y rndx))
  (defstrand resp 3 (a a) (b b) (h h) (y y))
  (deflistener (exp h y))
  (non-orig (privk a) (privk b))
  (traces
    ((recv h)
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) h (privk b)) (exp h y))))
      (recv (enc (enc h (exp (gen) y) (privk a)) (exp h y))))
    ((recv (exp h y)) (send (exp h y))))
  (label 15)
  (unrealized (0 2))
  (preskeleton)
  (origs)
  (comment "Not a skeleton"))

(defskeleton station-weak
  (vars (a b name) (h base) (y rndx))
  (defstrand resp 3 (a a) (b b) (h h) (y y))
  (deflistener (exp h y))
  (non-orig (privk a) (privk b))
  (traces
    ((recv h)
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) h (privk b)) (exp h y))))
      (recv (enc (enc h (exp (gen) y) (privk a)) (exp h y))))
    ((recv (exp h y)) (send (exp h y))))
  (label 16)
  (parent 15)
  (unrealized (0 2))
  (origs)
  (comment "3 in cohort - 3 not yet seen"))

(defskeleton station-weak
  (vars (a b b-0 name) (y x rndx))
  (defstrand resp 3 (a a) (b b) (h (exp (gen) x)) (y y))
  (deflistener (exp (gen) (mul y x)))
  (defstrand init 3 (a a) (b b-0) (h (exp (gen) y)) (x x))
  (precedes ((2 2) (0 2)))
  (non-orig (privk a) (privk b))
  (operation encryption-test (added-strand init 3)
    (enc (exp (gen) x) (exp (gen) y) (privk a)) (0 2))
  (strand-map 0 1)
  (traces
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x)))))
      (recv
        (enc (enc (exp (gen) x) (exp (gen) y) (privk a))
          (exp (gen) (mul y x)))))
    ((recv (exp (gen) (mul y x))) (send (exp (gen) (mul y x))))
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b-0))
            (exp (gen) (mul y x)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) y) (privk a))
          (exp (gen) (mul y x))))))
  (label 17)
  (parent 16)
  (realized)
  (shape)
  (maps ((0 1) ((a a) (b b) (y y) (h (exp (gen) x)))))
  (origs))

(defskeleton station-weak
  (vars (b name) (y rndx))
  (defstrand resp 3 (a b) (b b) (h (exp (gen) y)) (y y))
  (deflistener (exp (gen) (mul y y)))
  (non-orig (privk b))
  (operation encryption-test (displaced 2 0 resp 2)
    (enc (exp (gen) y-0) (exp (gen) y-1) (privk a)) (0 2))
  (strand-map 0 1)
  (traces
    ((recv (exp (gen) y))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) y) (privk b))
            (exp (gen) (mul y y)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) y) (privk b))
          (exp (gen) (mul y y)))))
    ((recv (exp (gen) (mul y y))) (send (exp (gen) (mul y y)))))
  (label 18)
  (parent 16)
  (realized)
  (shape)
  (maps ((0 1) ((a b) (b b) (y y) (h (exp (gen) y)))))
  (origs))

(defskeleton station-weak
  (vars (a b name) (y y-0 rndx))
  (defstrand resp 3 (a a) (b b) (h (exp (gen) y-0)) (y y))
  (deflistener (exp (gen) (mul y y-0)))
  (defstrand resp 2 (b a) (h (exp (gen) y)) (y y-0))
  (precedes ((2 1) (0 2)))
  (non-orig (privk a) (privk b))
  (operation encryption-test (added-strand resp 2)
    (enc (exp (gen) y-0) (exp (gen) y) (privk a)) (0 2))
  (strand-map 0 1)
  (traces
    ((recv (exp (gen) y-0))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) y-0) (privk b))
            (exp (gen) (mul y y-0)))))
      (recv
        (enc (enc (exp (gen) y-0) (exp (gen) y) (privk a))
          (exp (gen) (mul y y-0)))))
    ((recv (exp (gen) (mul y y-0))) (send (exp (gen) (mul y y-0))))
    ((recv (exp (gen) y))
      (send
        (cat (exp (gen) y-0)
          (enc (enc (exp (gen) y-0) (exp (gen) y) (privk a))
            (exp (gen) (mul y y-0)))))))
  (label 19)
  (parent 16)
  (realized)
  (shape)
  (maps ((0 1) ((a a) (b b) (y y) (h (exp (gen) y-0)))))
  (origs))

(comment "Nothing left to do")

(defprotocol station-weak diffie-hellman
  (defrole init
    (vars (x rndx) (h base) (a b name))
    (trace (send (exp (gen) x))
      (recv (cat h (enc (enc h (exp (gen) x) (privk b)) (exp h x))))
      (send (enc (enc (exp (gen) x) h (privk a)) (exp h x)))
      (send (privk a))))
  (defrole resp
    (vars (y rndx) (h base) (a b name))
    (trace (recv h)
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) h (privk b)) (exp h y))))
      (recv (enc (enc h (exp (gen) y) (privk a)) (exp h y)))
      (send (privk b))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton station-weak
  (vars (a b a-0 name) (x y rndx))
  (defstrand init 4 (a a) (b b) (h (exp (gen) y)) (x x))
  (defstrand resp 4 (a a-0) (b b) (h (exp (gen) x)) (y y))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (uniq-orig (privk a) (privk b))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) y) (privk a))
          (exp (gen) (mul x y)))) (send (privk a)))
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (recv
        (enc (enc (exp (gen) x) (exp (gen) y) (privk a-0))
          (exp (gen) (mul x y)))) (send (privk b))))
  (label 20)
  (realized)
  (shape)
  (maps ((0 1) ((a a) (b b) (x x) (y y) (a-0 a-0))))
  (origs ((privk b) (1 3)) ((privk a) (0 3))))

(comment "Nothing left to do")

(defprotocol station-weak diffie-hellman
  (defrole init
    (vars (x rndx) (h base) (a b name))
    (trace (send (exp (gen) x))
      (recv (cat h (enc (enc h (exp (gen) x) (privk b)) (exp h x))))
      (send (enc (enc (exp (gen) x) h (privk a)) (exp h x)))
      (send (privk a))))
  (defrole resp
    (vars (y rndx) (h base) (a b name))
    (trace (recv h)
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) h (privk b)) (exp h y))))
      (recv (enc (enc h (exp (gen) y) (privk a)) (exp h y)))
      (send (privk b))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton station-weak
  (vars (a b a-0 name) (x y rndx))
  (defstrand init 4 (a a) (b b) (h (exp (gen) y)) (x x))
  (defstrand resp 4 (a a-0) (b b) (h (exp (gen) x)) (y y))
  (deflistener (exp (gen) (mul x y)))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (uniq-orig (privk a) (privk b))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) y) (privk a))
          (exp (gen) (mul x y)))) (send (privk a)))
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (recv
        (enc (enc (exp (gen) x) (exp (gen) y) (privk a-0))
          (exp (gen) (mul x y)))) (send (privk b)))
    ((recv (exp (gen) (mul x y))) (send (exp (gen) (mul x y)))))
  (label 21)
  (realized)
  (shape)
  (maps ((0 1 2) ((a a) (b b) (x x) (y y) (a-0 a-0))))
  (origs ((privk b) (1 3)) ((privk a) (0 3))))

(comment "Nothing left to do")
