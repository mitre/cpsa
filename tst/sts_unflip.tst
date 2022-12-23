(herald "Station-to-station protocol unflipped"
  (algebra diffie-hellman))

(comment "CPSA 4.4.2")
(comment "All input read from tst/sts_unflip.scm")

(defprotocol station-to-station-unflip diffie-hellman
  (defrole init
    (vars (x rndx) (h base) (a b name))
    (trace (send (exp (gen) x))
      (recv (cat h (enc (enc h (exp (gen) x) (privk b)) (exp h x))))
      (send (enc (enc h (exp (gen) x) (privk a)) (exp h x)))
      (send (privk a)))
    (uniq-gen x))
  (defrole resp
    (vars (y rndx) (h base) (a b name))
    (trace (recv h)
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) h (privk b)) (exp h y))))
      (recv (enc (enc (exp (gen) y) h (privk a)) (exp h y)))
      (send (privk b)))
    (uniq-gen y))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton station-to-station-unflip
  (vars (a b name) (h base) (x rndx))
  (defstrand init 3 (a a) (b b) (h h) (x x))
  (non-orig (privk b))
  (uniq-gen x)
  (traces
    ((send (exp (gen) x))
      (recv (cat h (enc (enc h (exp (gen) x) (privk b)) (exp h x))))
      (send (enc (enc h (exp (gen) x) (privk a)) (exp h x)))))
  (label 0)
  (unrealized (0 1))
  (origs)
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-to-station-unflip
  (vars (a b name) (x y rndx))
  (defstrand init 3 (a a) (b b) (h (exp (gen) y)) (x x))
  (defstrand resp 2 (b b) (h (exp (gen) x)) (y y))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk b))
  (uniq-gen x y)
  (operation encryption-test (added-strand resp 2)
    (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
      (exp (gen) (mul x y))) (0 1))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (send
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul x y)))))
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))))
  (label 1)
  (parent 0)
  (realized)
  (shape)
  (maps ((0) ((a a) (b b) (x x) (h (exp (gen) y)))))
  (origs))

(defskeleton station-to-station-unflip
  (vars (a b name) (h base) (x rndx))
  (defstrand init 3 (a a) (b b) (h h) (x x))
  (deflistener (exp h x))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk b))
  (uniq-gen x)
  (operation encryption-test (added-listener (exp h x))
    (enc (enc h (exp (gen) x) (privk b)) (exp h x)) (0 1))
  (traces
    ((send (exp (gen) x))
      (recv (cat h (enc (enc h (exp (gen) x) (privk b)) (exp h x))))
      (send (enc (enc h (exp (gen) x) (privk a)) (exp h x))))
    ((recv (exp h x)) (send (exp h x))))
  (label 2)
  (parent 0)
  (unrealized (0 1) (1 0))
  (comment "5 in cohort - 5 not yet seen"))

(defskeleton station-to-station-unflip
  (vars (a b name) (x rndx))
  (defstrand init 3 (a a) (b b) (h (gen)) (x x))
  (deflistener (exp (gen) x))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk b))
  (uniq-gen x)
  (operation nonce-test (displaced 2 0 init 1) (exp (gen) x-0) (1 0))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (gen)
          (enc (enc (gen) (exp (gen) x) (privk b)) (exp (gen) x))))
      (send (enc (enc (gen) (exp (gen) x) (privk a)) (exp (gen) x))))
    ((recv (exp (gen) x)) (send (exp (gen) x))))
  (label 3)
  (parent 2)
  (unrealized (0 1))
  (dead)
  (comment "empty cohort"))

(defskeleton station-to-station-unflip
  (vars (a b name) (x rndx))
  (defstrand init 3 (a a) (b b) (h (exp (gen) (rec x))) (x x))
  (deflistener (gen))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk b))
  (uniq-gen x)
  (operation nonce-test (contracted (h (exp (gen) (rec x)))) (gen)
    (1 0))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) (rec x))
          (enc (enc (exp (gen) (rec x)) (exp (gen) x) (privk b))
            (gen))))
      (send
        (enc (enc (exp (gen) (rec x)) (exp (gen) x) (privk a)) (gen))))
    ((recv (gen)) (send (gen))))
  (label 4)
  (parent 2)
  (unrealized (0 1))
  (dead)
  (comment "empty cohort"))

(defskeleton station-to-station-unflip
  (vars (a b name) (x x-0 rndx))
  (defstrand init 3 (a a) (b b) (h (exp (gen) (mul (rec x) x-0))) (x x))
  (deflistener (exp (gen) x-0))
  (defstrand init 1 (x x-0))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)) ((2 0) (1 0)))
  (non-orig (privk b))
  (uniq-gen x x-0)
  (operation nonce-test (added-strand init 1) (exp (gen) x-0) (1 0))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) (mul (rec x) x-0))
          (enc
            (enc (exp (gen) (mul (rec x) x-0)) (exp (gen) x) (privk b))
            (exp (gen) x-0))))
      (send
        (enc (enc (exp (gen) (mul (rec x) x-0)) (exp (gen) x) (privk a))
          (exp (gen) x-0))))
    ((recv (exp (gen) x-0)) (send (exp (gen) x-0)))
    ((send (exp (gen) x-0))))
  (label 5)
  (parent 2)
  (unrealized (0 1))
  (dead)
  (comment "empty cohort"))

(defskeleton station-to-station-unflip
  (vars (a b b-0 name) (h base) (x y rndx))
  (defstrand init 3 (a a) (b b) (h (exp (gen) (mul (rec x) y))) (x x))
  (deflistener (exp (gen) y))
  (defstrand resp 2 (b b-0) (h h) (y y))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)) ((2 1) (1 0)))
  (non-orig (privk b))
  (uniq-gen x y)
  (operation nonce-test (added-strand resp 2) (exp (gen) y) (1 0))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) (mul (rec x) y))
          (enc (enc (exp (gen) (mul (rec x) y)) (exp (gen) x) (privk b))
            (exp (gen) y))))
      (send
        (enc (enc (exp (gen) (mul (rec x) y)) (exp (gen) x) (privk a))
          (exp (gen) y)))) ((recv (exp (gen) y)) (send (exp (gen) y)))
    ((recv h)
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) h (privk b-0)) (exp h y))))))
  (label 6)
  (parent 2)
  (unrealized (0 1))
  (dead)
  (comment "empty cohort"))

(defskeleton station-to-station-unflip
  (vars (a b name) (h base) (x rndx) (w expt))
  (defstrand init 3 (a a) (b b) (h h) (x x))
  (deflistener (exp h x))
  (deflistener (cat (exp h (mul x (rec w))) w))
  (precedes ((0 0) (2 0)) ((1 1) (0 1)) ((2 1) (1 0)))
  (non-orig (privk b))
  (uniq-gen x)
  (precur (2 0))
  (operation nonce-test (added-listener (cat (exp h (mul x (rec w))) w))
    (exp h x) (1 0))
  (traces
    ((send (exp (gen) x))
      (recv (cat h (enc (enc h (exp (gen) x) (privk b)) (exp h x))))
      (send (enc (enc h (exp (gen) x) (privk a)) (exp h x))))
    ((recv (exp h x)) (send (exp h x)))
    ((recv (cat (exp h (mul x (rec w))) w))
      (send (cat (exp h (mul x (rec w))) w))))
  (label 7)
  (parent 2)
  (unrealized (0 1) (2 0))
  (comment "4 in cohort - 4 not yet seen"))

(defskeleton station-to-station-unflip
  (vars (a b name) (w expt) (x rndx))
  (defstrand init 3 (a a) (b b) (h (exp (gen) w)) (x x))
  (deflistener (exp (gen) (mul w x)))
  (deflistener (cat (exp (gen) x) w))
  (precedes ((0 0) (2 0)) ((1 1) (0 1)) ((2 1) (1 0)))
  (non-orig (privk b))
  (uniq-gen x)
  (precur (2 0))
  (operation nonce-test (displaced 3 0 init 1) (exp (gen) x-0) (2 0))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) w)
          (enc (enc (exp (gen) w) (exp (gen) x) (privk b))
            (exp (gen) (mul w x)))))
      (send
        (enc (enc (exp (gen) w) (exp (gen) x) (privk a))
          (exp (gen) (mul w x)))))
    ((recv (exp (gen) (mul w x))) (send (exp (gen) (mul w x))))
    ((recv (cat (exp (gen) x) w)) (send (cat (exp (gen) x) w))))
  (label 8)
  (parent 7)
  (unrealized (0 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton station-to-station-unflip
  (vars (a b name) (x rndx) (w expt))
  (defstrand init 3 (a a) (b b) (h (exp (gen) (mul (rec x) w))) (x x))
  (deflistener (exp (gen) w))
  (deflistener (cat (gen) w))
  (precedes ((0 0) (2 0)) ((1 1) (0 1)) ((2 1) (1 0)))
  (non-orig (privk b))
  (uniq-gen x)
  (precur (2 0))
  (operation nonce-test (contracted (h (exp (gen) (mul (rec x) w))))
    (gen) (2 0))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) (mul (rec x) w))
          (enc (enc (exp (gen) (mul (rec x) w)) (exp (gen) x) (privk b))
            (exp (gen) w))))
      (send
        (enc (enc (exp (gen) (mul (rec x) w)) (exp (gen) x) (privk a))
          (exp (gen) w)))) ((recv (exp (gen) w)) (send (exp (gen) w)))
    ((recv (cat (gen) w)) (send (cat (gen) w))))
  (label 9)
  (parent 7)
  (unrealized (0 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton station-to-station-unflip
  (vars (a b name) (x rndx) (w expt) (x-0 rndx))
  (defstrand init 3 (a a) (b b) (h (exp (gen) (mul (rec x) w x-0)))
    (x x))
  (deflistener (exp (gen) (mul w x-0)))
  (deflistener (cat (exp (gen) x-0) w))
  (defstrand init 1 (x x-0))
  (precedes ((0 0) (2 0)) ((1 1) (0 1)) ((2 1) (1 0)) ((3 0) (2 0)))
  (non-orig (privk b))
  (uniq-gen x x-0)
  (precur (2 0))
  (operation nonce-test (added-strand init 1) (exp (gen) x-0) (2 0))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) (mul (rec x) w x-0))
          (enc
            (enc (exp (gen) (mul (rec x) w x-0)) (exp (gen) x)
              (privk b)) (exp (gen) (mul w x-0)))))
      (send
        (enc
          (enc (exp (gen) (mul (rec x) w x-0)) (exp (gen) x) (privk a))
          (exp (gen) (mul w x-0)))))
    ((recv (exp (gen) (mul w x-0))) (send (exp (gen) (mul w x-0))))
    ((recv (cat (exp (gen) x-0) w)) (send (cat (exp (gen) x-0) w)))
    ((send (exp (gen) x-0))))
  (label 10)
  (parent 7)
  (unrealized (0 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton station-to-station-unflip
  (vars (a b b-0 name) (h base) (x rndx) (w expt) (y rndx))
  (defstrand init 3 (a a) (b b) (h (exp (gen) (mul (rec x) w y))) (x x))
  (deflistener (exp (gen) (mul w y)))
  (deflistener (cat (exp (gen) y) w))
  (defstrand resp 2 (b b-0) (h h) (y y))
  (precedes ((0 0) (2 0)) ((1 1) (0 1)) ((2 1) (1 0)) ((3 1) (2 0)))
  (non-orig (privk b))
  (uniq-gen x y)
  (precur (2 0))
  (operation nonce-test (added-strand resp 2) (exp (gen) y) (2 0))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) (mul (rec x) w y))
          (enc
            (enc (exp (gen) (mul (rec x) w y)) (exp (gen) x) (privk b))
            (exp (gen) (mul w y)))))
      (send
        (enc (enc (exp (gen) (mul (rec x) w y)) (exp (gen) x) (privk a))
          (exp (gen) (mul w y)))))
    ((recv (exp (gen) (mul w y))) (send (exp (gen) (mul w y))))
    ((recv (cat (exp (gen) y) w)) (send (cat (exp (gen) y) w)))
    ((recv h)
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) h (privk b-0)) (exp h y))))))
  (label 11)
  (parent 7)
  (unrealized (0 1))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-to-station-unflip
  (vars (a b name) (x y rndx))
  (defstrand init 3 (a a) (b b) (h (exp (gen) y)) (x x))
  (deflistener (exp (gen) (mul x y)))
  (deflistener (cat (exp (gen) x) y))
  (defstrand resp 2 (b b) (h (exp (gen) x)) (y y))
  (precedes ((0 0) (3 0)) ((1 1) (0 1)) ((2 1) (1 0)) ((3 1) (2 0)))
  (non-orig (privk b))
  (uniq-gen x y)
  (precur (2 0))
  (operation encryption-test (added-strand resp 2)
    (enc (exp (gen) y) (exp (gen) x) (privk b)) (0 1))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (send
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul x y)))))
    ((recv (exp (gen) (mul x y))) (send (exp (gen) (mul x y))))
    ((recv (cat (exp (gen) x) y)) (send (cat (exp (gen) x) y)))
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))))
  (label 12)
  (parent 8)
  (unrealized (2 0))
  (dead)
  (comment "empty cohort"))

(defskeleton station-to-station-unflip
  (vars (a b name) (x y rndx))
  (defstrand init 3 (a a) (b b) (h (exp (gen) y)) (x x))
  (deflistener (exp (gen) (mul x y)))
  (deflistener (cat (gen) (mul x y)))
  (defstrand resp 2 (b b) (h (exp (gen) x)) (y y))
  (precedes ((0 0) (3 0)) ((1 1) (0 1)) ((2 1) (1 0)) ((3 1) (2 0)))
  (non-orig (privk b))
  (uniq-gen x y)
  (precur (2 0))
  (operation encryption-test (added-strand resp 2)
    (enc (exp (gen) y) (exp (gen) x) (privk b)) (0 1))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (send
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul x y)))))
    ((recv (exp (gen) (mul x y))) (send (exp (gen) (mul x y))))
    ((recv (cat (gen) (mul x y))) (send (cat (gen) (mul x y))))
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))))
  (label 13)
  (parent 9)
  (unrealized (1 0) (2 0))
  (dead)
  (comment "empty cohort"))

(defskeleton station-to-station-unflip
  (vars (a b name) (x x-0 y rndx))
  (defstrand init 3 (a a) (b b) (h (exp (gen) y)) (x x))
  (deflistener (exp (gen) (mul x y)))
  (deflistener (cat (exp (gen) x-0) (mul x (rec x-0) y)))
  (defstrand init 1 (x x-0))
  (defstrand resp 2 (b b) (h (exp (gen) x)) (y y))
  (precedes ((0 0) (4 0)) ((1 1) (0 1)) ((2 1) (1 0)) ((3 0) (2 0))
    ((4 1) (2 0)))
  (non-orig (privk b))
  (uniq-gen x x-0 y)
  (precur (2 0))
  (operation encryption-test (added-strand resp 2)
    (enc (exp (gen) y) (exp (gen) x) (privk b)) (0 1))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (send
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul x y)))))
    ((recv (exp (gen) (mul x y))) (send (exp (gen) (mul x y))))
    ((recv (cat (exp (gen) x-0) (mul x (rec x-0) y)))
      (send (cat (exp (gen) x-0) (mul x (rec x-0) y))))
    ((send (exp (gen) x-0)))
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))))
  (label 14)
  (parent 10)
  (unrealized (1 0) (2 0))
  (dead)
  (comment "empty cohort"))

(defskeleton station-to-station-unflip
  (vars (a b name) (x y rndx))
  (defstrand init 3 (a a) (b b) (h (exp (gen) y)) (x x))
  (deflistener (exp (gen) (mul x y)))
  (deflistener (cat (exp (gen) y) x))
  (defstrand resp 2 (b b) (h (exp (gen) x)) (y y))
  (precedes ((0 0) (3 0)) ((1 1) (0 1)) ((2 1) (1 0)) ((3 1) (2 0)))
  (non-orig (privk b))
  (uniq-gen x y)
  (precur (2 0))
  (operation encryption-test (displaced 4 3 resp 2)
    (enc (exp (gen) y-0) (exp (gen) x) (privk b-0)) (0 1))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (send
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul x y)))))
    ((recv (exp (gen) (mul x y))) (send (exp (gen) (mul x y))))
    ((recv (cat (exp (gen) y) x)) (send (cat (exp (gen) y) x)))
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))))
  (label 15)
  (parent 11)
  (unrealized (2 0))
  (dead)
  (comment "empty cohort"))

(defskeleton station-to-station-unflip
  (vars (a b b-0 name) (h base) (x y y-0 rndx))
  (defstrand init 3 (a a) (b b) (h (exp (gen) y-0)) (x x))
  (deflistener (exp (gen) (mul x y-0)))
  (deflistener (cat (exp (gen) y) (mul x (rec y) y-0)))
  (defstrand resp 2 (b b-0) (h h) (y y))
  (defstrand resp 2 (b b) (h (exp (gen) x)) (y y-0))
  (precedes ((0 0) (4 0)) ((1 1) (0 1)) ((2 1) (1 0)) ((3 1) (2 0))
    ((4 1) (2 0)))
  (non-orig (privk b))
  (uniq-gen x y y-0)
  (precur (2 0))
  (operation encryption-test (added-strand resp 2)
    (enc (exp (gen) y-0) (exp (gen) x) (privk b)) (0 1))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y-0)
          (enc (enc (exp (gen) y-0) (exp (gen) x) (privk b))
            (exp (gen) (mul x y-0)))))
      (send
        (enc (enc (exp (gen) y-0) (exp (gen) x) (privk a))
          (exp (gen) (mul x y-0)))))
    ((recv (exp (gen) (mul x y-0))) (send (exp (gen) (mul x y-0))))
    ((recv (cat (exp (gen) y) (mul x (rec y) y-0)))
      (send (cat (exp (gen) y) (mul x (rec y) y-0))))
    ((recv h)
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) h (privk b-0)) (exp h y)))))
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y-0)
          (enc (enc (exp (gen) y-0) (exp (gen) x) (privk b))
            (exp (gen) (mul x y-0)))))))
  (label 16)
  (parent 11)
  (unrealized (1 0) (2 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol station-to-station-unflip diffie-hellman
  (defrole init
    (vars (x rndx) (h base) (a b name))
    (trace (send (exp (gen) x))
      (recv (cat h (enc (enc h (exp (gen) x) (privk b)) (exp h x))))
      (send (enc (enc h (exp (gen) x) (privk a)) (exp h x)))
      (send (privk a)))
    (uniq-gen x))
  (defrole resp
    (vars (y rndx) (h base) (a b name))
    (trace (recv h)
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) h (privk b)) (exp h y))))
      (recv (enc (enc (exp (gen) y) h (privk a)) (exp h y)))
      (send (privk b)))
    (uniq-gen y))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton station-to-station-unflip
  (vars (a b name) (h base) (y rndx))
  (defstrand resp 3 (a a) (b b) (h h) (y y))
  (non-orig (privk a))
  (uniq-gen y)
  (traces
    ((recv h)
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) h (privk b)) (exp h y))))
      (recv (enc (enc (exp (gen) y) h (privk a)) (exp h y)))))
  (label 17)
  (unrealized (0 2))
  (origs)
  (comment "3 in cohort - 3 not yet seen"))

(defskeleton station-to-station-unflip
  (vars (a b b-0 name) (y x rndx))
  (defstrand resp 3 (a a) (b b) (h (exp (gen) x)) (y y))
  (defstrand init 3 (a a) (b b-0) (h (exp (gen) y)) (x x))
  (precedes ((0 1) (1 1)) ((1 0) (0 0)) ((1 2) (0 2)))
  (non-orig (privk a))
  (uniq-gen y x)
  (operation encryption-test (added-strand init 3)
    (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
      (exp (gen) (mul y x))) (0 2))
  (traces
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul y x)))))
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b-0))
            (exp (gen) (mul y x)))))
      (send
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul y x))))))
  (label 18)
  (parent 17)
  (unrealized (1 1))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-to-station-unflip
  (vars (b name) (h base) (y rndx))
  (defstrand resp 3 (a b) (b b) (h h) (y y))
  (non-orig (privk b))
  (uniq-gen y)
  (operation encryption-test (displaced 1 0 resp 2)
    (enc (enc (exp (gen) y) h (privk a)) (exp h y)) (0 2))
  (traces
    ((recv h)
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) h (privk b)) (exp h y))))
      (recv (enc (enc (exp (gen) y) h (privk b)) (exp h y)))))
  (label 19)
  (parent 17)
  (realized)
  (shape)
  (maps ((0) ((a b) (b b) (y y) (h h))))
  (origs))

(defskeleton station-to-station-unflip
  (vars (a b name) (h base) (y rndx))
  (defstrand resp 3 (a a) (b b) (h h) (y y))
  (deflistener (exp h y))
  (precedes ((0 1) (1 0)) ((1 1) (0 2)))
  (non-orig (privk a))
  (uniq-gen y)
  (operation encryption-test (added-listener (exp h y))
    (enc (enc (exp (gen) y) h (privk a)) (exp h y)) (0 2))
  (traces
    ((recv h)
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) h (privk b)) (exp h y))))
      (recv (enc (enc (exp (gen) y) h (privk a)) (exp h y))))
    ((recv (exp h y)) (send (exp h y))))
  (label 20)
  (parent 17)
  (unrealized (0 2) (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton station-to-station-unflip
  (vars (a b name) (x y rndx))
  (defstrand resp 3 (a a) (b b) (h (exp (gen) x)) (y y))
  (defstrand init 3 (a a) (b b) (h (exp (gen) y)) (x x))
  (precedes ((0 1) (1 1)) ((1 0) (0 0)) ((1 2) (0 2)))
  (non-orig (privk a))
  (uniq-gen x y)
  (operation encryption-test (displaced 2 0 resp 2)
    (enc (enc (exp (gen) y) (exp (gen) x) (privk b-0))
      (exp (gen) (mul x y))) (1 1))
  (traces
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul x y)))))
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (send
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul x y))))))
  (label 21)
  (parent 18)
  (realized)
  (shape)
  (maps ((0) ((a a) (b b) (y y) (h (exp (gen) x)))))
  (origs))

(defskeleton station-to-station-unflip
  (vars (a b b-0 name) (y x rndx))
  (defstrand resp 3 (a a) (b b) (h (exp (gen) x)) (y y))
  (defstrand init 3 (a a) (b b-0) (h (exp (gen) y)) (x x))
  (deflistener (exp (gen) (mul y x)))
  (precedes ((0 1) (2 0)) ((1 0) (0 0)) ((1 2) (0 2)) ((2 1) (1 1)))
  (non-orig (privk a))
  (uniq-gen y x)
  (operation encryption-test (added-listener (exp (gen) (mul y x)))
    (enc (enc (exp (gen) y) (exp (gen) x) (privk b-0))
      (exp (gen) (mul y x))) (1 1))
  (traces
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul y x)))))
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b-0))
            (exp (gen) (mul y x)))))
      (send
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul y x)))))
    ((recv (exp (gen) (mul y x))) (send (exp (gen) (mul y x)))))
  (label 22)
  (parent 18)
  (unrealized (2 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-to-station-unflip
  (vars (a b name) (h base) (y rndx) (w expt))
  (defstrand resp 3 (a a) (b b) (h h) (y y))
  (deflistener (exp h y))
  (deflistener (cat (exp h (mul y (rec w))) w))
  (precedes ((0 1) (2 0)) ((1 1) (0 2)) ((2 1) (1 0)))
  (non-orig (privk a))
  (uniq-gen y)
  (precur (2 0))
  (operation nonce-test (added-listener (cat (exp h (mul y (rec w))) w))
    (exp h y) (1 0))
  (traces
    ((recv h)
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) h (privk b)) (exp h y))))
      (recv (enc (enc (exp (gen) y) h (privk a)) (exp h y))))
    ((recv (exp h y)) (send (exp h y)))
    ((recv (cat (exp h (mul y (rec w))) w))
      (send (cat (exp h (mul y (rec w))) w))))
  (label 23)
  (parent 20)
  (unrealized (0 2) (2 0))
  (dead)
  (comment "empty cohort"))

(defskeleton station-to-station-unflip
  (vars (a b b-0 name) (y x rndx))
  (defstrand resp 3 (a a) (b b) (h (exp (gen) x)) (y y))
  (defstrand init 3 (a a) (b b-0) (h (exp (gen) y)) (x x))
  (deflistener (exp (gen) (mul y x)))
  (deflistener (cat (exp (gen) y) x))
  (precedes ((0 1) (3 0)) ((1 0) (0 0)) ((1 2) (0 2)) ((2 1) (1 1))
    ((3 1) (2 0)))
  (non-orig (privk a))
  (uniq-gen y x)
  (operation nonce-test (added-listener (cat (exp (gen) y) x))
    (exp (gen) (mul y x)) (2 0))
  (traces
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul y x)))))
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b-0))
            (exp (gen) (mul y x)))))
      (send
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul y x)))))
    ((recv (exp (gen) (mul y x))) (send (exp (gen) (mul y x))))
    ((recv (cat (exp (gen) y) x)) (send (cat (exp (gen) y) x))))
  (label 24)
  (parent 22)
  (unrealized (3 0))
  (dead)
  (comment "empty cohort"))

(defskeleton station-to-station-unflip
  (vars (a b b-0 name) (y x rndx))
  (defstrand resp 3 (a a) (b b) (h (exp (gen) x)) (y y))
  (defstrand init 3 (a a) (b b-0) (h (exp (gen) y)) (x x))
  (deflistener (exp (gen) (mul y x)))
  (deflistener (cat (exp (gen) x) y))
  (precedes ((0 1) (3 0)) ((1 0) (0 0)) ((1 2) (0 2)) ((2 1) (1 1))
    ((3 1) (2 0)))
  (non-orig (privk a))
  (uniq-gen y x)
  (operation nonce-test (added-listener (cat (exp (gen) x) y))
    (exp (gen) (mul y x)) (2 0))
  (traces
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul y x)))))
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b-0))
            (exp (gen) (mul y x)))))
      (send
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul y x)))))
    ((recv (exp (gen) (mul y x))) (send (exp (gen) (mul y x))))
    ((recv (cat (exp (gen) x) y)) (send (cat (exp (gen) x) y))))
  (label 25)
  (parent 22)
  (unrealized (3 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol station-to-station-unflip diffie-hellman
  (defrole init
    (vars (x rndx) (h base) (a b name))
    (trace (send (exp (gen) x))
      (recv (cat h (enc (enc h (exp (gen) x) (privk b)) (exp h x))))
      (send (enc (enc h (exp (gen) x) (privk a)) (exp h x)))
      (send (privk a)))
    (uniq-gen x))
  (defrole resp
    (vars (y rndx) (h base) (a b name))
    (trace (recv h)
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) h (privk b)) (exp h y))))
      (recv (enc (enc (exp (gen) y) h (privk a)) (exp h y)))
      (send (privk b)))
    (uniq-gen y))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton station-to-station-unflip
  (vars (a b name) (h base) (y rndx))
  (defstrand resp 3 (a a) (b b) (h h) (y y))
  (non-orig (privk a))
  (uniq-gen y)
  (facts (neq a b))
  (traces
    ((recv h)
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) h (privk b)) (exp h y))))
      (recv (enc (enc (exp (gen) y) h (privk a)) (exp h y)))))
  (label 26)
  (unrealized (0 2))
  (origs)
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-to-station-unflip
  (vars (a b b-0 name) (y x rndx))
  (defstrand resp 3 (a a) (b b) (h (exp (gen) x)) (y y))
  (defstrand init 3 (a a) (b b-0) (h (exp (gen) y)) (x x))
  (precedes ((0 1) (1 1)) ((1 0) (0 0)) ((1 2) (0 2)))
  (non-orig (privk a))
  (uniq-gen y x)
  (facts (neq a b))
  (operation encryption-test (added-strand init 3)
    (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
      (exp (gen) (mul y x))) (0 2))
  (traces
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul y x)))))
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b-0))
            (exp (gen) (mul y x)))))
      (send
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul y x))))))
  (label 27)
  (parent 26)
  (unrealized (1 1))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-to-station-unflip
  (vars (a b name) (h base) (y rndx))
  (defstrand resp 3 (a a) (b b) (h h) (y y))
  (deflistener (exp h y))
  (precedes ((0 1) (1 0)) ((1 1) (0 2)))
  (non-orig (privk a))
  (uniq-gen y)
  (facts (neq a b))
  (operation encryption-test (added-listener (exp h y))
    (enc (enc (exp (gen) y) h (privk a)) (exp h y)) (0 2))
  (traces
    ((recv h)
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) h (privk b)) (exp h y))))
      (recv (enc (enc (exp (gen) y) h (privk a)) (exp h y))))
    ((recv (exp h y)) (send (exp h y))))
  (label 28)
  (parent 26)
  (unrealized (0 2) (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton station-to-station-unflip
  (vars (a b name) (x y rndx))
  (defstrand resp 3 (a a) (b b) (h (exp (gen) x)) (y y))
  (defstrand init 3 (a a) (b b) (h (exp (gen) y)) (x x))
  (precedes ((0 1) (1 1)) ((1 0) (0 0)) ((1 2) (0 2)))
  (non-orig (privk a))
  (uniq-gen x y)
  (facts (neq a b))
  (operation encryption-test (displaced 2 0 resp 2)
    (enc (enc (exp (gen) y) (exp (gen) x) (privk b-0))
      (exp (gen) (mul x y))) (1 1))
  (traces
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul x y)))))
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (send
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul x y))))))
  (label 29)
  (parent 27)
  (realized)
  (shape)
  (maps ((0) ((a a) (b b) (y y) (h (exp (gen) x)))))
  (origs))

(defskeleton station-to-station-unflip
  (vars (a b b-0 name) (y x rndx))
  (defstrand resp 3 (a a) (b b) (h (exp (gen) x)) (y y))
  (defstrand init 3 (a a) (b b-0) (h (exp (gen) y)) (x x))
  (deflistener (exp (gen) (mul y x)))
  (precedes ((0 1) (2 0)) ((1 0) (0 0)) ((1 2) (0 2)) ((2 1) (1 1)))
  (non-orig (privk a))
  (uniq-gen y x)
  (facts (neq a b))
  (operation encryption-test (added-listener (exp (gen) (mul y x)))
    (enc (enc (exp (gen) y) (exp (gen) x) (privk b-0))
      (exp (gen) (mul y x))) (1 1))
  (traces
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul y x)))))
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b-0))
            (exp (gen) (mul y x)))))
      (send
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul y x)))))
    ((recv (exp (gen) (mul y x))) (send (exp (gen) (mul y x)))))
  (label 30)
  (parent 27)
  (unrealized (2 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-to-station-unflip
  (vars (a b name) (h base) (y rndx) (w expt))
  (defstrand resp 3 (a a) (b b) (h h) (y y))
  (deflistener (exp h y))
  (deflistener (cat (exp h (mul y (rec w))) w))
  (precedes ((0 1) (2 0)) ((1 1) (0 2)) ((2 1) (1 0)))
  (non-orig (privk a))
  (uniq-gen y)
  (precur (2 0))
  (facts (neq a b))
  (operation nonce-test (added-listener (cat (exp h (mul y (rec w))) w))
    (exp h y) (1 0))
  (traces
    ((recv h)
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) h (privk b)) (exp h y))))
      (recv (enc (enc (exp (gen) y) h (privk a)) (exp h y))))
    ((recv (exp h y)) (send (exp h y)))
    ((recv (cat (exp h (mul y (rec w))) w))
      (send (cat (exp h (mul y (rec w))) w))))
  (label 31)
  (parent 28)
  (unrealized (0 2) (2 0))
  (dead)
  (comment "empty cohort"))

(defskeleton station-to-station-unflip
  (vars (a b b-0 name) (y x rndx))
  (defstrand resp 3 (a a) (b b) (h (exp (gen) x)) (y y))
  (defstrand init 3 (a a) (b b-0) (h (exp (gen) y)) (x x))
  (deflistener (exp (gen) (mul y x)))
  (deflistener (cat (exp (gen) y) x))
  (precedes ((0 1) (3 0)) ((1 0) (0 0)) ((1 2) (0 2)) ((2 1) (1 1))
    ((3 1) (2 0)))
  (non-orig (privk a))
  (uniq-gen y x)
  (facts (neq a b))
  (operation nonce-test (added-listener (cat (exp (gen) y) x))
    (exp (gen) (mul y x)) (2 0))
  (traces
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul y x)))))
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b-0))
            (exp (gen) (mul y x)))))
      (send
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul y x)))))
    ((recv (exp (gen) (mul y x))) (send (exp (gen) (mul y x))))
    ((recv (cat (exp (gen) y) x)) (send (cat (exp (gen) y) x))))
  (label 32)
  (parent 30)
  (unrealized (3 0))
  (dead)
  (comment "empty cohort"))

(defskeleton station-to-station-unflip
  (vars (a b b-0 name) (y x rndx))
  (defstrand resp 3 (a a) (b b) (h (exp (gen) x)) (y y))
  (defstrand init 3 (a a) (b b-0) (h (exp (gen) y)) (x x))
  (deflistener (exp (gen) (mul y x)))
  (deflistener (cat (exp (gen) x) y))
  (precedes ((0 1) (3 0)) ((1 0) (0 0)) ((1 2) (0 2)) ((2 1) (1 1))
    ((3 1) (2 0)))
  (non-orig (privk a))
  (uniq-gen y x)
  (facts (neq a b))
  (operation nonce-test (added-listener (cat (exp (gen) x) y))
    (exp (gen) (mul y x)) (2 0))
  (traces
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul y x)))))
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b-0))
            (exp (gen) (mul y x)))))
      (send
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul y x)))))
    ((recv (exp (gen) (mul y x))) (send (exp (gen) (mul y x))))
    ((recv (cat (exp (gen) x) y)) (send (cat (exp (gen) x) y))))
  (label 33)
  (parent 30)
  (unrealized (3 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol station-to-station-unflip diffie-hellman
  (defrole init
    (vars (x rndx) (h base) (a b name))
    (trace (send (exp (gen) x))
      (recv (cat h (enc (enc h (exp (gen) x) (privk b)) (exp h x))))
      (send (enc (enc h (exp (gen) x) (privk a)) (exp h x)))
      (send (privk a)))
    (uniq-gen x))
  (defrole resp
    (vars (y rndx) (h base) (a b name))
    (trace (recv h)
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) h (privk b)) (exp h y))))
      (recv (enc (enc (exp (gen) y) h (privk a)) (exp h y)))
      (send (privk b)))
    (uniq-gen y))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton station-to-station-unflip
  (vars (a b name) (h base) (x rndx))
  (defstrand init 3 (a a) (b b) (h h) (x x))
  (deflistener (exp h x))
  (non-orig (privk a) (privk b))
  (uniq-gen x)
  (traces
    ((send (exp (gen) x))
      (recv (cat h (enc (enc h (exp (gen) x) (privk b)) (exp h x))))
      (send (enc (enc h (exp (gen) x) (privk a)) (exp h x))))
    ((recv (exp h x)) (send (exp h x))))
  (label 34)
  (unrealized (0 1) (1 0))
  (preskeleton)
  (origs)
  (comment "Not a skeleton"))

(defskeleton station-to-station-unflip
  (vars (a b name) (h base) (x rndx))
  (defstrand init 3 (a a) (b b) (h h) (x x))
  (deflistener (exp h x))
  (precedes ((0 0) (1 0)))
  (non-orig (privk a) (privk b))
  (uniq-gen x)
  (traces
    ((send (exp (gen) x))
      (recv (cat h (enc (enc h (exp (gen) x) (privk b)) (exp h x))))
      (send (enc (enc h (exp (gen) x) (privk a)) (exp h x))))
    ((recv (exp h x)) (send (exp h x))))
  (label 35)
  (parent 34)
  (unrealized (0 1) (1 0))
  (origs)
  (comment "5 in cohort - 5 not yet seen"))

(defskeleton station-to-station-unflip
  (vars (a b name) (x rndx))
  (defstrand init 3 (a a) (b b) (h (gen)) (x x))
  (deflistener (exp (gen) x))
  (precedes ((0 0) (1 0)))
  (non-orig (privk a) (privk b))
  (uniq-gen x)
  (operation nonce-test (displaced 2 0 init 1) (exp (gen) x-0) (1 0))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (gen)
          (enc (enc (gen) (exp (gen) x) (privk b)) (exp (gen) x))))
      (send (enc (enc (gen) (exp (gen) x) (privk a)) (exp (gen) x))))
    ((recv (exp (gen) x)) (send (exp (gen) x))))
  (label 36)
  (parent 35)
  (unrealized (0 1))
  (dead)
  (origs)
  (comment "empty cohort"))

(defskeleton station-to-station-unflip
  (vars (a b name) (x rndx))
  (defstrand init 3 (a a) (b b) (h (exp (gen) (rec x))) (x x))
  (deflistener (gen))
  (precedes ((0 0) (1 0)))
  (non-orig (privk a) (privk b))
  (uniq-gen x)
  (operation nonce-test (contracted (h (exp (gen) (rec x)))) (gen)
    (1 0))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) (rec x))
          (enc (enc (exp (gen) (rec x)) (exp (gen) x) (privk b))
            (gen))))
      (send
        (enc (enc (exp (gen) (rec x)) (exp (gen) x) (privk a)) (gen))))
    ((recv (gen)) (send (gen))))
  (label 37)
  (parent 35)
  (unrealized (0 1))
  (dead)
  (origs)
  (comment "empty cohort"))

(defskeleton station-to-station-unflip
  (vars (a b name) (x x-0 rndx))
  (defstrand init 3 (a a) (b b) (h (exp (gen) (mul (rec x) x-0))) (x x))
  (deflistener (exp (gen) x-0))
  (defstrand init 1 (x x-0))
  (precedes ((0 0) (1 0)) ((2 0) (0 1)) ((2 0) (1 0)))
  (non-orig (privk a) (privk b))
  (uniq-gen x x-0)
  (operation nonce-test (added-strand init 1) (exp (gen) x-0) (1 0))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) (mul (rec x) x-0))
          (enc
            (enc (exp (gen) (mul (rec x) x-0)) (exp (gen) x) (privk b))
            (exp (gen) x-0))))
      (send
        (enc (enc (exp (gen) (mul (rec x) x-0)) (exp (gen) x) (privk a))
          (exp (gen) x-0))))
    ((recv (exp (gen) x-0)) (send (exp (gen) x-0)))
    ((send (exp (gen) x-0))))
  (label 38)
  (parent 35)
  (unrealized (0 1))
  (dead)
  (comment "empty cohort"))

(defskeleton station-to-station-unflip
  (vars (a b b-0 name) (h base) (x y rndx))
  (defstrand init 3 (a a) (b b) (h (exp (gen) (mul (rec x) y))) (x x))
  (deflistener (exp (gen) y))
  (defstrand resp 2 (b b-0) (h h) (y y))
  (precedes ((0 0) (1 0)) ((2 1) (0 1)) ((2 1) (1 0)))
  (non-orig (privk a) (privk b))
  (uniq-gen x y)
  (operation nonce-test (added-strand resp 2) (exp (gen) y) (1 0))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) (mul (rec x) y))
          (enc (enc (exp (gen) (mul (rec x) y)) (exp (gen) x) (privk b))
            (exp (gen) y))))
      (send
        (enc (enc (exp (gen) (mul (rec x) y)) (exp (gen) x) (privk a))
          (exp (gen) y)))) ((recv (exp (gen) y)) (send (exp (gen) y)))
    ((recv h)
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) h (privk b-0)) (exp h y))))))
  (label 39)
  (parent 35)
  (unrealized (0 1))
  (dead)
  (comment "empty cohort"))

(defskeleton station-to-station-unflip
  (vars (a b name) (h base) (x rndx) (w expt))
  (defstrand init 3 (a a) (b b) (h h) (x x))
  (deflistener (exp h x))
  (deflistener (cat (exp h (mul x (rec w))) w))
  (precedes ((0 0) (2 0)) ((2 1) (1 0)))
  (non-orig (privk a) (privk b))
  (uniq-gen x)
  (precur (2 0))
  (operation nonce-test (added-listener (cat (exp h (mul x (rec w))) w))
    (exp h x) (1 0))
  (traces
    ((send (exp (gen) x))
      (recv (cat h (enc (enc h (exp (gen) x) (privk b)) (exp h x))))
      (send (enc (enc h (exp (gen) x) (privk a)) (exp h x))))
    ((recv (exp h x)) (send (exp h x)))
    ((recv (cat (exp h (mul x (rec w))) w))
      (send (cat (exp h (mul x (rec w))) w))))
  (label 40)
  (parent 35)
  (unrealized (0 1) (2 0))
  (comment "4 in cohort - 4 not yet seen"))

(defskeleton station-to-station-unflip
  (vars (a b name) (w expt) (x rndx))
  (defstrand init 3 (a a) (b b) (h (exp (gen) w)) (x x))
  (deflistener (exp (gen) (mul w x)))
  (deflistener (cat (exp (gen) x) w))
  (precedes ((0 0) (2 0)) ((2 1) (1 0)))
  (non-orig (privk a) (privk b))
  (uniq-gen x)
  (precur (2 0))
  (operation nonce-test (displaced 3 0 init 1) (exp (gen) x-0) (2 0))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) w)
          (enc (enc (exp (gen) w) (exp (gen) x) (privk b))
            (exp (gen) (mul w x)))))
      (send
        (enc (enc (exp (gen) w) (exp (gen) x) (privk a))
          (exp (gen) (mul w x)))))
    ((recv (exp (gen) (mul w x))) (send (exp (gen) (mul w x))))
    ((recv (cat (exp (gen) x) w)) (send (cat (exp (gen) x) w))))
  (label 41)
  (parent 40)
  (unrealized (0 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton station-to-station-unflip
  (vars (a b name) (x rndx) (w expt))
  (defstrand init 3 (a a) (b b) (h (exp (gen) (mul (rec x) w))) (x x))
  (deflistener (exp (gen) w))
  (deflistener (cat (gen) w))
  (precedes ((0 0) (2 0)) ((2 1) (1 0)))
  (non-orig (privk a) (privk b))
  (uniq-gen x)
  (precur (2 0))
  (operation nonce-test (contracted (h (exp (gen) (mul (rec x) w))))
    (gen) (2 0))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) (mul (rec x) w))
          (enc (enc (exp (gen) (mul (rec x) w)) (exp (gen) x) (privk b))
            (exp (gen) w))))
      (send
        (enc (enc (exp (gen) (mul (rec x) w)) (exp (gen) x) (privk a))
          (exp (gen) w)))) ((recv (exp (gen) w)) (send (exp (gen) w)))
    ((recv (cat (gen) w)) (send (cat (gen) w))))
  (label 42)
  (parent 40)
  (unrealized (0 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton station-to-station-unflip
  (vars (a b name) (x rndx) (w expt) (x-0 rndx))
  (defstrand init 3 (a a) (b b) (h (exp (gen) (mul (rec x) w x-0)))
    (x x))
  (deflistener (exp (gen) (mul w x-0)))
  (deflistener (cat (exp (gen) x-0) w))
  (defstrand init 1 (x x-0))
  (precedes ((0 0) (2 0)) ((2 1) (1 0)) ((3 0) (0 1)) ((3 0) (2 0)))
  (non-orig (privk a) (privk b))
  (uniq-gen x x-0)
  (precur (2 0))
  (operation nonce-test (added-strand init 1) (exp (gen) x-0) (2 0))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) (mul (rec x) w x-0))
          (enc
            (enc (exp (gen) (mul (rec x) w x-0)) (exp (gen) x)
              (privk b)) (exp (gen) (mul w x-0)))))
      (send
        (enc
          (enc (exp (gen) (mul (rec x) w x-0)) (exp (gen) x) (privk a))
          (exp (gen) (mul w x-0)))))
    ((recv (exp (gen) (mul w x-0))) (send (exp (gen) (mul w x-0))))
    ((recv (cat (exp (gen) x-0) w)) (send (cat (exp (gen) x-0) w)))
    ((send (exp (gen) x-0))))
  (label 43)
  (parent 40)
  (unrealized (0 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton station-to-station-unflip
  (vars (a b b-0 name) (h base) (x rndx) (w expt) (y rndx))
  (defstrand init 3 (a a) (b b) (h (exp (gen) (mul (rec x) w y))) (x x))
  (deflistener (exp (gen) (mul w y)))
  (deflistener (cat (exp (gen) y) w))
  (defstrand resp 2 (b b-0) (h h) (y y))
  (precedes ((0 0) (2 0)) ((2 1) (1 0)) ((3 1) (0 1)) ((3 1) (2 0)))
  (non-orig (privk a) (privk b))
  (uniq-gen x y)
  (precur (2 0))
  (operation nonce-test (added-strand resp 2) (exp (gen) y) (2 0))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) (mul (rec x) w y))
          (enc
            (enc (exp (gen) (mul (rec x) w y)) (exp (gen) x) (privk b))
            (exp (gen) (mul w y)))))
      (send
        (enc (enc (exp (gen) (mul (rec x) w y)) (exp (gen) x) (privk a))
          (exp (gen) (mul w y)))))
    ((recv (exp (gen) (mul w y))) (send (exp (gen) (mul w y))))
    ((recv (cat (exp (gen) y) w)) (send (cat (exp (gen) y) w)))
    ((recv h)
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) h (privk b-0)) (exp h y))))))
  (label 44)
  (parent 40)
  (unrealized (0 1))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-to-station-unflip
  (vars (a b name) (x y rndx))
  (defstrand init 3 (a a) (b b) (h (exp (gen) y)) (x x))
  (deflistener (exp (gen) (mul x y)))
  (deflistener (cat (exp (gen) x) y))
  (defstrand resp 2 (b b) (h (exp (gen) x)) (y y))
  (precedes ((0 0) (3 0)) ((2 1) (1 0)) ((3 1) (0 1)) ((3 1) (2 0)))
  (non-orig (privk a) (privk b))
  (uniq-gen x y)
  (precur (2 0))
  (operation encryption-test (added-strand resp 2)
    (enc (exp (gen) y) (exp (gen) x) (privk b)) (0 1))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (send
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul x y)))))
    ((recv (exp (gen) (mul x y))) (send (exp (gen) (mul x y))))
    ((recv (cat (exp (gen) x) y)) (send (cat (exp (gen) x) y)))
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))))
  (label 45)
  (parent 41)
  (unrealized (2 0))
  (dead)
  (comment "empty cohort"))

(defskeleton station-to-station-unflip
  (vars (a b name) (x y rndx))
  (defstrand init 3 (a a) (b b) (h (exp (gen) y)) (x x))
  (deflistener (exp (gen) (mul x y)))
  (deflistener (cat (gen) (mul x y)))
  (defstrand resp 2 (b b) (h (exp (gen) x)) (y y))
  (precedes ((0 0) (3 0)) ((2 1) (1 0)) ((3 1) (0 1)) ((3 1) (2 0)))
  (non-orig (privk a) (privk b))
  (uniq-gen x y)
  (precur (2 0))
  (operation encryption-test (added-strand resp 2)
    (enc (exp (gen) y) (exp (gen) x) (privk b)) (0 1))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (send
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul x y)))))
    ((recv (exp (gen) (mul x y))) (send (exp (gen) (mul x y))))
    ((recv (cat (gen) (mul x y))) (send (cat (gen) (mul x y))))
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))))
  (label 46)
  (parent 42)
  (unrealized (1 0) (2 0))
  (dead)
  (comment "empty cohort"))

(defskeleton station-to-station-unflip
  (vars (a b name) (x x-0 y rndx))
  (defstrand init 3 (a a) (b b) (h (exp (gen) y)) (x x))
  (deflistener (exp (gen) (mul x y)))
  (deflistener (cat (exp (gen) x-0) (mul x (rec x-0) y)))
  (defstrand init 1 (x x-0))
  (defstrand resp 2 (b b) (h (exp (gen) x)) (y y))
  (precedes ((0 0) (4 0)) ((2 1) (1 0)) ((3 0) (0 1)) ((3 0) (2 0))
    ((4 1) (0 1)) ((4 1) (2 0)))
  (non-orig (privk a) (privk b))
  (uniq-gen x x-0 y)
  (precur (2 0))
  (operation encryption-test (added-strand resp 2)
    (enc (exp (gen) y) (exp (gen) x) (privk b)) (0 1))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (send
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul x y)))))
    ((recv (exp (gen) (mul x y))) (send (exp (gen) (mul x y))))
    ((recv (cat (exp (gen) x-0) (mul x (rec x-0) y)))
      (send (cat (exp (gen) x-0) (mul x (rec x-0) y))))
    ((send (exp (gen) x-0)))
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))))
  (label 47)
  (parent 43)
  (unrealized (1 0) (2 0))
  (dead)
  (comment "empty cohort"))

(defskeleton station-to-station-unflip
  (vars (a b name) (x y rndx))
  (defstrand init 3 (a a) (b b) (h (exp (gen) y)) (x x))
  (deflistener (exp (gen) (mul x y)))
  (deflistener (cat (exp (gen) y) x))
  (defstrand resp 2 (b b) (h (exp (gen) x)) (y y))
  (precedes ((0 0) (3 0)) ((2 1) (1 0)) ((3 1) (0 1)) ((3 1) (2 0)))
  (non-orig (privk a) (privk b))
  (uniq-gen x y)
  (precur (2 0))
  (operation encryption-test (displaced 4 3 resp 2)
    (enc (exp (gen) y-0) (exp (gen) x) (privk b-0)) (0 1))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (send
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul x y)))))
    ((recv (exp (gen) (mul x y))) (send (exp (gen) (mul x y))))
    ((recv (cat (exp (gen) y) x)) (send (cat (exp (gen) y) x)))
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))))
  (label 48)
  (parent 44)
  (unrealized (2 0))
  (dead)
  (comment "empty cohort"))

(defskeleton station-to-station-unflip
  (vars (a b b-0 name) (h base) (x y y-0 rndx))
  (defstrand init 3 (a a) (b b) (h (exp (gen) y-0)) (x x))
  (deflistener (exp (gen) (mul x y-0)))
  (deflistener (cat (exp (gen) y) (mul x (rec y) y-0)))
  (defstrand resp 2 (b b-0) (h h) (y y))
  (defstrand resp 2 (b b) (h (exp (gen) x)) (y y-0))
  (precedes ((0 0) (4 0)) ((2 1) (1 0)) ((3 1) (0 1)) ((3 1) (2 0))
    ((4 1) (0 1)) ((4 1) (2 0)))
  (non-orig (privk a) (privk b))
  (uniq-gen x y y-0)
  (precur (2 0))
  (operation encryption-test (added-strand resp 2)
    (enc (exp (gen) y-0) (exp (gen) x) (privk b)) (0 1))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y-0)
          (enc (enc (exp (gen) y-0) (exp (gen) x) (privk b))
            (exp (gen) (mul x y-0)))))
      (send
        (enc (enc (exp (gen) y-0) (exp (gen) x) (privk a))
          (exp (gen) (mul x y-0)))))
    ((recv (exp (gen) (mul x y-0))) (send (exp (gen) (mul x y-0))))
    ((recv (cat (exp (gen) y) (mul x (rec y) y-0)))
      (send (cat (exp (gen) y) (mul x (rec y) y-0))))
    ((recv h)
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) h (privk b-0)) (exp h y)))))
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y-0)
          (enc (enc (exp (gen) y-0) (exp (gen) x) (privk b))
            (exp (gen) (mul x y-0)))))))
  (label 49)
  (parent 44)
  (unrealized (1 0) (2 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol station-to-station-unflip diffie-hellman
  (defrole init
    (vars (x rndx) (h base) (a b name))
    (trace (send (exp (gen) x))
      (recv (cat h (enc (enc h (exp (gen) x) (privk b)) (exp h x))))
      (send (enc (enc h (exp (gen) x) (privk a)) (exp h x)))
      (send (privk a)))
    (uniq-gen x))
  (defrole resp
    (vars (y rndx) (h base) (a b name))
    (trace (recv h)
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) h (privk b)) (exp h y))))
      (recv (enc (enc (exp (gen) y) h (privk a)) (exp h y)))
      (send (privk b)))
    (uniq-gen y))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton station-to-station-unflip
  (vars (a b name) (h base) (y rndx))
  (defstrand resp 3 (a a) (b b) (h h) (y y))
  (deflistener (exp h y))
  (non-orig (privk a) (privk b))
  (uniq-gen y)
  (traces
    ((recv h)
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) h (privk b)) (exp h y))))
      (recv (enc (enc (exp (gen) y) h (privk a)) (exp h y))))
    ((recv (exp h y)) (send (exp h y))))
  (label 50)
  (unrealized (0 2) (1 0))
  (preskeleton)
  (origs)
  (comment "Not a skeleton"))

(defskeleton station-to-station-unflip
  (vars (a b name) (h base) (y rndx))
  (defstrand resp 3 (a a) (b b) (h h) (y y))
  (deflistener (exp h y))
  (precedes ((0 1) (1 0)))
  (non-orig (privk a) (privk b))
  (uniq-gen y)
  (traces
    ((recv h)
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) h (privk b)) (exp h y))))
      (recv (enc (enc (exp (gen) y) h (privk a)) (exp h y))))
    ((recv (exp h y)) (send (exp h y))))
  (label 51)
  (parent 50)
  (unrealized (0 2) (1 0))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton station-to-station-unflip
  (vars (a b name) (h base) (y rndx) (w expt))
  (defstrand resp 3 (a a) (b b) (h h) (y y))
  (deflistener (exp h y))
  (deflistener (cat (exp h (mul y (rec w))) w))
  (precedes ((0 1) (2 0)) ((2 1) (1 0)))
  (non-orig (privk a) (privk b))
  (uniq-gen y)
  (precur (2 0))
  (operation nonce-test (added-listener (cat (exp h (mul y (rec w))) w))
    (exp h y) (1 0))
  (traces
    ((recv h)
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) h (privk b)) (exp h y))))
      (recv (enc (enc (exp (gen) y) h (privk a)) (exp h y))))
    ((recv (exp h y)) (send (exp h y)))
    ((recv (cat (exp h (mul y (rec w))) w))
      (send (cat (exp h (mul y (rec w))) w))))
  (label 52)
  (parent 51)
  (unrealized (0 2) (2 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol station-to-station-unflip diffie-hellman
  (defrole init
    (vars (x rndx) (h base) (a b name))
    (trace (send (exp (gen) x))
      (recv (cat h (enc (enc h (exp (gen) x) (privk b)) (exp h x))))
      (send (enc (enc h (exp (gen) x) (privk a)) (exp h x)))
      (send (privk a)))
    (uniq-gen x))
  (defrole resp
    (vars (y rndx) (h base) (a b name))
    (trace (recv h)
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) h (privk b)) (exp h y))))
      (recv (enc (enc (exp (gen) y) h (privk a)) (exp h y)))
      (send (privk b)))
    (uniq-gen y))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton station-to-station-unflip
  (vars (a b a-0 name) (x y rndx))
  (defstrand init 4 (a a) (b b) (h (exp (gen) y)) (x x))
  (defstrand resp 4 (a a-0) (b b) (h (exp (gen) x)) (y y))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (uniq-orig (privk a) (privk b))
  (uniq-gen x y)
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (send
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul x y)))) (send (privk a)))
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a-0))
          (exp (gen) (mul x y)))) (send (privk b))))
  (label 53)
  (unrealized (1 2))
  (origs ((privk b) (1 3)) ((privk a) (0 3)))
  (comment "3 in cohort - 3 not yet seen"))

(defskeleton station-to-station-unflip
  (vars (a b name) (y x rndx))
  (defstrand init 4 (a a) (b b) (h (exp (gen) y)) (x x))
  (defstrand resp 4 (a a) (b b) (h (exp (gen) x)) (y y))
  (precedes ((0 0) (1 0)) ((0 2) (1 2)) ((1 1) (0 1)))
  (uniq-orig (privk a) (privk b))
  (uniq-gen y x)
  (operation encryption-test (displaced 2 0 init 3)
    (enc (enc (exp (gen) y) (exp (gen) x) (privk a-0))
      (exp (gen) (mul y x))) (1 2))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x)))))
      (send
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul y x)))) (send (privk a)))
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul y x)))) (send (privk b))))
  (label 54)
  (parent 53)
  (realized)
  (shape)
  (maps ((0 1) ((a a) (b b) (x x) (y y) (a-0 a))))
  (origs ((privk b) (1 3)) ((privk a) (0 3))))

(defskeleton station-to-station-unflip
  (vars (a b name) (x y rndx))
  (defstrand init 4 (a a) (b b) (h (exp (gen) y)) (x x))
  (defstrand resp 4 (a b) (b b) (h (exp (gen) x)) (y y))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (uniq-orig (privk a) (privk b))
  (uniq-gen x y)
  (operation encryption-test (displaced 2 1 resp 2)
    (enc (enc (exp (gen) y) (exp (gen) x) (privk a-0))
      (exp (gen) (mul x y))) (1 2))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (send
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul x y)))) (send (privk a)))
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
          (exp (gen) (mul x y)))) (send (privk b))))
  (label 55)
  (parent 53)
  (realized)
  (shape)
  (maps ((0 1) ((a a) (b b) (x x) (y y) (a-0 b))))
  (origs ((privk b) (1 3)) ((privk a) (0 3))))

(defskeleton station-to-station-unflip
  (vars (a b a-0 name) (x y rndx))
  (defstrand init 4 (a a) (b b) (h (exp (gen) y)) (x x))
  (defstrand resp 4 (a a-0) (b b) (h (exp (gen) x)) (y y))
  (deflistener (exp (gen) (mul x y)))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)) ((1 1) (2 0)) ((2 1) (1 2)))
  (uniq-orig (privk a) (privk b))
  (uniq-gen x y)
  (operation encryption-test (added-listener (exp (gen) (mul x y)))
    (enc (enc (exp (gen) y) (exp (gen) x) (privk a-0))
      (exp (gen) (mul x y))) (1 2))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (send
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul x y)))) (send (privk a)))
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a-0))
          (exp (gen) (mul x y)))) (send (privk b)))
    ((recv (exp (gen) (mul x y))) (send (exp (gen) (mul x y)))))
  (label 56)
  (parent 53)
  (unrealized (2 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-to-station-unflip
  (vars (a b a-0 name) (x y rndx))
  (defstrand init 4 (a a) (b b) (h (exp (gen) y)) (x x))
  (defstrand resp 4 (a a-0) (b b) (h (exp (gen) x)) (y y))
  (deflistener (exp (gen) (mul x y)))
  (deflistener (cat (exp (gen) x) y))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)) ((1 1) (3 0)) ((2 1) (1 2))
    ((3 1) (2 0)))
  (uniq-orig (privk a) (privk b))
  (uniq-gen x y)
  (operation nonce-test (added-listener (cat (exp (gen) x) y))
    (exp (gen) (mul x y)) (2 0))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (send
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul x y)))) (send (privk a)))
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a-0))
          (exp (gen) (mul x y)))) (send (privk b)))
    ((recv (exp (gen) (mul x y))) (send (exp (gen) (mul x y))))
    ((recv (cat (exp (gen) x) y)) (send (cat (exp (gen) x) y))))
  (label 57)
  (parent 56)
  (unrealized (3 0))
  (dead)
  (comment "empty cohort"))

(defskeleton station-to-station-unflip
  (vars (a b a-0 name) (x y rndx))
  (defstrand init 4 (a a) (b b) (h (exp (gen) y)) (x x))
  (defstrand resp 4 (a a-0) (b b) (h (exp (gen) x)) (y y))
  (deflistener (exp (gen) (mul x y)))
  (deflistener (cat (exp (gen) y) x))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)) ((1 1) (3 0)) ((2 1) (1 2))
    ((3 1) (2 0)))
  (uniq-orig (privk a) (privk b))
  (uniq-gen x y)
  (operation nonce-test (added-listener (cat (exp (gen) y) x))
    (exp (gen) (mul x y)) (2 0))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (send
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul x y)))) (send (privk a)))
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a-0))
          (exp (gen) (mul x y)))) (send (privk b)))
    ((recv (exp (gen) (mul x y))) (send (exp (gen) (mul x y))))
    ((recv (cat (exp (gen) y) x)) (send (cat (exp (gen) y) x))))
  (label 58)
  (parent 56)
  (unrealized (3 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol station-to-station-unflip diffie-hellman
  (defrole init
    (vars (x rndx) (h base) (a b name))
    (trace (send (exp (gen) x))
      (recv (cat h (enc (enc h (exp (gen) x) (privk b)) (exp h x))))
      (send (enc (enc h (exp (gen) x) (privk a)) (exp h x)))
      (send (privk a)))
    (uniq-gen x))
  (defrole resp
    (vars (y rndx) (h base) (a b name))
    (trace (recv h)
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) h (privk b)) (exp h y))))
      (recv (enc (enc (exp (gen) y) h (privk a)) (exp h y)))
      (send (privk b)))
    (uniq-gen y))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton station-to-station-unflip
  (vars (a b a-0 name) (x y rndx))
  (defstrand init 4 (a a) (b b) (h (exp (gen) y)) (x x))
  (defstrand resp 4 (a a-0) (b b) (h (exp (gen) x)) (y y))
  (deflistener (exp (gen) (mul x y)))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (uniq-orig (privk a) (privk b))
  (uniq-gen x y)
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (send
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul x y)))) (send (privk a)))
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a-0))
          (exp (gen) (mul x y)))) (send (privk b)))
    ((recv (exp (gen) (mul x y))) (send (exp (gen) (mul x y)))))
  (label 59)
  (unrealized (1 2) (2 0))
  (preskeleton)
  (origs ((privk b) (1 3)) ((privk a) (0 3)))
  (comment "Not a skeleton"))

(defskeleton station-to-station-unflip
  (vars (a b a-0 name) (x y rndx))
  (defstrand init 4 (a a) (b b) (h (exp (gen) y)) (x x))
  (defstrand resp 4 (a a-0) (b b) (h (exp (gen) x)) (y y))
  (deflistener (exp (gen) (mul x y)))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)) ((1 1) (2 0)))
  (uniq-orig (privk a) (privk b))
  (uniq-gen x y)
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (send
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul x y)))) (send (privk a)))
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a-0))
          (exp (gen) (mul x y)))) (send (privk b)))
    ((recv (exp (gen) (mul x y))) (send (exp (gen) (mul x y)))))
  (label 60)
  (parent 59)
  (unrealized (1 2) (2 0))
  (origs ((privk b) (1 3)) ((privk a) (0 3)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-to-station-unflip
  (vars (a b a-0 name) (x y rndx))
  (defstrand init 4 (a a) (b b) (h (exp (gen) y)) (x x))
  (defstrand resp 4 (a a-0) (b b) (h (exp (gen) x)) (y y))
  (deflistener (exp (gen) (mul x y)))
  (deflistener (cat (exp (gen) x) y))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)) ((1 1) (3 0)) ((3 1) (2 0)))
  (uniq-orig (privk a) (privk b))
  (uniq-gen x y)
  (operation nonce-test (added-listener (cat (exp (gen) x) y))
    (exp (gen) (mul x y)) (2 0))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (send
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul x y)))) (send (privk a)))
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a-0))
          (exp (gen) (mul x y)))) (send (privk b)))
    ((recv (exp (gen) (mul x y))) (send (exp (gen) (mul x y))))
    ((recv (cat (exp (gen) x) y)) (send (cat (exp (gen) x) y))))
  (label 61)
  (parent 60)
  (unrealized (1 2) (3 0))
  (dead)
  (comment "empty cohort"))

(defskeleton station-to-station-unflip
  (vars (a b a-0 name) (x y rndx))
  (defstrand init 4 (a a) (b b) (h (exp (gen) y)) (x x))
  (defstrand resp 4 (a a-0) (b b) (h (exp (gen) x)) (y y))
  (deflistener (exp (gen) (mul x y)))
  (deflistener (cat (exp (gen) y) x))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)) ((1 1) (3 0)) ((3 1) (2 0)))
  (uniq-orig (privk a) (privk b))
  (uniq-gen x y)
  (operation nonce-test (added-listener (cat (exp (gen) y) x))
    (exp (gen) (mul x y)) (2 0))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (send
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul x y)))) (send (privk a)))
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a-0))
          (exp (gen) (mul x y)))) (send (privk b)))
    ((recv (exp (gen) (mul x y))) (send (exp (gen) (mul x y))))
    ((recv (cat (exp (gen) y) x)) (send (cat (exp (gen) y) x))))
  (label 62)
  (parent 60)
  (unrealized (1 2) (3 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")
