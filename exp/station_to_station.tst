(herald "Station-to-station protocol" (algebra diffie-hellman))

(comment "CPSA 2.3.4")
(comment "All input read from station_to_station.scm")

(defprotocol station-to-station diffie-hellman
  (defrole init
    (vars (x expn) (h base) (a b name))
    (trace (send (exp (gen) x))
      (recv (cat h (enc (enc h (exp (gen) x) (privk b)) (exp h x))))
      (send (enc (enc (exp (gen) x) h (privk a)) (exp h x))))
    (non-orig x)
    (uniq-orig (exp (gen) x)))
  (defrole resp
    (vars (y expn) (h base) (a b name))
    (trace (recv h)
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) h (privk b)) (exp h y))))
      (recv (enc (enc h (exp (gen) y) (privk a)) (exp h y))))
    (non-orig y)
    (uniq-orig (exp (gen) y))))

(defskeleton station-to-station
  (vars (a b name) (h base) (x expn))
  (defstrand init 3 (a a) (b b) (h h) (x x))
  (non-orig (privk a) (privk b) x)
  (uniq-orig (exp (gen) x))
  (traces
    ((send (exp (gen) x))
      (recv (cat h (enc (enc h (exp (gen) x) (privk b)) (exp h x))))
      (send (enc (enc (exp (gen) x) h (privk a)) (exp h x)))))
  (label 0)
  (unrealized (0 1))
  (origs ((exp (gen) x) (0 0)))
  (comment "3 in cohort - 3 not yet seen"))

(defskeleton station-to-station
  (vars (a b b-0 name) (x x-0 expn))
  (defstrand init 3 (a a) (b b) (h (exp (gen) x-0)) (x x))
  (defstrand init 3 (a b) (b b-0) (h (exp (gen) x)) (x x-0))
  (precedes ((0 0) (1 1)) ((1 2) (0 1)))
  (non-orig (privk a) (privk b) x x-0)
  (uniq-orig (exp (gen) x) (exp (gen) x-0))
  (operation encryption-test (added-strand init 3)
    (enc (enc (exp (gen) x-0) (exp (gen) x) (privk b))
      (exp (gen) (mul x x-0))) (0 1))
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

(defskeleton station-to-station
  (vars (a b name) (x y expn))
  (defstrand init 3 (a a) (b b) (h (exp (gen) y)) (x x))
  (defstrand resp 2 (b b) (h (exp (gen) x)) (y y))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a) (privk b) x y)
  (uniq-orig (exp (gen) x) (exp (gen) y))
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
        (enc (enc (exp (gen) x) (exp (gen) y) (privk a))
          (exp (gen) (mul x y)))))
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))))
  (label 2)
  (parent 0)
  (unrealized)
  (shape)
  (maps ((0) ((a a) (b b) (x x) (h (exp (gen) y)))))
  (origs ((exp (gen) y) (1 1)) ((exp (gen) x) (0 0))))

(defskeleton station-to-station
  (vars (a b name) (h base) (x expn))
  (defstrand init 3 (a a) (b b) (h h) (x x))
  (deflistener (exp h x))
  (precedes ((1 1) (0 1)))
  (non-orig (privk a) (privk b) x)
  (uniq-orig (exp (gen) x))
  (operation encryption-test (added-listener (exp h x))
    (enc (enc h (exp (gen) x) (privk b)) (exp h x)) (0 1))
  (traces
    ((send (exp (gen) x))
      (recv (cat h (enc (enc h (exp (gen) x) (privk b)) (exp h x))))
      (send (enc (enc (exp (gen) x) h (privk a)) (exp h x))))
    ((recv (exp h x)) (send (exp h x))))
  (label 3)
  (parent 0)
  (unrealized (0 1) (1 0))
  (comment "3 in cohort - 3 not yet seen"))

(defskeleton station-to-station
  (vars (a b b-0 name) (x x-0 expn))
  (defstrand init 3 (a a) (b b) (h (exp (gen) x-0)) (x x))
  (defstrand init 3 (a b) (b b-0) (h (exp (gen) x)) (x x-0))
  (deflistener (exp (gen) (mul x x-0)))
  (precedes ((0 0) (1 1)) ((1 2) (0 1)) ((2 1) (1 1)))
  (non-orig (privk a) (privk b) x x-0)
  (uniq-orig (exp (gen) x) (exp (gen) x-0))
  (operation encryption-test (added-listener (exp (gen) (mul x x-0)))
    (enc (enc (exp (gen) x) (exp (gen) x-0) (privk b-0))
      (exp (gen) (mul x x-0))) (1 1))
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
  (label 4)
  (parent 1)
  (unrealized (2 0))
  (comment "empty cohort"))

(defskeleton station-to-station
  (vars (a b name) (x expn))
  (defstrand init 3 (a a) (b b) (h (gen)) (x x))
  (deflistener (exp (gen) x))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a) (privk b) x)
  (uniq-orig (exp (gen) x))
  (operation encryption-test (displaced 2 0 init 1) (exp (gen) x-0)
    (1 0))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (gen)
          (enc (enc (gen) (exp (gen) x) (privk b)) (exp (gen) x))))
      (send (enc (enc (exp (gen) x) (gen) (privk a)) (exp (gen) x))))
    ((recv (exp (gen) x)) (send (exp (gen) x))))
  (label 5)
  (parent 3)
  (unrealized (0 1))
  (comment "empty cohort"))

(defskeleton station-to-station
  (vars (a b name) (x x-0 expn))
  (defstrand init 3 (a a) (b b) (h (exp (gen) (mul (rec x) x-0))) (x x))
  (deflistener (exp (gen) x-0))
  (defstrand init 1 (x x-0))
  (precedes ((1 1) (0 1)) ((2 0) (1 0)))
  (non-orig (privk a) (privk b) x x-0)
  (uniq-orig (exp (gen) x) (exp (gen) x-0))
  (operation encryption-test (added-strand init 1) (exp (gen) x-0)
    (1 0))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) (mul (rec x) x-0))
          (enc
            (enc (exp (gen) (mul (rec x) x-0)) (exp (gen) x) (privk b))
            (exp (gen) x-0))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) (mul (rec x) x-0)) (privk a))
          (exp (gen) x-0))))
    ((recv (exp (gen) x-0)) (send (exp (gen) x-0)))
    ((send (exp (gen) x-0))))
  (label 6)
  (parent 3)
  (unrealized (0 1))
  (comment "empty cohort"))

(defskeleton station-to-station
  (vars (a b b-0 name) (h base) (x y expn))
  (defstrand init 3 (a a) (b b) (h (exp (gen) (mul (rec x) y))) (x x))
  (deflistener (exp (gen) y))
  (defstrand resp 2 (b b-0) (h h) (y y))
  (precedes ((1 1) (0 1)) ((2 1) (1 0)))
  (non-orig (privk a) (privk b) x y)
  (uniq-orig (exp (gen) x) (exp (gen) y))
  (operation encryption-test (added-strand resp 2) (exp (gen) y) (1 0))
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) (mul (rec x) y))
          (enc (enc (exp (gen) (mul (rec x) y)) (exp (gen) x) (privk b))
            (exp (gen) y))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) (mul (rec x) y)) (privk a))
          (exp (gen) y)))) ((recv (exp (gen) y)) (send (exp (gen) y)))
    ((recv h)
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) h (privk b-0)) (exp h y))))))
  (label 7)
  (parent 3)
  (unrealized (0 1))
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol station-to-station diffie-hellman
  (defrole init
    (vars (x expn) (h base) (a b name))
    (trace (send (exp (gen) x))
      (recv (cat h (enc (enc h (exp (gen) x) (privk b)) (exp h x))))
      (send (enc (enc (exp (gen) x) h (privk a)) (exp h x))))
    (non-orig x)
    (uniq-orig (exp (gen) x)))
  (defrole resp
    (vars (y expn) (h base) (a b name))
    (trace (recv h)
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) h (privk b)) (exp h y))))
      (recv (enc (enc h (exp (gen) y) (privk a)) (exp h y))))
    (non-orig y)
    (uniq-orig (exp (gen) y))))

(defskeleton station-to-station
  (vars (a b name) (h base) (y expn))
  (defstrand resp 3 (a a) (b b) (h h) (y y))
  (non-orig (privk a) (privk b) y)
  (uniq-orig (exp (gen) y))
  (traces
    ((recv h)
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) h (privk b)) (exp h y))))
      (recv (enc (enc h (exp (gen) y) (privk a)) (exp h y)))))
  (label 8)
  (unrealized (0 2))
  (origs ((exp (gen) y) (0 1)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-to-station
  (vars (a b b-0 name) (y x expn))
  (defstrand resp 3 (a a) (b b) (h (exp (gen) x)) (y y))
  (defstrand init 3 (a a) (b b-0) (h (exp (gen) y)) (x x))
  (precedes ((0 1) (1 1)) ((1 0) (0 0)) ((1 2) (0 2)))
  (non-orig (privk a) (privk b) y x)
  (uniq-orig (exp (gen) y) (exp (gen) x))
  (operation encryption-test (added-strand init 3)
    (enc (enc (exp (gen) x) (exp (gen) y) (privk a))
      (exp (gen) (mul y x))) (0 2))
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
  (label 9)
  (parent 8)
  (unrealized (1 1))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-to-station
  (vars (a b name) (h base) (y expn))
  (defstrand resp 3 (a a) (b b) (h h) (y y))
  (deflistener (exp h y))
  (precedes ((1 1) (0 2)))
  (non-orig (privk a) (privk b) y)
  (uniq-orig (exp (gen) y))
  (operation encryption-test (added-listener (exp h y))
    (enc (enc h (exp (gen) y) (privk a)) (exp h y)) (0 2))
  (traces
    ((recv h)
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) h (privk b)) (exp h y))))
      (recv (enc (enc h (exp (gen) y) (privk a)) (exp h y))))
    ((recv (exp h y)) (send (exp h y))))
  (label 10)
  (parent 8)
  (unrealized (0 2) (1 0))
  (comment "3 in cohort - 3 not yet seen"))

(defskeleton station-to-station
  (vars (a b name) (x y expn))
  (defstrand resp 3 (a a) (b b) (h (exp (gen) x)) (y y))
  (defstrand init 3 (a a) (b b) (h (exp (gen) y)) (x x))
  (precedes ((0 1) (1 1)) ((1 0) (0 0)) ((1 2) (0 2)))
  (non-orig (privk a) (privk b) x y)
  (uniq-orig (exp (gen) x) (exp (gen) y))
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
  (label 11)
  (parent 9)
  (unrealized)
  (shape)
  (maps ((0) ((a a) (b b) (y y) (h (exp (gen) x)))))
  (origs ((exp (gen) y) (0 1)) ((exp (gen) x) (1 0))))

(defskeleton station-to-station
  (vars (a b b-0 name) (y x expn))
  (defstrand resp 3 (a a) (b b) (h (exp (gen) x)) (y y))
  (defstrand init 3 (a a) (b b-0) (h (exp (gen) y)) (x x))
  (deflistener (exp (gen) (mul y x)))
  (precedes ((0 1) (1 1)) ((1 0) (0 0)) ((1 2) (0 2)) ((2 1) (1 1)))
  (non-orig (privk a) (privk b) y x)
  (uniq-orig (exp (gen) y) (exp (gen) x))
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
  (label 12)
  (parent 9)
  (unrealized (2 0))
  (comment "empty cohort"))

(defskeleton station-to-station
  (vars (a b name) (y x expn))
  (defstrand resp 3 (a a) (b b) (h (exp (gen) (mul (rec y) x))) (y y))
  (deflistener (exp (gen) x))
  (defstrand init 1 (x x))
  (precedes ((1 1) (0 2)) ((2 0) (1 0)))
  (non-orig (privk a) (privk b) y x)
  (uniq-orig (exp (gen) y) (exp (gen) x))
  (operation encryption-test (added-strand init 1) (exp (gen) x) (1 0))
  (traces
    ((recv (exp (gen) (mul (rec y) x)))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) (mul (rec y) x)) (privk b))
            (exp (gen) x))))
      (recv
        (enc (enc (exp (gen) (mul (rec y) x)) (exp (gen) y) (privk a))
          (exp (gen) x)))) ((recv (exp (gen) x)) (send (exp (gen) x)))
    ((send (exp (gen) x))))
  (label 13)
  (parent 10)
  (unrealized (0 0) (0 2))
  (comment "empty cohort"))

(defskeleton station-to-station
  (vars (a b name) (y expn))
  (defstrand resp 3 (a a) (b b) (h (gen)) (y y))
  (deflistener (exp (gen) y))
  (precedes ((0 1) (1 0)) ((1 1) (0 2)))
  (non-orig (privk a) (privk b) y)
  (uniq-orig (exp (gen) y))
  (operation encryption-test (displaced 2 0 resp 2) (exp (gen) y-0)
    (1 0))
  (traces
    ((recv (gen))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (gen) (privk b)) (exp (gen) y))))
      (recv (enc (enc (gen) (exp (gen) y) (privk a)) (exp (gen) y))))
    ((recv (exp (gen) y)) (send (exp (gen) y))))
  (label 14)
  (parent 10)
  (unrealized (0 2))
  (comment "empty cohort"))

(defskeleton station-to-station
  (vars (a b b-0 name) (h base) (y y-0 expn))
  (defstrand resp 3 (a a) (b b) (h (exp (gen) (mul (rec y) y-0))) (y y))
  (deflistener (exp (gen) y-0))
  (defstrand resp 2 (b b-0) (h h) (y y-0))
  (precedes ((1 1) (0 2)) ((2 1) (1 0)))
  (non-orig (privk a) (privk b) y y-0)
  (uniq-orig (exp (gen) y) (exp (gen) y-0))
  (operation encryption-test (added-strand resp 2) (exp (gen) y-0)
    (1 0))
  (traces
    ((recv (exp (gen) (mul (rec y) y-0)))
      (send
        (cat (exp (gen) y)
          (enc
            (enc (exp (gen) y) (exp (gen) (mul (rec y) y-0)) (privk b))
            (exp (gen) y-0))))
      (recv
        (enc (enc (exp (gen) (mul (rec y) y-0)) (exp (gen) y) (privk a))
          (exp (gen) y-0))))
    ((recv (exp (gen) y-0)) (send (exp (gen) y-0)))
    ((recv h)
      (send
        (cat (exp (gen) y-0)
          (enc (enc (exp (gen) y-0) h (privk b-0)) (exp h y-0))))))
  (label 15)
  (parent 10)
  (unrealized (0 0) (0 2))
  (comment "empty cohort"))

(comment "Nothing left to do")
