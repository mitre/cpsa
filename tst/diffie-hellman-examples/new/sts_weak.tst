(herald "Station-to-station protocol:  Weakened version"
  (algebra diffie-hellman))

(comment "CPSA 4.4.4")
(comment "All input read from sts_weak.scm")

(defprotocol station-to-station diffie-hellman
  (defrole init
    (vars (x rndx) (eta expt) (a b name))
    (trace (send (exp (gen) x))
      (recv
        (cat (exp (gen) eta)
          (enc (enc (exp (gen) eta) (exp (gen) x) (privk b))
            (exp (gen) (mul x eta)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) eta) (privk a))
          (exp (gen) (mul x eta)))) (send (privk a))))
  (defrole resp
    (vars (y rndx) (chi expt) (a b name))
    (trace (recv (exp (gen) chi))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) chi) (privk b))
            (exp (gen) (mul y chi)))))
      (recv
        (enc (enc (exp (gen) chi) (exp (gen) y) (privk a))
          (exp (gen) (mul y chi)))) (send (privk b))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton station-to-station
  (vars (a b name) (x rndx) (eta expt))
  (defstrand init 3 (a a) (b b) (x x) (eta eta))
  (non-orig (privk a) (privk b))
  (uniq-gen x)
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) eta)
          (enc (enc (exp (gen) eta) (exp (gen) x) (privk b))
            (exp (gen) (mul x eta)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) eta) (privk a))
          (exp (gen) (mul x eta))))))
  (label 0)
  (unrealized (0 1))
  (origs)
  (ugens (x (0 0)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-to-station
  (vars (a b b-0 name) (x x-0 rndx))
  (defstrand init 3 (a a) (b b) (x x-0) (eta x))
  (defstrand init 3 (a b) (b b-0) (x x) (eta x-0))
  (precedes ((0 0) (1 1)) ((1 2) (0 1)))
  (non-orig (privk a) (privk b))
  (uniq-gen x-0)
  (operation encryption-test (added-strand init 3)
    (enc (exp (gen) x) (exp (gen) x-0) (privk b)) (0 1))
  (strand-map 0)
  (traces
    ((send (exp (gen) x-0))
      (recv
        (cat (exp (gen) x)
          (enc (enc (exp (gen) x) (exp (gen) x-0) (privk b))
            (exp (gen) (mul x x-0)))))
      (send
        (enc (enc (exp (gen) x-0) (exp (gen) x) (privk a))
          (exp (gen) (mul x x-0)))))
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) x-0)
          (enc (enc (exp (gen) x-0) (exp (gen) x) (privk b-0))
            (exp (gen) (mul x x-0)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) x-0) (privk b))
          (exp (gen) (mul x x-0))))))
  (label 1)
  (parent 0)
  (realized)
  (shape)
  (maps ((0) ((a a) (b b) (x x-0) (eta x))))
  (origs)
  (ugens (x-0 (0 0))))

(defskeleton station-to-station
  (vars (a b name) (y x rndx))
  (defstrand init 3 (a a) (b b) (x x) (eta y))
  (defstrand resp 2 (b b) (y y) (chi x))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a) (privk b))
  (uniq-gen x)
  (operation encryption-test (added-strand resp 2)
    (enc (exp (gen) y) (exp (gen) x) (privk b)) (0 1))
  (strand-map 0)
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) y) (privk a))
          (exp (gen) (mul y x)))))
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x)))))))
  (label 2)
  (parent 0)
  (realized)
  (shape)
  (maps ((0) ((a a) (b b) (x x) (eta y))))
  (origs)
  (ugens (x (0 0))))

(comment "Nothing left to do")

(defprotocol station-to-station diffie-hellman
  (defrole init
    (vars (x rndx) (eta expt) (a b name))
    (trace (send (exp (gen) x))
      (recv
        (cat (exp (gen) eta)
          (enc (enc (exp (gen) eta) (exp (gen) x) (privk b))
            (exp (gen) (mul x eta)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) eta) (privk a))
          (exp (gen) (mul x eta)))) (send (privk a))))
  (defrole resp
    (vars (y rndx) (chi expt) (a b name))
    (trace (recv (exp (gen) chi))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) chi) (privk b))
            (exp (gen) (mul y chi)))))
      (recv
        (enc (enc (exp (gen) chi) (exp (gen) y) (privk a))
          (exp (gen) (mul y chi)))) (send (privk b))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton station-to-station
  (vars (a b name) (y rndx) (chi expt))
  (defstrand resp 3 (a a) (b b) (y y) (chi chi))
  (non-orig (privk a) (privk b))
  (uniq-gen y)
  (traces
    ((recv (exp (gen) chi))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) chi) (privk b))
            (exp (gen) (mul y chi)))))
      (recv
        (enc (enc (exp (gen) chi) (exp (gen) y) (privk a))
          (exp (gen) (mul y chi))))))
  (label 3)
  (unrealized (0 2))
  (origs)
  (ugens (y (0 1)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-to-station
  (vars (a b b-0 name) (x y rndx))
  (defstrand resp 3 (a a) (b b) (y y) (chi x))
  (defstrand init 3 (a a) (b b-0) (x x) (eta y))
  (precedes ((0 1) (1 1)) ((1 2) (0 2)))
  (non-orig (privk a) (privk b))
  (uniq-gen y)
  (operation encryption-test (added-strand init 3)
    (enc (exp (gen) x) (exp (gen) y) (privk a)) (0 2))
  (strand-map 0)
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
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b-0))
            (exp (gen) (mul x y)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) y) (privk a))
          (exp (gen) (mul x y))))))
  (label 4)
  (parent 3)
  (realized)
  (shape)
  (maps ((0) ((a a) (b b) (y y) (chi x))))
  (origs)
  (ugens (y (0 1))))

(defskeleton station-to-station
  (vars (a b name) (y y-0 rndx))
  (defstrand resp 3 (a a) (b b) (y y-0) (chi y))
  (defstrand resp 2 (b a) (y y) (chi y-0))
  (precedes ((0 1) (1 0)) ((1 1) (0 2)))
  (non-orig (privk a) (privk b))
  (uniq-gen y-0)
  (operation encryption-test (added-strand resp 2)
    (enc (exp (gen) y) (exp (gen) y-0) (privk a)) (0 2))
  (strand-map 0)
  (traces
    ((recv (exp (gen) y))
      (send
        (cat (exp (gen) y-0)
          (enc (enc (exp (gen) y-0) (exp (gen) y) (privk b))
            (exp (gen) (mul y y-0)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) y-0) (privk a))
          (exp (gen) (mul y y-0)))))
    ((recv (exp (gen) y-0))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) y-0) (privk a))
            (exp (gen) (mul y y-0)))))))
  (label 5)
  (parent 3)
  (realized)
  (shape)
  (maps ((0) ((a a) (b b) (y y-0) (chi y))))
  (origs)
  (ugens (y-0 (0 1))))

(comment "Nothing left to do")

(defprotocol station-to-station diffie-hellman
  (defrole init
    (vars (x rndx) (eta expt) (a b name))
    (trace (send (exp (gen) x))
      (recv
        (cat (exp (gen) eta)
          (enc (enc (exp (gen) eta) (exp (gen) x) (privk b))
            (exp (gen) (mul x eta)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) eta) (privk a))
          (exp (gen) (mul x eta)))) (send (privk a))))
  (defrole resp
    (vars (y rndx) (chi expt) (a b name))
    (trace (recv (exp (gen) chi))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) chi) (privk b))
            (exp (gen) (mul y chi)))))
      (recv
        (enc (enc (exp (gen) chi) (exp (gen) y) (privk a))
          (exp (gen) (mul y chi)))) (send (privk b))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton station-to-station
  (vars (a b name) (x y rndx))
  (defstrand init 3 (a a) (b b) (x x) (eta y))
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
  (label 6)
  (unrealized (0 1))
  (origs)
  (ugens (x (0 0)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-to-station
  (vars (a b b-0 name) (x x-0 rndx))
  (defstrand init 3 (a a) (b b) (x x-0) (eta x))
  (defstrand init 3 (a b) (b b-0) (x x) (eta x-0))
  (precedes ((0 0) (1 1)) ((1 2) (0 1)))
  (non-orig (privk a) (privk b))
  (uniq-gen x x-0)
  (operation encryption-test (added-strand init 3)
    (enc (exp (gen) x) (exp (gen) x-0) (privk b)) (0 1))
  (strand-map 0)
  (traces
    ((send (exp (gen) x-0))
      (recv
        (cat (exp (gen) x)
          (enc (enc (exp (gen) x) (exp (gen) x-0) (privk b))
            (exp (gen) (mul x x-0)))))
      (send
        (enc (enc (exp (gen) x-0) (exp (gen) x) (privk a))
          (exp (gen) (mul x x-0)))))
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) x-0)
          (enc (enc (exp (gen) x-0) (exp (gen) x) (privk b-0))
            (exp (gen) (mul x x-0)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) x-0) (privk b))
          (exp (gen) (mul x x-0))))))
  (label 7)
  (parent 6)
  (unrealized (1 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton station-to-station
  (vars (a b name) (y x rndx))
  (defstrand init 3 (a a) (b b) (x x) (eta y))
  (defstrand resp 2 (b b) (y y) (chi x))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a) (privk b))
  (uniq-gen y x)
  (operation encryption-test (added-strand resp 2)
    (enc (exp (gen) y) (exp (gen) x) (privk b)) (0 1))
  (strand-map 0)
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) y) (privk a))
          (exp (gen) (mul y x)))))
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x)))))))
  (label 8)
  (parent 6)
  (realized)
  (shape)
  (maps ((0) ((a a) (b b) (x x) (y y))))
  (origs)
  (ugens (x (0 0)) (y (1 1))))

(defskeleton station-to-station
  (vars (a b b-0 name) (x x-0 rndx))
  (defstrand init 3 (a a) (b b) (x x-0) (eta x))
  (defstrand init 3 (a b) (b b-0) (x x) (eta x-0))
  (deflistener (exp (gen) (mul x x-0)))
  (precedes ((0 0) (2 0)) ((1 0) (2 0)) ((1 2) (0 1)) ((2 1) (1 1)))
  (non-orig (privk a) (privk b))
  (uniq-gen x x-0)
  (operation encryption-test (added-listener (exp (gen) (mul x x-0)))
    (enc (enc (exp (gen) x-0) (exp (gen) x) (privk b-0))
      (exp (gen) (mul x x-0))) (1 1))
  (strand-map 0 1)
  (traces
    ((send (exp (gen) x-0))
      (recv
        (cat (exp (gen) x)
          (enc (enc (exp (gen) x) (exp (gen) x-0) (privk b))
            (exp (gen) (mul x x-0)))))
      (send
        (enc (enc (exp (gen) x-0) (exp (gen) x) (privk a))
          (exp (gen) (mul x x-0)))))
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) x-0)
          (enc (enc (exp (gen) x-0) (exp (gen) x) (privk b-0))
            (exp (gen) (mul x x-0)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) x-0) (privk b))
          (exp (gen) (mul x x-0)))))
    ((recv (exp (gen) (mul x x-0))) (send (exp (gen) (mul x x-0)))))
  (label 9)
  (parent 7)
  (unrealized (2 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-to-station
  (vars (a b b-0 name) (x x-0 rndx))
  (defstrand init 3 (a a) (b b) (x x-0) (eta x))
  (defstrand init 3 (a b) (b b-0) (x x) (eta x-0))
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
    ((send (exp (gen) x-0))
      (recv
        (cat (exp (gen) x)
          (enc (enc (exp (gen) x) (exp (gen) x-0) (privk b))
            (exp (gen) (mul x x-0)))))
      (send
        (enc (enc (exp (gen) x-0) (exp (gen) x) (privk a))
          (exp (gen) (mul x x-0)))))
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) x-0)
          (enc (enc (exp (gen) x-0) (exp (gen) x) (privk b-0))
            (exp (gen) (mul x x-0)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) x-0) (privk b))
          (exp (gen) (mul x x-0)))))
    ((recv (exp (gen) (mul x x-0))) (send (exp (gen) (mul x x-0))))
    ((recv (cat (exp (gen) x) x-0)) (send (cat (exp (gen) x) x-0))))
  (label 10)
  (parent 9)
  (unrealized (3 0))
  (dead)
  (comment "empty cohort"))

(defskeleton station-to-station
  (vars (a b b-0 name) (x x-0 rndx))
  (defstrand init 3 (a a) (b b) (x x-0) (eta x))
  (defstrand init 3 (a b) (b b-0) (x x) (eta x-0))
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
    ((send (exp (gen) x-0))
      (recv
        (cat (exp (gen) x)
          (enc (enc (exp (gen) x) (exp (gen) x-0) (privk b))
            (exp (gen) (mul x x-0)))))
      (send
        (enc (enc (exp (gen) x-0) (exp (gen) x) (privk a))
          (exp (gen) (mul x x-0)))))
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) x-0)
          (enc (enc (exp (gen) x-0) (exp (gen) x) (privk b-0))
            (exp (gen) (mul x x-0)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) x-0) (privk b))
          (exp (gen) (mul x x-0)))))
    ((recv (exp (gen) (mul x x-0))) (send (exp (gen) (mul x x-0))))
    ((recv (cat (exp (gen) x-0) x)) (send (cat (exp (gen) x-0) x))))
  (label 11)
  (parent 9)
  (unrealized (3 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol station-to-station diffie-hellman
  (defrole init
    (vars (x rndx) (eta expt) (a b name))
    (trace (send (exp (gen) x))
      (recv
        (cat (exp (gen) eta)
          (enc (enc (exp (gen) eta) (exp (gen) x) (privk b))
            (exp (gen) (mul x eta)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) eta) (privk a))
          (exp (gen) (mul x eta)))) (send (privk a))))
  (defrole resp
    (vars (y rndx) (chi expt) (a b name))
    (trace (recv (exp (gen) chi))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) chi) (privk b))
            (exp (gen) (mul y chi)))))
      (recv
        (enc (enc (exp (gen) chi) (exp (gen) y) (privk a))
          (exp (gen) (mul y chi)))) (send (privk b))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton station-to-station
  (vars (a b name) (x y rndx))
  (defstrand resp 3 (a a) (b b) (y y) (chi x))
  (non-orig (privk a) (privk b))
  (uniq-gen x y)
  (traces
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul x y)))))
      (recv
        (enc (enc (exp (gen) x) (exp (gen) y) (privk a))
          (exp (gen) (mul x y))))))
  (label 12)
  (unrealized (0 2))
  (origs)
  (ugens (y (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton station-to-station
  (vars (a b b-0 name) (x y rndx))
  (defstrand resp 3 (a a) (b b) (y y) (chi x))
  (defstrand init 3 (a a) (b b-0) (x x) (eta y))
  (precedes ((0 1) (1 1)) ((1 0) (0 0)) ((1 2) (0 2)))
  (non-orig (privk a) (privk b))
  (uniq-gen x y)
  (operation encryption-test (added-strand init 3)
    (enc (exp (gen) x) (exp (gen) y) (privk a)) (0 2))
  (strand-map 0)
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
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b-0))
            (exp (gen) (mul x y)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) y) (privk a))
          (exp (gen) (mul x y))))))
  (label 13)
  (parent 12)
  (unrealized (1 1))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-to-station
  (vars (a b name) (y x rndx))
  (defstrand resp 3 (a a) (b b) (y y) (chi x))
  (defstrand init 3 (a a) (b b) (x x) (eta y))
  (precedes ((0 1) (1 1)) ((1 0) (0 0)) ((1 2) (0 2)))
  (non-orig (privk a) (privk b))
  (uniq-gen y x)
  (operation encryption-test (displaced 2 0 resp 2)
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
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) y) (privk a))
          (exp (gen) (mul y x))))))
  (label 14)
  (parent 13)
  (realized)
  (shape)
  (maps ((0) ((a a) (b b) (x x) (y y))))
  (origs)
  (ugens (x (1 0)) (y (0 1))))

(defskeleton station-to-station
  (vars (a b b-0 name) (x y rndx))
  (defstrand resp 3 (a a) (b b) (y y) (chi x))
  (defstrand init 3 (a a) (b b-0) (x x) (eta y))
  (deflistener (exp (gen) (mul x y)))
  (precedes ((0 1) (2 0)) ((1 0) (0 0)) ((1 2) (0 2)) ((2 1) (1 1)))
  (non-orig (privk a) (privk b))
  (uniq-gen x y)
  (operation encryption-test (added-listener (exp (gen) (mul x y)))
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
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b-0))
            (exp (gen) (mul x y)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) y) (privk a))
          (exp (gen) (mul x y)))))
    ((recv (exp (gen) (mul x y))) (send (exp (gen) (mul x y)))))
  (label 15)
  (parent 13)
  (unrealized (2 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-to-station
  (vars (a b b-0 name) (x y rndx))
  (defstrand resp 3 (a a) (b b) (y y) (chi x))
  (defstrand init 3 (a a) (b b-0) (x x) (eta y))
  (deflistener (exp (gen) (mul x y)))
  (deflistener (cat (exp (gen) x) y))
  (precedes ((0 1) (3 0)) ((1 0) (0 0)) ((1 2) (0 2)) ((2 1) (1 1))
    ((3 1) (2 0)))
  (non-orig (privk a) (privk b))
  (uniq-gen x y)
  (operation nonce-test (added-listener (cat (exp (gen) x) y))
    (exp (gen) (mul x y)) (2 0))
  (strand-map 0 1 2)
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
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b-0))
            (exp (gen) (mul x y)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) y) (privk a))
          (exp (gen) (mul x y)))))
    ((recv (exp (gen) (mul x y))) (send (exp (gen) (mul x y))))
    ((recv (cat (exp (gen) x) y)) (send (cat (exp (gen) x) y))))
  (label 16)
  (parent 15)
  (unrealized (3 0))
  (dead)
  (comment "empty cohort"))

(defskeleton station-to-station
  (vars (a b b-0 name) (x y rndx))
  (defstrand resp 3 (a a) (b b) (y y) (chi x))
  (defstrand init 3 (a a) (b b-0) (x x) (eta y))
  (deflistener (exp (gen) (mul x y)))
  (deflistener (cat (exp (gen) y) x))
  (precedes ((0 1) (3 0)) ((1 0) (0 0)) ((1 2) (0 2)) ((2 1) (1 1))
    ((3 1) (2 0)))
  (non-orig (privk a) (privk b))
  (uniq-gen x y)
  (operation nonce-test (added-listener (cat (exp (gen) y) x))
    (exp (gen) (mul x y)) (2 0))
  (strand-map 0 1 2)
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
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b-0))
            (exp (gen) (mul x y)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) y) (privk a))
          (exp (gen) (mul x y)))))
    ((recv (exp (gen) (mul x y))) (send (exp (gen) (mul x y))))
    ((recv (cat (exp (gen) y) x)) (send (cat (exp (gen) y) x))))
  (label 17)
  (parent 15)
  (unrealized (3 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol station-to-station diffie-hellman
  (defrole init
    (vars (x rndx) (eta expt) (a b name))
    (trace (send (exp (gen) x))
      (recv
        (cat (exp (gen) eta)
          (enc (enc (exp (gen) eta) (exp (gen) x) (privk b))
            (exp (gen) (mul x eta)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) eta) (privk a))
          (exp (gen) (mul x eta)))) (send (privk a))))
  (defrole resp
    (vars (y rndx) (chi expt) (a b name))
    (trace (recv (exp (gen) chi))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) chi) (privk b))
            (exp (gen) (mul y chi)))))
      (recv
        (enc (enc (exp (gen) chi) (exp (gen) y) (privk a))
          (exp (gen) (mul y chi)))) (send (privk b))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton station-to-station
  (vars (a b name) (x rndx) (eta expt))
  (defstrand init 3 (a a) (b b) (x x) (eta eta))
  (deflistener (exp (gen) (mul x eta)))
  (non-orig (privk a) (privk b))
  (uniq-gen x)
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) eta)
          (enc (enc (exp (gen) eta) (exp (gen) x) (privk b))
            (exp (gen) (mul x eta)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) eta) (privk a))
          (exp (gen) (mul x eta)))))
    ((recv (exp (gen) (mul x eta))) (send (exp (gen) (mul x eta)))))
  (label 18)
  (unrealized (0 1) (1 0))
  (preskeleton)
  (origs)
  (ugens (x (0 0)))
  (comment "Not a skeleton"))

(defskeleton station-to-station
  (vars (a b name) (x rndx) (eta expt))
  (defstrand init 3 (a a) (b b) (x x) (eta eta))
  (deflistener (exp (gen) (mul x eta)))
  (precedes ((0 0) (1 0)))
  (non-orig (privk a) (privk b))
  (uniq-gen x)
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) eta)
          (enc (enc (exp (gen) eta) (exp (gen) x) (privk b))
            (exp (gen) (mul x eta)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) eta) (privk a))
          (exp (gen) (mul x eta)))))
    ((recv (exp (gen) (mul x eta))) (send (exp (gen) (mul x eta)))))
  (label 19)
  (parent 18)
  (unrealized (0 1))
  (origs)
  (ugens (x (0 0)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-to-station
  (vars (a b b-0 name) (x x-0 rndx))
  (defstrand init 3 (a a) (b b) (x x-0) (eta x))
  (deflistener (exp (gen) (mul x x-0)))
  (defstrand init 3 (a b) (b b-0) (x x) (eta x-0))
  (precedes ((0 0) (1 0)) ((0 0) (2 1)) ((2 2) (0 1)))
  (non-orig (privk a) (privk b))
  (uniq-gen x-0)
  (operation encryption-test (added-strand init 3)
    (enc (exp (gen) x) (exp (gen) x-0) (privk b)) (0 1))
  (strand-map 0 1)
  (traces
    ((send (exp (gen) x-0))
      (recv
        (cat (exp (gen) x)
          (enc (enc (exp (gen) x) (exp (gen) x-0) (privk b))
            (exp (gen) (mul x x-0)))))
      (send
        (enc (enc (exp (gen) x-0) (exp (gen) x) (privk a))
          (exp (gen) (mul x x-0)))))
    ((recv (exp (gen) (mul x x-0))) (send (exp (gen) (mul x x-0))))
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) x-0)
          (enc (enc (exp (gen) x-0) (exp (gen) x) (privk b-0))
            (exp (gen) (mul x x-0)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) x-0) (privk b))
          (exp (gen) (mul x x-0))))))
  (label 20)
  (parent 19)
  (realized)
  (shape)
  (maps ((0 1) ((a a) (b b) (x x-0) (eta x))))
  (origs)
  (ugens (x-0 (0 0))))

(defskeleton station-to-station
  (vars (a b name) (y x rndx))
  (defstrand init 3 (a a) (b b) (x x) (eta y))
  (deflistener (exp (gen) (mul y x)))
  (defstrand resp 2 (b b) (y y) (chi x))
  (precedes ((0 0) (1 0)) ((0 0) (2 0)) ((2 1) (0 1)))
  (non-orig (privk a) (privk b))
  (uniq-gen x)
  (operation encryption-test (added-strand resp 2)
    (enc (exp (gen) y) (exp (gen) x) (privk b)) (0 1))
  (strand-map 0 1)
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) y) (privk a))
          (exp (gen) (mul y x)))))
    ((recv (exp (gen) (mul y x))) (send (exp (gen) (mul y x))))
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x)))))))
  (label 21)
  (parent 19)
  (realized)
  (shape)
  (maps ((0 1) ((a a) (b b) (x x) (eta y))))
  (origs)
  (ugens (x (0 0))))

(comment "Nothing left to do")

(defprotocol station-to-station diffie-hellman
  (defrole init
    (vars (x rndx) (eta expt) (a b name))
    (trace (send (exp (gen) x))
      (recv
        (cat (exp (gen) eta)
          (enc (enc (exp (gen) eta) (exp (gen) x) (privk b))
            (exp (gen) (mul x eta)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) eta) (privk a))
          (exp (gen) (mul x eta)))) (send (privk a))))
  (defrole resp
    (vars (y rndx) (chi expt) (a b name))
    (trace (recv (exp (gen) chi))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) chi) (privk b))
            (exp (gen) (mul y chi)))))
      (recv
        (enc (enc (exp (gen) chi) (exp (gen) y) (privk a))
          (exp (gen) (mul y chi)))) (send (privk b))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton station-to-station
  (vars (a b name) (y rndx) (chi expt))
  (defstrand resp 3 (a a) (b b) (y y) (chi chi))
  (deflistener (exp (gen) (mul y chi)))
  (non-orig (privk a) (privk b))
  (uniq-gen y)
  (traces
    ((recv (exp (gen) chi))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) chi) (privk b))
            (exp (gen) (mul y chi)))))
      (recv
        (enc (enc (exp (gen) chi) (exp (gen) y) (privk a))
          (exp (gen) (mul y chi)))))
    ((recv (exp (gen) (mul y chi))) (send (exp (gen) (mul y chi)))))
  (label 22)
  (unrealized (0 2) (1 0))
  (preskeleton)
  (origs)
  (ugens (y (0 1)))
  (comment "Not a skeleton"))

(defskeleton station-to-station
  (vars (a b name) (y rndx) (chi expt))
  (defstrand resp 3 (a a) (b b) (y y) (chi chi))
  (deflistener (exp (gen) (mul y chi)))
  (precedes ((0 1) (1 0)))
  (non-orig (privk a) (privk b))
  (uniq-gen y)
  (traces
    ((recv (exp (gen) chi))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) chi) (privk b))
            (exp (gen) (mul y chi)))))
      (recv
        (enc (enc (exp (gen) chi) (exp (gen) y) (privk a))
          (exp (gen) (mul y chi)))))
    ((recv (exp (gen) (mul y chi))) (send (exp (gen) (mul y chi)))))
  (label 23)
  (parent 22)
  (unrealized (0 2))
  (origs)
  (ugens (y (0 1)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-to-station
  (vars (a b b-0 name) (x y rndx))
  (defstrand resp 3 (a a) (b b) (y y) (chi x))
  (deflistener (exp (gen) (mul x y)))
  (defstrand init 3 (a a) (b b-0) (x x) (eta y))
  (precedes ((0 1) (1 0)) ((0 1) (2 1)) ((2 2) (0 2)))
  (non-orig (privk a) (privk b))
  (uniq-gen y)
  (operation encryption-test (added-strand init 3)
    (enc (exp (gen) x) (exp (gen) y) (privk a)) (0 2))
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
    ((recv (exp (gen) (mul x y))) (send (exp (gen) (mul x y))))
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b-0))
            (exp (gen) (mul x y)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) y) (privk a))
          (exp (gen) (mul x y))))))
  (label 24)
  (parent 23)
  (realized)
  (shape)
  (maps ((0 1) ((a a) (b b) (y y) (chi x))))
  (origs)
  (ugens (y (0 1))))

(defskeleton station-to-station
  (vars (a b name) (y y-0 rndx))
  (defstrand resp 3 (a a) (b b) (y y-0) (chi y))
  (deflistener (exp (gen) (mul y y-0)))
  (defstrand resp 2 (b a) (y y) (chi y-0))
  (precedes ((0 1) (1 0)) ((0 1) (2 0)) ((2 1) (0 2)))
  (non-orig (privk a) (privk b))
  (uniq-gen y-0)
  (operation encryption-test (added-strand resp 2)
    (enc (exp (gen) y) (exp (gen) y-0) (privk a)) (0 2))
  (strand-map 0 1)
  (traces
    ((recv (exp (gen) y))
      (send
        (cat (exp (gen) y-0)
          (enc (enc (exp (gen) y-0) (exp (gen) y) (privk b))
            (exp (gen) (mul y y-0)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) y-0) (privk a))
          (exp (gen) (mul y y-0)))))
    ((recv (exp (gen) (mul y y-0))) (send (exp (gen) (mul y y-0))))
    ((recv (exp (gen) y-0))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) y-0) (privk a))
            (exp (gen) (mul y y-0)))))))
  (label 25)
  (parent 23)
  (realized)
  (shape)
  (maps ((0 1) ((a a) (b b) (y y-0) (chi y))))
  (origs)
  (ugens (y-0 (0 1))))

(comment "Nothing left to do")

(defprotocol station-to-station diffie-hellman
  (defrole init
    (vars (x rndx) (eta expt) (a b name))
    (trace (send (exp (gen) x))
      (recv
        (cat (exp (gen) eta)
          (enc (enc (exp (gen) eta) (exp (gen) x) (privk b))
            (exp (gen) (mul x eta)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) eta) (privk a))
          (exp (gen) (mul x eta)))) (send (privk a))))
  (defrole resp
    (vars (y rndx) (chi expt) (a b name))
    (trace (recv (exp (gen) chi))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) chi) (privk b))
            (exp (gen) (mul y chi)))))
      (recv
        (enc (enc (exp (gen) chi) (exp (gen) y) (privk a))
          (exp (gen) (mul y chi)))) (send (privk b))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton station-to-station
  (vars (a b a-0 name) (x y rndx))
  (defstrand init 4 (a a) (b b) (x x) (eta y))
  (defstrand resp 4 (a a-0) (b b) (y y) (chi x))
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
  (label 26)
  (unrealized (1 2))
  (origs ((privk b) (1 3)) ((privk a) (0 3)))
  (ugens (x (0 0)) (y (1 1)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-to-station
  (vars (a b name) (x y rndx))
  (defstrand init 4 (a a) (b b) (x x) (eta y))
  (defstrand resp 4 (a a) (b b) (y y) (chi x))
  (precedes ((0 0) (1 0)) ((0 2) (1 2)) ((1 1) (0 1)))
  (uniq-orig (privk a) (privk b))
  (uniq-gen x y)
  (operation encryption-test (displaced 2 0 init 3)
    (enc (enc (exp (gen) x) (exp (gen) y) (privk a-0))
      (exp (gen) (mul x y))) (1 2))
  (strand-map 0 1)
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
        (enc (enc (exp (gen) x) (exp (gen) y) (privk a))
          (exp (gen) (mul x y)))) (send (privk b))))
  (label 27)
  (parent 26)
  (realized)
  (shape)
  (maps ((0 1) ((a a) (b b) (x x) (y y) (a-0 a))))
  (origs ((privk b) (1 3)) ((privk a) (0 3)))
  (ugens (x (0 0)) (y (1 1))))

(defskeleton station-to-station
  (vars (a b a-0 name) (x y rndx))
  (defstrand init 4 (a a) (b b) (x x) (eta y))
  (defstrand resp 4 (a a-0) (b b) (y y) (chi x))
  (deflistener (exp (gen) (mul x y)))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)) ((1 1) (2 0)) ((2 1) (1 2)))
  (uniq-orig (privk a) (privk b))
  (uniq-gen x y)
  (operation encryption-test (added-listener (exp (gen) (mul x y)))
    (enc (enc (exp (gen) x) (exp (gen) y) (privk a-0))
      (exp (gen) (mul x y))) (1 2))
  (strand-map 0 1)
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
  (label 28)
  (parent 26)
  (unrealized (2 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-to-station
  (vars (a b a-0 name) (x y rndx))
  (defstrand init 4 (a a) (b b) (x x) (eta y))
  (defstrand resp 4 (a a-0) (b b) (y y) (chi x))
  (deflistener (exp (gen) (mul x y)))
  (deflistener (cat (exp (gen) x) y))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)) ((1 1) (3 0)) ((2 1) (1 2))
    ((3 1) (2 0)))
  (uniq-orig (privk a) (privk b))
  (uniq-gen x y)
  (operation nonce-test (added-listener (cat (exp (gen) x) y))
    (exp (gen) (mul x y)) (2 0))
  (strand-map 0 1 2)
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
    ((recv (exp (gen) (mul x y))) (send (exp (gen) (mul x y))))
    ((recv (cat (exp (gen) x) y)) (send (cat (exp (gen) x) y))))
  (label 29)
  (parent 28)
  (unrealized (3 0))
  (dead)
  (comment "empty cohort"))

(defskeleton station-to-station
  (vars (a b a-0 name) (x y rndx))
  (defstrand init 4 (a a) (b b) (x x) (eta y))
  (defstrand resp 4 (a a-0) (b b) (y y) (chi x))
  (deflistener (exp (gen) (mul x y)))
  (deflistener (cat (exp (gen) y) x))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)) ((1 1) (3 0)) ((2 1) (1 2))
    ((3 1) (2 0)))
  (uniq-orig (privk a) (privk b))
  (uniq-gen x y)
  (operation nonce-test (added-listener (cat (exp (gen) y) x))
    (exp (gen) (mul x y)) (2 0))
  (strand-map 0 1 2)
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
    ((recv (exp (gen) (mul x y))) (send (exp (gen) (mul x y))))
    ((recv (cat (exp (gen) y) x)) (send (cat (exp (gen) y) x))))
  (label 30)
  (parent 28)
  (unrealized (3 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol station-to-station diffie-hellman
  (defrole init
    (vars (x rndx) (eta expt) (a b name))
    (trace (send (exp (gen) x))
      (recv
        (cat (exp (gen) eta)
          (enc (enc (exp (gen) eta) (exp (gen) x) (privk b))
            (exp (gen) (mul x eta)))))
      (send
        (enc (enc (exp (gen) x) (exp (gen) eta) (privk a))
          (exp (gen) (mul x eta)))) (send (privk a))))
  (defrole resp
    (vars (y rndx) (chi expt) (a b name))
    (trace (recv (exp (gen) chi))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) chi) (privk b))
            (exp (gen) (mul y chi)))))
      (recv
        (enc (enc (exp (gen) chi) (exp (gen) y) (privk a))
          (exp (gen) (mul y chi)))) (send (privk b))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton station-to-station
  (vars (a b a-0 name) (x y rndx))
  (defstrand init 4 (a a) (b b) (x x) (eta y))
  (defstrand resp 4 (a a-0) (b b) (y y) (chi x))
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
  (label 31)
  (unrealized (1 2) (2 0))
  (preskeleton)
  (origs ((privk b) (1 3)) ((privk a) (0 3)))
  (ugens (x (0 0)) (y (1 1)))
  (comment "Not a skeleton"))

(defskeleton station-to-station
  (vars (a b a-0 name) (x y rndx))
  (defstrand init 4 (a a) (b b) (x x) (eta y))
  (defstrand resp 4 (a a-0) (b b) (y y) (chi x))
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
  (label 32)
  (parent 31)
  (unrealized (1 2) (2 0))
  (origs ((privk b) (1 3)) ((privk a) (0 3)))
  (ugens (x (0 0)) (y (1 1)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-to-station
  (vars (a b a-0 name) (x y rndx))
  (defstrand init 4 (a a) (b b) (x x) (eta y))
  (defstrand resp 4 (a a-0) (b b) (y y) (chi x))
  (deflistener (exp (gen) (mul x y)))
  (deflistener (cat (exp (gen) x) y))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)) ((1 1) (3 0)) ((3 1) (2 0)))
  (uniq-orig (privk a) (privk b))
  (uniq-gen x y)
  (operation nonce-test (added-listener (cat (exp (gen) x) y))
    (exp (gen) (mul x y)) (2 0))
  (strand-map 0 1 2)
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
    ((recv (exp (gen) (mul x y))) (send (exp (gen) (mul x y))))
    ((recv (cat (exp (gen) x) y)) (send (cat (exp (gen) x) y))))
  (label 33)
  (parent 32)
  (unrealized (1 2) (3 0))
  (dead)
  (comment "empty cohort"))

(defskeleton station-to-station
  (vars (a b a-0 name) (x y rndx))
  (defstrand init 4 (a a) (b b) (x x) (eta y))
  (defstrand resp 4 (a a-0) (b b) (y y) (chi x))
  (deflistener (exp (gen) (mul x y)))
  (deflistener (cat (exp (gen) y) x))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)) ((1 1) (3 0)) ((3 1) (2 0)))
  (uniq-orig (privk a) (privk b))
  (uniq-gen x y)
  (operation nonce-test (added-listener (cat (exp (gen) y) x))
    (exp (gen) (mul x y)) (2 0))
  (strand-map 0 1 2)
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
    ((recv (exp (gen) (mul x y))) (send (exp (gen) (mul x y))))
    ((recv (cat (exp (gen) y) x)) (send (cat (exp (gen) y) x))))
  (label 34)
  (parent 32)
  (unrealized (1 2) (3 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")
