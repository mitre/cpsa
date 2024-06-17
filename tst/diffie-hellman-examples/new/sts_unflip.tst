(herald "Station-to-station protocol" (bound 20)
  (algebra diffie-hellman))

(comment "CPSA 4.4.4")
(comment "All input read from sts_unflip.scm")
(comment "Strand count bounded at 20")

(defprotocol station-to-station diffie-hellman
  (defrole init
    (vars (x rndx) (eta expt) (a b name))
    (trace (send (exp (gen) x))
      (recv
        (cat (exp (gen) eta)
          (enc (enc (exp (gen) eta) (exp (gen) x) (privk b))
            (exp (gen) (mul x eta)))))
      (send
        (enc (enc (exp (gen) eta) (exp (gen) x) (privk a))
          (exp (gen) (mul x eta)))) (send (privk a)))
    (uniq-gen x))
  (defrole resp
    (vars (y rndx) (chi expt) (a b name))
    (trace (recv (exp (gen) chi))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) chi) (privk b))
            (exp (gen) (mul y chi)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) chi) (privk a))
          (exp (gen) (mul y chi)))) (send (privk b)))
    (uniq-gen y)
    (absent (y chi)))
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
        (enc (enc (exp (gen) eta) (exp (gen) x) (privk a))
          (exp (gen) (mul x eta))))))
  (label 0)
  (unrealized (0 1))
  (origs)
  (ugens (x (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton station-to-station
  (vars (a b name) (y x rndx))
  (defstrand init 3 (a a) (b b) (x x) (eta y))
  (defstrand resp 2 (b b) (y y) (chi x))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a) (privk b))
  (uniq-gen y x)
  (absent (y x))
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
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul y x)))))
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x)))))))
  (label 1)
  (parent 0)
  (realized)
  (shape)
  (maps ((0) ((a a) (b b) (x x) (eta y))))
  (origs)
  (ugens (y (1 1)) (x (0 0))))

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
        (enc (enc (exp (gen) eta) (exp (gen) x) (privk a))
          (exp (gen) (mul x eta)))) (send (privk a)))
    (uniq-gen x))
  (defrole resp
    (vars (y rndx) (chi expt) (a b name))
    (trace (recv (exp (gen) chi))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) chi) (privk b))
            (exp (gen) (mul y chi)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) chi) (privk a))
          (exp (gen) (mul y chi)))) (send (privk b)))
    (uniq-gen y)
    (absent (y chi)))
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
  (absent (y chi))
  (traces
    ((recv (exp (gen) chi))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) chi) (privk b))
            (exp (gen) (mul y chi)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) chi) (privk a))
          (exp (gen) (mul y chi))))))
  (label 2)
  (unrealized (0 2))
  (origs)
  (ugens (y (0 1)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-to-station
  (vars (a b b-0 name) (y x rndx))
  (defstrand resp 3 (a a) (b b) (y y) (chi x))
  (defstrand init 3 (a a) (b b-0) (x x) (eta y))
  (precedes ((0 1) (1 1)) ((1 0) (0 0)) ((1 2) (0 2)))
  (non-orig (privk a) (privk b))
  (uniq-gen y x)
  (absent (y x))
  (operation encryption-test (added-strand init 3)
    (enc (exp (gen) y) (exp (gen) x) (privk a)) (0 2))
  (strand-map 0)
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
  (label 3)
  (parent 2)
  (unrealized (1 1))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-to-station
  (vars (b name) (y rndx) (chi expt))
  (defstrand resp 3 (a b) (b b) (y y) (chi chi))
  (non-orig (privk b))
  (uniq-gen y)
  (absent (y chi))
  (operation encryption-test (displaced 1 0 resp 2)
    (enc (exp (gen) y) (exp (gen) chi) (privk a)) (0 2))
  (strand-map 0)
  (traces
    ((recv (exp (gen) chi))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) chi) (privk b))
            (exp (gen) (mul y chi)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) chi) (privk b))
          (exp (gen) (mul y chi))))))
  (label 4)
  (parent 2)
  (realized)
  (shape)
  (maps ((0) ((a b) (b b) (y y) (chi chi))))
  (origs)
  (ugens (y (0 1))))

(defskeleton station-to-station
  (vars (a b name) (y x rndx))
  (defstrand resp 3 (a a) (b b) (y y) (chi x))
  (defstrand init 3 (a a) (b b) (x x) (eta y))
  (precedes ((0 1) (1 1)) ((1 0) (0 0)) ((1 2) (0 2)))
  (non-orig (privk a) (privk b))
  (uniq-gen y x)
  (absent (y x))
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
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul y x)))))
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x)))))
      (send
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul y x))))))
  (label 5)
  (parent 3)
  (realized)
  (shape)
  (maps ((0) ((a a) (b b) (y y) (chi x))))
  (origs)
  (ugens (y (0 1)) (x (1 0))))

(defskeleton station-to-station
  (vars (a b b-0 name) (y x rndx))
  (defstrand resp 3 (a a) (b b) (y y) (chi x))
  (defstrand init 3 (a a) (b b-0) (x x) (eta y))
  (deflistener (exp (gen) (mul y x)))
  (precedes ((0 1) (2 0)) ((1 0) (0 0)) ((1 2) (0 2)) ((2 1) (1 1)))
  (non-orig (privk a) (privk b))
  (uniq-gen y x)
  (absent (y x))
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
  (label 6)
  (parent 3)
  (unrealized (2 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-to-station
  (vars (a b b-0 name) (y x rndx))
  (defstrand resp 3 (a a) (b b) (y y) (chi x))
  (defstrand init 3 (a a) (b b-0) (x x) (eta y))
  (deflistener (exp (gen) (mul y x)))
  (deflistener (cat (exp (gen) y) x))
  (precedes ((0 1) (3 0)) ((1 0) (0 0)) ((1 2) (0 2)) ((2 1) (1 1))
    ((3 1) (2 0)))
  (non-orig (privk a) (privk b))
  (uniq-gen y x)
  (absent (y x))
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
  (label 7)
  (parent 6)
  (unrealized (3 0))
  (dead)
  (comment "empty cohort"))

(defskeleton station-to-station
  (vars (a b b-0 name) (y x rndx))
  (defstrand resp 3 (a a) (b b) (y y) (chi x))
  (defstrand init 3 (a a) (b b-0) (x x) (eta y))
  (deflistener (exp (gen) (mul y x)))
  (deflistener (cat (exp (gen) x) y))
  (precedes ((0 1) (3 0)) ((1 0) (0 0)) ((1 2) (0 2)) ((2 1) (1 1))
    ((3 1) (2 0)))
  (non-orig (privk a) (privk b))
  (uniq-gen y x)
  (absent (y x))
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
  (label 8)
  (parent 6)
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
        (enc (enc (exp (gen) eta) (exp (gen) x) (privk a))
          (exp (gen) (mul x eta)))) (send (privk a)))
    (uniq-gen x))
  (defrole resp
    (vars (y rndx) (chi expt) (a b name))
    (trace (recv (exp (gen) chi))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) chi) (privk b))
            (exp (gen) (mul y chi)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) chi) (privk a))
          (exp (gen) (mul y chi)))) (send (privk b)))
    (uniq-gen y)
    (absent (y chi)))
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
        (enc (enc (exp (gen) eta) (exp (gen) x) (privk a))
          (exp (gen) (mul x eta)))))
    ((recv (exp (gen) (mul x eta))) (send (exp (gen) (mul x eta)))))
  (label 9)
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
        (enc (enc (exp (gen) eta) (exp (gen) x) (privk a))
          (exp (gen) (mul x eta)))))
    ((recv (exp (gen) (mul x eta))) (send (exp (gen) (mul x eta)))))
  (label 10)
  (parent 9)
  (unrealized (0 1))
  (origs)
  (ugens (x (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton station-to-station
  (vars (a b name) (y x rndx))
  (defstrand init 3 (a a) (b b) (x x) (eta y))
  (deflistener (exp (gen) (mul y x)))
  (defstrand resp 2 (b b) (y y) (chi x))
  (precedes ((0 0) (2 0)) ((2 1) (0 1)) ((2 1) (1 0)))
  (non-orig (privk a) (privk b))
  (uniq-gen y x)
  (absent (y x))
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
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul y x)))))
    ((recv (exp (gen) (mul y x))) (send (exp (gen) (mul y x))))
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x)))))))
  (label 11)
  (parent 10)
  (unrealized (1 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-to-station
  (vars (a b name) (y x rndx))
  (defstrand init 3 (a a) (b b) (x x) (eta y))
  (deflistener (exp (gen) (mul y x)))
  (defstrand resp 2 (b b) (y y) (chi x))
  (deflistener (cat (exp (gen) y) x))
  (precedes ((0 0) (2 0)) ((2 1) (0 1)) ((2 1) (3 0)) ((3 1) (1 0)))
  (non-orig (privk a) (privk b))
  (uniq-gen y x)
  (absent (y x))
  (operation nonce-test (added-listener (cat (exp (gen) y) x))
    (exp (gen) (mul y x)) (1 0))
  (strand-map 0 1 2)
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x)))))
      (send
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul y x)))))
    ((recv (exp (gen) (mul y x))) (send (exp (gen) (mul y x))))
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x))))))
    ((recv (cat (exp (gen) y) x)) (send (cat (exp (gen) y) x))))
  (label 12)
  (parent 11)
  (unrealized (3 0))
  (dead)
  (comment "empty cohort"))

(defskeleton station-to-station
  (vars (a b name) (y x rndx))
  (defstrand init 3 (a a) (b b) (x x) (eta y))
  (deflistener (exp (gen) (mul y x)))
  (defstrand resp 2 (b b) (y y) (chi x))
  (deflistener (cat (exp (gen) x) y))
  (precedes ((0 0) (2 0)) ((2 1) (0 1)) ((2 1) (3 0)) ((3 1) (1 0)))
  (non-orig (privk a) (privk b))
  (uniq-gen y x)
  (absent (y x))
  (operation nonce-test (added-listener (cat (exp (gen) x) y))
    (exp (gen) (mul y x)) (1 0))
  (strand-map 0 1 2)
  (traces
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x)))))
      (send
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul y x)))))
    ((recv (exp (gen) (mul y x))) (send (exp (gen) (mul y x))))
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x))))))
    ((recv (cat (exp (gen) x) y)) (send (cat (exp (gen) x) y))))
  (label 13)
  (parent 11)
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
        (enc (enc (exp (gen) eta) (exp (gen) x) (privk a))
          (exp (gen) (mul x eta)))) (send (privk a)))
    (uniq-gen x))
  (defrole resp
    (vars (y rndx) (chi expt) (a b name))
    (trace (recv (exp (gen) chi))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) chi) (privk b))
            (exp (gen) (mul y chi)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) chi) (privk a))
          (exp (gen) (mul y chi)))) (send (privk b)))
    (uniq-gen y)
    (absent (y chi)))
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
  (absent (y chi))
  (traces
    ((recv (exp (gen) chi))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) chi) (privk b))
            (exp (gen) (mul y chi)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) chi) (privk a))
          (exp (gen) (mul y chi)))))
    ((recv (exp (gen) (mul y chi))) (send (exp (gen) (mul y chi)))))
  (label 14)
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
  (absent (y chi))
  (traces
    ((recv (exp (gen) chi))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) chi) (privk b))
            (exp (gen) (mul y chi)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) chi) (privk a))
          (exp (gen) (mul y chi)))))
    ((recv (exp (gen) (mul y chi))) (send (exp (gen) (mul y chi)))))
  (label 15)
  (parent 14)
  (unrealized (0 2))
  (origs)
  (ugens (y (0 1)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-to-station
  (vars (a b b-0 name) (y x rndx))
  (defstrand resp 3 (a a) (b b) (y y) (chi x))
  (deflistener (exp (gen) (mul y x)))
  (defstrand init 3 (a a) (b b-0) (x x) (eta y))
  (precedes ((0 1) (1 0)) ((0 1) (2 1)) ((2 0) (0 0)) ((2 2) (0 2)))
  (non-orig (privk a) (privk b))
  (uniq-gen y x)
  (absent (y x))
  (operation encryption-test (added-strand init 3)
    (enc (exp (gen) y) (exp (gen) x) (privk a)) (0 2))
  (strand-map 0 1)
  (traces
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul y x)))))
    ((recv (exp (gen) (mul y x))) (send (exp (gen) (mul y x))))
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b-0))
            (exp (gen) (mul y x)))))
      (send
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul y x))))))
  (label 16)
  (parent 15)
  (unrealized (1 0) (2 1))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-to-station
  (vars (b name) (y rndx) (chi expt))
  (defstrand resp 3 (a b) (b b) (y y) (chi chi))
  (deflistener (exp (gen) (mul y chi)))
  (precedes ((0 1) (1 0)))
  (non-orig (privk b))
  (uniq-gen y)
  (absent (y chi))
  (operation encryption-test (displaced 2 0 resp 2)
    (enc (exp (gen) y) (exp (gen) chi) (privk a)) (0 2))
  (strand-map 0 1)
  (traces
    ((recv (exp (gen) chi))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) chi) (privk b))
            (exp (gen) (mul y chi)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) chi) (privk b))
          (exp (gen) (mul y chi)))))
    ((recv (exp (gen) (mul y chi))) (send (exp (gen) (mul y chi)))))
  (label 17)
  (parent 15)
  (realized)
  (shape)
  (maps ((0 1) ((a b) (b b) (y y) (chi chi))))
  (origs)
  (ugens (y (0 1))))

(defskeleton station-to-station
  (vars (a b name) (y x rndx))
  (defstrand resp 3 (a a) (b b) (y y) (chi x))
  (deflistener (exp (gen) (mul y x)))
  (defstrand init 3 (a a) (b b) (x x) (eta y))
  (precedes ((0 1) (1 0)) ((0 1) (2 1)) ((2 0) (0 0)) ((2 2) (0 2)))
  (non-orig (privk a) (privk b))
  (uniq-gen y x)
  (absent (y x))
  (operation encryption-test (displaced 3 0 resp 2)
    (enc (enc (exp (gen) y) (exp (gen) x) (privk b-0))
      (exp (gen) (mul y x))) (2 1))
  (strand-map 0 1 2)
  (traces
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul y x)))))
    ((recv (exp (gen) (mul y x))) (send (exp (gen) (mul y x))))
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x)))))
      (send
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul y x))))))
  (label 18)
  (parent 16)
  (unrealized (1 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-to-station
  (vars (a b b-0 name) (y x rndx))
  (defstrand resp 3 (a a) (b b) (y y) (chi x))
  (deflistener (exp (gen) (mul y x)))
  (defstrand init 3 (a a) (b b-0) (x x) (eta y))
  (deflistener (exp (gen) (mul y x)))
  (precedes ((0 1) (1 0)) ((0 1) (3 0)) ((2 0) (0 0)) ((2 2) (0 2))
    ((3 1) (2 1)))
  (non-orig (privk a) (privk b))
  (uniq-gen y x)
  (absent (y x))
  (operation encryption-test (added-listener (exp (gen) (mul y x)))
    (enc (enc (exp (gen) y) (exp (gen) x) (privk b-0))
      (exp (gen) (mul y x))) (2 1))
  (strand-map 0 1 2)
  (traces
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul y x)))))
    ((recv (exp (gen) (mul y x))) (send (exp (gen) (mul y x))))
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b-0))
            (exp (gen) (mul y x)))))
      (send
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul y x)))))
    ((recv (exp (gen) (mul y x))) (send (exp (gen) (mul y x)))))
  (label 19)
  (parent 16)
  (unrealized (1 0) (3 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-to-station
  (vars (a b name) (y x rndx))
  (defstrand resp 3 (a a) (b b) (y y) (chi x))
  (deflistener (exp (gen) (mul y x)))
  (defstrand init 3 (a a) (b b) (x x) (eta y))
  (deflistener (cat (exp (gen) y) x))
  (precedes ((0 1) (2 1)) ((0 1) (3 0)) ((2 0) (0 0)) ((2 2) (0 2))
    ((3 1) (1 0)))
  (non-orig (privk a) (privk b))
  (uniq-gen y x)
  (absent (y x))
  (operation nonce-test (added-listener (cat (exp (gen) y) x))
    (exp (gen) (mul y x)) (1 0))
  (strand-map 0 1 2)
  (traces
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul y x)))))
    ((recv (exp (gen) (mul y x))) (send (exp (gen) (mul y x))))
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x)))))
      (send
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul y x)))))
    ((recv (cat (exp (gen) y) x)) (send (cat (exp (gen) y) x))))
  (label 20)
  (parent 18)
  (unrealized (3 0))
  (dead)
  (comment "empty cohort"))

(defskeleton station-to-station
  (vars (a b name) (y x rndx))
  (defstrand resp 3 (a a) (b b) (y y) (chi x))
  (deflistener (exp (gen) (mul y x)))
  (defstrand init 3 (a a) (b b) (x x) (eta y))
  (deflistener (cat (exp (gen) x) y))
  (precedes ((0 1) (2 1)) ((0 1) (3 0)) ((2 0) (0 0)) ((2 2) (0 2))
    ((3 1) (1 0)))
  (non-orig (privk a) (privk b))
  (uniq-gen y x)
  (absent (y x))
  (operation nonce-test (added-listener (cat (exp (gen) x) y))
    (exp (gen) (mul y x)) (1 0))
  (strand-map 0 1 2)
  (traces
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul y x)))))
    ((recv (exp (gen) (mul y x))) (send (exp (gen) (mul y x))))
    ((send (exp (gen) x))
      (recv
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x)))))
      (send
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul y x)))))
    ((recv (cat (exp (gen) x) y)) (send (cat (exp (gen) x) y))))
  (label 21)
  (parent 18)
  (unrealized (3 0))
  (dead)
  (comment "empty cohort"))

(defskeleton station-to-station
  (vars (a b b-0 name) (y x rndx))
  (defstrand resp 3 (a a) (b b) (y y) (chi x))
  (deflistener (exp (gen) (mul y x)))
  (defstrand init 3 (a a) (b b-0) (x x) (eta y))
  (deflistener (exp (gen) (mul y x)))
  (deflistener (cat (exp (gen) y) x))
  (precedes ((0 1) (1 0)) ((0 1) (4 0)) ((2 0) (0 0)) ((2 2) (0 2))
    ((3 1) (2 1)) ((4 1) (3 0)))
  (non-orig (privk a) (privk b))
  (uniq-gen y x)
  (absent (y x))
  (operation nonce-test (added-listener (cat (exp (gen) y) x))
    (exp (gen) (mul y x)) (3 0))
  (strand-map 0 1 2 3)
  (traces
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul y x)))))
    ((recv (exp (gen) (mul y x))) (send (exp (gen) (mul y x))))
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
  (label 22)
  (parent 19)
  (unrealized (1 0) (4 0))
  (dead)
  (comment "empty cohort"))

(defskeleton station-to-station
  (vars (a b b-0 name) (y x rndx))
  (defstrand resp 3 (a a) (b b) (y y) (chi x))
  (deflistener (exp (gen) (mul y x)))
  (defstrand init 3 (a a) (b b-0) (x x) (eta y))
  (deflistener (exp (gen) (mul y x)))
  (deflistener (cat (exp (gen) x) y))
  (precedes ((0 1) (1 0)) ((0 1) (4 0)) ((2 0) (0 0)) ((2 2) (0 2))
    ((3 1) (2 1)) ((4 1) (3 0)))
  (non-orig (privk a) (privk b))
  (uniq-gen y x)
  (absent (y x))
  (operation nonce-test (added-listener (cat (exp (gen) x) y))
    (exp (gen) (mul y x)) (3 0))
  (strand-map 0 1 2 3)
  (traces
    ((recv (exp (gen) x))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
            (exp (gen) (mul y x)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) x) (privk a))
          (exp (gen) (mul y x)))))
    ((recv (exp (gen) (mul y x))) (send (exp (gen) (mul y x))))
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
  (label 23)
  (parent 19)
  (unrealized (1 0) (4 0))
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
        (enc (enc (exp (gen) eta) (exp (gen) x) (privk a))
          (exp (gen) (mul x eta)))) (send (privk a)))
    (uniq-gen x))
  (defrole resp
    (vars (y rndx) (chi expt) (a b name))
    (trace (recv (exp (gen) chi))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) chi) (privk b))
            (exp (gen) (mul y chi)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) chi) (privk a))
          (exp (gen) (mul y chi)))) (send (privk b)))
    (uniq-gen y)
    (absent (y chi)))
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
  (absent (y x))
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
  (label 24)
  (unrealized (1 2))
  (origs ((privk b) (1 3)) ((privk a) (0 3)))
  (ugens (y (1 1)) (x (0 0)))
  (comment "3 in cohort - 3 not yet seen"))

(defskeleton station-to-station
  (vars (a b name) (y x rndx))
  (defstrand init 4 (a a) (b b) (x x) (eta y))
  (defstrand resp 4 (a a) (b b) (y y) (chi x))
  (precedes ((0 0) (1 0)) ((0 2) (1 2)) ((1 1) (0 1)))
  (uniq-orig (privk a) (privk b))
  (uniq-gen y x)
  (absent (y x))
  (operation encryption-test (displaced 2 0 init 3)
    (enc (enc (exp (gen) y) (exp (gen) x) (privk a-0))
      (exp (gen) (mul y x))) (1 2))
  (strand-map 0 1)
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
  (label 25)
  (parent 24)
  (realized)
  (shape)
  (maps ((0 1) ((a a) (b b) (x x) (y y) (a-0 a))))
  (origs ((privk b) (1 3)) ((privk a) (0 3)))
  (ugens (x (0 0)) (y (1 1))))

(defskeleton station-to-station
  (vars (a b name) (y x rndx))
  (defstrand init 4 (a a) (b b) (x x) (eta y))
  (defstrand resp 4 (a b) (b b) (y y) (chi x))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (uniq-orig (privk a) (privk b))
  (uniq-gen y x)
  (absent (y x))
  (operation encryption-test (displaced 2 1 resp 2)
    (enc (enc (exp (gen) y) (exp (gen) x) (privk a-0))
      (exp (gen) (mul y x))) (1 2))
  (strand-map 0 1)
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
        (enc (enc (exp (gen) y) (exp (gen) x) (privk b))
          (exp (gen) (mul y x)))) (send (privk b))))
  (label 26)
  (parent 24)
  (realized)
  (shape)
  (maps ((0 1) ((a a) (b b) (x x) (y y) (a-0 b))))
  (origs ((privk b) (1 3)) ((privk a) (0 3)))
  (ugens (y (1 1)) (x (0 0))))

(defskeleton station-to-station
  (vars (a b a-0 name) (x y rndx))
  (defstrand init 4 (a a) (b b) (x x) (eta y))
  (defstrand resp 4 (a a-0) (b b) (y y) (chi x))
  (deflistener (exp (gen) (mul x y)))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)) ((1 1) (2 0)) ((2 1) (1 2)))
  (uniq-orig (privk a) (privk b))
  (uniq-gen x y)
  (absent (y x))
  (operation encryption-test (added-listener (exp (gen) (mul x y)))
    (enc (enc (exp (gen) y) (exp (gen) x) (privk a-0))
      (exp (gen) (mul x y))) (1 2))
  (strand-map 0 1)
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
  (label 27)
  (parent 24)
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
  (absent (y x))
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
  (label 28)
  (parent 27)
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
  (absent (y x))
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
  (label 29)
  (parent 27)
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
        (enc (enc (exp (gen) eta) (exp (gen) x) (privk a))
          (exp (gen) (mul x eta)))) (send (privk a)))
    (uniq-gen x))
  (defrole resp
    (vars (y rndx) (chi expt) (a b name))
    (trace (recv (exp (gen) chi))
      (send
        (cat (exp (gen) y)
          (enc (enc (exp (gen) y) (exp (gen) chi) (privk b))
            (exp (gen) (mul y chi)))))
      (recv
        (enc (enc (exp (gen) y) (exp (gen) chi) (privk a))
          (exp (gen) (mul y chi)))) (send (privk b)))
    (uniq-gen y)
    (absent (y chi)))
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
  (absent (y x))
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
  (label 30)
  (unrealized (1 2) (2 0))
  (preskeleton)
  (origs ((privk b) (1 3)) ((privk a) (0 3)))
  (ugens (y (1 1)) (x (0 0)))
  (comment "Not a skeleton"))

(defskeleton station-to-station
  (vars (a b a-0 name) (x y rndx))
  (defstrand init 4 (a a) (b b) (x x) (eta y))
  (defstrand resp 4 (a a-0) (b b) (y y) (chi x))
  (deflistener (exp (gen) (mul x y)))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)) ((1 1) (2 0)))
  (uniq-orig (privk a) (privk b))
  (uniq-gen x y)
  (absent (y x))
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
  (label 31)
  (parent 30)
  (unrealized (1 2) (2 0))
  (origs ((privk b) (1 3)) ((privk a) (0 3)))
  (ugens (y (1 1)) (x (0 0)))
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
  (absent (y x))
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
  (label 32)
  (parent 31)
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
  (absent (y x))
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
  (label 33)
  (parent 31)
  (unrealized (1 2) (3 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")
