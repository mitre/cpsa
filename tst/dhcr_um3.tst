(herald "DHCR: unified model (UM) three-part" (bound 20) (limit 8000)
  (algebra diffie-hellman))

(comment "CPSA 4.4.2")
(comment "All input read from tst/dhcr_um3.scm")
(comment "Step count limited to 8000")
(comment "Strand count bounded at 20")

(defprotocol dhcr-um3 diffie-hellman
  (defrole init
    (vars (ltxa ltxb x rndx) (y expt) (a b name) (na nb data))
    (trace (recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul x y)))))) (send nb))
    (uniq-orig na)
    (uniq-gen x)
    (absent (x ltxa) (x ltxb))
    (fn-of ("principal-of" (ltxa a) (ltxb b))
      ("ltx-of" (a ltxa) (b ltxb)))
    (neq ((exp (gen) y) (gen))))
  (defrole resp
    (vars (ltxa ltxb y rndx) (x expt) (a b name) (na nb data))
    (trace (recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul y x)))))) (recv nb))
    (uniq-orig nb)
    (uniq-gen y)
    (absent (y ltxa) (y ltxb) (y x))
    (fn-of ("principal-of" (ltxa a) (ltxb b))
      ("ltx-of" (a ltxa) (b ltxb)))
    (neq ((exp (gen) x) (gen))))
  (defrole ltx-gen
    (vars (self name) (l rndx))
    (trace (send (cat self (exp (gen) l))) (recv "end-of-protocol")
      (send l))
    (uniq-gen l)
    (fn-of ("principal-of" (l self)) ("ltx-of" (self l))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self self-0 name) (ltxa ltxb x rndx) (y expt))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (x x) (y y))
  (defstrand ltx-gen 1 (self self) (l ltxa))
  (defstrand ltx-gen 1 (self self-0) (l ltxb))
  (non-orig ltxa ltxb)
  (uniq-orig na)
  (uniq-gen ltxa ltxb x)
  (absent (x ltxa) (x ltxb))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul x y)))))) (send nb))
    ((send (cat self (exp (gen) ltxa))))
    ((send (cat self-0 (exp (gen) ltxb)))))
  (label 0)
  (unrealized (0 0) (0 2))
  (preskeleton)
  (origs (na (0 1)))
  (ugens (ltxb (2 0)) (ltxa (1 0)) (x (0 1)))
  (comment "Not a skeleton"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self self-0 name) (ltxa ltxb x rndx) (y expt))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (x x) (y y))
  (defstrand ltx-gen 1 (self self) (l ltxa))
  (defstrand ltx-gen 1 (self self-0) (l ltxb))
  (precedes ((1 0) (0 0)) ((2 0) (0 0)))
  (non-orig ltxa ltxb)
  (uniq-orig na)
  (uniq-gen ltxa ltxb x)
  (absent (x ltxa) (x ltxb))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul x y)))))) (send nb))
    ((send (cat self (exp (gen) ltxa))))
    ((send (cat self-0 (exp (gen) ltxb)))))
  (label 1)
  (parent 0)
  (unrealized (0 2))
  (origs (na (0 1)))
  (ugens (ltxb (2 0)) (ltxa (1 0)) (x (0 1)))
  (comment "3 in cohort - 3 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (x rndx) (y expt) (ltxb rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb) (ltxb ltxb)
    (x x) (y y))
  (defstrand ltx-gen 1 (self self) (l ltxb))
  (precedes ((1 0) (0 0)))
  (non-orig ltxb)
  (uniq-orig na)
  (uniq-gen x ltxb)
  (absent (x ltxb))
  (operation collapsed 2 1)
  (traces
    ((recv (cat (exp (gen) ltxb) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul x y)))))) (send nb))
    ((send (cat self (exp (gen) ltxb)))))
  (label 2)
  (parent 1)
  (unrealized (0 2))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self self-0 name) (y x ltxa ltxb rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (x x) (y y))
  (defstrand ltx-gen 1 (self self) (l ltxa))
  (defstrand ltx-gen 1 (self self-0) (l ltxb))
  (defstrand resp 3 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (y y) (x x))
  (precedes ((0 1) (3 1)) ((1 0) (0 0)) ((1 0) (3 0)) ((2 0) (0 0))
    ((2 0) (3 0)) ((3 2) (0 2)))
  (non-orig ltxa ltxb)
  (uniq-orig na nb)
  (uniq-gen y x ltxa ltxb)
  (absent (y x) (y ltxa) (y ltxb) (x ltxa) (x ltxb))
  (operation encryption-test (added-strand resp 3)
    (enc na nb a b
      (hash (exp (gen) (mul y ltxa)) (exp (gen) (mul x ltxb))
        (exp (gen) (mul y x)))) (0 2))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxa)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x)))))) (send nb))
    ((send (cat self (exp (gen) ltxa))))
    ((send (cat self-0 (exp (gen) ltxb))))
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxa)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x))))))))
  (label 3)
  (parent 1)
  (realized)
  (shape)
  (maps
    ((0 1 2)
      ((ltxa ltxa) (ltxb ltxb) (a a) (b b) (x x) (y y) (na na) (nb nb)
        (self self) (self-0 self-0))))
  (origs (nb (3 2)) (na (0 1)))
  (ugens (y (3 2)) (ltxb (2 0)) (ltxa (1 0)) (x (0 1))))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self self-0 name) (y x ltxb ltxb-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb-0)
    (ltxb ltxb) (x x) (y (mul y ltxb (rec ltxb-0))))
  (defstrand ltx-gen 1 (self self) (l ltxb-0))
  (defstrand ltx-gen 1 (self self-0) (l ltxb))
  (defstrand resp 3 (na na) (nb nb) (a a) (b b) (ltxa ltxb)
    (ltxb ltxb-0) (y y) (x (mul x ltxb (rec ltxb-0))))
  (precedes ((0 1) (3 1)) ((1 0) (0 0)) ((1 0) (3 0)) ((2 0) (0 0))
    ((2 0) (3 0)) ((3 2) (0 2)))
  (non-orig ltxb ltxb-0)
  (uniq-orig na nb)
  (uniq-gen y x ltxb ltxb-0)
  (absent (y (mul x ltxb (rec ltxb-0))) (y ltxb) (y ltxb-0) (x ltxb)
    (x ltxb-0))
  (operation encryption-test (added-strand resp 3)
    (enc na nb a b
      (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
        (exp (gen) (mul y x ltxb (rec ltxb-0))))) (0 2))
  (traces
    ((recv (cat (exp (gen) ltxb-0) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul y ltxb (rec ltxb-0)))
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x ltxb (rec ltxb-0))))))) (send nb))
    ((send (cat self (exp (gen) ltxb-0))))
    ((send (cat self-0 (exp (gen) ltxb))))
    ((recv (cat (exp (gen) ltxb) (exp (gen) ltxb-0)))
      (recv (cat na a b (exp (gen) (mul x ltxb (rec ltxb-0)))))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x ltxb (rec ltxb-0)))))))))
  (label 4)
  (parent 1)
  (unrealized (0 2) (3 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self self-0 name) (ltxa ltxb x rndx) (y expt))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (x x) (y y))
  (defstrand ltx-gen 1 (self self) (l ltxa))
  (defstrand ltx-gen 1 (self self-0) (l ltxb))
  (deflistener
    (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul x y))))
  (precedes ((0 1) (3 0)) ((1 0) (0 0)) ((2 0) (0 0)) ((3 1) (0 2)))
  (non-orig ltxa ltxb)
  (uniq-orig na)
  (uniq-gen ltxa ltxb x)
  (absent (x ltxa) (x ltxb))
  (operation encryption-test
    (added-listener
      (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
        (exp (gen) (mul x y))))
    (enc na nb a b
      (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
        (exp (gen) (mul x y)))) (0 2))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul x y)))))) (send nb))
    ((send (cat self (exp (gen) ltxa))))
    ((send (cat self-0 (exp (gen) ltxb))))
    ((recv
       (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
          (exp (gen) (mul x y))))))
  (label 5)
  (parent 1)
  (unrealized (3 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (y x ltxb rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb) (ltxb ltxb)
    (x x) (y y))
  (defstrand ltx-gen 1 (self self) (l ltxb))
  (defstrand resp 3 (na na) (nb nb) (a a) (b b) (ltxa ltxb) (ltxb ltxb)
    (y y) (x x))
  (precedes ((0 1) (2 1)) ((1 0) (0 0)) ((1 0) (2 0)) ((2 2) (0 2)))
  (non-orig ltxb)
  (uniq-orig na nb)
  (uniq-gen y x ltxb)
  (absent (y x) (y ltxb) (x ltxb))
  (operation encryption-test (added-strand resp 3)
    (enc na nb a b
      (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
        (exp (gen) (mul y x)))) (0 2))
  (traces
    ((recv (cat (exp (gen) ltxb) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x)))))) (send nb))
    ((send (cat self (exp (gen) ltxb))))
    ((recv (cat (exp (gen) ltxb) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x))))))))
  (label 6)
  (parent 2)
  (realized)
  (shape)
  (maps
    ((0 1 1)
      ((ltxa ltxb) (ltxb ltxb) (a a) (b b) (x x) (y y) (na na) (nb nb)
        (self self) (self-0 self))))
  (origs (nb (2 2)) (na (0 1)))
  (ugens (y (2 2)) (ltxb (1 0)) (x (0 1))))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (x rndx) (y expt) (ltxb rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb) (ltxb ltxb)
    (x x) (y y))
  (defstrand ltx-gen 1 (self self) (l ltxb))
  (deflistener
    (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
      (exp (gen) (mul x y))))
  (precedes ((0 1) (2 0)) ((1 0) (0 0)) ((2 1) (0 2)))
  (non-orig ltxb)
  (uniq-orig na)
  (uniq-gen x ltxb)
  (absent (x ltxb))
  (operation encryption-test
    (added-listener
      (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
        (exp (gen) (mul x y))))
    (enc na nb a b
      (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
        (exp (gen) (mul x y)))) (0 2))
  (traces
    ((recv (cat (exp (gen) ltxb) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul x y)))))) (send nb))
    ((send (cat self (exp (gen) ltxb))))
    ((recv
       (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
          (exp (gen) (mul x y))))))
  (label 7)
  (parent 2)
  (unrealized (2 0))
  (origs (na (0 1)))
  (ugens (ltxb (1 0)) (x (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self self-0 name) (y x ltxb ltxb-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb-0)
    (ltxb ltxb) (x x) (y (mul y ltxb (rec ltxb-0))))
  (defstrand ltx-gen 1 (self self) (l ltxb-0))
  (defstrand ltx-gen 1 (self self-0) (l ltxb))
  (defstrand resp 3 (na na) (nb nb) (a a) (b b) (ltxa ltxb)
    (ltxb ltxb-0) (y y) (x (mul x ltxb (rec ltxb-0))))
  (deflistener (cat (exp (gen) (mul ltxb (rec ltxb-0))) x))
  (precedes ((0 1) (4 0)) ((1 0) (0 0)) ((1 0) (3 0)) ((2 0) (0 0))
    ((2 0) (3 0)) ((3 2) (0 2)) ((4 1) (3 1)))
  (non-orig ltxb ltxb-0)
  (uniq-orig na nb)
  (uniq-gen y x ltxb ltxb-0)
  (absent (y (mul x ltxb (rec ltxb-0))) (y ltxb) (y ltxb-0) (x ltxb)
    (x ltxb-0))
  (operation nonce-test
    (added-listener (cat (exp (gen) (mul ltxb (rec ltxb-0))) x))
    (exp (gen) (mul x ltxb (rec ltxb-0))) (3 1))
  (traces
    ((recv (cat (exp (gen) ltxb-0) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul y ltxb (rec ltxb-0)))
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x ltxb (rec ltxb-0))))))) (send nb))
    ((send (cat self (exp (gen) ltxb-0))))
    ((send (cat self-0 (exp (gen) ltxb))))
    ((recv (cat (exp (gen) ltxb) (exp (gen) ltxb-0)))
      (recv (cat na a b (exp (gen) (mul x ltxb (rec ltxb-0)))))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x ltxb (rec ltxb-0))))))))
    ((recv (cat (exp (gen) (mul ltxb (rec ltxb-0))) x))
      (send (cat (exp (gen) (mul ltxb (rec ltxb-0))) x))))
  (label 8)
  (parent 4)
  (unrealized (0 2) (4 0))
  (dead)
  (comment "empty cohort"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self self-0 name) (ltxa ltxb x rndx) (y expt))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (x x) (y y))
  (defstrand ltx-gen 1 (self self) (l ltxa))
  (defstrand ltx-gen 1 (self self-0) (l ltxb))
  (deflistener
    (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul x y))))
  (deflistener
    (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul x y))))
  (precedes ((0 1) (4 0)) ((1 0) (0 0)) ((2 0) (0 0)) ((3 1) (0 2))
    ((4 1) (3 0)))
  (non-orig ltxa ltxb)
  (uniq-orig na)
  (uniq-gen ltxa ltxb x)
  (absent (x ltxa) (x ltxb))
  (operation encryption-test
    (added-listener
      (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
        (exp (gen) (mul x y))))
    (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul x y))) (3 0))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul x y)))))) (send nb))
    ((send (cat self (exp (gen) ltxa))))
    ((send (cat self-0 (exp (gen) ltxb))))
    ((recv
       (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
          (exp (gen) (mul x y)))))
    ((recv
       (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
         (exp (gen) (mul x y))))
      (send
        (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
          (exp (gen) (mul x y))))))
  (label 9)
  (parent 5)
  (unrealized (4 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (x rndx) (y expt) (ltxb rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb) (ltxb ltxb)
    (x x) (y y))
  (defstrand ltx-gen 1 (self self) (l ltxb))
  (deflistener
    (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
      (exp (gen) (mul x y))))
  (deflistener
    (cat (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
      (exp (gen) (mul x y))))
  (precedes ((0 1) (3 0)) ((1 0) (0 0)) ((2 1) (0 2)) ((3 1) (2 0)))
  (non-orig ltxb)
  (uniq-orig na)
  (uniq-gen x ltxb)
  (absent (x ltxb))
  (operation encryption-test
    (added-listener
      (cat (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
        (exp (gen) (mul x y))))
    (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
      (exp (gen) (mul x y))) (2 0))
  (traces
    ((recv (cat (exp (gen) ltxb) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul x y)))))) (send nb))
    ((send (cat self (exp (gen) ltxb))))
    ((recv
       (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
          (exp (gen) (mul x y)))))
    ((recv
       (cat (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
         (exp (gen) (mul x y))))
      (send
        (cat (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
          (exp (gen) (mul x y))))))
  (label 10)
  (parent 7)
  (unrealized (3 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self self-0 name) (ltxa ltxb x rndx) (y expt))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (x x) (y y))
  (defstrand ltx-gen 1 (self self) (l ltxa))
  (defstrand ltx-gen 1 (self self-0) (l ltxb))
  (deflistener
    (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul x y))))
  (deflistener
    (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul x y))))
  (deflistener (cat (exp (gen) ltxb) x))
  (precedes ((0 1) (5 0)) ((1 0) (0 0)) ((2 0) (0 0)) ((3 1) (0 2))
    ((4 1) (3 0)) ((5 1) (4 0)))
  (non-orig ltxa ltxb)
  (uniq-orig na)
  (uniq-gen ltxa ltxb x)
  (absent (x ltxa) (x ltxb))
  (operation nonce-test (added-listener (cat (exp (gen) ltxb) x))
    (exp (gen) (mul ltxb x)) (4 0))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul x y)))))) (send nb))
    ((send (cat self (exp (gen) ltxa))))
    ((send (cat self-0 (exp (gen) ltxb))))
    ((recv
       (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
          (exp (gen) (mul x y)))))
    ((recv
       (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
         (exp (gen) (mul x y))))
      (send
        (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
          (exp (gen) (mul x y)))))
    ((recv (cat (exp (gen) ltxb) x)) (send (cat (exp (gen) ltxb) x))))
  (label 11)
  (parent 9)
  (unrealized (5 0))
  (dead)
  (comment "empty cohort"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (x rndx) (y expt) (ltxb rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb) (ltxb ltxb)
    (x x) (y y))
  (defstrand ltx-gen 1 (self self) (l ltxb))
  (deflistener
    (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
      (exp (gen) (mul x y))))
  (deflistener
    (cat (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
      (exp (gen) (mul x y))))
  (deflistener (cat (exp (gen) ltxb) x))
  (precedes ((0 1) (4 0)) ((1 0) (0 0)) ((2 1) (0 2)) ((3 1) (2 0))
    ((4 1) (3 0)))
  (non-orig ltxb)
  (uniq-orig na)
  (uniq-gen x ltxb)
  (absent (x ltxb))
  (operation nonce-test (added-listener (cat (exp (gen) ltxb) x))
    (exp (gen) (mul x ltxb)) (3 0))
  (traces
    ((recv (cat (exp (gen) ltxb) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul x y)))))) (send nb))
    ((send (cat self (exp (gen) ltxb))))
    ((recv
       (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
          (exp (gen) (mul x y)))))
    ((recv
       (cat (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
         (exp (gen) (mul x y))))
      (send
        (cat (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
          (exp (gen) (mul x y)))))
    ((recv (cat (exp (gen) ltxb) x)) (send (cat (exp (gen) ltxb) x))))
  (label 12)
  (parent 10)
  (unrealized (4 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol dhcr-um3 diffie-hellman
  (defrole init
    (vars (ltxa ltxb x rndx) (y expt) (a b name) (na nb data))
    (trace (recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul x y)))))) (send nb))
    (uniq-orig na)
    (uniq-gen x)
    (absent (x ltxa) (x ltxb))
    (fn-of ("principal-of" (ltxa a) (ltxb b))
      ("ltx-of" (a ltxa) (b ltxb)))
    (neq ((exp (gen) y) (gen))))
  (defrole resp
    (vars (ltxa ltxb y rndx) (x expt) (a b name) (na nb data))
    (trace (recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul y x)))))) (recv nb))
    (uniq-orig nb)
    (uniq-gen y)
    (absent (y ltxa) (y ltxb) (y x))
    (fn-of ("principal-of" (ltxa a) (ltxb b))
      ("ltx-of" (a ltxa) (b ltxb)))
    (neq ((exp (gen) x) (gen))))
  (defrole ltx-gen
    (vars (self name) (l rndx))
    (trace (send (cat self (exp (gen) l))) (recv "end-of-protocol")
      (send l))
    (uniq-gen l)
    (fn-of ("principal-of" (l self)) ("ltx-of" (self l))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (ltxa ltxb x rndx) (y expt))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (x x) (y y))
  (defstrand ltx-gen 1 (self self) (l ltxb))
  (non-orig ltxb)
  (uniq-orig na)
  (uniq-gen ltxb x)
  (absent (x ltxa) (x ltxb))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul x y)))))) (send nb))
    ((send (cat self (exp (gen) ltxb)))))
  (label 13)
  (unrealized (0 0) (0 2))
  (preskeleton)
  (origs (na (0 1)))
  (ugens (ltxb (1 0)) (x (0 1)))
  (comment "Not a skeleton"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (ltxa ltxb x rndx) (y expt))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (x x) (y y))
  (defstrand ltx-gen 1 (self self) (l ltxb))
  (precedes ((1 0) (0 0)))
  (non-orig ltxb)
  (uniq-orig na)
  (uniq-gen ltxb x)
  (absent (x ltxa) (x ltxb))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul x y)))))) (send nb))
    ((send (cat self (exp (gen) ltxb)))))
  (label 14)
  (parent 13)
  (unrealized (0 2))
  (origs (na (0 1)))
  (ugens (ltxb (1 0)) (x (0 1)))
  (comment "3 in cohort - 3 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (y x ltxa ltxb rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (x x) (y y))
  (defstrand ltx-gen 1 (self self) (l ltxb))
  (defstrand resp 3 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (y y) (x x))
  (precedes ((0 1) (2 1)) ((1 0) (0 0)) ((1 0) (2 0)) ((2 2) (0 2)))
  (non-orig ltxb)
  (uniq-orig na nb)
  (uniq-gen y x ltxb)
  (absent (y x) (y ltxa) (y ltxb) (x ltxa) (x ltxb))
  (operation encryption-test (added-strand resp 3)
    (enc na nb a b
      (hash (exp (gen) (mul y ltxa)) (exp (gen) (mul x ltxb))
        (exp (gen) (mul y x)))) (0 2))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxa)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x)))))) (send nb))
    ((send (cat self (exp (gen) ltxb))))
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxa)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x))))))))
  (label 15)
  (parent 14)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((ltxa ltxa) (ltxb ltxb) (a a) (b b) (x x) (y y) (na na) (nb nb)
        (self self))))
  (origs (nb (2 2)) (na (0 1)))
  (ugens (y (2 2)) (ltxb (1 0)) (x (0 1))))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (y x ltxb ltxb-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb-0)
    (ltxb ltxb) (x x) (y (mul y ltxb (rec ltxb-0))))
  (defstrand ltx-gen 1 (self self) (l ltxb))
  (defstrand resp 3 (na na) (nb nb) (a a) (b b) (ltxa ltxb)
    (ltxb ltxb-0) (y y) (x (mul x ltxb (rec ltxb-0))))
  (precedes ((0 1) (2 1)) ((1 0) (0 0)) ((1 0) (2 0)) ((2 2) (0 2)))
  (non-orig ltxb)
  (uniq-orig na nb)
  (uniq-gen y x ltxb)
  (absent (y (mul x ltxb (rec ltxb-0))) (y ltxb) (y ltxb-0) (x ltxb)
    (x ltxb-0))
  (operation encryption-test (added-strand resp 3)
    (enc na nb a b
      (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
        (exp (gen) (mul y x ltxb (rec ltxb-0))))) (0 2))
  (traces
    ((recv (cat (exp (gen) ltxb-0) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul y ltxb (rec ltxb-0)))
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x ltxb (rec ltxb-0))))))) (send nb))
    ((send (cat self (exp (gen) ltxb))))
    ((recv (cat (exp (gen) ltxb) (exp (gen) ltxb-0)))
      (recv (cat na a b (exp (gen) (mul x ltxb (rec ltxb-0)))))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x ltxb (rec ltxb-0)))))))))
  (label 16)
  (parent 14)
  (unrealized (0 2) (2 1))
  (comment "3 in cohort - 3 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (ltxa ltxb x rndx) (y expt))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (x x) (y y))
  (defstrand ltx-gen 1 (self self) (l ltxb))
  (deflistener
    (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul x y))))
  (precedes ((0 1) (2 0)) ((1 0) (0 0)) ((2 1) (0 2)))
  (non-orig ltxb)
  (uniq-orig na)
  (uniq-gen ltxb x)
  (absent (x ltxa) (x ltxb))
  (operation encryption-test
    (added-listener
      (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
        (exp (gen) (mul x y))))
    (enc na nb a b
      (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
        (exp (gen) (mul x y)))) (0 2))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul x y)))))) (send nb))
    ((send (cat self (exp (gen) ltxb))))
    ((recv
       (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
          (exp (gen) (mul x y))))))
  (label 17)
  (parent 14)
  (unrealized (2 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (y x ltxb rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb) (ltxb ltxb)
    (x x) (y y))
  (defstrand ltx-gen 1 (self self) (l ltxb))
  (defstrand resp 3 (na na) (nb nb) (a a) (b b) (ltxa ltxb) (ltxb ltxb)
    (y y) (x x))
  (precedes ((0 1) (2 1)) ((1 0) (0 0)) ((1 0) (2 0)) ((2 2) (0 2)))
  (non-orig ltxb)
  (uniq-orig na nb)
  (uniq-gen y x ltxb)
  (absent (y x) (y ltxb) (x ltxb))
  (operation nonce-test (displaced 3 0 init 2) (exp (gen) x) (2 1))
  (traces
    ((recv (cat (exp (gen) ltxb) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x)))))) (send nb))
    ((send (cat self (exp (gen) ltxb))))
    ((recv (cat (exp (gen) ltxb) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x))))))))
  (label 18)
  (parent 16)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((ltxa ltxb) (ltxb ltxb) (a a) (b b) (x x) (y y) (na na) (nb nb)
        (self self))))
  (origs (na (0 1)) (nb (2 2)))
  (ugens (x (0 1)) (y (2 2)) (ltxb (1 0))))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (y x ltxb ltxb-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb-0)
    (ltxb ltxb) (x x) (y (mul y ltxb (rec ltxb-0))))
  (defstrand ltx-gen 1 (self self) (l ltxb))
  (defstrand resp 3 (na na) (nb nb) (a a) (b b) (ltxa ltxb)
    (ltxb ltxb-0) (y y) (x (mul x ltxb (rec ltxb-0))))
  (deflistener (cat (exp (gen) (mul x ltxb)) ltxb-0))
  (precedes ((0 1) (3 0)) ((1 0) (0 0)) ((1 0) (2 0)) ((2 2) (0 2))
    ((3 1) (2 1)))
  (non-orig ltxb)
  (uniq-orig na nb)
  (uniq-gen y x ltxb)
  (absent (y (mul x ltxb (rec ltxb-0))) (y ltxb) (y ltxb-0) (x ltxb)
    (x ltxb-0))
  (operation nonce-test
    (added-listener (cat (exp (gen) (mul x ltxb)) ltxb-0))
    (exp (gen) (mul x ltxb (rec ltxb-0))) (2 1))
  (traces
    ((recv (cat (exp (gen) ltxb-0) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul y ltxb (rec ltxb-0)))
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x ltxb (rec ltxb-0))))))) (send nb))
    ((send (cat self (exp (gen) ltxb))))
    ((recv (cat (exp (gen) ltxb) (exp (gen) ltxb-0)))
      (recv (cat na a b (exp (gen) (mul x ltxb (rec ltxb-0)))))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x ltxb (rec ltxb-0))))))))
    ((recv (cat (exp (gen) (mul x ltxb)) ltxb-0))
      (send (cat (exp (gen) (mul x ltxb)) ltxb-0))))
  (label 19)
  (parent 16)
  (unrealized (0 2) (3 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (y x ltxb ltxb-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb-0)
    (ltxb ltxb) (x x) (y (mul y ltxb (rec ltxb-0))))
  (defstrand ltx-gen 1 (self self) (l ltxb))
  (defstrand resp 3 (na na) (nb nb) (a a) (b b) (ltxa ltxb)
    (ltxb ltxb-0) (y y) (x (mul x ltxb (rec ltxb-0))))
  (deflistener (cat (exp (gen) (mul ltxb (rec ltxb-0))) x))
  (precedes ((0 1) (3 0)) ((1 0) (0 0)) ((1 0) (2 0)) ((2 2) (0 2))
    ((3 1) (2 1)))
  (non-orig ltxb)
  (uniq-orig na nb)
  (uniq-gen y x ltxb)
  (absent (y (mul x ltxb (rec ltxb-0))) (y ltxb) (y ltxb-0) (x ltxb)
    (x ltxb-0))
  (operation nonce-test
    (added-listener (cat (exp (gen) (mul ltxb (rec ltxb-0))) x))
    (exp (gen) (mul x ltxb (rec ltxb-0))) (2 1))
  (traces
    ((recv (cat (exp (gen) ltxb-0) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul y ltxb (rec ltxb-0)))
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x ltxb (rec ltxb-0))))))) (send nb))
    ((send (cat self (exp (gen) ltxb))))
    ((recv (cat (exp (gen) ltxb) (exp (gen) ltxb-0)))
      (recv (cat na a b (exp (gen) (mul x ltxb (rec ltxb-0)))))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x ltxb (rec ltxb-0))))))))
    ((recv (cat (exp (gen) (mul ltxb (rec ltxb-0))) x))
      (send (cat (exp (gen) (mul ltxb (rec ltxb-0))) x))))
  (label 20)
  (parent 16)
  (unrealized (0 2) (3 0))
  (dead)
  (comment "empty cohort"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (ltxa ltxb x rndx) (y expt))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (x x) (y y))
  (defstrand ltx-gen 1 (self self) (l ltxb))
  (deflistener
    (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul x y))))
  (deflistener
    (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul x y))))
  (precedes ((0 1) (3 0)) ((1 0) (0 0)) ((2 1) (0 2)) ((3 1) (2 0)))
  (non-orig ltxb)
  (uniq-orig na)
  (uniq-gen ltxb x)
  (absent (x ltxa) (x ltxb))
  (operation encryption-test
    (added-listener
      (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
        (exp (gen) (mul x y))))
    (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul x y))) (2 0))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul x y)))))) (send nb))
    ((send (cat self (exp (gen) ltxb))))
    ((recv
       (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
          (exp (gen) (mul x y)))))
    ((recv
       (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
         (exp (gen) (mul x y))))
      (send
        (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
          (exp (gen) (mul x y))))))
  (label 21)
  (parent 17)
  (unrealized (3 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (y x ltxb ltxb-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb-0)
    (ltxb ltxb) (x x) (y (mul y ltxb (rec ltxb-0))))
  (defstrand ltx-gen 1 (self self) (l ltxb))
  (defstrand resp 3 (na na) (nb nb) (a a) (b b) (ltxa ltxb)
    (ltxb ltxb-0) (y y) (x (mul x ltxb (rec ltxb-0))))
  (deflistener (cat (exp (gen) (mul x ltxb)) ltxb-0))
  (deflistener (cat (exp (gen) ltxb) x))
  (precedes ((0 1) (4 0)) ((1 0) (0 0)) ((1 0) (2 0)) ((2 2) (0 2))
    ((3 1) (2 1)) ((4 1) (3 0)))
  (non-orig ltxb)
  (uniq-orig na nb)
  (uniq-gen y x ltxb)
  (absent (y (mul x ltxb (rec ltxb-0))) (y ltxb) (y ltxb-0) (x ltxb)
    (x ltxb-0))
  (operation nonce-test (added-listener (cat (exp (gen) ltxb) x))
    (exp (gen) (mul x ltxb)) (3 0))
  (traces
    ((recv (cat (exp (gen) ltxb-0) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul y ltxb (rec ltxb-0)))
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x ltxb (rec ltxb-0))))))) (send nb))
    ((send (cat self (exp (gen) ltxb))))
    ((recv (cat (exp (gen) ltxb) (exp (gen) ltxb-0)))
      (recv (cat na a b (exp (gen) (mul x ltxb (rec ltxb-0)))))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x ltxb (rec ltxb-0))))))))
    ((recv (cat (exp (gen) (mul x ltxb)) ltxb-0))
      (send (cat (exp (gen) (mul x ltxb)) ltxb-0)))
    ((recv (cat (exp (gen) ltxb) x)) (send (cat (exp (gen) ltxb) x))))
  (label 22)
  (parent 19)
  (unrealized (0 2) (4 0))
  (dead)
  (comment "empty cohort"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (ltxa ltxb x rndx) (y expt))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (x x) (y y))
  (defstrand ltx-gen 1 (self self) (l ltxb))
  (deflistener
    (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul x y))))
  (deflistener
    (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul x y))))
  (deflistener (cat (exp (gen) ltxb) x))
  (precedes ((0 1) (4 0)) ((1 0) (0 0)) ((2 1) (0 2)) ((3 1) (2 0))
    ((4 1) (3 0)))
  (non-orig ltxb)
  (uniq-orig na)
  (uniq-gen ltxb x)
  (absent (x ltxa) (x ltxb))
  (operation nonce-test (added-listener (cat (exp (gen) ltxb) x))
    (exp (gen) (mul ltxb x)) (3 0))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul x y)))))) (send nb))
    ((send (cat self (exp (gen) ltxb))))
    ((recv
       (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
          (exp (gen) (mul x y)))))
    ((recv
       (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
         (exp (gen) (mul x y))))
      (send
        (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
          (exp (gen) (mul x y)))))
    ((recv (cat (exp (gen) ltxb) x)) (send (cat (exp (gen) ltxb) x))))
  (label 23)
  (parent 21)
  (unrealized (4 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol dhcr-um3 diffie-hellman
  (defrole init
    (vars (ltxa ltxb x rndx) (y expt) (a b name) (na nb data))
    (trace (recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul x y)))))) (send nb))
    (uniq-orig na)
    (uniq-gen x)
    (absent (x ltxa) (x ltxb))
    (fn-of ("principal-of" (ltxa a) (ltxb b))
      ("ltx-of" (a ltxa) (b ltxb)))
    (neq ((exp (gen) y) (gen))))
  (defrole resp
    (vars (ltxa ltxb y rndx) (x expt) (a b name) (na nb data))
    (trace (recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul y x)))))) (recv nb))
    (uniq-orig nb)
    (uniq-gen y)
    (absent (y ltxa) (y ltxb) (y x))
    (fn-of ("principal-of" (ltxa a) (ltxb b))
      ("ltx-of" (a ltxa) (b ltxb)))
    (neq ((exp (gen) x) (gen))))
  (defrole ltx-gen
    (vars (self name) (l rndx))
    (trace (send (cat self (exp (gen) l))) (recv "end-of-protocol")
      (send l))
    (uniq-gen l)
    (fn-of ("principal-of" (l self)) ("ltx-of" (self l))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (ltxa ltxb x y rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (x x) (y y))
  (defstrand ltx-gen 1 (self self) (l ltxb))
  (deflistener (exp (gen) (mul x y)))
  (non-orig ltxb)
  (uniq-orig na)
  (uniq-gen ltxb x)
  (absent (x ltxa) (x ltxb))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul x y)))))) (send nb))
    ((send (cat self (exp (gen) ltxb))))
    ((recv (exp (gen) (mul x y))) (send (exp (gen) (mul x y)))))
  (label 24)
  (unrealized (0 0) (0 2) (2 0))
  (preskeleton)
  (origs (na (0 1)))
  (ugens (ltxb (1 0)) (x (0 1)))
  (comment "Not a skeleton"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (ltxa ltxb x y rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (x x) (y y))
  (defstrand ltx-gen 1 (self self) (l ltxb))
  (deflistener (exp (gen) (mul x y)))
  (precedes ((0 1) (2 0)) ((1 0) (0 0)))
  (non-orig ltxb)
  (uniq-orig na)
  (uniq-gen ltxb x)
  (absent (x ltxa) (x ltxb))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul x y)))))) (send nb))
    ((send (cat self (exp (gen) ltxb))))
    ((recv (exp (gen) (mul x y))) (send (exp (gen) (mul x y)))))
  (label 25)
  (parent 24)
  (unrealized (0 2))
  (origs (na (0 1)))
  (ugens (ltxb (1 0)) (x (0 1)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (ltxa y x ltxb rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (x x) (y y))
  (defstrand ltx-gen 1 (self self) (l ltxb))
  (deflistener (exp (gen) (mul y x)))
  (defstrand resp 3 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (y y) (x x))
  (precedes ((0 1) (3 1)) ((1 0) (0 0)) ((1 0) (3 0)) ((3 2) (0 2))
    ((3 2) (2 0)))
  (non-orig ltxb)
  (uniq-orig na nb)
  (uniq-gen y x ltxb)
  (absent (y ltxa) (y x) (y ltxb) (x ltxa) (x ltxb))
  (operation encryption-test (added-strand resp 3)
    (enc na nb a b
      (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x ltxb))
        (exp (gen) (mul y x)))) (0 2))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x)))))) (send nb))
    ((send (cat self (exp (gen) ltxb))))
    ((recv (exp (gen) (mul y x))) (send (exp (gen) (mul y x))))
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x))))))))
  (label 26)
  (parent 25)
  (unrealized (2 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (ltxa ltxb x y rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (x x) (y y))
  (defstrand ltx-gen 1 (self self) (l ltxb))
  (deflistener (exp (gen) (mul x y)))
  (deflistener
    (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul x y))))
  (precedes ((0 1) (2 0)) ((0 1) (3 0)) ((1 0) (0 0)) ((3 1) (0 2)))
  (non-orig ltxb)
  (uniq-orig na)
  (uniq-gen ltxb x)
  (absent (x ltxa) (x ltxb))
  (operation encryption-test
    (added-listener
      (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
        (exp (gen) (mul x y))))
    (enc na nb a b
      (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
        (exp (gen) (mul x y)))) (0 2))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul x y)))))) (send nb))
    ((send (cat self (exp (gen) ltxb))))
    ((recv (exp (gen) (mul x y))) (send (exp (gen) (mul x y))))
    ((recv
       (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
          (exp (gen) (mul x y))))))
  (label 27)
  (parent 25)
  (unrealized (3 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (ltxa y x ltxb rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (x x) (y y))
  (defstrand ltx-gen 1 (self self) (l ltxb))
  (deflistener (exp (gen) (mul y x)))
  (defstrand resp 3 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (y y) (x x))
  (deflistener (cat (exp (gen) y) x))
  (precedes ((0 1) (3 1)) ((1 0) (0 0)) ((1 0) (3 0)) ((3 2) (0 2))
    ((3 2) (4 0)) ((4 1) (2 0)))
  (non-orig ltxb)
  (uniq-orig na nb)
  (uniq-gen y x ltxb)
  (absent (y ltxa) (y x) (y ltxb) (x ltxa) (x ltxb))
  (operation nonce-test (added-listener (cat (exp (gen) y) x))
    (exp (gen) (mul y x)) (2 0))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x)))))) (send nb))
    ((send (cat self (exp (gen) ltxb))))
    ((recv (exp (gen) (mul y x))) (send (exp (gen) (mul y x))))
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x)))))))
    ((recv (cat (exp (gen) y) x)) (send (cat (exp (gen) y) x))))
  (label 28)
  (parent 26)
  (unrealized (4 0))
  (dead)
  (comment "empty cohort"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (ltxa y x ltxb rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (x x) (y y))
  (defstrand ltx-gen 1 (self self) (l ltxb))
  (deflistener (exp (gen) (mul y x)))
  (defstrand resp 3 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (y y) (x x))
  (deflistener (cat (exp (gen) x) y))
  (precedes ((0 1) (3 1)) ((1 0) (0 0)) ((1 0) (3 0)) ((3 2) (0 2))
    ((3 2) (4 0)) ((4 1) (2 0)))
  (non-orig ltxb)
  (uniq-orig na nb)
  (uniq-gen y x ltxb)
  (absent (y ltxa) (y x) (y ltxb) (x ltxa) (x ltxb))
  (operation nonce-test (added-listener (cat (exp (gen) x) y))
    (exp (gen) (mul y x)) (2 0))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x)))))) (send nb))
    ((send (cat self (exp (gen) ltxb))))
    ((recv (exp (gen) (mul y x))) (send (exp (gen) (mul y x))))
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x)))))))
    ((recv (cat (exp (gen) x) y)) (send (cat (exp (gen) x) y))))
  (label 29)
  (parent 26)
  (unrealized (4 0))
  (dead)
  (comment "empty cohort"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (ltxa ltxb x y rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (x x) (y y))
  (defstrand ltx-gen 1 (self self) (l ltxb))
  (deflistener (exp (gen) (mul x y)))
  (deflistener
    (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul x y))))
  (deflistener
    (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul x y))))
  (precedes ((0 1) (2 0)) ((0 1) (4 0)) ((1 0) (0 0)) ((3 1) (0 2))
    ((4 1) (3 0)))
  (non-orig ltxb)
  (uniq-orig na)
  (uniq-gen ltxb x)
  (absent (x ltxa) (x ltxb))
  (operation encryption-test
    (added-listener
      (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
        (exp (gen) (mul x y))))
    (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul x y))) (3 0))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul x y)))))) (send nb))
    ((send (cat self (exp (gen) ltxb))))
    ((recv (exp (gen) (mul x y))) (send (exp (gen) (mul x y))))
    ((recv
       (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
          (exp (gen) (mul x y)))))
    ((recv
       (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
         (exp (gen) (mul x y))))
      (send
        (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
          (exp (gen) (mul x y))))))
  (label 30)
  (parent 27)
  (unrealized (4 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (ltxa ltxb x y rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (x x) (y y))
  (defstrand ltx-gen 1 (self self) (l ltxb))
  (deflistener (exp (gen) (mul x y)))
  (deflistener
    (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul x y))))
  (deflistener
    (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul x y))))
  (deflistener (cat (exp (gen) ltxb) x))
  (precedes ((0 1) (2 0)) ((0 1) (5 0)) ((1 0) (0 0)) ((3 1) (0 2))
    ((4 1) (3 0)) ((5 1) (4 0)))
  (non-orig ltxb)
  (uniq-orig na)
  (uniq-gen ltxb x)
  (absent (x ltxa) (x ltxb))
  (operation nonce-test (added-listener (cat (exp (gen) ltxb) x))
    (exp (gen) (mul ltxb x)) (4 0))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul x y)))))) (send nb))
    ((send (cat self (exp (gen) ltxb))))
    ((recv (exp (gen) (mul x y))) (send (exp (gen) (mul x y))))
    ((recv
       (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
          (exp (gen) (mul x y)))))
    ((recv
       (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
         (exp (gen) (mul x y))))
      (send
        (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
          (exp (gen) (mul x y)))))
    ((recv (cat (exp (gen) ltxb) x)) (send (cat (exp (gen) ltxb) x))))
  (label 31)
  (parent 30)
  (unrealized (5 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol dhcr-um3 diffie-hellman
  (defrole init
    (vars (ltxa ltxb x rndx) (y expt) (a b name) (na nb data))
    (trace (recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul x y)))))) (send nb))
    (uniq-orig na)
    (uniq-gen x)
    (absent (x ltxa) (x ltxb))
    (fn-of ("principal-of" (ltxa a) (ltxb b))
      ("ltx-of" (a ltxa) (b ltxb)))
    (neq ((exp (gen) y) (gen))))
  (defrole resp
    (vars (ltxa ltxb y rndx) (x expt) (a b name) (na nb data))
    (trace (recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul y x)))))) (recv nb))
    (uniq-orig nb)
    (uniq-gen y)
    (absent (y ltxa) (y ltxb) (y x))
    (fn-of ("principal-of" (ltxa a) (ltxb b))
      ("ltx-of" (a ltxa) (b ltxb)))
    (neq ((exp (gen) x) (gen))))
  (defrole ltx-gen
    (vars (self name) (l rndx))
    (trace (send (cat self (exp (gen) l))) (recv "end-of-protocol")
      (send l))
    (uniq-gen l)
    (fn-of ("principal-of" (l self)) ("ltx-of" (self l))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self self-0 name) (ltxa ltxb y rndx) (x expt))
  (defstrand resp 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (y y) (x x))
  (defstrand ltx-gen 1 (self self) (l ltxa))
  (defstrand ltx-gen 1 (self self-0) (l ltxb))
  (non-orig ltxa ltxb)
  (uniq-orig nb)
  (uniq-gen ltxa ltxb y)
  (absent (y ltxa) (y ltxb) (y x))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul y x)))))) (recv nb))
    ((send (cat self (exp (gen) ltxa))))
    ((send (cat self-0 (exp (gen) ltxb)))))
  (label 32)
  (unrealized (0 0) (0 3))
  (preskeleton)
  (origs (nb (0 2)))
  (ugens (ltxb (2 0)) (ltxa (1 0)) (y (0 2)))
  (comment "Not a skeleton"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self self-0 name) (ltxa ltxb y rndx) (x expt))
  (defstrand resp 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (y y) (x x))
  (defstrand ltx-gen 1 (self self) (l ltxa))
  (defstrand ltx-gen 1 (self self-0) (l ltxb))
  (precedes ((1 0) (0 0)) ((2 0) (0 0)))
  (non-orig ltxa ltxb)
  (uniq-orig nb)
  (uniq-gen ltxa ltxb y)
  (absent (y ltxa) (y ltxb) (y x))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul y x)))))) (recv nb))
    ((send (cat self (exp (gen) ltxa))))
    ((send (cat self-0 (exp (gen) ltxb)))))
  (label 33)
  (parent 32)
  (unrealized (0 3))
  (origs (nb (0 2)))
  (ugens (ltxb (2 0)) (ltxa (1 0)) (y (0 2)))
  (comment "3 in cohort - 3 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (y rndx) (x expt) (ltxb rndx))
  (defstrand resp 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb) (ltxb ltxb)
    (y y) (x x))
  (defstrand ltx-gen 1 (self self) (l ltxb))
  (precedes ((1 0) (0 0)))
  (non-orig ltxb)
  (uniq-orig nb)
  (uniq-gen y ltxb)
  (absent (y x) (y ltxb))
  (operation collapsed 2 1)
  (traces
    ((recv (cat (exp (gen) ltxb) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x)))))) (recv nb))
    ((send (cat self (exp (gen) ltxb)))))
  (label 34)
  (parent 33)
  (unrealized (0 3))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self self-0 name) (y x ltxa ltxb rndx))
  (defstrand resp 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (y y) (x x))
  (defstrand ltx-gen 1 (self self) (l ltxa))
  (defstrand ltx-gen 1 (self self-0) (l ltxb))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (x x) (y y))
  (precedes ((0 2) (3 2)) ((1 0) (0 0)) ((1 0) (3 0)) ((2 0) (0 0))
    ((2 0) (3 0)) ((3 1) (0 1)) ((3 3) (0 3)))
  (non-orig ltxa ltxb)
  (uniq-orig na nb)
  (uniq-gen y x ltxa ltxb)
  (absent (y x) (y ltxa) (y ltxb) (x ltxa) (x ltxb))
  (operation nonce-test (added-strand init 4) nb (0 3)
    (enc na nb a b
      (hash (exp (gen) (mul y ltxa)) (exp (gen) (mul x ltxb))
        (exp (gen) (mul y x)))))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxa)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x)))))) (recv nb))
    ((send (cat self (exp (gen) ltxa))))
    ((send (cat self-0 (exp (gen) ltxb))))
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxa)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x)))))) (send nb)))
  (label 35)
  (parent 33)
  (realized)
  (shape)
  (maps
    ((0 1 2)
      ((ltxa ltxa) (ltxb ltxb) (a a) (b b) (y y) (x x) (na na) (nb nb)
        (self self) (self-0 self-0))))
  (origs (na (3 1)) (nb (0 2)))
  (ugens (x (3 1)) (ltxb (2 0)) (ltxa (1 0)) (y (0 2))))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self self-0 name) (y x ltxb ltxb-0 rndx))
  (defstrand resp 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb-0)
    (ltxb ltxb) (y y) (x (mul x (rec ltxb) ltxb-0)))
  (defstrand ltx-gen 1 (self self) (l ltxb-0))
  (defstrand ltx-gen 1 (self self-0) (l ltxb))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb)
    (ltxb ltxb-0) (x x) (y (mul y (rec ltxb) ltxb-0)))
  (precedes ((0 2) (3 2)) ((1 0) (0 0)) ((1 0) (3 0)) ((2 0) (0 0))
    ((2 0) (3 0)) ((3 1) (0 1)) ((3 3) (0 3)))
  (non-orig ltxb ltxb-0)
  (uniq-orig na nb)
  (uniq-gen y x ltxb ltxb-0)
  (absent (y (mul x (rec ltxb) ltxb-0)) (y ltxb) (y ltxb-0) (x ltxb)
    (x ltxb-0))
  (operation nonce-test (added-strand init 4) nb (0 3)
    (enc na nb a b
      (hash (exp (gen) (mul y ltxb-0)) (exp (gen) (mul x ltxb-0))
        (exp (gen) (mul y x (rec ltxb) ltxb-0)))))
  (traces
    ((recv (cat (exp (gen) ltxb-0) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) (mul x (rec ltxb) ltxb-0))))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb-0)) (exp (gen) (mul x ltxb-0))
              (exp (gen) (mul y x (rec ltxb) ltxb-0)))))) (recv nb))
    ((send (cat self (exp (gen) ltxb-0))))
    ((send (cat self-0 (exp (gen) ltxb))))
    ((recv (cat (exp (gen) ltxb) (exp (gen) ltxb-0)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul y (rec ltxb) ltxb-0))
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb-0)) (exp (gen) (mul x ltxb-0))
              (exp (gen) (mul y x (rec ltxb) ltxb-0)))))) (send nb)))
  (label 36)
  (parent 33)
  (unrealized (0 1) (3 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self self-0 name) (ltxa ltxb y rndx) (x expt))
  (defstrand resp 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (y y) (x x))
  (defstrand ltx-gen 1 (self self) (l ltxa))
  (defstrand ltx-gen 1 (self self-0) (l ltxb))
  (deflistener
    (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul y x))))
  (precedes ((0 2) (3 0)) ((1 0) (0 0)) ((2 0) (0 0)) ((3 1) (0 3)))
  (non-orig ltxa ltxb)
  (uniq-orig nb)
  (uniq-gen ltxa ltxb y)
  (absent (y ltxa) (y ltxb) (y x))
  (operation nonce-test
    (added-listener
      (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
        (exp (gen) (mul y x)))) nb (0 3)
    (enc na nb a b
      (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
        (exp (gen) (mul y x)))))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul y x)))))) (recv nb))
    ((send (cat self (exp (gen) ltxa))))
    ((send (cat self-0 (exp (gen) ltxb))))
    ((recv
       (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
         (exp (gen) (mul y x))))
      (send
        (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
          (exp (gen) (mul y x))))))
  (label 37)
  (parent 33)
  (unrealized (3 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (y x ltxb rndx))
  (defstrand resp 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb) (ltxb ltxb)
    (y y) (x x))
  (defstrand ltx-gen 1 (self self) (l ltxb))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb) (ltxb ltxb)
    (x x) (y y))
  (precedes ((0 2) (2 2)) ((1 0) (0 0)) ((1 0) (2 0)) ((2 1) (0 1))
    ((2 3) (0 3)))
  (non-orig ltxb)
  (uniq-orig na nb)
  (uniq-gen y x ltxb)
  (absent (y x) (y ltxb) (x ltxb))
  (operation nonce-test (added-strand init 4) nb (0 3)
    (enc na nb a b
      (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
        (exp (gen) (mul y x)))))
  (traces
    ((recv (cat (exp (gen) ltxb) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x)))))) (recv nb))
    ((send (cat self (exp (gen) ltxb))))
    ((recv (cat (exp (gen) ltxb) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x)))))) (send nb)))
  (label 38)
  (parent 34)
  (realized)
  (shape)
  (maps
    ((0 1 1)
      ((ltxa ltxb) (ltxb ltxb) (a a) (b b) (y y) (x x) (na na) (nb nb)
        (self self) (self-0 self))))
  (origs (na (2 1)) (nb (0 2)))
  (ugens (x (2 1)) (ltxb (1 0)) (y (0 2))))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (y rndx) (x expt) (ltxb rndx))
  (defstrand resp 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb) (ltxb ltxb)
    (y y) (x x))
  (defstrand ltx-gen 1 (self self) (l ltxb))
  (deflistener
    (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
      (exp (gen) (mul y x))))
  (precedes ((0 2) (2 0)) ((1 0) (0 0)) ((2 1) (0 3)))
  (non-orig ltxb)
  (uniq-orig nb)
  (uniq-gen y ltxb)
  (absent (y x) (y ltxb))
  (operation nonce-test
    (added-listener
      (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
        (exp (gen) (mul y x)))) nb (0 3)
    (enc na nb a b
      (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
        (exp (gen) (mul y x)))))
  (traces
    ((recv (cat (exp (gen) ltxb) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x)))))) (recv nb))
    ((send (cat self (exp (gen) ltxb))))
    ((recv
       (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
         (exp (gen) (mul y x))))
      (send
        (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
          (exp (gen) (mul y x))))))
  (label 39)
  (parent 34)
  (unrealized (2 0))
  (origs (nb (0 2)))
  (ugens (ltxb (1 0)) (y (0 2)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self self-0 name) (y x ltxb ltxb-0 rndx))
  (defstrand resp 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb-0)
    (ltxb ltxb) (y y) (x (mul x (rec ltxb) ltxb-0)))
  (defstrand ltx-gen 1 (self self) (l ltxb-0))
  (defstrand ltx-gen 1 (self self-0) (l ltxb))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb)
    (ltxb ltxb-0) (x x) (y (mul y (rec ltxb) ltxb-0)))
  (deflistener (cat (exp (gen) (mul (rec ltxb) ltxb-0)) y))
  (precedes ((0 2) (4 0)) ((1 0) (0 0)) ((1 0) (3 0)) ((2 0) (0 0))
    ((2 0) (3 0)) ((3 1) (0 1)) ((3 3) (0 3)) ((4 1) (3 2)))
  (non-orig ltxb ltxb-0)
  (uniq-orig na nb)
  (uniq-gen y x ltxb ltxb-0)
  (absent (y (mul x (rec ltxb) ltxb-0)) (y ltxb) (y ltxb-0) (x ltxb)
    (x ltxb-0))
  (operation nonce-test
    (added-listener (cat (exp (gen) (mul (rec ltxb) ltxb-0)) y))
    (exp (gen) (mul y (rec ltxb) ltxb-0)) (3 2))
  (traces
    ((recv (cat (exp (gen) ltxb-0) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) (mul x (rec ltxb) ltxb-0))))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb-0)) (exp (gen) (mul x ltxb-0))
              (exp (gen) (mul y x (rec ltxb) ltxb-0)))))) (recv nb))
    ((send (cat self (exp (gen) ltxb-0))))
    ((send (cat self-0 (exp (gen) ltxb))))
    ((recv (cat (exp (gen) ltxb) (exp (gen) ltxb-0)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul y (rec ltxb) ltxb-0))
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb-0)) (exp (gen) (mul x ltxb-0))
              (exp (gen) (mul y x (rec ltxb) ltxb-0)))))) (send nb))
    ((recv (cat (exp (gen) (mul (rec ltxb) ltxb-0)) y))
      (send (cat (exp (gen) (mul (rec ltxb) ltxb-0)) y))))
  (label 40)
  (parent 36)
  (unrealized (0 1) (4 0))
  (dead)
  (comment "empty cohort"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self self-0 name) (ltxa ltxb y rndx) (x expt))
  (defstrand resp 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (y y) (x x))
  (defstrand ltx-gen 1 (self self) (l ltxa))
  (defstrand ltx-gen 1 (self self-0) (l ltxb))
  (deflistener
    (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul y x))))
  (deflistener
    (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul y x))))
  (precedes ((0 2) (4 0)) ((1 0) (0 0)) ((2 0) (0 0)) ((3 1) (0 3))
    ((4 1) (3 0)))
  (non-orig ltxa ltxb)
  (uniq-orig nb)
  (uniq-gen ltxa ltxb y)
  (absent (y ltxa) (y ltxb) (y x))
  (operation encryption-test
    (added-listener
      (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
        (exp (gen) (mul y x))))
    (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul y x))) (3 0))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul y x)))))) (recv nb))
    ((send (cat self (exp (gen) ltxa))))
    ((send (cat self-0 (exp (gen) ltxb))))
    ((recv
       (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
         (exp (gen) (mul y x))))
      (send
        (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
          (exp (gen) (mul y x)))))
    ((recv
       (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
         (exp (gen) (mul y x))))
      (send
        (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
          (exp (gen) (mul y x))))))
  (label 41)
  (parent 37)
  (unrealized (4 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (y rndx) (x expt) (ltxb rndx))
  (defstrand resp 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb) (ltxb ltxb)
    (y y) (x x))
  (defstrand ltx-gen 1 (self self) (l ltxb))
  (deflistener
    (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
      (exp (gen) (mul y x))))
  (deflistener
    (cat (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
      (exp (gen) (mul y x))))
  (precedes ((0 2) (3 0)) ((1 0) (0 0)) ((2 1) (0 3)) ((3 1) (2 0)))
  (non-orig ltxb)
  (uniq-orig nb)
  (uniq-gen y ltxb)
  (absent (y x) (y ltxb))
  (operation encryption-test
    (added-listener
      (cat (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
        (exp (gen) (mul y x))))
    (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
      (exp (gen) (mul y x))) (2 0))
  (traces
    ((recv (cat (exp (gen) ltxb) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x)))))) (recv nb))
    ((send (cat self (exp (gen) ltxb))))
    ((recv
       (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
         (exp (gen) (mul y x))))
      (send
        (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
          (exp (gen) (mul y x)))))
    ((recv
       (cat (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
         (exp (gen) (mul y x))))
      (send
        (cat (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
          (exp (gen) (mul y x))))))
  (label 42)
  (parent 39)
  (unrealized (3 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self self-0 name) (ltxa ltxb y rndx) (x expt))
  (defstrand resp 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (y y) (x x))
  (defstrand ltx-gen 1 (self self) (l ltxa))
  (defstrand ltx-gen 1 (self self-0) (l ltxb))
  (deflistener
    (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul y x))))
  (deflistener
    (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul y x))))
  (deflistener (cat (exp (gen) ltxa) y))
  (precedes ((0 2) (5 0)) ((1 0) (0 0)) ((2 0) (0 0)) ((3 1) (0 3))
    ((4 1) (3 0)) ((5 1) (4 0)))
  (non-orig ltxa ltxb)
  (uniq-orig nb)
  (uniq-gen ltxa ltxb y)
  (absent (y ltxa) (y ltxb) (y x))
  (operation nonce-test (added-listener (cat (exp (gen) ltxa) y))
    (exp (gen) (mul ltxa y)) (4 0))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul y x)))))) (recv nb))
    ((send (cat self (exp (gen) ltxa))))
    ((send (cat self-0 (exp (gen) ltxb))))
    ((recv
       (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
         (exp (gen) (mul y x))))
      (send
        (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
          (exp (gen) (mul y x)))))
    ((recv
       (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
         (exp (gen) (mul y x))))
      (send
        (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
          (exp (gen) (mul y x)))))
    ((recv (cat (exp (gen) ltxa) y)) (send (cat (exp (gen) ltxa) y))))
  (label 43)
  (parent 41)
  (unrealized (5 0))
  (dead)
  (comment "empty cohort"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (y rndx) (x expt) (ltxb rndx))
  (defstrand resp 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb) (ltxb ltxb)
    (y y) (x x))
  (defstrand ltx-gen 1 (self self) (l ltxb))
  (deflistener
    (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
      (exp (gen) (mul y x))))
  (deflistener
    (cat (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
      (exp (gen) (mul y x))))
  (deflistener (cat (exp (gen) ltxb) y))
  (precedes ((0 2) (4 0)) ((1 0) (0 0)) ((2 1) (0 3)) ((3 1) (2 0))
    ((4 1) (3 0)))
  (non-orig ltxb)
  (uniq-orig nb)
  (uniq-gen y ltxb)
  (absent (y x) (y ltxb))
  (operation nonce-test (added-listener (cat (exp (gen) ltxb) y))
    (exp (gen) (mul y ltxb)) (3 0))
  (traces
    ((recv (cat (exp (gen) ltxb) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x)))))) (recv nb))
    ((send (cat self (exp (gen) ltxb))))
    ((recv
       (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
         (exp (gen) (mul y x))))
      (send
        (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
          (exp (gen) (mul y x)))))
    ((recv
       (cat (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
         (exp (gen) (mul y x))))
      (send
        (cat (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
          (exp (gen) (mul y x)))))
    ((recv (cat (exp (gen) ltxb) y)) (send (cat (exp (gen) ltxb) y))))
  (label 44)
  (parent 42)
  (unrealized (4 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol dhcr-um3 diffie-hellman
  (defrole init
    (vars (ltxa ltxb x rndx) (y expt) (a b name) (na nb data))
    (trace (recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul x y)))))) (send nb))
    (uniq-orig na)
    (uniq-gen x)
    (absent (x ltxa) (x ltxb))
    (fn-of ("principal-of" (ltxa a) (ltxb b))
      ("ltx-of" (a ltxa) (b ltxb)))
    (neq ((exp (gen) y) (gen))))
  (defrole resp
    (vars (ltxa ltxb y rndx) (x expt) (a b name) (na nb data))
    (trace (recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul y x)))))) (recv nb))
    (uniq-orig nb)
    (uniq-gen y)
    (absent (y ltxa) (y ltxb) (y x))
    (fn-of ("principal-of" (ltxa a) (ltxb b))
      ("ltx-of" (a ltxa) (b ltxb)))
    (neq ((exp (gen) x) (gen))))
  (defrole ltx-gen
    (vars (self name) (l rndx))
    (trace (send (cat self (exp (gen) l))) (recv "end-of-protocol")
      (send l))
    (uniq-gen l)
    (fn-of ("principal-of" (l self)) ("ltx-of" (self l))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (ltxa ltxb y rndx) (x expt))
  (defstrand resp 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (y y) (x x))
  (defstrand ltx-gen 1 (self self) (l ltxa))
  (non-orig ltxa)
  (uniq-orig nb)
  (uniq-gen ltxa y)
  (absent (y ltxa) (y ltxb) (y x))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul y x)))))) (recv nb))
    ((send (cat self (exp (gen) ltxa)))))
  (label 45)
  (unrealized (0 0) (0 3))
  (preskeleton)
  (origs (nb (0 2)))
  (ugens (ltxa (1 0)) (y (0 2)))
  (comment "Not a skeleton"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (ltxa ltxb y rndx) (x expt))
  (defstrand resp 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (y y) (x x))
  (defstrand ltx-gen 1 (self self) (l ltxa))
  (precedes ((1 0) (0 0)))
  (non-orig ltxa)
  (uniq-orig nb)
  (uniq-gen ltxa y)
  (absent (y ltxa) (y ltxb) (y x))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul y x)))))) (recv nb))
    ((send (cat self (exp (gen) ltxa)))))
  (label 46)
  (parent 45)
  (unrealized (0 3))
  (origs (nb (0 2)))
  (ugens (ltxa (1 0)) (y (0 2)))
  (comment "3 in cohort - 3 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (y x ltxa ltxb rndx))
  (defstrand resp 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (y y) (x x))
  (defstrand ltx-gen 1 (self self) (l ltxa))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (x x) (y y))
  (precedes ((0 2) (2 2)) ((1 0) (0 0)) ((1 0) (2 0)) ((2 1) (0 1))
    ((2 3) (0 3)))
  (non-orig ltxa)
  (uniq-orig na nb)
  (uniq-gen y x ltxa)
  (absent (y x) (y ltxa) (y ltxb) (x ltxa) (x ltxb))
  (operation nonce-test (added-strand init 4) nb (0 3)
    (enc na nb a b
      (hash (exp (gen) (mul y ltxa)) (exp (gen) (mul x ltxb))
        (exp (gen) (mul y x)))))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxa)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x)))))) (recv nb))
    ((send (cat self (exp (gen) ltxa))))
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxa)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x)))))) (send nb)))
  (label 47)
  (parent 46)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((ltxa ltxa) (ltxb ltxb) (a a) (b b) (y y) (x x) (na na) (nb nb)
        (self self))))
  (origs (na (2 1)) (nb (0 2)))
  (ugens (x (2 1)) (ltxa (1 0)) (y (0 2))))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (y x ltxb ltxb-0 rndx))
  (defstrand resp 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb-0)
    (ltxb ltxb) (y y) (x (mul x (rec ltxb) ltxb-0)))
  (defstrand ltx-gen 1 (self self) (l ltxb-0))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb)
    (ltxb ltxb-0) (x x) (y (mul y (rec ltxb) ltxb-0)))
  (precedes ((0 2) (2 2)) ((1 0) (0 0)) ((1 0) (2 0)) ((2 1) (0 1))
    ((2 3) (0 3)))
  (non-orig ltxb-0)
  (uniq-orig na nb)
  (uniq-gen y x ltxb-0)
  (absent (y (mul x (rec ltxb) ltxb-0)) (y ltxb) (y ltxb-0) (x ltxb)
    (x ltxb-0))
  (operation nonce-test (added-strand init 4) nb (0 3)
    (enc na nb a b
      (hash (exp (gen) (mul y ltxb-0)) (exp (gen) (mul x ltxb-0))
        (exp (gen) (mul y x (rec ltxb) ltxb-0)))))
  (traces
    ((recv (cat (exp (gen) ltxb-0) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) (mul x (rec ltxb) ltxb-0))))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb-0)) (exp (gen) (mul x ltxb-0))
              (exp (gen) (mul y x (rec ltxb) ltxb-0)))))) (recv nb))
    ((send (cat self (exp (gen) ltxb-0))))
    ((recv (cat (exp (gen) ltxb) (exp (gen) ltxb-0)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul y (rec ltxb) ltxb-0))
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb-0)) (exp (gen) (mul x ltxb-0))
              (exp (gen) (mul y x (rec ltxb) ltxb-0)))))) (send nb)))
  (label 48)
  (parent 46)
  (unrealized (0 1) (2 2))
  (comment "3 in cohort - 3 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (ltxa ltxb y rndx) (x expt))
  (defstrand resp 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (y y) (x x))
  (defstrand ltx-gen 1 (self self) (l ltxa))
  (deflistener
    (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul y x))))
  (precedes ((0 2) (2 0)) ((1 0) (0 0)) ((2 1) (0 3)))
  (non-orig ltxa)
  (uniq-orig nb)
  (uniq-gen ltxa y)
  (absent (y ltxa) (y ltxb) (y x))
  (operation nonce-test
    (added-listener
      (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
        (exp (gen) (mul y x)))) nb (0 3)
    (enc na nb a b
      (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
        (exp (gen) (mul y x)))))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul y x)))))) (recv nb))
    ((send (cat self (exp (gen) ltxa))))
    ((recv
       (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
         (exp (gen) (mul y x))))
      (send
        (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
          (exp (gen) (mul y x))))))
  (label 49)
  (parent 46)
  (unrealized (2 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (y ltxb x rndx))
  (defstrand resp 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb) (ltxb ltxb)
    (y y) (x x))
  (defstrand ltx-gen 1 (self self) (l ltxb))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb) (ltxb ltxb)
    (x x) (y y))
  (precedes ((0 2) (2 2)) ((1 0) (0 0)) ((1 0) (2 0)) ((2 1) (0 1))
    ((2 3) (0 3)))
  (non-orig ltxb)
  (uniq-orig na nb)
  (uniq-gen y ltxb x)
  (absent (y ltxb) (y x) (x ltxb))
  (operation nonce-test (displaced 3 0 resp 3) (exp (gen) y) (2 2))
  (traces
    ((recv (cat (exp (gen) ltxb) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul y x)))))) (recv nb))
    ((send (cat self (exp (gen) ltxb))))
    ((recv (cat (exp (gen) ltxb) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul y x)))))) (send nb)))
  (label 50)
  (parent 48)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((ltxa ltxb) (ltxb ltxb) (a a) (b b) (y y) (x x) (na na) (nb nb)
        (self self))))
  (origs (nb (0 2)) (na (2 1)))
  (ugens (y (0 2)) (x (2 1)) (ltxb (1 0))))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (y x ltxb ltxb-0 rndx))
  (defstrand resp 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb-0)
    (ltxb ltxb) (y y) (x (mul x (rec ltxb) ltxb-0)))
  (defstrand ltx-gen 1 (self self) (l ltxb-0))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb)
    (ltxb ltxb-0) (x x) (y (mul y (rec ltxb) ltxb-0)))
  (deflistener (cat (exp (gen) (mul y ltxb-0)) ltxb))
  (precedes ((0 2) (3 0)) ((1 0) (0 0)) ((1 0) (2 0)) ((2 1) (0 1))
    ((2 3) (0 3)) ((3 1) (2 2)))
  (non-orig ltxb-0)
  (uniq-orig na nb)
  (uniq-gen y x ltxb-0)
  (absent (y (mul x (rec ltxb) ltxb-0)) (y ltxb) (y ltxb-0) (x ltxb)
    (x ltxb-0))
  (operation nonce-test
    (added-listener (cat (exp (gen) (mul y ltxb-0)) ltxb))
    (exp (gen) (mul y (rec ltxb) ltxb-0)) (2 2))
  (traces
    ((recv (cat (exp (gen) ltxb-0) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) (mul x (rec ltxb) ltxb-0))))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb-0)) (exp (gen) (mul x ltxb-0))
              (exp (gen) (mul y x (rec ltxb) ltxb-0)))))) (recv nb))
    ((send (cat self (exp (gen) ltxb-0))))
    ((recv (cat (exp (gen) ltxb) (exp (gen) ltxb-0)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul y (rec ltxb) ltxb-0))
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb-0)) (exp (gen) (mul x ltxb-0))
              (exp (gen) (mul y x (rec ltxb) ltxb-0)))))) (send nb))
    ((recv (cat (exp (gen) (mul y ltxb-0)) ltxb))
      (send (cat (exp (gen) (mul y ltxb-0)) ltxb))))
  (label 51)
  (parent 48)
  (unrealized (0 1) (3 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (y x ltxb ltxb-0 rndx))
  (defstrand resp 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb-0)
    (ltxb ltxb) (y y) (x (mul x (rec ltxb) ltxb-0)))
  (defstrand ltx-gen 1 (self self) (l ltxb-0))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb)
    (ltxb ltxb-0) (x x) (y (mul y (rec ltxb) ltxb-0)))
  (deflistener (cat (exp (gen) (mul (rec ltxb) ltxb-0)) y))
  (precedes ((0 2) (3 0)) ((1 0) (0 0)) ((1 0) (2 0)) ((2 1) (0 1))
    ((2 3) (0 3)) ((3 1) (2 2)))
  (non-orig ltxb-0)
  (uniq-orig na nb)
  (uniq-gen y x ltxb-0)
  (absent (y (mul x (rec ltxb) ltxb-0)) (y ltxb) (y ltxb-0) (x ltxb)
    (x ltxb-0))
  (operation nonce-test
    (added-listener (cat (exp (gen) (mul (rec ltxb) ltxb-0)) y))
    (exp (gen) (mul y (rec ltxb) ltxb-0)) (2 2))
  (traces
    ((recv (cat (exp (gen) ltxb-0) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) (mul x (rec ltxb) ltxb-0))))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb-0)) (exp (gen) (mul x ltxb-0))
              (exp (gen) (mul y x (rec ltxb) ltxb-0)))))) (recv nb))
    ((send (cat self (exp (gen) ltxb-0))))
    ((recv (cat (exp (gen) ltxb) (exp (gen) ltxb-0)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul y (rec ltxb) ltxb-0))
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb-0)) (exp (gen) (mul x ltxb-0))
              (exp (gen) (mul y x (rec ltxb) ltxb-0)))))) (send nb))
    ((recv (cat (exp (gen) (mul (rec ltxb) ltxb-0)) y))
      (send (cat (exp (gen) (mul (rec ltxb) ltxb-0)) y))))
  (label 52)
  (parent 48)
  (unrealized (0 1) (3 0))
  (dead)
  (comment "empty cohort"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (ltxa ltxb y rndx) (x expt))
  (defstrand resp 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (y y) (x x))
  (defstrand ltx-gen 1 (self self) (l ltxa))
  (deflistener
    (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul y x))))
  (deflistener
    (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul y x))))
  (precedes ((0 2) (3 0)) ((1 0) (0 0)) ((2 1) (0 3)) ((3 1) (2 0)))
  (non-orig ltxa)
  (uniq-orig nb)
  (uniq-gen ltxa y)
  (absent (y ltxa) (y ltxb) (y x))
  (operation encryption-test
    (added-listener
      (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
        (exp (gen) (mul y x))))
    (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul y x))) (2 0))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul y x)))))) (recv nb))
    ((send (cat self (exp (gen) ltxa))))
    ((recv
       (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
         (exp (gen) (mul y x))))
      (send
        (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
          (exp (gen) (mul y x)))))
    ((recv
       (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
         (exp (gen) (mul y x))))
      (send
        (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
          (exp (gen) (mul y x))))))
  (label 53)
  (parent 49)
  (unrealized (3 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (y x ltxb ltxb-0 rndx))
  (defstrand resp 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb-0)
    (ltxb ltxb) (y y) (x (mul x (rec ltxb) ltxb-0)))
  (defstrand ltx-gen 1 (self self) (l ltxb-0))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb)
    (ltxb ltxb-0) (x x) (y (mul y (rec ltxb) ltxb-0)))
  (deflistener (cat (exp (gen) (mul y ltxb-0)) ltxb))
  (deflistener (cat (exp (gen) ltxb-0) y))
  (precedes ((0 2) (4 0)) ((1 0) (0 0)) ((1 0) (2 0)) ((2 1) (0 1))
    ((2 3) (0 3)) ((3 1) (2 2)) ((4 1) (3 0)))
  (non-orig ltxb-0)
  (uniq-orig na nb)
  (uniq-gen y x ltxb-0)
  (absent (y (mul x (rec ltxb) ltxb-0)) (y ltxb) (y ltxb-0) (x ltxb)
    (x ltxb-0))
  (operation nonce-test (added-listener (cat (exp (gen) ltxb-0) y))
    (exp (gen) (mul y ltxb-0)) (3 0))
  (traces
    ((recv (cat (exp (gen) ltxb-0) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) (mul x (rec ltxb) ltxb-0))))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb-0)) (exp (gen) (mul x ltxb-0))
              (exp (gen) (mul y x (rec ltxb) ltxb-0)))))) (recv nb))
    ((send (cat self (exp (gen) ltxb-0))))
    ((recv (cat (exp (gen) ltxb) (exp (gen) ltxb-0)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul y (rec ltxb) ltxb-0))
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb-0)) (exp (gen) (mul x ltxb-0))
              (exp (gen) (mul y x (rec ltxb) ltxb-0)))))) (send nb))
    ((recv (cat (exp (gen) (mul y ltxb-0)) ltxb))
      (send (cat (exp (gen) (mul y ltxb-0)) ltxb)))
    ((recv (cat (exp (gen) ltxb-0) y))
      (send (cat (exp (gen) ltxb-0) y))))
  (label 54)
  (parent 51)
  (unrealized (0 1) (4 0))
  (dead)
  (comment "empty cohort"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (ltxa ltxb y rndx) (x expt))
  (defstrand resp 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (y y) (x x))
  (defstrand ltx-gen 1 (self self) (l ltxa))
  (deflistener
    (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul y x))))
  (deflistener
    (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul y x))))
  (deflistener (cat (exp (gen) ltxa) y))
  (precedes ((0 2) (4 0)) ((1 0) (0 0)) ((2 1) (0 3)) ((3 1) (2 0))
    ((4 1) (3 0)))
  (non-orig ltxa)
  (uniq-orig nb)
  (uniq-gen ltxa y)
  (absent (y ltxa) (y ltxb) (y x))
  (operation nonce-test (added-listener (cat (exp (gen) ltxa) y))
    (exp (gen) (mul ltxa y)) (3 0))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul y x)))))) (recv nb))
    ((send (cat self (exp (gen) ltxa))))
    ((recv
       (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
         (exp (gen) (mul y x))))
      (send
        (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
          (exp (gen) (mul y x)))))
    ((recv
       (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
         (exp (gen) (mul y x))))
      (send
        (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
          (exp (gen) (mul y x)))))
    ((recv (cat (exp (gen) ltxa) y)) (send (cat (exp (gen) ltxa) y))))
  (label 55)
  (parent 53)
  (unrealized (4 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol dhcr-um3 diffie-hellman
  (defrole init
    (vars (ltxa ltxb x rndx) (y expt) (a b name) (na nb data))
    (trace (recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul x y)))))) (send nb))
    (uniq-orig na)
    (uniq-gen x)
    (absent (x ltxa) (x ltxb))
    (fn-of ("principal-of" (ltxa a) (ltxb b))
      ("ltx-of" (a ltxa) (b ltxb)))
    (neq ((exp (gen) y) (gen))))
  (defrole resp
    (vars (ltxa ltxb y rndx) (x expt) (a b name) (na nb data))
    (trace (recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul y x)))))) (recv nb))
    (uniq-orig nb)
    (uniq-gen y)
    (absent (y ltxa) (y ltxb) (y x))
    (fn-of ("principal-of" (ltxa a) (ltxb b))
      ("ltx-of" (a ltxa) (b ltxb)))
    (neq ((exp (gen) x) (gen))))
  (defrole ltx-gen
    (vars (self name) (l rndx))
    (trace (send (cat self (exp (gen) l))) (recv "end-of-protocol")
      (send l))
    (uniq-gen l)
    (fn-of ("principal-of" (l self)) ("ltx-of" (self l))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self self-0 name) (ltxa ltxb x rndx) (y expt))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (x x) (y y))
  (deflistener
    (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul x y))))
  (defstrand ltx-gen 3 (self self) (l ltxa))
  (defstrand ltx-gen 3 (self self-0) (l ltxb))
  (precedes ((0 3) (2 1)) ((0 3) (3 1)))
  (uniq-orig na)
  (uniq-gen ltxa ltxb x)
  (absent (x ltxa) (x ltxb))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul x y)))))) (send nb))
    ((recv
       (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
          (exp (gen) (mul x y)))))
    ((send (cat self (exp (gen) ltxa))) (recv "end-of-protocol")
      (send ltxa))
    ((send (cat self-0 (exp (gen) ltxb))) (recv "end-of-protocol")
      (send ltxb)))
  (label 56)
  (unrealized (0 0) (0 2) (1 0))
  (preskeleton)
  (origs (na (0 1)))
  (ugens (ltxb (3 0)) (ltxa (2 0)) (x (0 1)))
  (comment "Not a skeleton"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self self-0 name) (ltxa ltxb x rndx) (y expt))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (x x) (y y))
  (deflistener
    (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul x y))))
  (defstrand ltx-gen 3 (self self) (l ltxa))
  (defstrand ltx-gen 3 (self self-0) (l ltxb))
  (precedes ((0 1) (1 0)) ((0 3) (2 1)) ((0 3) (3 1)) ((2 0) (0 0))
    ((3 0) (0 0)))
  (uniq-orig na)
  (uniq-gen ltxa ltxb x)
  (absent (x ltxa) (x ltxb))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul x y)))))) (send nb))
    ((recv
       (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
          (exp (gen) (mul x y)))))
    ((send (cat self (exp (gen) ltxa))) (recv "end-of-protocol")
      (send ltxa))
    ((send (cat self-0 (exp (gen) ltxb))) (recv "end-of-protocol")
      (send ltxb)))
  (label 57)
  (parent 56)
  (unrealized (0 2) (1 0))
  (origs (na (0 1)))
  (ugens (ltxb (3 0)) (ltxa (2 0)) (x (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (x rndx) (y expt) (ltxb rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb) (ltxb ltxb)
    (x x) (y y))
  (deflistener
    (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
      (exp (gen) (mul x y))))
  (defstrand ltx-gen 3 (self self) (l ltxb))
  (precedes ((0 1) (1 0)) ((0 3) (2 1)) ((2 0) (0 0)))
  (uniq-orig na)
  (uniq-gen x ltxb)
  (absent (x ltxb))
  (operation collapsed 3 2)
  (traces
    ((recv (cat (exp (gen) ltxb) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul x y)))))) (send nb))
    ((recv
       (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
          (exp (gen) (mul x y)))))
    ((send (cat self (exp (gen) ltxb))) (recv "end-of-protocol")
      (send ltxb)))
  (label 58)
  (parent 57)
  (unrealized (0 2) (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self self-0 name) (ltxa ltxb x rndx) (y expt))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (x x) (y y))
  (deflistener
    (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul x y))))
  (defstrand ltx-gen 3 (self self) (l ltxa))
  (defstrand ltx-gen 3 (self self-0) (l ltxb))
  (deflistener
    (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul x y))))
  (precedes ((0 1) (4 0)) ((0 3) (2 1)) ((0 3) (3 1)) ((2 0) (0 0))
    ((3 0) (0 0)) ((4 1) (1 0)))
  (uniq-orig na)
  (uniq-gen ltxa ltxb x)
  (absent (x ltxa) (x ltxb))
  (operation encryption-test
    (added-listener
      (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
        (exp (gen) (mul x y))))
    (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul x y))) (1 0))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul x y)))))) (send nb))
    ((recv
       (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
          (exp (gen) (mul x y)))))
    ((send (cat self (exp (gen) ltxa))) (recv "end-of-protocol")
      (send ltxa))
    ((send (cat self-0 (exp (gen) ltxb))) (recv "end-of-protocol")
      (send ltxb))
    ((recv
       (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
         (exp (gen) (mul x y))))
      (send
        (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
          (exp (gen) (mul x y))))))
  (label 59)
  (parent 57)
  (unrealized (0 2) (4 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (x rndx) (y expt) (ltxb rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb) (ltxb ltxb)
    (x x) (y y))
  (deflistener
    (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
      (exp (gen) (mul x y))))
  (defstrand ltx-gen 3 (self self) (l ltxb))
  (deflistener
    (cat (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
      (exp (gen) (mul x y))))
  (precedes ((0 1) (3 0)) ((0 3) (2 1)) ((2 0) (0 0)) ((3 1) (1 0)))
  (uniq-orig na)
  (uniq-gen x ltxb)
  (absent (x ltxb))
  (operation encryption-test
    (added-listener
      (cat (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
        (exp (gen) (mul x y))))
    (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
      (exp (gen) (mul x y))) (1 0))
  (traces
    ((recv (cat (exp (gen) ltxb) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul x y)))))) (send nb))
    ((recv
       (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
          (exp (gen) (mul x y)))))
    ((send (cat self (exp (gen) ltxb))) (recv "end-of-protocol")
      (send ltxb))
    ((recv
       (cat (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
         (exp (gen) (mul x y))))
      (send
        (cat (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
          (exp (gen) (mul x y))))))
  (label 60)
  (parent 58)
  (unrealized (0 2) (3 0))
  (origs (na (0 1)))
  (ugens (ltxb (2 0)) (x (0 1)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self self-0 name) (ltxa ltxb x rndx) (y expt))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (x x) (y y))
  (deflistener
    (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul x y))))
  (defstrand ltx-gen 3 (self self) (l ltxa))
  (defstrand ltx-gen 3 (self self-0) (l ltxb))
  (deflistener
    (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul x y))))
  (deflistener (cat (exp (gen) ltxb) x))
  (precedes ((0 1) (5 0)) ((0 3) (2 1)) ((0 3) (3 1)) ((2 0) (0 0))
    ((3 0) (0 0)) ((4 1) (1 0)) ((5 1) (4 0)))
  (uniq-orig na)
  (uniq-gen ltxa ltxb x)
  (absent (x ltxa) (x ltxb))
  (operation nonce-test (added-listener (cat (exp (gen) ltxb) x))
    (exp (gen) (mul ltxb x)) (4 0))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul x y)))))) (send nb))
    ((recv
       (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
          (exp (gen) (mul x y)))))
    ((send (cat self (exp (gen) ltxa))) (recv "end-of-protocol")
      (send ltxa))
    ((send (cat self-0 (exp (gen) ltxb))) (recv "end-of-protocol")
      (send ltxb))
    ((recv
       (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
         (exp (gen) (mul x y))))
      (send
        (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
          (exp (gen) (mul x y)))))
    ((recv (cat (exp (gen) ltxb) x)) (send (cat (exp (gen) ltxb) x))))
  (label 61)
  (parent 59)
  (unrealized (0 2) (5 0))
  (dead)
  (comment "empty cohort"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self self-0 name) (ltxa ltxb x rndx) (y expt))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (x x) (y y))
  (deflistener
    (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul x y))))
  (defstrand ltx-gen 3 (self self) (l ltxa))
  (defstrand ltx-gen 3 (self self-0) (l ltxb))
  (deflistener
    (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
      (exp (gen) (mul x y))))
  (deflistener (cat (exp (gen) x) ltxb))
  (precedes ((0 1) (5 0)) ((0 3) (2 1)) ((0 3) (3 1)) ((2 0) (0 0))
    ((3 0) (0 0)) ((4 1) (1 0)) ((5 1) (4 0)))
  (uniq-orig na)
  (uniq-gen ltxa ltxb x)
  (absent (x ltxa) (x ltxb))
  (operation nonce-test (added-listener (cat (exp (gen) x) ltxb))
    (exp (gen) (mul ltxb x)) (4 0))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul x y)))))) (send nb))
    ((recv
       (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
          (exp (gen) (mul x y)))))
    ((send (cat self (exp (gen) ltxa))) (recv "end-of-protocol")
      (send ltxa))
    ((send (cat self-0 (exp (gen) ltxb))) (recv "end-of-protocol")
      (send ltxb))
    ((recv
       (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
         (exp (gen) (mul x y))))
      (send
        (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
          (exp (gen) (mul x y)))))
    ((recv (cat (exp (gen) x) ltxb)) (send (cat (exp (gen) x) ltxb))))
  (label 62)
  (parent 59)
  (unrealized (0 2) (5 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (x rndx) (y expt) (ltxb rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb) (ltxb ltxb)
    (x x) (y y))
  (deflistener
    (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
      (exp (gen) (mul x y))))
  (defstrand ltx-gen 3 (self self) (l ltxb))
  (deflistener
    (cat (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
      (exp (gen) (mul x y))))
  (deflistener (cat (exp (gen) x) ltxb))
  (precedes ((0 1) (4 0)) ((0 3) (2 1)) ((2 0) (0 0)) ((3 1) (1 0))
    ((4 1) (3 0)))
  (uniq-orig na)
  (uniq-gen x ltxb)
  (absent (x ltxb))
  (operation nonce-test (added-listener (cat (exp (gen) x) ltxb))
    (exp (gen) (mul x ltxb)) (3 0))
  (traces
    ((recv (cat (exp (gen) ltxb) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul x y)))))) (send nb))
    ((recv
       (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
          (exp (gen) (mul x y)))))
    ((send (cat self (exp (gen) ltxb))) (recv "end-of-protocol")
      (send ltxb))
    ((recv
       (cat (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
         (exp (gen) (mul x y))))
      (send
        (cat (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
          (exp (gen) (mul x y)))))
    ((recv (cat (exp (gen) x) ltxb)) (send (cat (exp (gen) x) ltxb))))
  (label 63)
  (parent 60)
  (unrealized (0 2) (4 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (x rndx) (y expt) (ltxb rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb) (ltxb ltxb)
    (x x) (y y))
  (deflistener
    (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
      (exp (gen) (mul x y))))
  (defstrand ltx-gen 3 (self self) (l ltxb))
  (deflistener
    (cat (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
      (exp (gen) (mul x y))))
  (deflistener (cat (exp (gen) ltxb) x))
  (precedes ((0 1) (4 0)) ((0 3) (2 1)) ((2 0) (0 0)) ((3 1) (1 0))
    ((4 1) (3 0)))
  (uniq-orig na)
  (uniq-gen x ltxb)
  (absent (x ltxb))
  (operation nonce-test (added-listener (cat (exp (gen) ltxb) x))
    (exp (gen) (mul x ltxb)) (3 0))
  (traces
    ((recv (cat (exp (gen) ltxb) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul x y)))))) (send nb))
    ((recv
       (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
          (exp (gen) (mul x y)))))
    ((send (cat self (exp (gen) ltxb))) (recv "end-of-protocol")
      (send ltxb))
    ((recv
       (cat (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
         (exp (gen) (mul x y))))
      (send
        (cat (exp (gen) (mul y ltxb)) (exp (gen) (mul x ltxb))
          (exp (gen) (mul x y)))))
    ((recv (cat (exp (gen) ltxb) x)) (send (cat (exp (gen) ltxb) x))))
  (label 64)
  (parent 60)
  (unrealized (0 2) (4 0))
  (dead)
  (comment "empty cohort"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self self-0 name) (ltxa x rndx) (y expt)
    (l rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb l)
    (x x) (y y))
  (deflistener
    (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
      (exp (gen) (mul x y))))
  (defstrand ltx-gen 3 (self self) (l ltxa))
  (defstrand ltx-gen 3 (self self-0) (l l))
  (deflistener
    (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
      (exp (gen) (mul x y))))
  (deflistener (cat (exp (gen) x) l))
  (precedes ((0 3) (2 1)) ((0 3) (3 1)) ((2 0) (0 0)) ((3 0) (0 0))
    ((3 2) (5 0)) ((4 1) (1 0)) ((5 1) (4 0)))
  (uniq-orig na)
  (uniq-gen ltxa x l)
  (absent (x ltxa) (x l))
  (operation nonce-test (displaced 6 3 ltx-gen 3) l (5 0))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) l)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
              (exp (gen) (mul x y)))))) (send nb))
    ((recv
       (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
          (exp (gen) (mul x y)))))
    ((send (cat self (exp (gen) ltxa))) (recv "end-of-protocol")
      (send ltxa))
    ((send (cat self-0 (exp (gen) l))) (recv "end-of-protocol")
      (send l))
    ((recv
       (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
         (exp (gen) (mul x y))))
      (send
        (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
          (exp (gen) (mul x y)))))
    ((recv (cat (exp (gen) x) l)) (send (cat (exp (gen) x) l))))
  (label 65)
  (parent 62)
  (unrealized (0 2))
  (comment "3 in cohort - 3 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (x rndx) (y expt) (l rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa l) (ltxb l) (x x)
    (y y))
  (deflistener
    (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
      (exp (gen) (mul x y))))
  (defstrand ltx-gen 3 (self self) (l l))
  (deflistener
    (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
      (exp (gen) (mul x y))))
  (deflistener (cat (exp (gen) x) l))
  (precedes ((0 3) (2 1)) ((2 0) (0 0)) ((2 2) (4 0)) ((3 1) (1 0))
    ((4 1) (3 0)))
  (uniq-orig na)
  (uniq-gen x l)
  (absent (x l))
  (operation nonce-test (displaced 5 2 ltx-gen 3) l (4 0))
  (traces
    ((recv (cat (exp (gen) l) (exp (gen) l)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
              (exp (gen) (mul x y)))))) (send nb))
    ((recv
       (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
          (exp (gen) (mul x y)))))
    ((send (cat self (exp (gen) l))) (recv "end-of-protocol") (send l))
    ((recv
       (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
         (exp (gen) (mul x y))))
      (send
        (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
          (exp (gen) (mul x y)))))
    ((recv (cat (exp (gen) x) l)) (send (cat (exp (gen) x) l))))
  (label 66)
  (parent 63)
  (unrealized (0 2))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self self-0 name) (y x ltxa ltxb rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (x x) (y y))
  (deflistener
    (hash (exp (gen) (mul y ltxa)) (exp (gen) (mul x ltxb))
      (exp (gen) (mul y x))))
  (defstrand ltx-gen 3 (self self) (l ltxa))
  (defstrand ltx-gen 3 (self self-0) (l ltxb))
  (deflistener
    (cat (exp (gen) (mul y ltxa)) (exp (gen) (mul x ltxb))
      (exp (gen) (mul y x))))
  (deflistener (cat (exp (gen) x) ltxb))
  (defstrand resp 3 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (y y) (x x))
  (precedes ((0 1) (6 1)) ((0 3) (2 1)) ((0 3) (3 1)) ((2 0) (0 0))
    ((2 0) (6 0)) ((3 0) (0 0)) ((3 0) (6 0)) ((3 2) (5 0))
    ((4 1) (1 0)) ((5 1) (4 0)) ((6 2) (0 2)))
  (uniq-orig na nb)
  (uniq-gen y x ltxa ltxb)
  (absent (y x) (y ltxa) (y ltxb) (x ltxa) (x ltxb))
  (operation encryption-test (added-strand resp 3)
    (enc na nb a b
      (hash (exp (gen) (mul y ltxa)) (exp (gen) (mul x ltxb))
        (exp (gen) (mul y x)))) (0 2))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxa)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x)))))) (send nb))
    ((recv
       (hash (exp (gen) (mul y ltxa)) (exp (gen) (mul x ltxb))
         (exp (gen) (mul y x))))
      (send
        (hash (exp (gen) (mul y ltxa)) (exp (gen) (mul x ltxb))
          (exp (gen) (mul y x)))))
    ((send (cat self (exp (gen) ltxa))) (recv "end-of-protocol")
      (send ltxa))
    ((send (cat self-0 (exp (gen) ltxb))) (recv "end-of-protocol")
      (send ltxb))
    ((recv
       (cat (exp (gen) (mul y ltxa)) (exp (gen) (mul x ltxb))
         (exp (gen) (mul y x))))
      (send
        (cat (exp (gen) (mul y ltxa)) (exp (gen) (mul x ltxb))
          (exp (gen) (mul y x)))))
    ((recv (cat (exp (gen) x) ltxb)) (send (cat (exp (gen) x) ltxb)))
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxa)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x))))))))
  (label 67)
  (parent 65)
  (unrealized (4 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self self-0 name) (y x l ltxb rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb) (ltxb l)
    (x x) (y (mul y l (rec ltxb))))
  (deflistener
    (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
      (exp (gen) (mul y x l (rec ltxb)))))
  (defstrand ltx-gen 3 (self self) (l ltxb))
  (defstrand ltx-gen 3 (self self-0) (l l))
  (deflistener
    (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
      (exp (gen) (mul y x l (rec ltxb)))))
  (deflistener (cat (exp (gen) x) l))
  (defstrand resp 3 (na na) (nb nb) (a a) (b b) (ltxa l) (ltxb ltxb)
    (y y) (x (mul x l (rec ltxb))))
  (precedes ((0 1) (6 1)) ((0 3) (2 1)) ((0 3) (3 1)) ((2 0) (0 0))
    ((2 0) (6 0)) ((3 0) (0 0)) ((3 0) (6 0)) ((3 2) (5 0))
    ((4 1) (1 0)) ((5 1) (4 0)) ((6 2) (0 2)))
  (uniq-orig na nb)
  (uniq-gen y x l ltxb)
  (absent (y (mul x l (rec ltxb))) (y l) (y ltxb) (x l) (x ltxb))
  (operation encryption-test (added-strand resp 3)
    (enc na nb a b
      (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
        (exp (gen) (mul y x l (rec ltxb))))) (0 2))
  (traces
    ((recv (cat (exp (gen) ltxb) (exp (gen) l)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul y l (rec ltxb)))
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
              (exp (gen) (mul y x l (rec ltxb))))))) (send nb))
    ((recv
       (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
         (exp (gen) (mul y x l (rec ltxb)))))
      (send
        (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
          (exp (gen) (mul y x l (rec ltxb))))))
    ((send (cat self (exp (gen) ltxb))) (recv "end-of-protocol")
      (send ltxb))
    ((send (cat self-0 (exp (gen) l))) (recv "end-of-protocol")
      (send l))
    ((recv
       (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
         (exp (gen) (mul y x l (rec ltxb)))))
      (send
        (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
          (exp (gen) (mul y x l (rec ltxb))))))
    ((recv (cat (exp (gen) x) l)) (send (cat (exp (gen) x) l)))
    ((recv (cat (exp (gen) l) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) (mul x l (rec ltxb)))))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
              (exp (gen) (mul y x l (rec ltxb)))))))))
  (label 68)
  (parent 65)
  (unrealized (0 2) (4 0) (6 1))
  (comment "3 in cohort - 3 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self self-0 name) (ltxa x rndx) (y expt)
    (l rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb l)
    (x x) (y y))
  (deflistener
    (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
      (exp (gen) (mul x y))))
  (defstrand ltx-gen 3 (self self) (l ltxa))
  (defstrand ltx-gen 3 (self self-0) (l l))
  (deflistener
    (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
      (exp (gen) (mul x y))))
  (deflistener (cat (exp (gen) x) l))
  (deflistener
    (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
      (exp (gen) (mul x y))))
  (precedes ((0 1) (6 0)) ((0 3) (2 1)) ((0 3) (3 1)) ((2 0) (0 0))
    ((3 0) (0 0)) ((3 2) (5 0)) ((4 1) (1 0)) ((5 1) (4 0))
    ((6 1) (0 2)))
  (uniq-orig na)
  (uniq-gen ltxa x l)
  (absent (x ltxa) (x l))
  (operation encryption-test
    (added-listener
      (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
        (exp (gen) (mul x y))))
    (enc na nb a b
      (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
        (exp (gen) (mul x y)))) (0 2))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) l)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
              (exp (gen) (mul x y)))))) (send nb))
    ((recv
       (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
          (exp (gen) (mul x y)))))
    ((send (cat self (exp (gen) ltxa))) (recv "end-of-protocol")
      (send ltxa))
    ((send (cat self-0 (exp (gen) l))) (recv "end-of-protocol")
      (send l))
    ((recv
       (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
         (exp (gen) (mul x y))))
      (send
        (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
          (exp (gen) (mul x y)))))
    ((recv (cat (exp (gen) x) l)) (send (cat (exp (gen) x) l)))
    ((recv
       (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
          (exp (gen) (mul x y))))))
  (label 69)
  (parent 65)
  (unrealized (6 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (y x l rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa l) (ltxb l) (x x)
    (y y))
  (deflistener
    (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
      (exp (gen) (mul y x))))
  (defstrand ltx-gen 3 (self self) (l l))
  (deflistener
    (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
      (exp (gen) (mul y x))))
  (deflistener (cat (exp (gen) x) l))
  (defstrand resp 3 (na na) (nb nb) (a a) (b b) (ltxa l) (ltxb l) (y y)
    (x x))
  (precedes ((0 1) (5 1)) ((0 3) (2 1)) ((2 0) (0 0)) ((2 0) (5 0))
    ((2 2) (4 0)) ((3 1) (1 0)) ((4 1) (3 0)) ((5 2) (0 2)))
  (uniq-orig na nb)
  (uniq-gen y x l)
  (absent (y x) (y l) (x l))
  (operation encryption-test (added-strand resp 3)
    (enc na nb a b
      (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
        (exp (gen) (mul y x)))) (0 2))
  (traces
    ((recv (cat (exp (gen) l) (exp (gen) l)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
              (exp (gen) (mul y x)))))) (send nb))
    ((recv
       (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
         (exp (gen) (mul y x))))
      (send
        (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
          (exp (gen) (mul y x)))))
    ((send (cat self (exp (gen) l))) (recv "end-of-protocol") (send l))
    ((recv
       (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
         (exp (gen) (mul y x))))
      (send
        (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
          (exp (gen) (mul y x)))))
    ((recv (cat (exp (gen) x) l)) (send (cat (exp (gen) x) l)))
    ((recv (cat (exp (gen) l) (exp (gen) l)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
              (exp (gen) (mul y x))))))))
  (label 70)
  (parent 66)
  (unrealized (3 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (x rndx) (y expt) (l rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa l) (ltxb l) (x x)
    (y y))
  (deflistener
    (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
      (exp (gen) (mul x y))))
  (defstrand ltx-gen 3 (self self) (l l))
  (deflistener
    (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
      (exp (gen) (mul x y))))
  (deflistener (cat (exp (gen) x) l))
  (deflistener
    (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
      (exp (gen) (mul x y))))
  (precedes ((0 1) (5 0)) ((0 3) (2 1)) ((2 0) (0 0)) ((2 2) (4 0))
    ((3 1) (1 0)) ((4 1) (3 0)) ((5 1) (0 2)))
  (uniq-orig na)
  (uniq-gen x l)
  (absent (x l))
  (operation encryption-test
    (added-listener
      (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
        (exp (gen) (mul x y))))
    (enc na nb a b
      (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
        (exp (gen) (mul x y)))) (0 2))
  (traces
    ((recv (cat (exp (gen) l) (exp (gen) l)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
              (exp (gen) (mul x y)))))) (send nb))
    ((recv
       (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
          (exp (gen) (mul x y)))))
    ((send (cat self (exp (gen) l))) (recv "end-of-protocol") (send l))
    ((recv
       (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
         (exp (gen) (mul x y))))
      (send
        (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
          (exp (gen) (mul x y)))))
    ((recv (cat (exp (gen) x) l)) (send (cat (exp (gen) x) l)))
    ((recv
       (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
          (exp (gen) (mul x y))))))
  (label 71)
  (parent 66)
  (unrealized (5 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self self-0 name) (y x ltxa ltxb rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (x x) (y y))
  (deflistener
    (hash (exp (gen) (mul y ltxa)) (exp (gen) (mul x ltxb))
      (exp (gen) (mul y x))))
  (defstrand ltx-gen 3 (self self) (l ltxa))
  (defstrand ltx-gen 3 (self self-0) (l ltxb))
  (deflistener
    (cat (exp (gen) (mul y ltxa)) (exp (gen) (mul x ltxb))
      (exp (gen) (mul y x))))
  (deflistener (cat (exp (gen) x) ltxb))
  (defstrand resp 3 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (y y) (x x))
  (deflistener (cat (exp (gen) y) ltxa))
  (precedes ((0 1) (6 1)) ((0 3) (2 1)) ((0 3) (3 1)) ((2 0) (0 0))
    ((2 0) (6 0)) ((3 0) (0 0)) ((3 0) (6 0)) ((3 2) (5 0))
    ((4 1) (1 0)) ((5 1) (4 0)) ((6 2) (0 2)) ((6 2) (7 0))
    ((7 1) (4 0)))
  (uniq-orig na nb)
  (uniq-gen y x ltxa ltxb)
  (absent (y x) (y ltxa) (y ltxb) (x ltxa) (x ltxb))
  (operation nonce-test (added-listener (cat (exp (gen) y) ltxa))
    (exp (gen) (mul y ltxa)) (4 0))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxa)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x)))))) (send nb))
    ((recv
       (hash (exp (gen) (mul y ltxa)) (exp (gen) (mul x ltxb))
         (exp (gen) (mul y x))))
      (send
        (hash (exp (gen) (mul y ltxa)) (exp (gen) (mul x ltxb))
          (exp (gen) (mul y x)))))
    ((send (cat self (exp (gen) ltxa))) (recv "end-of-protocol")
      (send ltxa))
    ((send (cat self-0 (exp (gen) ltxb))) (recv "end-of-protocol")
      (send ltxb))
    ((recv
       (cat (exp (gen) (mul y ltxa)) (exp (gen) (mul x ltxb))
         (exp (gen) (mul y x))))
      (send
        (cat (exp (gen) (mul y ltxa)) (exp (gen) (mul x ltxb))
          (exp (gen) (mul y x)))))
    ((recv (cat (exp (gen) x) ltxb)) (send (cat (exp (gen) x) ltxb)))
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxa)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x)))))))
    ((recv (cat (exp (gen) y) ltxa)) (send (cat (exp (gen) y) ltxa))))
  (label 72)
  (parent 67)
  (unrealized (4 0) (7 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self self-0 name) (y x ltxa ltxb rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (x x) (y y))
  (deflistener
    (hash (exp (gen) (mul y ltxa)) (exp (gen) (mul x ltxb))
      (exp (gen) (mul y x))))
  (defstrand ltx-gen 3 (self self) (l ltxa))
  (defstrand ltx-gen 3 (self self-0) (l ltxb))
  (deflistener
    (cat (exp (gen) (mul y ltxa)) (exp (gen) (mul x ltxb))
      (exp (gen) (mul y x))))
  (deflistener (cat (exp (gen) x) ltxb))
  (defstrand resp 3 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb ltxb)
    (y y) (x x))
  (deflistener (cat (exp (gen) ltxa) y))
  (precedes ((0 1) (6 1)) ((0 3) (2 1)) ((0 3) (3 1)) ((2 0) (0 0))
    ((2 0) (6 0)) ((3 0) (0 0)) ((3 0) (6 0)) ((3 2) (5 0))
    ((4 1) (1 0)) ((5 1) (4 0)) ((6 2) (0 2)) ((6 2) (7 0))
    ((7 1) (4 0)))
  (uniq-orig na nb)
  (uniq-gen y x ltxa ltxb)
  (absent (y x) (y ltxa) (y ltxb) (x ltxa) (x ltxb))
  (operation nonce-test (added-listener (cat (exp (gen) ltxa) y))
    (exp (gen) (mul y ltxa)) (4 0))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxa)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x)))))) (send nb))
    ((recv
       (hash (exp (gen) (mul y ltxa)) (exp (gen) (mul x ltxb))
         (exp (gen) (mul y x))))
      (send
        (hash (exp (gen) (mul y ltxa)) (exp (gen) (mul x ltxb))
          (exp (gen) (mul y x)))))
    ((send (cat self (exp (gen) ltxa))) (recv "end-of-protocol")
      (send ltxa))
    ((send (cat self-0 (exp (gen) ltxb))) (recv "end-of-protocol")
      (send ltxb))
    ((recv
       (cat (exp (gen) (mul y ltxa)) (exp (gen) (mul x ltxb))
         (exp (gen) (mul y x))))
      (send
        (cat (exp (gen) (mul y ltxa)) (exp (gen) (mul x ltxb))
          (exp (gen) (mul y x)))))
    ((recv (cat (exp (gen) x) ltxb)) (send (cat (exp (gen) x) ltxb)))
    ((recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y ltxa)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x)))))))
    ((recv (cat (exp (gen) ltxa) y)) (send (cat (exp (gen) ltxa) y))))
  (label 73)
  (parent 67)
  (unrealized (7 0))
  (dead)
  (comment "empty cohort"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self self-0 name) (y x l ltxb rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb) (ltxb l)
    (x x) (y (mul y l (rec ltxb))))
  (deflistener
    (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
      (exp (gen) (mul y x l (rec ltxb)))))
  (defstrand ltx-gen 3 (self self) (l ltxb))
  (defstrand ltx-gen 3 (self self-0) (l l))
  (deflistener
    (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
      (exp (gen) (mul y x l (rec ltxb)))))
  (deflistener (cat (exp (gen) x) l))
  (defstrand resp 3 (na na) (nb nb) (a a) (b b) (ltxa l) (ltxb ltxb)
    (y y) (x (mul x l (rec ltxb))))
  (deflistener (cat (exp (gen) (mul x l)) ltxb))
  (precedes ((0 1) (7 0)) ((0 3) (2 1)) ((0 3) (3 1)) ((2 0) (0 0))
    ((2 0) (6 0)) ((3 0) (0 0)) ((3 0) (6 0)) ((3 2) (5 0))
    ((4 1) (1 0)) ((5 1) (4 0)) ((6 2) (0 2)) ((7 1) (6 1)))
  (uniq-orig na nb)
  (uniq-gen y x l ltxb)
  (absent (y (mul x l (rec ltxb))) (y l) (y ltxb) (x l) (x ltxb))
  (operation nonce-test
    (added-listener (cat (exp (gen) (mul x l)) ltxb))
    (exp (gen) (mul x l (rec ltxb))) (6 1))
  (traces
    ((recv (cat (exp (gen) ltxb) (exp (gen) l)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul y l (rec ltxb)))
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
              (exp (gen) (mul y x l (rec ltxb))))))) (send nb))
    ((recv
       (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
         (exp (gen) (mul y x l (rec ltxb)))))
      (send
        (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
          (exp (gen) (mul y x l (rec ltxb))))))
    ((send (cat self (exp (gen) ltxb))) (recv "end-of-protocol")
      (send ltxb))
    ((send (cat self-0 (exp (gen) l))) (recv "end-of-protocol")
      (send l))
    ((recv
       (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
         (exp (gen) (mul y x l (rec ltxb)))))
      (send
        (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
          (exp (gen) (mul y x l (rec ltxb))))))
    ((recv (cat (exp (gen) x) l)) (send (cat (exp (gen) x) l)))
    ((recv (cat (exp (gen) l) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) (mul x l (rec ltxb)))))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
              (exp (gen) (mul y x l (rec ltxb))))))))
    ((recv (cat (exp (gen) (mul x l)) ltxb))
      (send (cat (exp (gen) (mul x l)) ltxb))))
  (label 74)
  (parent 68)
  (unrealized (0 2) (4 0) (7 0))
  (dead)
  (comment "empty cohort"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self self-0 name) (y x l ltxb rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb) (ltxb l)
    (x x) (y (mul y l (rec ltxb))))
  (deflistener
    (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
      (exp (gen) (mul y x l (rec ltxb)))))
  (defstrand ltx-gen 3 (self self) (l ltxb))
  (defstrand ltx-gen 3 (self self-0) (l l))
  (deflistener
    (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
      (exp (gen) (mul y x l (rec ltxb)))))
  (deflistener (cat (exp (gen) x) l))
  (defstrand resp 3 (na na) (nb nb) (a a) (b b) (ltxa l) (ltxb ltxb)
    (y y) (x (mul x l (rec ltxb))))
  (deflistener (cat (exp (gen) (mul x (rec ltxb))) l))
  (precedes ((0 1) (7 0)) ((0 3) (2 1)) ((0 3) (3 1)) ((2 0) (0 0))
    ((2 0) (6 0)) ((3 0) (0 0)) ((3 0) (6 0)) ((3 2) (5 0))
    ((4 1) (1 0)) ((5 1) (4 0)) ((6 2) (0 2)) ((7 1) (6 1)))
  (uniq-orig na nb)
  (uniq-gen y x l ltxb)
  (absent (y (mul x l (rec ltxb))) (y l) (y ltxb) (x l) (x ltxb))
  (operation nonce-test
    (added-listener (cat (exp (gen) (mul x (rec ltxb))) l))
    (exp (gen) (mul x l (rec ltxb))) (6 1))
  (traces
    ((recv (cat (exp (gen) ltxb) (exp (gen) l)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul y l (rec ltxb)))
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
              (exp (gen) (mul y x l (rec ltxb))))))) (send nb))
    ((recv
       (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
         (exp (gen) (mul y x l (rec ltxb)))))
      (send
        (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
          (exp (gen) (mul y x l (rec ltxb))))))
    ((send (cat self (exp (gen) ltxb))) (recv "end-of-protocol")
      (send ltxb))
    ((send (cat self-0 (exp (gen) l))) (recv "end-of-protocol")
      (send l))
    ((recv
       (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
         (exp (gen) (mul y x l (rec ltxb)))))
      (send
        (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
          (exp (gen) (mul y x l (rec ltxb))))))
    ((recv (cat (exp (gen) x) l)) (send (cat (exp (gen) x) l)))
    ((recv (cat (exp (gen) l) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) (mul x l (rec ltxb)))))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
              (exp (gen) (mul y x l (rec ltxb))))))))
    ((recv (cat (exp (gen) (mul x (rec ltxb))) l))
      (send (cat (exp (gen) (mul x (rec ltxb))) l))))
  (label 75)
  (parent 68)
  (unrealized (0 2) (4 0) (7 0))
  (dead)
  (comment "empty cohort"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self self-0 name) (y x l ltxb rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxb) (ltxb l)
    (x x) (y (mul y l (rec ltxb))))
  (deflistener
    (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
      (exp (gen) (mul y x l (rec ltxb)))))
  (defstrand ltx-gen 3 (self self) (l ltxb))
  (defstrand ltx-gen 3 (self self-0) (l l))
  (deflistener
    (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
      (exp (gen) (mul y x l (rec ltxb)))))
  (deflistener (cat (exp (gen) x) l))
  (defstrand resp 3 (na na) (nb nb) (a a) (b b) (ltxa l) (ltxb ltxb)
    (y y) (x (mul x l (rec ltxb))))
  (deflistener (cat (exp (gen) (mul l (rec ltxb))) x))
  (precedes ((0 1) (7 0)) ((0 3) (2 1)) ((0 3) (3 1)) ((2 0) (0 0))
    ((2 0) (6 0)) ((3 0) (0 0)) ((3 0) (6 0)) ((3 2) (5 0))
    ((4 1) (1 0)) ((5 1) (4 0)) ((6 2) (0 2)) ((7 1) (6 1)))
  (uniq-orig na nb)
  (uniq-gen y x l ltxb)
  (absent (y (mul x l (rec ltxb))) (y l) (y ltxb) (x l) (x ltxb))
  (operation nonce-test
    (added-listener (cat (exp (gen) (mul l (rec ltxb))) x))
    (exp (gen) (mul x l (rec ltxb))) (6 1))
  (traces
    ((recv (cat (exp (gen) ltxb) (exp (gen) l)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul y l (rec ltxb)))
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
              (exp (gen) (mul y x l (rec ltxb))))))) (send nb))
    ((recv
       (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
         (exp (gen) (mul y x l (rec ltxb)))))
      (send
        (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
          (exp (gen) (mul y x l (rec ltxb))))))
    ((send (cat self (exp (gen) ltxb))) (recv "end-of-protocol")
      (send ltxb))
    ((send (cat self-0 (exp (gen) l))) (recv "end-of-protocol")
      (send l))
    ((recv
       (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
         (exp (gen) (mul y x l (rec ltxb)))))
      (send
        (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
          (exp (gen) (mul y x l (rec ltxb))))))
    ((recv (cat (exp (gen) x) l)) (send (cat (exp (gen) x) l)))
    ((recv (cat (exp (gen) l) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) (mul x l (rec ltxb)))))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
              (exp (gen) (mul y x l (rec ltxb))))))))
    ((recv (cat (exp (gen) (mul l (rec ltxb))) x))
      (send (cat (exp (gen) (mul l (rec ltxb))) x))))
  (label 76)
  (parent 68)
  (unrealized (0 2) (4 0) (7 0))
  (dead)
  (comment "empty cohort"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self self-0 name) (ltxa x rndx) (y expt)
    (l rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb l)
    (x x) (y y))
  (deflistener
    (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
      (exp (gen) (mul x y))))
  (defstrand ltx-gen 3 (self self) (l ltxa))
  (defstrand ltx-gen 3 (self self-0) (l l))
  (deflistener
    (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
      (exp (gen) (mul x y))))
  (deflistener (cat (exp (gen) x) l))
  (deflistener
    (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
      (exp (gen) (mul x y))))
  (deflistener
    (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
      (exp (gen) (mul x y))))
  (precedes ((0 1) (7 0)) ((0 3) (2 1)) ((0 3) (3 1)) ((2 0) (0 0))
    ((3 0) (0 0)) ((3 2) (5 0)) ((4 1) (1 0)) ((5 1) (4 0))
    ((6 1) (0 2)) ((7 1) (6 0)))
  (uniq-orig na)
  (uniq-gen ltxa x l)
  (absent (x ltxa) (x l))
  (operation encryption-test
    (added-listener
      (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
        (exp (gen) (mul x y))))
    (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
      (exp (gen) (mul x y))) (6 0))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) l)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
              (exp (gen) (mul x y)))))) (send nb))
    ((recv
       (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
          (exp (gen) (mul x y)))))
    ((send (cat self (exp (gen) ltxa))) (recv "end-of-protocol")
      (send ltxa))
    ((send (cat self-0 (exp (gen) l))) (recv "end-of-protocol")
      (send l))
    ((recv
       (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
         (exp (gen) (mul x y))))
      (send
        (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
          (exp (gen) (mul x y)))))
    ((recv (cat (exp (gen) x) l)) (send (cat (exp (gen) x) l)))
    ((recv
       (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
          (exp (gen) (mul x y)))))
    ((recv
       (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
         (exp (gen) (mul x y))))
      (send
        (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
          (exp (gen) (mul x y))))))
  (label 77)
  (parent 69)
  (unrealized (7 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (y x l rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa l) (ltxb l) (x x)
    (y y))
  (deflistener
    (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
      (exp (gen) (mul y x))))
  (defstrand ltx-gen 3 (self self) (l l))
  (deflistener
    (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
      (exp (gen) (mul y x))))
  (deflistener (cat (exp (gen) x) l))
  (defstrand resp 3 (na na) (nb nb) (a a) (b b) (ltxa l) (ltxb l) (y y)
    (x x))
  (deflistener (cat (exp (gen) y) x))
  (precedes ((0 1) (5 1)) ((0 3) (2 1)) ((2 0) (0 0)) ((2 0) (5 0))
    ((2 2) (4 0)) ((3 1) (1 0)) ((4 1) (3 0)) ((5 2) (0 2))
    ((5 2) (6 0)) ((6 1) (3 0)))
  (uniq-orig na nb)
  (uniq-gen y x l)
  (absent (y x) (y l) (x l))
  (operation nonce-test (added-listener (cat (exp (gen) y) x))
    (exp (gen) (mul y x)) (3 0))
  (traces
    ((recv (cat (exp (gen) l) (exp (gen) l)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
              (exp (gen) (mul y x)))))) (send nb))
    ((recv
       (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
         (exp (gen) (mul y x))))
      (send
        (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
          (exp (gen) (mul y x)))))
    ((send (cat self (exp (gen) l))) (recv "end-of-protocol") (send l))
    ((recv
       (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
         (exp (gen) (mul y x))))
      (send
        (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
          (exp (gen) (mul y x)))))
    ((recv (cat (exp (gen) x) l)) (send (cat (exp (gen) x) l)))
    ((recv (cat (exp (gen) l) (exp (gen) l)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
              (exp (gen) (mul y x)))))))
    ((recv (cat (exp (gen) y) x)) (send (cat (exp (gen) y) x))))
  (label 78)
  (parent 70)
  (unrealized (6 0))
  (dead)
  (comment "empty cohort"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (y x l rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa l) (ltxb l) (x x)
    (y y))
  (deflistener
    (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
      (exp (gen) (mul y x))))
  (defstrand ltx-gen 3 (self self) (l l))
  (deflistener
    (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
      (exp (gen) (mul y x))))
  (deflistener (cat (exp (gen) x) l))
  (defstrand resp 3 (na na) (nb nb) (a a) (b b) (ltxa l) (ltxb l) (y y)
    (x x))
  (deflistener (cat (exp (gen) x) y))
  (precedes ((0 1) (5 1)) ((0 3) (2 1)) ((2 0) (0 0)) ((2 0) (5 0))
    ((2 2) (4 0)) ((3 1) (1 0)) ((4 1) (3 0)) ((5 2) (0 2))
    ((5 2) (6 0)) ((6 1) (3 0)))
  (uniq-orig na nb)
  (uniq-gen y x l)
  (absent (y x) (y l) (x l))
  (operation nonce-test (added-listener (cat (exp (gen) x) y))
    (exp (gen) (mul y x)) (3 0))
  (traces
    ((recv (cat (exp (gen) l) (exp (gen) l)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
              (exp (gen) (mul y x)))))) (send nb))
    ((recv
       (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
         (exp (gen) (mul y x))))
      (send
        (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
          (exp (gen) (mul y x)))))
    ((send (cat self (exp (gen) l))) (recv "end-of-protocol") (send l))
    ((recv
       (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
         (exp (gen) (mul y x))))
      (send
        (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
          (exp (gen) (mul y x)))))
    ((recv (cat (exp (gen) x) l)) (send (cat (exp (gen) x) l)))
    ((recv (cat (exp (gen) l) (exp (gen) l)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
              (exp (gen) (mul y x)))))))
    ((recv (cat (exp (gen) x) y)) (send (cat (exp (gen) x) y))))
  (label 79)
  (parent 70)
  (unrealized (6 0))
  (dead)
  (comment "empty cohort"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (x rndx) (y expt) (l rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa l) (ltxb l) (x x)
    (y y))
  (deflistener
    (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
      (exp (gen) (mul x y))))
  (defstrand ltx-gen 3 (self self) (l l))
  (deflistener
    (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
      (exp (gen) (mul x y))))
  (deflistener (cat (exp (gen) x) l))
  (deflistener
    (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
      (exp (gen) (mul x y))))
  (deflistener
    (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
      (exp (gen) (mul x y))))
  (precedes ((0 1) (6 0)) ((0 3) (2 1)) ((2 0) (0 0)) ((2 2) (4 0))
    ((3 1) (1 0)) ((4 1) (3 0)) ((5 1) (0 2)) ((6 1) (5 0)))
  (uniq-orig na)
  (uniq-gen x l)
  (absent (x l))
  (operation encryption-test
    (added-listener
      (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
        (exp (gen) (mul x y))))
    (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
      (exp (gen) (mul x y))) (5 0))
  (traces
    ((recv (cat (exp (gen) l) (exp (gen) l)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
              (exp (gen) (mul x y)))))) (send nb))
    ((recv
       (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
          (exp (gen) (mul x y)))))
    ((send (cat self (exp (gen) l))) (recv "end-of-protocol") (send l))
    ((recv
       (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
         (exp (gen) (mul x y))))
      (send
        (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
          (exp (gen) (mul x y)))))
    ((recv (cat (exp (gen) x) l)) (send (cat (exp (gen) x) l)))
    ((recv
       (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
          (exp (gen) (mul x y)))))
    ((recv
       (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
         (exp (gen) (mul x y))))
      (send
        (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
          (exp (gen) (mul x y))))))
  (label 80)
  (parent 71)
  (unrealized (6 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self self-0 name) (y x ltxb l rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa l) (ltxb ltxb)
    (x x) (y y))
  (deflistener
    (hash (exp (gen) (mul y l)) (exp (gen) (mul x ltxb))
      (exp (gen) (mul y x))))
  (defstrand ltx-gen 3 (self self) (l l))
  (defstrand ltx-gen 3 (self self-0) (l ltxb))
  (deflistener
    (cat (exp (gen) (mul y l)) (exp (gen) (mul x ltxb))
      (exp (gen) (mul y x))))
  (deflistener (cat (exp (gen) x) ltxb))
  (defstrand resp 3 (na na) (nb nb) (a a) (b b) (ltxa l) (ltxb ltxb)
    (y y) (x x))
  (deflistener (cat (exp (gen) y) l))
  (precedes ((0 1) (6 1)) ((0 3) (2 1)) ((0 3) (3 1)) ((2 0) (0 0))
    ((2 0) (6 0)) ((2 2) (7 0)) ((3 0) (0 0)) ((3 0) (6 0))
    ((3 2) (5 0)) ((4 1) (1 0)) ((5 1) (4 0)) ((6 2) (0 2))
    ((7 1) (4 0)))
  (uniq-orig na nb)
  (uniq-gen y x ltxb l)
  (absent (y x) (y ltxb) (y l) (x ltxb) (x l))
  (operation nonce-test (displaced 8 2 ltx-gen 3) l (7 0))
  (traces
    ((recv (cat (exp (gen) l) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x)))))) (send nb))
    ((recv
       (hash (exp (gen) (mul y l)) (exp (gen) (mul x ltxb))
         (exp (gen) (mul y x))))
      (send
        (hash (exp (gen) (mul y l)) (exp (gen) (mul x ltxb))
          (exp (gen) (mul y x)))))
    ((send (cat self (exp (gen) l))) (recv "end-of-protocol") (send l))
    ((send (cat self-0 (exp (gen) ltxb))) (recv "end-of-protocol")
      (send ltxb))
    ((recv
       (cat (exp (gen) (mul y l)) (exp (gen) (mul x ltxb))
         (exp (gen) (mul y x))))
      (send
        (cat (exp (gen) (mul y l)) (exp (gen) (mul x ltxb))
          (exp (gen) (mul y x)))))
    ((recv (cat (exp (gen) x) ltxb)) (send (cat (exp (gen) x) ltxb)))
    ((recv (cat (exp (gen) l) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x)))))))
    ((recv (cat (exp (gen) y) l)) (send (cat (exp (gen) y) l))))
  (label 81)
  (parent 72)
  (unrealized (4 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self self-0 name) (ltxa x rndx) (y expt)
    (l rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb l)
    (x x) (y y))
  (deflistener
    (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
      (exp (gen) (mul x y))))
  (defstrand ltx-gen 3 (self self) (l ltxa))
  (defstrand ltx-gen 3 (self self-0) (l l))
  (deflistener
    (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
      (exp (gen) (mul x y))))
  (deflistener (cat (exp (gen) x) l))
  (deflistener
    (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
      (exp (gen) (mul x y))))
  (deflistener
    (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
      (exp (gen) (mul x y))))
  (deflistener (cat (exp (gen) x) l))
  (precedes ((0 1) (8 0)) ((0 3) (2 1)) ((0 3) (3 1)) ((2 0) (0 0))
    ((3 0) (0 0)) ((3 2) (5 0)) ((4 1) (1 0)) ((5 1) (4 0))
    ((6 1) (0 2)) ((7 1) (6 0)) ((8 1) (7 0)))
  (uniq-orig na)
  (uniq-gen ltxa x l)
  (absent (x ltxa) (x l))
  (operation nonce-test (added-listener (cat (exp (gen) x) l))
    (exp (gen) (mul x l)) (7 0))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) l)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
              (exp (gen) (mul x y)))))) (send nb))
    ((recv
       (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
          (exp (gen) (mul x y)))))
    ((send (cat self (exp (gen) ltxa))) (recv "end-of-protocol")
      (send ltxa))
    ((send (cat self-0 (exp (gen) l))) (recv "end-of-protocol")
      (send l))
    ((recv
       (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
         (exp (gen) (mul x y))))
      (send
        (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
          (exp (gen) (mul x y)))))
    ((recv (cat (exp (gen) x) l)) (send (cat (exp (gen) x) l)))
    ((recv
       (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
          (exp (gen) (mul x y)))))
    ((recv
       (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
         (exp (gen) (mul x y))))
      (send
        (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
          (exp (gen) (mul x y)))))
    ((recv (cat (exp (gen) x) l)) (send (cat (exp (gen) x) l))))
  (label 82)
  (parent 77)
  (unrealized (8 0))
  (dead)
  (comment "empty cohort"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self self-0 name) (ltxa x rndx) (y expt)
    (l rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa ltxa) (ltxb l)
    (x x) (y y))
  (deflistener
    (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
      (exp (gen) (mul x y))))
  (defstrand ltx-gen 3 (self self) (l ltxa))
  (defstrand ltx-gen 3 (self self-0) (l l))
  (deflistener
    (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
      (exp (gen) (mul x y))))
  (deflistener (cat (exp (gen) x) l))
  (deflistener
    (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
      (exp (gen) (mul x y))))
  (deflistener
    (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
      (exp (gen) (mul x y))))
  (deflistener (cat (exp (gen) l) x))
  (precedes ((0 1) (8 0)) ((0 3) (2 1)) ((0 3) (3 1)) ((2 0) (0 0))
    ((3 0) (0 0)) ((3 2) (5 0)) ((4 1) (1 0)) ((5 1) (4 0))
    ((6 1) (0 2)) ((7 1) (6 0)) ((8 1) (7 0)))
  (uniq-orig na)
  (uniq-gen ltxa x l)
  (absent (x ltxa) (x l))
  (operation nonce-test (added-listener (cat (exp (gen) l) x))
    (exp (gen) (mul x l)) (7 0))
  (traces
    ((recv (cat (exp (gen) ltxa) (exp (gen) l)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
              (exp (gen) (mul x y)))))) (send nb))
    ((recv
       (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
          (exp (gen) (mul x y)))))
    ((send (cat self (exp (gen) ltxa))) (recv "end-of-protocol")
      (send ltxa))
    ((send (cat self-0 (exp (gen) l))) (recv "end-of-protocol")
      (send l))
    ((recv
       (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
         (exp (gen) (mul x y))))
      (send
        (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
          (exp (gen) (mul x y)))))
    ((recv (cat (exp (gen) x) l)) (send (cat (exp (gen) x) l)))
    ((recv
       (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
          (exp (gen) (mul x y)))))
    ((recv
       (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
         (exp (gen) (mul x y))))
      (send
        (cat (exp (gen) (mul ltxa y)) (exp (gen) (mul x l))
          (exp (gen) (mul x y)))))
    ((recv (cat (exp (gen) l) x)) (send (cat (exp (gen) l) x))))
  (label 83)
  (parent 77)
  (unrealized (8 0))
  (dead)
  (comment "empty cohort"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (x rndx) (y expt) (l rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa l) (ltxb l) (x x)
    (y y))
  (deflistener
    (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
      (exp (gen) (mul x y))))
  (defstrand ltx-gen 3 (self self) (l l))
  (deflistener
    (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
      (exp (gen) (mul x y))))
  (deflistener (cat (exp (gen) x) l))
  (deflistener
    (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
      (exp (gen) (mul x y))))
  (deflistener
    (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
      (exp (gen) (mul x y))))
  (deflistener (cat (exp (gen) x) l))
  (precedes ((0 1) (7 0)) ((0 3) (2 1)) ((2 0) (0 0)) ((2 2) (4 0))
    ((3 1) (1 0)) ((4 1) (3 0)) ((5 1) (0 2)) ((6 1) (5 0))
    ((7 1) (6 0)))
  (uniq-orig na)
  (uniq-gen x l)
  (absent (x l))
  (operation nonce-test (added-listener (cat (exp (gen) x) l))
    (exp (gen) (mul x l)) (6 0))
  (traces
    ((recv (cat (exp (gen) l) (exp (gen) l)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
              (exp (gen) (mul x y)))))) (send nb))
    ((recv
       (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
          (exp (gen) (mul x y)))))
    ((send (cat self (exp (gen) l))) (recv "end-of-protocol") (send l))
    ((recv
       (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
         (exp (gen) (mul x y))))
      (send
        (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
          (exp (gen) (mul x y)))))
    ((recv (cat (exp (gen) x) l)) (send (cat (exp (gen) x) l)))
    ((recv
       (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
          (exp (gen) (mul x y)))))
    ((recv
       (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
         (exp (gen) (mul x y))))
      (send
        (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
          (exp (gen) (mul x y)))))
    ((recv (cat (exp (gen) x) l)) (send (cat (exp (gen) x) l))))
  (label 84)
  (parent 80)
  (unrealized (7 0))
  (dead)
  (comment "empty cohort"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self name) (x rndx) (y expt) (l rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa l) (ltxb l) (x x)
    (y y))
  (deflistener
    (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
      (exp (gen) (mul x y))))
  (defstrand ltx-gen 3 (self self) (l l))
  (deflistener
    (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
      (exp (gen) (mul x y))))
  (deflistener (cat (exp (gen) x) l))
  (deflistener
    (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
      (exp (gen) (mul x y))))
  (deflistener
    (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
      (exp (gen) (mul x y))))
  (deflistener (cat (exp (gen) l) x))
  (precedes ((0 1) (7 0)) ((0 3) (2 1)) ((2 0) (0 0)) ((2 2) (4 0))
    ((3 1) (1 0)) ((4 1) (3 0)) ((5 1) (0 2)) ((6 1) (5 0))
    ((7 1) (6 0)))
  (uniq-orig na)
  (uniq-gen x l)
  (absent (x l))
  (operation nonce-test (added-listener (cat (exp (gen) l) x))
    (exp (gen) (mul x l)) (6 0))
  (traces
    ((recv (cat (exp (gen) l) (exp (gen) l)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
              (exp (gen) (mul x y)))))) (send nb))
    ((recv
       (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
          (exp (gen) (mul x y)))))
    ((send (cat self (exp (gen) l))) (recv "end-of-protocol") (send l))
    ((recv
       (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
         (exp (gen) (mul x y))))
      (send
        (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
          (exp (gen) (mul x y)))))
    ((recv (cat (exp (gen) x) l)) (send (cat (exp (gen) x) l)))
    ((recv
       (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
         (exp (gen) (mul x y))))
      (send
        (hash (exp (gen) (mul y l)) (exp (gen) (mul x l))
          (exp (gen) (mul x y)))))
    ((recv
       (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
         (exp (gen) (mul x y))))
      (send
        (cat (exp (gen) (mul y l)) (exp (gen) (mul x l))
          (exp (gen) (mul x y)))))
    ((recv (cat (exp (gen) l) x)) (send (cat (exp (gen) l) x))))
  (label 85)
  (parent 80)
  (unrealized (7 0))
  (dead)
  (comment "empty cohort"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self self-0 name) (y x ltxb l rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa l) (ltxb ltxb)
    (x x) (y y))
  (deflistener
    (hash (exp (gen) (mul y l)) (exp (gen) (mul x ltxb))
      (exp (gen) (mul y x))))
  (defstrand ltx-gen 3 (self self) (l l))
  (defstrand ltx-gen 3 (self self-0) (l ltxb))
  (deflistener
    (cat (exp (gen) (mul y l)) (exp (gen) (mul x ltxb))
      (exp (gen) (mul y x))))
  (deflistener (cat (exp (gen) x) ltxb))
  (defstrand resp 3 (na na) (nb nb) (a a) (b b) (ltxa l) (ltxb ltxb)
    (y y) (x x))
  (deflistener (cat (exp (gen) y) l))
  (deflistener (cat (exp (gen) y) x))
  (precedes ((0 1) (6 1)) ((0 3) (2 1)) ((0 3) (3 1)) ((2 0) (0 0))
    ((2 0) (6 0)) ((2 2) (7 0)) ((3 0) (0 0)) ((3 0) (6 0))
    ((3 2) (5 0)) ((4 1) (1 0)) ((5 1) (4 0)) ((6 2) (0 2))
    ((6 2) (8 0)) ((7 1) (4 0)) ((8 1) (4 0)))
  (uniq-orig na nb)
  (uniq-gen y x ltxb l)
  (absent (y x) (y ltxb) (y l) (x ltxb) (x l))
  (operation nonce-test (added-listener (cat (exp (gen) y) x))
    (exp (gen) (mul y x)) (4 0))
  (traces
    ((recv (cat (exp (gen) l) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x)))))) (send nb))
    ((recv
       (hash (exp (gen) (mul y l)) (exp (gen) (mul x ltxb))
         (exp (gen) (mul y x))))
      (send
        (hash (exp (gen) (mul y l)) (exp (gen) (mul x ltxb))
          (exp (gen) (mul y x)))))
    ((send (cat self (exp (gen) l))) (recv "end-of-protocol") (send l))
    ((send (cat self-0 (exp (gen) ltxb))) (recv "end-of-protocol")
      (send ltxb))
    ((recv
       (cat (exp (gen) (mul y l)) (exp (gen) (mul x ltxb))
         (exp (gen) (mul y x))))
      (send
        (cat (exp (gen) (mul y l)) (exp (gen) (mul x ltxb))
          (exp (gen) (mul y x)))))
    ((recv (cat (exp (gen) x) ltxb)) (send (cat (exp (gen) x) ltxb)))
    ((recv (cat (exp (gen) l) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x)))))))
    ((recv (cat (exp (gen) y) l)) (send (cat (exp (gen) y) l)))
    ((recv (cat (exp (gen) y) x)) (send (cat (exp (gen) y) x))))
  (label 86)
  (parent 81)
  (unrealized (8 0))
  (dead)
  (comment "empty cohort"))

(defskeleton dhcr-um3
  (vars (na nb data) (a b self self-0 name) (y x ltxb l rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (ltxa l) (ltxb ltxb)
    (x x) (y y))
  (deflistener
    (hash (exp (gen) (mul y l)) (exp (gen) (mul x ltxb))
      (exp (gen) (mul y x))))
  (defstrand ltx-gen 3 (self self) (l l))
  (defstrand ltx-gen 3 (self self-0) (l ltxb))
  (deflistener
    (cat (exp (gen) (mul y l)) (exp (gen) (mul x ltxb))
      (exp (gen) (mul y x))))
  (deflistener (cat (exp (gen) x) ltxb))
  (defstrand resp 3 (na na) (nb nb) (a a) (b b) (ltxa l) (ltxb ltxb)
    (y y) (x x))
  (deflistener (cat (exp (gen) y) l))
  (deflistener (cat (exp (gen) x) y))
  (precedes ((0 1) (6 1)) ((0 3) (2 1)) ((0 3) (3 1)) ((2 0) (0 0))
    ((2 0) (6 0)) ((2 2) (7 0)) ((3 0) (0 0)) ((3 0) (6 0))
    ((3 2) (5 0)) ((4 1) (1 0)) ((5 1) (4 0)) ((6 2) (0 2))
    ((6 2) (8 0)) ((7 1) (4 0)) ((8 1) (4 0)))
  (uniq-orig na nb)
  (uniq-gen y x ltxb l)
  (absent (y x) (y ltxb) (y l) (x ltxb) (x l))
  (operation nonce-test (added-listener (cat (exp (gen) x) y))
    (exp (gen) (mul y x)) (4 0))
  (traces
    ((recv (cat (exp (gen) l) (exp (gen) ltxb)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x)))))) (send nb))
    ((recv
       (hash (exp (gen) (mul y l)) (exp (gen) (mul x ltxb))
         (exp (gen) (mul y x))))
      (send
        (hash (exp (gen) (mul y l)) (exp (gen) (mul x ltxb))
          (exp (gen) (mul y x)))))
    ((send (cat self (exp (gen) l))) (recv "end-of-protocol") (send l))
    ((send (cat self-0 (exp (gen) ltxb))) (recv "end-of-protocol")
      (send ltxb))
    ((recv
       (cat (exp (gen) (mul y l)) (exp (gen) (mul x ltxb))
         (exp (gen) (mul y x))))
      (send
        (cat (exp (gen) (mul y l)) (exp (gen) (mul x ltxb))
          (exp (gen) (mul y x)))))
    ((recv (cat (exp (gen) x) ltxb)) (send (cat (exp (gen) x) ltxb)))
    ((recv (cat (exp (gen) l) (exp (gen) ltxb)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x ltxb))
              (exp (gen) (mul y x)))))))
    ((recv (cat (exp (gen) y) l)) (send (cat (exp (gen) y) l)))
    ((recv (cat (exp (gen) x) y)) (send (cat (exp (gen) x) y))))
  (label 87)
  (parent 81)
  (unrealized (8 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")
