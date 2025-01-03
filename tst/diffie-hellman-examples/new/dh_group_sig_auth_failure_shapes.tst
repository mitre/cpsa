(comment "CPSA 4.4.4")
(comment "Extracted shapes")

(herald "Signed group DH exchange (version with auth failure)"
  (algebra diffie-hellman) (limit 100))

(comment "CPSA 4.4.4")

(comment "All input read from dh_group_sig_auth_failure.scm")

(comment "Step count limited to 100")

(defprotocol dh_sig diffie-hellman
  (defrole group-init
    (vars (alpha rndx) (group text) (group-dist chan))
    (trace (send group-dist (cat "Group id" group (exp (gen) alpha))))
    (uniq-gen alpha)
    (conf group-dist))
  (defrole init
    (vars (x rndx) (y alpha expt) (group text) (a b name)
      (group-dist chan))
    (trace (recv group-dist (cat "Group id" group (exp (gen) alpha)))
      (send (enc (exp (gen) (mul x alpha)) (privk a)))
      (recv
        (enc (exp (gen) (mul y alpha)) (exp (gen) (mul x alpha))
          (privk b)))
      (send
        (enc "final" (exp (gen) (mul y alpha)) (exp (gen) (mul x alpha))
          (privk a))))
    (uniq-gen x)
    (absent (x alpha))
    (auth group-dist))
  (defrole resp
    (vars (y rndx) (x alpha expt) (group text) (a b name)
      (group-dist chan))
    (trace (recv group-dist (cat "Group id" group (exp (gen) alpha)))
      (recv (enc (exp (gen) (mul x alpha)) (privk a)))
      (send
        (enc (exp (gen) (mul y alpha)) (exp (gen) (mul x alpha))
          (privk b)))
      (recv
        (enc "final" (exp (gen) (mul y alpha)) (exp (gen) (mul x alpha))
          (privk a))))
    (uniq-gen y)
    (absent (y (mul x alpha)) (y alpha))
    (auth group-dist))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton dh_sig
  (vars (group text) (a b name) (group-dist chan) (x rndx)
    (y alpha expt))
  (defstrand init 4 (group group) (a a) (b b) (group-dist group-dist)
    (x x) (y y) (alpha alpha))
  (non-orig (privk a) (privk b))
  (uniq-gen x)
  (absent (x alpha))
  (auth group-dist)
  (traces
    ((recv group-dist (cat "Group id" group (exp (gen) alpha)))
      (send (enc (exp (gen) (mul x alpha)) (privk a)))
      (recv
        (enc (exp (gen) (mul y alpha)) (exp (gen) (mul x alpha))
          (privk b)))
      (send
        (enc "final" (exp (gen) (mul y alpha)) (exp (gen) (mul x alpha))
          (privk a)))))
  (label 0)
  (unrealized (0 0) (0 2))
  (origs)
  (ugens (x (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dh_sig
  (vars (group text) (a b a-0 name) (group-dist chan) (y x alpha rndx))
  (defstrand init 4 (group group) (a a) (b b) (group-dist group-dist)
    (x x) (y y) (alpha alpha))
  (defstrand group-init 1 (group group) (group-dist group-dist)
    (alpha alpha))
  (defstrand resp 3 (group group) (a a-0) (b b) (group-dist group-dist)
    (y y) (x x) (alpha alpha))
  (precedes ((0 1) (2 1)) ((1 0) (0 0)) ((1 0) (2 0)) ((2 2) (0 2)))
  (non-orig (privk a) (privk b))
  (uniq-gen y x alpha)
  (absent (y (mul x alpha)) (y alpha) (x alpha))
  (conf group-dist)
  (auth group-dist)
  (operation channel-test (displaced 3 1 group-init 1)
    (ch-msg group-dist-0 (cat "Group id" group-0 (exp (gen) alpha-0)))
    (2 0))
  (strand-map 0 1 2)
  (traces
    ((recv group-dist (cat "Group id" group (exp (gen) alpha)))
      (send (enc (exp (gen) (mul x alpha)) (privk a)))
      (recv
        (enc (exp (gen) (mul y alpha)) (exp (gen) (mul x alpha))
          (privk b)))
      (send
        (enc "final" (exp (gen) (mul y alpha)) (exp (gen) (mul x alpha))
          (privk a))))
    ((send group-dist (cat "Group id" group (exp (gen) alpha))))
    ((recv group-dist (cat "Group id" group (exp (gen) alpha)))
      (recv (enc (exp (gen) (mul x alpha)) (privk a-0)))
      (send
        (enc (exp (gen) (mul y alpha)) (exp (gen) (mul x alpha))
          (privk b)))))
  (label 3)
  (parent 0)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (x x) (y y) (alpha alpha) (group group)
        (group-dist group-dist))))
  (origs)
  (ugens (alpha (1 0)) (y (2 2)) (x (0 1))))

(defskeleton dh_sig
  (vars (group group-0 text) (a b a-0 name)
    (group-dist group-dist-0 chan) (y x alpha alpha-0 rndx))
  (defstrand init 4 (group group) (a a) (b b) (group-dist group-dist)
    (x x) (y (mul y (rec alpha) alpha-0)) (alpha alpha))
  (defstrand group-init 1 (group group) (group-dist group-dist)
    (alpha alpha))
  (defstrand resp 3 (group group-0) (a a-0) (b b)
    (group-dist group-dist-0) (y y) (x (mul x alpha (rec alpha-0)))
    (alpha alpha-0))
  (defstrand group-init 1 (group group-0) (group-dist group-dist-0)
    (alpha alpha-0))
  (precedes ((0 1) (2 1)) ((1 0) (0 0)) ((2 2) (0 2)) ((3 0) (2 0)))
  (non-orig (privk a) (privk b))
  (uniq-gen y x alpha alpha-0)
  (absent (y (mul x alpha)) (y alpha-0) (x alpha))
  (conf group-dist group-dist-0)
  (auth group-dist group-dist-0)
  (operation channel-test (added-strand group-init 1)
    (ch-msg group-dist-0 (cat "Group id" group-0 (exp (gen) alpha-0)))
    (2 0))
  (strand-map 0 1 2)
  (traces
    ((recv group-dist (cat "Group id" group (exp (gen) alpha)))
      (send (enc (exp (gen) (mul x alpha)) (privk a)))
      (recv
        (enc (exp (gen) (mul y alpha-0)) (exp (gen) (mul x alpha))
          (privk b)))
      (send
        (enc "final" (exp (gen) (mul y alpha-0))
          (exp (gen) (mul x alpha)) (privk a))))
    ((send group-dist (cat "Group id" group (exp (gen) alpha))))
    ((recv group-dist-0 (cat "Group id" group-0 (exp (gen) alpha-0)))
      (recv (enc (exp (gen) (mul x alpha)) (privk a-0)))
      (send
        (enc (exp (gen) (mul y alpha-0)) (exp (gen) (mul x alpha))
          (privk b))))
    ((send group-dist-0 (cat "Group id" group-0 (exp (gen) alpha-0)))))
  (label 4)
  (parent 0)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (x x) (y (mul y (rec alpha) alpha-0)) (alpha alpha)
        (group group) (group-dist group-dist))))
  (origs)
  (ugens (alpha-0 (3 0)) (y (2 2)) (alpha (1 0)) (x (0 1))))

(comment "Nothing left to do")

(defprotocol dh_sig diffie-hellman
  (defrole group-init
    (vars (alpha rndx) (group text) (group-dist chan))
    (trace (send group-dist (cat "Group id" group (exp (gen) alpha))))
    (uniq-gen alpha)
    (conf group-dist))
  (defrole init
    (vars (x rndx) (y alpha expt) (group text) (a b name)
      (group-dist chan))
    (trace (recv group-dist (cat "Group id" group (exp (gen) alpha)))
      (send (enc (exp (gen) (mul x alpha)) (privk a)))
      (recv
        (enc (exp (gen) (mul y alpha)) (exp (gen) (mul x alpha))
          (privk b)))
      (send
        (enc "final" (exp (gen) (mul y alpha)) (exp (gen) (mul x alpha))
          (privk a))))
    (uniq-gen x)
    (absent (x alpha))
    (auth group-dist))
  (defrole resp
    (vars (y rndx) (x alpha expt) (group text) (a b name)
      (group-dist chan))
    (trace (recv group-dist (cat "Group id" group (exp (gen) alpha)))
      (recv (enc (exp (gen) (mul x alpha)) (privk a)))
      (send
        (enc (exp (gen) (mul y alpha)) (exp (gen) (mul x alpha))
          (privk b)))
      (recv
        (enc "final" (exp (gen) (mul y alpha)) (exp (gen) (mul x alpha))
          (privk a))))
    (uniq-gen y)
    (absent (y (mul x alpha)) (y alpha))
    (auth group-dist))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton dh_sig
  (vars (group text) (a b name) (group-dist chan) (y rndx)
    (x alpha expt))
  (defstrand resp 4 (group group) (a a) (b b) (group-dist group-dist)
    (y y) (x x) (alpha alpha))
  (non-orig (privk a) (privk b))
  (uniq-gen y)
  (absent (y (mul x alpha)) (y alpha))
  (auth group-dist)
  (traces
    ((recv group-dist (cat "Group id" group (exp (gen) alpha)))
      (recv (enc (exp (gen) (mul x alpha)) (privk a)))
      (send
        (enc (exp (gen) (mul y alpha)) (exp (gen) (mul x alpha))
          (privk b)))
      (recv
        (enc "final" (exp (gen) (mul y alpha)) (exp (gen) (mul x alpha))
          (privk a)))))
  (label 5)
  (unrealized (0 0) (0 1) (0 3))
  (origs)
  (ugens (y (0 2)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dh_sig
  (vars (group text) (a b b-0 name) (group-dist chan) (y alpha x rndx))
  (defstrand resp 4 (group group) (a a) (b b) (group-dist group-dist)
    (y y) (x x) (alpha alpha))
  (defstrand group-init 1 (group group) (group-dist group-dist)
    (alpha alpha))
  (defstrand init 4 (group group) (a a) (b b-0) (group-dist group-dist)
    (x x) (y y) (alpha alpha))
  (precedes ((0 2) (2 2)) ((1 0) (0 0)) ((1 0) (2 0)) ((2 1) (0 1))
    ((2 3) (0 3)))
  (non-orig (privk a) (privk b))
  (uniq-gen y alpha x)
  (absent (y alpha) (y (mul alpha x)) (x alpha))
  (conf group-dist)
  (auth group-dist)
  (operation encryption-test (displaced 2 3 init 4)
    (enc "final" (exp (gen) (mul y alpha)) (exp (gen) (mul x-0 alpha))
      (privk a)) (0 3))
  (strand-map 0 1 2)
  (traces
    ((recv group-dist (cat "Group id" group (exp (gen) alpha)))
      (recv (enc (exp (gen) (mul alpha x)) (privk a)))
      (send
        (enc (exp (gen) (mul y alpha)) (exp (gen) (mul alpha x))
          (privk b)))
      (recv
        (enc "final" (exp (gen) (mul y alpha)) (exp (gen) (mul alpha x))
          (privk a))))
    ((send group-dist (cat "Group id" group (exp (gen) alpha))))
    ((recv group-dist (cat "Group id" group (exp (gen) alpha)))
      (send (enc (exp (gen) (mul alpha x)) (privk a)))
      (recv
        (enc (exp (gen) (mul y alpha)) (exp (gen) (mul alpha x))
          (privk b-0)))
      (send
        (enc "final" (exp (gen) (mul y alpha)) (exp (gen) (mul alpha x))
          (privk a)))))
  (label 10)
  (parent 5)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (y y) (x x) (alpha alpha) (group group)
        (group-dist group-dist))))
  (origs)
  (ugens (x (2 1)) (alpha (1 0)) (y (0 2))))

(defskeleton dh_sig
  (vars (group group-0 text) (a b b-0 name)
    (group-dist group-dist-0 chan) (y alpha alpha-0 x rndx))
  (defstrand resp 4 (group group) (a a) (b b) (group-dist group-dist)
    (y y) (x (mul (rec alpha) alpha-0 x)) (alpha alpha))
  (defstrand group-init 1 (group group) (group-dist group-dist)
    (alpha alpha))
  (defstrand group-init 1 (group group-0) (group-dist group-dist-0)
    (alpha alpha-0))
  (defstrand init 4 (group group-0) (a a) (b b-0)
    (group-dist group-dist-0) (x x) (y (mul y alpha (rec alpha-0)))
    (alpha alpha-0))
  (precedes ((0 2) (3 2)) ((1 0) (0 0)) ((2 0) (3 0)) ((3 1) (0 1))
    ((3 3) (0 3)))
  (non-orig (privk a) (privk b))
  (uniq-gen y alpha alpha-0 x)
  (absent (y alpha) (y (mul alpha-0 x)) (x alpha-0))
  (conf group-dist group-dist-0)
  (auth group-dist group-dist-0)
  (operation encryption-test (displaced 2 4 init 4)
    (enc "final" (exp (gen) (mul y alpha)) (exp (gen) (mul x-0 alpha-0))
      (privk a)) (0 3))
  (strand-map 0 1 3 2)
  (traces
    ((recv group-dist (cat "Group id" group (exp (gen) alpha)))
      (recv (enc (exp (gen) (mul alpha-0 x)) (privk a)))
      (send
        (enc (exp (gen) (mul y alpha)) (exp (gen) (mul alpha-0 x))
          (privk b)))
      (recv
        (enc "final" (exp (gen) (mul y alpha))
          (exp (gen) (mul alpha-0 x)) (privk a))))
    ((send group-dist (cat "Group id" group (exp (gen) alpha))))
    ((send group-dist-0 (cat "Group id" group-0 (exp (gen) alpha-0))))
    ((recv group-dist-0 (cat "Group id" group-0 (exp (gen) alpha-0)))
      (send (enc (exp (gen) (mul alpha-0 x)) (privk a)))
      (recv
        (enc (exp (gen) (mul y alpha)) (exp (gen) (mul alpha-0 x))
          (privk b-0)))
      (send
        (enc "final" (exp (gen) (mul y alpha))
          (exp (gen) (mul alpha-0 x)) (privk a)))))
  (label 11)
  (parent 5)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (y y) (x (mul (rec alpha) alpha-0 x)) (alpha alpha)
        (group group) (group-dist group-dist))))
  (origs)
  (ugens (x (3 1)) (alpha-0 (2 0)) (alpha (1 0)) (y (0 2))))

(comment "Nothing left to do")
