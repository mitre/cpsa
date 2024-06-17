(comment "CPSA 4.4.4")
(comment "Extracted shapes")

(herald "Signed group DH exchange (improved version)"
  (algebra diffie-hellman) (limit 100))

(comment "CPSA 4.4.4")

(comment "All input read from dh_group_sig.scm")

(comment "Step count limited to 100")

(defprotocol dh_sig diffie-hellman
  (defrole group-init
    (vars (alpha rndx) (group text) (group-dist chan))
    (trace (send group-dist (cat "Group id" group (exp (gen) alpha))))
    (uniq-gen alpha)
    (conf group-dist))
  (defrole init
    (vars (x rndx) (y alpha expt) (group na nb text) (a b name)
      (group-dist chan))
    (trace (recv group-dist (cat "Group id" group (exp (gen) alpha)))
      (send (enc (exp (gen) (mul x alpha)) (privk a)))
      (recv
        (enc a (exp (gen) (mul y alpha)) (exp (gen) (mul x alpha))
          (privk b)))
      (send
        (enc "final" b na (exp (gen) (mul y alpha))
          (exp (gen) (mul x alpha)) (privk a)))
      (recv (enc na nb (exp (gen) (mul x y alpha)))) (send nb))
    (uniq-gen na x)
    (absent (x alpha))
    (auth group-dist))
  (defrole resp
    (vars (y rndx) (x alpha expt) (group na nb text) (a b name)
      (group-dist chan))
    (trace (recv group-dist (cat "Group id" group (exp (gen) alpha)))
      (recv (enc (exp (gen) (mul x alpha)) (privk a)))
      (send
        (enc a (exp (gen) (mul y alpha)) (exp (gen) (mul x alpha))
          (privk b)))
      (recv
        (enc "final" b na (exp (gen) (mul y alpha))
          (exp (gen) (mul x alpha)) (privk a)))
      (send (enc na nb (exp (gen) (mul y x alpha)))) (recv nb))
    (uniq-gen nb y)
    (absent (y (mul x alpha)) (y alpha))
    (auth group-dist))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton dh_sig
  (vars (group na nb text) (a b name) (group-dist chan) (x rndx)
    (y alpha expt))
  (defstrand init 6 (group group) (na na) (nb nb) (a a) (b b)
    (group-dist group-dist) (x x) (y y) (alpha alpha))
  (non-orig (privk a) (privk b))
  (uniq-gen na x)
  (absent (x alpha))
  (auth group-dist)
  (traces
    ((recv group-dist (cat "Group id" group (exp (gen) alpha)))
      (send (enc (exp (gen) (mul x alpha)) (privk a)))
      (recv
        (enc a (exp (gen) (mul y alpha)) (exp (gen) (mul x alpha))
          (privk b)))
      (send
        (enc "final" b na (exp (gen) (mul y alpha))
          (exp (gen) (mul x alpha)) (privk a)))
      (recv (enc na nb (exp (gen) (mul x y alpha)))) (send nb)))
  (label 0)
  (unrealized (0 0) (0 2))
  (origs)
  (ugens (x (0 1)) (na (0 3)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dh_sig
  (vars (na nb group text) (a b name) (group-dist chan)
    (x alpha y rndx))
  (defstrand init 6 (group group) (na na) (nb nb) (a a) (b b)
    (group-dist group-dist) (x x) (y y) (alpha alpha))
  (defstrand group-init 1 (group group) (group-dist group-dist)
    (alpha alpha))
  (defstrand resp 5 (group group) (na na) (nb nb) (a a) (b b)
    (group-dist group-dist) (y y) (x x) (alpha alpha))
  (precedes ((0 1) (2 1)) ((0 3) (2 3)) ((1 0) (0 0)) ((1 0) (2 0))
    ((2 2) (0 2)) ((2 4) (0 4)))
  (non-orig (privk a) (privk b))
  (uniq-gen na nb x alpha y)
  (absent (x alpha) (y (mul x alpha)) (y alpha))
  (conf group-dist)
  (auth group-dist)
  (operation encryption-test (displaced 2 3 resp 5)
    (enc na nb (exp (gen) (mul y-0 x alpha-0))) (0 4))
  (strand-map 0 1 2)
  (traces
    ((recv group-dist (cat "Group id" group (exp (gen) alpha)))
      (send (enc (exp (gen) (mul x alpha)) (privk a)))
      (recv
        (enc a (exp (gen) (mul alpha y)) (exp (gen) (mul x alpha))
          (privk b)))
      (send
        (enc "final" b na (exp (gen) (mul alpha y))
          (exp (gen) (mul x alpha)) (privk a)))
      (recv (enc na nb (exp (gen) (mul x alpha y)))) (send nb))
    ((send group-dist (cat "Group id" group (exp (gen) alpha))))
    ((recv group-dist (cat "Group id" group (exp (gen) alpha)))
      (recv (enc (exp (gen) (mul x alpha)) (privk a)))
      (send
        (enc a (exp (gen) (mul alpha y)) (exp (gen) (mul x alpha))
          (privk b)))
      (recv
        (enc "final" b na (exp (gen) (mul alpha y))
          (exp (gen) (mul x alpha)) (privk a)))
      (send (enc na nb (exp (gen) (mul x alpha y))))))
  (label 5)
  (parent 0)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (x x) (y y) (alpha alpha) (group group) (na na)
        (nb nb) (group-dist group-dist))))
  (origs)
  (ugens (nb (2 4)) (y (2 2)) (alpha (1 0)) (x (0 1)) (na (0 3))))

(comment "Nothing left to do")

(defprotocol dh_sig diffie-hellman
  (defrole group-init
    (vars (alpha rndx) (group text) (group-dist chan))
    (trace (send group-dist (cat "Group id" group (exp (gen) alpha))))
    (uniq-gen alpha)
    (conf group-dist))
  (defrole init
    (vars (x rndx) (y alpha expt) (group na nb text) (a b name)
      (group-dist chan))
    (trace (recv group-dist (cat "Group id" group (exp (gen) alpha)))
      (send (enc (exp (gen) (mul x alpha)) (privk a)))
      (recv
        (enc a (exp (gen) (mul y alpha)) (exp (gen) (mul x alpha))
          (privk b)))
      (send
        (enc "final" b na (exp (gen) (mul y alpha))
          (exp (gen) (mul x alpha)) (privk a)))
      (recv (enc na nb (exp (gen) (mul x y alpha)))) (send nb))
    (uniq-gen na x)
    (absent (x alpha))
    (auth group-dist))
  (defrole resp
    (vars (y rndx) (x alpha expt) (group na nb text) (a b name)
      (group-dist chan))
    (trace (recv group-dist (cat "Group id" group (exp (gen) alpha)))
      (recv (enc (exp (gen) (mul x alpha)) (privk a)))
      (send
        (enc a (exp (gen) (mul y alpha)) (exp (gen) (mul x alpha))
          (privk b)))
      (recv
        (enc "final" b na (exp (gen) (mul y alpha))
          (exp (gen) (mul x alpha)) (privk a)))
      (send (enc na nb (exp (gen) (mul y x alpha)))) (recv nb))
    (uniq-gen nb y)
    (absent (y (mul x alpha)) (y alpha))
    (auth group-dist))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton dh_sig
  (vars (group na nb text) (a b name) (group-dist chan) (y rndx)
    (x alpha expt))
  (defstrand resp 6 (group group) (na na) (nb nb) (a a) (b b)
    (group-dist group-dist) (y y) (x x) (alpha alpha))
  (non-orig (privk a) (privk b))
  (uniq-gen nb y)
  (absent (y (mul x alpha)) (y alpha))
  (auth group-dist)
  (traces
    ((recv group-dist (cat "Group id" group (exp (gen) alpha)))
      (recv (enc (exp (gen) (mul x alpha)) (privk a)))
      (send
        (enc a (exp (gen) (mul y alpha)) (exp (gen) (mul x alpha))
          (privk b)))
      (recv
        (enc "final" b na (exp (gen) (mul y alpha))
          (exp (gen) (mul x alpha)) (privk a)))
      (send (enc na nb (exp (gen) (mul y x alpha)))) (recv nb)))
  (label 14)
  (unrealized (0 0) (0 1) (0 3))
  (origs)
  (ugens (y (0 2)) (nb (0 4)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dh_sig
  (vars (na nb group text) (a b name) (group-dist chan)
    (y alpha x rndx))
  (defstrand resp 6 (group group) (na na) (nb nb) (a a) (b b)
    (group-dist group-dist) (y y) (x x) (alpha alpha))
  (defstrand group-init 1 (group group) (group-dist group-dist)
    (alpha alpha))
  (defstrand init 6 (group group) (na na) (nb nb) (a a) (b b)
    (group-dist group-dist) (x x) (y y) (alpha alpha))
  (precedes ((0 2) (2 2)) ((0 4) (2 4)) ((1 0) (0 0)) ((1 0) (2 0))
    ((2 1) (0 1)) ((2 3) (0 3)) ((2 5) (0 5)))
  (non-orig (privk a) (privk b))
  (uniq-gen na nb y alpha x)
  (absent (y alpha) (y (mul alpha x)) (x alpha))
  (conf group-dist)
  (auth group-dist)
  (operation nonce-test (displaced 2 3 init 6) nb (0 5)
    (enc na nb (exp (gen) (mul y alpha-0 x-0))))
  (strand-map 0 1 2)
  (traces
    ((recv group-dist (cat "Group id" group (exp (gen) alpha)))
      (recv (enc (exp (gen) (mul alpha x)) (privk a)))
      (send
        (enc a (exp (gen) (mul y alpha)) (exp (gen) (mul alpha x))
          (privk b)))
      (recv
        (enc "final" b na (exp (gen) (mul y alpha))
          (exp (gen) (mul alpha x)) (privk a)))
      (send (enc na nb (exp (gen) (mul y alpha x)))) (recv nb))
    ((send group-dist (cat "Group id" group (exp (gen) alpha))))
    ((recv group-dist (cat "Group id" group (exp (gen) alpha)))
      (send (enc (exp (gen) (mul alpha x)) (privk a)))
      (recv
        (enc a (exp (gen) (mul y alpha)) (exp (gen) (mul alpha x))
          (privk b)))
      (send
        (enc "final" b na (exp (gen) (mul y alpha))
          (exp (gen) (mul alpha x)) (privk a)))
      (recv (enc na nb (exp (gen) (mul y alpha x)))) (send nb)))
  (label 21)
  (parent 14)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (y y) (x x) (alpha alpha) (group group) (na na)
        (nb nb) (group-dist group-dist))))
  (origs)
  (ugens (na (2 3)) (x (2 1)) (alpha (1 0)) (y (0 2)) (nb (0 4))))

(comment "Nothing left to do")
