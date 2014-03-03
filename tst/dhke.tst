(herald "Diffie-Hellman Key Exchange" (algebra diffie-hellman))

(comment "CPSA 2.3.4")
(comment "All input read from dhke.lsp")

(defprotocol dhke diffie-hellman
  (defrole init
    (vars (a b name) (h base) (x expn))
    (trace (send (enc "i" (exp (gen) x) (privk a)))
      (recv (cat (enc h (privk b)) (enc a b (exp h x))))
      (send (enc "i" a b (exp h x))))
    (non-orig x)
    (uniq-orig (exp (gen) x)))
  (defrole resp
    (vars (a b name) (h base) (x expn))
    (trace (recv (enc "i" h (privk a)))
      (send (cat (enc (exp (gen) x) (privk b)) (enc a b (exp h x))))
      (recv (enc "i" a b (exp h x))))
    (non-orig x)
    (uniq-orig (exp (gen) x))))

(defskeleton dhke
  (vars (a b name) (h base) (x expn))
  (defstrand resp 3 (a a) (b b) (h h) (x x))
  (non-orig (privk a) (privk b) x)
  (uniq-orig (exp (gen) x))
  (traces
    ((recv (enc "i" h (privk a)))
      (send (cat (enc (exp (gen) x) (privk b)) (enc a b (exp h x))))
      (recv (enc "i" a b (exp h x)))))
  (label 0)
  (unrealized (0 0) (0 2))
  (origs ((exp (gen) x) (0 1)))
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol dhke diffie-hellman
  (defrole init
    (vars (a b name) (h base) (x expn))
    (trace (send (enc "i" (exp (gen) x) (privk a)))
      (recv (cat (enc h (privk b)) (enc a b (exp h x))))
      (send (enc "i" a b (exp h x))))
    (non-orig x)
    (uniq-orig (exp (gen) x)))
  (defrole resp
    (vars (a b name) (h base) (x expn))
    (trace (recv (enc "i" h (privk a)))
      (send (cat (enc (exp (gen) x) (privk b)) (enc a b (exp h x))))
      (recv (enc "i" a b (exp h x))))
    (non-orig x)
    (uniq-orig (exp (gen) x))))

(defskeleton dhke
  (vars (a b name) (h base) (x expn))
  (defstrand init 2 (a a) (b b) (h h) (x x))
  (non-orig (privk a) (privk b) x)
  (uniq-orig (exp (gen) x))
  (traces
    ((send (enc "i" (exp (gen) x) (privk a)))
      (recv (cat (enc h (privk b)) (enc a b (exp h x))))))
  (label 1)
  (unrealized (0 1))
  (origs ((exp (gen) x) (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dhke
  (vars (a b a-0 name) (h base) (x x-0 expn))
  (defstrand init 2 (a a) (b b) (h (exp (gen) x-0)) (x x))
  (defstrand resp 2 (a a-0) (b b) (h h) (x x-0))
  (precedes ((1 1) (0 1)))
  (non-orig (privk a) (privk b) x x-0)
  (uniq-orig (exp (gen) x) (exp (gen) x-0))
  (operation encryption-test (added-strand resp 2)
    (enc (exp (gen) x-0) (privk b)) (0 1))
  (traces
    ((send (enc "i" (exp (gen) x) (privk a)))
      (recv
        (cat (enc (exp (gen) x-0) (privk b))
          (enc a b (exp (gen) (mul x x-0))))))
    ((recv (enc "i" h (privk a-0)))
      (send
        (cat (enc (exp (gen) x-0) (privk b)) (enc a-0 b (exp h x-0))))))
  (label 2)
  (parent 1)
  (unrealized (0 1))
  (comment "3 in cohort - 3 not yet seen"))

(defskeleton dhke
  (vars (b a name) (x x-0 expn))
  (defstrand init 2 (a a) (b b) (h (exp (gen) x-0)) (x x))
  (defstrand resp 2 (a a) (b b) (h (exp (gen) x)) (x x-0))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk b) (privk a) x x-0)
  (uniq-orig (exp (gen) x) (exp (gen) x-0))
  (operation encryption-test (displaced 2 1 resp 2)
    (enc a-0 b (exp (gen) (mul x x-1))) (0 1))
  (traces
    ((send (enc "i" (exp (gen) x) (privk a)))
      (recv
        (cat (enc (exp (gen) x-0) (privk b))
          (enc a b (exp (gen) (mul x x-0))))))
    ((recv (enc "i" (exp (gen) x) (privk a)))
      (send
        (cat (enc (exp (gen) x-0) (privk b))
          (enc a b (exp (gen) (mul x x-0)))))))
  (label 3)
  (parent 2)
  (unrealized)
  (shape)
  (maps ((0) ((a a) (b b) (h (exp (gen) x-0)) (x x))))
  (origs ((exp (gen) x-0) (1 1)) ((exp (gen) x) (0 0))))

(defskeleton dhke
  (vars (a b a-0 name) (h base) (x x-0 x-1 expn))
  (defstrand init 2 (a a) (b b) (h (exp (gen) x-0)) (x x))
  (defstrand resp 2 (a a-0) (b b) (h h) (x x-0))
  (defstrand resp 2 (a a) (b b) (h (exp (gen) (mul x x-0 (rec x-1))))
    (x x-1))
  (precedes ((1 1) (0 1)) ((2 1) (0 1)))
  (non-orig (privk a) (privk b) x x-0 x-1)
  (uniq-orig (exp (gen) x) (exp (gen) x-0) (exp (gen) x-1))
  (operation encryption-test (added-strand resp 2)
    (enc a b (exp (gen) (mul x x-0))) (0 1))
  (traces
    ((send (enc "i" (exp (gen) x) (privk a)))
      (recv
        (cat (enc (exp (gen) x-0) (privk b))
          (enc a b (exp (gen) (mul x x-0))))))
    ((recv (enc "i" h (privk a-0)))
      (send
        (cat (enc (exp (gen) x-0) (privk b)) (enc a-0 b (exp h x-0)))))
    ((recv (enc "i" (exp (gen) (mul x x-0 (rec x-1))) (privk a)))
      (send
        (cat (enc (exp (gen) x-1) (privk b))
          (enc a b (exp (gen) (mul x x-0)))))))
  (label 4)
  (parent 2)
  (unrealized (2 0))
  (comment "empty cohort"))

(defskeleton dhke
  (vars (a b a-0 name) (h base) (x x-0 x-1 x-2 expn))
  (defstrand init 2 (a a) (b b) (h (exp (gen) x-0)) (x x))
  (defstrand resp 2 (a a-0) (b b) (h h) (x x-0))
  (deflistener (exp (gen) (mul x x-0)))
  (precedes ((1 1) (0 1)) ((2 1) (0 1)))
  (non-orig (privk a) (privk b) x x-0)
  (uniq-orig (exp (gen) x) (exp (gen) x-0))
  (operation encryption-test (added-listener (exp (gen) (mul x x-0)))
    (enc a b (exp (gen) (mul x x-0))) (0 1))
  (traces
    ((send (enc "i" (exp (gen) x) (privk a)))
      (recv
        (cat (enc (exp (gen) x-0) (privk b))
          (enc a b (exp (gen) (mul x x-0))))))
    ((recv (enc "i" h (privk a-0)))
      (send
        (cat (enc (exp (gen) x-0) (privk b)) (enc a-0 b (exp h x-0)))))
    ((recv (exp (gen) (mul x x-0))) (send (exp (gen) (mul x x-0)))))
  (label 5)
  (parent 2)
  (unrealized (2 0))
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol dh-mim diffie-hellman
  (defrole init
    (vars (h base) (x expn) (n text))
    (trace (send (exp (gen) x)) (recv h) (send (enc n (exp h x))))
    (non-orig x)
    (uniq-orig n (exp (gen) x)))
  (defrole resp
    (vars (h base) (x expn) (n text))
    (trace (recv h) (send (exp (gen) x)) (recv (enc n (exp h x))))
    (non-orig x)
    (uniq-orig (exp (gen) x)))
  (comment "Diffie-Hellman without signatures"
    "has a man-in-the-middle attack"))

(defskeleton dh-mim
  (vars (n text) (h base) (x expn))
  (defstrand init 3 (n n) (h h) (x x))
  (deflistener n)
  (non-orig x)
  (uniq-orig n (exp (gen) x))
  (traces ((send (exp (gen) x)) (recv h) (send (enc n (exp h x))))
    ((recv n) (send n)))
  (label 6)
  (unrealized (1 0))
  (preskeleton)
  (comment "Not a skeleton"))

(defskeleton dh-mim
  (vars (n text) (h base) (x expn))
  (defstrand init 3 (n n) (h h) (x x))
  (deflistener n)
  (precedes ((0 2) (1 0)))
  (non-orig x)
  (uniq-orig n (exp (gen) x))
  (traces ((send (exp (gen) x)) (recv h) (send (enc n (exp h x))))
    ((recv n) (send n)))
  (label 7)
  (parent 6)
  (unrealized (1 0))
  (origs ((exp (gen) x) (0 0)) (n (0 2)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dh-mim
  (vars (n text) (h base) (x x-0 expn))
  (defstrand init 3 (n n) (h h) (x x))
  (deflistener n)
  (deflistener (exp h x))
  (precedes ((0 2) (1 0)) ((2 1) (1 0)))
  (non-orig x)
  (uniq-orig n (exp (gen) x))
  (operation nonce-test (added-listener (exp h x)) n (1 0)
    (enc n (exp h x)))
  (traces ((send (exp (gen) x)) (recv h) (send (enc n (exp h x))))
    ((recv n) (send n)) ((recv (exp h x)) (send (exp h x))))
  (label 8)
  (parent 7)
  (unrealized (2 0))
  (comment "empty cohort"))

(comment "Nothing left to do")
