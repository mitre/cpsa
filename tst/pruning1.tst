(comment "CPSA 2.3.1")
(comment "All input read from pruning1.scm")

(defprotocol prune basic
  (defrole init
    (vars (a b name) (n text))
    (trace (send (enc n (pubk a))) (recv (enc n (pubk b) (pubk a)))
      (recv (enc n (privk b) (pubk a))))
    (non-orig (privk a))
    (uniq-orig n))
  (defrole trans
    (vars (a name) (n text) (k akey))
    (trace (recv (enc n (pubk a))) (recv k) (send (enc n k (pubk a)))))
  (comment "Shows a failure with generalization"
    "Run this with a step count of 4"))

(defskeleton prune
  (vars (n text) (a b name))
  (defstrand init 3 (n n) (a a) (b b))
  (non-orig (privk a))
  (uniq-orig n)
  (traces
    ((send (enc n (pubk a))) (recv (enc n (pubk b) (pubk a)))
      (recv (enc n (privk b) (pubk a)))))
  (label 0)
  (unrealized (0 1) (0 2))
  (origs (n (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton prune
  (vars (n text) (a b name) (k akey))
  (defstrand init 3 (n n) (a a) (b b))
  (defstrand trans 3 (n n) (a a) (k k))
  (precedes ((0 0) (1 0)) ((1 2) (0 1)))
  (non-orig (privk a))
  (uniq-orig n)
  (operation nonce-test (added-strand trans 3) n (0 1) (enc n (pubk a)))
  (traces
    ((send (enc n (pubk a))) (recv (enc n (pubk b) (pubk a)))
      (recv (enc n (privk b) (pubk a))))
    ((recv (enc n (pubk a))) (recv k) (send (enc n k (pubk a)))))
  (label 1)
  (parent 0)
  (unrealized (0 1) (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton prune
  (vars (n text) (a b name))
  (defstrand init 3 (n n) (a a) (b b))
  (defstrand trans 3 (n n) (a a) (k (pubk b)))
  (precedes ((0 0) (1 0)) ((1 2) (0 1)))
  (non-orig (privk a))
  (uniq-orig n)
  (operation nonce-test (contracted (k (pubk b))) n (0 1)
    (enc n (pubk a)) (enc n (pubk b) (pubk a)))
  (traces
    ((send (enc n (pubk a))) (recv (enc n (pubk b) (pubk a)))
      (recv (enc n (privk b) (pubk a))))
    ((recv (enc n (pubk a))) (recv (pubk b))
      (send (enc n (pubk b) (pubk a)))))
  (label 2)
  (parent 1)
  (unrealized (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton prune
  (vars (n text) (a b name) (k akey))
  (defstrand init 3 (n n) (a a) (b b))
  (defstrand trans 3 (n n) (a a) (k (pubk b)))
  (defstrand trans 3 (n n) (a a) (k k))
  (precedes ((0 0) (1 0)) ((0 0) (2 0)) ((1 2) (0 1)) ((2 2) (0 2)))
  (non-orig (privk a))
  (uniq-orig n)
  (operation nonce-test (added-strand trans 3) n (0 2) (enc n (pubk a))
    (enc n (pubk b) (pubk a)))
  (traces
    ((send (enc n (pubk a))) (recv (enc n (pubk b) (pubk a)))
      (recv (enc n (privk b) (pubk a))))
    ((recv (enc n (pubk a))) (recv (pubk b))
      (send (enc n (pubk b) (pubk a))))
    ((recv (enc n (pubk a))) (recv k) (send (enc n k (pubk a)))))
  (label 3)
  (parent 2)
  (unrealized (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton prune
  (vars (n text) (a b name))
  (defstrand init 3 (n n) (a a) (b b))
  (defstrand trans 3 (n n) (a a) (k (pubk b)))
  (defstrand trans 3 (n n) (a a) (k (privk b)))
  (precedes ((0 0) (1 0)) ((0 0) (2 0)) ((1 2) (0 1)) ((2 2) (0 2)))
  (non-orig (privk a))
  (uniq-orig n)
  (operation nonce-test (contracted (k (privk b))) n (0 2)
    (enc n (pubk a)) (enc n (privk b) (pubk a))
    (enc n (pubk b) (pubk a)))
  (traces
    ((send (enc n (pubk a))) (recv (enc n (pubk b) (pubk a)))
      (recv (enc n (privk b) (pubk a))))
    ((recv (enc n (pubk a))) (recv (pubk b))
      (send (enc n (pubk b) (pubk a))))
    ((recv (enc n (pubk a))) (recv (privk b))
      (send (enc n (privk b) (pubk a)))))
  (label 4)
  (parent 3)
  (unrealized)
  (shape)
  (maps ((0) ((a a) (b b) (n n))))
  (origs (n (0 0))))

(comment "Nothing left to do")

(defprotocol prune basic
  (defrole init
    (vars (a b name) (n text))
    (trace (send (enc n (pubk a))) (recv (enc n (pubk b) (pubk a)))
      (recv (enc n (privk b) (pubk a))))
    (non-orig (privk a))
    (uniq-orig n))
  (defrole trans
    (vars (a name) (n text) (k akey))
    (trace (recv (enc n (pubk a))) (recv k) (send (enc n k (pubk a)))))
  (comment "Shows a failure with generalization"
    "Run this with a step count of 4"))

(defskeleton prune
  (vars (n text) (a b name))
  (defstrand init 3 (n n) (a a) (b b))
  (defstrand trans 3 (n n) (a a) (k (pubk b)))
  (defstrand trans 3 (n n) (a a) (k (privk b)))
  (precedes ((0 0) (1 0)) ((0 0) (2 0)) ((1 2) (0 1)) ((2 2) (0 2)))
  (non-orig (privk a))
  (uniq-orig n)
  (traces
    ((send (enc n (pubk a))) (recv (enc n (pubk b) (pubk a)))
      (recv (enc n (privk b) (pubk a))))
    ((recv (enc n (pubk a))) (recv (pubk b))
      (send (enc n (pubk b) (pubk a))))
    ((recv (enc n (pubk a))) (recv (privk b))
      (send (enc n (privk b) (pubk a)))))
  (label 5)
  (unrealized)
  (shape)
  (maps ((0 1 2) ((n n) (a a) (b b))))
  (origs (n (0 0))))

(comment "Nothing left to do")
