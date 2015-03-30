(herald goals)

(comment "CPSA 2.5.0")
(comment "All input read from goals.scm")

(defprotocol unilateral basic
  (defrole init
    (vars (a name) (n text))
    (trace (send (enc n (pubk a))) (recv n)))
  (defrole resp
    (vars (b name) (n text))
    (trace (recv (enc n (pubk b))) (send n))))

(defskeleton unilateral
  (vars (n text) (a name))
  (defstrand init 2 (n n) (a a))
  (non-orig (privk a))
  (uniq-orig n)
  (goals
    (forall ((a name) (n text) (z0 node))
      (implies
        (and (p "init" 1 z0) (p "init" "n" z0 n) (p "init" "a" z0 a)
          (non (privk a)) (uniq n))
        (exists ((z1 node))
          (and (p "resp" 1 z1) (p "resp" "b" z1 a))))))
  (comment "Authentication goal")
  (traces ((send (enc n (pubk a))) (recv n)))
  (label 0)
  (unrealized (0 1))
  (origs (n (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton unilateral
  (vars (n text) (a name))
  (defstrand init 2 (n n) (a a))
  (defstrand resp 2 (n n) (b a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a))
  (uniq-orig n)
  (operation nonce-test (added-strand resp 2) n (0 1) (enc n (pubk a)))
  (traces ((send (enc n (pubk a))) (recv n))
    ((recv (enc n (pubk a))) (send n)))
  (label 1)
  (parent 0)
  (unrealized)
  (shape)
  (satisfies yes)
  (maps ((0) ((a a) (n n))))
  (origs (n (0 0))))

(comment "Nothing left to do")

(defprotocol ns basic
  (defrole init
    (vars (a b name) (n1 n2 text))
    (trace (send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b)))))
  (defrole resp
    (vars (b a name) (n2 n1 text))
    (trace (recv (enc n1 a (pubk b))) (send (enc n1 n2 (pubk a)))
      (recv (enc n2 (pubk b)))))
  (comment "Needham-Schroeder"))

(defskeleton ns
  (vars (n n2 text) (a a-0 name))
  (defstrand init 2 (n1 n) (n2 n2) (a a-0) (b a))
  (non-orig (privk a))
  (uniq-orig n)
  (goals
    (forall ((a name) (n text) (z0 node))
      (implies
        (and (p "init" 1 z0) (p "init" "n1" z0 n) (p "init" "b" z0 a)
          (non (privk a)) (uniq n))
        (exists ((z1 node))
          (and (p "resp" 1 z1) (p "resp" "b" z1 a))))))
  (comment "Initiator authentication goal"
    "Same as unilateral goal under the predicate mapping:" (p "init" 1)
    "->" (p "init" 1) "and" (p "init" "n") "->" (p "init" "n1") "and"
    (p "init" "a") "->" (p "init" "b") "and" (p "resp" 1) "->"
    (p "resp" 1))
  (traces ((send (enc n a-0 (pubk a))) (recv (enc n n2 (pubk a-0)))))
  (label 2)
  (unrealized (0 1))
  (origs (n (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (n n2 n2-0 text) (a a-0 name))
  (defstrand init 2 (n1 n) (n2 n2) (a a-0) (b a))
  (defstrand resp 2 (n2 n2-0) (n1 n) (b a) (a a-0))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a))
  (uniq-orig n)
  (operation nonce-test (added-strand resp 2) n (0 1)
    (enc n a-0 (pubk a)))
  (traces ((send (enc n a-0 (pubk a))) (recv (enc n n2 (pubk a-0))))
    ((recv (enc n a-0 (pubk a))) (send (enc n n2-0 (pubk a-0)))))
  (label 3)
  (parent 2)
  (unrealized)
  (shape)
  (satisfies yes)
  (maps ((0) ((a a) (n n) (a-0 a-0) (n2 n2))))
  (origs (n (0 0))))

(comment "Nothing left to do")

(defprotocol ns basic
  (defrole init
    (vars (a b name) (n1 n2 text))
    (trace (send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b)))))
  (defrole resp
    (vars (b a name) (n2 n1 text))
    (trace (recv (enc n1 a (pubk b))) (send (enc n1 n2 (pubk a)))
      (recv (enc n2 (pubk b)))))
  (comment "Needham-Schroeder"))

(defskeleton ns
  (vars (n n1 text) (a b name))
  (defstrand resp 3 (n2 n) (n1 n1) (b b) (a a))
  (non-orig (privk a))
  (uniq-orig n)
  (goals
    (forall ((a name) (n text) (z0 node))
      (implies
        (and (p "resp" 2 z0) (p "resp" "n2" z0 n) (p "resp" "a" z0 a)
          (non (privk a)) (uniq n))
        (exists ((z1 node))
          (and (p "resp" 2 z1) (p "resp" "a" z1 a))))))
  (comment "Responder authentication goal"
    "Same as unilateral goal under the predicate mapping:" (p "init" 1)
    "->" (p "resp" 2) "and" (p "init" "n") "->" (p "resp" "n2") "and"
    (p "init" "a") "->" (p "resp" "a") "and" (p "resp" 1) "->"
    (p "init" 2))
  (traces
    ((recv (enc n1 a (pubk b))) (send (enc n1 n (pubk a)))
      (recv (enc n (pubk b)))))
  (label 4)
  (unrealized (0 2))
  (origs (n (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (n n1 text) (a b b-0 name))
  (defstrand resp 3 (n2 n) (n1 n1) (b b) (a a))
  (defstrand init 3 (n1 n1) (n2 n) (a a) (b b-0))
  (precedes ((0 1) (1 1)) ((1 2) (0 2)))
  (non-orig (privk a))
  (uniq-orig n)
  (operation nonce-test (added-strand init 3) n (0 2)
    (enc n1 n (pubk a)))
  (traces
    ((recv (enc n1 a (pubk b))) (send (enc n1 n (pubk a)))
      (recv (enc n (pubk b))))
    ((send (enc n1 a (pubk b-0))) (recv (enc n1 n (pubk a)))
      (send (enc n (pubk b-0)))))
  (label 5)
  (parent 4)
  (unrealized)
  (shape)
  (satisfies yes)
  (maps ((0) ((a a) (n n) (b b) (n1 n1))))
  (origs (n (0 1))))

(comment "Nothing left to do")

(defprotocol ns basic
  (defrole init
    (vars (a b name) (n1 n2 text))
    (trace (send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b)))))
  (defrole resp
    (vars (b a name) (n2 n1 text))
    (trace (recv (enc n1 a (pubk b))) (send (enc n1 n2 (pubk a)))
      (recv (enc n2 (pubk b)))))
  (comment "Needham-Schroeder"))

(defskeleton ns
  (vars (n1 n2 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (non-orig (privk a) (privk b))
  (uniq-orig n1)
  (goals
    (forall ((a b name) (n1 text) (no nu node))
      (implies
        (and (p "init" 2 no) (p "init" "a" no a) (p "init" "b" no b)
          (p "init" "n1" no n1) (p "init" 0 nu) (str-prec nu no)
          (non (privk a)) (non (privk b)) (uniq-at n1 nu))
        (exists ((na nb node))
          (and (p "init" 2 na) (p "resp" 1 nb) (p "init" "b" na b)
            (p "resp" "b" nb b))))))
  (comment "Initiator point-of-view")
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b)))))
  (label 6)
  (unrealized (0 1))
  (origs (n1 (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (n1 n2 n2-0 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (defstrand resp 2 (n2 n2-0) (n1 n1) (b b) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a) (privk b))
  (uniq-orig n1)
  (operation nonce-test (added-strand resp 2) n1 (0 1)
    (enc n1 a (pubk b)))
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b))))
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2-0 (pubk a)))))
  (label 7)
  (parent 6)
  (unrealized (0 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (n1 n2 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (defstrand resp 2 (n2 n2) (n1 n1) (b b) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a) (privk b))
  (uniq-orig n1)
  (operation nonce-test (contracted (n2-0 n2)) n1 (0 1)
    (enc n1 n2 (pubk a)) (enc n1 a (pubk b)))
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b))))
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2 (pubk a)))))
  (label 8)
  (parent 7)
  (unrealized)
  (shape)
  (satisfies yes)
  (maps ((0) ((a a) (b b) (n1 n1) (n2 n2))))
  (origs (n1 (0 0))))

(comment "Nothing left to do")

(defprotocol ns basic
  (defrole init
    (vars (a b name) (n1 n2 text))
    (trace (send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b)))))
  (defrole resp
    (vars (b a name) (n2 n1 text))
    (trace (recv (enc n1 a (pubk b))) (send (enc n1 n2 (pubk a)))
      (recv (enc n2 (pubk b)))))
  (comment "Needham-Schroeder"))

(defskeleton ns
  (vars (n1 n2 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (non-orig (privk a) (privk b))
  (uniq-orig n1)
  (goals
    (forall ((a b name) (n1 text) (no nu node))
      (implies
        (and (p "init" 2 no) (p "init" "a" no a) (p "init" "b" no b)
          (p "init" "n1" no n1) (p "init" 0 nu) (str-prec nu no)
          (non (privk a)) (non (privk b)) (uniq-at n1 nu))
        (exists ((na nb node))
          (and (p "init" 2 na) (p "resp" 1 nb) (p "init" "b" na b)
            (p "resp" "b" nb b))))))
  (comment "Initiator point-of-view")
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b)))))
  (label 9)
  (unrealized (0 1))
  (origs (n1 (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (n1 n2 n2-0 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (defstrand resp 2 (n2 n2-0) (n1 n1) (b b) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a) (privk b))
  (uniq-orig n1)
  (operation nonce-test (added-strand resp 2) n1 (0 1)
    (enc n1 a (pubk b)))
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b))))
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2-0 (pubk a)))))
  (label 10)
  (parent 9)
  (unrealized (0 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (n1 n2 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (defstrand resp 2 (n2 n2) (n1 n1) (b b) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a) (privk b))
  (uniq-orig n1)
  (operation nonce-test (contracted (n2-0 n2)) n1 (0 1)
    (enc n1 n2 (pubk a)) (enc n1 a (pubk b)))
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b))))
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2 (pubk a)))))
  (label 11)
  (parent 10)
  (unrealized)
  (shape)
  (satisfies yes)
  (maps ((0) ((a a) (b b) (n1 n1) (n2 n2))))
  (origs (n1 (0 0))))

(comment "Nothing left to do")

(defprotocol ns basic
  (defrole init
    (vars (a b name) (n1 n2 text))
    (trace (send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b)))))
  (defrole resp
    (vars (b a name) (n2 n1 text))
    (trace (recv (enc n1 a (pubk b))) (send (enc n1 n2 (pubk a)))
      (recv (enc n2 (pubk b)))))
  (comment "Needham-Schroeder"))

(defskeleton ns
  (vars (n2 n1 text) (a b name))
  (defstrand resp 3 (n2 n2) (n1 n1) (b b) (a a))
  (non-orig (privk a))
  (uniq-orig n2)
  (goals
    (forall ((n2 n1 text) (a b name) (z z-0 node))
      (implies
        (and (p "resp" 1 z) (p "resp" 2 z-0) (p "resp" "n2" z-0 n2)
          (p "resp" "n1" z-0 n1) (p "resp" "b" z-0 b)
          (p "resp" "a" z-0 a) (str-prec z z-0) (non (privk a))
          (uniq-at n2 z))
        (exists ((b-0 name) (z-1 z-2 node))
          (and (p "init" 1 z-1) (p "init" 2 z-2) (p "init" "n1" z-2 n1)
            (p "init" "n2" z-2 n2) (p "init" "a" z-2 a)
            (p "init" "b" z-2 b-0) (prec z z-1) (prec z-2 z-0)
            (str-prec z-1 z-2))))))
  (comment "Responder point-of-view")
  (traces
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2 (pubk a)))
      (recv (enc n2 (pubk b)))))
  (label 12)
  (unrealized (0 2))
  (origs (n2 (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (n2 n1 text) (a b b-0 name))
  (defstrand resp 3 (n2 n2) (n1 n1) (b b) (a a))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b-0))
  (precedes ((0 1) (1 1)) ((1 2) (0 2)))
  (non-orig (privk a))
  (uniq-orig n2)
  (operation nonce-test (added-strand init 3) n2 (0 2)
    (enc n1 n2 (pubk a)))
  (traces
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2 (pubk a)))
      (recv (enc n2 (pubk b))))
    ((send (enc n1 a (pubk b-0))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b-0)))))
  (label 13)
  (parent 12)
  (unrealized)
  (shape)
  (satisfies yes)
  (maps ((0) ((a a) (n2 n2) (b b) (n1 n1))))
  (origs (n2 (0 1))))

(comment "Nothing left to do")

(defprotocol ns basic
  (defrole init
    (vars (a b name) (n1 n2 text))
    (trace (send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b)))))
  (defrole resp
    (vars (b a name) (n2 n1 text))
    (trace (recv (enc n1 a (pubk b))) (send (enc n1 n2 (pubk a)))
      (recv (enc n2 (pubk b)))))
  (comment "Needham-Schroeder"))

(defskeleton ns
  (vars (n2 n1 text) (a b name))
  (defstrand resp 3 (n2 n2) (n1 n1) (b b) (a a))
  (non-orig (privk a))
  (uniq-orig n2)
  (goals
    (forall ((n2 n1 text) (a b name) (z z-0 node))
      (implies
        (and (p "resp" 1 z) (p "resp" 2 z-0) (p "resp" "n2" z-0 n2)
          (p "resp" "n1" z-0 n1) (p "resp" "b" z-0 b)
          (p "resp" "a" z-0 a) (str-prec z z-0) (non (privk a))
          (uniq-at n2 z))
        (exists ((b-0 name) (z-1 z-2 node))
          (and (p "init" 1 z-1) (p "init" 2 z-2) (p "init" "n1" z-2 n1)
            (p "init" "n2" z-2 n2) (p "init" "a" z-2 a)
            (p "init" "b" z-2 b-0) (prec z z-1) (prec z-2 z-0)
            (str-prec z-1 z-2))))))
  (comment "Responder point-of-view")
  (traces
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2 (pubk a)))
      (recv (enc n2 (pubk b)))))
  (label 14)
  (unrealized (0 2))
  (origs (n2 (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (n2 n1 text) (a b b-0 name))
  (defstrand resp 3 (n2 n2) (n1 n1) (b b) (a a))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b-0))
  (precedes ((0 1) (1 1)) ((1 2) (0 2)))
  (non-orig (privk a))
  (uniq-orig n2)
  (operation nonce-test (added-strand init 3) n2 (0 2)
    (enc n1 n2 (pubk a)))
  (traces
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2 (pubk a)))
      (recv (enc n2 (pubk b))))
    ((send (enc n1 a (pubk b-0))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b-0)))))
  (label 15)
  (parent 14)
  (unrealized)
  (shape)
  (satisfies yes)
  (maps ((0) ((a a) (n2 n2) (b b) (n1 n1))))
  (origs (n2 (0 1))))

(comment "Nothing left to do")

(defprotocol ns basic
  (defrole init
    (vars (a b name) (n1 n2 text))
    (trace (send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b)))))
  (defrole resp
    (vars (b a name) (n2 n1 text))
    (trace (recv (enc n1 a (pubk b))) (send (enc n1 n2 (pubk a)))
      (recv (enc n2 (pubk b)))))
  (comment "Needham-Schroeder"))

(defskeleton ns
  (vars (n1 n1-0 n2 n2-0 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (defstrand init 3 (n1 n1-0) (n2 n2-0) (a a) (b b))
  (non-orig (privk a) (privk b))
  (uniq-orig n1 n1-0)
  (goals
    (forall ((n1 n1-0 n2 n2-0 text) (a b name) (z z-0 z-1 z-2 node))
      (implies
        (and (p "init" 0 z) (p "init" 2 z-0) (p "init" 0 z-1)
          (p "init" 2 z-2) (p "init" "n1" z-0 n1) (p "init" "n2" z-0 n2)
          (p "init" "a" z-0 a) (p "init" "b" z-0 b)
          (p "init" "n1" z-2 n1-0) (p "init" "n2" z-2 n2-0)
          (p "init" "a" z-2 a) (p "init" "b" z-2 b) (str-prec z z-0)
          (str-prec z-1 z-2) (non (privk a)) (non (privk b))
          (uniq-at n1 z) (uniq-at n1-0 z-1)) (= z-1 z))))
  (comment "Double initiator point-of-view")
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b))))
    ((send (enc n1-0 a (pubk b))) (recv (enc n1-0 n2-0 (pubk a)))
      (send (enc n2-0 (pubk b)))))
  (label 16)
  (unrealized (0 1) (1 1))
  (origs (n1 (0 0)) (n1-0 (1 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (n1 n2 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (non-orig (privk a) (privk b))
  (uniq-orig n1)
  (operation collapsed 1 0)
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b)))))
  (label 17)
  (parent 16)
  (unrealized (0 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (n1 n1-0 n2 n2-0 n2-1 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (defstrand init 3 (n1 n1-0) (n2 n2-0) (a a) (b b))
  (defstrand resp 2 (n2 n2-1) (n1 n1-0) (b b) (a a))
  (precedes ((1 0) (2 0)) ((2 1) (1 1)))
  (non-orig (privk a) (privk b))
  (uniq-orig n1 n1-0)
  (operation nonce-test (added-strand resp 2) n1-0 (1 1)
    (enc n1-0 a (pubk b)))
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b))))
    ((send (enc n1-0 a (pubk b))) (recv (enc n1-0 n2-0 (pubk a)))
      (send (enc n2-0 (pubk b))))
    ((recv (enc n1-0 a (pubk b))) (send (enc n1-0 n2-1 (pubk a)))))
  (label 18)
  (parent 16)
  (unrealized (0 1) (1 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (n1 n2 n2-0 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (defstrand resp 2 (n2 n2-0) (n1 n1) (b b) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a) (privk b))
  (uniq-orig n1)
  (operation nonce-test (added-strand resp 2) n1 (0 1)
    (enc n1 a (pubk b)))
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b))))
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2-0 (pubk a)))))
  (label 19)
  (parent 17)
  (unrealized (0 1))
  (origs (n1 (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (n1 n1-0 n2 n2-0 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (defstrand init 3 (n1 n1-0) (n2 n2-0) (a a) (b b))
  (defstrand resp 2 (n2 n2-0) (n1 n1-0) (b b) (a a))
  (precedes ((1 0) (2 0)) ((2 1) (1 1)))
  (non-orig (privk a) (privk b))
  (uniq-orig n1 n1-0)
  (operation nonce-test (contracted (n2-1 n2-0)) n1-0 (1 1)
    (enc n1-0 n2-0 (pubk a)) (enc n1-0 a (pubk b)))
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b))))
    ((send (enc n1-0 a (pubk b))) (recv (enc n1-0 n2-0 (pubk a)))
      (send (enc n2-0 (pubk b))))
    ((recv (enc n1-0 a (pubk b))) (send (enc n1-0 n2-0 (pubk a)))))
  (label 20)
  (parent 18)
  (unrealized (0 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (n1 n2 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (defstrand resp 2 (n2 n2) (n1 n1) (b b) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a) (privk b))
  (uniq-orig n1)
  (operation nonce-test (contracted (n2-0 n2)) n1 (0 1)
    (enc n1 n2 (pubk a)) (enc n1 a (pubk b)))
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b))))
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2 (pubk a)))))
  (label 21)
  (parent 19)
  (unrealized)
  (shape)
  (satisfies yes)
  (maps ((0 0) ((a a) (b b) (n1 n1) (n1-0 n1) (n2 n2) (n2-0 n2))))
  (origs (n1 (0 0))))

(defskeleton ns
  (vars (n1 n1-0 n2 n2-0 n2-1 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (defstrand init 3 (n1 n1-0) (n2 n2-0) (a a) (b b))
  (defstrand resp 2 (n2 n2-0) (n1 n1-0) (b b) (a a))
  (defstrand resp 2 (n2 n2-1) (n1 n1) (b b) (a a))
  (precedes ((0 0) (3 0)) ((1 0) (2 0)) ((2 1) (1 1)) ((3 1) (0 1)))
  (non-orig (privk a) (privk b))
  (uniq-orig n1 n1-0)
  (operation nonce-test (added-strand resp 2) n1 (0 1)
    (enc n1 a (pubk b)))
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b))))
    ((send (enc n1-0 a (pubk b))) (recv (enc n1-0 n2-0 (pubk a)))
      (send (enc n2-0 (pubk b))))
    ((recv (enc n1-0 a (pubk b))) (send (enc n1-0 n2-0 (pubk a))))
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2-1 (pubk a)))))
  (label 22)
  (parent 20)
  (unrealized (0 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (n1 n1-0 n2 n2-0 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2-0) (a a) (b b))
  (defstrand init 3 (n1 n1-0) (n2 n2) (a a) (b b))
  (defstrand resp 2 (n2 n2) (n1 n1-0) (b b) (a a))
  (defstrand resp 2 (n2 n2-0) (n1 n1) (b b) (a a))
  (precedes ((0 0) (3 0)) ((1 0) (2 0)) ((2 1) (1 1)) ((3 1) (0 1)))
  (non-orig (privk a) (privk b))
  (uniq-orig n1 n1-0)
  (operation nonce-test (contracted (n2-1 n2-0)) n1 (0 1)
    (enc n1 n2-0 (pubk a)) (enc n1 a (pubk b)))
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2-0 (pubk a)))
      (send (enc n2-0 (pubk b))))
    ((send (enc n1-0 a (pubk b))) (recv (enc n1-0 n2 (pubk a)))
      (send (enc n2 (pubk b))))
    ((recv (enc n1-0 a (pubk b))) (send (enc n1-0 n2 (pubk a))))
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2-0 (pubk a)))))
  (label 23)
  (parent 22)
  (unrealized)
  (shape)
  (satisfies
    (no (n1 n1) (n1-0 n1-0) (n2 n2-0) (n2-0 n2) (a a) (b b) (z (0 0))
      (z-0 (0 2)) (z-1 (1 0)) (z-2 (1 2))))
  (maps ((0 1) ((a a) (b b) (n1 n1) (n1-0 n1-0) (n2 n2-0) (n2-0 n2))))
  (origs (n1 (0 0)) (n1-0 (1 0))))

(comment "Nothing left to do")

(defprotocol ns-role-origs basic
  (defrole init
    (vars (a b name) (n1 n2 text))
    (trace (send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b))))
    (non-orig (privk b))
    (uniq-orig n1))
  (defrole resp
    (vars (b a name) (n2 n1 text))
    (trace (recv (enc n1 a (pubk b))) (send (enc n1 n2 (pubk a)))
      (recv (enc n2 (pubk b))))
    (non-orig (privk a))
    (uniq-orig n2))
  (comment
    "Needham-Schroeder with role assumptions that are too strong"))

(defskeleton ns-role-origs
  (vars (n1 n2 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (non-orig (privk b))
  (uniq-orig n1)
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b)))))
  (label 24)
  (unrealized (0 1))
  (origs (n1 (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns-role-origs
  (vars (n1 n2 n2-0 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (defstrand resp 2 (n2 n2-0) (n1 n1) (b b) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a) (privk b))
  (uniq-orig n1 n2-0)
  (operation nonce-test (added-strand resp 2) n1 (0 1)
    (enc n1 a (pubk b)))
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b))))
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2-0 (pubk a)))))
  (label 25)
  (parent 24)
  (unrealized (0 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns-role-origs
  (vars (n1 n2 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (defstrand resp 2 (n2 n2) (n1 n1) (b b) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a) (privk b))
  (uniq-orig n1 n2)
  (operation nonce-test (contracted (n2-0 n2)) n1 (0 1)
    (enc n1 n2 (pubk a)) (enc n1 a (pubk b)))
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b))))
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2 (pubk a)))))
  (label 26)
  (parent 25)
  (unrealized)
  (shape)
  (maps ((0) ((a a) (b b) (n1 n1) (n2 n2))))
  (origs (n2 (1 1)) (n1 (0 0))))

(comment "Nothing left to do")

(defprotocol ns-role-origs basic
  (defrole init
    (vars (a b name) (n1 n2 text))
    (trace (send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b))))
    (non-orig (privk b))
    (uniq-orig n1))
  (defrole resp
    (vars (b a name) (n2 n1 text))
    (trace (recv (enc n1 a (pubk b))) (send (enc n1 n2 (pubk a)))
      (recv (enc n2 (pubk b))))
    (non-orig (privk a))
    (uniq-orig n2))
  (comment
    "Needham-Schroeder with role assumptions that are too strong"))

(defskeleton ns-role-origs
  (vars (n2 n1 text) (b a name))
  (defstrand resp 3 (n2 n2) (n1 n1) (b b) (a a))
  (non-orig (privk a))
  (uniq-orig n2)
  (traces
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2 (pubk a)))
      (recv (enc n2 (pubk b)))))
  (label 27)
  (unrealized (0 2))
  (origs (n2 (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns-role-origs
  (vars (n2 n1 text) (b a b-0 name))
  (defstrand resp 3 (n2 n2) (n1 n1) (b b) (a a))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b-0))
  (precedes ((0 1) (1 1)) ((1 0) (0 0)) ((1 2) (0 2)))
  (non-orig (privk a) (privk b-0))
  (uniq-orig n2 n1)
  (operation nonce-test (added-strand init 3) n2 (0 2)
    (enc n1 n2 (pubk a)))
  (traces
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2 (pubk a)))
      (recv (enc n2 (pubk b))))
    ((send (enc n1 a (pubk b-0))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b-0)))))
  (label 28)
  (parent 27)
  (unrealized (0 0) (0 2))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton ns-role-origs
  (vars (n2 n1 text) (a b name))
  (defstrand resp 3 (n2 n2) (n1 n1) (b b) (a a))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (precedes ((0 1) (1 1)) ((1 0) (0 0)) ((1 2) (0 2)))
  (non-orig (privk a) (privk b))
  (uniq-orig n2 n1)
  (operation nonce-test (contracted (b-0 b)) n1 (0 0)
    (enc n1 a (pubk b)))
  (traces
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2 (pubk a)))
      (recv (enc n2 (pubk b))))
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b)))))
  (label 29)
  (parent 28)
  (unrealized)
  (shape)
  (maps ((0) ((b b) (a a) (n2 n2) (n1 n1))))
  (origs (n1 (1 0)) (n2 (0 1))))

(defskeleton ns-role-origs
  (vars (n2 n1 n2-0 text) (b a b-0 name))
  (defstrand resp 3 (n2 n2) (n1 n1) (b b) (a a))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b-0))
  (defstrand resp 2 (n2 n2-0) (n1 n1) (b b-0) (a a))
  (precedes ((0 1) (1 1)) ((1 0) (2 0)) ((1 2) (0 2)) ((2 1) (0 0)))
  (non-orig (privk a) (privk b-0))
  (uniq-orig n2 n1 n2-0)
  (operation nonce-test (added-strand resp 2) n1 (0 0)
    (enc n1 a (pubk b-0)))
  (traces
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2 (pubk a)))
      (recv (enc n2 (pubk b))))
    ((send (enc n1 a (pubk b-0))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b-0))))
    ((recv (enc n1 a (pubk b-0))) (send (enc n1 n2-0 (pubk a)))))
  (label 30)
  (parent 28)
  (unrealized (0 0) (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns-role-origs
  (vars (n2 n1 n2-0 text) (a b name))
  (defstrand resp 3 (n2 n2) (n1 n1) (b b) (a a))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (defstrand resp 2 (n2 n2-0) (n1 n1) (b b) (a a))
  (precedes ((0 1) (1 1)) ((1 0) (2 0)) ((1 2) (0 2)) ((2 1) (0 0)))
  (non-orig (privk a) (privk b))
  (uniq-orig n2 n1 n2-0)
  (operation nonce-test (contracted (b-0 b)) n1 (0 0)
    (enc n1 n2-0 (pubk a)) (enc n1 a (pubk b)))
  (traces
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2 (pubk a)))
      (recv (enc n2 (pubk b))))
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b))))
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2-0 (pubk a)))))
  (label 31)
  (parent 30)
  (seen 29)
  (unrealized)
  (comment "1 in cohort - 0 not yet seen"))

(comment "Nothing left to do")

(defprotocol ns2 basic
  (defrole init
    (vars (a b name) (n1 n2 n3 text))
    (trace (send (enc n1 n3 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b)))))
  (defrole resp
    (vars (b a name) (n2 n1 text))
    (trace (recv (enc n1 n1 a (pubk b))) (send (enc n1 n2 (pubk a)))
      (recv (enc n2 (pubk b))))
    (note doubled nonce in the first message))
  (note that this protocol is derived from Needham-Schroeder))

(defskeleton ns2
  (vars (n1 n2 n3 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (n3 n3) (a a) (b b))
  (non-orig (privk a) (privk b))
  (uniq-orig n1)
  (traces
    ((send (enc n1 n3 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b)))))
  (label 32)
  (unrealized (0 1))
  (origs (n1 (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns2
  (vars (n2 n3 n2-0 text) (a b name))
  (defstrand init 3 (n1 n3) (n2 n2) (n3 n3) (a a) (b b))
  (defstrand resp 2 (n2 n2-0) (n1 n3) (b b) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a) (privk b))
  (uniq-orig n3)
  (operation nonce-test (added-strand resp 2) n3 (0 1)
    (enc n3 n3 a (pubk b)))
  (traces
    ((send (enc n3 n3 a (pubk b))) (recv (enc n3 n2 (pubk a)))
      (send (enc n2 (pubk b))))
    ((recv (enc n3 n3 a (pubk b))) (send (enc n3 n2-0 (pubk a)))))
  (label 33)
  (parent 32)
  (unrealized (0 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns2
  (vars (n3 n2 text) (a b name))
  (defstrand init 3 (n1 n3) (n2 n2) (n3 n3) (a a) (b b))
  (defstrand resp 2 (n2 n2) (n1 n3) (b b) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a) (privk b))
  (uniq-orig n3)
  (operation nonce-test (contracted (n2-0 n2)) n3 (0 1)
    (enc n3 n2 (pubk a)) (enc n3 n3 a (pubk b)))
  (traces
    ((send (enc n3 n3 a (pubk b))) (recv (enc n3 n2 (pubk a)))
      (send (enc n2 (pubk b))))
    ((recv (enc n3 n3 a (pubk b))) (send (enc n3 n2 (pubk a)))))
  (label 34)
  (parent 33)
  (unrealized)
  (shape)
  (maps ((0) ((a a) (b b) (n1 n3) (n2 n2) (n3 n3))))
  (origs (n3 (0 0))))

(comment "Nothing left to do")

(defprotocol ns basic
  (defrole init
    (vars (a b name) (n1 n2 text))
    (trace (send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b)))))
  (defrole resp
    (vars (b a name) (n2 n1 text))
    (trace (recv (enc n1 a (pubk b))) (send (enc n1 n2 (pubk a)))
      (recv (enc n2 (pubk b)))))
  (comment "Needham-Schroeder"))

(defskeleton ns
  (vars (n1 n2 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (defstrand resp 2 (n2 n2) (n1 n1) (b b) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a) (privk b))
  (uniq-orig n1)
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 (pubk a)))
      (send (enc n2 (pubk b))))
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2 (pubk a)))))
  (label 35)
  (unrealized)
  (shape)
  (maps ((0 1) ((n1 n1) (n2 n2) (a a) (b b))))
  (origs (n1 (0 0))))

(comment "Nothing left to do")

(defprotocol nsl-typeless basic
  (defrole init
    (vars (a b name) (n1 text) (n2 mesg))
    (trace (send (enc a n1 (pubk b))) (recv (enc n1 n2 b (pubk a)))
      (send (enc n2 (pubk b)))))
  (defrole resp
    (vars (b a name) (n2 text) (n1 mesg))
    (trace (recv (enc a n1 (pubk b))) (send (enc n1 n2 b (pubk a)))
      (recv (enc n2 (pubk b)))))
  (comment "Needham-Schroeder-Lowe with untyped nonces"))

(defskeleton nsl-typeless
  (vars (n1 mesg) (n2 text) (a b name))
  (defstrand resp 2 (n1 n1) (n2 n2) (b b) (a a))
  (deflistener n2)
  (non-orig (privk a) (privk b))
  (uniq-orig n2)
  (comment "Shows typeflaw in typeless NSL")
  (traces ((recv (enc a n1 (pubk b))) (send (enc n1 n2 b (pubk a))))
    ((recv n2) (send n2)))
  (label 36)
  (unrealized (1 0))
  (preskeleton)
  (comment "Not a skeleton"))

(defskeleton nsl-typeless
  (vars (n1 mesg) (n2 text) (a b name))
  (defstrand resp 2 (n1 n1) (n2 n2) (b b) (a a))
  (deflistener n2)
  (precedes ((0 1) (1 0)))
  (non-orig (privk a) (privk b))
  (uniq-orig n2)
  (traces ((recv (enc a n1 (pubk b))) (send (enc n1 n2 b (pubk a))))
    ((recv n2) (send n2)))
  (label 37)
  (parent 36)
  (unrealized (1 0))
  (origs (n2 (0 1)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton nsl-typeless
  (vars (n2 n1 text) (a b name))
  (defstrand resp 2 (n1 n1) (n2 n2) (b b) (a a))
  (deflistener n2)
  (defstrand init 3 (n2 n2) (n1 n1) (a a) (b b))
  (precedes ((0 1) (2 1)) ((2 2) (1 0)))
  (non-orig (privk a) (privk b))
  (uniq-orig n2)
  (operation nonce-test (added-strand init 3) n2 (1 0)
    (enc n1 n2 b (pubk a)))
  (traces ((recv (enc a n1 (pubk b))) (send (enc n1 n2 b (pubk a))))
    ((recv n2) (send n2))
    ((send (enc a n1 (pubk b))) (recv (enc n1 n2 b (pubk a)))
      (send (enc n2 (pubk b)))))
  (label 38)
  (parent 37)
  (unrealized (1 0))
  (comment "empty cohort"))

(defskeleton nsl-typeless
  (vars (n2 n2-0 text) (a b a-0 name))
  (defstrand resp 2 (n1 a-0) (n2 n2) (b b) (a a))
  (deflistener n2)
  (defstrand resp 2 (n1 (cat n2 b)) (n2 n2-0) (b a) (a a-0))
  (precedes ((0 1) (2 0)) ((2 1) (1 0)))
  (non-orig (privk a) (privk b))
  (uniq-orig n2)
  (operation nonce-test (added-strand resp 2) n2 (1 0)
    (enc a-0 n2 b (pubk a)))
  (traces ((recv (enc a a-0 (pubk b))) (send (enc a-0 n2 b (pubk a))))
    ((recv n2) (send n2))
    ((recv (enc a-0 n2 b (pubk a)))
      (send (enc (cat n2 b) n2-0 a (pubk a-0)))))
  (label 39)
  (parent 37)
  (unrealized)
  (shape)
  (maps ((0 1) ((a a) (b b) (n2 n2) (n1 a-0))))
  (origs (n2 (0 1))))

(comment "Nothing left to do")
