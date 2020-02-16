(herald facts)

(comment "CPSA 4.2.3")
(comment "All input read from tst/facts.scm")

(defprotocol unilateral basic
  (defrole init
    (vars (n text) (k akey))
    (trace (send (enc n k)) (recv n))
    (uniq-orig n))
  (defrole resp
    (vars (n text) (k akey))
    (trace (recv (enc n k)) (send n))))

(defskeleton unilateral
  (vars (n text) (k akey))
  (defstrand init 2 (n n) (k k))
  (non-orig (invk k))
  (uniq-orig n)
  (facts (foo 0 k) (bar 0 (invk k)))
  (traces ((send (enc n k)) (recv n)))
  (label 0)
  (unrealized (0 1))
  (origs (n (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton unilateral
  (vars (n text) (k akey))
  (defstrand init 2 (n n) (k k))
  (defstrand resp 2 (n n) (k k))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (invk k))
  (uniq-orig n)
  (facts (foo 0 k) (bar 0 (invk k)))
  (operation nonce-test (added-strand resp 2) n (0 1) (enc n k))
  (traces ((send (enc n k)) (recv n)) ((recv (enc n k)) (send n)))
  (label 1)
  (parent 0)
  (unrealized)
  (shape)
  (maps ((0) ((k k) (n n))))
  (origs (n (0 0))))

(comment "Nothing left to do")

(defprotocol unilateral basic
  (defrole init
    (vars (n text) (k akey))
    (trace (send (enc n k)) (recv n))
    (uniq-orig n))
  (defrole resp
    (vars (n text) (k akey))
    (trace (recv (enc n k)) (send n))))

(defskeleton unilateral
  (vars (n text) (k akey))
  (defstrand resp 2 (n n) (k k))
  (non-orig (invk k))
  (pen-non-orig n)
  (traces ((recv (enc n k)) (send n)))
  (label 2)
  (unrealized (0 0))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton unilateral
  (vars (n text) (k k-0 akey))
  (defstrand resp 2 (n n) (k k))
  (defstrand init 1 (n n) (k k-0))
  (precedes ((1 0) (0 0)))
  (non-orig (invk k))
  (pen-non-orig n)
  (uniq-orig n)
  (operation nonce-test (added-strand init 1) n (0 0))
  (traces ((recv (enc n k)) (send n)) ((send (enc n k-0))))
  (label 3)
  (parent 2)
  (unrealized)
  (shape)
  (maps ((0) ((n n) (k k))))
  (origs (n (1 0))))

(comment "Nothing left to do")

(defprotocol unilateral basic
  (defrole init
    (vars (n text) (k akey))
    (trace (send (enc n k)) (recv n))
    (uniq-orig n))
  (defrole resp
    (vars (n text) (k akey))
    (trace (recv (enc n k)) (send n))))

(defskeleton unilateral
  (vars (n text) (k akey))
  (defstrand init 2 (n n) (k k))
  (non-orig (invk k))
  (uniq-orig n)
  (facts (foo 0 k) (bar 0 (invk k)))
  (goals
    (forall ((n text) (k akey) (z strd))
      (implies
        (and (p "init" z 2) (p "init" "n" z n) (p "init" "k" z k)
          (non (invk k)) (uniq-at n z 0) (fact foo z k)
          (fact bar z (invk k)))
        (exists ((z-0 strd))
          (and (p "resp" z-0 2) (p "resp" "n" z-0 n)
            (p "resp" "k" z-0 k) (prec z 0 z-0 0) (prec z-0 1 z 1))))))
  (traces ((send (enc n k)) (recv n)))
  (label 4)
  (unrealized (0 1))
  (origs (n (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton unilateral
  (vars (n text) (k akey))
  (defstrand init 2 (n n) (k k))
  (defstrand resp 2 (n n) (k k))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (invk k))
  (uniq-orig n)
  (facts (foo 0 k) (bar 0 (invk k)))
  (operation nonce-test (added-strand resp 2) n (0 1) (enc n k))
  (traces ((send (enc n k)) (recv n)) ((recv (enc n k)) (send n)))
  (label 5)
  (parent 4)
  (unrealized)
  (shape)
  (satisfies yes)
  (maps ((0) ((n n) (k k))))
  (origs (n (0 0))))

(comment "Nothing left to do")

(defprotocol unilateral basic
  (defrole init
    (vars (n text) (k akey))
    (trace (send (enc n k)) (recv n))
    (uniq-orig n))
  (defrole resp
    (vars (n text) (k akey))
    (trace (recv (enc n k)) (send n))))

(defskeleton unilateral
  (vars (n text) (k akey))
  (defstrand resp 2 (n n) (k k))
  (non-orig (invk k))
  (pen-non-orig n)
  (goals
    (forall ((n text) (k akey) (z strd))
      (implies
        (and (p "resp" z 2) (p "resp" "n" z n) (p "resp" "k" z k)
          (non (invk k)) (pnon n))
        (exists ((k-0 akey) (z-0 strd))
          (and (p "init" z-0 1) (p "init" "n" z-0 n)
            (p "init" "k" z-0 k-0) (prec z-0 0 z 0)
            (uniq-at n z-0 0))))))
  (traces ((recv (enc n k)) (send n)))
  (label 6)
  (unrealized (0 0))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton unilateral
  (vars (n text) (k k-0 akey))
  (defstrand resp 2 (n n) (k k))
  (defstrand init 1 (n n) (k k-0))
  (precedes ((1 0) (0 0)))
  (non-orig (invk k))
  (pen-non-orig n)
  (uniq-orig n)
  (operation nonce-test (added-strand init 1) n (0 0))
  (traces ((recv (enc n k)) (send n)) ((send (enc n k-0))))
  (label 7)
  (parent 6)
  (unrealized)
  (shape)
  (satisfies yes)
  (maps ((0) ((n n) (k k))))
  (origs (n (1 0))))

(comment "Nothing left to do")

(defprotocol iso-unilateral basic
  (defrole resp
    (vars (na nb t1 t2 t3 text) (b name))
    (trace (recv (cat nb t1))
      (send (cat na nb b t3 (enc na nb b t2 (privk b)))))
    (uniq-orig na))
  (defrole init
    (vars (na nb t1 t2 t3 text) (b name))
    (trace (send (cat nb t1))
      (recv (cat na nb b t3 (enc na nb b t2 (privk b)))))
    (uniq-orig nb))
  (comment "Two pass authentication"))

(defskeleton iso-unilateral
  (vars (na nb t1 t2 t3 text) (b name))
  (defstrand init 2 (na na) (nb nb) (t1 t1) (t2 t2) (t3 t3) (b b))
  (non-orig (privk b))
  (uniq-orig nb)
  (traces
    ((send (cat nb t1))
      (recv (cat na nb b t3 (enc na nb b t2 (privk b))))))
  (label 8)
  (unrealized (0 1))
  (origs (nb (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton iso-unilateral
  (vars (na nb t1 t2 t3 t1-0 t3-0 text) (b name))
  (defstrand init 2 (na na) (nb nb) (t1 t1) (t2 t2) (t3 t3) (b b))
  (defstrand resp 2 (na na) (nb nb) (t1 t1-0) (t2 t2) (t3 t3-0) (b b))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk b))
  (uniq-orig na nb)
  (operation encryption-test (added-strand resp 2)
    (enc na nb b t2 (privk b)) (0 1))
  (traces
    ((send (cat nb t1))
      (recv (cat na nb b t3 (enc na nb b t2 (privk b)))))
    ((recv (cat nb t1-0))
      (send (cat na nb b t3-0 (enc na nb b t2 (privk b))))))
  (label 9)
  (parent 8)
  (unrealized)
  (shape)
  (maps ((0) ((b b) (na na) (nb nb) (t1 t1) (t2 t2) (t3 t3))))
  (origs (na (1 1)) (nb (0 0))))

(comment "Nothing left to do")

(defprotocol iso-unilateral basic
  (defrole resp
    (vars (na nb t1 t2 t3 text) (b name))
    (trace (recv (cat nb t1))
      (send (cat na nb b t3 (enc na nb b t2 (privk b)))))
    (uniq-orig na))
  (defrole init
    (vars (na nb t1 t2 t3 text) (b name))
    (trace (send (cat nb t1))
      (recv (cat na nb b t3 (enc na nb b t2 (privk b)))))
    (uniq-orig nb))
  (comment "Two pass authentication"))

(defskeleton iso-unilateral
  (vars (na nb t1 t2 t3 text) (b name))
  (defstrand init 2 (na na) (nb nb) (t1 t1) (t2 t2) (t3 t3) (b b))
  (non-orig (privk b))
  (uniq-orig nb)
  (goals
    (forall ((b name) (z strd))
      (implies (and (p "init" z 2) (p "init" "b" z b) (non (privk b)))
        (exists ((y strd)) (and (p "resp" y 2) (p "resp" "b" y b))))))
  (traces
    ((send (cat nb t1))
      (recv (cat na nb b t3 (enc na nb b t2 (privk b))))))
  (label 10)
  (unrealized (0 1))
  (origs (nb (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton iso-unilateral
  (vars (na nb t1 t2 t3 t1-0 t3-0 text) (b name))
  (defstrand init 2 (na na) (nb nb) (t1 t1) (t2 t2) (t3 t3) (b b))
  (defstrand resp 2 (na na) (nb nb) (t1 t1-0) (t2 t2) (t3 t3-0) (b b))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk b))
  (uniq-orig na nb)
  (operation encryption-test (added-strand resp 2)
    (enc na nb b t2 (privk b)) (0 1))
  (traces
    ((send (cat nb t1))
      (recv (cat na nb b t3 (enc na nb b t2 (privk b)))))
    ((recv (cat nb t1-0))
      (send (cat na nb b t3-0 (enc na nb b t2 (privk b))))))
  (label 11)
  (parent 10)
  (unrealized)
  (shape)
  (satisfies yes)
  (maps ((0) ((b b) (na na) (nb nb) (t1 t1) (t2 t2) (t3 t3))))
  (origs (na (1 1)) (nb (0 0))))

(comment "Nothing left to do")

(defprotocol iso-unilateral basic
  (defrole resp
    (vars (na nb t1 t2 t3 text) (b name))
    (trace (recv (cat nb t1))
      (send (cat na nb b t3 (enc na nb b t2 (privk b)))))
    (uniq-orig na))
  (defrole init
    (vars (na nb t1 t2 t3 text) (b name))
    (trace (send (cat nb t1))
      (recv (cat na nb b t3 (enc na nb b t2 (privk b)))))
    (uniq-orig nb))
  (comment "Two pass authentication"))

(defskeleton iso-unilateral
  (vars (na nb t1 t2 t3 text) (b name))
  (defstrand init 2 (na na) (nb nb) (t1 t1) (t2 t2) (t3 t3) (b b))
  (non-orig (privk b))
  (uniq-orig nb)
  (goals
    (forall ((b name) (z strd))
      (implies (and (p "init" z 2) (p "init" "b" z b) (non (privk b)))
        (false))))
  (traces
    ((send (cat nb t1))
      (recv (cat na nb b t3 (enc na nb b t2 (privk b))))))
  (label 12)
  (unrealized (0 1))
  (origs (nb (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton iso-unilateral
  (vars (na nb t1 t2 t3 t1-0 t3-0 text) (b name))
  (defstrand init 2 (na na) (nb nb) (t1 t1) (t2 t2) (t3 t3) (b b))
  (defstrand resp 2 (na na) (nb nb) (t1 t1-0) (t2 t2) (t3 t3-0) (b b))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk b))
  (uniq-orig na nb)
  (operation encryption-test (added-strand resp 2)
    (enc na nb b t2 (privk b)) (0 1))
  (traces
    ((send (cat nb t1))
      (recv (cat na nb b t3 (enc na nb b t2 (privk b)))))
    ((recv (cat nb t1-0))
      (send (cat na nb b t3-0 (enc na nb b t2 (privk b))))))
  (label 13)
  (parent 12)
  (unrealized)
  (shape)
  (satisfies (no (b b) (z 0)))
  (maps ((0) ((b b) (na na) (nb nb) (t1 t1) (t2 t2) (t3 t3))))
  (origs (na (1 1)) (nb (0 0))))

(comment "Nothing left to do")
