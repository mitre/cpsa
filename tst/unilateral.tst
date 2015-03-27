(herald unilateral)

(comment "CPSA 2.5.0")
(comment "All input read from unilateral.scm")

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
  (goals
    (forall ((n text) (k akey) (z z-0 node))
      (implies
        (and (p "init" 0 z) (p "init" 1 z-0) (p "init" "n" z-0 n)
          (p "init" "k" z-0 k) (str-prec z z-0) (non (invk k))
          (uniq-at n z))
        (exists ((z-1 z-2 node))
          (and (p "resp" 0 z-1) (p "resp" 1 z-2) (p "resp" "n" z-2 n)
            (p "resp" "k" z-2 k) (prec z z-1) (prec z-2 z-0)
            (str-prec z-1 z-2))))))
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
    (forall ((n text) (k akey) (z node))
      (implies
        (and (p "resp" 1 z) (p "resp" "n" z n) (p "resp" "k" z k)
          (non (invk k)) (pnon n))
        (exists ((k-0 akey) (z-0 z-1 node))
          (and (p "resp" 0 z-0) (p "init" 0 z-1) (p "init" "n" z-1 n)
            (p "init" "k" z-1 k-0) (prec z-1 z-0) (str-prec z-0 z)
            (uniq-at n z-1))))))
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
