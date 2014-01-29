(comment "CPSA 2.3.1")
(comment "All input read from deorig_contract.scm")

(defprotocol deorig-contract basic
  (defrole init
    (vars (k akey) (x1 x2 text))
    (trace (send (enc x1 k)) (send (enc x2 k)) (recv (enc x1 x2 k)))
    (non-orig (invk k))
    (uniq-orig x1 x2))
  (defrole resp
    (vars (k akey) (y1 y2 y3 text))
    (trace (recv (enc y1 k)) (recv (enc y2 k)) (send (enc y1 y3 k)))))

(defskeleton deorig-contract
  (vars (x1 x2 text) (k akey))
  (defstrand init 3 (x1 x1) (x2 x2) (k k))
  (non-orig (invk k))
  (uniq-orig x1 x2)
  (traces ((send (enc x1 k)) (send (enc x2 k)) (recv (enc x1 x2 k))))
  (label 0)
  (unrealized (0 2))
  (origs (x2 (0 1)) (x1 (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton deorig-contract
  (vars (x1 x2 y2 y3 text) (k akey))
  (defstrand init 3 (x1 x1) (x2 x2) (k k))
  (defstrand resp 3 (y1 x1) (y2 y2) (y3 y3) (k k))
  (precedes ((0 0) (1 0)) ((1 2) (0 2)))
  (non-orig (invk k))
  (uniq-orig x1 x2)
  (operation nonce-test (added-strand resp 3) x1 (0 2) (enc x1 k))
  (traces ((send (enc x1 k)) (send (enc x2 k)) (recv (enc x1 x2 k)))
    ((recv (enc x1 k)) (recv (enc y2 k)) (send (enc x1 y3 k))))
  (label 1)
  (parent 0)
  (unrealized (0 2))
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol deorig-contract basic
  (defrole init
    (vars (k akey) (x1 x2 text))
    (trace (send (enc x1 k)) (send (enc x2 k)) (recv (enc x1 x2 k)))
    (non-orig (invk k))
    (uniq-orig x1 x2))
  (defrole resp
    (vars (k akey) (y1 y2 y3 text))
    (trace (recv (enc y1 k)) (recv (enc y2 k)) (send (enc y1 y3 k)))))

(defskeleton deorig-contract
  (vars (x1 x2 text) (k akey))
  (defstrand init 3 (x1 x1) (x2 x2) (k k))
  (defstrand resp 3 (y1 x1) (y2 x2) (y3 x2) (k k))
  (precedes ((0 0) (1 0)) ((0 1) (1 1)) ((1 2) (0 2)))
  (non-orig (invk k))
  (uniq-orig x1 x2)
  (traces ((send (enc x1 k)) (send (enc x2 k)) (recv (enc x1 x2 k)))
    ((recv (enc x1 k)) (recv (enc x2 k)) (send (enc x1 x2 k))))
  (label 2)
  (unrealized)
  (shape)
  (maps ((0 1) ((k k) (x1 x1) (x2 x2))))
  (origs (x2 (0 1)) (x1 (0 0))))

(comment "Nothing left to do")
