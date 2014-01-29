(herald deorig-simple)

(comment "CPSA 2.3.1")
(comment "All input read from deorig_simple.scm")

(defprotocol deorig-simple basic
  (defrole init
    (vars (k akey) (x text))
    (trace (send (enc x k)) (recv x))
    (non-orig (invk k))
    (uniq-orig x))
  (defrole resp
    (vars (k akey) (x y text))
    (trace (recv (enc x k)) (send y))))

(defskeleton deorig-simple
  (vars (x text) (k akey))
  (defstrand init 2 (x x) (k k))
  (non-orig (invk k))
  (uniq-orig x)
  (traces ((send (enc x k)) (recv x)))
  (label 0)
  (unrealized (0 1))
  (origs (x (0 0)))
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol deorig-simple basic
  (defrole init
    (vars (k akey) (x text))
    (trace (send (enc x k)) (recv x))
    (non-orig (invk k))
    (uniq-orig x))
  (defrole resp
    (vars (k akey) (x y text))
    (trace (recv (enc x k)) (send y))))

(defskeleton deorig-simple
  (vars (z text) (k akey))
  (defstrand init 2 (x z) (k k))
  (defstrand resp 2 (x z) (y z) (k k))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (invk k))
  (uniq-orig z)
  (traces ((send (enc z k)) (recv z)) ((recv (enc z k)) (send z)))
  (label 1)
  (unrealized)
  (shape)
  (maps ((0 1) ((k k) (z z))))
  (origs (z (0 0))))

(comment "Nothing left to do")
