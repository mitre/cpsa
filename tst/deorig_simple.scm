(herald deorig-simple)

;;;  Deorig_simple:     Demonstrates the same incompleteness as
;;;                     deorig_contract, but with fewer messages.
;;;
;;;  This simply sets up the archetypal nonce test for an init strand
;;;  but the resp role is only a partial match for the test.  In particular,
;;;  it sends a different value than it receives.  The obvious shape is one
;;;  in which the resp strand sends the same value it receives, but this
;;;  shape is not found.

(defprotocol deorig-simple basic
  (defrole init
    (vars (k akey) (x text))
    (trace (send (enc x k)) (recv x))
    (uniq-orig x)
    (non-orig (invk k)))
  (defrole resp
    (vars (k akey) (x y text))
    (trace (recv (enc x k)) (send y))))

(defskeleton deorig-simple
  (vars)
  (defstrand init 2))

(defskeleton deorig-simple
  (vars (k akey) (z text))
  (defstrand init 2 (k k) (x z))
  (defstrand resp 2 (k k) (x z) (y z))
  (precedes ((0 0) (1 0)) ((1 1) (0 1))))
