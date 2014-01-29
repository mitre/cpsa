(herald deorig-mesg)

(defprotocol deorig-mesg basic
  (defrole init
    (vars (k akey) (x text))
    (trace (send (enc x k)) (recv x))
    (uniq-orig x)
    (non-orig (invk k)))
  (defrole resp
    (vars (x mesg) (y text))
    (trace (recv x) (send y))))

(defskeleton deorig-mesg (vars) (defstrand init 2))

(defskeleton deorig-mesg
  (vars (k akey) (z text))
  (defstrand init 2 (k k) (x z))
  (defstrand resp 2 (x (enc z k)) (y z))
  (precedes ((0 0) (1 0)) ((1 1) (0 1))))
