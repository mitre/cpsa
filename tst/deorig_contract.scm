;;;  Deorig_contract:  Demonstrates a subtle incompleteness.
;;;
;;;  Attempts to show that deorigination may be necessary
;;; even during non-augmentation steps, such as in a contraction.
;;;  The idea is to make for a situation in which a value will
;;; be originated on a strand but later a contraction will force
;;; that value to be one that is restricted, where deorigination
;;; can solve the problem but CPSA will probably eliminate the
;;; contraction from the cohort.

(defprotocol deorig-contract basic
  (defrole init (vars (k akey) (x1 x2 text))
     (trace
       (send (enc x1 k))
       (send (enc x2 k))
       (recv (enc x1 x2 k))
     )
     (uniq-orig x1 x2)
     (non-orig (invk k))
   )
   (defrole resp (vars (k akey) (y1 y2 y3 text))
     (trace
       (recv (enc y1 k))
       (recv (enc y2 k))
       (send (enc y1 y3 k))
     )
   )
)

(defskeleton deorig-contract
   (vars)
   (defstrand init 3)
)

(defskeleton deorig-contract
   (vars (k akey) (x1 x2 text))
   (defstrand init 3 (k k) (x1 x1) (x2 x2))
   (defstrand resp 3 (k k) (y1 x1) (y2 x2) (y3 x2))
   (precedes ((0 0) (1 0)) ((0 1) (1 1)) ((1 2) (0 2)))
)
