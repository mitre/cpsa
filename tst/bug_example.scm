(herald bug_example (bound 10))

(defprotocol bug_example basic
  (defrole init (vars (x y akey))
    (trace
     (send (enc y (hash x (invk y)))))
    (non-orig (invk y) (invk x)))
  (defrole resp (vars (x y akey))
    (trace
     (recv (enc y (hash (invk x) y))))
    (non-orig (invk x) (invk y)))
  (defrole flip (vars (k k1 k2 akey))
    (trace
     (recv (enc k (hash k1 k2)))
     (send (enc k (hash (invk k1) (invk k2)))))))

(defskeleton bug_example
  (vars (x y akey))
  (defstrand resp 1 (x x) (y y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprotocol bug_example basic
  (defrole init (vars (x y akey))
    (trace
     (send (enc y (hash x (invk y)))))
    (non-orig (invk y) (invk x)))
  (defrole resp (vars (x y akey))
    (trace
     (recv (enc y (hash (invk x) y))))
    (non-orig (invk x) (invk y)))
  (defrole flip1 (vars (k k1 k2 akey))
    (trace
     (recv (enc k (hash (invk k1) k2)))
     (send (enc k (hash k1 (invk k2))))))
  (defrole flip2 (vars (k k1 k2 akey))
    (trace
     (recv (enc k (hash k1 (invk k2))))
     (send (enc k (hash (invk k1) k2))))))

(defskeleton bug_example
  (vars (x y akey))
  (defstrand resp 1 (x x) (y y)))
