;;; Hashtest.scm is designed to test if the
;;; hash is working properly.
(herald "Hashtest")

(defprotocol hashtest basic
  (defrole init (vars (n data) (k akey))
     (trace
       (send (enc n k))
       (recv (enc "h" n))
     )
     (uniq-orig n)
     (non-orig (invk k))
   )
   (defrole resp (vars (k akey) (n data))
     (trace
       (recv (enc n k))
       (send (enc "h" n))
     )
   )
)

(defskeleton hashtest
   (vars)
   (defstrand init 2)
)
