(herald basic-dh (algebra diffie-hellman))

(defprotocol basic-dh diffie-hellman
  (defrole init
    (vars (a rndx) (b base) (n text))
    (trace
     (send (exp (gen) a))
     (recv b)
     (send (enc n (exp b a)))
     (recv n))
    (uniq-orig n)
    (uniq-gen a))
  (defrole recv
    (vars (a rndx) (b base) (n text))
    (trace
     (recv b)
     (send (exp (gen) a))
     (recv (enc n (exp b a)))
     (send n))
    (uniq-gen a)))

(defskeleton basic-dh
  (vars)
  (defstrand init 4))

(defskeleton basic-dh
  (vars)
  (defstrand recv 4))
  
