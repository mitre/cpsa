(herald disclosure)

(defprotocol disc basic
  (defrole init
    (vars (a b name) (k skey) (n text))
    (trace
     (send (enc a b n k))
     (recv n)
     (send k))
    (pen-non-orig k))

  (defrole resp
    (vars (a b name) (k skey) (n text))
    (trace
     (recv (enc a b n k))
     (send n))))

(defskeleton disc
  (vars (n text))
  (defstrand init 2 (n n))
  (uniq-orig n))
    
    
    
  

