(herald ltk)

(defprotocol ltk basic
  (defrole rho
    (vars (ch chan) (a b name) (k akey))
    (trace
     (recv ch (enc a b (ltk a b) k))
     (send ch (enc a b (ltk a b))))
    (inputs ch (invk k))))
