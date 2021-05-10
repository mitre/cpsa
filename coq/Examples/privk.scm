(herald privk)

(defprotocol privk basic
  (defrole rho
    (vars (ch chan) (a name) (k akey))
    (trace
     (recv ch (enc a (privk a) k))
     (send ch (enc a (privk a))))
    (inputs ch (invk k))))
