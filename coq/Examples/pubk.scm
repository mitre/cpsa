(herald pubk)

(defprotocol pubk basic
  (defrole rho
    (vars (ch chan) (a name) (k akey))
    (trace
     (recv ch (enc a (pubk a) k))
     (send ch (enc a (pubk a))))
    (inputs ch (invk k))))
