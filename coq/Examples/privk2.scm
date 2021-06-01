(herald privk2)

(defprotocol privk2 basic
  (defrole rho
    (vars (ch chan) (a name) (k akey))
    (trace
     (recv ch (enc a (privk "enc" a) k))
     (send ch (enc a (privk "enc" a))))
    (inputs ch (invk k))))
