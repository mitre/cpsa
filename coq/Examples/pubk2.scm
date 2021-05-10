(herald pubk2)

(defprotocol pubk2 basic
  (defrole rho
    (vars (ch chan) (a name) (k akey))
    (trace
     (recv ch (enc a (pubk "enc" a) k))
     (send ch (enc a (pubk "enc" a))))
    (inputs ch (invk k))))
