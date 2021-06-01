(herald invk)

(defprotocol invk basic
  (defrole rho
    (vars (ch chan) (a name) (k akey))
    (trace
     (recv ch (cat a (invk k)))
     (send ch (enc a k)))
    (inputs ch k)))
