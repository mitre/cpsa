(defprotocol cert basic
  (defrole init
    (vars (ch chan) (x text) (k akey))
    (trace (send ch (enc x (invk k))))
    (inputs ch k (enc x (invk k)))))

(defskeleton cert
  (vars)
  (defstrand init 1))
