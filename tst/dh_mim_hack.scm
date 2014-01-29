(defmacro (CDH gx gy dhkey) (enc "dh" gx gy dhkey))

(defprotocol dh_mim basic
  (defrole init
    (vars (gx gy akey) (n text) (dhkey skey))
    (trace (send gx) (recv gy) (send (enc n (CDH gx gy dhkey))))
    (uniq-orig n gx)
    (non-orig (invk gx) dhkey))
  (defrole resp
    (vars (gx gy akey) (n text) (dhkey skey))
    (trace (recv gx) (send gy) (recv (enc n (CDH gx gy dhkey))))
    (uniq-orig gy)
    (non-orig (invk gy) dhkey))
  (defrole CDHcalc1 (vars (gx gy akey) (dhkey skey))
   (trace
    (recv (cat gx (invk gy)))
    (send (CDH gx gy dhkey))
  ))
  (defrole CDHcalc2 (vars (gx gy akey) (dhkey skey))
   (trace
    (recv (cat gy (invk gx)))
    (send (CDH gx gy dhkey))
  ))
  (comment "Diffie-hellman key exchange followed by an encryption"))

(defskeleton dh_mim
  (vars (n text) (gx gy akey) (dhkey skey))
  (defstrand init 3 (n n) (gx gx) (dhkey dhkey))
  (defstrand resp 3 (n n) (gy gy) (dhkey dhkey))
  (precedes ((0 2) (1 2)))
  (comment "Agreement on the encrypted text only"))
