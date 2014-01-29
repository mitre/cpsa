(herald dhencrypt (algebra basic))

(defmacro (CDH gx gy dhkey) (enc "dh" gx gy dhkey))

(defprotocol dhencrypt basic
  (defrole init (vars (gx h akey) (dhkey skey) (n text))
    (trace
     (send gx)
     (recv (cat h (enc n (CDH gx h dhkey))))
     (send (enc "check" n (CDH gx h dhkey)))
    )
    (non-orig (invk gx) dhkey)
  )
  (defrole resp (vars (h gy akey) (dhkey skey) (n text))
    (trace
     (recv h)
     (send (cat gy (enc n (CDH h gy dhkey))))
     (recv (enc "check" n (CDH h gy dhkey)))
    )
    (non-orig (invk gy) dhkey)
    (uniq-orig gy n)
  )
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
  (comment "Diffie-hellman key exchange followed by an encrypted-nonce challenge/response")
)

(defskeleton dhencrypt
   (vars (gx h akey) (dhkey skey) (n text))
   (defstrand init 3 (gx gx) (h h) (dhkey dhkey) (n n))
   (comment "Initiator full point of view")
)

(defskeleton dhencrypt
   (vars (gy h akey) (dhkey skey) (n text))
   (defstrand resp 3 (gy gy) (h h) (dhkey dhkey) (n n))
   (comment "Responder full point of view")
)

(defskeleton dhencrypt
   (vars (gx gy akey) (n text))
   (defstrand init 2 (gx gx) (h gy) (n n))
   (defstrand resp 3 (h gx) (gy gy) (n n))
   (comment "Point of view where the natural result should be the only shape")
)
