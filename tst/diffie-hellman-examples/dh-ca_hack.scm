(herald dhca (algebra basic) (bound 12))

(defmacro (CDH gx gy dhkey) (enc "dh" gx gy dhkey))

(defprotocol dhca basic
  (defrole init (vars (gx h akey) (dhkey skey) (a b ca name) (n text))
    (trace
     (recv (enc gx a (privk ca)))
     (send (cat gx (enc gx a (privk ca))))
     (recv (cat h (enc h b (privk ca)) (enc n (CDH gx h dhkey))))
     (send (enc "check" n (CDH gx h dhkey))))
    (non-orig (privk ca) dhkey))
  (defrole resp (vars (gy h akey) (dhkey skey) (a b ca name) (n text))
    (trace
     (recv (enc gy b (privk ca)))
     (recv (cat h (enc h a (privk ca))))
     (send (cat gy (enc gy b (privk ca))
		(enc n (CDH h gy dhkey))))
     (recv (enc "check" n (CDH h gy dhkey))))
    (non-orig (privk ca) dhkey))
  (defrole ca (vars (subject ca name) (gz akey))
    (trace
     (send (enc gz subject (privk ca)) ))
    (non-orig (invk gz)))
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
;  (comment "A diffie-hellman exchange which uses a certificate
;    authority to certify long-term DH values.")
)

(defskeleton dhca
  (vars )
  (defstrand init 4 )
(comment "Full initiator point-of-view.  No need to make extra assumptions."))

(defskeleton dhca
  (vars (n text))
  (defstrand resp 4 (n n))
  (uniq-orig n)
  (comment "Full responder point of view with freshly chosen n")
)

(defskeleton dhca
  (vars (n text))
  (defstrand resp 4 (n n))
  (deflistener n)
  (uniq-orig n)
  (comment "Full responder point of view with freshly chosen n")
)

(defskeleton dhca
  (vars (a b ca name) (gx gy akey) (n text) (dhkey skey))
  (defstrand init 4 (gx gx) (h gy) (ca ca) (a a) (b b) (n n) (dhkey dhkey))
  (defstrand resp 4 (h gx) (gy gy) (ca ca) (a a) (b b) (n n) (dhkey dhkey))
(uniq-orig n)
;(comment "point of view in which init and resp each complete and
;    they agree on the relevant parameters.")
)
