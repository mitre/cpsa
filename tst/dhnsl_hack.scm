(herald "Diffie-Hellman enhanced Needham-Schroeder-Lowe Protocol"
  (algebra basic))

(defmacro (CDH gx gy dhkey) (enc "dh" gx gy dhkey))

(defprotocol dhnsl basic
  (defrole init
    (vars (a b name) (h2 h3 gx akey) (dhkey skey))
    (trace
     (send (enc gx a (pubk b)))
     (recv (enc h2 (CDH h2 gx dhkey) h3 b (pubk a)))
     (send (enc (CDH h3 gx dhkey) (pubk b)))
    )
    (uniq-orig gx)
    (non-orig (invk gx) dhkey)
    (comment "X should be assumed to be freshly chosen per role")
  )
  (defrole resp
    (vars (b a name) (h1 gy gz akey) (dhkey skey))
    (trace
     (recv (enc h1 a (pubk b)))
     (send (enc gy (CDH gy h1 dhkey) gz b (pubk a)))
     (recv (enc (CDH gz h1 dhkey) (pubk b)))
    )
    (uniq-orig gy gz)
    (non-orig (invk gy) (invk gz) dhkey)
    (comment "Y and Z should be assumed to be freshly chosen per role")
  )
  (comment "Needham-Schroeder-Lowe DH challenge/responses in place of nonces")
)

;;; The initiator point-of-view
(defskeleton dhnsl
  (vars (a b name) (gx gy gz akey))
  (defstrand init 3 (a a) (b b) (h2 gy) (h3 gz) (gx gx))
  (non-orig (privk b) (privk a))
  (comment "Initiator point-of-view"))

;;; The responder point-of-view
(defskeleton dhnsl
  (vars (a b name) (gx gy gz akey))
  (defstrand resp 3 (a a) (b b) (h1 gx) (gy gy) (gz gz))
  (non-orig (privk a))
  (comment "Responder point-of-view"))
