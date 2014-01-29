(defprotocol dass basic
  (defrole init
    (vars (a name) (b name) (ks name) (k skey) (l text) (ta text) (kp akey) (tb text))
    (trace (send b)
	   (recv (enc (cat b (pubk b)) (privk ks)))
	   (send (cat (enc ta k) (enc (cat l a kp) (privk a)) (enc (enc k (pubk b)) kp)))
	   (recv (enc tb k))))
  (defrole resp
    (vars (a name) (b name) (ks name) (k skey) (l text) (ta text) (kp akey) (tb text))
    (trace (recv (cat (enc ta k) (enc (cat l a kp) (privk a)) (enc (enc k (pubk b)) kp)))
	   (send a)
	   (recv (enc (cat a (pubk a)) (privk ks)))
	   (send (enc tb k))))
  (defrole keyserver
    (vars (a name) (b name) (ks name))
    (trace (recv b)
	   (send (enc (cat b (pubk b)) (privk ks)))
	   (recv a)
	   (send (enc (cat a (pubk a)) (privk ks))))))

(defskeleton dass
  (vars (a name) (b name) (ks name) (k skey) (kp akey))
  (defstrand init 4 (a a) (b b) (ks ks) (k k) (kp kp))
  (non-orig (privk a) (privk b) (privk ks))
  (uniq-orig k kp))

(defskeleton dass
  (vars (a name) (b name) (ks name) (k skey) (kp akey))
  (defstrand resp 4 (a a) (b b) (ks ks) (k k) (kp kp))
  (non-orig (privk a) (privk b) (privk ks))
  (uniq-orig k kp))
