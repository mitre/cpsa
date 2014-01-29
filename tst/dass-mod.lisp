(defprotocol dass basic
  (defrole init
    (vars (a name) (b name) (ks name) (k skey) (l text) (ta text) (tb text))
    (trace (send b)
	   (recv (enc (cat b (pubk b)) (privk ks)))
	   (send (enc (cat (enc ta k) l a (enc k (pubk b))) (privk a)))
	   (recv (enc tb k))))
  (defrole resp
    (vars (a name) (b name) (ks name) (k skey) (l text) (ta text) (tb text))
    (trace (recv (enc (cat (enc ta k) l a (enc k (pubk b))) (privk a)))
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
  (vars (a name) (b name) (ks name) (k skey))
  (defstrand init 4 (a a) (b b) (ks ks) (k k))
  (non-orig (privk a) (privk b) (privk ks))
  (uniq-orig k))

(defskeleton dass
  (vars (a name) (b name) (ks name) (k skey))
  (defstrand resp 4 (a a) (b b) (ks ks) (k k))
  (non-orig (privk a) (privk b) (privk ks))
  (uniq-orig k))
