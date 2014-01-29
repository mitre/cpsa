(herald "Distributed Authentication Security Service Protocol Variants")

(defprotocol dass-simple basic
  (defrole init (vars (a b name) (k skey) (ta text) (kp akey) (tb text))
    (trace (send (cat (enc "init" ta k)
		      (enc a kp (privk a))
		      (enc (enc k (pubk b)) (invk kp))))
	   (recv (enc "resp" tb k))))
  (defrole resp (vars (a b name) (k skey) (ta text) (kp akey) (tb text))
    (trace (recv (cat (enc "init" ta k)
		      (enc a kp (privk a))
		      (enc (enc k (pubk b)) (invk kp))))
	   (send (enc "resp" tb k))))
  (comment "In this version of the protocol ")
  (comment "b might interact with a compromised initiator.")
  (comment "That is why a is not authenticated to b."))

(defprotocol dass+ basic
  (defrole init (vars (a b name) (k skey) (ta text) (kp akey) (tb text))
    (trace (send (cat (enc "init" ta k)
		      (enc a kp (privk a))
		      (enc (enc k (pubk b)) (invk kp))))
	   (recv (enc "resp" tb k))))
  (defrole resp (vars (a b name) (k skey) (ta text) (kp akey) (tb text))
    (trace (recv (cat (enc "init" ta k)
		      (enc a kp (privk a))
		      (enc (enc k (pubk b)) (invk kp))))
	   (send (enc "resp" tb k)))
    (non-orig (privk a)))
  (comment "In this version of the protocol ")
  (comment "b never interacts with a compromised initiator.")
  (comment "That is why a is properly authenticated to b."))

(defskeleton dass-simple
  (vars (a name) (b name) (k skey) (kp akey) (ta text)(tb text))
  (defstrand init 2 (a a) (b b) (k k) (kp kp) (ta ta) (tb tb))
  (non-orig (privk a) (privk b) (invk kp))
  (uniq-orig k kp))

(defskeleton dass+
  (vars (a name) (b name) (k skey) (kp akey) (ta text)(tb text))
  (defstrand init 2 (a a) (b b) (k k) (kp kp) (ta ta) (tb tb))
  (non-orig (privk a) (privk b) (invk kp))
  (uniq-orig k kp))

(comment
 (defskeleton dass
   (vars (a name) (b name) (ks name) (k skey) (kp akey))
   (defstrand init 4 (a a) (b b) (ks ks) (k k) (kp kp))
   (non-orig (privk a) (privk b) (privk ks))
   (uniq-orig k kp))

 (defskeleton dass
   (vars (a name) (b name) (ks name) (k skey) (kp akey))
   (defstrand resp 4 (a a) (b b) (ks ks) (k k) (kp kp))
   (non-orig (privk a) (privk b) (privk ks))
   (uniq-orig k kp)))
