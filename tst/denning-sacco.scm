(herald "Denning-Sacco Protocol")

(defprotocol denning-sacco basic
  (defrole init (vars (a b ks name) (k skey) (ta text))
    (trace
     (send (cat a b))
     (recv (cat (enc b (pubk b) (privk ks))
		(enc a (pubk a) (privk ks))))
     (send (enc (enc a b k ta (privk a))
		(enc b (pubk b) (privk ks))
		(enc a (pubk a) (privk ks)) (pubk b)))))
  (defrole resp (vars (a b ks name) (k skey) (ta text))
    (trace
     (recv (enc (enc a b k ta (privk a))
		(enc b (pubk b) (privk ks))
		(enc a (pubk a) (privk ks)) (pubk b)))))
  (defrole keyserver (vars (a b ks name))
    (trace
     (recv (cat a b))
     (send (cat (enc b (pubk b) (privk ks))
		(enc a (pubk a) (privk ks)))))))

(defskeleton denning-sacco
  (vars (a b ks name) (k skey))
  (defstrand resp 1 (a a) (b b) (ks ks) (k k))
  (non-orig (privk b) (privk a) (privk ks))
  (uniq-orig k))
