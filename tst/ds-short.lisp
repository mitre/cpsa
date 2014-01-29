;;; This is something like the Denning Sacco protocol with
;;; public keys as described by Clark and Jacob, but without
;;; timestamps.  Since the whole point of the protocol was to
;;; show how timestamps could be used, this is a funny thing to do!

(defprotocol denning-sacco-with-pk basic
  (defrole init ; A
    (vars (a name) (b name) (ks name) (k skey))
    (trace (send (cat a b))
	   (recv (cat (enc (cat b (pubk b)) (privk ks)) ; certB
		      (enc (cat a (pubk a)) (privk ks)))) ; cert A
	   (send (cat (enc (enc k (privk a)) (pubk b)) ; sign & encr k
		      (enc (cat b (pubk b)) (privk ks))
		      (enc (cat a  (pubk a)) (privk ks))))))
  (defrole resp ; B
    (vars (a name) (b name) (ks name) (k skey))
    (trace (recv (cat (enc (enc k (privk a)) (pubk b))
		      (enc (cat b (pubk b)) (privk ks))
		      (enc (cat a (pubk a)) (privk ks))))))
  (defrole keyserver
    (vars (a name) (b name) (ks name))
    (trace (recv (cat a b))
	   (send (cat (enc (cat b (pubk b)) (privk ks))
		      (enc (cat a (pubk a)) (privk ks)))))))

;;; For the preskeleton, I'd like to require every initiator and
;;; respondent to use the same ks.  How can that be done?

(defskeleton denning-sacco-with-pk
  (vars (a name) (b name) (ks name) (k skey))
  (defstrand resp 1 (a a) (b b) (ks ks) (k k))
  (non-orig (privk b) (privk a) (privk ks))
  (uniq-orig k))
