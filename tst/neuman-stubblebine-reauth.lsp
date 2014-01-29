(defprotocol neuman-stubblebine-reauth basic
  (defrole init (vars (a b ks name) (ra rb text) (k skey) (tb text))
    (trace
     (send (cat a ra))
     (recv (cat (enc b ra k tb (ltk a ks)) (enc a k tb (ltk b ks)) rb))
     (send (cat (enc a k tb (ltk b ks)) (enc rb k)))))
  (defrole resp (vars (a b ks name) (ra rb text) (k skey) (tb text))
    (trace
     (recv (cat a ra)) (send (cat b rb (enc a ra tb (ltk b ks))))
     (recv (cat (enc a k tb (ltk b ks)) (enc rb k)))))
  (defrole init-reauth
    (vars (a b ks name) (ra-prime rb-prime text) (k skey) (tb text))
    (trace
     (recv (enc a k tb (ltk b ks)))
     (send (cat (enc a k tb (ltk b ks)) ra-prime))
     (recv (cat rb-prime (enc ra-prime k))) (send (enc rb-prime k))))
  (defrole resp-reauth
    (vars (a b ks name) (ra-prime rb-prime text) (k skey) (tb text))
    (trace
     (recv (cat (enc a k tb (ltk b ks)) ra-prime))
     (send (cat rb-prime (enc ra-prime k)))
     (recv (enc rb-prime k))))
  (defrole keyserver
    (vars (a b ks name) (ra rb text) (k skey) (tb text))
    (trace
     (recv (cat b rb (enc a ra tb (ltk b ks))))
     (send (cat (enc b ra k tb (ltk a ks))
		(enc a k tb (ltk b ks)) rb)))
    (uniq-orig k)))

(defskeleton neuman-stubblebine-reauth
  (vars (ra rb-0 tb rb text) (a b ks name) (k skey)
	(ra-prime rb-prime text))
  (defstrand resp 3 (a a) (b b) (ks ks) (ra ra) (rb rb) (k k) (tb tb))
  (defstrand resp-reauth 3 (a a) (b b) (ks ks) (k k) (ra-prime ra-prime)
    (rb-prime rb-prime))
  (non-orig (ltk a ks) (ltk b ks))
  (uniq-orig ra rb k ra-prime rb-prime))
