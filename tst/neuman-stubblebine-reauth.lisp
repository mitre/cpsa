(defprotocol neuman-stubblebine basic
  (defrole init
    (vars (a name) (b name) (ks name) (ra text) (ra-prime text) (rb text) (rb-prime text) (k skey) (tb text))
    (trace (send (cat a ra))
	   (recv (cat (enc (cat b ra k tb) (ltk a ks)) (enc (cat a k tb) (ltk b ks)) rb))
	   (send (cat (enc (cat a k tb) (ltk b ks)) (enc rb k)))
	   (send (cat (enc (cat a k tb) (ltk b ks)) ra-prime))
	   (recv (cat rb-prime (enc ra-prime k)))
	   (send (enc rb-prime k))))
  (defrole resp
    (vars (a name) (b name) (ks name) (ra text) (ra-prime text) (rb text) (rb-prime text) (k skey) (tb text))
    (trace (recv (cat a ra))
	   (send (cat b rb (enc (cat a ra tb) (ltk b ks))))
	   (recv (cat (enc (cat a k tb) (ltk b ks)) (enc rb k)))
	   (recv (cat (enc (cat a k tb) (ltk b ks)) ra-prime))
	   (send (cat rb-prime (enc ra-prime k)))
	   (recv (enc rb-prime k))))
  (defrole keyserver
    (vars (a name) (b name) (ks name) (ra text) (rb text) (k skey) (tb text))
    (trace (recv (cat b rb (enc (cat a ra tb) (ltk b ks))))
	   (send (cat (enc (cat b ra k tb) (ltk a ks)) (enc (cat a k tb) (ltk b ks)) rb)))
    (uniq-orig k)))

;(defskeleton neuman-stubblebine
;  (vars (a name) (b name) (k skey) (ks name) (ra text) (rb text))
;  (defstrand init 6 (a a) (b b) (ks ks) (ra ra) (rb rb))
;  (deflistener k)
;  (uniq-orig ra rb)
;  (non-orig (ltk a ks) (ltk b ks)))

(defskeleton neuman-stubblebine
  (vars (a name) (b name) (ks name) (ra text) (rb text) (k skey))
  (defstrand resp 6 (a a) (b b) (ks ks) (ra ra) (rb rb) (k k))
 ; (deflistener k)
  (uniq-orig ra rb)
  (non-orig (ltk a ks) (ltk b ks)))

;(defskeleton neuman-stubblebine
;  (vars (a name) (b name) (ks name) (ra text) (rb text))
;  (defstrand keyserver 2 (a a) (b b) (ks ks) (ra ra) (rb rb))
;  (uniq-orig ra rb)
;  (non-orig (ltk a ks) (ltk b ks)))
