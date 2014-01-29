(defprotocol neuman-stubblebine basic
  (defrole init (vars (a b ks name) (ra rb text) (k skey) (tb text))
    (trace
     (send (cat a ra))
     (recv (cat (enc b ra k tb (ltk a ks))
		(enc a k tb (ltk b ks)) rb))
     (send (cat (enc a k tb (ltk b ks)) (enc rb k)))))
  (defrole resp (vars (a b ks name) (ra rb text) (k skey) (tb text))
    (trace
     (recv (cat a ra))
     (send (cat b rb (enc a ra tb (ltk b ks))))
     (recv (cat (enc a k tb (ltk b ks)) (enc rb k)))))
  (defrole keyserver
    (vars (a b ks name) (ra rb text) (k skey) (tb text))
    (trace
     (recv (cat b rb (enc a ra tb (ltk b ks))))
     (send (cat (enc b ra k tb (ltk a ks))
		(enc a k tb (ltk b ks)) rb)))
    (uniq-orig k)))

(defskeleton neuman-stubblebine
  (vars (a b ks name) (ra rb text))
  (defstrand init 3 (a a) (b b) (ks ks) (ra ra) (rb rb))
  (uniq-orig ra rb)
  (non-orig (ltk a ks) (ltk b ks)))

(defskeleton neuman-stubblebine
  (vars (a b ks name) (ra rb text))
  (defstrand resp 3 (a a) (b b) (ks ks) (ra ra) (rb rb))
  (uniq-orig ra rb)
  (non-orig (ltk a ks) (ltk b ks)))

(defskeleton neuman-stubblebine
  (vars (a b ks name) (ra rb text))
  (defstrand keyserver 2 (a a) (b b) (ks ks) (ra ra) (rb rb))
  (uniq-orig ra rb)
  (non-orig (ltk a ks) (ltk b ks)))
