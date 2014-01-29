(herald "Wide-Mouth Frog Protocol from Scyther"
  (comment "This protocol has an infinite number of shapes"))

(defprotocol wide-mouth-frog basic
  (defrole init (vars (a b t name) (ta text) (k skey))
    (trace (send (cat a (enc a ta b k (ltk a t))))))
  (defrole resp (vars (a b t name) (k skey) (tb text))
    (trace (recv (enc t tb a k (ltk b t)))))
  (defrole ks (vars (a b t name) (k skey) (ta tb text))
    (trace (recv (cat a (enc a ta b k (ltk a t))))
	   (send (enc t tb a k (ltk b t))))))

(defskeleton wide-mouth-frog
  (vars (a t name) (k skey))
  (defstrand init 1 (a a) (t t) (k k))
  (non-orig (ltk a t))
  (uniq-orig k))

(defskeleton wide-mouth-frog
  (vars (b t name) (k skey))
  (defstrand resp 1 (b b) (t t) (k k))
  (non-orig (ltk b t))
  (uniq-orig k))

(defskeleton wide-mouth-frog
  (vars (a b t name) (k skey))
  (defstrand ks 2 (a a) (b b) (t t) (k k))
  (non-orig (ltk a t) (ltk b t))
  (uniq-orig k))
