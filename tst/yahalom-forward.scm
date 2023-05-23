(herald "Yahalom Protocol With Forwarding" (bound 15))

(defprotocol yahalom basic
  (defrole init
    (vars (a b c name) (n-a n-b text) (k skey))
    (trace (send (cat a n-a))
	   (recv (enc b k n-a n-b (ltk a c)))
	   (send (enc n-b k))))
  (defrole resp
    (vars (b a c name) (n-a n-b text) (rest mesg) (k skey))
    (trace (recv (cat a n-a))
	   (send (cat b (enc a n-a n-b (ltk b c))))
	   (recv (cat (enc a k (ltk b c)) rest))
	   (send rest) 
	   (recv (enc n-b k))))
  (defrole serv
    (vars (c a b name) (n-a n-b text) (k skey))
    (trace (recv (cat b (enc a n-a n-b (ltk b c))))
	   (send (cat (enc a k (ltk b c))
		      (enc b k n-a n-b (ltk a c)))))
    (uniq-orig k)))

(defskeleton yahalom
  (vars (a b c name) (n-b text))
  (defstrand resp 5 (a a) (b b) (c c) (n-b n-b))
  (non-orig (ltk b c) (ltk a c))
  (uniq-orig n-b))

;;; Ensure encryption key remains secret.
(defskeleton yahalom
  (vars (a b c name) (n-b text) (k skey))
  (defstrand resp 5 (a a) (b b) (c c) (n-b n-b) (k k))
  (deflistener k)
  (non-orig (ltk b c) (ltk a c))
  (uniq-orig n-b))

(defskeleton yahalom
  (vars (a b c name) (n-a text))
  (defstrand init 3 (n-a n-a) (a a) (b b) (c c))
  (non-orig (ltk b c) (ltk a c))
  (uniq-orig n-a))
