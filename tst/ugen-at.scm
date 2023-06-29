(herald uniq-at)

(defprotocol yahalom-plus-uniq-at basic 

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
    (uniq-gen k))

  (defrule uniq-at
    (forall
     ((z strd) (i indx) (v mesg))
     (implies (uniq-at v z i)
	      (fact remember v z))))

  (defrule ugen-at
    (forall
     ((z strd) (i indx) (v mesg))
     (implies (ugen-at v z i)
	      (fact remember-gen v z)))))

(defskeleton yahalom-plus-uniq-at
  (vars (a b c name) (n-b text) (k skey))
  (defstrand resp 5 (a a) (b b) (c c) (n-b n-b) (k k))
  (deflistener k)
  (non-orig (ltk b c) (ltk a c))
  (uniq-gen n-b))

(defskeleton yahalom-plus-uniq-at
  (vars (a b c name) (n-a text))
  (defstrand init 3 (n-a n-a) (a a) (b b) (c c))
  (non-orig (ltk b c) (ltk a c))
  (uniq-gen n-a))





  
