(herald "Yahalom Protocol Without Forwarding" (bound 15))

(defprotocol yahalom basic
  (defrole init
    (vars (a b c name) (n-a n-b text) (k skey) (ch chan))
    (trace (send (cat a n-a))
	   (recv ch (cat a b k n-a n-b))
	   (send (enc n-b k))))
  (defrole resp
    (vars (b a c name) (n-a n-b text) (k skey) (ch1 ch2 chan))
    (trace (recv (cat a n-a))
	   (send ch1 (cat a b n-a n-b))
	   (recv ch2 (cat a b k))
	   (recv (enc n-b k))))
  (defrole serv
    (vars (c a b name) (n-a n-b text) (k skey) (ch1 ch2 ch3 chan))
    (trace (recv ch1 (cat a b n-a n-b))
	   (send ch3 (cat a b k n-a n-b))
	   (send ch2 (cat a b k)))
    (conf ch3 ch2)
    (auth ch2)
    (uniq-orig k)))

(defskeleton yahalom
  (vars (a b c name) (n-b text) (ch1 ch2 chan))
  (defstrand resp 4 (a a) (b b) (n-b n-b) (ch1 ch1) (ch2 ch2))
  (conf ch1)
  (uniq-orig n-b))

(defskeleton yahalom
  (vars (a b c name) (n-b text) (k skey) (ch1 ch2 chan))
  (defstrand resp 4 (a a) (b b) (n-b n-b) (k k) (ch1 ch1) (ch2 ch2))
  (deflistener k)
  (conf ch1 ch2)
  (auth ch2)
  (uniq-orig n-b))

(defskeleton yahalom
  (vars (a b c name) (n-b text) (k skey) (ch chan))
  (defstrand init 3 (ch ch))
  (auth ch)
  (conf ch))
