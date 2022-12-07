(herald "Yahalom Protocol Without Forwarding" (bound 15))

(defprotocol yahalom basic
  (defrole init
    (vars (a b c name) (n-a n-b text) (k skey) (ch3 chan))
    (trace (send (cat a n-a))
	   (recv ch3 (cat a b k n-a n-b))
	   (send (enc n-b k)))
    (auth ch3))
  (defrole resp
    (vars (b a c name) (n-a n-b text) (k skey) (ch1 ch2 chan))
    (trace (recv (cat a n-a))
	   (send ch1 (cat a b n-a n-b))
	   (recv ch2 (cat a b k))
	   (recv (enc n-b k)))
    (auth ch2))
  (defrole serv
    (vars (c a b name) (n-a n-b text) (k skey) (ch1 ch2 ch3 chan))
    (trace (recv ch1 (cat a b n-a n-b))
	   (send ch3 (cat a b k n-a n-b))
	   (send ch2 (cat a b k)))
    (conf ch3 ch2)
    (uniq-orig k)))

;;; How much do we know assuming that the resp had a run, which
;;; because of the role declaration is necessarily using an
;;; authenticated channel ch2?  We also assume the responder's nonce
;;; is freshly chosen.

(defskeleton yahalom
  (vars (a b c name) (n-b text) (ch1 ch2 chan))
  (defstrand resp 4 (n-b n-b))
  (uniq-orig n-b))

(defskeleton yahalom
  (vars (a b c name) (k skey) (n-b text) (ch1 ch2 chan))
  (defstrand resp 4 (k k) (n-b n-b))
  (deflistener k)
  (uniq-orig n-b))

;;; Let's turn now to the initiator's point of view:

(defskeleton yahalom
  (vars (a b c name) (n-a text) (k skey) (ch3 chan))
  (defstrand init 3 (n-a n-a))
  (uniq-orig n-a))

(defskeleton yahalom
  (vars (a b c name) (n-a text) (k skey) (ch3 chan))
  (defstrand init 3 (k k))
  (deflistener k))

(defskeleton yahalom
  (vars (a b c name) (n-a text) (k skey) (ch3 chan))
  (defstrand init 3 (k k) (n-a n-a))
  (defstrand resp 3 (k k))
  (uniq-orig n-a))

(defskeleton yahalom
  (vars (a b c name) (n-a text) (k skey) (ch3 chan))
  (defstrand init 3 (k k) (n-a n-a))
  (defstrand resp 4 (k k))
  (uniq-orig n-a))

;;; Finally, the server knows only that the responder has requested a
;;; session key.

(defskeleton yahalom
  (vars (c a b name) (n-a n-b text) (k skey) (ch1 ch2 ch3 chan))
  (defstrand serv 3))

;;; However, the server can be sure that the session key will not be
;;; disclosed.

(defskeleton yahalom
  (vars (c a b name) (n-a n-b text) (k skey) (ch1 ch2 ch3 chan))
  (defstrand serv 3 (k k))
  (deflistener k))
