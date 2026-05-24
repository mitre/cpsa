(herald "Yahalom Protocol Without Forwarding" (bound 15)
	(comment "Testing channels as arbitrary messages."))

(defprotocol yahalom basic
  (defrole init
    (vars (a b c name) (n-a n-b text) (k skey))
    (trace (send (cat a n-a))
	   (recv (cat c a) (cat a b k n-a n-b))
	   (send (enc n-b k))))
  (defrole resp
    (vars (b a c name) (n-a n-b text) (k skey) (ch1 ch2 chan))
    (trace (recv (cat a n-a))
	   (send (cat b c) (cat a b n-a n-b))
	   (recv (cat c b) (cat a b k))
	   (recv (enc n-b k))))
  (defrole serv
    (vars (c a b name) (n-a n-b text) (k skey) (ch1 ch2 ch3 chan))
    (trace (recv (cat b c) (cat a b n-a n-b))
	   (send (cat c a) (cat a b k n-a n-b))
	   (send (cat c b) (cat a b k)))
    (uniq-orig k))
  (comment "Use (cat x y) as channel from x to y. Matching channel should force matching names."))

;;; How much do we know assuming that the resp had a run with an
;;; authenticated channel ch2?  We also assume the responder's nonce
;;; is freshly chosen.

(defskeleton yahalom
  (vars (a b c name) (n-b text))
  (defstrand resp 4 (a a) (b b) (c c) (n-b n-b))
  (auth (cat c b))
  (uniq-orig n-b))

;;; This is the answer to the previous question, to which we have
;;; added the assumptions ...

(defskeleton yahalom
  (vars (k skey) (n-b n-a n-a-0 n-b-0 text) (a b c name))
  (defstrand resp 4 (k k) (n-a n-a) (n-b n-b) (b b) (a a) (c c))
  (defstrand serv 3 (k k) (n-a n-a-0) (n-b n-b-0) (c c) (a a) (b b))
  (precedes ((1 2) (0 2)))
  (uniq-orig k n-b)
  (auth (cat c b))
  (conf (cat c b) (cat c a)))


;;; This is the ...
(defskeleton yahalom
  (vars (k skey) (n-b n-a n-a-0 n-b-0 text) (a b c name))
  (defstrand resp 4 (k k) (n-a n-a) (n-b n-b) (b b) (a a) (c c))
  (defstrand serv 3 (k k) (n-a n-a-0) (n-b n-b-0) (c c) (a a) (b b))
  (uniq-orig k n-b)
  (auth (cat c b) (cat b c))
  (conf (cat c b) (cat c a)))

;;; In particular, we can now check that the session key cannot be
;;; compromised, subject to the assumptions we have imposed, using
;;; (deflistener k).

(defskeleton yahalom
  (vars (k skey) (n-b n-a n-a-0 n-b-0 text) (a b c name))
  (defstrand resp 4 (k k) (n-a n-a) (n-b n-b) (b b) (a a) (c c))
  (defstrand serv 3 (k k) (n-a n-a-0) (n-b n-b-0) (c c) (a a) (b b))
  (deflistener k)
  (uniq-orig k n-b)
  (auth (cat c b) (cat b c))
  (conf (cat c b) (cat c a)))

;;; Let's turn now to the initiator's point of view:

(defskeleton yahalom
  (vars (a b c name) (n-a text) (k skey))
  (defstrand init 3 (n-a n-a) (c c) (a a))
  (uniq-orig n-a)
  (auth (cat c a)))

;;; The initiator infers the presence of the server.  We can now add
;;; the assumptions that the server's channels
;;; have the same trust properties as before, ie ch1 is auth and ch is
;;; conf, in addition to the auth previously assumed:
(defskeleton yahalom
  (vars (k skey) (n-a n-b text) (a c b c-0 name))
  (defstrand init 3 (k k) (n-a n-a) (n-b n-b) (a a) (b b) (c c))
  (defstrand serv 2 (k k) (n-a n-a) (n-b n-b) (c c-0) (a a) (b b))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (uniq-orig k n-a)
  (auth (cat c a) (cat b c-0))
  (conf (cat c-0 a)))

;;; This now authenticates the presence of the responder for the first
;;; two nodes, and its agreement on all of the values present there.

;;; Finally, let us consider the server's point of view, with an
;;; authenticated channel for the request, and confidential channels
;;; over which to transmit the session key.

(defskeleton yahalom
  (vars (c a b name) (n-a n-b text) (k skey))
  (defstrand serv 3 (a a) (b b) (c c))
  (auth (cat b c))
  (conf (cat c b) (cat c a)))

;;; This query confirms that the server has authenticated the first
;;; two nodes of the responder, but has not authenticated the
;;; initiator at all.

;;; However, the session key is safe:

(defskeleton yahalom
  (vars (c a b name) (n-a n-b text) (k skey))
  (defstrand serv 3 (k k) (a a) (b b) (c c))
  (deflistener k)
  (auth (cat b c))
  (conf (cat c b) (cat c a)))
