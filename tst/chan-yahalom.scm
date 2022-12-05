(herald "Yahalom Protocol Without Forwarding" (bound 15))

(defprotocol yahalom basic
  (defrole init
    (vars (a b c name) (n-a n-b text) (k skey) (ch3 chan))
    (trace (send (cat a n-a))
	   (recv ch3 (cat a b k n-a n-b))
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
    (uniq-orig k)))

;;; How much do we know assuming that the resp had a run with an
;;; authenticated channel ch2?  We also assume the responder's nonce
;;; is freshly chosen.

(defskeleton yahalom
  (vars (a b c name) (n-b text) (ch1 ch2 chan))
  (defstrand resp 4 (a a) (b b) (n-b n-b) (ch1 ch1) (ch2 ch2))
  (auth ch2)
  (uniq-orig n-b))

;;; This is the answer to the previous question, to which we have
;;; added the assumptions that ch2 and ch3, used by the key server to
;;; distribute the key, are confidential channels.  In this case, we
;;; find *almost* all we would expect.

(defskeleton yahalom
  (vars (k skey) (n-b n-a n-a-0 n-b-0 text) (a b name)
    (ch1 ch2 ch1-0 ch3 chan))
  (defstrand resp 4 (k k) (n-a n-a) (n-b n-b) (b b) (a a) (ch1 ch1)
    (ch2 ch2))
  (defstrand serv 3 (k k) (n-a n-a-0) (n-b n-b-0) (a a) (b b)
    (ch1 ch1-0) (ch2 ch2) (ch3 ch3))
  (precedes ((1 2) (0 2)))
  (uniq-orig k n-b)
  (auth ch2)
  (conf ch2 ch3))

;;; This is the answer to the previous question, together with the
;;; assumption that the server's request channel is an authenticated
;;; channel.  This yields all of the desired result, including the
;;; fact that the channels used by the server and the responder agree:
;;; ch1-0 = ch1.

(defskeleton yahalom
  (vars (k skey) (n-b n-a n-a-0 n-b-0 text) (a b name)
    (ch1 ch2 ch1-0 ch3 chan))
  (defstrand resp 4 (k k) (n-a n-a) (n-b n-b) (b b) (a a) (ch1 ch1)
    (ch2 ch2))
  (defstrand serv 3 (k k) (n-a n-a-0) (n-b n-b-0) (a a) (b b)
    (ch1 ch1-0) (ch2 ch2) (ch3 ch3))
  (uniq-orig k n-b)
  (auth ch2 ch1-0)
  (conf ch2 ch3))

;;; In particular, we can now check that the session key cannot be
;;; compromised, subject to the assumptions we have imposed, using
;;; (deflistener k).

(defskeleton yahalom
  (vars (k skey) (n-b n-a n-a-0 n-b-0 text) (a b name)
    (ch1 ch2 ch1-0 ch3 chan))
  (defstrand resp 4 (k k) (n-a n-a) (n-b n-b) (b b) (a a) (ch1 ch1)
    (ch2 ch2))
  (defstrand serv 3 (k k) (n-a n-a-0) (n-b n-b-0) (a a) (b b)
    (ch1 ch1-0) (ch2 ch2) (ch3 ch3))
  (deflistener k)
  (uniq-orig k n-b)
  (auth ch2 ch1-0)
  (conf ch2 ch3))

;;; Let's turn now to the initiator's point of view:

(defskeleton yahalom
  (vars (a b c name) (n-a text) (k skey) (ch3 chan))
  (defstrand init 3 (ch3 ch3) (n-a n-a))
  (uniq-orig n-a)
  (auth ch3))

;;; The initiator infers the presence of the server.  We can now add
;;; the assumptions that the server's channels -- ch1 and ch, here --
;;; have the same trust properties as before, ie ch1 is auth and ch is
;;; conf, in addition to the auth previously assumed:

(defskeleton yahalom
  (vars (k skey) (n-a n-b text) (a b name) (ch3 ch3-0 ch1 chan))
  (defstrand init 3 (k k) (n-a n-a) (n-b n-b) (a a) (b b) (ch3 ch3))
  (defstrand serv 2 (k k) (n-a n-a) (n-b n-b) (a a) (b b) (ch1 ch1)
    (ch3 ch3-0))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (uniq-orig k n-a)
  (auth ch3 ch1)
  (conf ch3-0))

;;; This now authenticates the presence of the responder for the first
;;; two nodes, and its agreement on all of the values present there.

;;; Finally, let us consider the server's point of view, with an
;;; authenticated channel for the request, and confidential channels
;;; over which to transmit the session key.

(defskeleton yahalom
  (vars (c a b name) (n-a n-b text) (k skey) (ch1 ch2 ch3 chan))
  (defstrand serv 3 (ch1 ch1) (ch2 ch2) (ch3 ch3))
  (auth ch1)
  (conf ch2 ch3))

;;; This query confirms that the server has authenticated the first
;;; two nodes of the responder, but has not authenticated the
;;; initiator at all.

;;; However, the session key is safe:

(defskeleton yahalom
  (vars (c a b name) (n-a n-b text) (k skey) (ch1 ch2 ch3 chan))
  (defstrand serv 3 (k k) (ch1 ch1) (ch2 ch2) (ch3 ch3))
  (deflistener k)
  (auth ch1)
  (conf ch2 ch3))
