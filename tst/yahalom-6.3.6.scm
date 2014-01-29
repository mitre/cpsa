(herald "Yahalom Protocol"
  (comment "A Survey of Authentication Protocol Literature:"
	   "Version 1.0, John Clark and Jeremy Jacob,"
	   "Yahalom Protocol, Section 6.3.6, Page 49")
  (url "http://www.eecs.umich.edu/acal/swerve/docs/49-1.pdf")
  (bound 15))

(defprotocol yahalom basic
  (defrole init
    (vars (a b s name) (n-a n-b text) (k skey) (blob mesg))
    (trace
     (send (cat a n-a))
     (recv (cat (enc b k n-a n-b (ltk a s)) blob))
     (send (cat blob (enc n-b k)))))
  (defrole resp
    (vars (a b s name) (n-a n-b text) (k skey))
    (trace
     (recv (cat a n-a))
     (send (cat b (enc a n-a n-b (ltk b s))))
     (recv (cat (enc a k (ltk b s)) (enc n-b k)))))
  (defrole serv
    (vars (a b s name) (n-a n-b text) (k skey))
    (trace
     (recv (cat b (enc a n-a n-b (ltk b s))))
     (send (cat (enc b k n-a n-b (ltk a s)) (enc a k (ltk b s)))))
    (uniq-orig k))
  (comment "Yahalom protocol, Section 6.3.6, Page 49")
  (url "http://www.eecs.umich.edu/acal/swerve/docs/49-1.pdf"))

(defskeleton yahalom
  (vars (a b s name) (n-a n-b text))
  (defstrand init 3 (a a) (b b) (s s) (n-a n-a) (n-b n-b))
  (non-orig (ltk a s) (ltk b s))
  (uniq-orig n-a n-b))

(defskeleton yahalom
  (vars (a b s name) (n-a n-b text) (k skey))
  (defstrand resp 3 (a a) (b b) (s s) (n-a n-a) (n-b n-b) (k k))
  (deflistener k)
  (non-orig (ltk a s) (ltk b s))
  (uniq-orig n-a n-b))

(defskeleton yahalom
  (vars (a b s name) (n-a n-b text))
  (defstrand resp 3 (a a) (b b) (s s) (n-a n-a) (n-b n-b))
  (non-orig (ltk a s) (ltk b s))
  (uniq-orig n-a n-b))

(defskeleton yahalom
  (vars (a b s name) (n-a n-b text))
  (defstrand serv 2 (a a) (b b) (s s) (n-a n-a) (n-b n-b))
  (non-orig (ltk a s) (ltk b s))
  (uniq-orig n-a n-b))
