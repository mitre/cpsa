(comment
 (defrole keyserver
   (vars (a name) (b name) (ks name) (t text) (l text) (sk kas kbs skey))
   (trace
    (recv (cat a b))
    (guar (and (long-term-key ks a kas)
	       (long-term-key ks b kbs)))
    (send
     (cat (enc (cat t l sk b) kas)
	  (enc (cat t l sk a) kbs))))
   (uniq-orig sk)))





(herald "ALternate Needham-Schroeder Public-Key Protocol Variants")

(defprotocol ns basic
  (defrole init
    (vars (a b name) (n1 n2 text))
    (trace
     (send (enc n1 a (pubk b)))
     (recv (enc n1 n2 b (pubk a)))
     (send (enc n2 (pubk b))))
    (facts (rel1 n1 n2)
	   (rel2 n1 n2)))
  (defrole resp
    (vars (b a name) (n2 n1 text))
    (trace
     (recv (enc n1 a (pubk b)))
     (send (enc n1 n2 b (pubk a)))
     (recv (enc n2 (pubk b)))))

  (defrule rebind-x 			; This rule tests rebinding in the conclusion of a rule.  
    (forall
     ((x y text))
     (implies
      (fact rel1 x y)
      (exists ((x name)) (fact rel2 x y)))))
  
  (comment "Needham-Schroeder with no role origination assumptions"))

;;; The initiator point-of-view
(defskeleton ns
  (vars (a b name) (n1 text))
  (defstrand init 3 (a a) (b b) (n1 n1))
  (non-orig (privk b) (privk a))
  (uniq-orig n1)
  (comment "Initiator point-of-view"))

(defskeleton ns
  (vars (a b name) (n1 text))
  (defstrand init 3 (a a) (b b) (n1 n1))
  (non-orig (privk b) (privk a))
  (uniq-orig n1)
  (facts (rel n1 n1))
  (comment "Initiator point-of-view"))

(defskeleton ns
  (vars (a b name) (n1 text))
  (defstrand init 3 (a a) (b b) (n1 n1))
  (non-orig (privk b))
  (uniq-orig n1)
  (comment "Initiator point-of-view"))

(defskeleton ns
  (vars (a b name) (n1 text))
  (defstrand init 3 (a a) (b b) (n1 n1))
  (deflistener n1)
  (non-orig (privk b) (privk a))
  (uniq-orig n1)
  (comment "Initiator point-of-view"))

;;; Double initiator point-of-view
(defskeleton ns
  (vars (a b name) (n1 n1-0 text))
  (defstrand init 3 (a a) (b b) (n1 n1))
  (defstrand init 3 (a a) (b b) (n1 n1-0))
  (non-orig (privk b) (privk a))
  (uniq-orig n1 n1-0)
  (comment "Double initiator point-of-view"))

;;; Double initiator point-of-view, same nonce
(defskeleton ns
  (vars (a b name) (n1 text))
  (defstrand init 3 (a a) (b b) (n1 n1))
  (defstrand init 3 (a a) (b b) (n1 n1))
  (non-orig (privk b) (privk a))
  (uniq-orig n1)
  (comment "Double initiator point-of-view, same nonce"))

;;; The responder point-of-view
(defskeleton ns
  (vars (a name) (n2 text))
  (defstrand resp 3 (a a) (n2 n2))
  (non-orig (privk a))
  (uniq-orig n2)
  (comment "Responder point-of-view"))

