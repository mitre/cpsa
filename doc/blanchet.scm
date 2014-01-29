(herald "Blanchet's Simple Example Protocol"
  (comment "There is a flaw in this protocol by design"))

(defprotocol blanchet basic
  (defrole init
    (vars (a b name) (s skey) (d data))
    (trace
     (send (enc (enc s (privk a)) (pubk b)))
     (recv (enc d s))))
  (defrole resp
    (vars (a b name) (s skey) (d data))
    (trace
     (recv (enc (enc s (privk a)) (pubk b)))
     (send (enc d s))))
  (comment "Blanchet's protocol using named asymmetric keys"))

(defskeleton blanchet
  (vars (a b name) (s skey) (d data))
  (defstrand init 2 (a a) (b b) (s s) (d d))
  (non-orig (privk b))
  (uniq-orig s)
  (comment "Analyze from the initiator's perspective"))

(defskeleton blanchet
  (vars (a b name) (s skey) (d data))
  (defstrand init 2 (a a) (b b) (s s) (d d))
  (deflistener d)
  (non-orig (privk b))
  (uniq-orig s d)
  (comment "From the initiator's perspective, is the secret leaked?"))

(defskeleton blanchet
  (vars (a b name) (s skey) (d data))
  (defstrand resp 2 (a a) (b b) (s s) (d d))
  (non-orig (privk a) (privk b))
  (uniq-orig s)
  (comment "Analyze from the responder's perspective"))

(defskeleton blanchet
  (vars (a b name) (s skey) (d data))
  (defstrand resp 2 (a a) (b b) (s s) (d d))
  (deflistener d)
  (non-orig (privk a) (privk b))
  (uniq-orig s d)
  (comment "From the responders's perspective, is the secret leaked?"))

(defprotocol blanchet-fixed basic
  (defrole init
    (vars (a b name) (s skey) (d data))
    (trace
     (send (enc (enc s b (privk a)) (pubk b)))
     (recv (enc d s))))
  (defrole resp
    (vars (a b name) (s skey) (d data))
    (trace
     (recv (enc (enc s b (privk a)) (pubk b)))
     (send (enc d s))))
  (comment "Fixed Blanchet's protocol using named asymmetric keys"))

(defskeleton blanchet-fixed
  (vars (a b name) (s skey) (d data))
  (defstrand init 2 (a a) (b b) (s s) (d d))
  (non-orig (privk b))
  (uniq-orig s)
  (comment "Analyze from the initiator's perspective"))

(defskeleton blanchet-fixed
  (vars (a b name) (s skey) (d data))
  (defstrand init 2 (a a) (b b) (s s) (d d))
  (deflistener d)
  (non-orig (privk b))
  (uniq-orig s d)
  (comment "From the initiator's perspective, is the secret leaked?"))

(defskeleton blanchet-fixed
  (vars (a b name) (s skey) (d data))
  (defstrand resp 2 (a a) (b b) (s s) (d d))
  (non-orig (privk a) (privk b))
  (uniq-orig s)
  (comment "Analyze from the responder's perspective"))

(defskeleton blanchet-fixed
  (vars (a b name) (s skey) (d data))
  (defstrand resp 2 (a a) (b b) (s s) (d d))
  (deflistener d)
  (non-orig (privk a) (privk b))
  (uniq-orig s d)
  (comment "From the responders's perspective, is the secret leaked?"))
