(herald "Corrected Blanchet's Simple Example Protocol")

(defprotocol blanchet-fixed basic
  (defrole init
    (vars (a b name) (s skey) (d data) (ch chan))
    (trace
     (send ch (enc (enc s b (privk a)) (pubk b)))
     (recv ch (enc d s)))
    (uniq-orig s)
    (inputs ch b (privk a) (pubk b))
    (outputs d s))
  (defrole resp
    (vars (a b name) (s skey) (d data) (ch chan))
    (trace
     (recv ch (enc (enc s b (privk a)) (pubk b)))
     (send ch (enc d s)))
    (uniq-orig d)
    (inputs ch b (pubk a) (privk b))
    (outputs d s))
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
