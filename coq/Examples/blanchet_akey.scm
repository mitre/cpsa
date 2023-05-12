(herald blanchet-akey-fixed)

(defprotocol blanchet-akey-fixed basic
  (defrole init
    (vars (ch chan) (a b akey) (s skey) (d data))
    (trace
     (send ch (enc (enc b s (invk a)) b))
     (recv ch(enc d s)))
    (uniq-orig s)
    (inputs ch b (invk a))
    (outputs d s))
  (defrole resp
    (vars (ch chan) (a b akey) (s skey) (d data))
    (trace
     (recv ch (enc (enc b s (invk a)) b))
     (send ch (enc d s)))
    (uniq-orig d)
    (inputs ch a (invk b))
    (outputs d s))
  (comment "Blanchet's protocol using unnamed asymmetric keys"))

(defskeleton blanchet-akey-fixed
  (vars (b akey))
  (defstrand init 2 (b b))
  (non-orig (invk b))
  (comment "Analyze from the initiator's perspective"))

(defskeleton blanchet-akey-fixed
  (vars (b akey) (d data))
  (defstrand init 2 (b b) (d d))
  (deflistener d)
  (non-orig (invk b))
  (uniq-orig d)
  (comment "From the initiator's perspective, is the secret leaked?"))

(defskeleton blanchet-akey-fixed
  (vars (a b akey))
  (defstrand resp 2 (a a) (b b))
  (non-orig (invk a) (invk b))
  (comment "Analyze from the responder's perspective"))

(defskeleton blanchet-akey-fixed
  (vars (a b akey) (s skey) (d data))
  (defstrand resp 2 (a a) (b b) (s s) (d d))
  (deflistener d)
  (non-orig (invk a) (invk b))
  (uniq-orig s)
  (comment "From the responders's perspective, is the secret leaked?"))
