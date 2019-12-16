(herald "Blanchet's Simple Example Protocol"
	(comment "There is a flaw in this protocol by design")
	(comment "It also shows how variable renaming works"))

(defprotocol blanchet basic
  (defrole init
    (vars (a b name) (s skey) (d data))
    (trace
     (send (enc (enc s (privk a)) (pubk b)))
     (recv (enc d s))))
  (defrole resp
    (vars (d a name) (b skey) (s data))
    (trace
     (recv (enc (enc b (privk d)) (pubk a)))
     (send (enc s b))))
  (comment "Blanchet's protocol using named asymmetric keys"))

(defskeleton blanchet
  (vars (s d name) (a skey) (b data))
  (defstrand resp 2 (d s) (a d) (b a) (s b))
  (non-orig (privk s) (privk d))
  (uniq-orig a)
  (comment "Analyze from the responder's perspective"))

(defskeleton blanchet
  (vars (s d name) (a skey) (b data))
  (defstrand init 2 (a s) (b d) (s a) (d b))
  (non-orig (privk d))
  (uniq-orig a)
  (comment "Analyze from the initiator's perspective"))
