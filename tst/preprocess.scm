(herald "Pre-processing test example: modified NS with two responders")

(defprotocol ns basic
  (defrole init
    (vars (a b name) (n1 n2 n3 text))
    (trace
     (send (enc n1 a (pubk b)))
     (recv (enc n1 n2 n3 (pubk a)))
     (send (enc n2 n3 (pubk b))))
	(uniq-orig n1))
  (defrole resp
    (vars (a b name) (n1 n2 n3 text))
    (trace
     (recv (enc n1 a (pubk b)))
     (send (enc n1 n2 n3 (pubk a)))
     (recv (enc n2 n3 (pubk b))))
	(uniq-orig n2 n3))
  (comment "modified Needham-Schroeder with role origination assumptions"))

;;; The initiator and two entangled responders POV
(defskeleton ns
  (vars (a b name) (n1 n2 n3 n2p n3p text))
  (defstrand init 3 (a a) (b b) (n1 n1) (n2 n2) (n3 n3))
  (defstrand resp 3 (a a) (b b) (n1 n1) (n2 n2) (n3 n3p))
  (defstrand resp 3 (a a) (b b) (n1 n1) (n2 n2p) (n3 n3))
  (non-orig (privk b) (privk a))
)
