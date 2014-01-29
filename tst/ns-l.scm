(herald "Needham-Schroeder-Low Public-Key Protocol"
	(comment "With deflistener's"))

;;; Used to generate output for inclusion in the primer.
;;; Use margin = 60 (-m 60) to generate the output.

(defprotocol ns basic
  (defrole init
    (vars (a b name) (n1 n2 text))
    (trace
     (send (enc n1 a (pubk b)))
     (recv (enc b n1 n2 (pubk a)))
     (send (enc n2 (pubk b)))))
  (defrole resp
    (vars (b a name) (n2 n1 text))
    (trace
     (recv (enc n1 a (pubk b)))
     (send (enc b n1 n2 (pubk a)))
     (recv (enc n2 (pubk b)))))
  (comment "Needham-Schroeder"))

;;; The initiator point-of-view
(defskeleton ns
  (vars (a b name) (n1 text))
  (defstrand init 3 (a a) (b b) (n1 n1))
  (deflistener n1)
  (non-orig (privk b) (privk a))
  (uniq-orig n1)
  (comment "Initiator point-of-view with a listener"))

;;; The responder point-of-view
(defskeleton ns
  (vars (a name) (n2 text))
  (defstrand resp 3 (a a) (n2 n2))
  (deflistener n2)
  (non-orig (privk a))
  (uniq-orig n2)
  (comment "Responder point-of-view with a listener"))
