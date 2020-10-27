(herald "Needham-Schroeder-Lowe")

(defprotocol nsl basic
  (defrole init
    (vars (ch chan) (a b akey) (n1 n2 text))
    (trace
     (send ch (enc n1 a b))
     (recv ch (enc n1 n2 b a))
     (send ch (enc n2 b)))
    (uniq-orig n1)
    (inputs ch (invk a) a b)
    (outputs n1 n2))
  (defrole resp
    (vars (ch chan) (b a akey) (n2 n1 text))
    (trace
     (recv ch (enc n1 a b))
     (send ch (enc n1 n2 b a))
     (recv ch (enc n2 b)))
    (uniq-orig n2)
    (inputs ch (invk b) b a)
    (outputs n2 n1)))

;;; The initiator point-of-view
(defskeleton nsl
  (vars (a b akey))
  (defstrand init 3 (a a) (b b))
  (non-orig (invk b) (invk a)))

;;; The responder point-of-view
(defskeleton nsl
  (vars (a b akey))
  (defstrand resp 3 (a a) (b b))
  (non-orig (invk b) (invk a)))
