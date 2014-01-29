; uniq-orig
;   Shows that our notion of uniquely-originating
; does not necessarily correspond to the notion of
; a freshly-generated nonce, because such values can
; be used in non-carried positions before they are
; received.  Here, the initiator originates n in its
; message but no problem is detected with a responder
; that sends a message encrypted under n as its first
; message, before receiving n.

(defprotocol uniq-orig basic
  (defrole init
    (vars (n text))
    (trace (send n))
    (uniq-orig n))
  (defrole resp
    (vars (m n text))
    (trace
     (send (enc m n))
     (recv n))))

(defskeleton uniq-orig
  (vars (n text))
  (defstrand init 1 (n n))
  (defstrand resp 2 (n n)))
