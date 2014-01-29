; uncarried-keys
;   Shows that our notion of uniquely-originating
; does not necessarily correspond to the notion of
; a freshly-generated nonce, because such values can
; be used in non-carried positions before they are
; received.  Here, the initiator originates K in its
; 4th message but receives (earlier) a message
; encrypted with K from the responder.

(defprotocol uncarried-keys basic
  (defrole init
    (vars (a text) (A B name) (K akey))
    (trace
     (send (enc "start" a A B (pubk B)))
     (recv (enc a A B (pubk A)))
     (send (enc a K (pubk B)))
     (recv (enc a A B K)))
    (non-orig (privk B) (invk K))
    (uniq-orig a K))
  (defrole resp
    (vars (a text) (A B name) (K akey))
    (trace
     (recv (enc "start" a A B (pubk B)))
     (send (enc a A B (pubk A)))
     (recv (enc a K (pubk B)))
     (send (enc a A B K)))))

(defskeleton uncarried-keys
  (vars (a text) (A B name) (K akey))
  (defstrand init 4 (a a) (A A) (B B) (K K)))
