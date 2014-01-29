(defprotocol kerberos basic
  (defrole init
    (vars (a name) (b name) (ks name) (t text) (t-prime text) (l text) (k skey))
    (trace (send (cat a b))
      (recv
        (cat (enc (cat t l k b) (ltk a ks))
          (enc (cat t l k a) (ltk b ks))))
      (send (cat (enc (cat a t) k) (enc (cat t l k a) (ltk b ks))))
      (recv (enc t-prime k))))
  (defrole resp
    (vars (a name) (b name) (ks name) (t text) (t-prime text) (l text) (k skey))
    (trace (recv (cat (enc (cat a t) k) (enc (cat t l k a) (ltk b ks))))
      (send (enc t-prime k))))
  (defrole keyserver
    (vars (a name) (b name) (ks name) (t text) (l text) (k skey))
    (trace (recv (cat a b))
      (send
        (cat (enc (cat t l k b) (ltk a ks))
          (enc (cat t l k a) (ltk b ks))))) (uniq-orig k)))

; we'll observe two shapes resulting from these preskeletons
; because the keyserver can reverse a and b with no change
; in the protocol
(defskeleton kerberos
  (vars (a name) (b name) (ks name))
  (defstrand init 4 (a a) (b b) (ks ks))
  (non-orig (ltk a ks) (ltk b ks)))

(defskeleton kerberos
  (vars (a name) (b name) (ks name))
  (defstrand resp 2 (a a) (b b) (ks ks))
  (non-orig (ltk a ks) (ltk b ks)))

(defskeleton kerberos
  (vars (a name) (b name) (ks name))
  (defstrand keyserver 2 (a a) (b b) (ks ks))
  (non-orig (ltk a ks) (ltk b ks)))
