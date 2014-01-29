(herald "Kerberos PK init")

(defprotocol pkinit basic
  (defrole client
    (vars (c t as name) (n2 n1 text) (tc tk tgt data) (k ak skey))
    (trace (send (cat (enc tc n2 (privk c)) c t n1))
      (recv
        (cat (enc (enc k n2 (privk as)) (pubk c)) c tgt
          (enc ak n1 tk t k))))
    (uniq-orig n1 n2))
  (defrole auth
    (vars (c t as name) (n2 n1 text) (tc tk tgt data) (k ak skey))
    (trace (recv (cat (enc tc n2 (privk c)) c t n1))
      (send
        (cat (enc (enc k n2 (privk as)) (pubk c)) c tgt
          (enc ak n1 tk t k))))
    (uniq-orig k ak)))

(defskeleton pkinit
  (vars (c as name))
  (defstrand client 2 (c c) (as as))
  (non-orig (privk c) (privk as)))
