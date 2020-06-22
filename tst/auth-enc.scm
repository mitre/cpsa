(herald auth-enc)

(defprotocol auth-enc basic
  (defrole init
    (vars (n text) (k skey) (ch chan))
    (trace (send ch (enc n k)) (send ch (cat n k)))
    (uniq-orig n k)
    (inputs ch))
  (defrole resp
    (vars (n text) (k skey) (ch chan))
    (trace (recv ch (enc n k)) (recv ch (cat n k)))
    (inputs ch)
    (outputs n)))

(defskeleton auth-enc
  (vars (ch chan))
  (defstrand resp 2 (ch ch))
  (auth ch))
