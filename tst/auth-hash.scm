(herald auth-hash)

(defprotocol auth-hash basic
  (defrole init
    (vars (n text) (ch chan))
    (trace (send ch (hash n)) (send ch n))
    (uniq-orig n)
    (inputs ch))
  (defrole resp
    (vars (n text) (ch chan))
    (trace (recv ch (hash n)) (recv ch n))
    (inputs ch)
    (outputs n)))

(defskeleton auth-hash
  (vars (ch chan))
  (defstrand resp 2 (ch ch))
  (auth ch))
