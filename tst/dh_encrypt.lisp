(herald dhencrypt (algebra diffie-hellman))

(defprotocol dhencrypt diffie-hellman
  (defrole init (vars (x exp) (h base) (n text))
    (trace
     (send (expn (gen) x))
     (recv (cat h (enc n (expn h x))))
     (send (enc "check" n (expn h x)))
    )
    (non-orig x)
  )
  (defrole resp (vars (y exp) (h base) (n text))
    (trace
     (recv h)
     (send (cat (expn (gen) y) (enc n (expn h y))))
     (recv (enc "check" n (expn h y)))
    )
    (non-orig y)
    (uniq-orig n)
  )
  (comment "Diffie-hellman key exchange followed by an encrypted-nonce challenge/response")
)

(defskeleton dhencrypt
   (vars (x exp) (h base) (n text))
   (defstrand init 3 (x x) (h h) (n n))
   (comment "Initiator full point of view")
)

(defskeleton dhencrypt
   (vars (y exp) (h base) (n text))
   (defstrand resp 3 (y y) (h h) (n n))
   (comment "Responder full point of view")
)

(defskeleton dhencrypt
   (vars (x y exp) (n text))
   (defstrand init 2 (x x) (h (expn (gen) y)) (n n))
   (defstrand resp 3 (y y) (h (expn (gen) x)) (n n))
   (comment "Point of view where the natural result should be the only shape")
)
