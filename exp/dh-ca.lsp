(herald dhca (algebra diffie-hellman))

(defprotocol dhca diffie-hellman
  (defrole init (vars (x expn) (a b ca name) (h base) (n text))
    (trace
     (recv (enc (exp (gen) x) a (privk ca)))
     (send (cat (exp (gen) x) (enc (exp (gen) x) a (privk ca))))
     (recv (cat h (enc h b (privk ca)) (enc n (exp h x))))
     (send (enc "check" n (exp h x))))
    (non-orig (privk ca)))
  (defrole resp (vars (y expn) (a b ca name) (h base) (n text))
    (trace
     (recv (enc (exp (gen) y) b (privk ca)))
     (recv (cat h (enc h a (privk ca))))
     (send (cat (exp (gen) y) (enc (exp (gen) y) b (privk ca))
		(enc n (exp h y))))
     (recv (enc "check" n (exp h y))))
    (non-orig (privk ca)))
  (defrole ca (vars (subject ca name) (z expn))
    (trace
     (send (enc (exp (gen) z) subject (privk ca)) ))
    (non-orig z))
  (comment "A diffie-hellman exchange which uses a certificate"
    "authority to certify long-term DH values.")
)

(defskeleton dhca
  (vars )
  (defstrand init 4 )
(comment "Full initiator point-of-view.  No need to make extra assumptions."))

(defskeleton dhca
  (vars (n text))
  (defstrand resp 4 (n n))
  (uniq-orig n)
  (comment "Full responder point of view with freshly chosen n")
)

(defskeleton dhca
  (vars (a b ca name) (x y expn) (n text))
  (defstrand init 4 (x x) (h (exp (gen) y)) (ca ca) (a a) (b b) (n n))
  (defstrand resp 4 (y y) (h (exp (gen) x)) (ca ca) (a a) (b b) (n n))
(uniq-orig n)
(comment "point of view in which init and resp each complete and"
    "they agree on the relevant parameters.")
)
