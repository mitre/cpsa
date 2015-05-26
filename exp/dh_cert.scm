(herald "Diffie-Hellman with Certificate" (algebra diffie-hellman))

(defmacro (cert p ps-ltv)
  (enc "cert" p (exp (gen) ps-ltv) (privk "certify" ca)))

(defmacro (hash x) (enc "hash" x))

(defprotocol dh-cert diffie-hellman
  (defrole ca
    (vars (p ca name) (ps-ltv expn))
    (trace (send (cert p ps-ltv)))
    (uniq-orig ps-ltv))
  (defrole init
    (vars (a b ca name) (as-ltv bs-ltv x expn) (gB gy base) (hk akey))
    (trace (send (cat (exp (gen) as-ltv) (cert a as-ltv) (exp (gen) x)))
      (recv (cat gB (cert b bs-ltv) gy))
      (send
        (enc "tag1"
          (cat (exp (gen) as-ltv) (cert a as-ltv) (exp (gen) x))
          (cat gB (cert b bs-ltv) gy)
          (hash (cat (exp gB x) (exp gy as-ltv)))))
      (recv
        (enc "tag2"
          (cat (exp (gen) as-ltv) (cert a as-ltv) (exp (gen) x))
          (cat gB (cert b bs-ltv) gy)
          (hash (cat (exp gB x) (exp gy as-ltv))))))
    (uniq-orig as-ltv x))
  (defrole resp
    (vars (a b ca name) (bs-ltv as-ltv y expn) (gB gA gx base)
      (hk akey))
    (trace (recv (cat gA (cert a as-ltv) gx))
      (send (cat (exp (gen) bs-ltv) (cert b bs-ltv) (exp (gen) y)))
      (recv
        (enc "tag1" (cat gA (cert a as-ltv) gx)
          (cat (exp (gen) bs-ltv) (cert b bs-ltv) (exp (gen) y))
          (hash (cat (exp gx bs-ltv) (exp gA y)))))
      (send
        (enc "tag2" (cat gA (cert a as-ltv) gx)
          (cat (exp (gen) bs-ltv) (cert b bs-ltv) (exp (gen) y))
          (hash (cat (exp gx bs-ltv) (exp gA y))))))
    (uniq-orig bs-ltv y)))

(defskeleton dh-cert
  (vars (ca name))
  (defstrand init 4 (ca ca))
  (non-orig (privk ca)))

(defskeleton dh-cert
  (vars (ca name))
  (defstrand resp 4 (ca ca))
  (non-orig (privk ca)))
