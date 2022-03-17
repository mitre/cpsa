(herald cert-lang)

(defprotocol cert-uni basic
  (defrole certify
    (vars (ch chan) (subj ca name) (pk akey) (serial data))
    (trace
      (send ch
        (cert (cert-body subj serial pk) (privk "cert" ca))))
    (inputs ch subj pk serial (privk "cert" ca)))
  (defrole init
    (vars (ch-ca ch-r chan) (subj ca name) (pk akey)
      (serial data) (chal text))
    (trace
      (recv ch-ca
        (cert (cert-body subj serial pk) (privk "cert" ca)))
      (send ch-r (enc "challenge" chal pk))
      (recv ch-r chal))
    (uniq-orig chal)
    (inputs ch-ca ch-r subj (pubk "cert" ca))
    (outputs chal))
  (defrole resp
    (vars (ch-ca ch-i chan) (subj ca name) (pk akey)
      (serial data) (chal text))
    (trace
      (recv ch-ca
        (cert (cert-body subj serial pk) (privk "cert" ca)))
      (recv ch-i (enc "challenge" chal pk))
      (send ch-i chal))
    (inputs ch-ca ch-i subj (pubk "cert" ca) (invk pk))
    (outputs chal))
  (defrule certified-keys-uncompromised
    (forall ((zca strd) (subj ca name) (pk akey))
      (implies
        (and (p "certify" zca 1)
          (p "certify" "subj" zca subj)
          (p "certify" "ca" zca ca)
          (p "certify" "pk" zca pk) (non (privk "cert" ca)))
        (non (invk pk)))))
   (lang (cert sign) (cert-body (tupl 3))))

(defskeleton cert-uni
  (vars (subj ca name) (pk akey) (serial data) (chal text))
  (defstrand init 3 (ca ca) (chal chal))
  (non-orig (privk "cert" ca)))

