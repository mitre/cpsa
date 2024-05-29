(herald cert-lang)

(comment "CPSA 4.4.3")
(comment "All input read from tst/cert_lang.scm")

(defprotocol cert-uni basic
  (defrole certify
    (vars (ch chan) (subj ca name) (pk akey) (serial data))
    (trace
      (send ch (cert (cert-body subj serial pk) (privk "cert" ca))))
    (inputs ch subj pk serial (privk "cert" ca)))
  (defrole init
    (vars (ch-ca ch-r chan) (subj ca name) (pk akey) (serial data)
      (chal text))
    (trace
      (recv ch-ca (cert (cert-body subj serial pk) (privk "cert" ca)))
      (send ch-r (enc "challenge" chal pk)) (recv ch-r chal))
    (uniq-orig chal)
    (inputs ch-ca ch-r subj (pubk "cert" ca))
    (outputs chal))
  (defrole resp
    (vars (ch-ca ch-i chan) (subj ca name) (pk akey) (serial data)
      (chal text))
    (trace
      (recv ch-ca (cert (cert-body subj serial pk) (privk "cert" ca)))
      (recv ch-i (enc "challenge" chal pk)) (send ch-i chal))
    (inputs ch-ca ch-i subj (pubk "cert" ca) (invk pk))
    (outputs chal))
  (defrule certified-keys-uncompromised
    (forall ((zca strd) (subj ca name) (pk akey))
      (implies
        (and (p "certify" zca (idx 1)) (p "certify" "subj" zca subj)
          (p "certify" "ca" zca ca) (p "certify" "pk" zca pk)
          (non (privk "cert" ca)))
        (non (invk pk)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (lang (cert sign) (cert-body (tupl 3))))

(defskeleton cert-uni
  (vars (serial data) (chal text) (pk akey) (ca subj name)
    (ch-ca ch-r chan))
  (defstrand init 3 (serial serial) (chal chal) (pk pk) (subj subj)
    (ca ca) (ch-ca ch-ca) (ch-r ch-r))
  (non-orig (privk "cert" ca))
  (uniq-orig chal)
  (traces
    ((recv ch-ca (cert (cert-body subj serial pk) (privk "cert" ca)))
      (send ch-r (enc "challenge" chal pk)) (recv ch-r chal)))
  (label 0)
  (unrealized (0 0))
  (origs (chal (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton cert-uni
  (vars (serial data) (chal text) (pk akey) (ca subj name)
    (ch-ca ch-r ch chan))
  (defstrand init 3 (serial serial) (chal chal) (pk pk) (subj subj)
    (ca ca) (ch-ca ch-ca) (ch-r ch-r))
  (defstrand certify 1 (serial serial) (pk pk) (subj subj) (ca ca)
    (ch ch))
  (precedes ((1 0) (0 0)))
  (non-orig (invk pk) (privk "cert" ca))
  (uniq-orig chal)
  (rule certified-keys-uncompromised)
  (operation encryption-test (added-strand certify 1)
    (cert (cert-body subj serial pk) (privk "cert" ca)) (0 0))
  (traces
    ((recv ch-ca (cert (cert-body subj serial pk) (privk "cert" ca)))
      (send ch-r (enc "challenge" chal pk)) (recv ch-r chal))
    ((send ch (cert (cert-body subj serial pk) (privk "cert" ca)))))
  (label 1)
  (parent 0)
  (unrealized (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton cert-uni
  (vars (serial serial-0 data) (chal text) (pk akey)
    (ca subj subj-0 ca-0 name) (ch-ca ch-r ch ch-ca-0 ch-i chan))
  (defstrand init 3 (serial serial) (chal chal) (pk pk) (subj subj)
    (ca ca) (ch-ca ch-ca) (ch-r ch-r))
  (defstrand certify 1 (serial serial) (pk pk) (subj subj) (ca ca)
    (ch ch))
  (defstrand resp 3 (serial serial-0) (chal chal) (pk pk) (subj subj-0)
    (ca ca-0) (ch-ca ch-ca-0) (ch-i ch-i))
  (precedes ((0 1) (2 1)) ((1 0) (0 0)) ((2 2) (0 2)))
  (non-orig (invk pk) (privk "cert" ca))
  (uniq-orig chal)
  (operation nonce-test (added-strand resp 3) chal (0 2)
    (enc "challenge" chal pk))
  (traces
    ((recv ch-ca (cert (cert-body subj serial pk) (privk "cert" ca)))
      (send ch-r (enc "challenge" chal pk)) (recv ch-r chal))
    ((send ch (cert (cert-body subj serial pk) (privk "cert" ca))))
    ((recv ch-ca-0
       (cert (cert-body subj-0 serial-0 pk) (privk "cert" ca-0)))
      (recv ch-i (enc "challenge" chal pk)) (send ch-i chal)))
  (label 2)
  (parent 1)
  (realized)
  (shape)
  (maps
    ((0)
      ((ca ca) (chal chal) (ch-ca ch-ca) (ch-r ch-r) (subj subj) (pk pk)
        (serial serial))))
  (origs (chal (0 1))))

(comment "Nothing left to do")
