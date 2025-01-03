; Unified Model.  This version used in the paper, tooldev/dh/conf_dh/dh_ebn.tex

; This file models the "Unified Model" method of determining a fresh
; key from long-term and ephemeral Diffie-Hellman exponents.  We use
; function relation declarations to link names to long-term public
; values.

;;; This file contains the criss-cross version, in which each
;;; ephemeral is mixed with the peer's static exponent.

; A role is provided in which a party signs a fresh long-term
; Diffie-Hellman value, and then leaks the exponent.  The latter step
; is used to test forward security.

; Two inputs are analyzed.  In the first, we model that two
; participants exist that agree on the UM key.  The notion of
; "implicit authentication" suggests that if one participant exists
; and another party knows the same key, that party must be either the
; participant or the participant's intended partner.

; In this version, we assume that the long-term keys of the
; participants do not leak.

; The second input checks whether the key can be learned when the key
; is generated honestly.  In this version, we do NOT assume that the
; long-term keys of the participants do not leak.

(herald "DHCR: unified model (UM) criss-cross" (bound 20) (limit 8000) (algebra diffie-hellman))

(defmacro (kcfa ltxa ltxb x hy)
  (hash (exp hy ltxa) (exp (gen) (mul ltxb x))))

(defmacro (kcfb ltxa ltxb y hx)
  (hash (exp (gen) (mul ltxa y)) (exp hx ltxb)))

(defprotocol dhcr-umx diffie-hellman
  (defrole init
    (vars (ltxa ltxb expt) (x rndx) (y expt) (a b name) (na nb data))
    (trace
     (recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
     (send (cat na a b (exp (gen) x)))
     (recv (cat (exp (gen) y) (enc na nb a b (kcfa ltxa ltxb x (exp (gen) y)))))
     (send nb)
     )
    (fn-of ("principal-of" (ltxa a) (ltxb b))
           ("ltx-of" (a ltxa) (b ltxb)))
    (uniq-gen x)
    (uniq-orig na)
    (neq ((exp (gen) y) (gen))))

  (defrole resp
    (vars (ltxa ltxb expt) (y rndx) (x expt) (a b name) (na nb data))
    (trace
     (recv (cat (exp (gen) ltxa) (exp (gen) ltxb)))
     (recv (cat na a b (exp (gen) x)))
     (send (cat (exp (gen) y) (enc na nb a b (kcfb ltxa ltxb y (exp (gen) x)))))
     (recv nb)
     )
    (fn-of ("principal-of" (ltxa a) (ltxb b))
	   ("ltx-of" (a ltxa) (b ltxb)))
    (uniq-gen y)
    (uniq-orig nb)
    (neq ((exp (gen) x) (gen))))

  (defrole ltx-gen
    (vars (self name) (l rndx))
    (trace
     (send (cat self (exp (gen) l)))
     (recv "end-of-protocol")
     (send l))
    (uniq-gen l)
    (fn-of ("principal-of" (l self))
	   ("ltx-of" (self l)))))

; Omitting the a\not=b changes basically nothing.
(defskeleton dhcr-umx
  (vars (ltxa expt) (ltxb rndx) (a b name))
  (defstrand init 4 (ltxa ltxa) (ltxb ltxb) (a a) (b b))
  (defstrand ltx-gen 1 (self b) (l ltxb))
  (precedes ((1 0) (0 0)))
  (non-orig ltxb)
;   (neq (a b))
  )

; Initiator point of view: partner's exponent secret
(defskeleton dhcr-umx
  (vars (ltxa expt) (ltxb rndx) (a b name))
  (defstrand init 4 (ltxa ltxa) (ltxb ltxb) (a a) (b b))
  (defstrand ltx-gen 1 (self b) (l ltxb))
  (precedes ((1 0) (0 0)))
  (non-orig ltxb)
  (neq (a b)))

; Initiator point of view: both LTX exponents secret
(defskeleton dhcr-umx
  (vars (ltxa ltxb rndx) (a b name))
  (defstrand init 4 (ltxa ltxa) (ltxb ltxb) (a a) (b b))
  (defstrand ltx-gen 1 (l ltxa))
  (defstrand ltx-gen 1 (l ltxb))
  (non-orig ltxa ltxb) (neq (a b)))

; Responder point of view; both exponents secret
(defskeleton dhcr-umx
  (vars (ltxa ltxb rndx) (a b name))
  (defstrand resp 4 (ltxa ltxa) (ltxb ltxb) (a a) (b b))
  (defstrand ltx-gen 1 (l ltxa))
  (defstrand ltx-gen 1 (l ltxb))
  (non-orig ltxa ltxb)
  (neq (a b)))

; Responder point of view; partner's exponent secre
(defskeleton dhcr-umx
  (vars (ltxa rndx) (a b name))
  (defstrand resp 4 (ltxa ltxa) (a a) (b b))
  (defstrand ltx-gen 1 (l ltxa))
  (non-orig ltxa)
  (neq (a b)))

(defskeleton dhcr-umx
  (vars (ltxa rndx) (a b name))
  (defstrand resp 4 (ltxa ltxa) (a a) (b b))
  (defstrand ltx-gen 1 (l ltxa))
  (non-orig ltxa)
  ;; (neq (a b))
  )

;;; Forward secrecy, neither long-term exponent secure
(defskeleton dhcr-umx
  (vars (ltxa ltxb rndx) (x rndx) (y expt) (a b name))
  (defstrand init 4 (ltxa ltxa) (ltxb ltxb) (x x) (y y) (a a) (b b))
  (deflistener (kcfa ltxa ltxb x (exp (gen) y)))
  (defstrand ltx-gen 3 (l ltxa))
  (defstrand ltx-gen 3 (l ltxb))
  (precedes ((0 3) (3 1)) ((0 3) (2 1)))
  (neq (a b)))
