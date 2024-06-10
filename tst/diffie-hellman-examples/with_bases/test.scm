;;; Unified Model  This version used in the paper, tooldev/dh/conf_dh/dh_ebn.tex

;;; This file models the "Unified Model" method of determining a fresh
;;; key from long-term and ephemeral Diffie-Hellman exponents.  We use
;;; function relation declarations to link names to long-term public
;;; values.

;;; This file contains the standard version, in which the two
;;; ephemeral exponents are mixed, as are the two static exponents.

;;; A role is provided in which a party signs a fresh long-term
;;; Diffie-Hellman value, and then leaks the exponent.  The latter step
;;; is used to test the notion of forward security.

;;; Two inputs are analyzed.  In the first, we model that two
;;; participants exist that agree on the UM key.  The notion of
;;; "implicit authentication" suggests that if one participant exists
;;; and another party knows the same key, that party must be either the
;;; participant or the participant's intended partner.

;;; In this version, we assume that the long-term keys of the
;;; participants do not leak.

;;; The second input checks whether the key can be learned when the key
;;; is generated honestly.  In this version, we do NOT assume that the
;;; long-term keys of the participants do not leak.

;;; CPSA4 revisions:
;;;
;;; 1.  Self certify my public value in ltx-gen,
;;;     and assume signing keys non.
;;; 2.  Deposit private value in state and retrieve
;;;	it at the beginning of each init or resp run.
;;; 3.  Discard the private value from state before
;;;	disclosing it, when testing forward secrecy.

(herald "DHCR: unified model (UM) original"
	(bound 20)
	(limit 12000)
	(algebra diffie-hellman))

(defmacro (kcfa l gb x gy)
  (hash (exp gb l) (exp gy x)))

(defmacro (kcfb l ga y gx)
  (hash (exp ga l) (exp gx y)))

;; (hash (exp (gen) (mul l l-0)) (exp (gen) (mul y zeta)

(defprotocol dhcr-um diffie-hellman
  (defrole init
    (vars (la x rndx) (beta upsilon expt) (a b name) (na nb data) (priv-stor locn))
    (trace
     (load priv-stor (pv a la))
     (recv (sig (body b (exp (gen) beta) (pubk "sig" b))
		(privk "sig" b)))
     (send (cat na a b (exp (gen) x) ;; (sig na a b (exp (gen) x) (privk "sig" a))
		))
     (recv (cat (exp (gen) upsilon)
		(enc na nb a b
		     (kcfa la (exp (gen) beta) x (exp (gen) upsilon)))))
     (send nb)
     )
    (uniq-gen x)
    (uniq-orig na)
    ;; (facts (neq (exp (gen) upsilon) (gen)))
    (gen-st (pv a la))
    (fn-off ("principal-of" (ltxa a) (ltxb b))
           ("ltx-of" (a ltxa) (b ltxb))))

  (defrole resp
    (vars (lb y rndx) (alpha zeta expt) (a b name) (na nb data) (priv-stor locn))
    (trace
     (load priv-stor (pv b lb))
     (recv (sig (body a (exp (gen) alpha) (pubk "sig" a))
		(privk "sig" a)))
     (recv (cat na a b (exp (gen) zeta) ;; (sig na a b (exp (gen) zeta) (privk "sig" a))
		))
     (send (cat (exp (gen) y)
		(enc na nb a b
		     (kcfa lb (exp (gen) alpha) y (exp (gen) zeta)))))
     (recv nb)
     )
    (uniq-gen y)
    (uniq-orig nb)
    ;;    (facts (neq zeta (one)))
    (gen-st (pv b lb))
    (fn-off ("principal-of" (ltxa a) (ltxb b))
	   ("ltx-of" (a ltxa) (b ltxb))))

  (defrole ltx-gen
    (vars (self name) (l rndx)
	  (priv-stor locn) (ignore mesg))
    (trace
     (load priv-stor ignore)
     (stor priv-stor (pv self l))
     (send (sig (body self (exp (gen) l) (pubk "sig" self))
		(privk "sig" self))))
    (uniq-orig l)
    (fn-off ("principal-of" (l self))
	   ("ltx-of" (self l))))

  (defrole ltx-disclose
    (vars (self name) (l rndx)
	  (priv-stor locn) (ignore mesg))
    (trace
     (load priv-stor (pv self l))
     (stor priv-stor "nil")
     (send l))
    (gen-st (pv self l))
    (fn-off ("principal-of" (l self))
	   ("ltx-of" (self l))))

;     (defrule fact-resp-neq0
;       (forall ((z strd) (zeta expt))
;         (implies (and (p "resp" z 3) (p "resp" "zeta" z zeta))
;           (fact neq zeta one))))

  (defrule undisclosed-not-disclosed
    (forall
     ((z strd) (l rndx))
     (implies
      (and (fact undisclosed l)
	  (p "ltx-disclose" z 2)
	  (p "ltx-disclose" "l" z l))
      (false))))

  (lang (sig sign)
	(body (tuple 3))
	(pv (tuple 2))))


(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
	(priv-stor priv-stor-0 locn) (y rndx)
	(zeta expt) (l l-0 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (lb l) (y y) (alpha l-0) (zeta zeta))
  (defstrand ltx-gen 2 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l-0))
  (precedes ((1 1) (0 0)) ((2 2) (0 1)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig nb l l-0)
  (uniq-gen y)
  (absent (y zeta) (y l) (y l-0))
  (gen-st (pv b l))
  (facts (neq a b) (undisclosed l) (undisclosed l-0)))




(comment 
					; Initiator point of view: both LTX exponents secret
 (defskeleton dhcr-um
   (vars (a b name) (la l-peer rndx) (beta expt))
   (defstrand init 5 (a a) (b b) (la la) (beta beta))
   (non-orig (privk "sig" b))
   (facts (neq a b)
	  (undisclosed la)
	  (undisclosed beta)))

					; Initiator point of view:  peer exponent secret
 (defskeleton dhcr-um
   (vars (a b name) (la l-peer rndx) (beta expt))
   (defstrand init 5 (a a) (b b) (la la) (beta beta))
   (non-orig (privk "sig" b))
   (facts (neq a b)
	  ;;	 (undisclosed la)
	  (undisclosed beta)))

					; Initiator point of view:  my exponent secret
 (defskeleton dhcr-um
   (vars (a b name) (la rndx))
   (defstrand init 5 (a a) (b b) (la la) )
   (non-orig (privk "sig" b))
   (facts (neq a b)
	  ;;	 (undisclosed l-peer)
	  (undisclosed la)))

					; Initiator point of view:  neither exponent secret

 (defskeleton dhcr-um
   (vars (a b name) (la rndx))
   (defstrand init 5 (a a) (b b) (la la))
   (non-orig (privk "sig" b))
   (facts (neq a b)
	  ;;	 (undisclosed l-peer)
	  ;;	 (undisclosed la)
	  ))

 (defskeleton dhcr-um
   (vars (a b name) (la lb rndx) (alpha beta expt))
   (defstrand resp 5 (a a) (b b) (lb lb) (alpha alpha))
   (defstrand init 5 (a a) (b b) (la la) (beta beta))
   (non-orig (privk "sig" a) (privk "sig" b))
   (facts (neq a b)
	  (undisclosed la)
	  (undisclosed lb)))

					; Responder point of view: both exponents secret
 (defskeleton dhcr-um
   (vars (a b name) (lb rndx) (alpha expt))
   (defstrand resp 5 (a a) (b b) (lb lb) (alpha alpha))
   (non-orig (privk "sig" a) (privk "sig" b))
   (facts (neq a b)
	  (undisclosed lb)
	  (undisclosed alpha)))

					; Responder point of view:  peer exponent secret
 (defskeleton dhcr-um
   (vars (a b name) (lb l-peer rndx) (alpha expt))
   (defstrand resp 5 (a a) (b b) (lb lb) (alpha alpha))
   (non-orig (privk "sig" a))
   (facts (neq a b)
	  ;;	 (undisclosed lb)
	  (undisclosed alpha)))

					; Responder point of view:  my exponent secret
 (defskeleton dhcr-um
   (vars (a b name) (lb rndx) (l-peer expt))
   (defstrand resp 5 (a a) (b b) (lb lb) )
   (non-orig (privk "sig" a))
   (facts (neq a b)
	  ;;	 (undisclosed l-peer)
	  (undisclosed lb)))

					; Responder point of view:  neither exponent secret

 (defskeleton dhcr-um
   (vars (a b name) (lb rndx) (l-peer expt))
   (defstrand resp 5 (a a) (b b) (lb lb))
   (non-orig (privk "sig" a))
   (facts (neq a b)
	  ;;	 (undisclosed l-peer)
	  ;;	 (undisclosed lb)
	  ))

 (defskeleton dhcr-um
   (vars (la x beta rndx) (upsilon expt) (a b name))
   (defstrand init 5 (la la) (beta beta) (x x) (upsilon upsilon) (a a) (b b))
   (deflistener (kcfa la (exp (gen) beta)
		      x (exp (gen) upsilon)))
   (defstrand ltx-gen 3 (l la))
   (defstrand ltx-gen 3 (l beta))
   (precedes ((0 4) (3 0)) ((0 4) (2 0)))
   (neq (a b))))


