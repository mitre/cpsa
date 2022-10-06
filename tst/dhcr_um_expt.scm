;;; Unified Model  This version used in the paper, tooldev/dh/conf_dh/dh_ebn.tex

;;; This file models the "Unified Model" method of determining a fresh
;;; key from long-term and ephemeral Diffie-Hellman exponents.  We use
;;; function relation declarations to link names to long-term public
;;; values.

;;; This file contains the standard version, in which the two
;;; ephemeral are mixed, as are the two static exponents.

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
    (facts (neq (exp (gen) upsilon) (gen)))
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
		     (kcfb lb (exp (gen) alpha) y (exp (gen) zeta)))))
     (recv nb)
     )
    (uniq-gen y)
    (uniq-orig nb)
    (facts (neq (exp (gen) zeta) (gen)))
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

(comment 
(defskeleton dhcr-um
  (vars (a b name) (la lb rndx) (alpha beta expt))
  (defstrand resp 5 (a a) (b b) (lb lb) (alpha alpha))
  (defstrand init 5 (a a) (b b) (la la) (beta beta))
  (non-orig (privk "sig" a) (privk "sig" b))
  (facts (neq a b)
	 (undisclosed la)
	 (undisclosed lb))))

; Responder point of view: both exponents secret
(defskeleton dhcr-um
  (vars (a b name) (lb rndx) (alpha expt))
  (defstrand resp 5 (a a) (b b) (lb lb) (alpha alpha))
  (non-orig (privk "sig" a))
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

(comment 
;;; Initiator point of view: partner's exponent secret
(defskeleton dhcr-um
  (vars (ltxa ltxb rndx) (a b name))
  (defstrand init 4 (ltxa ltxa) (ltxb ltxb) (a a) (b b))
  (defstrand ltx-gen 1 (l ltxb))
  (non-orig ltxb)
  (neq (a b)))

					; Responder point of view; both exponents secret
(defskeleton dhcr-um
  (vars (ltxa ltxb rndx) (a b name))
  (defstrand resp 4 (ltxa ltxa) (ltxb ltxb) (a a) (b b))
  (defstrand ltx-gen 1 (l ltxa))
  (defstrand ltx-gen 1 (l ltxb))
  (non-orig ltxa ltxb)
  (neq (a b)))

; Responder point of view; partner's exponent secre
(defskeleton dhcr-um
  (vars (ltxa ltxb rndx) (a b name))
  (defstrand resp 4 (ltxa ltxa) (ltxb ltxb) (a a) (b b))
  (defstrand ltx-gen 1 (l ltxa))
  (non-orig ltxa)
  (neq (a b)))

;;; Forward secrecy, neither long-term exponent secure
(defskeleton dhcr-um
   (vars (ltxa ltxb x rndx) (y expt) (a b name))
   (defstrand init 4 (ltxa ltxa) (ltxb ltxb) (x x) (y y) (a a) (b b))
   (deflistener (kcfa ltxa ltxb x (exp (gen) y)))
   (defstrand ltx-gen 3 (l ltxa))
   (defstrand ltx-gen 3 (l ltxb))
   (precedes ((0 3) (3 1)) ((0 3) (2 1)))
   (neq (a b)))

;;; Forward secrecy, neither long-term exponent secure
 (defskeleton dhcr-um
   (vars (ltxa ltxb x rndx) (y expt) (a b name))
   (defstrand init 4 (ltxa ltxa) (ltxb ltxb) (x x) (y y) (a a) (b b))
   (deflistener (exp (gen) (mul x y)))
   (defstrand ltx-gen 3 (l ltxa))
   (defstrand ltx-gen 3 (l ltxb))
   (precedes ((0 3) (3 1)) ((0 3) (2 1)))
   (neq (a b)))
 )
