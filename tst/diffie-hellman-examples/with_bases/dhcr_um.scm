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
	(limit 2000)
	(algebra diffie-hellman))

(defmacro (kcfa l gb x gy)
  (hash (exp gb l) (exp gy x)))

(defmacro (kcfb l ga y gx)
  (hash (exp ga l) (exp gx y)))

(defprotocol dhcr-um diffie-hellman
  (defrole init
    (vars (l x rndx) (beta eta expt) (a b name) (na nb data) (priv-stor locn))
    (trace
     (load priv-stor (pv a l))
     (recv (sig (body b (exp (gen) beta) (pubk "sig" b))
		(privk "sig" b)))
     (send (cat na a b (exp (gen) x)))
     (recv (cat (exp (gen) eta) (enc na nb a b (kcfa l (exp (gen) beta) x (exp (gen) eta)))))
     (send nb)
     )
    (uniq-gen x)
    (uniq-orig na)
    ;; (facts (neq (exp (gen) eta) (gen)))
    (gen-st (pv a l))
    (fn-of ("principal-of" (ltxa a) (ltxb b))
           ("ltx-of" (a ltxa) (b ltxb))))

  (defrole resp
    (vars (l y rndx) (alpha chi expt) (a b name) (na nb data) (priv-stor locn))
    (trace
     (load priv-stor (pv b l))
     (recv (sig (body a (exp (gen) alpha) (pubk "sig" a))
		(privk "sig" a)))
     (recv (cat na a b (exp (gen) chi)))
     (send (cat (exp (gen) y) (enc na nb a b (kcfb l (exp (gen) alpha) y (exp (gen) chi)))))
     (recv nb)
     )
    (uniq-gen y)
    (uniq-orig nb)
    ;;    (facts (neq (exp (gen) chi) (gen)))
    (gen-st (pv b l))
    (fn-of ("principal-of" (ltxa a) (ltxb b))
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
    (fn-of ("principal-of" (l self))
	   ("ltx-of" (self l))))

  (defrole ltx-disclose
    (vars (self name) (l rndx)
	  (priv-stor locn) (ignore mesg))
    (trace
     (load priv-stor (pv self l))
     (stor priv-stor "nil")
     (send l))
    (gen-st (pv self l))
    (fn-of ("principal-of" (l self))
	   ("ltx-of" (self l))))

;     (defrule fact-resp-neq0
;       (forall ((z strd) ;(gx expt)
;   	     )
;   	    (implies (and (p "resp" z 3) (p "resp" "gx" z (gen))) (false))))

  ;   (defrule fact-init-neq0
;       (forall ((z strd) ;(gx expt)
;   	     )
;   	    (implies (and (p "init" z 4) (p "init" "eta" z (gen))) (false))))

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
  (vars (a b name) (l l-peer rndx))
  (defstrand init 4 (a a) (b b) (l l) ((exp (gen) beta) (exp (gen) l-peer)))
  (non-orig (privk "sig" b))
  (facts (neq a b)
	 (undisclosed l)
	 (undisclosed l-peer)))



; Initiator point of view:  peer exponent secret
(defskeleton dhcr-um
  (vars (a b name) (l l-peer rndx))
  (defstrand init 4 (a a) (b b) (l l) ((exp (gen) beta) (exp (gen) l-peer)))
  (non-orig (privk "sig" b))
  (facts (neq a b)
	 ;;	 (undisclosed l)
	 (undisclosed l-peer)))

; Initiator point of view:  my exponent secret
(defskeleton dhcr-um
  (vars (a b name) (l rndx) (l-peer expt))
  (defstrand init 4 (a a) (b b) (l l) ((exp (gen) beta) (exp (gen) l-peer)))
  (non-orig (privk "sig" b))
  (facts (neq a b)
	 ;;	 (undisclosed l-peer)
	 (undisclosed l)))

; Initiator point of view:  neither exponent secret

(defskeleton dhcr-um
  (vars (a b name) (l rndx) (l-peer expt))
  (defstrand init 4 (a a) (b b) (l l) ((exp (gen) beta) (exp (gen) l-peer)))
  (non-orig (privk "sig" b))
  (facts (neq a b)
	 ;;	 (undisclosed l-peer)
	 ;;	 (undisclosed l)
	 ))

(comment
					; Initiator point of view: partner's exponent secret
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
   (deflistener (exp (exp (gen) x) y))
   (defstrand ltx-gen 3 (l ltxa))
   (defstrand ltx-gen 3 (l ltxb))
   (precedes ((0 3) (3 1)) ((0 3) (2 1)))
   (neq (a b)))
 )
