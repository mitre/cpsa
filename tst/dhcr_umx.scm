;;; Unified Model  This version used in the paper, tooldev/dh/conf_dh/dh_ebn.tex

;;; This file models the "Unified Model" method of determining a fresh
;;; key from long-term and ephemeral Diffie-Hellman exponents.  We use
;;; self-signed certificates to link names to long-term public values.

;;; This file contains the criss-crossed version, in which each
;;; ephemeral is mixed with the peer's static exponent.  Only the key
;;; derivation macros differ from the version in dhcr_um.scm

;;; A role is provided to expose the long term exponent.  The latter
;;; step is used to test the notion of forward security, assuming that
;;; it happens *after* the session which agrees the key in question.  

;;; A sequence of queries are analyzed.  Four show what happens given
;;; an initiator run, depnding which long term values are exposed.
;;; Then four ask the corresponding questions about the responder.  In
;;; each group of four, we first assume neither long term exponent is
;;; exposed, then consider each exposure individually, and then both
;;; exposed.

;;; Then we consider the forward secrecy question, first from the
;;; initiator's point of view, and then from the responder's.

;;; The UMX key derivation fails to achieve forward secrecy.  Its
;;; strength relative to the standard UM key derivation a
;;; participant's *own* long term value may be exposed without an
;;; adversary being able to acquire a key shared with them for any
;;; claimed peer.  A fine point that the analysis exposes is that this
;;; is true when the peer has had only one long key generated.  Other
;;; disclosed long terms keys yield counterxamples.  If my peer's long
;;; term value is exposed of course anyone can impersonate them.

;;; CPSA4 revisions:
;;;
;;; 1.  Self certify my public value in ltx-gen,
;;;     and assume signing keys non.
;;; 2.  Deposit private value in state and retrieve
;;;	it at the beginning of each init or resp run.
;;; 3.  Discard the private value from state before
;;;	disclosing it, when testing forward secrecy.

(herald "DHCR: unified model (UM) with criss-cross key derivation"
	(bound 30)
	(limit 8000)
	(algebra diffie-hellman))

(defmacro (kcfa ltxa gbeta x hy)
  (hash (exp hy ltxa) (exp gbeta x)))

(defmacro (kcfb ltxb galpha y hx)
  (hash (exp galpha y) (exp hx ltxb)))

(defprotocol dhcr-umx diffie-hellman
  (defrole init
    (vars (l x rndx) (beta eta expt) (a b name) (na nb data) (priv-stor locn))
    (trace
     (load priv-stor (pv a l))
     (recv (sig (body b (exp (gen) beta) (pubk "sig" b))
		(privk "sig" b)))
     (send (cat na a b (exp (gen) x)))
     (recv (cat (exp (gen) eta)
		(enc na nb a b
		     (kcfa l (exp (gen) beta)
			   x (exp (gen) eta)))))
     (send nb)
     )
    (uniq-gen x)
    (uniq-orig na)
    (facts (neq a b))
    ;; (facts (neq (exp (gen) eta) (gen)))
    (gen-st (pv a l)))

  (defrole resp
    (vars (l y rndx) (alpha chi expt) (a b name) (na nb data) (priv-stor locn))
    (trace
     (load priv-stor (pv b l))
     (recv (sig (body a (exp (gen) alpha) (pubk "sig" a))
		(privk "sig" a)))
     (recv (cat na a b (exp (gen) chi)))
     (send (cat (exp (gen) y)
		(enc na nb a b
		     (kcfb l (exp (gen) alpha)
			   y (exp (gen) chi)))))
     (recv nb)
     (send "done")
     )
    (uniq-gen y)
    (uniq-orig nb)
    (facts (neq a b))
    ;;    (facts (neq (exp (gen) chi) (gen)))
    (gen-st (pv b l)))

  (defrole ltx-gen
    (vars (self name) (l rndx)
	  (priv-stor locn) (ignore mesg))
    (trace
     (load priv-stor ignore)
     (stor priv-stor (pv self l))
     (send (sig (body self (exp (gen) l) (pubk "sig" self))
		(privk "sig" self))))
    (uniq-orig l))

  (defrole ltx-disclose
    (vars (self name) (l rndx)
	  (priv-stor locn) (ignore mesg))
    (trace
     (load priv-stor (pv self l))
     (stor priv-stor "nil")
     (send l))
    (gen-st (pv self l)))

  (defrule undisclosed-not-disclosed
    (forall
     ((z strd) (l rndx))
     (implies
      (and (fact undisclosed l)
	  (p "ltx-disclose" z 2)
	  (p "ltx-disclose" "l" z l))
      (false))))

  (defrule ltx-gen-once-inference
    (forall
     ((z1 z2 strd) (self name))
     (implies
      (and
       (fact ltx-gen-once self)
       (p "ltx-gen" z1 2)
       (p "ltx-gen" "self" z1 self)
       (p "ltx-gen" z2 2)
       (p "ltx-gen" "self" z2 self))
      (= z1 z2))))

  (defrule eq-means-=
    (forall
     ((v1 v2 mesg))
     (implies
      (fact eq v1 v2)
      (= v1 v2))))

  (lang (sig sign)
	(body (tuple 3))
	(pv (tuple 2))))
 

; Initiator point of view: both LTX exponents secret
(defskeleton dhcr-umx
  (vars (a b name) (l l-peer rndx))
  (defstrand init 4 (a a) (b b) (l l) (beta l-peer))
  (non-orig (privk "sig" a) (privk "sig" b))
  (facts (neq a b)
	 (undisclosed l)
	 (undisclosed l-peer)))



; Initiator point of view:  peer exponent secret
(defskeleton dhcr-umx
  (vars (a b name) (l l-peer rndx))
  (defstrand init 4 (a a) (b b) (l l) (beta l-peer))
  (non-orig (privk "sig" a) (privk "sig" b))
  (facts (neq a b)
	 ;;	 (undisclosed l)
	 (undisclosed l-peer)))

;;; Initiator point of view:  peer exponent secret,
;;; my key generated only once
(defskeleton dhcr-umx
  (vars (a b name) (l l-peer rndx))
  (defstrand init 4 (a a) (b b) (l l) (beta l-peer))
  (non-orig (privk "sig" a) (privk "sig" b))
  (facts (neq a b)
	 (ltx-gen-once a)
	 ;;	 (undisclosed l)
	 (undisclosed l-peer)))



; Initiator point of view:  my exponent secret
(defskeleton dhcr-umx
  (vars (a b name) (l rndx) (l-peer expt))
  (defstrand init 4 (a a) (b b) (l l) (beta l-peer))
  (non-orig (privk "sig" a) (privk "sig" b))
  (facts (neq a b)
	 ;;	 (undisclosed l-peer)
	 (undisclosed l)))

; Initiator point of view:  neither exponent secret

(defskeleton dhcr-umx
  (vars (a b name) (l rndx) (l-peer expt))
  (defstrand init 4 (a a) (b b) (l l) (beta l-peer))
  (non-orig (privk "sig" a) (privk "sig" b))
  (facts (neq a b)
	 ;;	 (undisclosed l-peer)
	 ;;	 (undisclosed l)
	 ))


;;; Responder cases

(defskeleton dhcr-umx
  (vars (a b name) (l l-peer rndx))
  (defstrand resp 5 (a a) (b b) (l l) (alpha l-peer))
  (non-orig (privk "sig" a) (privk "sig" b))
  (facts (neq a b)
	 (undisclosed l)
	 (undisclosed l-peer)))

(defskeleton dhcr-umx
  (vars (a b name) (l l-peer rndx))
  (defstrand resp 5 (a a) (b b) (l l) (alpha l-peer))
  (non-orig (privk "sig" a) (privk "sig" b))
  (facts (neq a b)
	 ;; 	 (undisclosed l) 
	 (undisclosed l-peer)))

(defskeleton dhcr-umx
  (vars (a b name) (l l-peer rndx))
  (defstrand resp 5 (a a) (b b) (l l) (alpha l-peer))
  (non-orig (privk "sig" a) (privk "sig" b))
  (facts (neq a b)
	 (ltx-gen-once b)
	 ;; 	 (undisclosed l)
	 (undisclosed l-peer)))

(defskeleton dhcr-umx
  (vars (a b name) (l l-peer rndx))
  (defstrand resp 5 (a a) (b b) (l l) (alpha l-peer))
  (non-orig (privk "sig" a) (privk "sig" b))
  (facts (neq a b)
	 (undisclosed l)
	 ;;	 (undisclosed l-peer)
	 ))

(defskeleton dhcr-umx
  (vars (a b name) (l l-peer rndx))
  (defstrand resp 5 (a a) (b b) (l l) (alpha l-peer))
  (non-orig (privk "sig" a) (privk "sig" b))
  (facts (neq a b)
	 ;;      (undisclosed l)
	 ;;	 (undisclosed l-peer)
	 ))

;; Forward secrecy for each participant 

(comment
;;; These forward secrecy queries are commented out because they take
;;; a long time to run (10 minutes plus).  They're not suitable for
;;; the regular test suite for this reason.

;;; They should however be checked from time to time.  

 (defskeleton dhcr-umx
   (vars (ltxa ltxb x rndx) (y expt) (a b name))
   (defstrand init 5 (l ltxa) (beta ltxb) (x x) (eta y) (a a) (b b))
   (deflistener (kcfa ltxa (exp (gen) ltxb) x (exp (gen) y)))
   (defstrand ltx-disclose 3 (l ltxa))
   (defstrand ltx-disclose 3 (l ltxb))
   (precedes ((0 4) (3 0)) ((0 4) (2 0)))
   (non-orig (privk "sig" a) (privk "sig" b))
   (facts (neq a b)))

 (defskeleton dhcr-umx
   (vars (ltxa ltxb y rndx) (chi expt) (a b name))
   (defstrand resp 6 (l ltxa) (alpha ltxb) (y y) (chi chi) (a a) (b b))
   (deflistener (kcfb ltxb (exp (gen) ltxa) y (exp (gen) chi)))
   (defstrand ltx-disclose 3 (l ltxa))
   (defstrand ltx-disclose 3 (l ltxb))
   (precedes ((0 5) (3 0)) ((0 5) (2 0)))
   (facts (neq a b))))

