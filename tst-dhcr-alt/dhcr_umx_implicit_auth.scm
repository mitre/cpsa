;;; Unified Model  This version used in the paper, tooldev/dh/conf_dh/dh_ebn.tex

;;; This file models the "Unified Model" method of determining a fresh
;;; key from long-term and ephemeral Diffie-Hellman exponents.  We use
;;; self-signed certificates to link names to long-term public values.

;;; This file contains the criss-crossed version, in which the each
;;; ephemeral is mixed with the peer's static exponent.  Only the key
;;; derivation macros differ from the version in dhcr_um.scm

;;; A role is provided to expose the long term exponent.  The latter
;;; step is used to test the notion of forward security, assuming that
;;; it happens *after* the session which agrees the key in question.  

;;; This file considers a single goal statement.  It asserts the
;;; implicit authentication claim, namely that if *anyone* shares a
;;; key with me, then that party and I agree on each others'
;;; identities and long term values.  This assumes that the values
;;; remain undisclosed.

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
	(limit 4000)
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

  (defrule eq-means-=
    (forall
     ((v1 v2 mesg))
     (implies
      (fact eq v1 v2)
      (= v1 v2))))

  (lang (sig sign)
	(body (tuple 3))
	(pv (tuple 2))))
 
;; Implicit authentication

(defgoal dhcr-umx
  (forall
   ((zi zr strd) (ltxa ltxb x y rndx) (eta chi beta alpha expt)
    (a b a-0 b-0 name))
   (implies
    (and
     (p "init" zi 4)
     (p "init" "l" zi ltxa)
     (p "init" "beta" zi beta)
     (p "init" "x" zi x)
     (p "init" "eta" zi eta)
     (p "init" "a" zi a)
     (p "init" "b" zi b-0)
     
     (p "resp" zr 4)
     (p "resp" "l" zr ltxb)
     (p "resp" "alpha" zr alpha)
     (p "resp" "y" zr y)
     (p "resp" "chi" zr chi)     
     (p "resp" "a" zr a-0)
     (p "resp" "b" zr b)
     (fact eq
	   (kcfa ltxa (exp (gen) beta)
		 x (exp (gen) eta))
	   (kcfb ltxb (exp (gen) alpha)
		 y (exp (gen) chi)))
     (non (privk "sig" b))
     (non (privk "sig" a))
     (fact neq ltxa ltxb)
     (fact undisclosed ltxa)
     (fact undisclosed beta)
     (fact undisclosed ltxb)
     (fact undisclosed alpha))
    (and
     (= a-0 a)
     (= b-0 b)
     (= beta ltxb)
     (= alpha ltxa)))))

