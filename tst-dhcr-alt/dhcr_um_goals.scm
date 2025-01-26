;;; Unified Model  This version used in the paper, tooldev/dh/conf_dh/dh_ebn.tex

;;; This file models the "Unified Model" method of determining a fresh
;;; key from long-term and ephemeral Diffie-Hellman exponents.  We use
;;; self-signed certificates to link names to long-term public values.

;;; This file contains the standard version, in which the two
;;; ephemeral are mixed, as are the two static exponents.

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

;;; The UM key derivation achieves forward secrecy.  Its weakness is
;;; that if a participant's *own* long term value is exposed, an
;;; adversary can acquire a key shared with them for any claimed peer.
;;; This remains true if we stipulate that the partcipant generates a
;;; long trem key only once.  If my peer's long term value is exposed
;;; of course anyone can impersonate them.

;;; CPSA4 revisions:
;;;
;;; 1.  Self certify my public value in ltx-gen,
;;;     and assume signing keys non.
;;; 2.  Deposit private value in state and retrieve
;;;	it at the beginning of each init or resp run.
;;; 3.  Discard the private value from state before
;;;	disclosing it, when testing forward secrecy.

(herald "DHCR: unified model (UM) original"
	(bound 30)
	(limit 8000)
	(goals-sat)
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


(defgoal dhcr-um
  (forall
   ((na nb data) (a b name) (priv-stor locn) (l l-peer x rndx)
    (eta expt) (z strd))
   (implies
    (and
     (p "init" z 4)
     (p "init" "na" z na)
     (p "init" "nb" z nb)     
     (p "init" "a" z a)
     (p "init" "b" z b)
     (p "init" "priv-stor" z priv-stor)
     (p "init" "l" z l)
     (p "init" "x" z x)
     (p "init" "beta" z l-peer)     
     (p "init" "eta" z eta)
     (non (privk "sig" b))
     (ugen x)
     (uniq-at na z 2)
     (fact neq a b)
     (fact undisclosed l)
     (fact undisclosed l-peer))
    (exists
     ((z-1 strd) (y rndx) (w expt))
     (and
      (= eta (mul w y))
      (p "resp" z-1 4) 
      (p "resp" "na" z-1 na)
      (p "resp" "nb" z-1 nb) (p "resp" "a" z-1 a)
      (p "resp" "b" z-1 b) 
      (p "resp" "l" z-1 l-peer) (p "resp" "y" z-1 y)
      (p "resp" "alpha" z-1 l) (p "resp" "chi" z-1 (mul y w))
      (prec z 2 z-1 2) 
      (ugen y) (uniq-at nb z-1 3))))))


(defgoal dhcr-um
  (forall
   ((z strd) (na nb data) (a b name) (l l-peer y rndx)
    (chi expt))
   (implies
    (and (p "resp" z 5)
	 (p "resp" "na" z na)
	 (p "resp" "nb" z nb)
         (p "resp" "a" z a)
	 (p "resp" "b" z b)
	 (p "resp" "l" z l)
         (p "resp" "y" z y)
	 (p "resp" "alpha" z l-peer)
         (p "resp" "chi" z chi)
	 (non (privk "sig" a)) (ugen y)
         (uniq-at nb z 3) (fact neq a b) (fact undisclosed l)
         (fact undisclosed l-peer))      
    (exists
     ((z-1 strd) (x rndx) (w expt))
     (and (= chi (mul x w))
	  (p "init" z-1 5)
          (p "resp" "chi" z (mul x w)) 
	  (p "init" "na" z-1 na)
          (p "init" "nb" z-1 nb)
	  (p "init" "a" z-1 a)
          (p "init" "b" z-1 b) 
          (p "init" "l" z-1 l-peer)
	  (p "init" "x" z-1 x)
          (p "init" "beta" z-1 l)
	  (p "init" "eta" z-1 (mul y w))
	  (prec z 3 z-1 3) (prec z-1 2 z 2)
	  (prec z-1 4 z 4) (ugen x)
	  (uniq-at na z-1 2))))))


(defgoal dhcr-um
  (forall
   ((z zl strd) (na nb data) (a b name) (priv-stor locn) (l x rndx)
    (eta beta expt))
   (implies
    (and
     (p "init" z 4)
     (p "init" "na" z na)
     (p "init" "nb" z nb)     
     (p "init" "a" z a)
     (p "init" "b" z b)
     (p "init" "priv-stor" z priv-stor)
     (p "init" "l" z l)
     (p "init" "x" z x)
     (p "init" "beta" z beta)     
     (p "init" "eta" z eta)
     (non (privk "sig" b))
     (ugen x)
     (uniq-at na z 2)
     (fact neq a b)
     (fact undisclosed l)
     (fact undisclosed beta)
     ;; ... gets the secrecy we need
     (p "" zl 2)
     (p "" "x" zl 
	(kcfa l (exp (gen) beta)
	      x (exp (gen) eta))))
    (false))))

(comment
;;; comment these out for brevity in the tst suite run.  Be sure to
;;; test them periodically, though.

;;; Forward secrecy 

 (defgoal dhcr-um
   (forall
    ((na nb data) (a b self self-0 name)
     (ltxa ltxb x rndx)
     (y expt) (z z-0 z-1 z-2 strd))
    (implies
     (and (p "init" z 5)
	  (p "" z-0 2)
	  (p "ltx-disclose" z-1 3)
	  (p "ltx-disclose" z-2 3)

	  (p "init" "na" z na)
          (p "init" "nb" z nb)
	  (p "init" "a" z a)
	  (p "init" "b" z b)
	  (p "init" "l" z ltxa)
          (p "init" "x" z x)
	  (p "init" "beta" z ltxb)
	  (p "init" "eta" z y)
	 
          (p "" "x" z-0
             (hash (exp (gen) (mul ltxa ltxb))
		   (exp (gen) (mul x y))))
	 
          (p "ltx-disclose" "self" z-1 self)
          (p "ltx-disclose" "l" z-1 ltxa)
          (p "ltx-disclose" "self" z-2 self-0)
          (p "ltx-disclose" "l" z-2 ltxb)
	  (ugen x)
	  (uniq-at na z 2)
	  (prec z 4 z-1 0)
	  (prec z 4 z-2 0))
     (false))))


 (defgoal dhcr-um
   (forall
    ((na nb data) (a b self self-0 name)
     (ltxa ltxb y rndx)
     (chi expt) (z z-0 z-1 z-2 strd))
    (implies
     (and
      (p "resp" z 6)
      (p "" z-0 2)
      (p "ltx-disclose" z-1 3)     
      (p "ltx-disclose" z-2 3)
     
      (p "resp" "na" z na)
      (p "resp" "nb" z nb)
      (p "resp" "a" z a)
      (p "resp" "b" z b)
      (p "resp" "l" z ltxa)
      (p "resp" "y" z y)
      (p "resp" "alpha" z ltxb)
      (p "resp" "chi" z chi)

      (p "" "x" z-0
         (hash (exp (gen) (mul ltxa ltxb))
	       (exp (gen) (mul y chi))))
     
      (p "ltx-disclose" "self" z-1 self)         
      (p "ltx-disclose" "l" z-1 ltxa)
      (p "ltx-disclose" "self" z-2 self-0)         
      (p "ltx-disclose" "l" z-2 ltxb)
      (prec z 5 z-1 0)
      (prec z 5 z-2 0)
      (ugen y) (uniq-at nb z 3))
     (false)))))
