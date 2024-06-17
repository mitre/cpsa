(comment "CPSA 4.4.4")
(comment "Extracted shapes")

(herald "DHCR: unified model (UM) with criss-cross key derivation"
  (bound 30) (limit 16000) (goals-sat) (algebra diffie-hellman))

(comment "CPSA 4.4.4")

(comment "All input read from dhcr_umx_goals.scm")

(comment "Step count limited to 16000")

(comment "Strand count bounded at 30")

(defprotocol dhcr-umx diffie-hellman
  (defrole init
    (vars (l x rndx) (beta eta expt) (a b name) (na nb data)
      (priv-stor locn))
    (trace (load priv-stor (pv a l))
      (recv
        (sig (body b (exp (gen) beta) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) eta)
          (enc na nb a b
            (hash (exp (gen) (mul l eta)) (exp (gen) (mul x beta))))))
      (send nb))
    (uniq-orig na)
    (uniq-gen x)
    (absent (x l) (x beta))
    (facts (neq a b))
    (gen-st (pv a l)))
  (defrole resp
    (vars (l y rndx) (alpha chi expt) (a b name) (na nb data)
      (priv-stor locn))
    (trace (load priv-stor (pv b l))
      (recv
        (sig (body a (exp (gen) alpha) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) chi)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y alpha)) (exp (gen) (mul l chi))))))
      (recv nb) (send "done"))
    (uniq-orig nb)
    (uniq-gen y)
    (absent (y l) (y alpha) (y chi))
    (facts (neq a b))
    (gen-st (pv b l)))
  (defrole ltx-gen
    (vars (self name) (l rndx) (priv-stor locn) (ignore mesg))
    (trace (load priv-stor ignore) (stor priv-stor (pv self l))
      (send
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self))))
    (uniq-orig l))
  (defrole ltx-disclose
    (vars (self name) (l rndx) (priv-stor locn))
    (trace (load priv-stor (pv self l)) (stor priv-stor "nil") (send l))
    (gen-st (pv self l)))
  (defrule undisclosed-not-disclosed
    (forall ((z strd) (l rndx))
      (implies
        (and (fact undisclosed l) (p "ltx-disclose" z (idx 2))
          (p "ltx-disclose" "l" z l))
        (false))))
  (defrule ltx-gen-once-inference
    (forall ((z1 z2 strd) (self name))
      (implies
        (and (fact ltx-gen-once self) (p "ltx-gen" z1 (idx 2))
          (p "ltx-gen" "self" z1 self) (p "ltx-gen" z2 (idx 2))
          (p "ltx-gen" "self" z2 self))
        (= z1 z2))))
  (defrule eq-means-=
    (forall ((v1 v2 mesg)) (implies (fact eq v1 v2) (= v1 v2))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defgenrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2)) (false))))
  (defgenrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defgenrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defgenrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1)))))
  (defgenrule fact-init-neq0
    (forall ((z strd) (b a name))
      (implies
        (and (p "init" z (idx 2)) (p "init" "a" z a) (p "init" "b" z b))
        (fact neq a b))))
  (defgenrule fact-resp-neq0
    (forall ((z strd) (b a name))
      (implies
        (and (p "resp" z (idx 2)) (p "resp" "a" z a) (p "resp" "b" z b))
        (fact neq a b))))
  (defgenrule trRl_ltx-gen-at-1
    (forall ((z strd))
      (implies (p "ltx-gen" z (idx 2)) (trans z (idx 1)))))
  (defgenrule trRl_ltx-gen-at-0
    (forall ((z strd))
      (implies (p "ltx-gen" z (idx 2)) (trans z (idx 0)))))
  (defgenrule trRl_ltx-disclose-at-1
    (forall ((z strd))
      (implies (p "ltx-disclose" z (idx 2)) (trans z (idx 1)))))
  (defgenrule trRl_ltx-disclose-at-0
    (forall ((z strd))
      (implies (p "ltx-disclose" z (idx 2)) (trans z (idx 0)))))
  (defgenrule gen-st-init-0
    (forall ((z strd) (a name) (l rndx))
      (implies
        (and (p "init" z (idx 1)) (p "init" "l" z l) (p "init" "a" z a))
        (gen-st (pv a l)))))
  (defgenrule gen-st-resp-0
    (forall ((z strd) (b name) (l rndx))
      (implies
        (and (p "resp" z (idx 1)) (p "resp" "l" z l) (p "resp" "b" z b))
        (gen-st (pv b l)))))
  (defgenrule gen-st-ltx-disclose-0
    (forall ((z strd) (self name) (l rndx))
      (implies
        (and (p "ltx-disclose" z (idx 1)) (p "ltx-disclose" "l" z l)
          (p "ltx-disclose" "self" z self)) (gen-st (pv self l)))))
  (lang (sig sign) (body (tuple 3)) (pv (tuple 2))))

(defskeleton dhcr-umx
  (vars (na nb data) (a b name) (pt pval) (priv-stor locn)
    (l l-peer x rndx) (eta expt))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (x x) (beta l-peer) (eta eta))
  (non-orig (privk "sig" b))
  (uniq-orig na)
  (uniq-gen x)
  (absent (x l) (x l-peer))
  (facts (neq a b) (undisclosed l-peer))
  (goals
    (forall
      ((na nb data) (a b name) (l l-peer x rndx) (eta expt) (z strd))
      (implies
        (and (p "init" z 4) (p "init" "na" z na) (p "init" "nb" z nb)
          (p "init" "a" z a) (p "init" "b" z b) (p "init" "l" z l)
          (p "init" "x" z x) (p "init" "beta" z l-peer)
          (p "init" "eta" z eta) (non (privk "sig" b)) (ugen x)
          (uniq-at na z 2) (fact neq a b) (fact undisclosed l-peer))
        (exists ((z-1 strd) (y rndx) (w expt))
          (and (p "resp" z-1 4) (p "resp" "na" z-1 na)
            (p "resp" "nb" z-1 nb) (p "resp" "a" z-1 a)
            (p "resp" "b" z-1 b) (prec z 2 z-1 2))))))
  (traces
    ((load priv-stor (cat pt (pv a l)))
      (recv
        (sig (body b (exp (gen) l-peer) (pubk "sig" b))
          (privk "sig" b))) (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) eta)
          (enc na nb a b
            (hash (exp (gen) (mul l eta))
              (exp (gen) (mul l-peer x))))))))
  (label 0)
  (unrealized (0 1))
  (origs (na (0 2)))
  (ugens (x (0 2)))
  (comment "Not closed under rules"))

(comment "Nothing left to do")

(defprotocol dhcr-umx diffie-hellman
  (defrole init
    (vars (l x rndx) (beta eta expt) (a b name) (na nb data)
      (priv-stor locn))
    (trace (load priv-stor (pv a l))
      (recv
        (sig (body b (exp (gen) beta) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) eta)
          (enc na nb a b
            (hash (exp (gen) (mul l eta)) (exp (gen) (mul x beta))))))
      (send nb))
    (uniq-orig na)
    (uniq-gen x)
    (absent (x l) (x beta))
    (facts (neq a b))
    (gen-st (pv a l)))
  (defrole resp
    (vars (l y rndx) (alpha chi expt) (a b name) (na nb data)
      (priv-stor locn))
    (trace (load priv-stor (pv b l))
      (recv
        (sig (body a (exp (gen) alpha) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) chi)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y alpha)) (exp (gen) (mul l chi))))))
      (recv nb) (send "done"))
    (uniq-orig nb)
    (uniq-gen y)
    (absent (y l) (y alpha) (y chi))
    (facts (neq a b))
    (gen-st (pv b l)))
  (defrole ltx-gen
    (vars (self name) (l rndx) (priv-stor locn) (ignore mesg))
    (trace (load priv-stor ignore) (stor priv-stor (pv self l))
      (send
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self))))
    (uniq-orig l))
  (defrole ltx-disclose
    (vars (self name) (l rndx) (priv-stor locn))
    (trace (load priv-stor (pv self l)) (stor priv-stor "nil") (send l))
    (gen-st (pv self l)))
  (defrule undisclosed-not-disclosed
    (forall ((z strd) (l rndx))
      (implies
        (and (fact undisclosed l) (p "ltx-disclose" z (idx 2))
          (p "ltx-disclose" "l" z l))
        (false))))
  (defrule ltx-gen-once-inference
    (forall ((z1 z2 strd) (self name))
      (implies
        (and (fact ltx-gen-once self) (p "ltx-gen" z1 (idx 2))
          (p "ltx-gen" "self" z1 self) (p "ltx-gen" z2 (idx 2))
          (p "ltx-gen" "self" z2 self))
        (= z1 z2))))
  (defrule eq-means-=
    (forall ((v1 v2 mesg)) (implies (fact eq v1 v2) (= v1 v2))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defgenrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2)) (false))))
  (defgenrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defgenrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defgenrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1)))))
  (defgenrule fact-init-neq0
    (forall ((z strd) (b a name))
      (implies
        (and (p "init" z (idx 2)) (p "init" "a" z a) (p "init" "b" z b))
        (fact neq a b))))
  (defgenrule fact-resp-neq0
    (forall ((z strd) (b a name))
      (implies
        (and (p "resp" z (idx 2)) (p "resp" "a" z a) (p "resp" "b" z b))
        (fact neq a b))))
  (defgenrule trRl_ltx-gen-at-1
    (forall ((z strd))
      (implies (p "ltx-gen" z (idx 2)) (trans z (idx 1)))))
  (defgenrule trRl_ltx-gen-at-0
    (forall ((z strd))
      (implies (p "ltx-gen" z (idx 2)) (trans z (idx 0)))))
  (defgenrule trRl_ltx-disclose-at-1
    (forall ((z strd))
      (implies (p "ltx-disclose" z (idx 2)) (trans z (idx 1)))))
  (defgenrule trRl_ltx-disclose-at-0
    (forall ((z strd))
      (implies (p "ltx-disclose" z (idx 2)) (trans z (idx 0)))))
  (defgenrule gen-st-init-0
    (forall ((z strd) (a name) (l rndx))
      (implies
        (and (p "init" z (idx 1)) (p "init" "l" z l) (p "init" "a" z a))
        (gen-st (pv a l)))))
  (defgenrule gen-st-resp-0
    (forall ((z strd) (b name) (l rndx))
      (implies
        (and (p "resp" z (idx 1)) (p "resp" "l" z l) (p "resp" "b" z b))
        (gen-st (pv b l)))))
  (defgenrule gen-st-ltx-disclose-0
    (forall ((z strd) (self name) (l rndx))
      (implies
        (and (p "ltx-disclose" z (idx 1)) (p "ltx-disclose" "l" z l)
          (p "ltx-disclose" "self" z self)) (gen-st (pv self l)))))
  (lang (sig sign) (body (tuple 3)) (pv (tuple 2))))

(defskeleton dhcr-umx
  (vars (na nb data) (a b name) (pt pval) (priv-stor locn) (l x rndx)
    (eta beta expt))
  (deflistener (hash (exp (gen) (mul l eta)) (exp (gen) (mul x beta))))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (x x) (beta beta) (eta eta))
  (non-orig (privk "sig" b))
  (uniq-orig na)
  (uniq-gen x)
  (absent (x l) (x beta))
  (facts (neq a b) (undisclosed beta))
  (goals
    (forall
      ((z zl strd) (na nb data) (a b name) (l x rndx) (eta beta expt))
      (implies
        (and (p "init" z 4) (p "init" "na" z na) (p "init" "nb" z nb)
          (p "init" "a" z a) (p "init" "b" z b) (p "init" "l" z l)
          (p "init" "x" z x) (p "init" "beta" z beta)
          (p "init" "eta" z eta) (non (privk "sig" b)) (ugen x)
          (uniq-at na z 2) (fact neq a b) (fact undisclosed beta)
          (p "" zl 2)
          (p "" "x" zl
            (hash (exp (exp (gen) eta) l) (exp (exp (gen) beta) x))))
        (false))))
  (traces
    ((recv (hash (exp (gen) (mul l eta)) (exp (gen) (mul x beta))))
      (send (hash (exp (gen) (mul l eta)) (exp (gen) (mul x beta)))))
    ((load priv-stor (cat pt (pv a l)))
      (recv
        (sig (body b (exp (gen) beta) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) eta)
          (enc na nb a b
            (hash (exp (gen) (mul l eta)) (exp (gen) (mul x beta))))))))
  (label 78)
  (unrealized (0 0) (1 1))
  (preskeleton)
  (origs (na (1 2)))
  (ugens (x (1 2)))
  (comment "Not a skeleton"))

(comment "Nothing left to do")
