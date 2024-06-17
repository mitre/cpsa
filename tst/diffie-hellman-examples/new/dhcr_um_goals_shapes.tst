(comment "CPSA 4.4.4")
(comment "Extracted shapes")

(herald "DHCR: unified model (UM) original" (bound 30) (limit 8000)
  (goals-sat) (algebra diffie-hellman))

(comment "CPSA 4.4.4")

(comment "All input read from dhcr_um_goals.scm")

(comment "Step count limited to 8000")

(comment "Strand count bounded at 30")

(defprotocol dhcr-um diffie-hellman
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
            (hash (exp (gen) (mul l beta)) (exp (gen) (mul x eta))))))
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
            (hash (exp (gen) (mul l alpha)) (exp (gen) (mul y chi))))))
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

(defskeleton dhcr-um
  (vars (na nb data) (a b name) (pt pval) (priv-stor locn)
    (l l-peer x rndx) (eta expt))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (x x) (beta l-peer) (eta eta))
  (non-orig (privk "sig" b))
  (uniq-orig na)
  (uniq-gen x)
  (absent (x l) (x l-peer))
  (facts (neq a b) (undisclosed l) (undisclosed l-peer))
  (goals
    (forall
      ((na nb data) (a b name) (priv-stor locn) (l l-peer x rndx)
        (eta expt) (z strd))
      (implies
        (and (p "init" z 4) (p "init" "na" z na) (p "init" "nb" z nb)
          (p "init" "a" z a) (p "init" "b" z b)
          (p "init" "priv-stor" z priv-stor) (p "init" "l" z l)
          (p "init" "x" z x) (p "init" "beta" z l-peer)
          (p "init" "eta" z eta) (non (privk "sig" b)) (ugen x)
          (uniq-at na z 2) (fact neq a b) (fact undisclosed l)
          (fact undisclosed l-peer))
        (exists ((z-1 strd) (y rndx) (w expt))
          (and (= eta (mul w y)) (p "resp" z-1 4) (p "resp" "na" z-1 na)
            (p "resp" "nb" z-1 nb) (p "resp" "a" z-1 a)
            (p "resp" "b" z-1 b) (p "resp" "l" z-1 l-peer)
            (p "resp" "y" z-1 y) (p "resp" "alpha" z-1 l)
            (p "resp" "chi" z-1 (mul y w)) (prec z 2 z-1 2) (ugen y)
            (uniq-at nb z-1 3))))))
  (traces
    ((load priv-stor (cat pt (pv a l)))
      (recv
        (sig (body b (exp (gen) l-peer) (pubk "sig" b))
          (privk "sig" b))) (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) eta)
          (enc na nb a b
            (hash (exp (gen) (mul l l-peer))
              (exp (gen) (mul x eta))))))))
  (label 0)
  (unrealized (0 1))
  (origs (na (0 2)))
  (ugens (x (0 2)))
  (comment "Not closed under rules"))

(comment "Nothing left to do")

(defprotocol dhcr-um diffie-hellman
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
            (hash (exp (gen) (mul l beta)) (exp (gen) (mul x eta))))))
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
            (hash (exp (gen) (mul l alpha)) (exp (gen) (mul y chi))))))
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

(defskeleton dhcr-um
  (vars (na nb data) (a b name) (pt pval) (priv-stor locn)
    (l l-peer y rndx) (chi expt))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (y y) (alpha l-peer) (chi chi))
  (non-orig (privk "sig" a))
  (uniq-orig nb)
  (uniq-gen y)
  (absent (y l) (y l-peer) (y chi))
  (facts (neq a b) (undisclosed l) (undisclosed l-peer))
  (goals
    (forall
      ((z strd) (na nb data) (a b name) (l l-peer y rndx) (chi expt))
      (implies
        (and (p "resp" z 5) (p "resp" "na" z na) (p "resp" "nb" z nb)
          (p "resp" "a" z a) (p "resp" "b" z b) (p "resp" "l" z l)
          (p "resp" "y" z y) (p "resp" "alpha" z l-peer)
          (p "resp" "chi" z chi) (non (privk "sig" a)) (ugen y)
          (uniq-at nb z 3) (fact neq a b) (fact undisclosed l)
          (fact undisclosed l-peer))
        (exists ((z-1 strd) (x rndx) (w expt))
          (and (= chi (mul x w)) (p "init" z-1 5)
            (p "resp" "chi" z (mul x w)) (p "init" "na" z-1 na)
            (p "init" "nb" z-1 nb) (p "init" "a" z-1 a)
            (p "init" "b" z-1 b) (p "init" "l" z-1 l-peer)
            (p "init" "x" z-1 x) (p "init" "beta" z-1 l)
            (p "init" "eta" z-1 (mul y w)) (prec z 3 z-1 3)
            (prec z-1 2 z 2) (prec z-1 4 z 4) (ugen x)
            (uniq-at na z-1 2))))))
  (traces
    ((load priv-stor (cat pt (pv b l)))
      (recv
        (sig (body a (exp (gen) l-peer) (pubk "sig" a))
          (privk "sig" a))) (recv (cat na a b (exp (gen) chi)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul l l-peer)) (exp (gen) (mul y chi))))))
      (recv nb)))
  (label 17)
  (unrealized (0 1))
  (origs (nb (0 3)))
  (ugens (y (0 3)))
  (comment "Not closed under rules"))

(comment "Nothing left to do")

(defprotocol dhcr-um diffie-hellman
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
            (hash (exp (gen) (mul l beta)) (exp (gen) (mul x eta))))))
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
            (hash (exp (gen) (mul l alpha)) (exp (gen) (mul y chi))))))
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

(defskeleton dhcr-um
  (vars (na nb data) (a b name) (pt pval) (priv-stor locn) (l x rndx)
    (eta beta expt))
  (deflistener (hash (exp (gen) (mul l beta)) (exp (gen) (mul x eta))))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (x x) (beta beta) (eta eta))
  (non-orig (privk "sig" b))
  (uniq-orig na)
  (uniq-gen x)
  (absent (x l) (x beta))
  (facts (neq a b) (undisclosed l) (undisclosed beta))
  (goals
    (forall
      ((z zl strd) (na nb data) (a b name) (priv-stor locn) (l x rndx)
        (eta beta expt))
      (implies
        (and (p "init" z 4) (p "init" "na" z na) (p "init" "nb" z nb)
          (p "init" "a" z a) (p "init" "b" z b)
          (p "init" "priv-stor" z priv-stor) (p "init" "l" z l)
          (p "init" "x" z x) (p "init" "beta" z beta)
          (p "init" "eta" z eta) (non (privk "sig" b)) (ugen x)
          (uniq-at na z 2) (fact neq a b) (fact undisclosed l)
          (fact undisclosed beta) (p "" zl 2)
          (p "" "x" zl
            (hash (exp (exp (gen) beta) l) (exp (exp (gen) eta) x))))
        (false))))
  (traces
    ((recv (hash (exp (gen) (mul l beta)) (exp (gen) (mul x eta))))
      (send (hash (exp (gen) (mul l beta)) (exp (gen) (mul x eta)))))
    ((load priv-stor (cat pt (pv a l)))
      (recv
        (sig (body b (exp (gen) beta) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) eta)
          (enc na nb a b
            (hash (exp (gen) (mul l beta)) (exp (gen) (mul x eta))))))))
  (label 34)
  (unrealized (0 0) (1 1))
  (preskeleton)
  (origs (na (1 2)))
  (ugens (x (1 2)))
  (comment "Not a skeleton"))

(comment "Nothing left to do")

(defprotocol dhcr-um diffie-hellman
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
            (hash (exp (gen) (mul l beta)) (exp (gen) (mul x eta))))))
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
            (hash (exp (gen) (mul l alpha)) (exp (gen) (mul y chi))))))
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

(defskeleton dhcr-um
  (vars (na nb data) (a b self self-0 name)
    (pt pt-0 pt-1 pt-2 pt-3 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (ltxa ltxb x rndx)
    (y expt))
  (defstrand ltx-disclose 3 (self self-0) (priv-stor priv-stor)
    (l ltxb))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor-0)
    (l ltxa))
  (deflistener (hash (exp (gen) (mul ltxa ltxb)) (exp (gen) (mul x y))))
  (defstrand init 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor-1)
    (l ltxa) (x x) (beta ltxb) (eta y))
  (precedes ((3 4) (0 0)) ((3 4) (1 0)))
  (uniq-orig na)
  (uniq-gen x)
  (absent (x ltxa) (x ltxb))
  (goals
    (forall
      ((na nb data) (a b self self-0 name) (ltxa ltxb x rndx) (y expt)
        (z z-0 z-1 z-2 strd))
      (implies
        (and (p "init" z 5) (p "" z-0 2) (p "ltx-disclose" z-1 3)
          (p "ltx-disclose" z-2 3) (p "init" "na" z na)
          (p "init" "nb" z nb) (p "init" "a" z a) (p "init" "b" z b)
          (p "init" "l" z ltxa) (p "init" "x" z x)
          (p "init" "beta" z ltxb) (p "init" "eta" z y)
          (p "" "x" z-0
            (hash (exp (gen) (mul ltxa ltxb)) (exp (gen) (mul x y))))
          (p "ltx-disclose" "self" z-1 self)
          (p "ltx-disclose" "l" z-1 ltxa)
          (p "ltx-disclose" "self" z-2 self-0)
          (p "ltx-disclose" "l" z-2 ltxb) (ugen x) (uniq-at na z 2)
          (prec z 4 z-1 0) (prec z 4 z-2 0)) (false))))
  (traces
    ((load priv-stor (cat pt (pv self-0 ltxb)))
      (stor priv-stor (cat pt-0 "nil")) (send ltxb))
    ((load priv-stor-0 (cat pt-1 (pv self ltxa)))
      (stor priv-stor-0 (cat pt-2 "nil")) (send ltxa))
    ((recv (hash (exp (gen) (mul ltxa ltxb)) (exp (gen) (mul x y))))
      (send (hash (exp (gen) (mul ltxa ltxb)) (exp (gen) (mul x y)))))
    ((load priv-stor-1 (cat pt-3 (pv a ltxa)))
      (recv
        (sig (body b (exp (gen) ltxb) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa ltxb)) (exp (gen) (mul x y))))))
      (send nb)))
  (label 111)
  (unrealized (2 0))
  (preskeleton)
  (origs (pt-2 (1 1)) (pt-0 (0 1)) (na (3 2)))
  (ugens (x (3 2)))
  (comment "Not a skeleton"))

(comment "Nothing left to do")

(defprotocol dhcr-um diffie-hellman
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
            (hash (exp (gen) (mul l beta)) (exp (gen) (mul x eta))))))
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
            (hash (exp (gen) (mul l alpha)) (exp (gen) (mul y chi))))))
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

(defskeleton dhcr-um
  (vars (na nb data) (a b self self-0 name)
    (pt pt-0 pt-1 pt-2 pt-3 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (ltxa ltxb y rndx)
    (chi expt))
  (defstrand ltx-disclose 3 (self self-0) (priv-stor priv-stor)
    (l ltxb))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor-0)
    (l ltxa))
  (deflistener
    (hash (exp (gen) (mul ltxa ltxb)) (exp (gen) (mul y chi))))
  (defstrand resp 6 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor-1)
    (l ltxa) (y y) (alpha ltxb) (chi chi))
  (precedes ((3 5) (0 0)) ((3 5) (1 0)))
  (uniq-orig nb)
  (uniq-gen y)
  (absent (y ltxa) (y ltxb) (y chi))
  (goals
    (forall
      ((na nb data) (a b self self-0 name) (ltxa ltxb y rndx) (chi expt)
        (z z-0 z-1 z-2 strd))
      (implies
        (and (p "resp" z 6) (p "" z-0 2) (p "ltx-disclose" z-1 3)
          (p "ltx-disclose" z-2 3) (p "resp" "na" z na)
          (p "resp" "nb" z nb) (p "resp" "a" z a) (p "resp" "b" z b)
          (p "resp" "l" z ltxa) (p "resp" "y" z y)
          (p "resp" "alpha" z ltxb) (p "resp" "chi" z chi)
          (p "" "x" z-0
            (hash (exp (gen) (mul ltxa ltxb)) (exp (gen) (mul y chi))))
          (p "ltx-disclose" "self" z-1 self)
          (p "ltx-disclose" "l" z-1 ltxa)
          (p "ltx-disclose" "self" z-2 self-0)
          (p "ltx-disclose" "l" z-2 ltxb) (prec z 5 z-1 0)
          (prec z 5 z-2 0) (ugen y) (uniq-at nb z 3)) (false))))
  (traces
    ((load priv-stor (cat pt (pv self-0 ltxb)))
      (stor priv-stor (cat pt-0 "nil")) (send ltxb))
    ((load priv-stor-0 (cat pt-1 (pv self ltxa)))
      (stor priv-stor-0 (cat pt-2 "nil")) (send ltxa))
    ((recv (hash (exp (gen) (mul ltxa ltxb)) (exp (gen) (mul y chi))))
      (send (hash (exp (gen) (mul ltxa ltxb)) (exp (gen) (mul y chi)))))
    ((load priv-stor-1 (cat pt-3 (pv b ltxa)))
      (recv
        (sig (body a (exp (gen) ltxb) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) chi)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa ltxb))
              (exp (gen) (mul y chi)))))) (recv nb) (send "done")))
  (label 2391)
  (unrealized (2 0))
  (preskeleton)
  (origs (pt-2 (1 1)) (pt-0 (0 1)) (nb (3 3)))
  (ugens (y (3 3)))
  (comment "Not a skeleton"))

(comment "Nothing left to do")
