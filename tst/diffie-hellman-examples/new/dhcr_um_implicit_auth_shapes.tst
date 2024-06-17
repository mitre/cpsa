(comment "CPSA 4.4.4")
(comment "Extracted shapes")

(herald "DHCR: unified model (UM) original" (bound 30) (limit 4000)
  (goals-sat) (algebra diffie-hellman))

(comment "CPSA 4.4.4")

(comment "All input read from dhcr_um_implicit_auth.scm")

(comment "Step count limited to 4000")

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
  (vars (na nb na-0 nb-0 data) (a b a-0 b-0 name) (pt pt-0 pval)
    (priv-stor priv-stor-0 locn) (ltxa ltxb x y rndx)
    (eta chi beta alpha expt))
  (defstrand resp 4 (na na) (nb nb) (a a-0) (b b) (priv-stor priv-stor)
    (l ltxb) (y y) (alpha alpha) (chi chi))
  (defstrand init 4 (na na-0) (nb nb-0) (a a) (b b-0)
    (priv-stor priv-stor-0) (l ltxa) (x x) (beta beta) (eta eta))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig nb na-0)
  (uniq-gen x y)
  (absent (x ltxa) (x beta) (y ltxb) (y chi) (y alpha))
  (facts
    (eq (hash (exp (gen) (mul ltxa beta)) (exp (gen) (mul x eta)))
      (hash (exp (gen) (mul ltxb alpha)) (exp (gen) (mul y chi))))
    (neq ltxa ltxb) (undisclosed ltxa) (undisclosed beta)
    (undisclosed ltxb) (undisclosed alpha))
  (goals
    (forall
      ((zi zr strd) (ltxa ltxb x y rndx) (eta chi beta alpha expt)
        (a b a-0 b-0 name))
      (implies
        (and (p "init" zi 4) (p "init" "l" zi ltxa)
          (p "init" "beta" zi beta) (p "init" "x" zi x)
          (p "init" "eta" zi eta) (p "init" "a" zi a)
          (p "init" "b" zi b-0) (p "resp" zr 4) (p "resp" "l" zr ltxb)
          (p "resp" "alpha" zr alpha) (p "resp" "y" zr y)
          (p "resp" "chi" zr chi) (p "resp" "a" zr a-0)
          (p "resp" "b" zr b)
          (fact eq
            (hash (exp (exp (gen) beta) ltxa) (exp (exp (gen) eta) x))
            (hash (exp (exp (gen) alpha) ltxb) (exp (exp (gen) chi) y)))
          (non (privk "sig" b)) (non (privk "sig" a))
          (fact neq ltxa ltxb) (fact undisclosed ltxa)
          (fact undisclosed beta) (fact undisclosed ltxb)
          (fact undisclosed alpha))
        (and (= a-0 a) (= b-0 b) (= beta ltxb) (= alpha ltxa)))))
  (traces
    ((load priv-stor (cat pt (pv b ltxb)))
      (recv
        (sig (body a-0 (exp (gen) alpha) (pubk "sig" a-0))
          (privk "sig" a-0))) (recv (cat na a-0 b (exp (gen) chi)))
      (send
        (cat (exp (gen) y)
          (enc na nb a-0 b
            (hash (exp (gen) (mul ltxb alpha))
              (exp (gen) (mul y chi)))))))
    ((load priv-stor-0 (cat pt-0 (pv a ltxa)))
      (recv
        (sig (body b-0 (exp (gen) beta) (pubk "sig" b-0))
          (privk "sig" b-0))) (send (cat na-0 a b-0 (exp (gen) x)))
      (recv
        (cat (exp (gen) eta)
          (enc na-0 nb-0 a b-0
            (hash (exp (gen) (mul ltxa beta))
              (exp (gen) (mul x eta))))))))
  (label 0)
  (realized)
  (origs (na-0 (1 2)) (nb (0 3)))
  (ugens (x (1 2)) (y (0 3)))
  (comment "Not closed under rules"))

(comment "Nothing left to do")
