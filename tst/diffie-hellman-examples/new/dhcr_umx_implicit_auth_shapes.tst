(comment "CPSA 4.4.4")
(comment "Extracted shapes")

(herald "DHCR: unified model (UM) with criss-cross key derivation"
  (bound 30) (limit 4000) (algebra diffie-hellman))

(comment "CPSA 4.4.4")

(comment "All input read from dhcr_umx_implicit_auth.scm")

(comment "Step count limited to 4000")

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
    (eq (hash (exp (gen) (mul ltxa eta)) (exp (gen) (mul x beta)))
      (hash (exp (gen) (mul y alpha)) (exp (gen) (mul ltxb chi))))
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
            (hash (exp (exp (gen) eta) ltxa) (exp (exp (gen) beta) x))
            (hash (exp (exp (gen) alpha) y) (exp (exp (gen) chi) ltxb)))
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
            (hash (exp (gen) (mul y alpha))
              (exp (gen) (mul ltxb chi)))))))
    ((load priv-stor-0 (cat pt-0 (pv a ltxa)))
      (recv
        (sig (body b-0 (exp (gen) beta) (pubk "sig" b-0))
          (privk "sig" b-0))) (send (cat na-0 a b-0 (exp (gen) x)))
      (recv
        (cat (exp (gen) eta)
          (enc na-0 nb-0 a b-0
            (hash (exp (gen) (mul ltxa eta))
              (exp (gen) (mul x beta))))))))
  (label 0)
  (realized)
  (origs (na-0 (1 2)) (nb (0 3)))
  (ugens (x (1 2)) (y (0 3)))
  (comment "Not closed under rules"))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (b a name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn)
    (y x l l-0 rndx))
  (defstrand resp 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (y y) (alpha l-0) (chi x))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor-0)
    (l l-0) (x x) (beta l) (eta y))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l-0))
  (precedes ((0 3) (1 3)) ((1 2) (0 2)) ((2 1) (0 0)) ((2 2) (1 1))
    ((3 1) (1 0)) ((3 2) (0 1)))
  (non-orig (privk "sig" b) (privk "sig" a))
  (uniq-orig na nb l l-0)
  (uniq-gen y x)
  (absent (y x) (y l) (y l-0) (x l) (x l-0))
  (gen-st (pv b l) (pv a l-0))
  (facts (neq b a) (neq a b)
    (eq (hash (exp (gen) (mul y l-0)) (exp (gen) (mul x l)))
      (hash (exp (gen) (mul y l-0)) (exp (gen) (mul x l)))) (neq l-0 l)
    (undisclosed l-0) (undisclosed l))
  (leads-to ((2 1) (0 0)) ((3 1) (1 0)))
  (rule fact-resp-neq0 trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation encryption-test (displaced 2 4 ltx-gen 3)
    (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)) (0 1))
  (strand-map 0 1 3 2)
  (traces
    ((load priv-stor (cat pt-0 (pv b l)))
      (recv
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l-0)) (exp (gen) (mul x l)))))))
    ((load priv-stor-0 (cat pt-2 (pv a l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l-0)) (exp (gen) (mul x l)))))))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l-0)))
      (send
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))))
  (label 33)
  (parent 0)
  (realized)
  (shape)
  (satisfies yes)
  (maps
    ((0 1)
      ((ltxa l-0) (ltxb l) (x x) (y y) (eta y) (chi x) (beta l)
        (alpha l-0) (a a) (b b) (a-0 a) (b-0 b) (na na) (nb nb)
        (priv-stor priv-stor) (na-0 na) (nb-0 nb)
        (priv-stor-0 priv-stor-0))))
  (origs (l-0 (3 1)) (pt-2 (3 1)) (l (2 1)) (pt-0 (2 1)) (nb (0 3))
    (na (1 2)))
  (ugens (y (0 3)) (x (1 2))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (b a name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn)
    (y x l l-0 rndx))
  (defstrand resp 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (y y) (alpha l-0) (chi x))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor-0)
    (l l-0) (x x) (beta l) (eta y))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l-0))
  (precedes ((0 3) (1 3)) ((1 2) (0 2)) ((2 1) (0 0)) ((2 2) (1 1))
    ((3 1) (1 0)) ((3 2) (0 1)))
  (non-orig (privk "sig" b) (privk "sig" a))
  (uniq-orig na nb l l-0)
  (uniq-gen y x)
  (absent (y x) (y l) (y l-0) (x l) (x l-0) (l-0 (one)))
  (gen-st (pv b l) (pv a l-0))
  (facts (neq b a) (neq a b)
    (eq (hash (exp (gen) (mul y l-0)) (exp (gen) (mul x l)))
      (hash (exp (gen) (mul y l-0)) (exp (gen) (mul x l)))) (neq l-0 l)
    (undisclosed l-0) (undisclosed l))
  (leads-to ((2 1) (0 0)) ((3 1) (1 0)))
  (rule fact-resp-neq0 trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (2 0))
  (strand-map 0 1 3 4)
  (traces
    ((load priv-stor (cat pt-0 (pv b l)))
      (recv
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l-0)) (exp (gen) (mul x l)))))))
    ((load priv-stor-0 (cat pt-2 (pv a l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l-0)) (exp (gen) (mul x l)))))))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l-0)))
      (send
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))))
  (label 75)
  (parent 0)
  (realized)
  (shape)
  (satisfies yes)
  (maps
    ((0 1)
      ((ltxa l-0) (ltxb l) (x x) (y y) (eta y) (chi x) (beta l)
        (alpha l-0) (a a) (b b) (a-0 a) (b-0 b) (na na) (nb nb)
        (priv-stor priv-stor) (na-0 na) (nb-0 nb)
        (priv-stor-0 priv-stor-0))))
  (origs (l-0 (3 1)) (pt-2 (3 1)) (l (2 1)) (pt-0 (2 1)) (nb (0 3))
    (na (1 2)))
  (ugens (y (0 3)) (x (1 2))))

(comment "Nothing left to do")
