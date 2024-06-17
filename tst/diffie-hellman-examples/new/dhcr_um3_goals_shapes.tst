(comment "CPSA 4.4.4")
(comment "Extracted shapes")

(herald "DHCR: unified model (UM) three-component version" (bound 30)
  (limit 8000) (algebra diffie-hellman))

(comment "CPSA 4.4.4")

(comment "All input read from dhcr_um3_goals.scm")

(comment "Step count limited to 8000")

(comment "Strand count bounded at 30")

(defprotocol dhcr-um3 diffie-hellman
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
            (hash (exp (gen) (mul l eta)) (exp (gen) (mul x beta))
              (exp (gen) (mul x eta)))))) (send nb))
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
            (hash (exp (gen) (mul y alpha)) (exp (gen) (mul l chi))
              (exp (gen) (mul y chi)))))) (recv nb) (send "done"))
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

(defskeleton dhcr-um3
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
            (hash (exp (gen) (mul l eta)) (exp (gen) (mul l-peer x))
              (exp (gen) (mul x eta))))))))
  (label 0)
  (unrealized (0 1))
  (origs (na (0 2)))
  (ugens (x (0 2)))
  (comment "Not closed under rules"))

(defskeleton dhcr-um3
  (vars (ignore ignore-0 mesg) (na nb data) (b self name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn)
    (y x l l-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a self) (b b)
    (priv-stor priv-stor-0) (l l-0) (x x) (beta l) (eta y))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l))
  (defstrand resp 4 (na na) (nb nb) (a self) (b b) (priv-stor priv-stor)
    (l l) (y y) (alpha l-0) (chi x))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l-0))
  (precedes ((0 2) (2 2)) ((1 1) (2 0)) ((1 2) (0 1)) ((2 3) (0 3))
    ((3 1) (0 0)) ((3 2) (2 1)))
  (non-orig (privk "sig" b))
  (uniq-orig na nb l l-0)
  (uniq-gen y x)
  (absent (y x) (y l) (y l-0) (x l) (x l-0))
  (gen-st (pv b l) (pv self l-0))
  (facts (neq b self) (neq self b) (undisclosed l))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation nonce-test (displaced 1 4 ltx-gen 3) (exp (gen) l-0) (3 1))
  (strand-map 0 3 1 2)
  (traces
    ((load priv-stor-0 (cat pt-2 (pv self l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na self b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb self b
            (hash (exp (gen) (mul y l-0)) (exp (gen) (mul x l))
              (exp (gen) (mul y x)))))))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt-0 (pv b l)))
      (recv
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self))) (recv (cat na self b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb self b
            (hash (exp (gen) (mul y l-0)) (exp (gen) (mul x l))
              (exp (gen) (mul y x)))))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv self l-0)))
      (send
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self)))))
  (label 9)
  (parent 0)
  (realized)
  (shape)
  (satisfies yes)
  (maps
    ((0)
      ((na na) (nb nb) (a self) (b b) (l l-0) (l-peer l) (x x) (eta y)
        (priv-stor priv-stor-0))))
  (origs (l-0 (3 1)) (pt-2 (3 1)) (l (1 1)) (pt-0 (1 1)) (nb (2 3))
    (na (0 2)))
  (ugens (y (2 3)) (x (0 2))))

(defskeleton dhcr-um3
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (y x l l-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-0) (x x) (beta l) (eta y))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l))
  (defstrand resp 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor-0)
    (l l) (y y) (alpha l-0) (chi x))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l-0))
  (precedes ((0 2) (3 2)) ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0))
    ((2 2) (0 1)) ((3 3) (0 3)) ((4 2) (3 1)))
  (non-orig (privk "sig" b))
  (uniq-orig na nb l l-0)
  (uniq-gen y x)
  (absent (y x) (y l) (y l-0) (x l) (x l-0))
  (gen-st (pv a l-0) (pv b l))
  (facts (neq b a) (neq a b) (undisclosed l))
  (leads-to ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (4 0))
  (strand-map 0 1 2 3 5)
  (traces
    ((load priv-stor (cat pt (pv a l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l-0)) (exp (gen) (mul x l))
              (exp (gen) (mul y x)))))))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l-0))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-0 (cat pt-2 (pv b l)))
      (recv
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l-0)) (exp (gen) (mul x l))
              (exp (gen) (mul y x)))))))
    ((load priv-stor (cat pt (pv a l-0)))
      (stor priv-stor (cat pt-3 "nil")) (send l-0)))
  (label 93)
  (parent 0)
  (realized)
  (shape)
  (satisfies yes)
  (maps
    ((0)
      ((na na) (nb nb) (a a) (b b) (l l-0) (l-peer l) (x x) (eta y)
        (priv-stor priv-stor))))
  (origs (pt-3 (4 1)) (l (2 1)) (pt-2 (2 1)) (nb (3 3)) (l-0 (1 1))
    (pt (1 1)) (na (0 2)))
  (ugens (y (3 3)) (x (0 2))))

(comment "Nothing left to do")

(defprotocol dhcr-um3 diffie-hellman
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
            (hash (exp (gen) (mul l eta)) (exp (gen) (mul x beta))
              (exp (gen) (mul x eta)))))) (send nb))
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
            (hash (exp (gen) (mul y alpha)) (exp (gen) (mul l chi))
              (exp (gen) (mul y chi)))))) (recv nb) (send "done"))
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

(defskeleton dhcr-um3
  (vars (na nb data) (a b name) (pt pval) (priv-stor locn) (l x rndx)
    (eta beta expt))
  (deflistener
    (hash (exp (gen) (mul l eta)) (exp (gen) (mul x beta))
      (exp (gen) (mul x eta))))
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
            (hash (exp (exp (gen) eta) l) (exp (exp (gen) beta) x)
              (exp (exp (gen) eta) x)))) (false))))
  (traces
    ((recv
       (hash (exp (gen) (mul l eta)) (exp (gen) (mul x beta))
         (exp (gen) (mul x eta))))
      (send
        (hash (exp (gen) (mul l eta)) (exp (gen) (mul x beta))
          (exp (gen) (mul x eta)))))
    ((load priv-stor (cat pt (pv a l)))
      (recv
        (sig (body b (exp (gen) beta) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) eta)
          (enc na nb a b
            (hash (exp (gen) (mul l eta)) (exp (gen) (mul x beta))
              (exp (gen) (mul x eta))))))))
  (label 168)
  (unrealized (0 0) (1 1))
  (preskeleton)
  (origs (na (1 2)))
  (ugens (x (1 2)))
  (comment "Not a skeleton"))

(comment "Nothing left to do")

(defprotocol dhcr-um3 diffie-hellman
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
            (hash (exp (gen) (mul l eta)) (exp (gen) (mul x beta))
              (exp (gen) (mul x eta)))))) (send nb))
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
            (hash (exp (gen) (mul y alpha)) (exp (gen) (mul l chi))
              (exp (gen) (mul y chi)))))) (recv nb) (send "done"))
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

(defskeleton dhcr-um3
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
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))
              (exp (gen) (mul x y)))))) (send nb)))
  (label 351)
  (unrealized (2 0))
  (preskeleton)
  (origs (pt-2 (1 1)) (pt-0 (0 1)) (na (3 2)))
  (ugens (x (3 2)))
  (comment "Not a skeleton"))

(comment "Nothing left to do")

(defprotocol dhcr-um3 diffie-hellman
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
            (hash (exp (gen) (mul l eta)) (exp (gen) (mul x beta))
              (exp (gen) (mul x eta)))))) (send nb))
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
            (hash (exp (gen) (mul y alpha)) (exp (gen) (mul l chi))
              (exp (gen) (mul y chi)))))) (recv nb) (send "done"))
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

(defskeleton dhcr-um3
  (vars (na nb data) (a b self self-0 name)
    (pt pt-0 pt-1 pt-2 pt-3 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (ltxa ltxb y rndx)
    (chi expt))
  (defstrand ltx-disclose 3 (self self-0) (priv-stor priv-stor)
    (l ltxb))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor-0)
    (l ltxa))
  (deflistener
    (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb chi))
      (exp (gen) (mul y chi))))
  (defstrand resp 6 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor-1)
    (l ltxa) (y y) (alpha ltxb) (chi chi))
  (precedes ((3 5) (0 0)) ((3 5) (1 0)))
  (uniq-orig nb)
  (uniq-gen y)
  (absent (y ltxa) (y ltxb) (y chi))
  (facts (neq a b))
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
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb chi))
              (exp (gen) (mul y chi))))
          (p "ltx-disclose" "self" z-1 self)
          (p "ltx-disclose" "l" z-1 ltxa)
          (p "ltx-disclose" "self" z-2 self-0)
          (p "ltx-disclose" "l" z-2 ltxb) (prec z 5 z-1 0)
          (prec z 5 z-2 0) (ugen y) (uniq-at nb z 3) (fact neq a b))
        (false))))
  (traces
    ((load priv-stor (cat pt (pv self-0 ltxb)))
      (stor priv-stor (cat pt-0 "nil")) (send ltxb))
    ((load priv-stor-0 (cat pt-1 (pv self ltxa)))
      (stor priv-stor-0 (cat pt-2 "nil")) (send ltxa))
    ((recv
       (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb chi))
         (exp (gen) (mul y chi))))
      (send
        (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb chi))
          (exp (gen) (mul y chi)))))
    ((load priv-stor-1 (cat pt-3 (pv b ltxa)))
      (recv
        (sig (body a (exp (gen) ltxb) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) chi)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxb y)) (exp (gen) (mul ltxa chi))
              (exp (gen) (mul y chi)))))) (recv nb) (send "done")))
  (label 3080)
  (unrealized (2 0))
  (preskeleton)
  (origs (pt-2 (1 1)) (pt-0 (0 1)) (nb (3 3)))
  (ugens (y (3 3)))
  (comment "Not a skeleton"))

(comment "Nothing left to do")
