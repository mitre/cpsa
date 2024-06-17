(comment "CPSA 4.4.4")
(comment "Extracted shapes")

(herald "DHCR: unified model (UM) original" (bound 30) (limit 4000)
  (algebra diffie-hellman))

(comment "CPSA 4.4.4")

(comment "All input read from dhcr_um.scm")

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

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (b self name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn)
    (l l-0 x y rndx))
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
  (uniq-gen x y)
  (absent (x l) (x l-0) (y l) (y l-0) (y x))
  (gen-st (pv b l) (pv self l-0))
  (facts (neq b self) (neq self b) (undisclosed l-0) (undisclosed l))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation nonce-test (displaced 4 2 resp 4) (exp (gen) y-0) (0 3))
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor-0 (cat pt-2 (pv self l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na self b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb self b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y)))))))
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
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y)))))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv self l-0)))
      (send
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self)))))
  (label 16)
  (parent 0)
  (realized)
  (shape)
  (maps
    ((0)
      ((a self) (b b) (l l-0) (l-peer l) (x x) (eta y) (na na) (nb nb)
        (priv-stor priv-stor-0))))
  (origs (nb (2 3)) (l-0 (3 1)) (pt-2 (3 1)) (l (1 1)) (pt-0 (1 1))
    (na (0 2)))
  (ugens (y (2 3)) (x (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (b self name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn) (l l-0 x rndx)
    (w expt) (y rndx))
  (defstrand init 4 (na na) (nb nb) (a self) (b b)
    (priv-stor priv-stor-0) (l l-0) (x x) (beta l) (eta (mul w y)))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l))
  (defstrand resp 4 (na na) (nb nb) (a self) (b b) (priv-stor priv-stor)
    (l l) (y y) (alpha l-0) (chi (mul x w)))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l-0))
  (precedes ((0 2) (2 2)) ((1 1) (2 0)) ((1 2) (0 1)) ((2 3) (0 3))
    ((3 1) (0 0)) ((3 2) (2 1)))
  (non-orig (privk "sig" b))
  (uniq-orig na nb l l-0)
  (uniq-gen x y)
  (absent (x l) (x l-0) (y l) (y l-0) (y (mul x w)))
  (gen-st (pv b l) (pv self l-0))
  (facts (neq b self) (neq self b) (undisclosed l-0) (undisclosed l))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (4 0))
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor-0 (cat pt-2 (pv self l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na self b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul w y))
          (enc na nb self b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x w y)))))))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt-0 (pv b l)))
      (recv
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self)))
      (recv (cat na self b (exp (gen) (mul x w))))
      (send
        (cat (exp (gen) y)
          (enc na nb self b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x w y)))))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv self l-0)))
      (send
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self)))))
  (label 44)
  (parent 0)
  (realized)
  (shape)
  (maps
    ((0)
      ((a self) (b b) (l l-0) (l-peer l) (x x) (eta (mul w y)) (na na)
        (nb nb) (priv-stor priv-stor-0))))
  (origs (nb (2 3)) (l-0 (3 1)) (pt-2 (3 1)) (l (1 1)) (pt-0 (1 1))
    (na (0 2)))
  (ugens (y (2 3)) (x (0 2))))

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
    (l l-peer x rndx) (eta expt))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (x x) (beta l-peer) (eta eta))
  (non-orig (privk "sig" b))
  (uniq-orig na)
  (uniq-gen x)
  (absent (x l) (x l-peer))
  (facts (neq a b) (undisclosed l-peer))
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
  (label 65)
  (unrealized (0 1))
  (origs (na (0 2)))
  (ugens (x (0 2)))
  (comment "Not closed under rules"))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (b self name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn)
    (l l-0 x y rndx))
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
  (uniq-gen x y)
  (absent (x l) (x l-0) (y l) (y l-0) (y x))
  (gen-st (pv b l) (pv self l-0))
  (facts (neq b self) (neq self b) (undisclosed l))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation nonce-test (displaced 4 2 resp 4) (exp (gen) y-0) (0 3))
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor-0 (cat pt-2 (pv self l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na self b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb self b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y)))))))
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
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y)))))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv self l-0)))
      (send
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self)))))
  (label 81)
  (parent 65)
  (realized)
  (shape)
  (maps
    ((0)
      ((a self) (b b) (l l-0) (l-peer l) (x x) (eta y) (na na) (nb nb)
        (priv-stor priv-stor-0))))
  (origs (nb (2 3)) (l-0 (3 1)) (pt-2 (3 1)) (l (1 1)) (pt-0 (1 1))
    (na (0 2)))
  (ugens (y (2 3)) (x (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (b self name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn) (l l-0 x rndx)
    (w expt) (y rndx))
  (defstrand init 4 (na na) (nb nb) (a self) (b b)
    (priv-stor priv-stor-0) (l l-0) (x x) (beta l) (eta (mul w y)))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l))
  (defstrand resp 4 (na na) (nb nb) (a self) (b b) (priv-stor priv-stor)
    (l l) (y y) (alpha l-0) (chi (mul x w)))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l-0))
  (precedes ((0 2) (2 2)) ((1 1) (2 0)) ((1 2) (0 1)) ((2 3) (0 3))
    ((3 1) (0 0)) ((3 2) (2 1)))
  (non-orig (privk "sig" b))
  (uniq-orig na nb l l-0)
  (uniq-gen x y)
  (absent (x l) (x l-0) (y l) (y l-0) (y (mul x w)))
  (gen-st (pv b l) (pv self l-0))
  (facts (neq b self) (neq self b) (undisclosed l))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (4 0))
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor-0 (cat pt-2 (pv self l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na self b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul w y))
          (enc na nb self b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x w y)))))))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt-0 (pv b l)))
      (recv
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self)))
      (recv (cat na self b (exp (gen) (mul x w))))
      (send
        (cat (exp (gen) y)
          (enc na nb self b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x w y)))))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv self l-0)))
      (send
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self)))))
  (label 116)
  (parent 65)
  (realized)
  (shape)
  (maps
    ((0)
      ((a self) (b b) (l l-0) (l-peer l) (x x) (eta (mul w y)) (na na)
        (nb nb) (priv-stor priv-stor-0))))
  (origs (nb (2 3)) (l-0 (3 1)) (pt-2 (3 1)) (l (1 1)) (pt-0 (1 1))
    (na (0 2)))
  (ugens (y (2 3)) (x (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn) (x rndx)
    (eta expt) (l l-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (x x) (beta l-0) (eta eta))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (precedes ((1 1) (0 0)) ((1 1) (3 0)) ((2 2) (0 1)) ((3 2) (0 3)))
  (non-orig (privk "sig" b))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0))
  (gen-st (pv a l))
  (facts (neq b a) (neq a b) (undisclosed l-0))
  (leads-to ((1 1) (0 0)) ((1 1) (3 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (3 0))
  (strand-map 0 1 2 4)
  (traces
    ((load priv-stor (cat pt (pv a l)))
      (recv
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) eta)
          (enc na nb a b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x eta)))))))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l-0)))
      (send
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt (pv a l)))
      (stor priv-stor (cat pt-3 "nil")) (send l)))
  (label 198)
  (parent 65)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l) (l-peer l-0) (x x) (eta eta) (na na) (nb nb)
        (priv-stor priv-stor))))
  (origs (l-0 (2 1)) (pt-2 (2 1)) (pt-3 (3 1)) (l (1 1)) (pt (1 1))
    (na (0 2)))
  (ugens (x (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (l l-0 x y rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-0) (x x) (beta l) (eta y))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l-0))
  (precedes ((1 1) (0 0)) ((1 1) (3 0)) ((2 2) (0 1)) ((3 2) (0 3)))
  (non-orig (privk "sig" b))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0))
  (gen-st (pv a l-0) (pv b l))
  (facts (neq b a) (neq a b) (undisclosed l))
  (leads-to ((1 1) (0 0)) ((1 1) (3 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization forgot nb)
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor (cat pt (pv a l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y)))))))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l-0))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt (pv a l-0)))
      (stor priv-stor (cat pt-3 "nil")) (send l-0)))
  (label 200)
  (parent 65)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-0) (l-peer l) (x x) (eta y) (na na) (nb nb)
        (priv-stor priv-stor))))
  (origs (pt-3 (3 1)) (l (2 1)) (pt-2 (2 1)) (l-0 (1 1)) (pt (1 1))
    (na (0 2)))
  (ugens (x (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (l l-0 x rndx) (w expt) (y rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-0) (x x) (beta l) (eta (mul w y)))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l-0))
  (precedes ((1 1) (0 0)) ((1 1) (3 0)) ((2 2) (0 1)) ((3 2) (0 3)))
  (non-orig (privk "sig" b))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0))
  (gen-st (pv a l-0) (pv b l))
  (facts (neq b a) (neq a b) (undisclosed l))
  (leads-to ((1 1) (0 0)) ((1 1) (3 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization forgot nb)
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor (cat pt (pv a l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul w y))
          (enc na nb a b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x w y)))))))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l-0))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt (pv a l-0)))
      (stor priv-stor (cat pt-3 "nil")) (send l-0)))
  (label 284)
  (parent 65)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-0) (l-peer l) (x x) (eta (mul w y)) (na na)
        (nb nb) (priv-stor priv-stor))))
  (origs (pt-3 (3 1)) (l (2 1)) (pt-2 (2 1)) (l-0 (1 1)) (pt (1 1))
    (na (0 2)))
  (ugens (x (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (l l-0 x y rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (x x) (beta l-0) (eta y))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (precedes ((1 1) (0 0)) ((1 1) (3 0)) ((2 2) (0 1)) ((3 2) (0 3)))
  (non-orig (privk "sig" b))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0))
  (gen-st (pv a l))
  (facts (neq b a) (neq a b) (undisclosed l-0))
  (leads-to ((1 1) (0 0)) ((1 1) (3 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization forgot nb)
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor (cat pt (pv a l)))
      (recv
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y)))))))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l-0)))
      (send
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt (pv a l)))
      (stor priv-stor (cat pt-3 "nil")) (send l)))
  (label 324)
  (parent 65)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l) (l-peer l-0) (x x) (eta y) (na na) (nb nb)
        (priv-stor priv-stor))))
  (origs (l-0 (2 1)) (pt-2 (2 1)) (pt-3 (3 1)) (l (1 1)) (pt (1 1))
    (na (0 2)))
  (ugens (x (0 2))))

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
    (l l-peer x rndx) (eta expt))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (x x) (beta l-peer) (eta eta))
  (non-orig (privk "sig" b))
  (uniq-orig na)
  (uniq-gen x)
  (absent (x l) (x l-peer))
  (facts (neq a b) (ltx-gen-once a) (undisclosed l-peer))
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
  (label 331)
  (unrealized (0 1))
  (origs (na (0 2)))
  (ugens (x (0 2)))
  (comment "Not closed under rules"))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (b self name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn)
    (l l-0 x y rndx))
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
  (uniq-gen x y)
  (absent (x l) (x l-0) (y l) (y l-0) (y x))
  (gen-st (pv b l) (pv self l-0))
  (facts (neq b self) (neq self b) (ltx-gen-once self) (undisclosed l))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation nonce-test (displaced 4 2 resp 4) (exp (gen) y-0) (0 3))
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor-0 (cat pt-2 (pv self l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na self b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb self b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y)))))))
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
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y)))))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv self l-0)))
      (send
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self)))))
  (label 347)
  (parent 331)
  (realized)
  (shape)
  (maps
    ((0)
      ((a self) (b b) (l l-0) (l-peer l) (x x) (eta y) (na na) (nb nb)
        (priv-stor priv-stor-0))))
  (origs (nb (2 3)) (l-0 (3 1)) (pt-2 (3 1)) (l (1 1)) (pt-0 (1 1))
    (na (0 2)))
  (ugens (y (2 3)) (x (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (b self name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn) (l l-0 x rndx)
    (w expt) (y rndx))
  (defstrand init 4 (na na) (nb nb) (a self) (b b)
    (priv-stor priv-stor-0) (l l-0) (x x) (beta l) (eta (mul w y)))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l))
  (defstrand resp 4 (na na) (nb nb) (a self) (b b) (priv-stor priv-stor)
    (l l) (y y) (alpha l-0) (chi (mul x w)))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l-0))
  (precedes ((0 2) (2 2)) ((1 1) (2 0)) ((1 2) (0 1)) ((2 3) (0 3))
    ((3 1) (0 0)) ((3 2) (2 1)))
  (non-orig (privk "sig" b))
  (uniq-orig na nb l l-0)
  (uniq-gen x y)
  (absent (x l) (x l-0) (y l) (y l-0) (y (mul x w)))
  (gen-st (pv b l) (pv self l-0))
  (facts (neq b self) (neq self b) (ltx-gen-once self) (undisclosed l))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (4 0))
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor-0 (cat pt-2 (pv self l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na self b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul w y))
          (enc na nb self b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x w y)))))))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt-0 (pv b l)))
      (recv
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self)))
      (recv (cat na self b (exp (gen) (mul x w))))
      (send
        (cat (exp (gen) y)
          (enc na nb self b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x w y)))))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv self l-0)))
      (send
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self)))))
  (label 382)
  (parent 331)
  (realized)
  (shape)
  (maps
    ((0)
      ((a self) (b b) (l l-0) (l-peer l) (x x) (eta (mul w y)) (na na)
        (nb nb) (priv-stor priv-stor-0))))
  (origs (nb (2 3)) (l-0 (3 1)) (pt-2 (3 1)) (l (1 1)) (pt-0 (1 1))
    (na (0 2)))
  (ugens (y (2 3)) (x (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn) (x rndx)
    (eta expt) (l l-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (x x) (beta l-0) (eta eta))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (precedes ((1 1) (0 0)) ((1 1) (3 0)) ((2 2) (0 1)) ((3 2) (0 3)))
  (non-orig (privk "sig" b))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0))
  (gen-st (pv a l))
  (facts (neq b a) (neq a b) (ltx-gen-once a) (undisclosed l-0))
  (leads-to ((1 1) (0 0)) ((1 1) (3 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (3 0))
  (strand-map 0 1 2 4)
  (traces
    ((load priv-stor (cat pt (pv a l)))
      (recv
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) eta)
          (enc na nb a b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x eta)))))))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l-0)))
      (send
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt (pv a l)))
      (stor priv-stor (cat pt-3 "nil")) (send l)))
  (label 464)
  (parent 331)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l) (l-peer l-0) (x x) (eta eta) (na na) (nb nb)
        (priv-stor priv-stor))))
  (origs (l-0 (2 1)) (pt-2 (2 1)) (pt-3 (3 1)) (l (1 1)) (pt (1 1))
    (na (0 2)))
  (ugens (x (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (l l-0 x y rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-0) (x x) (beta l) (eta y))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l-0))
  (precedes ((1 1) (0 0)) ((1 1) (3 0)) ((2 2) (0 1)) ((3 2) (0 3)))
  (non-orig (privk "sig" b))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0))
  (gen-st (pv a l-0) (pv b l))
  (facts (neq b a) (neq a b) (ltx-gen-once a) (undisclosed l))
  (leads-to ((1 1) (0 0)) ((1 1) (3 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization forgot nb)
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor (cat pt (pv a l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y)))))))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l-0))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt (pv a l-0)))
      (stor priv-stor (cat pt-3 "nil")) (send l-0)))
  (label 466)
  (parent 331)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-0) (l-peer l) (x x) (eta y) (na na) (nb nb)
        (priv-stor priv-stor))))
  (origs (pt-3 (3 1)) (l (2 1)) (pt-2 (2 1)) (l-0 (1 1)) (pt (1 1))
    (na (0 2)))
  (ugens (x (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (l l-0 x rndx) (w expt) (y rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-0) (x x) (beta l) (eta (mul w y)))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l-0))
  (precedes ((1 1) (0 0)) ((1 1) (3 0)) ((2 2) (0 1)) ((3 2) (0 3)))
  (non-orig (privk "sig" b))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0))
  (gen-st (pv a l-0) (pv b l))
  (facts (neq b a) (neq a b) (ltx-gen-once a) (undisclosed l))
  (leads-to ((1 1) (0 0)) ((1 1) (3 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization forgot nb)
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor (cat pt (pv a l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul w y))
          (enc na nb a b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x w y)))))))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l-0))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt (pv a l-0)))
      (stor priv-stor (cat pt-3 "nil")) (send l-0)))
  (label 550)
  (parent 331)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-0) (l-peer l) (x x) (eta (mul w y)) (na na)
        (nb nb) (priv-stor priv-stor))))
  (origs (pt-3 (3 1)) (l (2 1)) (pt-2 (2 1)) (l-0 (1 1)) (pt (1 1))
    (na (0 2)))
  (ugens (x (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (l l-0 x y rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (x x) (beta l-0) (eta y))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (precedes ((1 1) (0 0)) ((1 1) (3 0)) ((2 2) (0 1)) ((3 2) (0 3)))
  (non-orig (privk "sig" b))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0))
  (gen-st (pv a l))
  (facts (neq b a) (neq a b) (ltx-gen-once a) (undisclosed l-0))
  (leads-to ((1 1) (0 0)) ((1 1) (3 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization forgot nb)
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor (cat pt (pv a l)))
      (recv
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y)))))))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l-0)))
      (send
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt (pv a l)))
      (stor priv-stor (cat pt-3 "nil")) (send l)))
  (label 590)
  (parent 331)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l) (l-peer l-0) (x x) (eta y) (na na) (nb nb)
        (priv-stor priv-stor))))
  (origs (l-0 (2 1)) (pt-2 (2 1)) (pt-3 (3 1)) (l (1 1)) (pt (1 1))
    (na (0 2)))
  (ugens (x (0 2))))

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
  (vars (na nb data) (a b name) (pt pval) (priv-stor locn) (l rndx)
    (l-peer expt) (x rndx) (eta expt))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (x x) (beta l-peer) (eta eta))
  (non-orig (privk "sig" b))
  (uniq-orig na)
  (uniq-gen x)
  (absent (x l) (x l-peer))
  (facts (neq a b) (undisclosed l))
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
  (label 597)
  (unrealized (0 1))
  (origs (na (0 2)))
  (ugens (x (0 2)))
  (comment "Not closed under rules"))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (b self name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn)
    (l l-0 x y rndx))
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
  (uniq-gen x y)
  (absent (x l) (x l-0) (y l) (y l-0) (y x))
  (gen-st (pv b l) (pv self l-0))
  (facts (neq b self) (neq self b) (undisclosed l-0))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation nonce-test (displaced 4 2 resp 4) (exp (gen) y-0) (0 3))
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor-0 (cat pt-2 (pv self l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na self b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb self b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y)))))))
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
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y)))))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv self l-0)))
      (send
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self)))))
  (label 613)
  (parent 597)
  (realized)
  (shape)
  (maps
    ((0)
      ((a self) (b b) (l l-0) (l-peer l) (x x) (eta y) (na na) (nb nb)
        (priv-stor priv-stor-0))))
  (origs (nb (2 3)) (l-0 (3 1)) (pt-2 (3 1)) (l (1 1)) (pt-0 (1 1))
    (na (0 2)))
  (ugens (y (2 3)) (x (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (b self name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn) (l l-0 x rndx)
    (w expt) (y rndx))
  (defstrand init 4 (na na) (nb nb) (a self) (b b)
    (priv-stor priv-stor-0) (l l-0) (x x) (beta l) (eta (mul w y)))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l))
  (defstrand resp 4 (na na) (nb nb) (a self) (b b) (priv-stor priv-stor)
    (l l) (y y) (alpha l-0) (chi (mul x w)))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l-0))
  (precedes ((0 2) (2 2)) ((1 1) (2 0)) ((1 2) (0 1)) ((2 3) (0 3))
    ((3 1) (0 0)) ((3 2) (2 1)))
  (non-orig (privk "sig" b))
  (uniq-orig na nb l l-0)
  (uniq-gen x y)
  (absent (x l) (x l-0) (y l) (y l-0) (y (mul x w)))
  (gen-st (pv b l) (pv self l-0))
  (facts (neq b self) (neq self b) (undisclosed l-0))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (4 0))
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor-0 (cat pt-2 (pv self l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na self b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul w y))
          (enc na nb self b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x w y)))))))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt-0 (pv b l)))
      (recv
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self)))
      (recv (cat na self b (exp (gen) (mul x w))))
      (send
        (cat (exp (gen) y)
          (enc na nb self b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x w y)))))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv self l-0)))
      (send
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self)))))
  (label 647)
  (parent 597)
  (realized)
  (shape)
  (maps
    ((0)
      ((a self) (b b) (l l-0) (l-peer l) (x x) (eta (mul w y)) (na na)
        (nb nb) (priv-stor priv-stor-0))))
  (origs (nb (2 3)) (l-0 (3 1)) (pt-2 (3 1)) (l (1 1)) (pt-0 (1 1))
    (na (0 2)))
  (ugens (y (2 3)) (x (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (b self name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn) (x rndx)
    (eta expt) (l l-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a self) (b b)
    (priv-stor priv-stor-0) (l l-0) (x x) (beta l) (eta eta))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l-0))
  (precedes ((1 1) (2 0)) ((1 2) (0 1)) ((2 2) (0 3)) ((3 1) (0 0))
    ((3 2) (0 3)))
  (non-orig (privk "sig" b))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0))
  (gen-st (pv b l) (pv self l-0))
  (facts (neq b self) (neq self b) (undisclosed l-0))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (2 0))
  (strand-map 0 1 3 4)
  (traces
    ((load priv-stor-0 (cat pt-3 (pv self l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na self b (exp (gen) x)))
      (recv
        (cat (exp (gen) eta)
          (enc na nb self b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x eta)))))))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt-0 (pv b l)))
      (stor priv-stor (cat pt-1 "nil")) (send l))
    ((load priv-stor-0 (cat pt-2 ignore-0))
      (stor priv-stor-0 (cat pt-3 (pv self l-0)))
      (send
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self)))))
  (label 710)
  (parent 597)
  (realized)
  (shape)
  (maps
    ((0)
      ((a self) (b b) (l l-0) (l-peer l) (x x) (eta eta) (na na) (nb nb)
        (priv-stor priv-stor-0))))
  (origs (l-0 (3 1)) (pt-3 (3 1)) (pt-1 (2 1)) (l (1 1)) (pt-0 (1 1))
    (na (0 2)))
  (ugens (x (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (b self name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (l l-0 x y rndx))
  (defstrand init 4 (na na) (nb nb) (a self) (b b)
    (priv-stor priv-stor-0) (l l-0) (x x) (beta l) (eta y))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l-0))
  (precedes ((1 1) (2 0)) ((1 2) (0 1)) ((2 2) (0 3)) ((3 1) (0 0))
    ((3 2) (0 3)))
  (non-orig (privk "sig" b))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0))
  (gen-st (pv b l) (pv self l-0))
  (facts (neq b self) (neq self b) (undisclosed l-0))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization forgot nb)
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor-0 (cat pt-3 (pv self l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na self b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb self b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y)))))))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt-0 (pv b l)))
      (stor priv-stor (cat pt-1 "nil")) (send l))
    ((load priv-stor-0 (cat pt-2 ignore-0))
      (stor priv-stor-0 (cat pt-3 (pv self l-0)))
      (send
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self)))))
  (label 832)
  (parent 597)
  (realized)
  (shape)
  (maps
    ((0)
      ((a self) (b b) (l l-0) (l-peer l) (x x) (eta y) (na na) (nb nb)
        (priv-stor priv-stor-0))))
  (origs (l-0 (3 1)) (pt-3 (3 1)) (pt-1 (2 1)) (l (1 1)) (pt-0 (1 1))
    (na (0 2)))
  (ugens (x (0 2))))

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
  (vars (na nb data) (a b name) (pt pval) (priv-stor locn) (l rndx)
    (l-peer expt) (x rndx) (eta expt))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (x x) (beta l-peer) (eta eta))
  (non-orig (privk "sig" b))
  (uniq-orig na)
  (uniq-gen x)
  (absent (x l) (x l-peer))
  (facts (neq a b))
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
  (label 839)
  (unrealized (0 1))
  (origs (na (0 2)))
  (ugens (x (0 2)))
  (comment "Not closed under rules"))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (b self name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn)
    (l l-0 x y rndx))
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
  (uniq-gen x y)
  (absent (x l) (x l-0) (y l) (y l-0) (y x))
  (gen-st (pv b l) (pv self l-0))
  (facts (neq b self) (neq self b))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation nonce-test (displaced 4 2 resp 4) (exp (gen) y-0) (0 3))
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor-0 (cat pt-2 (pv self l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na self b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb self b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y)))))))
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
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y)))))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv self l-0)))
      (send
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self)))))
  (label 855)
  (parent 839)
  (realized)
  (shape)
  (maps
    ((0)
      ((a self) (b b) (l l-0) (l-peer l) (x x) (eta y) (na na) (nb nb)
        (priv-stor priv-stor-0))))
  (origs (nb (2 3)) (l-0 (3 1)) (pt-2 (3 1)) (l (1 1)) (pt-0 (1 1))
    (na (0 2)))
  (ugens (y (2 3)) (x (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (b self name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn) (l l-0 x rndx)
    (w expt) (y rndx))
  (defstrand init 4 (na na) (nb nb) (a self) (b b)
    (priv-stor priv-stor-0) (l l-0) (x x) (beta l) (eta (mul w y)))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l))
  (defstrand resp 4 (na na) (nb nb) (a self) (b b) (priv-stor priv-stor)
    (l l) (y y) (alpha l-0) (chi (mul x w)))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l-0))
  (precedes ((0 2) (2 2)) ((1 1) (2 0)) ((1 2) (0 1)) ((2 3) (0 3))
    ((3 1) (0 0)) ((3 2) (2 1)))
  (non-orig (privk "sig" b))
  (uniq-orig na nb l l-0)
  (uniq-gen x y)
  (absent (x l) (x l-0) (y l) (y l-0) (y (mul x w)))
  (gen-st (pv b l) (pv self l-0))
  (facts (neq b self) (neq self b))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (4 0))
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor-0 (cat pt-2 (pv self l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na self b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul w y))
          (enc na nb self b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x w y)))))))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt-0 (pv b l)))
      (recv
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self)))
      (recv (cat na self b (exp (gen) (mul x w))))
      (send
        (cat (exp (gen) y)
          (enc na nb self b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x w y)))))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv self l-0)))
      (send
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self)))))
  (label 896)
  (parent 839)
  (realized)
  (shape)
  (maps
    ((0)
      ((a self) (b b) (l l-0) (l-peer l) (x x) (eta (mul w y)) (na na)
        (nb nb) (priv-stor priv-stor-0))))
  (origs (nb (2 3)) (l-0 (3 1)) (pt-2 (3 1)) (l (1 1)) (pt-0 (1 1))
    (na (0 2)))
  (ugens (y (2 3)) (x (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (b self name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn) (x rndx)
    (eta expt) (l l-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a self) (b b)
    (priv-stor priv-stor-0) (l l-0) (x x) (beta l) (eta eta))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l-0))
  (precedes ((1 1) (2 0)) ((1 2) (0 1)) ((2 2) (0 3)) ((3 1) (0 0))
    ((3 2) (0 3)))
  (non-orig (privk "sig" b))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0))
  (gen-st (pv b l) (pv self l-0))
  (facts (neq b self) (neq self b))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (2 0))
  (strand-map 0 1 3 4)
  (traces
    ((load priv-stor-0 (cat pt-3 (pv self l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na self b (exp (gen) x)))
      (recv
        (cat (exp (gen) eta)
          (enc na nb self b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x eta)))))))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt-0 (pv b l)))
      (stor priv-stor (cat pt-1 "nil")) (send l))
    ((load priv-stor-0 (cat pt-2 ignore-0))
      (stor priv-stor-0 (cat pt-3 (pv self l-0)))
      (send
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self)))))
  (label 1042)
  (parent 839)
  (realized)
  (shape)
  (maps
    ((0)
      ((a self) (b b) (l l-0) (l-peer l) (x x) (eta eta) (na na) (nb nb)
        (priv-stor priv-stor-0))))
  (origs (l-0 (3 1)) (pt-3 (3 1)) (pt-1 (2 1)) (l (1 1)) (pt-0 (1 1))
    (na (0 2)))
  (ugens (x (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn) (x rndx)
    (eta expt) (l l-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (x x) (beta l-0) (eta eta))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (precedes ((1 1) (0 0)) ((1 1) (3 0)) ((2 2) (0 1)) ((3 2) (0 3)))
  (non-orig (privk "sig" b))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0))
  (gen-st (pv a l))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (0 0)) ((1 1) (3 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (3 0))
  (strand-map 0 1 2 4)
  (traces
    ((load priv-stor (cat pt (pv a l)))
      (recv
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) eta)
          (enc na nb a b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x eta)))))))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l-0)))
      (send
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt (pv a l)))
      (stor priv-stor (cat pt-3 "nil")) (send l)))
  (label 1045)
  (parent 839)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l) (l-peer l-0) (x x) (eta eta) (na na) (nb nb)
        (priv-stor priv-stor))))
  (origs (l-0 (2 1)) (pt-2 (2 1)) (pt-3 (3 1)) (l (1 1)) (pt (1 1))
    (na (0 2)))
  (ugens (x (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (l l-0 x y rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-0) (x x) (beta l) (eta y))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l-0))
  (precedes ((1 1) (0 0)) ((1 1) (3 0)) ((2 2) (0 1)) ((3 2) (0 3)))
  (non-orig (privk "sig" b))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0))
  (gen-st (pv a l-0) (pv b l))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (0 0)) ((1 1) (3 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization forgot nb)
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor (cat pt (pv a l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y)))))))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l-0))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt (pv a l-0)))
      (stor priv-stor (cat pt-3 "nil")) (send l-0)))
  (label 1048)
  (parent 839)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-0) (l-peer l) (x x) (eta y) (na na) (nb nb)
        (priv-stor priv-stor))))
  (origs (pt-3 (3 1)) (l (2 1)) (pt-2 (2 1)) (l-0 (1 1)) (pt (1 1))
    (na (0 2)))
  (ugens (x (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (l l-0 x rndx) (w expt) (y rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-0) (x x) (beta l) (eta (mul w y)))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l-0))
  (precedes ((1 1) (0 0)) ((1 1) (3 0)) ((2 2) (0 1)) ((3 2) (0 3)))
  (non-orig (privk "sig" b))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0))
  (gen-st (pv a l-0) (pv b l))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (0 0)) ((1 1) (3 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization forgot nb)
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor (cat pt (pv a l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul w y))
          (enc na nb a b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x w y)))))))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l-0))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt (pv a l-0)))
      (stor priv-stor (cat pt-3 "nil")) (send l-0)))
  (label 1253)
  (parent 839)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-0) (l-peer l) (x x) (eta (mul w y)) (na na)
        (nb nb) (priv-stor priv-stor))))
  (origs (pt-3 (3 1)) (l (2 1)) (pt-2 (2 1)) (l-0 (1 1)) (pt (1 1))
    (na (0 2)))
  (ugens (x (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (b self name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (l l-0 x y rndx))
  (defstrand init 4 (na na) (nb nb) (a self) (b b)
    (priv-stor priv-stor-0) (l l-0) (x x) (beta l) (eta y))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l-0))
  (precedes ((1 1) (2 0)) ((1 2) (0 1)) ((2 2) (0 3)) ((3 1) (0 0))
    ((3 2) (0 3)))
  (non-orig (privk "sig" b))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0))
  (gen-st (pv b l) (pv self l-0))
  (facts (neq b self) (neq self b))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization forgot nb)
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor-0 (cat pt-3 (pv self l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na self b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb self b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y)))))))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt-0 (pv b l)))
      (stor priv-stor (cat pt-1 "nil")) (send l))
    ((load priv-stor-0 (cat pt-2 ignore-0))
      (stor priv-stor-0 (cat pt-3 (pv self l-0)))
      (send
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self)))))
  (label 1510)
  (parent 839)
  (realized)
  (shape)
  (maps
    ((0)
      ((a self) (b b) (l l-0) (l-peer l) (x x) (eta y) (na na) (nb nb)
        (priv-stor priv-stor-0))))
  (origs (l-0 (3 1)) (pt-3 (3 1)) (pt-1 (2 1)) (l (1 1)) (pt-0 (1 1))
    (na (0 2)))
  (ugens (x (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (l l-0 x y rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (x x) (beta l-0) (eta y))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (precedes ((1 1) (0 0)) ((1 1) (3 0)) ((2 2) (0 1)) ((3 2) (0 3)))
  (non-orig (privk "sig" b))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0))
  (gen-st (pv a l))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (0 0)) ((1 1) (3 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization forgot nb)
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor (cat pt (pv a l)))
      (recv
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y)))))))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l-0)))
      (send
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt (pv a l)))
      (stor priv-stor (cat pt-3 "nil")) (send l)))
  (label 1516)
  (parent 839)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l) (l-peer l-0) (x x) (eta y) (na na) (nb nb)
        (priv-stor priv-stor))))
  (origs (l-0 (2 1)) (pt-2 (2 1)) (pt-3 (3 1)) (l (1 1)) (pt (1 1))
    (na (0 2)))
  (ugens (x (0 2))))

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
  (label 1568)
  (unrealized (0 1))
  (origs (nb (0 3)))
  (ugens (y (0 3)))
  (comment "Not closed under rules"))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a self name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn)
    (l l-0 x y rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b self)
    (priv-stor priv-stor-0) (l l) (y y) (alpha l-0) (chi x))
  (defstrand ltx-gen 3 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-0))
  (defstrand init 5 (na na) (nb nb) (a a) (b self) (priv-stor priv-stor)
    (l l-0) (x x) (beta l) (eta y))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l))
  (precedes ((0 3) (2 3)) ((1 1) (2 0)) ((1 2) (0 1)) ((2 2) (0 2))
    ((2 4) (0 4)) ((3 1) (0 0)) ((3 2) (2 1)))
  (non-orig (privk "sig" a))
  (uniq-orig na nb l l-0)
  (uniq-gen x y)
  (absent (x l) (x l-0) (y l) (y l-0) (y x))
  (gen-st (pv a l-0) (pv self l))
  (facts (neq self a) (neq a self) (undisclosed l) (undisclosed l-0))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation nonce-test (displaced 4 0 resp 4) (exp (gen) y-0) (2 3))
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor-0 (cat pt-2 (pv self l)))
      (recv
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a self (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a self
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y))))))
      (recv nb))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv a l-0)))
      (send
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor (cat pt-0 (pv a l-0)))
      (recv
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self))) (send (cat na a self (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a self
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y))))))
      (send nb))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv self l)))
      (send
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self)))))
  (label 1584)
  (parent 1568)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b self) (l l) (l-peer l-0) (y y) (chi x) (na na) (nb nb)
        (priv-stor priv-stor-0))))
  (origs (nb (0 3)) (l (3 1)) (pt-2 (3 1)) (l-0 (1 1)) (pt-0 (1 1))
    (na (2 2)))
  (ugens (y (0 3)) (x (2 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a self name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn) (l l-0 x rndx)
    (w expt) (y rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b self)
    (priv-stor priv-stor-0) (l l) (y y) (alpha l-0) (chi (mul x w)))
  (defstrand ltx-gen 3 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-0))
  (defstrand init 5 (na na) (nb nb) (a a) (b self) (priv-stor priv-stor)
    (l l-0) (x x) (beta l) (eta (mul w y)))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l))
  (precedes ((0 3) (2 3)) ((1 1) (2 0)) ((1 2) (0 1)) ((2 2) (0 2))
    ((2 4) (0 4)) ((3 1) (0 0)) ((3 2) (2 1)))
  (non-orig (privk "sig" a))
  (uniq-orig na nb l l-0)
  (uniq-gen x y)
  (absent (x l) (x l-0) (y l) (y l-0) (y (mul x w)))
  (gen-st (pv a l-0) (pv self l))
  (facts (neq self a) (neq a self) (undisclosed l) (undisclosed l-0))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (4 0))
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor-0 (cat pt-2 (pv self l)))
      (recv
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a self (exp (gen) (mul x w))))
      (send
        (cat (exp (gen) y)
          (enc na nb a self
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x w y))))))
      (recv nb))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv a l-0)))
      (send
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor (cat pt-0 (pv a l-0)))
      (recv
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self))) (send (cat na a self (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul w y))
          (enc na nb a self
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x w y))))))
      (send nb))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv self l)))
      (send
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self)))))
  (label 1611)
  (parent 1568)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b self) (l l) (l-peer l-0) (y y) (chi (mul x w)) (na na)
        (nb nb) (priv-stor priv-stor-0))))
  (origs (nb (0 3)) (l (3 1)) (pt-2 (3 1)) (l-0 (1 1)) (pt-0 (1 1))
    (na (2 2)))
  (ugens (y (0 3)) (x (2 2))))

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
  (facts (neq a b) (undisclosed l-peer))
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
  (label 1632)
  (unrealized (0 1))
  (origs (nb (0 3)))
  (ugens (y (0 3)))
  (comment "Not closed under rules"))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a self name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn)
    (l l-0 x y rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b self)
    (priv-stor priv-stor-0) (l l) (y y) (alpha l-0) (chi x))
  (defstrand ltx-gen 3 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-0))
  (defstrand init 5 (na na) (nb nb) (a a) (b self) (priv-stor priv-stor)
    (l l-0) (x x) (beta l) (eta y))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l))
  (precedes ((0 3) (2 3)) ((1 1) (2 0)) ((1 2) (0 1)) ((2 2) (0 2))
    ((2 4) (0 4)) ((3 1) (0 0)) ((3 2) (2 1)))
  (non-orig (privk "sig" a))
  (uniq-orig na nb l l-0)
  (uniq-gen x y)
  (absent (x l) (x l-0) (y l) (y l-0) (y x))
  (gen-st (pv a l-0) (pv self l))
  (facts (neq self a) (neq a self) (undisclosed l-0))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation nonce-test (displaced 4 0 resp 4) (exp (gen) y-0) (2 3))
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor-0 (cat pt-2 (pv self l)))
      (recv
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a self (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a self
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y))))))
      (recv nb))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv a l-0)))
      (send
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor (cat pt-0 (pv a l-0)))
      (recv
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self))) (send (cat na a self (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a self
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y))))))
      (send nb))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv self l)))
      (send
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self)))))
  (label 1648)
  (parent 1632)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b self) (l l) (l-peer l-0) (y y) (chi x) (na na) (nb nb)
        (priv-stor priv-stor-0))))
  (origs (nb (0 3)) (l (3 1)) (pt-2 (3 1)) (l-0 (1 1)) (pt-0 (1 1))
    (na (2 2)))
  (ugens (y (0 3)) (x (2 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a self name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn) (l l-0 x rndx)
    (w expt) (y rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b self)
    (priv-stor priv-stor-0) (l l) (y y) (alpha l-0) (chi (mul x w)))
  (defstrand ltx-gen 3 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-0))
  (defstrand init 5 (na na) (nb nb) (a a) (b self) (priv-stor priv-stor)
    (l l-0) (x x) (beta l) (eta (mul w y)))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l))
  (precedes ((0 3) (2 3)) ((1 1) (2 0)) ((1 2) (0 1)) ((2 2) (0 2))
    ((2 4) (0 4)) ((3 1) (0 0)) ((3 2) (2 1)))
  (non-orig (privk "sig" a))
  (uniq-orig na nb l l-0)
  (uniq-gen x y)
  (absent (x l) (x l-0) (y l) (y l-0) (y (mul x w)))
  (gen-st (pv a l-0) (pv self l))
  (facts (neq self a) (neq a self) (undisclosed l-0))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (4 0))
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor-0 (cat pt-2 (pv self l)))
      (recv
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a self (exp (gen) (mul x w))))
      (send
        (cat (exp (gen) y)
          (enc na nb a self
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x w y))))))
      (recv nb))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv a l-0)))
      (send
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor (cat pt-0 (pv a l-0)))
      (recv
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self))) (send (cat na a self (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul w y))
          (enc na nb a self
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x w y))))))
      (send nb))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv self l)))
      (send
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self)))))
  (label 1682)
  (parent 1632)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b self) (l l) (l-peer l-0) (y y) (chi (mul x w)) (na na)
        (nb nb) (priv-stor priv-stor-0))))
  (origs (nb (0 3)) (l (3 1)) (pt-2 (3 1)) (l-0 (1 1)) (pt-0 (1 1))
    (na (2 2)))
  (ugens (y (0 3)) (x (2 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn) (y rndx)
    (chi expt) (l l-0 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (y y) (alpha l-0) (chi chi))
  (defstrand ltx-gen 2 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l))
  (precedes ((1 1) (0 0)) ((1 1) (3 0)) ((2 2) (0 1)) ((3 2) (0 4)))
  (non-orig (privk "sig" a))
  (uniq-orig nb l l-0)
  (uniq-gen y)
  (absent (y chi) (y l) (y l-0))
  (gen-st (pv b l))
  (facts (neq b a) (neq a b) (undisclosed l-0))
  (leads-to ((1 1) (0 0)) ((1 1) (3 0)))
  (rule fact-init-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (3 0))
  (strand-map 0 1 2 4)
  (traces
    ((load priv-stor (cat pt (pv b l)))
      (recv
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) chi)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul y chi))))))
      (recv nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv b l))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l-0)))
      (send
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor (cat pt (pv b l)))
      (stor priv-stor (cat pt-3 "nil")) (send l)))
  (label 1762)
  (parent 1632)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l) (l-peer l-0) (y y) (chi chi) (na na) (nb nb)
        (priv-stor priv-stor))))
  (origs (l-0 (2 1)) (pt-2 (2 1)) (pt-3 (3 1)) (l (1 1)) (pt (1 1))
    (nb (0 3)))
  (ugens (y (0 3))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (l l-0 x y rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (y y) (alpha l-0) (chi x))
  (defstrand ltx-gen 2 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l))
  (precedes ((1 1) (0 0)) ((1 1) (3 0)) ((2 2) (0 1)) ((3 2) (0 4)))
  (non-orig (privk "sig" a))
  (uniq-orig nb l l-0)
  (uniq-gen y)
  (absent (y l) (y l-0) (y x))
  (gen-st (pv a l-0) (pv b l))
  (facts (neq b a) (neq a b) (undisclosed l-0))
  (leads-to ((1 1) (0 0)) ((1 1) (3 0)))
  (rule fact-init-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization weakened ((3 1) (0 2)))
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor (cat pt (pv b l)))
      (recv
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y))))))
      (recv nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv b l))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l-0)))
      (send
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor (cat pt (pv b l)))
      (stor priv-stor (cat pt-3 "nil")) (send l)))
  (label 1849)
  (parent 1632)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l) (l-peer l-0) (y y) (chi x) (na na) (nb nb)
        (priv-stor priv-stor))))
  (origs (nb (0 3)) (pt-3 (3 1)) (l-0 (2 1)) (pt-2 (2 1)) (l (1 1))
    (pt (1 1)))
  (ugens (y (0 3))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (l l-0 x rndx) (w expt) (y rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (y y) (alpha l-0) (chi (mul x w)))
  (defstrand ltx-gen 2 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l))
  (precedes ((1 1) (0 0)) ((1 1) (3 0)) ((2 2) (0 1)) ((3 2) (0 4)))
  (non-orig (privk "sig" a))
  (uniq-orig nb l l-0)
  (uniq-gen y)
  (absent (y l) (y l-0) (y (mul x w)))
  (gen-st (pv a l-0) (pv b l))
  (facts (neq b a) (neq a b) (undisclosed l-0))
  (leads-to ((1 1) (0 0)) ((1 1) (3 0)))
  (rule fact-init-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization weakened ((3 1) (0 2)))
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor (cat pt (pv b l)))
      (recv
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) (mul x w))))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x w y))))))
      (recv nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv b l))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l-0)))
      (send
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor (cat pt (pv b l)))
      (stor priv-stor (cat pt-3 "nil")) (send l)))
  (label 1884)
  (parent 1632)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l) (l-peer l-0) (y y) (chi (mul x w)) (na na)
        (nb nb) (priv-stor priv-stor))))
  (origs (nb (0 3)) (pt-3 (3 1)) (l-0 (2 1)) (pt-2 (2 1)) (l (1 1))
    (pt (1 1)))
  (ugens (y (0 3))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (l l-0 x y rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (y y) (alpha l-0) (chi x))
  (defstrand ltx-gen 2 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l))
  (precedes ((1 1) (0 0)) ((1 1) (3 0)) ((2 2) (0 1)) ((3 2) (0 4)))
  (non-orig (privk "sig" a))
  (uniq-orig nb l l-0)
  (uniq-gen y)
  (absent (y l) (y l-0) (y x))
  (gen-st (pv b l))
  (facts (neq b a) (neq a b) (undisclosed l-0))
  (leads-to ((1 1) (0 0)) ((1 1) (3 0)))
  (rule fact-init-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization weakened ((3 1) (0 2)))
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor (cat pt (pv b l)))
      (recv
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y))))))
      (recv nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv b l))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l-0)))
      (send
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor (cat pt (pv b l)))
      (stor priv-stor (cat pt-3 "nil")) (send l)))
  (label 1900)
  (parent 1632)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l) (l-peer l-0) (y y) (chi x) (na na) (nb nb)
        (priv-stor priv-stor))))
  (origs (nb (0 3)) (l-0 (2 1)) (pt-2 (2 1)) (pt-3 (3 1)) (l (1 1))
    (pt (1 1)))
  (ugens (y (0 3))))

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
  (facts (neq a b) (undisclosed l))
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
  (label 1903)
  (unrealized (0 1))
  (origs (nb (0 3)))
  (ugens (y (0 3)))
  (comment "Not closed under rules"))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a self name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn)
    (l l-0 x y rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b self)
    (priv-stor priv-stor-0) (l l) (y y) (alpha l-0) (chi x))
  (defstrand ltx-gen 3 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-0))
  (defstrand init 5 (na na) (nb nb) (a a) (b self) (priv-stor priv-stor)
    (l l-0) (x x) (beta l) (eta y))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l))
  (precedes ((0 3) (2 3)) ((1 1) (2 0)) ((1 2) (0 1)) ((2 2) (0 2))
    ((2 4) (0 4)) ((3 1) (0 0)) ((3 2) (2 1)))
  (non-orig (privk "sig" a))
  (uniq-orig na nb l l-0)
  (uniq-gen x y)
  (absent (x l) (x l-0) (y l) (y l-0) (y x))
  (gen-st (pv a l-0) (pv self l))
  (facts (neq self a) (neq a self) (undisclosed l))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation nonce-test (displaced 4 0 resp 4) (exp (gen) y-0) (2 3))
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor-0 (cat pt-2 (pv self l)))
      (recv
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a self (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a self
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y))))))
      (recv nb))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv a l-0)))
      (send
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor (cat pt-0 (pv a l-0)))
      (recv
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self))) (send (cat na a self (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a self
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y))))))
      (send nb))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv self l)))
      (send
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self)))))
  (label 1919)
  (parent 1903)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b self) (l l) (l-peer l-0) (y y) (chi x) (na na) (nb nb)
        (priv-stor priv-stor-0))))
  (origs (nb (0 3)) (l (3 1)) (pt-2 (3 1)) (l-0 (1 1)) (pt-0 (1 1))
    (na (2 2)))
  (ugens (y (0 3)) (x (2 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a self name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn) (l l-0 x rndx)
    (w expt) (y rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b self)
    (priv-stor priv-stor-0) (l l) (y y) (alpha l-0) (chi (mul x w)))
  (defstrand ltx-gen 3 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-0))
  (defstrand init 5 (na na) (nb nb) (a a) (b self) (priv-stor priv-stor)
    (l l-0) (x x) (beta l) (eta (mul w y)))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l))
  (precedes ((0 3) (2 3)) ((1 1) (2 0)) ((1 2) (0 1)) ((2 2) (0 2))
    ((2 4) (0 4)) ((3 1) (0 0)) ((3 2) (2 1)))
  (non-orig (privk "sig" a))
  (uniq-orig na nb l l-0)
  (uniq-gen x y)
  (absent (x l) (x l-0) (y l) (y l-0) (y (mul x w)))
  (gen-st (pv a l-0) (pv self l))
  (facts (neq self a) (neq a self) (undisclosed l))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (4 0))
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor-0 (cat pt-2 (pv self l)))
      (recv
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a self (exp (gen) (mul x w))))
      (send
        (cat (exp (gen) y)
          (enc na nb a self
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x w y))))))
      (recv nb))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv a l-0)))
      (send
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor (cat pt-0 (pv a l-0)))
      (recv
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self))) (send (cat na a self (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul w y))
          (enc na nb a self
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x w y))))))
      (send nb))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv self l)))
      (send
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self)))))
  (label 1952)
  (parent 1903)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b self) (l l) (l-peer l-0) (y y) (chi (mul x w)) (na na)
        (nb nb) (priv-stor priv-stor-0))))
  (origs (nb (0 3)) (l (3 1)) (pt-2 (3 1)) (l-0 (1 1)) (pt-0 (1 1))
    (na (2 2)))
  (ugens (y (0 3)) (x (2 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a self name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn) (y rndx)
    (chi expt) (l l-0 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b self)
    (priv-stor priv-stor-0) (l l-0) (y y) (alpha l) (chi chi))
  (defstrand ltx-gen 3 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l-0))
  (precedes ((1 1) (2 0)) ((1 2) (0 1)) ((2 2) (0 4)) ((3 1) (0 0))
    ((3 2) (0 4)))
  (non-orig (privk "sig" a))
  (uniq-orig nb l l-0)
  (uniq-gen y)
  (absent (y chi) (y l) (y l-0))
  (gen-st (pv a l) (pv self l-0))
  (facts (neq self a) (neq a self) (undisclosed l-0))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-init-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (2 0))
  (strand-map 0 1 3 4)
  (traces
    ((load priv-stor-0 (cat pt-3 (pv self l-0)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a self (exp (gen) chi)))
      (send
        (cat (exp (gen) y)
          (enc na nb a self
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul y chi))))))
      (recv nb))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv a l)))
      (send
        (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor (cat pt-0 (pv a l)))
      (stor priv-stor (cat pt-1 "nil")) (send l))
    ((load priv-stor-0 (cat pt-2 ignore-0))
      (stor priv-stor-0 (cat pt-3 (pv self l-0)))
      (send
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self)))))
  (label 2013)
  (parent 1903)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b self) (l l-0) (l-peer l) (y y) (chi chi) (na na) (nb nb)
        (priv-stor priv-stor-0))))
  (origs (l-0 (3 1)) (pt-3 (3 1)) (pt-1 (2 1)) (l (1 1)) (pt-0 (1 1))
    (nb (0 3)))
  (ugens (y (0 3))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a self name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (l l-0 x y rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b self)
    (priv-stor priv-stor-0) (l l) (y y) (alpha l-0) (chi x))
  (defstrand ltx-gen 3 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l))
  (precedes ((1 1) (2 0)) ((1 2) (0 1)) ((2 2) (0 4)) ((3 1) (0 0))
    ((3 2) (0 4)))
  (non-orig (privk "sig" a))
  (uniq-orig nb l l-0)
  (uniq-gen y)
  (absent (y l) (y l-0) (y x))
  (gen-st (pv a l-0) (pv self l))
  (facts (neq self a) (neq a self) (undisclosed l))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-init-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization weakened ((3 2) (0 2)))
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor-0 (cat pt-3 (pv self l)))
      (recv
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a self (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a self
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y))))))
      (recv nb))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv a l-0)))
      (send
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor (cat pt-0 (pv a l-0)))
      (stor priv-stor (cat pt-1 "nil")) (send l-0))
    ((load priv-stor-0 (cat pt-2 ignore-0))
      (stor priv-stor-0 (cat pt-3 (pv self l)))
      (send
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self)))))
  (label 2145)
  (parent 1903)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b self) (l l) (l-peer l-0) (y y) (chi x) (na na) (nb nb)
        (priv-stor priv-stor-0))))
  (origs (nb (0 3)) (l (3 1)) (pt-3 (3 1)) (pt-1 (2 1)) (l-0 (1 1))
    (pt-0 (1 1)))
  (ugens (y (0 3))))

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
  (facts (neq a b))
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
  (label 2148)
  (unrealized (0 1))
  (origs (nb (0 3)))
  (ugens (y (0 3)))
  (comment "Not closed under rules"))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a self name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn)
    (l l-0 x y rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b self)
    (priv-stor priv-stor-0) (l l) (y y) (alpha l-0) (chi x))
  (defstrand ltx-gen 3 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-0))
  (defstrand init 5 (na na) (nb nb) (a a) (b self) (priv-stor priv-stor)
    (l l-0) (x x) (beta l) (eta y))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l))
  (precedes ((0 3) (2 3)) ((1 1) (2 0)) ((1 2) (0 1)) ((2 2) (0 2))
    ((2 4) (0 4)) ((3 1) (0 0)) ((3 2) (2 1)))
  (non-orig (privk "sig" a))
  (uniq-orig na nb l l-0)
  (uniq-gen x y)
  (absent (x l) (x l-0) (y l) (y l-0) (y x))
  (gen-st (pv a l-0) (pv self l))
  (facts (neq self a) (neq a self))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation nonce-test (displaced 4 0 resp 4) (exp (gen) y-0) (2 3))
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor-0 (cat pt-2 (pv self l)))
      (recv
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a self (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a self
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y))))))
      (recv nb))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv a l-0)))
      (send
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor (cat pt-0 (pv a l-0)))
      (recv
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self))) (send (cat na a self (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a self
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y))))))
      (send nb))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv self l)))
      (send
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self)))))
  (label 2164)
  (parent 2148)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b self) (l l) (l-peer l-0) (y y) (chi x) (na na) (nb nb)
        (priv-stor priv-stor-0))))
  (origs (nb (0 3)) (l (3 1)) (pt-2 (3 1)) (l-0 (1 1)) (pt-0 (1 1))
    (na (2 2)))
  (ugens (y (0 3)) (x (2 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a self name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn) (l l-0 x rndx)
    (w expt) (y rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b self)
    (priv-stor priv-stor-0) (l l) (y y) (alpha l-0) (chi (mul x w)))
  (defstrand ltx-gen 3 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-0))
  (defstrand init 5 (na na) (nb nb) (a a) (b self) (priv-stor priv-stor)
    (l l-0) (x x) (beta l) (eta (mul w y)))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l))
  (precedes ((0 3) (2 3)) ((1 1) (2 0)) ((1 2) (0 1)) ((2 2) (0 2))
    ((2 4) (0 4)) ((3 1) (0 0)) ((3 2) (2 1)))
  (non-orig (privk "sig" a))
  (uniq-orig na nb l l-0)
  (uniq-gen x y)
  (absent (x l) (x l-0) (y l) (y l-0) (y (mul x w)))
  (gen-st (pv a l-0) (pv self l))
  (facts (neq self a) (neq a self))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (4 0))
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor-0 (cat pt-2 (pv self l)))
      (recv
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a self (exp (gen) (mul x w))))
      (send
        (cat (exp (gen) y)
          (enc na nb a self
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x w y))))))
      (recv nb))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv a l-0)))
      (send
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor (cat pt-0 (pv a l-0)))
      (recv
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self))) (send (cat na a self (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul w y))
          (enc na nb a self
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x w y))))))
      (send nb))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv self l)))
      (send
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self)))))
  (label 2204)
  (parent 2148)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b self) (l l) (l-peer l-0) (y y) (chi (mul x w)) (na na)
        (nb nb) (priv-stor priv-stor-0))))
  (origs (nb (0 3)) (l (3 1)) (pt-2 (3 1)) (l-0 (1 1)) (pt-0 (1 1))
    (na (2 2)))
  (ugens (y (0 3)) (x (2 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a self name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn) (y rndx)
    (chi expt) (l l-0 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b self)
    (priv-stor priv-stor-0) (l l-0) (y y) (alpha l) (chi chi))
  (defstrand ltx-gen 3 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l-0))
  (precedes ((1 1) (2 0)) ((1 2) (0 1)) ((2 2) (0 4)) ((3 1) (0 0))
    ((3 2) (0 4)))
  (non-orig (privk "sig" a))
  (uniq-orig nb l l-0)
  (uniq-gen y)
  (absent (y chi) (y l) (y l-0))
  (gen-st (pv a l) (pv self l-0))
  (facts (neq self a) (neq a self))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-init-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (2 0))
  (strand-map 0 1 3 4)
  (traces
    ((load priv-stor-0 (cat pt-3 (pv self l-0)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a self (exp (gen) chi)))
      (send
        (cat (exp (gen) y)
          (enc na nb a self
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul y chi))))))
      (recv nb))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv a l)))
      (send
        (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor (cat pt-0 (pv a l)))
      (stor priv-stor (cat pt-1 "nil")) (send l))
    ((load priv-stor-0 (cat pt-2 ignore-0))
      (stor priv-stor-0 (cat pt-3 (pv self l-0)))
      (send
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self)))))
  (label 2344)
  (parent 2148)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b self) (l l-0) (l-peer l) (y y) (chi chi) (na na) (nb nb)
        (priv-stor priv-stor-0))))
  (origs (l-0 (3 1)) (pt-3 (3 1)) (pt-1 (2 1)) (l (1 1)) (pt-0 (1 1))
    (nb (0 3)))
  (ugens (y (0 3))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn) (y rndx)
    (chi expt) (l l-0 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (y y) (alpha l-0) (chi chi))
  (defstrand ltx-gen 2 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l))
  (precedes ((1 1) (0 0)) ((1 1) (3 0)) ((2 2) (0 1)) ((3 2) (0 4)))
  (non-orig (privk "sig" a))
  (uniq-orig nb l l-0)
  (uniq-gen y)
  (absent (y chi) (y l) (y l-0))
  (gen-st (pv b l))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (0 0)) ((1 1) (3 0)))
  (rule fact-init-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (3 0))
  (strand-map 0 1 2 4)
  (traces
    ((load priv-stor (cat pt (pv b l)))
      (recv
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) chi)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul y chi))))))
      (recv nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv b l))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l-0)))
      (send
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor (cat pt (pv b l)))
      (stor priv-stor (cat pt-3 "nil")) (send l)))
  (label 2347)
  (parent 2148)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l) (l-peer l-0) (y y) (chi chi) (na na) (nb nb)
        (priv-stor priv-stor))))
  (origs (l-0 (2 1)) (pt-2 (2 1)) (pt-3 (3 1)) (l (1 1)) (pt (1 1))
    (nb (0 3)))
  (ugens (y (0 3))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (l l-0 x y rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (y y) (alpha l-0) (chi x))
  (defstrand ltx-gen 2 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l))
  (precedes ((1 1) (0 0)) ((1 1) (3 0)) ((2 2) (0 1)) ((3 2) (0 4)))
  (non-orig (privk "sig" a))
  (uniq-orig nb l l-0)
  (uniq-gen y)
  (absent (y l) (y l-0) (y x))
  (gen-st (pv a l-0) (pv b l))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (0 0)) ((1 1) (3 0)))
  (rule fact-init-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization weakened ((3 1) (0 2)))
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor (cat pt (pv b l)))
      (recv
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y))))))
      (recv nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv b l))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l-0)))
      (send
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor (cat pt (pv b l)))
      (stor priv-stor (cat pt-3 "nil")) (send l)))
  (label 2556)
  (parent 2148)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l) (l-peer l-0) (y y) (chi x) (na na) (nb nb)
        (priv-stor priv-stor))))
  (origs (nb (0 3)) (pt-3 (3 1)) (l-0 (2 1)) (pt-2 (2 1)) (l (1 1))
    (pt (1 1)))
  (ugens (y (0 3))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn) (y rndx)
    (chi expt) (l l-0 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-0) (y y) (alpha l) (chi chi))
  (defstrand ltx-gen 2 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l-0))
  (precedes ((1 1) (0 0)) ((1 1) (3 0)) ((2 2) (0 1)) ((3 2) (0 4)))
  (non-orig (privk "sig" a))
  (uniq-orig nb l l-0)
  (uniq-gen y)
  (absent (y chi) (y l) (y l-0))
  (gen-st (pv a l) (pv b l-0))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (0 0)) ((1 1) (3 0)))
  (rule fact-init-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (3 0))
  (strand-map 0 1 2 4)
  (traces
    ((load priv-stor (cat pt (pv b l-0)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) chi)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul y chi))))))
      (recv nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv b l-0))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l)))
      (send
        (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor (cat pt (pv b l-0)))
      (stor priv-stor (cat pt-3 "nil")) (send l-0)))
  (label 2753)
  (parent 2148)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-0) (l-peer l) (y y) (chi chi) (na na) (nb nb)
        (priv-stor priv-stor))))
  (origs (pt-3 (3 1)) (l (2 1)) (pt-2 (2 1)) (l-0 (1 1)) (pt (1 1))
    (nb (0 3)))
  (ugens (y (0 3))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (l l-0 x y rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (y y) (alpha l-0) (chi x))
  (defstrand ltx-gen 2 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l))
  (precedes ((1 1) (0 0)) ((1 1) (3 0)) ((2 2) (0 1)) ((3 2) (0 4)))
  (non-orig (privk "sig" a))
  (uniq-orig nb l l-0)
  (uniq-gen y)
  (absent (y l) (y l-0) (y x))
  (gen-st (pv b l))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (0 0)) ((1 1) (3 0)))
  (rule fact-init-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization weakened ((3 1) (0 2)))
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor (cat pt (pv b l)))
      (recv
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y))))))
      (recv nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv b l))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l-0)))
      (send
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor (cat pt (pv b l)))
      (stor priv-stor (cat pt-3 "nil")) (send l)))
  (label 2864)
  (parent 2148)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l) (l-peer l-0) (y y) (chi x) (na na) (nb nb)
        (priv-stor priv-stor))))
  (origs (nb (0 3)) (l-0 (2 1)) (pt-2 (2 1)) (pt-3 (3 1)) (l (1 1))
    (pt (1 1)))
  (ugens (y (0 3))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a self name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (l l-0 x y rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b self)
    (priv-stor priv-stor-0) (l l) (y y) (alpha l-0) (chi x))
  (defstrand ltx-gen 3 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l))
  (precedes ((1 1) (2 0)) ((1 2) (0 1)) ((2 2) (0 4)) ((3 1) (0 0))
    ((3 2) (0 4)))
  (non-orig (privk "sig" a))
  (uniq-orig nb l l-0)
  (uniq-gen y)
  (absent (y l) (y l-0) (y x))
  (gen-st (pv a l-0) (pv self l))
  (facts (neq self a) (neq a self))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-init-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization weakened ((3 2) (0 2)))
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor-0 (cat pt-3 (pv self l)))
      (recv
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a self (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a self
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y))))))
      (recv nb))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv a l-0)))
      (send
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor (cat pt-0 (pv a l-0)))
      (stor priv-stor (cat pt-1 "nil")) (send l-0))
    ((load priv-stor-0 (cat pt-2 ignore-0))
      (stor priv-stor-0 (cat pt-3 (pv self l)))
      (send
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self)))))
  (label 2873)
  (parent 2148)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b self) (l l) (l-peer l-0) (y y) (chi x) (na na) (nb nb)
        (priv-stor priv-stor-0))))
  (origs (nb (0 3)) (l (3 1)) (pt-3 (3 1)) (pt-1 (2 1)) (l-0 (1 1))
    (pt-0 (1 1)))
  (ugens (y (0 3))))

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
  (defstrand init 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l ltxa) (x x) (beta ltxb) (eta y))
  (deflistener (hash (exp (gen) (mul ltxa ltxb)) (exp (gen) (mul x y))))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor-0)
    (l ltxa))
  (defstrand ltx-disclose 3 (self self-0) (priv-stor priv-stor-1)
    (l ltxb))
  (precedes ((0 4) (2 0)) ((0 4) (3 0)))
  (uniq-orig na)
  (uniq-gen x)
  (absent (x ltxa) (x ltxb))
  (traces
    ((load priv-stor (cat pt (pv a ltxa)))
      (recv
        (sig (body b (exp (gen) ltxb) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa ltxb)) (exp (gen) (mul x y))))))
      (send nb))
    ((recv (hash (exp (gen) (mul ltxa ltxb)) (exp (gen) (mul x y))))
      (send (hash (exp (gen) (mul ltxa ltxb)) (exp (gen) (mul x y)))))
    ((load priv-stor-0 (cat pt-0 (pv self ltxa)))
      (stor priv-stor-0 (cat pt-1 "nil")) (send ltxa))
    ((load priv-stor-1 (cat pt-2 (pv self-0 ltxb)))
      (stor priv-stor-1 (cat pt-3 "nil")) (send ltxb)))
  (label 2884)
  (unrealized (1 0))
  (preskeleton)
  (origs (pt-3 (3 1)) (pt-1 (2 1)) (na (0 2)))
  (ugens (x (0 2)))
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
  (defstrand resp 6 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l ltxa) (y y) (alpha ltxb) (chi chi))
  (deflistener
    (hash (exp (gen) (mul ltxa ltxb)) (exp (gen) (mul y chi))))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor-0)
    (l ltxa))
  (defstrand ltx-disclose 3 (self self-0) (priv-stor priv-stor-1)
    (l ltxb))
  (precedes ((0 5) (2 0)) ((0 5) (3 0)))
  (uniq-orig nb)
  (uniq-gen y)
  (absent (y ltxa) (y ltxb) (y chi))
  (traces
    ((load priv-stor (cat pt (pv b ltxa)))
      (recv
        (sig (body a (exp (gen) ltxb) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) chi)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa ltxb))
              (exp (gen) (mul y chi)))))) (recv nb) (send "done"))
    ((recv (hash (exp (gen) (mul ltxa ltxb)) (exp (gen) (mul y chi))))
      (send (hash (exp (gen) (mul ltxa ltxb)) (exp (gen) (mul y chi)))))
    ((load priv-stor-0 (cat pt-0 (pv self ltxa)))
      (stor priv-stor-0 (cat pt-1 "nil")) (send ltxa))
    ((load priv-stor-1 (cat pt-2 (pv self-0 ltxb)))
      (stor priv-stor-1 (cat pt-3 "nil")) (send ltxb)))
  (label 4537)
  (unrealized (1 0))
  (preskeleton)
  (origs (pt-3 (3 1)) (pt-1 (2 1)) (nb (0 3)))
  (ugens (y (0 3)))
  (comment "Not a skeleton"))

(comment "Nothing left to do")
