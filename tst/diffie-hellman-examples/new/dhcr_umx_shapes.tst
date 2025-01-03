(comment "CPSA 4.4.4")
(comment "Extracted shapes")

(herald "DHCR: unified model (UM) with criss-cross key derivation"
  (bound 30) (limit 8000) (algebra diffie-hellman))

(comment "CPSA 4.4.4")

(comment "All input read from dhcr_umx.scm")

(comment "Step count limited to 8000")

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
  (non-orig (privk "sig" a) (privk "sig" b))
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
            (hash (exp (gen) (mul l eta))
              (exp (gen) (mul l-peer x))))))))
  (label 0)
  (unrealized (0 1))
  (origs (na (0 2)))
  (ugens (x (0 2)))
  (comment "Not closed under rules"))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn)
    (y x l l-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor-0)
    (l l-0) (x x) (beta l) (eta y))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l))
  (defstrand resp 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (y y) (alpha l-0) (chi x))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l-0))
  (precedes ((0 2) (2 2)) ((1 1) (2 0)) ((1 2) (0 1)) ((2 3) (0 3))
    ((3 1) (0 0)) ((3 2) (2 1)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig na nb l l-0)
  (uniq-gen y x)
  (absent (y x) (y l) (y l-0) (x l) (x l-0))
  (gen-st (pv a l-0) (pv b l))
  (facts (neq b a) (neq a b) (undisclosed l-0) (undisclosed l))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation encryption-test (displaced 1 4 ltx-gen 3)
    (sig (body a (exp (gen) l-1) (pubk "sig" a)) (privk "sig" a)) (3 1))
  (strand-map 0 3 1 2)
  (traces
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
    ((load priv-stor (cat pt-0 (pv b l)))
      (recv
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l-0)) (exp (gen) (mul x l)))))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l-0)))
      (send
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))))
  (label 9)
  (parent 0)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-0) (l-peer l) (x x) (eta y) (na na) (nb nb)
        (priv-stor priv-stor-0))))
  (origs (l-0 (3 1)) (pt-2 (3 1)) (l (1 1)) (pt-0 (1 1)) (nb (2 3))
    (na (0 2)))
  (ugens (y (2 3)) (x (0 2))))

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
  (vars (na nb data) (a b name) (pt pval) (priv-stor locn)
    (l l-peer x rndx) (eta expt))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (x x) (beta l-peer) (eta eta))
  (non-orig (privk "sig" a) (privk "sig" b))
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
            (hash (exp (gen) (mul l eta))
              (exp (gen) (mul l-peer x))))))))
  (label 102)
  (unrealized (0 1))
  (origs (na (0 2)))
  (ugens (x (0 2)))
  (comment "Not closed under rules"))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn)
    (y x l l-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor-0)
    (l l-0) (x x) (beta l) (eta y))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l))
  (defstrand resp 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (y y) (alpha l-0) (chi x))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l-0))
  (precedes ((0 2) (2 2)) ((1 1) (2 0)) ((1 2) (0 1)) ((2 3) (0 3))
    ((3 1) (0 0)) ((3 2) (2 1)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig na nb l l-0)
  (uniq-gen y x)
  (absent (y x) (y l) (y l-0) (x l) (x l-0))
  (gen-st (pv a l-0) (pv b l))
  (facts (neq b a) (neq a b) (undisclosed l))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation encryption-test (displaced 1 4 ltx-gen 3)
    (sig (body a (exp (gen) l-1) (pubk "sig" a)) (privk "sig" a)) (3 1))
  (strand-map 0 3 1 2)
  (traces
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
    ((load priv-stor (cat pt-0 (pv b l)))
      (recv
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l-0)) (exp (gen) (mul x l)))))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l-0)))
      (send
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))))
  (label 111)
  (parent 102)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-0) (l-peer l) (x x) (eta y) (na na) (nb nb)
        (priv-stor priv-stor-0))))
  (origs (l-0 (3 1)) (pt-2 (3 1)) (l (1 1)) (pt-0 (1 1)) (nb (2 3))
    (na (0 2)))
  (ugens (y (2 3)) (x (0 2))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 ignore-1 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pt-6 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (y x l l-0 l-1 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-1) (x x) (beta l) (eta (mul y l-0 (rec l-1))))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-1))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l))
  (defstrand resp 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor-0)
    (l l) (y y) (alpha l-0) (chi x))
  (defstrand ltx-gen 3 (ignore ignore-1) (self a)
    (priv-stor priv-stor-1) (l l-0))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor-1) (l l-0))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l-1))
  (precedes ((0 2) (3 2)) ((1 1) (0 0)) ((1 1) (6 0)) ((2 1) (3 0))
    ((2 2) (0 1)) ((3 3) (0 3)) ((4 1) (5 0)) ((4 2) (3 1))
    ((5 2) (0 3)) ((6 2) (0 3)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig na nb l l-0 l-1)
  (uniq-gen y x)
  (absent (y x) (y l) (y l-0) (x l) (x l-1))
  (gen-st (pv a l-0) (pv a l-1) (pv b l))
  (facts (neq b a) (neq a b) (undisclosed l))
  (leads-to ((1 1) (0 0)) ((1 1) (6 0)) ((2 1) (3 0)) ((4 1) (5 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (6 0))
  (strand-map 0 1 2 3 4 5 7)
  (traces
    ((load priv-stor (cat pt (pv a l-1)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul y l-0 (rec l-1)))
          (enc na nb a b
            (hash (exp (gen) (mul y l-0)) (exp (gen) (mul x l)))))))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l-1))))
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
            (hash (exp (gen) (mul y l-0)) (exp (gen) (mul x l)))))))
    ((load priv-stor-1 (cat pt-3 ignore-1))
      (stor priv-stor-1 (cat pt-4 (pv a l-0)))
      (send
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor-1 (cat pt-4 (pv a l-0)))
      (stor priv-stor-1 (cat pt-5 "nil")) (send l-0))
    ((load priv-stor (cat pt (pv a l-1)))
      (stor priv-stor (cat pt-6 "nil")) (send l-1)))
  (label 211)
  (parent 102)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-1) (l-peer l) (x x) (eta (mul y l-0 (rec l-1)))
        (na na) (nb nb) (priv-stor priv-stor))))
  (origs (pt-6 (6 1)) (pt-5 (5 1)) (l-0 (4 1)) (pt-4 (4 1)) (l (2 1))
    (pt-2 (2 1)) (nb (3 3)) (l-1 (1 1)) (pt (1 1)) (na (0 2)))
  (ugens (y (3 3)) (x (0 2))))

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
  (vars (na nb data) (a b name) (pt pval) (priv-stor locn)
    (l l-peer x rndx) (eta expt))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (x x) (beta l-peer) (eta eta))
  (non-orig (privk "sig" a) (privk "sig" b))
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
            (hash (exp (gen) (mul l eta))
              (exp (gen) (mul l-peer x))))))))
  (label 212)
  (unrealized (0 1))
  (origs (na (0 2)))
  (ugens (x (0 2)))
  (comment "Not closed under rules"))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn)
    (y x l l-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor-0)
    (l l-0) (x x) (beta l) (eta y))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l))
  (defstrand resp 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (y y) (alpha l-0) (chi x))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l-0))
  (precedes ((0 2) (2 2)) ((1 1) (2 0)) ((1 2) (0 1)) ((2 3) (0 3))
    ((3 1) (0 0)) ((3 2) (2 1)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig na nb l l-0)
  (uniq-gen y x)
  (absent (y x) (y l) (y l-0) (x l) (x l-0))
  (gen-st (pv a l-0) (pv b l))
  (facts (neq b a) (neq a b) (ltx-gen-once a) (undisclosed l))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation encryption-test (displaced 1 4 ltx-gen 3)
    (sig (body a (exp (gen) l-1) (pubk "sig" a)) (privk "sig" a)) (3 1))
  (strand-map 0 3 1 2)
  (traces
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
    ((load priv-stor (cat pt-0 (pv b l)))
      (recv
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l-0)) (exp (gen) (mul x l)))))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l-0)))
      (send
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))))
  (label 221)
  (parent 212)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-0) (l-peer l) (x x) (eta y) (na na) (nb nb)
        (priv-stor priv-stor-0))))
  (origs (l-0 (3 1)) (pt-2 (3 1)) (l (1 1)) (pt-0 (1 1)) (nb (2 3))
    (na (0 2)))
  (ugens (y (2 3)) (x (0 2))))

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
  (vars (na nb data) (a b name) (pt pval) (priv-stor locn) (l rndx)
    (l-peer expt) (x rndx) (eta expt))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (x x) (beta l-peer) (eta eta))
  (non-orig (privk "sig" a) (privk "sig" b))
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
            (hash (exp (gen) (mul l eta))
              (exp (gen) (mul l-peer x))))))))
  (label 300)
  (unrealized (0 1))
  (origs (na (0 2)))
  (ugens (x (0 2)))
  (comment "Not closed under rules"))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn)
    (y x l l-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor-0)
    (l l-0) (x x) (beta l) (eta y))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l))
  (defstrand resp 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (y y) (alpha l-0) (chi x))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l-0))
  (precedes ((0 2) (2 2)) ((1 1) (2 0)) ((1 2) (0 1)) ((2 3) (0 3))
    ((3 1) (0 0)) ((3 2) (2 1)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig na nb l l-0)
  (uniq-gen y x)
  (absent (y x) (y l) (y l-0) (x l) (x l-0))
  (gen-st (pv a l-0) (pv b l))
  (facts (neq b a) (neq a b) (undisclosed l-0))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation encryption-test (displaced 1 4 ltx-gen 3)
    (sig (body a (exp (gen) l-1) (pubk "sig" a)) (privk "sig" a)) (3 1))
  (strand-map 0 3 1 2)
  (traces
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
    ((load priv-stor (cat pt-0 (pv b l)))
      (recv
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l-0)) (exp (gen) (mul x l)))))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l-0)))
      (send
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))))
  (label 309)
  (parent 300)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-0) (l-peer l) (x x) (eta y) (na na) (nb nb)
        (priv-stor priv-stor-0))))
  (origs (l-0 (3 1)) (pt-2 (3 1)) (l (1 1)) (pt-0 (1 1)) (nb (2 3))
    (na (0 2)))
  (ugens (y (2 3)) (x (0 2))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (b self name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (x l l-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a self) (b b)
    (priv-stor priv-stor-0) (l l) (x x) (beta l-0) (eta (one)))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l-0))
  (precedes ((1 1) (3 0)) ((1 2) (0 1)) ((2 1) (0 0)) ((2 2) (0 3))
    ((3 2) (0 3)))
  (non-orig (privk "sig" b) (privk "sig" self))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0))
  (gen-st (pv b l-0) (pv self l))
  (facts (neq b self) (neq self b) (undisclosed l))
  (leads-to ((1 1) (3 0)) ((2 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (3 0))
  (strand-map 0 1 2 4)
  (traces
    ((load priv-stor-0 (cat pt-2 (pv self l)))
      (recv
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na self b (exp (gen) x)))
      (recv
        (cat (gen)
          (enc na nb self b
            (hash (exp (gen) l) (exp (gen) (mul x l-0)))))))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv b l-0)))
      (send
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv self l)))
      (send
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self))))
    ((load priv-stor (cat pt-0 (pv b l-0)))
      (stor priv-stor (cat pt-3 "nil")) (send l-0)))
  (label 515)
  (parent 300)
  (realized)
  (shape)
  (maps
    ((0)
      ((a self) (b b) (l l) (l-peer l-0) (x x) (eta (one)) (na na)
        (nb nb) (priv-stor priv-stor-0))))
  (origs (pt-3 (3 1)) (l (2 1)) (pt-2 (2 1)) (l-0 (1 1)) (pt-0 (1 1))
    (na (0 2)))
  (ugens (x (0 2))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (b self name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn) (x rndx)
    (w expt) (l l-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a self) (b b)
    (priv-stor priv-stor-0) (l l) (x x) (beta l-0) (eta w))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l-0))
  (precedes ((1 1) (3 0)) ((1 2) (0 1)) ((2 1) (0 0)) ((2 2) (0 3))
    ((3 2) (0 3)))
  (non-orig (privk "sig" b) (privk "sig" self))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0))
  (gen-st (pv b l-0) (pv self l))
  (facts (neq b self) (neq self b) (undisclosed l))
  (leads-to ((1 1) (3 0)) ((2 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (3 0))
  (strand-map 0 1 2 4)
  (traces
    ((load priv-stor-0 (cat pt-2 (pv self l)))
      (recv
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na self b (exp (gen) x)))
      (recv
        (cat (exp (gen) w)
          (enc na nb self b
            (hash (exp (gen) (mul w l)) (exp (gen) (mul x l-0)))))))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv b l-0)))
      (send
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv self l)))
      (send
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self))))
    ((load priv-stor (cat pt-0 (pv b l-0)))
      (stor priv-stor (cat pt-3 "nil")) (send l-0)))
  (label 1167)
  (parent 300)
  (realized)
  (shape)
  (maps
    ((0)
      ((a self) (b b) (l l) (l-peer l-0) (x x) (eta w) (na na) (nb nb)
        (priv-stor priv-stor-0))))
  (origs (pt-3 (3 1)) (l (2 1)) (pt-2 (2 1)) (l-0 (1 1)) (pt-0 (1 1))
    (na (0 2)))
  (ugens (x (0 2))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (y x l l-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor-0)
    (l l) (x x) (beta l-0) (eta y))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l-0))
  (precedes ((1 1) (3 0)) ((1 2) (0 1)) ((2 1) (0 0)) ((2 2) (0 3))
    ((3 2) (0 3)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0))
  (gen-st (pv a l) (pv b l-0))
  (facts (neq b a) (neq a b) (undisclosed l))
  (leads-to ((1 1) (3 0)) ((2 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization forgot nb)
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor-0 (cat pt-2 (pv a l)))
      (recv
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l-0)))))))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv b l-0)))
      (send
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l)))
      (send
        (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor (cat pt-0 (pv b l-0)))
      (stor priv-stor (cat pt-3 "nil")) (send l-0)))
  (label 2564)
  (parent 300)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l) (l-peer l-0) (x x) (eta y) (na na) (nb nb)
        (priv-stor priv-stor-0))))
  (origs (pt-3 (3 1)) (l (2 1)) (pt-2 (2 1)) (l-0 (1 1)) (pt-0 (1 1))
    (na (0 2)))
  (ugens (x (0 2))))

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
  (vars (na nb data) (a b name) (pt pval) (priv-stor locn) (l rndx)
    (l-peer expt) (x rndx) (eta expt))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (x x) (beta l-peer) (eta eta))
  (non-orig (privk "sig" a) (privk "sig" b))
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
            (hash (exp (gen) (mul l eta))
              (exp (gen) (mul l-peer x))))))))
  (label 2565)
  (unrealized (0 1))
  (origs (na (0 2)))
  (ugens (x (0 2)))
  (comment "Not closed under rules"))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn)
    (y x l l-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor-0)
    (l l-0) (x x) (beta l) (eta y))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l))
  (defstrand resp 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (y y) (alpha l-0) (chi x))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l-0))
  (precedes ((0 2) (2 2)) ((1 1) (2 0)) ((1 2) (0 1)) ((2 3) (0 3))
    ((3 1) (0 0)) ((3 2) (2 1)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig na nb l l-0)
  (uniq-gen y x)
  (absent (y x) (y l) (y l-0) (x l) (x l-0))
  (gen-st (pv a l-0) (pv b l))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation encryption-test (displaced 1 4 ltx-gen 3)
    (sig (body a (exp (gen) l-1) (pubk "sig" a)) (privk "sig" a)) (3 1))
  (strand-map 0 3 1 2)
  (traces
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
    ((load priv-stor (cat pt-0 (pv b l)))
      (recv
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l-0)) (exp (gen) (mul x l)))))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l-0)))
      (send
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))))
  (label 2574)
  (parent 2565)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-0) (l-peer l) (x x) (eta y) (na na) (nb nb)
        (priv-stor priv-stor-0))))
  (origs (l-0 (3 1)) (pt-2 (3 1)) (l (1 1)) (pt-0 (1 1)) (nb (2 3))
    (na (0 2)))
  (ugens (y (2 3)) (x (0 2))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (b self name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (x l l-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a self) (b b)
    (priv-stor priv-stor-0) (l l) (x x) (beta l-0) (eta (one)))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l-0))
  (precedes ((1 1) (3 0)) ((1 2) (0 1)) ((2 1) (0 0)) ((2 2) (0 3))
    ((3 2) (0 3)))
  (non-orig (privk "sig" b) (privk "sig" self))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0))
  (gen-st (pv b l-0) (pv self l))
  (facts (neq b self) (neq self b))
  (leads-to ((1 1) (3 0)) ((2 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (3 0))
  (strand-map 0 1 2 4)
  (traces
    ((load priv-stor-0 (cat pt-2 (pv self l)))
      (recv
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na self b (exp (gen) x)))
      (recv
        (cat (gen)
          (enc na nb self b
            (hash (exp (gen) l) (exp (gen) (mul x l-0)))))))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv b l-0)))
      (send
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv self l)))
      (send
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self))))
    ((load priv-stor (cat pt-0 (pv b l-0)))
      (stor priv-stor (cat pt-3 "nil")) (send l-0)))
  (label 2799)
  (parent 2565)
  (realized)
  (shape)
  (maps
    ((0)
      ((a self) (b b) (l l) (l-peer l-0) (x x) (eta (one)) (na na)
        (nb nb) (priv-stor priv-stor-0))))
  (origs (pt-3 (3 1)) (l (2 1)) (pt-2 (2 1)) (l-0 (1 1)) (pt-0 (1 1))
    (na (0 2)))
  (ugens (x (0 2))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 ignore-1 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pt-6 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (y x l l-0 l-1 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-1) (x x) (beta l) (eta (mul y l-0 (rec l-1))))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-1))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l))
  (defstrand resp 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor-0)
    (l l) (y y) (alpha l-0) (chi x))
  (defstrand ltx-gen 3 (ignore ignore-1) (self a)
    (priv-stor priv-stor-1) (l l-0))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor-1) (l l-0))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l-1))
  (precedes ((0 2) (3 2)) ((1 1) (0 0)) ((1 1) (6 0)) ((2 1) (3 0))
    ((2 2) (0 1)) ((3 3) (0 3)) ((4 1) (5 0)) ((4 2) (3 1))
    ((5 2) (0 3)) ((6 2) (0 3)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig na nb l l-0 l-1)
  (uniq-gen y x)
  (absent (y x) (y l) (y l-0) (x l) (x l-1))
  (gen-st (pv a l-0) (pv a l-1) (pv b l))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (0 0)) ((1 1) (6 0)) ((2 1) (3 0)) ((4 1) (5 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (6 0))
  (strand-map 0 1 2 3 4 5 7)
  (traces
    ((load priv-stor (cat pt (pv a l-1)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul y l-0 (rec l-1)))
          (enc na nb a b
            (hash (exp (gen) (mul y l-0)) (exp (gen) (mul x l)))))))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l-1))))
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
            (hash (exp (gen) (mul y l-0)) (exp (gen) (mul x l)))))))
    ((load priv-stor-1 (cat pt-3 ignore-1))
      (stor priv-stor-1 (cat pt-4 (pv a l-0)))
      (send
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor-1 (cat pt-4 (pv a l-0)))
      (stor priv-stor-1 (cat pt-5 "nil")) (send l-0))
    ((load priv-stor (cat pt (pv a l-1)))
      (stor priv-stor (cat pt-6 "nil")) (send l-1)))
  (label 2920)
  (parent 2565)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-1) (l-peer l) (x x) (eta (mul y l-0 (rec l-1)))
        (na na) (nb nb) (priv-stor priv-stor))))
  (origs (pt-6 (6 1)) (pt-5 (5 1)) (l-0 (4 1)) (pt-4 (4 1)) (l (2 1))
    (pt-2 (2 1)) (nb (3 3)) (l-1 (1 1)) (pt (1 1)) (na (0 2)))
  (ugens (y (3 3)) (x (0 2))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (b self name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn) (x rndx)
    (w expt) (l l-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a self) (b b)
    (priv-stor priv-stor-0) (l l) (x x) (beta l-0) (eta w))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l-0))
  (precedes ((1 1) (3 0)) ((1 2) (0 1)) ((2 1) (0 0)) ((2 2) (0 3))
    ((3 2) (0 3)))
  (non-orig (privk "sig" b) (privk "sig" self))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0))
  (gen-st (pv b l-0) (pv self l))
  (facts (neq b self) (neq self b))
  (leads-to ((1 1) (3 0)) ((2 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (3 0))
  (strand-map 0 1 2 4)
  (traces
    ((load priv-stor-0 (cat pt-2 (pv self l)))
      (recv
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na self b (exp (gen) x)))
      (recv
        (cat (exp (gen) w)
          (enc na nb self b
            (hash (exp (gen) (mul w l)) (exp (gen) (mul x l-0)))))))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv b l-0)))
      (send
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv self l)))
      (send
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self))))
    ((load priv-stor (cat pt-0 (pv b l-0)))
      (stor priv-stor (cat pt-3 "nil")) (send l-0)))
  (label 3541)
  (parent 2565)
  (realized)
  (shape)
  (maps
    ((0)
      ((a self) (b b) (l l) (l-peer l-0) (x x) (eta w) (na na) (nb nb)
        (priv-stor priv-stor-0))))
  (origs (pt-3 (3 1)) (l (2 1)) (pt-2 (2 1)) (l-0 (1 1)) (pt-0 (1 1))
    (na (0 2)))
  (ugens (x (0 2))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (priv-stor priv-stor-0 locn)
    (x l l-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-0) (x x) (beta l) (eta (mul x (rec l-0))))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l-0))
  (precedes ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)) ((2 2) (0 1))
    ((3 2) (0 3)) ((4 2) (0 3)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0))
  (gen-st (pv a l-0) (pv b l))
  (facts (neq b a) (neq a b))
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
        (cat (exp (gen) (mul x (rec l-0)))
          (enc na nb a b (hash (exp (gen) x) (exp (gen) (mul x l)))))))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l-0))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-0 (cat pt-2 (pv b l)))
      (stor priv-stor-0 (cat pt-3 "nil")) (send l))
    ((load priv-stor (cat pt (pv a l-0)))
      (stor priv-stor (cat pt-4 "nil")) (send l-0)))
  (label 3869)
  (parent 2565)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-0) (l-peer l) (x x) (eta (mul x (rec l-0)))
        (na na) (nb nb) (priv-stor priv-stor))))
  (origs (pt-4 (4 1)) (pt-3 (3 1)) (na (0 2)) (l (2 1)) (pt-2 (2 1))
    (l-0 (1 1)) (pt (1 1)))
  (ugens (x (0 2))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (priv-stor priv-stor-0 locn)
    (x l l-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (x x) (beta l-0) (eta (mul (rec l) l-0)))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (precedes ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)) ((2 2) (0 1))
    ((3 2) (0 3)) ((4 2) (0 3)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0))
  (gen-st (pv a l) (pv b l-0))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (4 0))
  (strand-map 0 1 2 3 5)
  (traces
    ((load priv-stor (cat pt (pv a l)))
      (recv
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul (rec l) l-0))
          (enc na nb a b
            (hash (exp (gen) l-0) (exp (gen) (mul x l-0)))))))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l-0)))
      (send
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-0 (cat pt-2 (pv b l-0)))
      (stor priv-stor-0 (cat pt-3 "nil")) (send l-0))
    ((load priv-stor (cat pt (pv a l)))
      (stor priv-stor (cat pt-4 "nil")) (send l)))
  (label 4651)
  (parent 2565)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l) (l-peer l-0) (x x) (eta (mul (rec l) l-0))
        (na na) (nb nb) (priv-stor priv-stor))))
  (origs (l-0 (2 1)) (pt-2 (2 1)) (pt-4 (4 1)) (pt-3 (3 1)) (l (1 1))
    (pt (1 1)) (na (0 2)))
  (ugens (x (0 2))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (priv-stor priv-stor-0 locn)
    (l x l-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-0) (x x) (beta l) (eta x))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l-0))
  (precedes ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)) ((2 2) (0 1))
    ((3 2) (0 3)) ((4 2) (0 3)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0))
  (gen-st (pv a l-0) (pv b l))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (3 0))
  (strand-map 0 1 2 4 5)
  (traces
    ((load priv-stor (cat pt (pv a l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) x)
          (enc na nb a b
            (hash (exp (gen) (mul x l-0)) (exp (gen) (mul l x)))))))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l-0))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-0 (cat pt-2 (pv b l)))
      (stor priv-stor-0 (cat pt-3 "nil")) (send l))
    ((load priv-stor (cat pt (pv a l-0)))
      (stor priv-stor (cat pt-4 "nil")) (send l-0)))
  (label 4853)
  (parent 2565)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-0) (l-peer l) (x x) (eta x) (na na) (nb nb)
        (priv-stor priv-stor))))
  (origs (pt-4 (4 1)) (na (0 2)) (pt-3 (3 1)) (l (2 1)) (pt-2 (2 1))
    (l-0 (1 1)) (pt (1 1)))
  (ugens (x (0 2))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (priv-stor priv-stor-0 locn)
    (x l l-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-0) (x x) (beta l) (eta (one)))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l-0))
  (precedes ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)) ((2 2) (0 1))
    ((3 2) (0 3)) ((4 2) (0 3)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0))
  (gen-st (pv a l-0) (pv b l))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (3 0))
  (strand-map 0 1 2 4 5)
  (traces
    ((load priv-stor (cat pt (pv a l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (gen)
          (enc na nb a b
            (hash (exp (gen) l-0) (exp (gen) (mul x l)))))))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l-0))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-0 (cat pt-2 (pv b l)))
      (stor priv-stor-0 (cat pt-3 "nil")) (send l))
    ((load priv-stor (cat pt (pv a l-0)))
      (stor priv-stor (cat pt-4 "nil")) (send l-0)))
  (label 4858)
  (parent 2565)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-0) (l-peer l) (x x) (eta (one)) (na na) (nb nb)
        (priv-stor priv-stor))))
  (origs (pt-4 (4 1)) (pt-3 (3 1)) (l (2 1)) (pt-2 (2 1)) (l-0 (1 1))
    (pt (1 1)) (na (0 2)))
  (ugens (x (0 2))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (priv-stor priv-stor-0 locn)
    (x l l-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-0) (x x) (beta l) (eta l))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l-0))
  (precedes ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)) ((2 2) (0 1))
    ((3 2) (0 3)) ((4 2) (0 3)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0))
  (gen-st (pv a l-0) (pv b l))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (3 0))
  (strand-map 0 1 2 4 5)
  (traces
    ((load priv-stor (cat pt (pv a l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) l)
          (enc na nb a b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x l)))))))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l-0))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-0 (cat pt-2 (pv b l)))
      (stor priv-stor-0 (cat pt-3 "nil")) (send l))
    ((load priv-stor (cat pt (pv a l-0)))
      (stor priv-stor (cat pt-4 "nil")) (send l-0)))
  (label 5067)
  (parent 2565)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-0) (l-peer l) (x x) (eta l) (na na) (nb nb)
        (priv-stor priv-stor))))
  (origs (pt-4 (4 1)) (l (2 1)) (pt-2 (2 1)) (pt-3 (3 1)) (l-0 (1 1))
    (pt (1 1)) (na (0 2)))
  (ugens (x (0 2))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (y x l l-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor-0)
    (l l) (x x) (beta l-0) (eta y))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l-0))
  (precedes ((1 1) (3 0)) ((1 2) (0 1)) ((2 1) (0 0)) ((2 2) (0 3))
    ((3 2) (0 3)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0))
  (gen-st (pv a l) (pv b l-0))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (3 0)) ((2 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization forgot nb)
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor-0 (cat pt-2 (pv a l)))
      (recv
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l-0)))))))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv b l-0)))
      (send
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l)))
      (send
        (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor (cat pt-0 (pv b l-0)))
      (stor priv-stor (cat pt-3 "nil")) (send l-0)))
  (label 5093)
  (parent 2565)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l) (l-peer l-0) (x x) (eta y) (na na) (nb nb)
        (priv-stor priv-stor-0))))
  (origs (pt-3 (3 1)) (l (2 1)) (pt-2 (2 1)) (l-0 (1 1)) (pt-0 (1 1))
    (na (0 2)))
  (ugens (x (0 2))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (priv-stor priv-stor-0 locn)
    (x y l l-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-0) (x x) (beta l) (eta (mul y (rec l-0))))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l-0))
  (precedes ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)) ((2 2) (0 1))
    ((3 2) (0 3)) ((4 2) (0 3)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0))
  (gen-st (pv a l-0) (pv b l))
  (facts (neq b a) (neq a b))
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
        (cat (exp (gen) (mul y (rec l-0)))
          (enc na nb a b (hash (exp (gen) y) (exp (gen) (mul x l)))))))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l-0))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-0 (cat pt-2 (pv b l)))
      (stor priv-stor-0 (cat pt-3 "nil")) (send l))
    ((load priv-stor (cat pt (pv a l-0)))
      (stor priv-stor (cat pt-4 "nil")) (send l-0)))
  (label 5098)
  (parent 2565)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-0) (l-peer l) (x x) (eta (mul y (rec l-0)))
        (na na) (nb nb) (priv-stor priv-stor))))
  (origs (pt-4 (4 1)) (pt-3 (3 1)) (l-0 (1 1)) (pt (1 1)) (l (2 1))
    (pt-2 (2 1)) (na (0 2)))
  (ugens (x (0 2))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (priv-stor priv-stor-0 locn)
    (x l l-0 l-1 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-1) (x x) (beta l) (eta l-0))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-1))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l-1))
  (precedes ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)) ((2 2) (0 1))
    ((3 2) (0 3)) ((4 2) (0 3)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig na l l-1)
  (uniq-gen x)
  (absent (x l) (x l-1))
  (gen-st (pv a l-1) (pv b l))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (3 0))
  (strand-map 0 1 2 4 5)
  (traces
    ((load priv-stor (cat pt (pv a l-1)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) l-0)
          (enc na nb a b
            (hash (exp (gen) (mul l-0 l-1)) (exp (gen) (mul x l)))))))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l-1))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-0 (cat pt-2 (pv b l)))
      (stor priv-stor-0 (cat pt-3 "nil")) (send l))
    ((load priv-stor (cat pt (pv a l-1)))
      (stor priv-stor (cat pt-4 "nil")) (send l-1)))
  (label 5158)
  (parent 2565)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-1) (l-peer l) (x x) (eta l-0) (na na) (nb nb)
        (priv-stor priv-stor))))
  (origs (pt-4 (4 1)) (pt-3 (3 1)) (l (2 1)) (pt-2 (2 1)) (l-1 (1 1))
    (pt (1 1)) (na (0 2)))
  (ugens (x (0 2))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (priv-stor priv-stor-0 locn)
    (x l l-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-0) (x x) (beta l) (eta (rec l-0)))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l-0))
  (precedes ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)) ((2 2) (0 1))
    ((3 2) (0 3)) ((4 2) (0 3)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0))
  (gen-st (pv a l-0) (pv b l))
  (facts (neq b a) (neq a b))
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
        (cat (exp (gen) (rec l-0))
          (enc na nb a b (hash (gen) (exp (gen) (mul x l)))))))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l-0))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-0 (cat pt-2 (pv b l)))
      (stor priv-stor-0 (cat pt-3 "nil")) (send l))
    ((load priv-stor (cat pt (pv a l-0)))
      (stor priv-stor (cat pt-4 "nil")) (send l-0)))
  (label 5170)
  (parent 2565)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-0) (l-peer l) (x x) (eta (rec l-0)) (na na)
        (nb nb) (priv-stor priv-stor))))
  (origs (pt-4 (4 1)) (pt-3 (3 1)) (l (2 1)) (pt-2 (2 1)) (l-0 (1 1))
    (pt (1 1)) (na (0 2)))
  (ugens (x (0 2))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (b self name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (priv-stor priv-stor-0 locn)
    (x l l-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a self) (b b)
    (priv-stor priv-stor-0) (l l-0) (x x) (beta l) (eta l-0))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l))
  (defstrand ltx-gen 2 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor-0) (l l-0))
  (precedes ((1 1) (2 0)) ((1 2) (0 1)) ((2 2) (0 3)) ((3 1) (0 0))
    ((3 1) (4 0)) ((4 2) (0 3)))
  (non-orig (privk "sig" b) (privk "sig" self))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0))
  (gen-st (pv b l) (pv self l-0))
  (facts (neq b self) (neq self b))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)) ((3 1) (4 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (4 0))
  (strand-map 0 1 2 3 5)
  (traces
    ((load priv-stor-0 (cat pt-3 (pv self l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na self b (exp (gen) x)))
      (recv
        (cat (exp (gen) l-0)
          (enc na nb self b
            (hash (exp (gen) (mul l-0 l-0)) (exp (gen) (mul x l)))))))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt-0 (pv b l)))
      (stor priv-stor (cat pt-1 "nil")) (send l))
    ((load priv-stor-0 (cat pt-2 ignore-0))
      (stor priv-stor-0 (cat pt-3 (pv self l-0))))
    ((load priv-stor-0 (cat pt-3 (pv self l-0)))
      (stor priv-stor-0 (cat pt-4 "nil")) (send l-0)))
  (label 5255)
  (parent 2565)
  (realized)
  (shape)
  (maps
    ((0)
      ((a self) (b b) (l l-0) (l-peer l) (x x) (eta l-0) (na na) (nb nb)
        (priv-stor priv-stor-0))))
  (origs (pt-4 (4 1)) (l-0 (3 1)) (pt-3 (3 1)) (pt-1 (2 1)) (l (1 1))
    (pt-0 (1 1)) (na (0 2)))
  (ugens (x (0 2))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 ignore-1 mesg) (na nb data) (a b self name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pt-6 pt-7 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (x l l-0 l-1 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-0) (x x) (beta l) (eta (mul (rec l-0) l-1)))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-gen 2 (ignore ignore-1) (self self)
    (priv-stor priv-stor-1) (l l-1))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l-0))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor-1) (l l-1))
  (precedes ((1 1) (0 0)) ((1 1) (5 0)) ((2 1) (4 0)) ((2 2) (0 1))
    ((3 1) (6 0)) ((4 2) (0 3)) ((5 2) (0 3)) ((6 2) (0 3)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig na l l-0 l-1)
  (uniq-gen x)
  (absent (x l) (x l-0))
  (precur (5 0))
  (gen-st (pv a l-0) (pv b l) (pv self l-1))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (0 0)) ((1 1) (5 0)) ((2 1) (4 0)) ((3 1) (6 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (6 0))
  (strand-map 0 1 2 3 4 5 7)
  (traces
    ((load priv-stor (cat pt (pv a l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul (rec l-0) l-1))
          (enc na nb a b
            (hash (exp (gen) l-1) (exp (gen) (mul x l)))))))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l-0))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-1 (cat pt-3 ignore-1))
      (stor priv-stor-1 (cat pt-4 (pv self l-1))))
    ((load priv-stor-0 (cat pt-2 (pv b l)))
      (stor priv-stor-0 (cat pt-5 "nil")) (send l))
    ((load priv-stor (cat pt (pv a l-0)))
      (stor priv-stor (cat pt-6 "nil")) (send l-0))
    ((load priv-stor-1 (cat pt-4 (pv self l-1)))
      (stor priv-stor-1 (cat pt-7 "nil")) (send l-1)))
  (label 5289)
  (parent 2565)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-0) (l-peer l) (x x) (eta (mul (rec l-0) l-1))
        (na na) (nb nb) (priv-stor priv-stor))))
  (origs (pt-7 (6 1)) (pt-6 (5 1)) (pt-5 (4 1)) (l-1 (3 1)) (pt-4 (3 1))
    (l (2 1)) (pt-2 (2 1)) (l-0 (1 1)) (pt (1 1)) (na (0 2)))
  (ugens (x (0 2))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (priv-stor priv-stor-0 locn)
    (w expt) (l x l-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-0) (x x) (beta l) (eta (mul w x)))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l-0))
  (precedes ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)) ((2 2) (0 1))
    ((3 2) (0 3)) ((4 2) (0 3)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0))
  (gen-st (pv a l-0) (pv b l))
  (facts (neq b a) (neq a b))
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
        (cat (exp (gen) (mul w x))
          (enc na nb a b
            (hash (exp (gen) (mul w x l-0)) (exp (gen) (mul l x)))))))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l-0))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-0 (cat pt-2 (pv b l)))
      (stor priv-stor-0 (cat pt-3 "nil")) (send l))
    ((load priv-stor (cat pt (pv a l-0)))
      (stor priv-stor (cat pt-4 "nil")) (send l-0)))
  (label 5300)
  (parent 2565)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-0) (l-peer l) (x x) (eta (mul w x)) (na na)
        (nb nb) (priv-stor priv-stor))))
  (origs (pt-4 (4 1)) (na (0 2)) (pt-3 (3 1)) (l (2 1)) (pt-2 (2 1))
    (l-0 (1 1)) (pt (1 1)))
  (ugens (x (0 2))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (priv-stor priv-stor-0 locn)
    (w expt) (l x l-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-0) (x x) (beta l) (eta (mul w x (rec l-0))))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l-0))
  (precedes ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)) ((2 2) (0 1))
    ((3 2) (0 3)) ((4 2) (0 3)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0) (l-0 w))
  (gen-st (pv a l-0) (pv b l))
  (facts (neq b a) (neq a b))
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
        (cat (exp (gen) (mul w x (rec l-0)))
          (enc na nb a b
            (hash (exp (gen) (mul w x)) (exp (gen) (mul l x)))))))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l-0))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-0 (cat pt-2 (pv b l)))
      (stor priv-stor-0 (cat pt-3 "nil")) (send l))
    ((load priv-stor (cat pt (pv a l-0)))
      (stor priv-stor (cat pt-4 "nil")) (send l-0)))
  (label 5321)
  (parent 2565)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-0) (l-peer l) (x x) (eta (mul w x (rec l-0)))
        (na na) (nb nb) (priv-stor priv-stor))))
  (origs (pt-4 (4 1)) (na (0 2)) (pt-3 (3 1)) (l (2 1)) (pt-2 (2 1))
    (l-0 (1 1)) (pt (1 1)))
  (ugens (x (0 2))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (priv-stor priv-stor-0 locn)
    (x l rndx) (w expt) (l-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-0) (x x) (beta l) (eta (mul w (rec l-0))))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l-0))
  (precedes ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)) ((2 2) (0 1))
    ((3 2) (0 3)) ((4 2) (0 3)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0) (l-0 w))
  (gen-st (pv a l-0) (pv b l))
  (facts (neq b a) (neq a b))
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
        (cat (exp (gen) (mul w (rec l-0)))
          (enc na nb a b (hash (exp (gen) w) (exp (gen) (mul x l)))))))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l-0))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-0 (cat pt-2 (pv b l)))
      (stor priv-stor-0 (cat pt-3 "nil")) (send l))
    ((load priv-stor (cat pt (pv a l-0)))
      (stor priv-stor (cat pt-4 "nil")) (send l-0)))
  (label 5322)
  (parent 2565)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-0) (l-peer l) (x x) (eta (mul w (rec l-0)))
        (na na) (nb nb) (priv-stor priv-stor))))
  (origs (pt-4 (4 1)) (pt-3 (3 1)) (l (2 1)) (pt-2 (2 1)) (l-0 (1 1))
    (pt (1 1)) (na (0 2)))
  (ugens (x (0 2))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (priv-stor priv-stor-0 locn)
    (x l l-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-0) (x x) (beta l) (eta l))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l-0))
  (precedes ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)) ((2 2) (0 1))
    ((3 2) (0 3)) ((4 2) (0 3)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0) (l l-0))
  (gen-st (pv a l-0) (pv b l))
  (facts (neq b a) (neq a b))
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
        (cat (exp (gen) l)
          (enc na nb a b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x l)))))))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l-0))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-0 (cat pt-2 (pv b l)))
      (stor priv-stor-0 (cat pt-3 "nil")) (send l))
    ((load priv-stor (cat pt (pv a l-0)))
      (stor priv-stor (cat pt-4 "nil")) (send l-0)))
  (label 5327)
  (parent 2565)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-0) (l-peer l) (x x) (eta l) (na na) (nb nb)
        (priv-stor priv-stor))))
  (origs (pt-4 (4 1)) (pt-3 (3 1)) (l (2 1)) (pt-2 (2 1)) (l-0 (1 1))
    (pt (1 1)) (na (0 2)))
  (ugens (x (0 2))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (priv-stor priv-stor-0 locn)
    (x rndx) (w expt) (l l-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-0) (x x) (beta l) (eta (mul w l (rec l-0))))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l-0))
  (precedes ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)) ((2 2) (0 1))
    ((3 2) (0 3)) ((4 2) (0 3)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0) (l-0 w))
  (gen-st (pv a l-0) (pv b l))
  (facts (neq b a) (neq a b))
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
        (cat (exp (gen) (mul w l (rec l-0)))
          (enc na nb a b
            (hash (exp (gen) (mul w l)) (exp (gen) (mul x l)))))))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l-0))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-0 (cat pt-2 (pv b l)))
      (stor priv-stor-0 (cat pt-3 "nil")) (send l))
    ((load priv-stor (cat pt (pv a l-0)))
      (stor priv-stor (cat pt-4 "nil")) (send l-0)))
  (label 5329)
  (parent 2565)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-0) (l-peer l) (x x) (eta (mul w l (rec l-0)))
        (na na) (nb nb) (priv-stor priv-stor))))
  (origs (pt-4 (4 1)) (l (2 1)) (pt-2 (2 1)) (pt-3 (3 1)) (l-0 (1 1))
    (pt (1 1)) (na (0 2)))
  (ugens (x (0 2))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 ignore-1 mesg) (na nb data) (a b self name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pt-6 pt-7 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (x l l-0 l-1 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-1) (x x) (beta l) (eta l-0))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-1))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-gen 2 (ignore ignore-1) (self self)
    (priv-stor priv-stor-1) (l l-0))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor-1) (l l-0))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l-1))
  (precedes ((1 1) (0 0)) ((1 1) (6 0)) ((2 1) (4 0)) ((2 2) (0 1))
    ((3 1) (5 0)) ((4 2) (0 3)) ((5 2) (0 3)) ((6 2) (0 3)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig na l l-0 l-1)
  (uniq-gen x)
  (absent (x l) (x l-1))
  (precur (4 0))
  (gen-st (pv a l-1) (pv b l) (pv self l-0))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (0 0)) ((1 1) (6 0)) ((2 1) (4 0)) ((3 1) (5 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (5 0))
  (strand-map 0 1 2 3 4 6 7)
  (traces
    ((load priv-stor (cat pt (pv a l-1)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) l-0)
          (enc na nb a b
            (hash (exp (gen) (mul l-0 l-1)) (exp (gen) (mul x l)))))))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l-1))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-1 (cat pt-3 ignore-1))
      (stor priv-stor-1 (cat pt-4 (pv self l-0))))
    ((load priv-stor-0 (cat pt-2 (pv b l)))
      (stor priv-stor-0 (cat pt-5 "nil")) (send l))
    ((load priv-stor-1 (cat pt-4 (pv self l-0)))
      (stor priv-stor-1 (cat pt-6 "nil")) (send l-0))
    ((load priv-stor (cat pt (pv a l-1)))
      (stor priv-stor (cat pt-7 "nil")) (send l-1)))
  (label 5330)
  (parent 2565)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-1) (l-peer l) (x x) (eta l-0) (na na) (nb nb)
        (priv-stor priv-stor))))
  (origs (pt-7 (6 1)) (pt-6 (5 1)) (l-1 (1 1)) (pt (1 1)) (pt-5 (4 1))
    (l-0 (3 1)) (pt-4 (3 1)) (l (2 1)) (pt-2 (2 1)) (na (0 2)))
  (ugens (x (0 2))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 ignore-1 mesg) (na nb data) (a b self name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pt-6 pt-7 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (x l l-0 l-1 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-1) (x x) (beta l) (eta l-0))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-1))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-gen 2 (ignore ignore-1) (self self)
    (priv-stor priv-stor-1) (l l-0))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor-1) (l l-0))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l-1))
  (precedes ((1 1) (0 0)) ((1 1) (6 0)) ((2 1) (4 0)) ((2 2) (0 1))
    ((3 1) (5 0)) ((4 2) (0 3)) ((5 2) (0 3)) ((6 2) (0 3)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig na l l-0 l-1)
  (uniq-gen x)
  (absent (x l) (x l-1) (l-0 l-1))
  (precur (4 0))
  (gen-st (pv a l-1) (pv b l) (pv self l-0))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (0 0)) ((1 1) (6 0)) ((2 1) (4 0)) ((3 1) (5 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (5 0))
  (strand-map 0 1 2 3 4 6 7)
  (traces
    ((load priv-stor (cat pt (pv a l-1)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) l-0)
          (enc na nb a b
            (hash (exp (gen) (mul l-0 l-1)) (exp (gen) (mul x l)))))))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l-1))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-1 (cat pt-3 ignore-1))
      (stor priv-stor-1 (cat pt-4 (pv self l-0))))
    ((load priv-stor-0 (cat pt-2 (pv b l)))
      (stor priv-stor-0 (cat pt-5 "nil")) (send l))
    ((load priv-stor-1 (cat pt-4 (pv self l-0)))
      (stor priv-stor-1 (cat pt-6 "nil")) (send l-0))
    ((load priv-stor (cat pt (pv a l-1)))
      (stor priv-stor (cat pt-7 "nil")) (send l-1)))
  (label 5341)
  (parent 2565)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-1) (l-peer l) (x x) (eta l-0) (na na) (nb nb)
        (priv-stor priv-stor))))
  (origs (pt-7 (6 1)) (pt-6 (5 1)) (l-0 (3 1)) (pt-4 (3 1)) (pt-5 (4 1))
    (l (2 1)) (pt-2 (2 1)) (l-1 (1 1)) (pt (1 1)) (na (0 2)))
  (ugens (x (0 2))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (priv-stor priv-stor-0 locn)
    (x l rndx) (w expt) (l-0 l-1 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-1) (x x) (beta l) (eta (mul w l-0 (rec l-1))))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-1))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor-0) (l l))
  (deflistener (cat (exp (gen) l-0) (mul w (rec l-1))))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l-1))
  (precedes ((1 1) (0 0)) ((1 1) (5 0)) ((2 1) (3 0)) ((2 2) (0 1))
    ((3 2) (0 3)) ((5 2) (0 3)) ((5 2) (4 0)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig na l l-1)
  (uniq-gen x)
  (absent (x l) (x l-1) (l-1 w))
  (precur (4 0))
  (gen-st (pv a l-1) (pv b l))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (0 0)) ((1 1) (5 0)) ((2 1) (3 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (5 0))
  (strand-map 0 1 2 3 4 6)
  (traces
    ((load priv-stor (cat pt (pv a l-1)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul w l-0 (rec l-1)))
          (enc na nb a b
            (hash (exp (gen) (mul w l-0)) (exp (gen) (mul x l)))))))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l-1))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-0 (cat pt-2 (pv b l)))
      (stor priv-stor-0 (cat pt-3 "nil")) (send l))
    ((recv (cat (exp (gen) l-0) (mul w (rec l-1)))))
    ((load priv-stor (cat pt (pv a l-1)))
      (stor priv-stor (cat pt-4 "nil")) (send l-1)))
  (label 5343)
  (parent 2565)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-1) (l-peer l) (x x) (eta (mul w l-0 (rec l-1)))
        (na na) (nb nb) (priv-stor priv-stor))))
  (origs (pt-4 (5 1)) (pt-3 (3 1)) (l (2 1)) (pt-2 (2 1)) (l-1 (1 1))
    (pt (1 1)) (na (0 2)))
  (ugens (x (0 2))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (b self name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (priv-stor priv-stor-0 locn)
    (x l l-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a self) (b b)
    (priv-stor priv-stor-0) (l l-0) (x x) (beta l) (eta (mul l l-0)))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l))
  (defstrand ltx-gen 2 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor-0) (l l-0))
  (precedes ((1 1) (2 0)) ((1 2) (0 1)) ((2 2) (0 3)) ((3 1) (0 0))
    ((3 1) (4 0)) ((4 2) (0 3)))
  (non-orig (privk "sig" b) (privk "sig" self))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0) (l (mul l-0 l-0)))
  (gen-st (pv b l) (pv self l-0))
  (facts (neq b self) (neq self b))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)) ((3 1) (4 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (4 0))
  (strand-map 0 1 2 3 5)
  (traces
    ((load priv-stor-0 (cat pt-3 (pv self l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na self b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul l l-0))
          (enc na nb self b
            (hash (exp (gen) (mul l l-0 l-0)) (exp (gen) (mul x l)))))))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt-0 (pv b l)))
      (stor priv-stor (cat pt-1 "nil")) (send l))
    ((load priv-stor-0 (cat pt-2 ignore-0))
      (stor priv-stor-0 (cat pt-3 (pv self l-0))))
    ((load priv-stor-0 (cat pt-3 (pv self l-0)))
      (stor priv-stor-0 (cat pt-4 "nil")) (send l-0)))
  (label 5351)
  (parent 2565)
  (realized)
  (shape)
  (maps
    ((0)
      ((a self) (b b) (l l-0) (l-peer l) (x x) (eta (mul l l-0)) (na na)
        (nb nb) (priv-stor priv-stor-0))))
  (origs (pt-4 (4 1)) (pt-1 (2 1)) (l (1 1)) (pt-0 (1 1)) (l-0 (3 1))
    (pt-3 (3 1)) (na (0 2)))
  (ugens (x (0 2))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 ignore-1 mesg) (na nb data)
    (b self self-0 name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pt-6 pt-7 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (x l l-0 l-1 rndx))
  (defstrand init 4 (na na) (nb nb) (a self-0) (b b)
    (priv-stor priv-stor-1) (l l-1) (x x) (beta l) (eta (mul l-0 l-1)))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 2 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l))
  (defstrand ltx-gen 2 (ignore ignore-1) (self self-0)
    (priv-stor priv-stor-1) (l l-1))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-disclose 3 (self self-0) (priv-stor priv-stor-1)
    (l l-1))
  (precedes ((1 1) (3 0)) ((1 2) (0 1)) ((2 1) (5 0)) ((3 2) (0 3))
    ((4 1) (0 0)) ((4 1) (6 0)) ((5 2) (0 3)) ((6 2) (0 3)))
  (non-orig (privk "sig" b) (privk "sig" self-0))
  (uniq-orig na l l-0 l-1)
  (uniq-gen x)
  (absent (x l) (x l-1) (l-0 (mul l-1 l-1)))
  (precur (3 0))
  (gen-st (pv b l) (pv self l-0) (pv self-0 l-1))
  (facts (neq b self-0) (neq self-0 b))
  (leads-to ((1 1) (3 0)) ((2 1) (5 0)) ((4 1) (0 0)) ((4 1) (6 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (6 0))
  (strand-map 0 1 2 3 4 5 7)
  (traces
    ((load priv-stor-1 (cat pt-5 (pv self-0 l-1)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na self-0 b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul l-0 l-1))
          (enc na nb self-0 b
            (hash (exp (gen) (mul l-0 l-1 l-1))
              (exp (gen) (mul x l)))))))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv self l-0))))
    ((load priv-stor (cat pt-0 (pv b l)))
      (stor priv-stor (cat pt-3 "nil")) (send l))
    ((load priv-stor-1 (cat pt-4 ignore-1))
      (stor priv-stor-1 (cat pt-5 (pv self-0 l-1))))
    ((load priv-stor-0 (cat pt-2 (pv self l-0)))
      (stor priv-stor-0 (cat pt-6 "nil")) (send l-0))
    ((load priv-stor-1 (cat pt-5 (pv self-0 l-1)))
      (stor priv-stor-1 (cat pt-7 "nil")) (send l-1)))
  (label 5354)
  (parent 2565)
  (realized)
  (shape)
  (maps
    ((0)
      ((a self-0) (b b) (l l-1) (l-peer l) (x x) (eta (mul l-0 l-1))
        (na na) (nb nb) (priv-stor priv-stor-1))))
  (origs (pt-7 (6 1)) (pt-6 (5 1)) (l-0 (2 1)) (pt-2 (2 1)) (l-1 (4 1))
    (pt-5 (4 1)) (pt-3 (3 1)) (l (1 1)) (pt-0 (1 1)) (na (0 2)))
  (ugens (x (0 2))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 ignore-1 mesg) (na nb data) (a b a-0 name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pt-6 pt-7 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (y x l l-0 l-1 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-1) (x x) (beta l) (eta (mul y l-0 (rec l-1))))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-1))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-gen 2 (ignore ignore-1) (self a-0)
    (priv-stor priv-stor-1) (l l-0))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self a-0) (priv-stor priv-stor-1) (l l-0))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l-1))
  (precedes ((1 1) (0 0)) ((1 1) (6 0)) ((2 1) (4 0)) ((2 2) (0 1))
    ((3 1) (5 0)) ((4 2) (0 3)) ((5 2) (0 3)) ((6 2) (0 3)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig na l l-0 l-1)
  (uniq-gen x)
  (absent (x l) (x l-1))
  (gen-st (pv a l-0) (pv a l-1) (pv b l) (pv a-0 l-0))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (0 0)) ((1 1) (6 0)) ((2 1) (4 0)) ((3 1) (5 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization forgot (privk "sig" a-0))
  (strand-map 0 1 2 3 4 5 6)
  (traces
    ((load priv-stor (cat pt (pv a l-1)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul y l-0 (rec l-1)))
          (enc na nb a b
            (hash (exp (gen) (mul y l-0)) (exp (gen) (mul x l)))))))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l-1))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-1 (cat pt-3 ignore-1))
      (stor priv-stor-1 (cat pt-4 (pv a-0 l-0))))
    ((load priv-stor-0 (cat pt-2 (pv b l)))
      (stor priv-stor-0 (cat pt-5 "nil")) (send l))
    ((load priv-stor-1 (cat pt-4 (pv a-0 l-0)))
      (stor priv-stor-1 (cat pt-6 "nil")) (send l-0))
    ((load priv-stor (cat pt (pv a l-1)))
      (stor priv-stor (cat pt-7 "nil")) (send l-1)))
  (label 5355)
  (parent 2565)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-1) (l-peer l) (x x) (eta (mul y l-0 (rec l-1)))
        (na na) (nb nb) (priv-stor priv-stor))))
  (origs (pt-7 (6 1)) (pt-6 (5 1)) (pt-5 (4 1)) (l-0 (3 1)) (pt-4 (3 1))
    (l (2 1)) (pt-2 (2 1)) (l-1 (1 1)) (pt (1 1)) (na (0 2)))
  (ugens (x (0 2))))

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
  (vars (na nb data) (a b name) (pt pval) (priv-stor locn)
    (l l-peer y rndx) (chi expt))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (y y) (alpha l-peer) (chi chi))
  (non-orig (privk "sig" a) (privk "sig" b))
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
            (hash (exp (gen) (mul l-peer y)) (exp (gen) (mul l chi))))))
      (recv nb)))
  (label 5356)
  (unrealized (0 1))
  (origs (nb (0 3)))
  (ugens (y (0 3)))
  (comment "Not closed under rules"))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn)
    (y x l l-0 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor-0)
    (l l-0) (y y) (alpha l) (chi x))
  (defstrand ltx-gen 3 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand init 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (x x) (beta l-0) (eta y))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l-0))
  (precedes ((0 3) (2 3)) ((1 1) (2 0)) ((1 2) (0 1)) ((2 2) (0 2))
    ((2 4) (0 4)) ((3 1) (0 0)) ((3 2) (2 1)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig na nb l l-0)
  (uniq-gen y x)
  (absent (y x) (y l) (y l-0) (x l) (x l-0))
  (gen-st (pv a l) (pv b l-0))
  (facts (neq b a) (neq a b) (undisclosed l-0) (undisclosed l))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation encryption-test (displaced 1 4 ltx-gen 3)
    (sig (body b (exp (gen) l-1) (pubk "sig" b)) (privk "sig" b)) (3 1))
  (strand-map 0 3 1 2)
  (traces
    ((load priv-stor-0 (cat pt-2 (pv b l-0)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l-0))))))
      (recv nb))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv a l)))
      (send
        (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor (cat pt-0 (pv a l)))
      (recv
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l-0))))))
      (send nb))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l-0)))
      (send
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b)))))
  (label 5365)
  (parent 5356)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-0) (l-peer l) (y y) (chi x) (na na) (nb nb)
        (priv-stor priv-stor-0))))
  (origs (l-0 (3 1)) (pt-2 (3 1)) (l (1 1)) (pt-0 (1 1)) (na (2 2))
    (nb (0 3)))
  (ugens (x (2 2)) (y (0 3))))

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
  (vars (na nb data) (a b name) (pt pval) (priv-stor locn)
    (l l-peer y rndx) (chi expt))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (y y) (alpha l-peer) (chi chi))
  (non-orig (privk "sig" a) (privk "sig" b))
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
            (hash (exp (gen) (mul l-peer y)) (exp (gen) (mul l chi))))))
      (recv nb)))
  (label 5389)
  (unrealized (0 1))
  (origs (nb (0 3)))
  (ugens (y (0 3)))
  (comment "Not closed under rules"))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn)
    (y x l l-0 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor-0)
    (l l-0) (y y) (alpha l) (chi x))
  (defstrand ltx-gen 3 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand init 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (x x) (beta l-0) (eta y))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l-0))
  (precedes ((0 3) (2 3)) ((1 1) (2 0)) ((1 2) (0 1)) ((2 2) (0 2))
    ((2 4) (0 4)) ((3 1) (0 0)) ((3 2) (2 1)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig na nb l l-0)
  (uniq-gen y x)
  (absent (y x) (y l) (y l-0) (x l) (x l-0))
  (gen-st (pv a l) (pv b l-0))
  (facts (neq b a) (neq a b) (undisclosed l))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation encryption-test (displaced 1 4 ltx-gen 3)
    (sig (body b (exp (gen) l-1) (pubk "sig" b)) (privk "sig" b)) (3 1))
  (strand-map 0 3 1 2)
  (traces
    ((load priv-stor-0 (cat pt-2 (pv b l-0)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l-0))))))
      (recv nb))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv a l)))
      (send
        (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor (cat pt-0 (pv a l)))
      (recv
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l-0))))))
      (send nb))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l-0)))
      (send
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b)))))
  (label 5398)
  (parent 5389)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-0) (l-peer l) (y y) (chi x) (na na) (nb nb)
        (priv-stor priv-stor-0))))
  (origs (l-0 (3 1)) (pt-2 (3 1)) (l (1 1)) (pt-0 (1 1)) (na (2 2))
    (nb (0 3)))
  (ugens (x (2 2)) (y (0 3))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 ignore-1 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pt-6 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (y x l l-0 l-1 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-1) (y y) (alpha l) (chi (mul x l-0 (rec l-1))))
  (defstrand ltx-gen 2 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l-1))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l))
  (defstrand init 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor-0)
    (l l) (x x) (beta l-0) (eta y))
  (defstrand ltx-gen 3 (ignore ignore-1) (self b)
    (priv-stor priv-stor-1) (l l-0))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor-1) (l l-0))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l-1))
  (precedes ((0 3) (3 3)) ((1 1) (0 0)) ((1 1) (6 0)) ((2 1) (3 0))
    ((2 2) (0 1)) ((3 2) (0 2)) ((3 4) (0 4)) ((4 1) (5 0))
    ((4 2) (3 1)) ((5 2) (0 2)) ((6 2) (0 2)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig na nb l l-0 l-1)
  (uniq-gen y x)
  (absent (y (mul x l-0 (rec l-1))) (y l) (y l-1) (x l) (x l-0))
  (gen-st (pv a l) (pv b l-0) (pv b l-1))
  (facts (neq b a) (neq a b) (undisclosed l))
  (leads-to ((1 1) (0 0)) ((1 1) (6 0)) ((2 1) (3 0)) ((4 1) (5 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (6 0))
  (strand-map 0 1 2 3 4 5 7)
  (traces
    ((load priv-stor (cat pt (pv b l-1)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) (mul x l-0 (rec l-1)))))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l-0))))))
      (recv nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv b l-1))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l)))
      (send
        (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor-0 (cat pt-2 (pv a l)))
      (recv
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l-0))))))
      (send nb))
    ((load priv-stor-1 (cat pt-3 ignore-1))
      (stor priv-stor-1 (cat pt-4 (pv b l-0)))
      (send
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-1 (cat pt-4 (pv b l-0)))
      (stor priv-stor-1 (cat pt-5 "nil")) (send l-0))
    ((load priv-stor (cat pt (pv b l-1)))
      (stor priv-stor (cat pt-6 "nil")) (send l-1)))
  (label 5429)
  (parent 5389)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-1) (l-peer l) (y y) (chi (mul x l-0 (rec l-1)))
        (na na) (nb nb) (priv-stor priv-stor))))
  (origs (pt-6 (6 1)) (pt-5 (5 1)) (l-0 (4 1)) (pt-4 (4 1)) (l (2 1))
    (pt-2 (2 1)) (na (3 2)) (l-1 (1 1)) (pt (1 1)) (nb (0 3)))
  (ugens (x (3 2)) (y (0 3))))

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
  (vars (na nb data) (a b name) (pt pval) (priv-stor locn)
    (l l-peer y rndx) (chi expt))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (y y) (alpha l-peer) (chi chi))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig nb)
  (uniq-gen y)
  (absent (y l) (y l-peer) (y chi))
  (facts (neq a b) (ltx-gen-once b) (undisclosed l-peer))
  (traces
    ((load priv-stor (cat pt (pv b l)))
      (recv
        (sig (body a (exp (gen) l-peer) (pubk "sig" a))
          (privk "sig" a))) (recv (cat na a b (exp (gen) chi)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul l-peer y)) (exp (gen) (mul l chi))))))
      (recv nb)))
  (label 5430)
  (unrealized (0 1))
  (origs (nb (0 3)))
  (ugens (y (0 3)))
  (comment "Not closed under rules"))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn)
    (y x l l-0 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor-0)
    (l l-0) (y y) (alpha l) (chi x))
  (defstrand ltx-gen 3 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand init 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (x x) (beta l-0) (eta y))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l-0))
  (precedes ((0 3) (2 3)) ((1 1) (2 0)) ((1 2) (0 1)) ((2 2) (0 2))
    ((2 4) (0 4)) ((3 1) (0 0)) ((3 2) (2 1)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig na nb l l-0)
  (uniq-gen y x)
  (absent (y x) (y l) (y l-0) (x l) (x l-0))
  (gen-st (pv a l) (pv b l-0))
  (facts (neq b a) (neq a b) (ltx-gen-once b) (undisclosed l))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation encryption-test (displaced 1 4 ltx-gen 3)
    (sig (body b (exp (gen) l-1) (pubk "sig" b)) (privk "sig" b)) (3 1))
  (strand-map 0 3 1 2)
  (traces
    ((load priv-stor-0 (cat pt-2 (pv b l-0)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l-0))))))
      (recv nb))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv a l)))
      (send
        (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor (cat pt-0 (pv a l)))
      (recv
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l-0))))))
      (send nb))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l-0)))
      (send
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b)))))
  (label 5439)
  (parent 5430)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-0) (l-peer l) (y y) (chi x) (na na) (nb nb)
        (priv-stor priv-stor-0))))
  (origs (l-0 (3 1)) (pt-2 (3 1)) (l (1 1)) (pt-0 (1 1)) (na (2 2))
    (nb (0 3)))
  (ugens (x (2 2)) (y (0 3))))

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
  (vars (na nb data) (a b name) (pt pval) (priv-stor locn)
    (l l-peer y rndx) (chi expt))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (y y) (alpha l-peer) (chi chi))
  (non-orig (privk "sig" a) (privk "sig" b))
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
            (hash (exp (gen) (mul l-peer y)) (exp (gen) (mul l chi))))))
      (recv nb)))
  (label 5449)
  (unrealized (0 1))
  (origs (nb (0 3)))
  (ugens (y (0 3)))
  (comment "Not closed under rules"))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn)
    (y x l l-0 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor-0)
    (l l-0) (y y) (alpha l) (chi x))
  (defstrand ltx-gen 3 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand init 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (x x) (beta l-0) (eta y))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l-0))
  (precedes ((0 3) (2 3)) ((1 1) (2 0)) ((1 2) (0 1)) ((2 2) (0 2))
    ((2 4) (0 4)) ((3 1) (0 0)) ((3 2) (2 1)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig na nb l l-0)
  (uniq-gen y x)
  (absent (y x) (y l) (y l-0) (x l) (x l-0))
  (gen-st (pv a l) (pv b l-0))
  (facts (neq b a) (neq a b) (undisclosed l-0))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation encryption-test (displaced 1 4 ltx-gen 3)
    (sig (body b (exp (gen) l-1) (pubk "sig" b)) (privk "sig" b)) (3 1))
  (strand-map 0 3 1 2)
  (traces
    ((load priv-stor-0 (cat pt-2 (pv b l-0)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l-0))))))
      (recv nb))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv a l)))
      (send
        (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor (cat pt-0 (pv a l)))
      (recv
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l-0))))))
      (send nb))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l-0)))
      (send
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b)))))
  (label 5458)
  (parent 5449)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-0) (l-peer l) (y y) (chi x) (na na) (nb nb)
        (priv-stor priv-stor-0))))
  (origs (l-0 (3 1)) (pt-2 (3 1)) (l (1 1)) (pt-0 (1 1)) (na (2 2))
    (nb (0 3)))
  (ugens (x (2 2)) (y (0 3))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a self name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (y l l-0 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b self)
    (priv-stor priv-stor-0) (l l-0) (y y) (alpha l) (chi (one)))
  (defstrand ltx-gen 3 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l-0))
  (precedes ((1 1) (2 0)) ((1 2) (0 1)) ((2 2) (0 4)) ((3 1) (0 0))
    ((3 2) (0 4)))
  (non-orig (privk "sig" a) (privk "sig" self))
  (uniq-orig nb l l-0)
  (uniq-gen y)
  (absent (y (one)) (y l) (y l-0))
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
      (recv (cat na a self (gen)))
      (send
        (cat (exp (gen) y)
          (enc na nb a self
            (hash (exp (gen) (mul y l)) (exp (gen) l-0))))) (recv nb))
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
  (label 5586)
  (parent 5449)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b self) (l l-0) (l-peer l) (y y) (chi (one)) (na na)
        (nb nb) (priv-stor priv-stor-0))))
  (origs (l-0 (3 1)) (pt-3 (3 1)) (pt-1 (2 1)) (l (1 1)) (pt-0 (1 1))
    (nb (0 3)))
  (ugens (y (0 3))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a self name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (y l rndx) (w expt) (l-0 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b self)
    (priv-stor priv-stor-0) (l l-0) (y y) (alpha l) (chi w))
  (defstrand ltx-gen 3 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l-0))
  (precedes ((1 1) (2 0)) ((1 2) (0 1)) ((2 2) (0 4)) ((3 1) (0 0))
    ((3 2) (0 4)))
  (non-orig (privk "sig" a) (privk "sig" self))
  (uniq-orig nb l l-0)
  (uniq-gen y)
  (absent (y l) (y w) (y l-0))
  (gen-st (pv a l) (pv self l-0))
  (facts (neq self a) (neq a self) (undisclosed l-0))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-init-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (3 0))
  (strand-map 0 1 2 4)
  (traces
    ((load priv-stor-0 (cat pt-3 (pv self l-0)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a self (exp (gen) w)))
      (send
        (cat (exp (gen) y)
          (enc na nb a self
            (hash (exp (gen) (mul y l)) (exp (gen) (mul w l-0))))))
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
  (label 6084)
  (parent 5449)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b self) (l l-0) (l-peer l) (y y) (chi w) (na na) (nb nb)
        (priv-stor priv-stor-0))))
  (origs (l-0 (3 1)) (pt-3 (3 1)) (pt-1 (2 1)) (l (1 1)) (pt-0 (1 1))
    (nb (0 3)))
  (ugens (y (0 3))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (y x l l-0 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor-0)
    (l l) (y y) (alpha l-0) (chi x))
  (defstrand ltx-gen 3 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l-0))
  (precedes ((1 1) (3 0)) ((1 2) (0 1)) ((2 1) (0 0)) ((2 2) (0 4))
    ((3 2) (0 4)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig nb l l-0)
  (uniq-gen y)
  (absent (y x) (y l) (y l-0))
  (gen-st (pv a l-0) (pv b l))
  (facts (neq b a) (neq a b) (undisclosed l))
  (leads-to ((1 1) (3 0)) ((2 1) (0 0)))
  (rule fact-init-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization weakened ((2 2) (0 2)))
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor-0 (cat pt-2 (pv b l)))
      (recv
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l-0)) (exp (gen) (mul x l))))))
      (recv nb))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv a l-0)))
      (send
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt-0 (pv a l-0)))
      (stor priv-stor (cat pt-3 "nil")) (send l-0)))
  (label 7339)
  (parent 5449)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l) (l-peer l-0) (y y) (chi x) (na na) (nb nb)
        (priv-stor priv-stor-0))))
  (origs (pt-3 (3 1)) (l (2 1)) (pt-2 (2 1)) (l-0 (1 1)) (pt-0 (1 1))
    (nb (0 3)))
  (ugens (y (0 3))))

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
  (vars (na nb data) (a b name) (pt pval) (priv-stor locn)
    (l l-peer y rndx) (chi expt))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (y y) (alpha l-peer) (chi chi))
  (non-orig (privk "sig" a) (privk "sig" b))
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
            (hash (exp (gen) (mul l-peer y)) (exp (gen) (mul l chi))))))
      (recv nb)))
  (label 7340)
  (unrealized (0 1))
  (origs (nb (0 3)))
  (ugens (y (0 3)))
  (comment "Not closed under rules"))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn)
    (y x l l-0 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor-0)
    (l l-0) (y y) (alpha l) (chi x))
  (defstrand ltx-gen 3 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand init 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (x x) (beta l-0) (eta y))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l-0))
  (precedes ((0 3) (2 3)) ((1 1) (2 0)) ((1 2) (0 1)) ((2 2) (0 2))
    ((2 4) (0 4)) ((3 1) (0 0)) ((3 2) (2 1)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig na nb l l-0)
  (uniq-gen y x)
  (absent (y x) (y l) (y l-0) (x l) (x l-0))
  (gen-st (pv a l) (pv b l-0))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-resp-neq0 trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation encryption-test (displaced 1 4 ltx-gen 3)
    (sig (body b (exp (gen) l-1) (pubk "sig" b)) (privk "sig" b)) (3 1))
  (strand-map 0 3 1 2)
  (traces
    ((load priv-stor-0 (cat pt-2 (pv b l-0)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l-0))))))
      (recv nb))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv a l)))
      (send
        (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor (cat pt-0 (pv a l)))
      (recv
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l-0))))))
      (send nb))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l-0)))
      (send
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b)))))
  (label 7349)
  (parent 7340)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-0) (l-peer l) (y y) (chi x) (na na) (nb nb)
        (priv-stor priv-stor-0))))
  (origs (l-0 (3 1)) (pt-2 (3 1)) (l (1 1)) (pt-0 (1 1)) (na (2 2))
    (nb (0 3)))
  (ugens (x (2 2)) (y (0 3))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a self name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (y l l-0 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b self)
    (priv-stor priv-stor-0) (l l-0) (y y) (alpha l) (chi (one)))
  (defstrand ltx-gen 3 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l-0))
  (precedes ((1 1) (2 0)) ((1 2) (0 1)) ((2 2) (0 4)) ((3 1) (0 0))
    ((3 2) (0 4)))
  (non-orig (privk "sig" a) (privk "sig" self))
  (uniq-orig nb l l-0)
  (uniq-gen y)
  (absent (y (one)) (y l) (y l-0))
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
      (recv (cat na a self (gen)))
      (send
        (cat (exp (gen) y)
          (enc na nb a self
            (hash (exp (gen) (mul y l)) (exp (gen) l-0))))) (recv nb))
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
  (label 7494)
  (parent 7340)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b self) (l l-0) (l-peer l) (y y) (chi (one)) (na na)
        (nb nb) (priv-stor priv-stor-0))))
  (origs (l-0 (3 1)) (pt-3 (3 1)) (pt-1 (2 1)) (l (1 1)) (pt-0 (1 1))
    (nb (0 3)))
  (ugens (y (0 3))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 ignore-1 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pt-6 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (y x l l-0 l-1 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-1) (y y) (alpha l) (chi (mul x l-0 (rec l-1))))
  (defstrand ltx-gen 2 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l-1))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l))
  (defstrand init 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor-0)
    (l l) (x x) (beta l-0) (eta y))
  (defstrand ltx-gen 3 (ignore ignore-1) (self b)
    (priv-stor priv-stor-1) (l l-0))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor-1) (l l-0))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l-1))
  (precedes ((0 3) (3 3)) ((1 1) (0 0)) ((1 1) (6 0)) ((2 1) (3 0))
    ((2 2) (0 1)) ((3 2) (0 2)) ((3 4) (0 4)) ((4 1) (5 0))
    ((4 2) (3 1)) ((5 2) (0 2)) ((6 2) (0 2)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig na nb l l-0 l-1)
  (uniq-gen y x)
  (absent (y (mul x l-0 (rec l-1))) (y l) (y l-1) (x l) (x l-0))
  (gen-st (pv a l) (pv b l-0) (pv b l-1))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (0 0)) ((1 1) (6 0)) ((2 1) (3 0)) ((4 1) (5 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (6 0))
  (strand-map 0 1 2 3 4 5 7)
  (traces
    ((load priv-stor (cat pt (pv b l-1)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) (mul x l-0 (rec l-1)))))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l-0))))))
      (recv nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv b l-1))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l)))
      (send
        (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor-0 (cat pt-2 (pv a l)))
      (recv
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l-0))))))
      (send nb))
    ((load priv-stor-1 (cat pt-3 ignore-1))
      (stor priv-stor-1 (cat pt-4 (pv b l-0)))
      (send
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-1 (cat pt-4 (pv b l-0)))
      (stor priv-stor-1 (cat pt-5 "nil")) (send l-0))
    ((load priv-stor (cat pt (pv b l-1)))
      (stor priv-stor (cat pt-6 "nil")) (send l-1)))
  (label 7592)
  (parent 7340)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-1) (l-peer l) (y y) (chi (mul x l-0 (rec l-1)))
        (na na) (nb nb) (priv-stor priv-stor))))
  (origs (pt-6 (6 1)) (pt-5 (5 1)) (l-0 (4 1)) (pt-4 (4 1)) (l (2 1))
    (pt-2 (2 1)) (na (3 2)) (l-1 (1 1)) (pt (1 1)) (nb (0 3)))
  (ugens (x (3 2)) (y (0 3))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a self name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (y l rndx) (w expt) (l-0 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b self)
    (priv-stor priv-stor-0) (l l-0) (y y) (alpha l) (chi w))
  (defstrand ltx-gen 3 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l-0))
  (precedes ((1 1) (2 0)) ((1 2) (0 1)) ((2 2) (0 4)) ((3 1) (0 0))
    ((3 2) (0 4)))
  (non-orig (privk "sig" a) (privk "sig" self))
  (uniq-orig nb l l-0)
  (uniq-gen y)
  (absent (y l) (y w) (y l-0))
  (gen-st (pv a l) (pv self l-0))
  (facts (neq self a) (neq a self))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)))
  (rule fact-init-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (3 0))
  (strand-map 0 1 2 4)
  (traces
    ((load priv-stor-0 (cat pt-3 (pv self l-0)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a self (exp (gen) w)))
      (send
        (cat (exp (gen) y)
          (enc na nb a self
            (hash (exp (gen) (mul y l)) (exp (gen) (mul w l-0))))))
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
  (label 8073)
  (parent 7340)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b self) (l l-0) (l-peer l) (y y) (chi w) (na na) (nb nb)
        (priv-stor priv-stor-0))))
  (origs (l-0 (3 1)) (pt-3 (3 1)) (pt-1 (2 1)) (l (1 1)) (pt-0 (1 1))
    (nb (0 3)))
  (ugens (y (0 3))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (priv-stor priv-stor-0 locn)
    (y l l-0 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (y y) (alpha l-0) (chi (mul (rec l) l-0)))
  (defstrand ltx-gen 2 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l))
  (precedes ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)) ((2 2) (0 1))
    ((3 2) (0 4)) ((4 2) (0 2)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig nb l l-0)
  (uniq-gen y)
  (absent (y (mul (rec l) l-0)) (y l) (y l-0))
  (gen-st (pv a l-0) (pv b l))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)))
  (rule fact-init-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (4 0))
  (strand-map 0 1 2 3 5)
  (traces
    ((load priv-stor (cat pt (pv b l)))
      (recv
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) (mul (rec l) l-0))))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l-0)) (exp (gen) l-0))))) (recv nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv b l))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l-0)))
      (send
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor-0 (cat pt-2 (pv a l-0)))
      (stor priv-stor-0 (cat pt-3 "nil")) (send l-0))
    ((load priv-stor (cat pt (pv b l)))
      (stor priv-stor (cat pt-4 "nil")) (send l)))
  (label 9039)
  (parent 7340)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l) (l-peer l-0) (y y) (chi (mul (rec l) l-0))
        (na na) (nb nb) (priv-stor priv-stor))))
  (origs (l-0 (2 1)) (pt-2 (2 1)) (pt-4 (4 1)) (pt-3 (3 1)) (l (1 1))
    (pt (1 1)) (nb (0 3)))
  (ugens (y (0 3))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (priv-stor priv-stor-0 locn)
    (y l l-0 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-0) (y y) (alpha l) (chi (one)))
  (defstrand ltx-gen 2 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l-0))
  (precedes ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)) ((2 2) (0 1))
    ((3 2) (0 4)) ((4 2) (0 4)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig nb l l-0)
  (uniq-gen y)
  (absent (y (one)) (y l) (y l-0))
  (gen-st (pv a l) (pv b l-0))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)))
  (rule fact-init-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (4 0))
  (strand-map 0 1 2 3 5)
  (traces
    ((load priv-stor (cat pt (pv b l-0)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (gen)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b (hash (exp (gen) (mul y l)) (exp (gen) l-0)))))
      (recv nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv b l-0))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l)))
      (send
        (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor-0 (cat pt-2 (pv a l)))
      (stor priv-stor-0 (cat pt-3 "nil")) (send l))
    ((load priv-stor (cat pt (pv b l-0)))
      (stor priv-stor (cat pt-4 "nil")) (send l-0)))
  (label 9241)
  (parent 7340)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-0) (l-peer l) (y y) (chi (one)) (na na) (nb nb)
        (priv-stor priv-stor))))
  (origs (pt-4 (4 1)) (pt-3 (3 1)) (l (2 1)) (pt-2 (2 1)) (l-0 (1 1))
    (pt (1 1)) (nb (0 3)))
  (ugens (y (0 3))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (priv-stor priv-stor-0 locn)
    (y l l-0 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-0) (y y) (alpha l) (chi l))
  (defstrand ltx-gen 2 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l-0))
  (precedes ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)) ((2 2) (0 1))
    ((3 2) (0 4)) ((4 2) (0 4)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig nb l l-0)
  (uniq-gen y)
  (absent (y l) (y l-0))
  (gen-st (pv a l) (pv b l-0))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)))
  (rule fact-init-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (4 0))
  (strand-map 0 1 2 3 5)
  (traces
    ((load priv-stor (cat pt (pv b l-0)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) l)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul l l-0))))))
      (recv nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv b l-0))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l)))
      (send
        (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor-0 (cat pt-2 (pv a l)))
      (stor priv-stor-0 (cat pt-3 "nil")) (send l))
    ((load priv-stor (cat pt (pv b l-0)))
      (stor priv-stor (cat pt-4 "nil")) (send l-0)))
  (label 9450)
  (parent 7340)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-0) (l-peer l) (y y) (chi l) (na na) (nb nb)
        (priv-stor priv-stor))))
  (origs (pt-4 (4 1)) (l (2 1)) (pt-2 (2 1)) (pt-3 (3 1)) (l-0 (1 1))
    (pt (1 1)) (nb (0 3)))
  (ugens (y (0 3))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (priv-stor priv-stor-0 locn)
    (y l y-0 l-0 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-0) (y y) (alpha l) (chi (mul y-0 (rec l-0))))
  (defstrand ltx-gen 2 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l-0))
  (precedes ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)) ((2 2) (0 1))
    ((3 2) (0 4)) ((4 2) (0 2)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig nb l l-0)
  (uniq-gen y)
  (absent (y l) (y (mul y-0 (rec l-0))) (y l-0))
  (gen-st (pv a l) (pv b l-0))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)))
  (rule fact-init-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (4 0))
  (strand-map 0 1 2 3 5)
  (traces
    ((load priv-stor (cat pt (pv b l-0)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) (mul y-0 (rec l-0)))))
      (send
        (cat (exp (gen) y)
          (enc na nb a b (hash (exp (gen) (mul y l)) (exp (gen) y-0)))))
      (recv nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv b l-0))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l)))
      (send
        (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor-0 (cat pt-2 (pv a l)))
      (stor priv-stor-0 (cat pt-3 "nil")) (send l))
    ((load priv-stor (cat pt (pv b l-0)))
      (stor priv-stor (cat pt-4 "nil")) (send l-0)))
  (label 9481)
  (parent 7340)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-0) (l-peer l) (y y) (chi (mul y-0 (rec l-0)))
        (na na) (nb nb) (priv-stor priv-stor))))
  (origs (pt-4 (4 1)) (l-0 (1 1)) (pt (1 1)) (pt-3 (3 1)) (l (2 1))
    (pt-2 (2 1)) (nb (0 3)))
  (ugens (y (0 3))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (priv-stor priv-stor-0 locn)
    (y l l-0 l-1 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-1) (y y) (alpha l) (chi l-0))
  (defstrand ltx-gen 2 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l-1))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l-1))
  (precedes ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)) ((2 2) (0 1))
    ((3 2) (0 4)) ((4 2) (0 4)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig nb l l-1)
  (uniq-gen y)
  (absent (y l) (y l-0) (y l-1))
  (gen-st (pv a l) (pv b l-1))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)))
  (rule fact-init-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (4 0))
  (strand-map 0 1 2 3 5)
  (traces
    ((load priv-stor (cat pt (pv b l-1)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) l-0)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul l-0 l-1))))))
      (recv nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv b l-1))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l)))
      (send
        (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor-0 (cat pt-2 (pv a l)))
      (stor priv-stor-0 (cat pt-3 "nil")) (send l))
    ((load priv-stor (cat pt (pv b l-1)))
      (stor priv-stor (cat pt-4 "nil")) (send l-1)))
  (label 9542)
  (parent 7340)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-1) (l-peer l) (y y) (chi l-0) (na na) (nb nb)
        (priv-stor priv-stor))))
  (origs (pt-4 (4 1)) (pt-3 (3 1)) (l (2 1)) (pt-2 (2 1)) (l-1 (1 1))
    (pt (1 1)) (nb (0 3)))
  (ugens (y (0 3))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (y x l l-0 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor-0)
    (l l) (y y) (alpha l-0) (chi x))
  (defstrand ltx-gen 3 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l-0))
  (precedes ((1 1) (3 0)) ((1 2) (0 1)) ((2 1) (0 0)) ((2 2) (0 4))
    ((3 2) (0 4)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig nb l l-0)
  (uniq-gen y)
  (absent (y x) (y l) (y l-0))
  (gen-st (pv a l-0) (pv b l))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (3 0)) ((2 1) (0 0)))
  (rule fact-init-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization weakened ((2 2) (0 2)))
  (strand-map 0 1 2 3)
  (traces
    ((load priv-stor-0 (cat pt-2 (pv b l)))
      (recv
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l-0)) (exp (gen) (mul x l))))))
      (recv nb))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv a l-0)))
      (send
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt-0 (pv a l-0)))
      (stor priv-stor (cat pt-3 "nil")) (send l-0)))
  (label 9550)
  (parent 7340)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l) (l-peer l-0) (y y) (chi x) (na na) (nb nb)
        (priv-stor priv-stor-0))))
  (origs (pt-3 (3 1)) (l (2 1)) (pt-2 (2 1)) (l-0 (1 1)) (pt-0 (1 1))
    (nb (0 3)))
  (ugens (y (0 3))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (priv-stor priv-stor-0 locn)
    (y l l-0 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-0) (y y) (alpha l) (chi (rec l-0)))
  (defstrand ltx-gen 2 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l-0))
  (precedes ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)) ((2 2) (0 1))
    ((3 2) (0 4)) ((4 2) (0 2)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig nb l l-0)
  (uniq-gen y)
  (absent (y l) (y (rec l-0)) (y l-0))
  (gen-st (pv a l) (pv b l-0))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)))
  (rule fact-init-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (4 0))
  (strand-map 0 1 2 3 5)
  (traces
    ((load priv-stor (cat pt (pv b l-0)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) (rec l-0))))
      (send
        (cat (exp (gen) y)
          (enc na nb a b (hash (exp (gen) (mul y l)) (gen)))))
      (recv nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv b l-0))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l)))
      (send
        (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor-0 (cat pt-2 (pv a l)))
      (stor priv-stor-0 (cat pt-3 "nil")) (send l))
    ((load priv-stor (cat pt (pv b l-0)))
      (stor priv-stor (cat pt-4 "nil")) (send l-0)))
  (label 9555)
  (parent 7340)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-0) (l-peer l) (y y) (chi (rec l-0)) (na na)
        (nb nb) (priv-stor priv-stor))))
  (origs (pt-4 (4 1)) (pt-3 (3 1)) (l (2 1)) (pt-2 (2 1)) (l-0 (1 1))
    (pt (1 1)) (nb (0 3)))
  (ugens (y (0 3))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a self name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (priv-stor priv-stor-0 locn)
    (y l l-0 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b self)
    (priv-stor priv-stor-0) (l l-0) (y y) (alpha l) (chi l-0))
  (defstrand ltx-gen 3 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor-0) (l l-0))
  (precedes ((1 1) (2 0)) ((1 2) (0 1)) ((2 2) (0 4)) ((3 1) (0 0))
    ((3 1) (4 0)) ((3 2) (0 2)) ((4 2) (0 4)))
  (non-orig (privk "sig" a) (privk "sig" self))
  (uniq-orig nb l l-0)
  (uniq-gen y)
  (absent (y l) (y l-0))
  (gen-st (pv a l) (pv self l-0))
  (facts (neq self a) (neq a self))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)) ((3 1) (4 0)))
  (rule fact-init-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (4 0))
  (strand-map 0 1 2 3 5)
  (traces
    ((load priv-stor-0 (cat pt-3 (pv self l-0)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a self (exp (gen) l-0)))
      (send
        (cat (exp (gen) y)
          (enc na nb a self
            (hash (exp (gen) (mul y l)) (exp (gen) (mul l-0 l-0))))))
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
          (privk "sig" self))))
    ((load priv-stor-0 (cat pt-3 (pv self l-0)))
      (stor priv-stor-0 (cat pt-4 "nil")) (send l-0)))
  (label 9576)
  (parent 7340)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b self) (l l-0) (l-peer l) (y y) (chi l-0) (na na) (nb nb)
        (priv-stor priv-stor-0))))
  (origs (pt-4 (4 1)) (l-0 (3 1)) (pt-3 (3 1)) (pt-1 (2 1)) (l (1 1))
    (pt-0 (1 1)) (nb (0 3)))
  (ugens (y (0 3))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 ignore-1 mesg) (na nb data) (a b self name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pt-6 pt-7 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (y l l-0 l-1 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-0) (y y) (alpha l) (chi (mul (rec l-0) l-1)))
  (defstrand ltx-gen 2 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor-0) (l l))
  (defstrand ltx-gen 2 (ignore ignore-1) (self self)
    (priv-stor priv-stor-1) (l l-1))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l-0))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor-1) (l l-1))
  (precedes ((1 1) (0 0)) ((1 1) (5 0)) ((2 1) (3 0)) ((2 2) (0 1))
    ((3 2) (0 4)) ((4 1) (6 0)) ((5 2) (0 2)) ((6 2) (0 2)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig nb l l-0 l-1)
  (uniq-gen y)
  (absent (y l) (y (mul (rec l-0) l-1)) (y l-0))
  (precur (5 0))
  (gen-st (pv a l) (pv b l-0) (pv self l-1))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (0 0)) ((1 1) (5 0)) ((2 1) (3 0)) ((4 1) (6 0)))
  (rule fact-init-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (6 0))
  (strand-map 0 1 2 3 4 5 7)
  (traces
    ((load priv-stor (cat pt (pv b l-0)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) (mul (rec l-0) l-1))))
      (send
        (cat (exp (gen) y)
          (enc na nb a b (hash (exp (gen) (mul y l)) (exp (gen) l-1)))))
      (recv nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv b l-0))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l)))
      (send
        (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor-0 (cat pt-2 (pv a l)))
      (stor priv-stor-0 (cat pt-3 "nil")) (send l))
    ((load priv-stor-1 (cat pt-4 ignore-1))
      (stor priv-stor-1 (cat pt-5 (pv self l-1))))
    ((load priv-stor (cat pt (pv b l-0)))
      (stor priv-stor (cat pt-6 "nil")) (send l-0))
    ((load priv-stor-1 (cat pt-5 (pv self l-1)))
      (stor priv-stor-1 (cat pt-7 "nil")) (send l-1)))
  (label 9679)
  (parent 7340)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-0) (l-peer l) (y y) (chi (mul (rec l-0) l-1))
        (na na) (nb nb) (priv-stor priv-stor))))
  (origs (pt-7 (6 1)) (pt-6 (5 1)) (l-1 (4 1)) (pt-5 (4 1)) (pt-3 (3 1))
    (l (2 1)) (pt-2 (2 1)) (l-0 (1 1)) (pt (1 1)) (nb (0 3)))
  (ugens (y (0 3))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (priv-stor priv-stor-0 locn)
    (y l rndx) (w expt) (l-0 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-0) (y y) (alpha l) (chi w))
  (defstrand ltx-gen 2 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l-0))
  (precedes ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)) ((2 2) (0 1))
    ((3 2) (0 4)) ((4 2) (0 4)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig nb l l-0)
  (uniq-gen y)
  (absent (y l) (y w) (y l-0))
  (gen-st (pv a l) (pv b l-0))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)))
  (rule fact-init-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (4 0))
  (strand-map 0 1 2 3 5)
  (traces
    ((load priv-stor (cat pt (pv b l-0)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) w)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul w l-0))))))
      (recv nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv b l-0))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l)))
      (send
        (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor-0 (cat pt-2 (pv a l)))
      (stor priv-stor-0 (cat pt-3 "nil")) (send l))
    ((load priv-stor (cat pt (pv b l-0)))
      (stor priv-stor (cat pt-4 "nil")) (send l-0)))
  (label 9693)
  (parent 7340)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-0) (l-peer l) (y y) (chi w) (na na) (nb nb)
        (priv-stor priv-stor))))
  (origs (pt-4 (4 1)) (pt-3 (3 1)) (l (2 1)) (pt-2 (2 1)) (l-0 (1 1))
    (pt (1 1)) (nb (0 3)))
  (ugens (y (0 3))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a self name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (priv-stor priv-stor-0 locn)
    (y l rndx) (w expt) (l-0 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b self)
    (priv-stor priv-stor-0) (l l-0) (y y) (alpha l) (chi (mul w l-0)))
  (defstrand ltx-gen 3 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor-0) (l l-0))
  (precedes ((1 1) (2 0)) ((1 2) (0 1)) ((2 2) (0 4)) ((3 1) (0 0))
    ((3 1) (4 0)) ((3 2) (0 2)) ((4 2) (0 4)))
  (non-orig (privk "sig" a) (privk "sig" self))
  (uniq-orig nb l l-0)
  (uniq-gen y)
  (absent (y l) (y (mul w l-0)) (y l-0))
  (gen-st (pv a l) (pv self l-0))
  (facts (neq self a) (neq a self))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)) ((3 1) (4 0)))
  (rule fact-init-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (4 0))
  (strand-map 0 1 2 3 5)
  (traces
    ((load priv-stor-0 (cat pt-3 (pv self l-0)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a self (exp (gen) (mul w l-0))))
      (send
        (cat (exp (gen) y)
          (enc na nb a self
            (hash (exp (gen) (mul y l)) (exp (gen) (mul w l-0 l-0))))))
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
          (privk "sig" self))))
    ((load priv-stor-0 (cat pt-3 (pv self l-0)))
      (stor priv-stor-0 (cat pt-4 "nil")) (send l-0)))
  (label 9696)
  (parent 7340)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b self) (l l-0) (l-peer l) (y y) (chi (mul w l-0)) (na na)
        (nb nb) (priv-stor priv-stor-0))))
  (origs (pt-4 (4 1)) (l-0 (3 1)) (pt-3 (3 1)) (pt-1 (2 1)) (l (1 1))
    (pt-0 (1 1)) (nb (0 3)))
  (ugens (y (0 3))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (priv-stor priv-stor-0 locn)
    (y l rndx) (w expt) (l-0 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-0) (y y) (alpha l) (chi (mul w (rec l-0))))
  (defstrand ltx-gen 2 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l-0))
  (precedes ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)) ((2 2) (0 1))
    ((3 2) (0 4)) ((4 2) (0 2)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig nb l l-0)
  (uniq-gen y)
  (absent (y l) (y (mul w (rec l-0))) (y l-0) (l-0 w))
  (gen-st (pv a l) (pv b l-0))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)))
  (rule fact-init-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (4 0))
  (strand-map 0 1 2 3 5)
  (traces
    ((load priv-stor (cat pt (pv b l-0)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) (mul w (rec l-0)))))
      (send
        (cat (exp (gen) y)
          (enc na nb a b (hash (exp (gen) (mul y l)) (exp (gen) w)))))
      (recv nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv b l-0))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l)))
      (send
        (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor-0 (cat pt-2 (pv a l)))
      (stor priv-stor-0 (cat pt-3 "nil")) (send l))
    ((load priv-stor (cat pt (pv b l-0)))
      (stor priv-stor (cat pt-4 "nil")) (send l-0)))
  (label 9724)
  (parent 7340)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-0) (l-peer l) (y y) (chi (mul w (rec l-0)))
        (na na) (nb nb) (priv-stor priv-stor))))
  (origs (pt-4 (4 1)) (pt-3 (3 1)) (l (2 1)) (pt-2 (2 1)) (l-0 (1 1))
    (pt (1 1)) (nb (0 3)))
  (ugens (y (0 3))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (priv-stor priv-stor-0 locn)
    (y rndx) (w expt) (l l-0 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-0) (y y) (alpha l) (chi (mul w l (rec l-0))))
  (defstrand ltx-gen 2 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l-0))
  (precedes ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)) ((2 2) (0 1))
    ((3 2) (0 4)) ((4 2) (0 2)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig nb l l-0)
  (uniq-gen y)
  (absent (y (mul w l (rec l-0))) (y l) (y l-0) (l-0 w))
  (gen-st (pv a l) (pv b l-0))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)))
  (rule fact-init-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (4 0))
  (strand-map 0 1 2 3 5)
  (traces
    ((load priv-stor (cat pt (pv b l-0)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) (mul w l (rec l-0)))))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul w l))))))
      (recv nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv b l-0))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l)))
      (send
        (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor-0 (cat pt-2 (pv a l)))
      (stor priv-stor-0 (cat pt-3 "nil")) (send l))
    ((load priv-stor (cat pt (pv b l-0)))
      (stor priv-stor (cat pt-4 "nil")) (send l-0)))
  (label 9732)
  (parent 7340)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-0) (l-peer l) (y y) (chi (mul w l (rec l-0)))
        (na na) (nb nb) (priv-stor priv-stor))))
  (origs (pt-4 (4 1)) (l (2 1)) (pt-2 (2 1)) (pt-3 (3 1)) (l-0 (1 1))
    (pt (1 1)) (nb (0 3)))
  (ugens (y (0 3))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 ignore-1 mesg) (na nb data) (a b self name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pt-6 pt-7 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (y l l-0 l-1 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-1) (y y) (alpha l) (chi l-0))
  (defstrand ltx-gen 2 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l-1))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor-0) (l l))
  (defstrand ltx-gen 2 (ignore ignore-1) (self self)
    (priv-stor priv-stor-1) (l l-0))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor-1) (l l-0))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l-1))
  (precedes ((1 1) (0 0)) ((1 1) (6 0)) ((2 1) (3 0)) ((2 2) (0 1))
    ((3 2) (0 4)) ((4 1) (5 0)) ((5 2) (0 2)) ((6 2) (0 4)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig nb l l-0 l-1)
  (uniq-gen y)
  (absent (y l) (y l-0) (y l-1))
  (precur (4 0))
  (gen-st (pv a l) (pv b l-1) (pv self l-0))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (0 0)) ((1 1) (6 0)) ((2 1) (3 0)) ((4 1) (5 0)))
  (rule fact-init-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (5 0))
  (strand-map 0 1 2 3 4 6 7)
  (traces
    ((load priv-stor (cat pt (pv b l-1)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) l-0)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul l-0 l-1))))))
      (recv nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv b l-1))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l)))
      (send
        (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor-0 (cat pt-2 (pv a l)))
      (stor priv-stor-0 (cat pt-3 "nil")) (send l))
    ((load priv-stor-1 (cat pt-4 ignore-1))
      (stor priv-stor-1 (cat pt-5 (pv self l-0))))
    ((load priv-stor-1 (cat pt-5 (pv self l-0)))
      (stor priv-stor-1 (cat pt-6 "nil")) (send l-0))
    ((load priv-stor (cat pt (pv b l-1)))
      (stor priv-stor (cat pt-7 "nil")) (send l-1)))
  (label 9733)
  (parent 7340)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-1) (l-peer l) (y y) (chi l-0) (na na) (nb nb)
        (priv-stor priv-stor))))
  (origs (pt-7 (6 1)) (pt-6 (5 1)) (l-1 (1 1)) (pt (1 1)) (l-0 (4 1))
    (pt-5 (4 1)) (pt-3 (3 1)) (l (2 1)) (pt-2 (2 1)) (nb (0 3)))
  (ugens (y (0 3))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 ignore-1 mesg) (na nb data) (a b self name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pt-6 pt-7 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (y l l-0 l-1 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-1) (y y) (alpha l) (chi l-0))
  (defstrand ltx-gen 2 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l-1))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor-0) (l l))
  (defstrand ltx-gen 2 (ignore ignore-1) (self self)
    (priv-stor priv-stor-1) (l l-0))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor-1) (l l-0))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l-1))
  (precedes ((1 1) (0 0)) ((1 1) (6 0)) ((2 1) (3 0)) ((2 2) (0 1))
    ((3 2) (0 4)) ((4 1) (5 0)) ((5 2) (0 2)) ((6 2) (0 4)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig nb l l-0 l-1)
  (uniq-gen y)
  (absent (y l) (y l-0) (y l-1) (l-0 l-1))
  (precur (4 0))
  (gen-st (pv a l) (pv b l-1) (pv self l-0))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (0 0)) ((1 1) (6 0)) ((2 1) (3 0)) ((4 1) (5 0)))
  (rule fact-init-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (5 0))
  (strand-map 0 1 2 3 4 6 7)
  (traces
    ((load priv-stor (cat pt (pv b l-1)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) l-0)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul l-0 l-1))))))
      (recv nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv b l-1))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l)))
      (send
        (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor-0 (cat pt-2 (pv a l)))
      (stor priv-stor-0 (cat pt-3 "nil")) (send l))
    ((load priv-stor-1 (cat pt-4 ignore-1))
      (stor priv-stor-1 (cat pt-5 (pv self l-0))))
    ((load priv-stor-1 (cat pt-5 (pv self l-0)))
      (stor priv-stor-1 (cat pt-6 "nil")) (send l-0))
    ((load priv-stor (cat pt (pv b l-1)))
      (stor priv-stor (cat pt-7 "nil")) (send l-1)))
  (label 9747)
  (parent 7340)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-1) (l-peer l) (y y) (chi l-0) (na na) (nb nb)
        (priv-stor priv-stor))))
  (origs (pt-7 (6 1)) (pt-6 (5 1)) (l-0 (4 1)) (pt-5 (4 1)) (pt-3 (3 1))
    (l (2 1)) (pt-2 (2 1)) (l-1 (1 1)) (pt (1 1)) (nb (0 3)))
  (ugens (y (0 3))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (priv-stor priv-stor-0 locn)
    (y l rndx) (w expt) (l-0 l-1 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-1) (y y) (alpha l) (chi (mul w l-0 (rec l-1))))
  (defstrand ltx-gen 2 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l-1))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor-0) (l l))
  (deflistener (cat (exp (gen) l-0) (mul w (rec l-1))))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l-1))
  (precedes ((1 1) (0 0)) ((1 1) (5 0)) ((2 1) (3 0)) ((2 2) (0 1))
    ((3 2) (0 4)) ((5 2) (0 2)) ((5 2) (4 0)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig nb l l-1)
  (uniq-gen y)
  (absent (y l) (y (mul w l-0 (rec l-1))) (y l-1) (l-1 w))
  (precur (4 0))
  (gen-st (pv a l) (pv b l-1))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (0 0)) ((1 1) (5 0)) ((2 1) (3 0)))
  (rule fact-init-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (5 0))
  (strand-map 0 1 2 3 4 6)
  (traces
    ((load priv-stor (cat pt (pv b l-1)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) (mul w l-0 (rec l-1)))))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul w l-0))))))
      (recv nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv b l-1))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l)))
      (send
        (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor-0 (cat pt-2 (pv a l)))
      (stor priv-stor-0 (cat pt-3 "nil")) (send l))
    ((recv (cat (exp (gen) l-0) (mul w (rec l-1)))))
    ((load priv-stor (cat pt (pv b l-1)))
      (stor priv-stor (cat pt-4 "nil")) (send l-1)))
  (label 9749)
  (parent 7340)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-1) (l-peer l) (y y) (chi (mul w l-0 (rec l-1)))
        (na na) (nb nb) (priv-stor priv-stor))))
  (origs (pt-4 (5 1)) (pt-3 (3 1)) (l (2 1)) (pt-2 (2 1)) (l-1 (1 1))
    (pt (1 1)) (nb (0 3)))
  (ugens (y (0 3))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (priv-stor priv-stor-0 locn)
    (y l l-0 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-0) (y y) (alpha l) (chi l))
  (defstrand ltx-gen 2 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l-0))
  (precedes ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)) ((2 2) (0 1))
    ((3 2) (0 4)) ((4 2) (0 4)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig nb l l-0)
  (uniq-gen y)
  (absent (y l) (y l-0) (l l-0))
  (gen-st (pv a l) (pv b l-0))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (0 0)) ((1 1) (4 0)) ((2 1) (3 0)))
  (rule fact-init-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization weakened ((3 1) (0 2)))
  (strand-map 0 1 2 3 4)
  (traces
    ((load priv-stor (cat pt (pv b l-0)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) l)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul l l-0))))))
      (recv nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv b l-0))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l)))
      (send
        (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor-0 (cat pt-2 (pv a l)))
      (stor priv-stor-0 (cat pt-3 "nil")) (send l))
    ((load priv-stor (cat pt (pv b l-0)))
      (stor priv-stor (cat pt-4 "nil")) (send l-0)))
  (label 9756)
  (parent 7340)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-0) (l-peer l) (y y) (chi l) (na na) (nb nb)
        (priv-stor priv-stor))))
  (origs (pt-4 (4 1)) (pt-3 (3 1)) (l (2 1)) (pt-2 (2 1)) (l-0 (1 1))
    (pt (1 1)) (nb (0 3)))
  (ugens (y (0 3))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a self name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (priv-stor priv-stor-0 locn)
    (y l l-0 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b self)
    (priv-stor priv-stor-0) (l l-0) (y y) (alpha l) (chi (mul l l-0)))
  (defstrand ltx-gen 3 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor-0) (l l-0))
  (precedes ((1 1) (2 0)) ((1 2) (0 1)) ((2 2) (0 2)) ((3 1) (0 0))
    ((3 1) (4 0)) ((3 2) (0 2)) ((4 2) (0 4)))
  (non-orig (privk "sig" a) (privk "sig" self))
  (uniq-orig nb l l-0)
  (uniq-gen y)
  (absent (y l) (y (mul l l-0)) (y l-0) (l (mul l-0 l-0)))
  (gen-st (pv a l) (pv self l-0))
  (facts (neq self a) (neq a self))
  (leads-to ((1 1) (2 0)) ((3 1) (0 0)) ((3 1) (4 0)))
  (rule fact-init-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (4 0))
  (strand-map 0 1 2 3 5)
  (traces
    ((load priv-stor-0 (cat pt-3 (pv self l-0)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a self (exp (gen) (mul l l-0))))
      (send
        (cat (exp (gen) y)
          (enc na nb a self
            (hash (exp (gen) (mul y l)) (exp (gen) (mul l l-0 l-0))))))
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
          (privk "sig" self))))
    ((load priv-stor-0 (cat pt-3 (pv self l-0)))
      (stor priv-stor-0 (cat pt-4 "nil")) (send l-0)))
  (label 9757)
  (parent 7340)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b self) (l l-0) (l-peer l) (y y) (chi (mul l l-0)) (na na)
        (nb nb) (priv-stor priv-stor-0))))
  (origs (pt-4 (4 1)) (pt-1 (2 1)) (l (1 1)) (pt-0 (1 1)) (l-0 (3 1))
    (pt-3 (3 1)) (nb (0 3)))
  (ugens (y (0 3))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 ignore-1 mesg) (na nb data)
    (a self self-0 name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pt-6 pt-7 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (y l l-0 l-1 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b self-0)
    (priv-stor priv-stor-1) (l l-1) (y y) (alpha l) (chi (mul l-0 l-1)))
  (defstrand ltx-gen 3 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (defstrand ltx-gen 2 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-1) (self self-0)
    (priv-stor priv-stor-1) (l l-1))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-disclose 3 (self self-0) (priv-stor priv-stor-1)
    (l l-1))
  (precedes ((1 1) (2 0)) ((1 2) (0 1)) ((2 2) (0 4)) ((3 1) (5 0))
    ((4 1) (0 0)) ((4 1) (6 0)) ((4 2) (0 2)) ((5 2) (0 2))
    ((6 2) (0 4)))
  (non-orig (privk "sig" a) (privk "sig" self-0))
  (uniq-orig nb l l-0 l-1)
  (uniq-gen y)
  (absent (y l) (y (mul l-0 l-1)) (y l-1) (l-0 (mul l-1 l-1)))
  (precur (3 0))
  (gen-st (pv a l) (pv self l-0) (pv self-0 l-1))
  (facts (neq self-0 a) (neq a self-0))
  (leads-to ((1 1) (2 0)) ((3 1) (5 0)) ((4 1) (0 0)) ((4 1) (6 0)))
  (rule fact-init-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (6 0))
  (strand-map 0 1 2 3 4 5 7)
  (traces
    ((load priv-stor-1 (cat pt-5 (pv self-0 l-1)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a self-0 (exp (gen) (mul l-0 l-1))))
      (send
        (cat (exp (gen) y)
          (enc na nb a self-0
            (hash (exp (gen) (mul y l))
              (exp (gen) (mul l-0 l-1 l-1)))))) (recv nb))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv a l)))
      (send
        (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor (cat pt-0 (pv a l)))
      (stor priv-stor (cat pt-1 "nil")) (send l))
    ((load priv-stor-0 (cat pt-2 ignore-0))
      (stor priv-stor-0 (cat pt-3 (pv self l-0))))
    ((load priv-stor-1 (cat pt-4 ignore-1))
      (stor priv-stor-1 (cat pt-5 (pv self-0 l-1)))
      (send
        (sig (body self-0 (exp (gen) l-1) (pubk "sig" self-0))
          (privk "sig" self-0))))
    ((load priv-stor-0 (cat pt-3 (pv self l-0)))
      (stor priv-stor-0 (cat pt-6 "nil")) (send l-0))
    ((load priv-stor-1 (cat pt-5 (pv self-0 l-1)))
      (stor priv-stor-1 (cat pt-7 "nil")) (send l-1)))
  (label 9762)
  (parent 7340)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b self-0) (l l-1) (l-peer l) (y y) (chi (mul l-0 l-1))
        (na na) (nb nb) (priv-stor priv-stor-1))))
  (origs (pt-7 (6 1)) (pt-6 (5 1)) (l-0 (3 1)) (pt-3 (3 1)) (l-1 (4 1))
    (pt-5 (4 1)) (pt-1 (2 1)) (l (1 1)) (pt-0 (1 1)) (nb (0 3)))
  (ugens (y (0 3))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 ignore-1 mesg) (na nb data) (a b b-0 name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pt-6 pt-7 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (y x l l-0 l-1 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l-1) (y y) (alpha l) (chi (mul x l-0 (rec l-1))))
  (defstrand ltx-gen 2 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l-1))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-gen 2 (ignore ignore-1) (self b-0)
    (priv-stor priv-stor-1) (l l-0))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self b-0) (priv-stor priv-stor-1) (l l-0))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l-1))
  (precedes ((1 1) (0 0)) ((1 1) (6 0)) ((2 1) (4 0)) ((2 2) (0 1))
    ((3 1) (5 0)) ((4 2) (0 4)) ((5 2) (0 2)) ((6 2) (0 2)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig nb l l-0 l-1)
  (uniq-gen y)
  (absent (y (mul x l-0 (rec l-1))) (y l) (y l-1))
  (gen-st (pv a l) (pv b l-0) (pv b l-1) (pv b-0 l-0))
  (facts (neq b a) (neq a b))
  (leads-to ((1 1) (0 0)) ((1 1) (6 0)) ((2 1) (4 0)) ((3 1) (5 0)))
  (rule fact-init-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization forgot (privk "sig" b-0))
  (strand-map 0 1 2 3 4 5 6)
  (traces
    ((load priv-stor (cat pt (pv b l-1)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) (mul x l-0 (rec l-1)))))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l-0))))))
      (recv nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv b l-1))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l)))
      (send
        (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor-1 (cat pt-3 ignore-1))
      (stor priv-stor-1 (cat pt-4 (pv b-0 l-0))))
    ((load priv-stor-0 (cat pt-2 (pv a l)))
      (stor priv-stor-0 (cat pt-5 "nil")) (send l))
    ((load priv-stor-1 (cat pt-4 (pv b-0 l-0)))
      (stor priv-stor-1 (cat pt-6 "nil")) (send l-0))
    ((load priv-stor (cat pt (pv b l-1)))
      (stor priv-stor (cat pt-7 "nil")) (send l-1)))
  (label 9764)
  (parent 7340)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (l l-1) (l-peer l) (y y) (chi (mul x l-0 (rec l-1)))
        (na na) (nb nb) (priv-stor priv-stor))))
  (origs (pt-7 (6 1)) (pt-6 (5 1)) (pt-5 (4 1)) (l-0 (3 1)) (pt-4 (3 1))
    (l (2 1)) (pt-2 (2 1)) (l-1 (1 1)) (pt (1 1)) (nb (0 3)))
  (ugens (y (0 3))))

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
  (vars (na nb data) (a b self self-0 name)
    (pt pt-0 pt-1 pt-2 pt-3 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (ltxa ltxb x rndx)
    (y expt))
  (defstrand init 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l ltxa) (x x) (beta ltxb) (eta y))
  (deflistener (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor-0)
    (l ltxa))
  (defstrand ltx-disclose 3 (self self-0) (priv-stor priv-stor-1)
    (l ltxb))
  (precedes ((0 4) (2 0)) ((0 4) (3 0)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig na)
  (uniq-gen x)
  (absent (x ltxa) (x ltxb))
  (facts (neq a b))
  (traces
    ((load priv-stor (cat pt (pv a ltxa)))
      (recv
        (sig (body b (exp (gen) ltxb) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))))))
      (send nb))
    ((recv (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x))))
      (send (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb x)))))
    ((load priv-stor-0 (cat pt-0 (pv self ltxa)))
      (stor priv-stor-0 (cat pt-1 "nil")) (send ltxa))
    ((load priv-stor-1 (cat pt-2 (pv self-0 ltxb)))
      (stor priv-stor-1 (cat pt-3 "nil")) (send ltxb)))
  (label 9765)
  (unrealized (0 1) (1 0))
  (preskeleton)
  (origs (pt-3 (3 1)) (pt-1 (2 1)) (na (0 2)))
  (ugens (x (0 2)))
  (comment "Not a skeleton"))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (b a name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (priv-stor priv-stor-0 locn)
    (l x y l-0 rndx))
  (defstrand init 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor-0)
    (l l-0) (x x) (beta l) (eta y))
  (deflistener (hash (exp (gen) (mul y l-0)) (exp (gen) (mul l x))))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l))
  (defstrand resp 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l l) (y y) (alpha l-0) (chi x))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l-0))
  (precedes ((0 2) (4 2)) ((0 4) (2 0)) ((0 4) (3 0)) ((2 2) (1 0))
    ((3 2) (1 0)) ((4 3) (0 3)) ((5 1) (4 0)) ((5 2) (0 1))
    ((6 1) (0 0)) ((6 2) (4 1)))
  (non-orig (privk "sig" b) (privk "sig" a))
  (uniq-orig na nb l l-0)
  (uniq-gen x y)
  (absent (x l) (x l-0) (y l) (y x) (y l-0))
  (gen-st (pv b l) (pv a l-0))
  (facts (neq b a) (neq a b))
  (leads-to ((5 1) (3 0)) ((5 1) (4 0)) ((6 1) (0 0)) ((6 1) (2 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (5 0))
  (strand-map 0 1 2 3 4 6 7)
  (traces
    ((load priv-stor-0 (cat pt-4 (pv a l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l-0)) (exp (gen) (mul l x))))))
      (send nb))
    ((recv (hash (exp (gen) (mul y l-0)) (exp (gen) (mul l x))))
      (send (hash (exp (gen) (mul y l-0)) (exp (gen) (mul l x)))))
    ((load priv-stor-0 (cat pt-4 (pv a l-0)))
      (stor priv-stor-0 (cat pt "nil")) (send l-0))
    ((load priv-stor (cat pt-2 (pv b l)))
      (stor priv-stor (cat pt-0 "nil")) (send l))
    ((load priv-stor (cat pt-2 (pv b l)))
      (recv
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul y l-0)) (exp (gen) (mul l x)))))))
    ((load priv-stor (cat pt-1 ignore))
      (stor priv-stor (cat pt-2 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-0 (cat pt-3 ignore-0))
      (stor priv-stor-0 (cat pt-4 (pv a l-0)))
      (send
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))))
  (label 10568)
  (parent 9765)
  (realized)
  (shape)
  (maps
    ((0 1 2 3)
      ((ltxa l-0) (ltxb l) (x x) (y y) (a a) (b b) (na na) (nb nb)
        (priv-stor priv-stor-0) (self a) (priv-stor-0 priv-stor-0)
        (self-0 b) (priv-stor-1 priv-stor))))
  (origs (pt (2 1)) (l-0 (6 1)) (pt-4 (6 1)) (nb (4 3)) (l (5 1))
    (pt-2 (5 1)) (pt-0 (3 1)) (na (0 2)))
  (ugens (y (4 3)) (x (0 2))))

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
  (vars (na nb data) (a b self self-0 name)
    (pt pt-0 pt-1 pt-2 pt-3 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (ltxa ltxb y rndx)
    (chi expt))
  (defstrand resp 6 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (l ltxa) (y y) (alpha ltxb) (chi chi))
  (deflistener
    (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb chi))))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor-0)
    (l ltxa))
  (defstrand ltx-disclose 3 (self self-0) (priv-stor priv-stor-1)
    (l ltxb))
  (precedes ((0 5) (2 0)) ((0 5) (3 0)))
  (uniq-orig nb)
  (uniq-gen y)
  (absent (y ltxa) (y ltxb) (y chi))
  (facts (neq a b))
  (traces
    ((load priv-stor (cat pt (pv b ltxa)))
      (recv
        (sig (body a (exp (gen) ltxb) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) chi)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul ltxb y))
              (exp (gen) (mul ltxa chi)))))) (recv nb) (send "done"))
    ((recv (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb chi))))
      (send (hash (exp (gen) (mul ltxa y)) (exp (gen) (mul ltxb chi)))))
    ((load priv-stor-0 (cat pt-0 (pv self ltxa)))
      (stor priv-stor-0 (cat pt-1 "nil")) (send ltxa))
    ((load priv-stor-1 (cat pt-2 (pv self-0 ltxb)))
      (stor priv-stor-1 (cat pt-3 "nil")) (send ltxb)))
  (label 10589)
  (unrealized (1 0))
  (preskeleton)
  (origs (pt-3 (3 1)) (pt-1 (2 1)) (nb (0 3)))
  (ugens (y (0 3)))
  (comment "Not a skeleton"))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a self name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (priv-stor priv-stor-0 locn)
    (y l x l-0 rndx))
  (defstrand resp 6 (na na) (nb nb) (a a) (b self)
    (priv-stor priv-stor-0) (l l-0) (y y) (alpha l) (chi x))
  (deflistener (hash (exp (gen) (mul y l-0)) (exp (gen) (mul l x))))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (defstrand ltx-gen 3 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand init 5 (na na) (nb nb) (a a) (b self) (priv-stor priv-stor)
    (l l) (x x) (beta l-0) (eta y))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l-0))
  (precedes ((0 3) (5 3)) ((0 5) (2 0)) ((0 5) (3 0)) ((2 2) (1 0))
    ((3 2) (1 0)) ((4 1) (5 0)) ((4 2) (0 1)) ((5 2) (0 2))
    ((5 4) (0 4)) ((6 1) (0 0)) ((6 2) (5 1)))
  (uniq-orig na nb l l-0)
  (uniq-gen y x)
  (absent (y l) (y x) (y l-0) (x l) (x l-0))
  (gen-st (pv a l) (pv self l-0))
  (facts (neq self a) (neq a self))
  (leads-to ((4 1) (3 0)) ((4 1) (5 0)) ((6 1) (0 0)) ((6 1) (2 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (4 0))
  (strand-map 0 1 2 3 5 6 7)
  (traces
    ((load priv-stor-0 (cat pt-4 (pv self l-0)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a self (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a self
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l-0))))))
      (recv nb) (send "done"))
    ((recv (hash (exp (gen) (mul y l-0)) (exp (gen) (mul l x))))
      (send (hash (exp (gen) (mul y l-0)) (exp (gen) (mul l x)))))
    ((load priv-stor-0 (cat pt-4 (pv self l-0)))
      (stor priv-stor-0 (cat pt "nil")) (send l-0))
    ((load priv-stor (cat pt-2 (pv a l)))
      (stor priv-stor (cat pt-0 "nil")) (send l))
    ((load priv-stor (cat pt-1 ignore))
      (stor priv-stor (cat pt-2 (pv a l)))
      (send
        (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor (cat pt-2 (pv a l)))
      (recv
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self))) (send (cat na a self (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a self
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l-0))))))
      (send nb))
    ((load priv-stor-0 (cat pt-3 ignore-0))
      (stor priv-stor-0 (cat pt-4 (pv self l-0)))
      (send
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self)))))
  (label 14942)
  (parent 10589)
  (realized)
  (shape)
  (maps
    ((0 1 2 3)
      ((ltxa l-0) (ltxb l) (y y) (chi x) (a a) (b self) (na na) (nb nb)
        (priv-stor priv-stor-0) (self self) (priv-stor-0 priv-stor-0)
        (self-0 a) (priv-stor-1 priv-stor))))
  (origs (l-0 (6 1)) (pt-4 (6 1)) (na (5 2)) (pt-0 (3 1)) (l (4 1))
    (pt-2 (4 1)) (pt (2 1)) (nb (0 3)))
  (ugens (x (5 2)) (y (0 3))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a self name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (priv-stor priv-stor-0 locn)
    (y l x l-0 rndx))
  (defstrand resp 6 (na na) (nb nb) (a a) (b self)
    (priv-stor priv-stor-0) (l l-0) (y y) (alpha l) (chi x))
  (deflistener (hash (exp (gen) (mul y l-0)) (exp (gen) (mul l x))))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (defstrand ltx-gen 3 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand init 5 (na na) (nb nb) (a a) (b self) (priv-stor priv-stor)
    (l l) (x x) (beta l-0) (eta y))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l-0))
  (precedes ((0 3) (5 3)) ((0 5) (2 0)) ((0 5) (3 0)) ((2 2) (1 0))
    ((3 2) (1 0)) ((4 1) (5 0)) ((4 2) (0 1)) ((5 2) (0 2))
    ((5 4) (0 4)) ((6 1) (0 0)) ((6 2) (5 1)))
  (uniq-orig na nb l l-0)
  (uniq-gen y x)
  (absent (y l) (y x) (y l-0) (x l) (x l-0) (l-0 (one)))
  (gen-st (pv a l) (pv self l-0))
  (facts (neq self a) (neq a self))
  (leads-to ((4 1) (3 0)) ((4 1) (5 0)) ((6 1) (0 0)) ((6 1) (2 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (5 0))
  (strand-map 0 1 2 3 4 6 7)
  (traces
    ((load priv-stor-0 (cat pt-4 (pv self l-0)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a self (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a self
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l-0))))))
      (recv nb) (send "done"))
    ((recv (hash (exp (gen) (mul y l-0)) (exp (gen) (mul l x))))
      (send (hash (exp (gen) (mul y l-0)) (exp (gen) (mul l x)))))
    ((load priv-stor-0 (cat pt-4 (pv self l-0)))
      (stor priv-stor-0 (cat pt "nil")) (send l-0))
    ((load priv-stor (cat pt-2 (pv a l)))
      (stor priv-stor (cat pt-0 "nil")) (send l))
    ((load priv-stor (cat pt-1 ignore))
      (stor priv-stor (cat pt-2 (pv a l)))
      (send
        (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor (cat pt-2 (pv a l)))
      (recv
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self))) (send (cat na a self (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a self
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l-0))))))
      (send nb))
    ((load priv-stor-0 (cat pt-3 ignore-0))
      (stor priv-stor-0 (cat pt-4 (pv self l-0)))
      (send
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self)))))
  (label 15545)
  (parent 10589)
  (realized)
  (shape)
  (maps
    ((0 1 2 3)
      ((ltxa l-0) (ltxb l) (y y) (chi x) (a a) (b self) (na na) (nb nb)
        (priv-stor priv-stor-0) (self self) (priv-stor-0 priv-stor-0)
        (self-0 a) (priv-stor-1 priv-stor))))
  (origs (l-0 (6 1)) (pt-4 (6 1)) (na (5 2)) (pt-0 (3 1)) (l (4 1))
    (pt-2 (4 1)) (pt (2 1)) (nb (0 3)))
  (ugens (x (5 2)) (y (0 3))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 mesg) (na nb data) (a self name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (priv-stor priv-stor-0 locn)
    (y l x rndx) (w expt) (l-0 rndx))
  (defstrand resp 6 (na na) (nb nb) (a a) (b self)
    (priv-stor priv-stor-0) (l l-0) (y y) (alpha l) (chi (mul x w)))
  (deflistener (hash (exp (gen) (mul y l-0)) (exp (gen) (mul l x w))))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (defstrand ltx-gen 3 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand init 5 (na na) (nb nb) (a a) (b self) (priv-stor priv-stor)
    (l l) (x x) (beta (mul w l-0)) (eta y))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l-0))
  (precedes ((0 3) (5 3)) ((0 5) (2 0)) ((0 5) (3 0)) ((2 2) (1 0))
    ((3 2) (1 0)) ((4 1) (5 0)) ((4 2) (0 1)) ((5 2) (0 2))
    ((5 4) (0 4)) ((6 1) (0 0)) ((6 2) (5 1)))
  (uniq-orig na nb l l-0)
  (uniq-gen y x)
  (absent (y l) (y (mul x w)) (y l-0) (x l) (x (mul w l-0)) (l-0 w))
  (gen-st (pv a l) (pv self l-0))
  (facts (neq self a) (neq a self))
  (leads-to ((4 1) (3 0)) ((4 1) (5 0)) ((6 1) (0 0)) ((6 1) (2 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (6 0))
  (strand-map 0 1 2 3 4 5 7)
  (traces
    ((load priv-stor-0 (cat pt-4 (pv self l-0)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a self (exp (gen) (mul x w))))
      (send
        (cat (exp (gen) y)
          (enc na nb a self
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x w l-0))))))
      (recv nb) (send "done"))
    ((recv (hash (exp (gen) (mul y l-0)) (exp (gen) (mul l x w))))
      (send (hash (exp (gen) (mul y l-0)) (exp (gen) (mul l x w)))))
    ((load priv-stor-0 (cat pt-4 (pv self l-0)))
      (stor priv-stor-0 (cat pt "nil")) (send l-0))
    ((load priv-stor (cat pt-2 (pv a l)))
      (stor priv-stor (cat pt-0 "nil")) (send l))
    ((load priv-stor (cat pt-1 ignore))
      (stor priv-stor (cat pt-2 (pv a l)))
      (send
        (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor (cat pt-2 (pv a l)))
      (recv
        (sig (body self (exp (gen) (mul w l-0)) (pubk "sig" self))
          (privk "sig" self))) (send (cat na a self (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a self
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x w l-0))))))
      (send nb))
    ((load priv-stor-0 (cat pt-3 ignore-0))
      (stor priv-stor-0 (cat pt-4 (pv self l-0)))
      (send
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self)))))
  (label 15566)
  (parent 10589)
  (realized)
  (shape)
  (maps
    ((0 1 2 3)
      ((ltxa l-0) (ltxb l) (y y) (chi (mul x w)) (a a) (b self) (na na)
        (nb nb) (priv-stor priv-stor-0) (self self)
        (priv-stor-0 priv-stor-0) (self-0 a) (priv-stor-1 priv-stor))))
  (origs (l-0 (6 1)) (pt-4 (6 1)) (na (5 2)) (pt-0 (3 1)) (l (4 1))
    (pt-2 (4 1)) (pt (2 1)) (nb (0 3)))
  (ugens (x (5 2)) (y (0 3))))

(defskeleton dhcr-umx
  (vars (ignore ignore-0 ignore-1 mesg) (na nb data)
    (a self self-0 name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pt-6 pt-7 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (y l x l-0 l-1 rndx))
  (defstrand resp 6 (na na) (nb nb) (a a) (b self-0)
    (priv-stor priv-stor-1) (l l-1) (y y) (alpha l) (chi (mul x l-0)))
  (deflistener (hash (exp (gen) (mul y l-1)) (exp (gen) (mul l x l-0))))
  (defstrand ltx-disclose 3 (self self-0) (priv-stor priv-stor-1)
    (l l-1))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (defstrand ltx-gen 3 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand init 5 (na na) (nb nb) (a a) (b self-0)
    (priv-stor priv-stor) (l l) (x x) (beta (mul l-0 l-1)) (eta y))
  (defstrand ltx-gen 2 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-1) (self self-0)
    (priv-stor priv-stor-1) (l l-1))
  (precedes ((0 3) (5 3)) ((0 5) (2 0)) ((0 5) (3 0)) ((2 2) (1 0))
    ((3 2) (1 0)) ((4 1) (5 0)) ((4 2) (0 1)) ((5 2) (0 2))
    ((5 4) (0 4)) ((6 1) (7 0)) ((7 2) (5 1)) ((8 1) (0 0))
    ((8 2) (5 1)))
  (uniq-orig na nb l l-0 l-1)
  (uniq-gen y x)
  (absent (y l) (y (mul x l-0)) (y l-1) (x l) (x (mul l-0 l-1)))
  (gen-st (pv a l) (pv self l-0) (pv self-0 l-1))
  (facts (neq self-0 a) (neq a self-0))
  (leads-to ((4 1) (3 0)) ((4 1) (5 0)) ((6 1) (7 0)) ((8 1) (0 0))
    ((8 1) (2 0)))
  (rule fact-resp-neq0 trRl_ltx-disclose-at-0 trRl_ltx-disclose-at-1
    trRl_ltx-gen-at-0 trRl_ltx-gen-at-1)
  (operation generalization deleted (7 0))
  (strand-map 0 1 2 3 4 5 6 8 9)
  (traces
    ((load priv-stor-1 (cat pt-7 (pv self-0 l-1)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a self-0 (exp (gen) (mul x l-0))))
      (send
        (cat (exp (gen) y)
          (enc na nb a self-0
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l-0 l-1))))))
      (recv nb) (send "done"))
    ((recv (hash (exp (gen) (mul y l-1)) (exp (gen) (mul l x l-0))))
      (send (hash (exp (gen) (mul y l-1)) (exp (gen) (mul l x l-0)))))
    ((load priv-stor-1 (cat pt-7 (pv self-0 l-1)))
      (stor priv-stor-1 (cat pt "nil")) (send l-1))
    ((load priv-stor (cat pt-2 (pv a l)))
      (stor priv-stor (cat pt-0 "nil")) (send l))
    ((load priv-stor (cat pt-1 ignore))
      (stor priv-stor (cat pt-2 (pv a l)))
      (send
        (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor (cat pt-2 (pv a l)))
      (recv
        (sig (body self-0 (exp (gen) (mul l-0 l-1)) (pubk "sig" self-0))
          (privk "sig" self-0))) (send (cat na a self-0 (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a self-0
            (hash (exp (gen) (mul y l)) (exp (gen) (mul x l-0 l-1))))))
      (send nb))
    ((load priv-stor-0 (cat pt-3 ignore-0))
      (stor priv-stor-0 (cat pt-4 (pv self l-0))))
    ((load priv-stor-0 (cat pt-4 (pv self l-0)))
      (stor priv-stor-0 (cat pt-5 "nil")) (send l-0))
    ((load priv-stor-1 (cat pt-6 ignore-1))
      (stor priv-stor-1 (cat pt-7 (pv self-0 l-1)))
      (send
        (sig (body self-0 (exp (gen) l-1) (pubk "sig" self-0))
          (privk "sig" self-0)))))
  (label 15568)
  (parent 10589)
  (realized)
  (shape)
  (maps
    ((0 1 2 3)
      ((ltxa l-1) (ltxb l) (y y) (chi (mul x l-0)) (a a) (b self-0)
        (na na) (nb nb) (priv-stor priv-stor-1) (self self-0)
        (priv-stor-0 priv-stor-1) (self-0 a) (priv-stor-1 priv-stor))))
  (origs (l-1 (8 1)) (pt-7 (8 1)) (pt-5 (7 1)) (l-0 (6 1)) (pt-4 (6 1))
    (na (5 2)) (pt-0 (3 1)) (l (4 1)) (pt-2 (4 1)) (pt (2 1))
    (nb (0 3)))
  (ugens (x (5 2)) (y (0 3))))

(comment "Nothing left to do")
