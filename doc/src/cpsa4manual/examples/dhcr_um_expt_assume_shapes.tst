(comment "CPSA 4.3.1")
(comment "Extracted shapes")

(herald "DHCR: unified model (UM) original" (bound 20) (limit 12000)
  (algebra diffie-hellman))

(comment "CPSA 4.3.1")

(comment "All input read from dhcr_um_expt_assume.scm")

(comment "Step count limited to 12000")

(comment "Strand count bounded at 20")

(defprotocol dhcr-um diffie-hellman
  (defrole init
    (vars (la x rndx) (beta upsilon expt) (a b name) (na nb data)
      (priv-stor locn))
    (trace (load priv-stor (pv a la))
      (recv
        (sig (body b (exp (gen) beta) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) upsilon)
          (enc na nb a b
            (hash (exp (gen) (mul la beta))
              (exp (gen) (mul x upsilon)))))) (send nb))
    (uniq-orig na)
    (uniq-gen x)
    (absent (x la) (x beta))
    (assume (fact neq (exp (gen) upsilon) (gen)))
    (gen-st (pv a la)))
  (defrole resp
    (vars (lb y rndx) (alpha zeta expt) (a b name) (na nb data)
      (priv-stor locn))
    (trace (load priv-stor (pv b lb))
      (recv
        (sig (body a (exp (gen) alpha) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) zeta)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul lb alpha))
              (exp (gen) (mul y zeta)))))) (recv nb))
    (uniq-orig nb)
    (uniq-gen y)
    (absent (y lb) (y alpha) (y zeta))
    (assume (fact neq (exp (gen) zeta) (gen)))
    (gen-st (pv b lb)))
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
        (and (fact undisclosed l) (p "ltx-disclose" z 2)
          (p "ltx-disclose" "l" z l))
        (false))))
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
  (defgenrule assume-init-0
    (forall ((z strd) (upsilon expt))
      (implies (and (p "init" z 4) (p "init" "upsilon" z upsilon))
        (fact neq (exp (gen) upsilon) (gen)))))
  (defgenrule assume-resp-0
    (forall ((z strd) (zeta expt))
      (implies (and (p "resp" z 3) (p "resp" "zeta" z zeta))
        (fact neq (exp (gen) zeta) (gen)))))
  (defgenrule trRl_ltx-gen-at-1
    (forall ((z strd)) (implies (p "ltx-gen" z 2) (trans z 1))))
  (defgenrule trRl_ltx-gen-at-0
    (forall ((z strd)) (implies (p "ltx-gen" z 2) (trans z 0))))
  (defgenrule trRl_ltx-disclose-at-1
    (forall ((z strd)) (implies (p "ltx-disclose" z 2) (trans z 1))))
  (defgenrule trRl_ltx-disclose-at-0
    (forall ((z strd)) (implies (p "ltx-disclose" z 2) (trans z 0))))
  (defgenrule gen-st-init-0
    (forall ((z strd) (la rndx) (a name))
      (implies
        (and (p "init" z 1) (p "init" "la" z la) (p "init" "a" z a))
        (gen-st (pv a la)))))
  (defgenrule gen-st-resp-0
    (forall ((z strd) (lb rndx) (b name))
      (implies
        (and (p "resp" z 1) (p "resp" "lb" z lb) (p "resp" "b" z b))
        (gen-st (pv b lb)))))
  (defgenrule gen-st-ltx-disclose-0
    (forall ((z strd) (l rndx) (self name))
      (implies
        (and (p "ltx-disclose" z 1) (p "ltx-disclose" "l" z l)
          (p "ltx-disclose" "self" z self)) (gen-st (pv self l)))))
  (lang (sig sign) (body (tuple 3)) (pv (tuple 2))))

(defskeleton dhcr-um
  (vars (na nb data) (a b name) (pt pval) (priv-stor locn) (la rndx)
    (beta expt) (x rndx) (upsilon expt))
  (defstrand init 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (la la) (x x) (beta beta) (upsilon upsilon))
  (non-orig (privk "sig" b))
  (uniq-orig na)
  (uniq-gen x)
  (absent (x la) (x beta))
  (facts (neq a b) (undisclosed la) (undisclosed beta))
  (traces
    ((load priv-stor (cat pt (pv a la)))
      (recv
        (sig (body b (exp (gen) beta) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) upsilon)
          (enc na nb a b
            (hash (exp (gen) (mul la beta))
              (exp (gen) (mul x upsilon)))))) (send nb)))
  (label 0)
  (unrealized (0 1))
  (origs (na (0 2)))
  (comment "Not closed under rules"))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (b self name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn)
    (lb l x y rndx))
  (defstrand init 5 (na na) (nb nb) (a self) (b b)
    (priv-stor priv-stor-0) (la l) (x x) (beta lb) (upsilon y))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l lb))
  (defstrand resp 4 (na na) (nb nb) (a self) (b b) (priv-stor priv-stor)
    (lb lb) (y y) (alpha l) (zeta x))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l))
  (precedes ((0 2) (2 2)) ((1 1) (2 0)) ((1 2) (0 1)) ((2 3) (0 3))
    ((3 1) (0 0)) ((3 2) (2 1)))
  (non-orig (privk "sig" b))
  (uniq-orig na nb lb l)
  (uniq-gen x y)
  (absent (x lb) (x l) (y lb) (y l) (y x))
  (gen-st (pv b lb) (pv self l))
  (facts (neq (exp (gen) y) (gen)) (neq (exp (gen) x) (gen)) (trans 3 1)
    (trans 1 1) (trans 3 0) (trans 1 0) (neq self b) (undisclosed l)
    (undisclosed lb))
  (operation nonce-test (displaced 4 2 resp 4) (exp (gen) y-0) (0 3))
  (traces
    ((load priv-stor-0 (cat pt-2 (pv self l)))
      (recv
        (sig (body b (exp (gen) lb) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na self b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb self b
            (hash (exp (gen) (mul lb l)) (exp (gen) (mul x y))))))
      (send nb))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv b lb)))
      (send
        (sig (body b (exp (gen) lb) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt-0 (pv b lb)))
      (recv
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self))) (recv (cat na self b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb self b
            (hash (exp (gen) (mul lb l)) (exp (gen) (mul x y)))))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv self l)))
      (send
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self)))))
  (label 16)
  (parent 0)
  (realized)
  (shape)
  (maps
    ((0)
      ((a self) (b b) (la l) (beta lb) (x x) (upsilon y) (na na) (nb nb)
        (priv-stor priv-stor-0) (pt pt-2))))
  (origs (nb (2 3)) (l (3 1)) (pt-2 (3 1)) (lb (1 1)) (pt-0 (1 1))
    (na (0 2))))

(comment "Nothing left to do")

(defprotocol dhcr-um diffie-hellman
  (defrole init
    (vars (la x rndx) (beta upsilon expt) (a b name) (na nb data)
      (priv-stor locn))
    (trace (load priv-stor (pv a la))
      (recv
        (sig (body b (exp (gen) beta) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) upsilon)
          (enc na nb a b
            (hash (exp (gen) (mul la beta))
              (exp (gen) (mul x upsilon)))))) (send nb))
    (uniq-orig na)
    (uniq-gen x)
    (absent (x la) (x beta))
    (assume (fact neq (exp (gen) upsilon) (gen)))
    (gen-st (pv a la)))
  (defrole resp
    (vars (lb y rndx) (alpha zeta expt) (a b name) (na nb data)
      (priv-stor locn))
    (trace (load priv-stor (pv b lb))
      (recv
        (sig (body a (exp (gen) alpha) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) zeta)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul lb alpha))
              (exp (gen) (mul y zeta)))))) (recv nb))
    (uniq-orig nb)
    (uniq-gen y)
    (absent (y lb) (y alpha) (y zeta))
    (assume (fact neq (exp (gen) zeta) (gen)))
    (gen-st (pv b lb)))
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
        (and (fact undisclosed l) (p "ltx-disclose" z 2)
          (p "ltx-disclose" "l" z l))
        (false))))
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
  (defgenrule assume-init-0
    (forall ((z strd) (upsilon expt))
      (implies (and (p "init" z 4) (p "init" "upsilon" z upsilon))
        (fact neq (exp (gen) upsilon) (gen)))))
  (defgenrule assume-resp-0
    (forall ((z strd) (zeta expt))
      (implies (and (p "resp" z 3) (p "resp" "zeta" z zeta))
        (fact neq (exp (gen) zeta) (gen)))))
  (defgenrule trRl_ltx-gen-at-1
    (forall ((z strd)) (implies (p "ltx-gen" z 2) (trans z 1))))
  (defgenrule trRl_ltx-gen-at-0
    (forall ((z strd)) (implies (p "ltx-gen" z 2) (trans z 0))))
  (defgenrule trRl_ltx-disclose-at-1
    (forall ((z strd)) (implies (p "ltx-disclose" z 2) (trans z 1))))
  (defgenrule trRl_ltx-disclose-at-0
    (forall ((z strd)) (implies (p "ltx-disclose" z 2) (trans z 0))))
  (defgenrule gen-st-init-0
    (forall ((z strd) (la rndx) (a name))
      (implies
        (and (p "init" z 1) (p "init" "la" z la) (p "init" "a" z a))
        (gen-st (pv a la)))))
  (defgenrule gen-st-resp-0
    (forall ((z strd) (lb rndx) (b name))
      (implies
        (and (p "resp" z 1) (p "resp" "lb" z lb) (p "resp" "b" z b))
        (gen-st (pv b lb)))))
  (defgenrule gen-st-ltx-disclose-0
    (forall ((z strd) (l rndx) (self name))
      (implies
        (and (p "ltx-disclose" z 1) (p "ltx-disclose" "l" z l)
          (p "ltx-disclose" "self" z self)) (gen-st (pv self l)))))
  (lang (sig sign) (body (tuple 3)) (pv (tuple 2))))

(defskeleton dhcr-um
  (vars (na nb data) (a b name) (pt pval) (priv-stor locn) (la rndx)
    (beta expt) (x rndx) (upsilon expt))
  (defstrand init 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (la la) (x x) (beta beta) (upsilon upsilon))
  (non-orig (privk "sig" b))
  (uniq-orig na)
  (uniq-gen x)
  (absent (x la) (x beta))
  (facts (neq a b) (undisclosed beta))
  (traces
    ((load priv-stor (cat pt (pv a la)))
      (recv
        (sig (body b (exp (gen) beta) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) upsilon)
          (enc na nb a b
            (hash (exp (gen) (mul la beta))
              (exp (gen) (mul x upsilon)))))) (send nb)))
  (label 64)
  (unrealized (0 1))
  (origs (na (0 2)))
  (comment "Not closed under rules"))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (b self name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn)
    (lb l x y rndx))
  (defstrand init 5 (na na) (nb nb) (a self) (b b)
    (priv-stor priv-stor-0) (la l) (x x) (beta lb) (upsilon y))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l lb))
  (defstrand resp 4 (na na) (nb nb) (a self) (b b) (priv-stor priv-stor)
    (lb lb) (y y) (alpha l) (zeta x))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l))
  (precedes ((0 2) (2 2)) ((1 1) (2 0)) ((1 2) (0 1)) ((2 3) (0 3))
    ((3 1) (0 0)) ((3 2) (2 1)))
  (non-orig (privk "sig" b))
  (uniq-orig na nb lb l)
  (uniq-gen x y)
  (absent (x lb) (x l) (y lb) (y l) (y x))
  (gen-st (pv b lb) (pv self l))
  (facts (neq (exp (gen) y) (gen)) (neq (exp (gen) x) (gen)) (trans 3 1)
    (trans 1 1) (trans 3 0) (trans 1 0) (neq self b) (undisclosed lb))
  (operation nonce-test (displaced 4 2 resp 4) (exp (gen) y-0) (0 3))
  (traces
    ((load priv-stor-0 (cat pt-2 (pv self l)))
      (recv
        (sig (body b (exp (gen) lb) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na self b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb self b
            (hash (exp (gen) (mul lb l)) (exp (gen) (mul x y))))))
      (send nb))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv b lb)))
      (send
        (sig (body b (exp (gen) lb) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt-0 (pv b lb)))
      (recv
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self))) (recv (cat na self b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb self b
            (hash (exp (gen) (mul lb l)) (exp (gen) (mul x y)))))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv self l)))
      (send
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self)))))
  (label 80)
  (parent 64)
  (realized)
  (shape)
  (maps
    ((0)
      ((a self) (b b) (la l) (beta lb) (x x) (upsilon y) (na na) (nb nb)
        (priv-stor priv-stor-0) (pt pt-2))))
  (origs (nb (2 3)) (l (3 1)) (pt-2 (3 1)) (lb (1 1)) (pt-0 (1 1))
    (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn) (x rndx)
    (upsilon expt) (l l-0 rndx))
  (defstrand init 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (la l) (x x) (beta l-0) (upsilon upsilon))
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
  (facts (neq (exp (gen) upsilon) (gen)) (trans 2 1) (trans 1 1)
    (trans 2 0) (trans 1 0) (trans 3 1) (trans 3 0) (neq a b)
    (undisclosed l-0))
  (operation generalization deleted (3 0))
  (traces
    ((load priv-stor (cat pt (pv a l)))
      (recv
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) upsilon)
          (enc na nb a b
            (hash (exp (gen) (mul l l-0))
              (exp (gen) (mul x upsilon)))))) (send nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l-0)))
      (send
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt (pv a l)))
      (stor priv-stor (cat pt-3 "nil")) (send l)))
  (label 196)
  (parent 64)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (la l) (beta l-0) (x x) (upsilon upsilon) (na na)
        (nb nb) (priv-stor priv-stor) (pt pt))))
  (origs (l-0 (2 1)) (pt-2 (2 1)) (pt-3 (3 1)) (l (1 1)) (pt (1 1))
    (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (lb l x y rndx))
  (defstrand init 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (la l) (x x) (beta lb) (upsilon y))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l lb))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (precedes ((1 1) (0 0)) ((1 1) (3 0)) ((2 2) (0 1)) ((3 2) (0 3)))
  (non-orig (privk "sig" b))
  (uniq-orig na lb l)
  (uniq-gen x y)
  (absent (x lb) (x l) (y lb) (y l) (y x))
  (gen-st (pv a l) (pv b lb))
  (facts (neq (exp (gen) y) (gen)) (trans 2 1) (trans 1 1) (trans 2 0)
    (trans 1 0) (trans 3 1) (trans 3 0) (neq a b) (undisclosed lb))
  (operation generalization forgot nb)
  (traces
    ((load priv-stor (cat pt (pv a l)))
      (recv
        (sig (body b (exp (gen) lb) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul lb l)) (exp (gen) (mul x y))))))
      (send nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b lb)))
      (send
        (sig (body b (exp (gen) lb) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt (pv a l)))
      (stor priv-stor (cat pt-3 "nil")) (send l)))
  (label 198)
  (parent 64)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (la l) (beta lb) (x x) (upsilon y) (na na) (nb nb)
        (priv-stor priv-stor) (pt pt))))
  (origs (pt-3 (3 1)) (lb (2 1)) (pt-2 (2 1)) (l (1 1)) (pt (1 1))
    (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 ignore-1 mesg) (na nb data) (a b b-0 name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (l l-0 lb x y rndx))
  (defstrand init 5 (na na) (nb nb) (a a) (b b-0) (priv-stor priv-stor)
    (la l) (x x) (beta l-0) (upsilon y))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b-0)
    (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-gen 2 (ignore ignore-1) (self b)
    (priv-stor priv-stor-1) (l lb))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (precedes ((1 1) (0 0)) ((1 1) (4 0)) ((2 2) (0 1)) ((4 2) (0 3)))
  (non-orig (privk "sig" b-0))
  (uniq-orig na l l-0 lb)
  (uniq-gen x y)
  (absent (x l) (x l-0) (y (mul l l-0 (rec lb))) (y lb) (y x))
  (gen-st (pv a l) (pv b lb))
  (facts (neq (exp (gen) y) (gen)) (trans 3 1) (trans 2 1) (trans 1 1)
    (trans 3 0) (trans 2 0) (trans 1 0) (trans 4 1) (trans 4 0)
    (neq a b-0) (undisclosed l-0))
  (operation generalization forgot (privk "sig" b))
  (traces
    ((load priv-stor (cat pt (pv a l)))
      (recv
        (sig (body b-0 (exp (gen) l-0) (pubk "sig" b-0))
          (privk "sig" b-0))) (send (cat na a b-0 (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b-0
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y))))))
      (send nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b-0 l-0)))
      (send
        (sig (body b-0 (exp (gen) l-0) (pubk "sig" b-0))
          (privk "sig" b-0))))
    ((load priv-stor-1 (cat pt-4 ignore-1))
      (stor priv-stor-1 (cat pt-3 (pv b lb))))
    ((load priv-stor (cat pt (pv a l)))
      (stor priv-stor (cat pt-5 "nil")) (send l)))
  (label 329)
  (parent 64)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b-0) (la l) (beta l-0) (x x) (upsilon y) (na na) (nb nb)
        (priv-stor priv-stor) (pt pt))))
  (origs (l-0 (2 1)) (pt-2 (2 1)) (pt-5 (4 1)) (lb (3 1)) (pt-3 (3 1))
    (l (1 1)) (pt (1 1)) (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (lb l x rndx) (w expt) (y rndx))
  (defstrand init 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (la l) (x x) (beta lb) (upsilon (mul w y)))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l lb))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (deflistener (cat (exp (gen) y) w))
  (precedes ((1 1) (0 0)) ((1 1) (3 0)) ((2 2) (0 1)) ((3 2) (0 3)))
  (non-orig (privk "sig" b))
  (uniq-orig na lb l)
  (uniq-gen x y)
  (absent (x lb) (x l) (y lb) (y l) (y (mul x w)))
  (precur (4 0))
  (gen-st (pv a l) (pv b lb))
  (facts (neq (exp (gen) (mul w y)) (gen)) (trans 2 1) (trans 1 1)
    (trans 2 0) (trans 1 0) (trans 3 1) (trans 3 0) (neq a b)
    (undisclosed lb))
  (operation generalization forgot nb)
  (traces
    ((load priv-stor (cat pt (pv a l)))
      (recv
        (sig (body b (exp (gen) lb) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul w y))
          (enc na nb a b
            (hash (exp (gen) (mul lb l)) (exp (gen) (mul x w y))))))
      (send nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b lb)))
      (send
        (sig (body b (exp (gen) lb) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt (pv a l)))
      (stor priv-stor (cat pt-3 "nil")) (send l))
    ((recv (cat (exp (gen) y) w))))
  (label 331)
  (parent 64)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (la l) (beta lb) (x x) (upsilon (mul w y)) (na na)
        (nb nb) (priv-stor priv-stor) (pt pt))))
  (origs (pt-3 (3 1)) (lb (2 1)) (pt-2 (2 1)) (l (1 1)) (pt (1 1))
    (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 ignore-1 mesg) (na nb data) (a b b-0 name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (l l-0 lb x rndx) (w expt)
    (y rndx))
  (defstrand init 5 (na na) (nb nb) (a a) (b b-0) (priv-stor priv-stor)
    (la l) (x x) (beta l-0) (upsilon (mul w y)))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b-0)
    (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-gen 2 (ignore ignore-1) (self b)
    (priv-stor priv-stor-1) (l lb))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (deflistener (cat (exp (gen) y) w))
  (precedes ((1 1) (0 0)) ((1 1) (4 0)) ((2 2) (0 1)) ((4 2) (0 3)))
  (non-orig (privk "sig" b-0))
  (uniq-orig na l l-0 lb)
  (uniq-gen x y)
  (absent (x l) (x l-0) (y (mul l l-0 (rec lb))) (y lb) (y (mul x w)))
  (precur (5 0))
  (gen-st (pv a l) (pv b lb))
  (facts (neq (exp (gen) (mul w y)) (gen)) (trans 3 1) (trans 2 1)
    (trans 1 1) (trans 3 0) (trans 2 0) (trans 1 0) (trans 4 1)
    (trans 4 0) (neq a b-0) (undisclosed l-0))
  (operation generalization forgot (privk "sig" b))
  (traces
    ((load priv-stor (cat pt (pv a l)))
      (recv
        (sig (body b-0 (exp (gen) l-0) (pubk "sig" b-0))
          (privk "sig" b-0))) (send (cat na a b-0 (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul w y))
          (enc na nb a b-0
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x w y))))))
      (send nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b-0 l-0)))
      (send
        (sig (body b-0 (exp (gen) l-0) (pubk "sig" b-0))
          (privk "sig" b-0))))
    ((load priv-stor-1 (cat pt-4 ignore-1))
      (stor priv-stor-1 (cat pt-3 (pv b lb))))
    ((load priv-stor (cat pt (pv a l)))
      (stor priv-stor (cat pt-5 "nil")) (send l))
    ((recv (cat (exp (gen) y) w))))
  (label 340)
  (parent 64)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b-0) (la l) (beta l-0) (x x) (upsilon (mul w y)) (na na)
        (nb nb) (priv-stor priv-stor) (pt pt))))
  (origs (l-0 (2 1)) (pt-2 (2 1)) (pt-5 (4 1)) (lb (3 1)) (pt-3 (3 1))
    (l (1 1)) (pt (1 1)) (na (0 2))))

(comment "Nothing left to do")

(defprotocol dhcr-um diffie-hellman
  (defrole init
    (vars (la x rndx) (beta upsilon expt) (a b name) (na nb data)
      (priv-stor locn))
    (trace (load priv-stor (pv a la))
      (recv
        (sig (body b (exp (gen) beta) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) upsilon)
          (enc na nb a b
            (hash (exp (gen) (mul la beta))
              (exp (gen) (mul x upsilon)))))) (send nb))
    (uniq-orig na)
    (uniq-gen x)
    (absent (x la) (x beta))
    (assume (fact neq (exp (gen) upsilon) (gen)))
    (gen-st (pv a la)))
  (defrole resp
    (vars (lb y rndx) (alpha zeta expt) (a b name) (na nb data)
      (priv-stor locn))
    (trace (load priv-stor (pv b lb))
      (recv
        (sig (body a (exp (gen) alpha) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) zeta)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul lb alpha))
              (exp (gen) (mul y zeta)))))) (recv nb))
    (uniq-orig nb)
    (uniq-gen y)
    (absent (y lb) (y alpha) (y zeta))
    (assume (fact neq (exp (gen) zeta) (gen)))
    (gen-st (pv b lb)))
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
        (and (fact undisclosed l) (p "ltx-disclose" z 2)
          (p "ltx-disclose" "l" z l))
        (false))))
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
  (defgenrule assume-init-0
    (forall ((z strd) (upsilon expt))
      (implies (and (p "init" z 4) (p "init" "upsilon" z upsilon))
        (fact neq (exp (gen) upsilon) (gen)))))
  (defgenrule assume-resp-0
    (forall ((z strd) (zeta expt))
      (implies (and (p "resp" z 3) (p "resp" "zeta" z zeta))
        (fact neq (exp (gen) zeta) (gen)))))
  (defgenrule trRl_ltx-gen-at-1
    (forall ((z strd)) (implies (p "ltx-gen" z 2) (trans z 1))))
  (defgenrule trRl_ltx-gen-at-0
    (forall ((z strd)) (implies (p "ltx-gen" z 2) (trans z 0))))
  (defgenrule trRl_ltx-disclose-at-1
    (forall ((z strd)) (implies (p "ltx-disclose" z 2) (trans z 1))))
  (defgenrule trRl_ltx-disclose-at-0
    (forall ((z strd)) (implies (p "ltx-disclose" z 2) (trans z 0))))
  (defgenrule gen-st-init-0
    (forall ((z strd) (la rndx) (a name))
      (implies
        (and (p "init" z 1) (p "init" "la" z la) (p "init" "a" z a))
        (gen-st (pv a la)))))
  (defgenrule gen-st-resp-0
    (forall ((z strd) (lb rndx) (b name))
      (implies
        (and (p "resp" z 1) (p "resp" "lb" z lb) (p "resp" "b" z b))
        (gen-st (pv b lb)))))
  (defgenrule gen-st-ltx-disclose-0
    (forall ((z strd) (l rndx) (self name))
      (implies
        (and (p "ltx-disclose" z 1) (p "ltx-disclose" "l" z l)
          (p "ltx-disclose" "self" z self)) (gen-st (pv self l)))))
  (lang (sig sign) (body (tuple 3)) (pv (tuple 2))))

(defskeleton dhcr-um
  (vars (na nb data) (a b name) (pt pval) (priv-stor locn) (la x rndx)
    (beta upsilon expt))
  (defstrand init 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (la la) (x x) (beta beta) (upsilon upsilon))
  (non-orig (privk "sig" b))
  (uniq-orig na)
  (uniq-gen x)
  (absent (x la) (x beta))
  (facts (neq a b) (undisclosed la))
  (traces
    ((load priv-stor (cat pt (pv a la)))
      (recv
        (sig (body b (exp (gen) beta) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) upsilon)
          (enc na nb a b
            (hash (exp (gen) (mul la beta))
              (exp (gen) (mul x upsilon)))))) (send nb)))
  (label 341)
  (unrealized (0 1))
  (origs (na (0 2)))
  (comment "Not closed under rules"))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (b self name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn)
    (lb l x y rndx))
  (defstrand init 5 (na na) (nb nb) (a self) (b b)
    (priv-stor priv-stor-0) (la l) (x x) (beta lb) (upsilon y))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l lb))
  (defstrand resp 4 (na na) (nb nb) (a self) (b b) (priv-stor priv-stor)
    (lb lb) (y y) (alpha l) (zeta x))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l))
  (precedes ((0 2) (2 2)) ((1 1) (2 0)) ((1 2) (0 1)) ((2 3) (0 3))
    ((3 1) (0 0)) ((3 2) (2 1)))
  (non-orig (privk "sig" b))
  (uniq-orig na nb lb l)
  (uniq-gen x y)
  (absent (x lb) (x l) (y lb) (y l) (y x))
  (gen-st (pv b lb) (pv self l))
  (facts (neq (exp (gen) y) (gen)) (neq (exp (gen) x) (gen)) (trans 3 1)
    (trans 1 1) (trans 3 0) (trans 1 0) (neq self b) (undisclosed l))
  (operation nonce-test (displaced 4 2 resp 4) (exp (gen) y-0) (0 3))
  (traces
    ((load priv-stor-0 (cat pt-2 (pv self l)))
      (recv
        (sig (body b (exp (gen) lb) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na self b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb self b
            (hash (exp (gen) (mul lb l)) (exp (gen) (mul x y))))))
      (send nb))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv b lb)))
      (send
        (sig (body b (exp (gen) lb) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt-0 (pv b lb)))
      (recv
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self))) (recv (cat na self b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb self b
            (hash (exp (gen) (mul lb l)) (exp (gen) (mul x y)))))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv self l)))
      (send
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self)))))
  (label 357)
  (parent 341)
  (realized)
  (shape)
  (maps
    ((0)
      ((a self) (b b) (la l) (x x) (beta lb) (upsilon y) (na na) (nb nb)
        (priv-stor priv-stor-0) (pt pt-2))))
  (origs (nb (2 3)) (l (3 1)) (pt-2 (3 1)) (lb (1 1)) (pt-0 (1 1))
    (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (b self name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn) (x rndx)
    (upsilon expt) (l l-0 rndx))
  (defstrand init 5 (na na) (nb nb) (a self) (b b)
    (priv-stor priv-stor-0) (la l-0) (x x) (beta l) (upsilon upsilon))
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
  (facts (neq (exp (gen) upsilon) (gen)) (trans 3 1) (trans 1 1)
    (trans 3 0) (trans 1 0) (trans 2 1) (trans 2 0) (neq self b)
    (undisclosed l-0))
  (operation generalization deleted (2 0))
  (traces
    ((load priv-stor-0 (cat pt-3 (pv self l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na self b (exp (gen) x)))
      (recv
        (cat (exp (gen) upsilon)
          (enc na nb self b
            (hash (exp (gen) (mul l l-0))
              (exp (gen) (mul x upsilon)))))) (send nb))
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
  (label 453)
  (parent 341)
  (realized)
  (shape)
  (maps
    ((0)
      ((a self) (b b) (la l-0) (x x) (beta l) (upsilon upsilon) (na na)
        (nb nb) (priv-stor priv-stor-0) (pt pt-3))))
  (origs (l-0 (3 1)) (pt-3 (3 1)) (pt-1 (2 1)) (l (1 1)) (pt-0 (1 1))
    (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 ignore-1 mesg) (na nb data) (b self name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (l l-0 lb x y rndx))
  (defstrand init 5 (na na) (nb nb) (a self) (b b)
    (priv-stor priv-stor-1) (la l-0) (x x) (beta l) (upsilon y))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 2 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l lb))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l))
  (defstrand ltx-gen 3 (ignore ignore-1) (self self)
    (priv-stor priv-stor-1) (l l-0))
  (precedes ((1 1) (3 0)) ((1 2) (0 1)) ((3 2) (0 3)) ((4 1) (0 0))
    ((4 2) (0 3)))
  (non-orig (privk "sig" b))
  (uniq-orig na l l-0 lb)
  (uniq-gen x y)
  (absent (x l) (x l-0) (y (mul l l-0 (rec lb))) (y lb) (y x))
  (gen-st (pv b l) (pv b lb) (pv self l-0))
  (facts (neq (exp (gen) y) (gen)) (trans 4 1) (trans 2 1) (trans 1 1)
    (trans 4 0) (trans 2 0) (trans 1 0) (trans 3 1) (trans 3 0)
    (neq self b) (undisclosed l-0))
  (operation generalization forgot nb)
  (traces
    ((load priv-stor-1 (cat pt-5 (pv self l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na self b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb self b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y))))))
      (send nb))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-0 (cat pt-2 ignore-0))
      (stor priv-stor-0 (cat pt-1 (pv b lb))))
    ((load priv-stor (cat pt-0 (pv b l)))
      (stor priv-stor (cat pt-3 "nil")) (send l))
    ((load priv-stor-1 (cat pt-4 ignore-1))
      (stor priv-stor-1 (cat pt-5 (pv self l-0)))
      (send
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self)))))
  (label 572)
  (parent 341)
  (realized)
  (shape)
  (maps
    ((0)
      ((a self) (b b) (la l-0) (x x) (beta l) (upsilon y) (na na)
        (nb nb) (priv-stor priv-stor-1) (pt pt-5))))
  (origs (l-0 (4 1)) (pt-5 (4 1)) (pt-3 (3 1)) (lb (2 1)) (pt-1 (2 1))
    (l (1 1)) (pt-0 (1 1)) (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 ignore-1 mesg) (na nb data) (b self name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (l l-0 lb x rndx) (w expt)
    (y rndx))
  (defstrand init 5 (na na) (nb nb) (a self) (b b)
    (priv-stor priv-stor-1) (la l-0) (x x) (beta l) (upsilon (mul w y)))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 2 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l lb))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l))
  (defstrand ltx-gen 3 (ignore ignore-1) (self self)
    (priv-stor priv-stor-1) (l l-0))
  (deflistener (cat (exp (gen) y) w))
  (precedes ((1 1) (3 0)) ((1 2) (0 1)) ((3 2) (0 3)) ((4 1) (0 0))
    ((4 2) (0 3)))
  (non-orig (privk "sig" b))
  (uniq-orig na l l-0 lb)
  (uniq-gen x y)
  (absent (x l) (x l-0) (y (mul l l-0 (rec lb))) (y lb) (y (mul x w)))
  (precur (5 0))
  (gen-st (pv b l) (pv b lb) (pv self l-0))
  (facts (neq (exp (gen) (mul w y)) (gen)) (trans 4 1) (trans 2 1)
    (trans 1 1) (trans 4 0) (trans 2 0) (trans 1 0) (trans 3 1)
    (trans 3 0) (neq self b) (undisclosed l-0))
  (operation generalization forgot nb)
  (traces
    ((load priv-stor-1 (cat pt-5 (pv self l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na self b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul w y))
          (enc na nb self b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x w y))))))
      (send nb))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-0 (cat pt-2 ignore-0))
      (stor priv-stor-0 (cat pt-1 (pv b lb))))
    ((load priv-stor (cat pt-0 (pv b l)))
      (stor priv-stor (cat pt-3 "nil")) (send l))
    ((load priv-stor-1 (cat pt-4 ignore-1))
      (stor priv-stor-1 (cat pt-5 (pv self l-0)))
      (send
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self)))) ((recv (cat (exp (gen) y) w))))
  (label 584)
  (parent 341)
  (realized)
  (shape)
  (maps
    ((0)
      ((a self) (b b) (la l-0) (x x) (beta l) (upsilon (mul w y))
        (na na) (nb nb) (priv-stor priv-stor-1) (pt pt-5))))
  (origs (l-0 (4 1)) (pt-5 (4 1)) (pt-3 (3 1)) (lb (2 1)) (pt-1 (2 1))
    (l (1 1)) (pt-0 (1 1)) (na (0 2))))

(comment "Nothing left to do")

(defprotocol dhcr-um diffie-hellman
  (defrole init
    (vars (la x rndx) (beta upsilon expt) (a b name) (na nb data)
      (priv-stor locn))
    (trace (load priv-stor (pv a la))
      (recv
        (sig (body b (exp (gen) beta) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) upsilon)
          (enc na nb a b
            (hash (exp (gen) (mul la beta))
              (exp (gen) (mul x upsilon)))))) (send nb))
    (uniq-orig na)
    (uniq-gen x)
    (absent (x la) (x beta))
    (assume (fact neq (exp (gen) upsilon) (gen)))
    (gen-st (pv a la)))
  (defrole resp
    (vars (lb y rndx) (alpha zeta expt) (a b name) (na nb data)
      (priv-stor locn))
    (trace (load priv-stor (pv b lb))
      (recv
        (sig (body a (exp (gen) alpha) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) zeta)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul lb alpha))
              (exp (gen) (mul y zeta)))))) (recv nb))
    (uniq-orig nb)
    (uniq-gen y)
    (absent (y lb) (y alpha) (y zeta))
    (assume (fact neq (exp (gen) zeta) (gen)))
    (gen-st (pv b lb)))
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
        (and (fact undisclosed l) (p "ltx-disclose" z 2)
          (p "ltx-disclose" "l" z l))
        (false))))
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
  (defgenrule assume-init-0
    (forall ((z strd) (upsilon expt))
      (implies (and (p "init" z 4) (p "init" "upsilon" z upsilon))
        (fact neq (exp (gen) upsilon) (gen)))))
  (defgenrule assume-resp-0
    (forall ((z strd) (zeta expt))
      (implies (and (p "resp" z 3) (p "resp" "zeta" z zeta))
        (fact neq (exp (gen) zeta) (gen)))))
  (defgenrule trRl_ltx-gen-at-1
    (forall ((z strd)) (implies (p "ltx-gen" z 2) (trans z 1))))
  (defgenrule trRl_ltx-gen-at-0
    (forall ((z strd)) (implies (p "ltx-gen" z 2) (trans z 0))))
  (defgenrule trRl_ltx-disclose-at-1
    (forall ((z strd)) (implies (p "ltx-disclose" z 2) (trans z 1))))
  (defgenrule trRl_ltx-disclose-at-0
    (forall ((z strd)) (implies (p "ltx-disclose" z 2) (trans z 0))))
  (defgenrule gen-st-init-0
    (forall ((z strd) (la rndx) (a name))
      (implies
        (and (p "init" z 1) (p "init" "la" z la) (p "init" "a" z a))
        (gen-st (pv a la)))))
  (defgenrule gen-st-resp-0
    (forall ((z strd) (lb rndx) (b name))
      (implies
        (and (p "resp" z 1) (p "resp" "lb" z lb) (p "resp" "b" z b))
        (gen-st (pv b lb)))))
  (defgenrule gen-st-ltx-disclose-0
    (forall ((z strd) (l rndx) (self name))
      (implies
        (and (p "ltx-disclose" z 1) (p "ltx-disclose" "l" z l)
          (p "ltx-disclose" "self" z self)) (gen-st (pv self l)))))
  (lang (sig sign) (body (tuple 3)) (pv (tuple 2))))

(defskeleton dhcr-um
  (vars (na nb data) (a b name) (pt pval) (priv-stor locn) (la x rndx)
    (beta upsilon expt))
  (defstrand init 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (la la) (x x) (beta beta) (upsilon upsilon))
  (non-orig (privk "sig" b))
  (uniq-orig na)
  (uniq-gen x)
  (absent (x la) (x beta))
  (facts (neq a b))
  (traces
    ((load priv-stor (cat pt (pv a la)))
      (recv
        (sig (body b (exp (gen) beta) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) upsilon)
          (enc na nb a b
            (hash (exp (gen) (mul la beta))
              (exp (gen) (mul x upsilon)))))) (send nb)))
  (label 585)
  (unrealized (0 1))
  (origs (na (0 2)))
  (comment "Not closed under rules"))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (b self name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn)
    (lb l x y rndx))
  (defstrand init 5 (na na) (nb nb) (a self) (b b)
    (priv-stor priv-stor-0) (la l) (x x) (beta lb) (upsilon y))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l lb))
  (defstrand resp 4 (na na) (nb nb) (a self) (b b) (priv-stor priv-stor)
    (lb lb) (y y) (alpha l) (zeta x))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l))
  (precedes ((0 2) (2 2)) ((1 1) (2 0)) ((1 2) (0 1)) ((2 3) (0 3))
    ((3 1) (0 0)) ((3 2) (2 1)))
  (non-orig (privk "sig" b))
  (uniq-orig na nb lb l)
  (uniq-gen x y)
  (absent (x lb) (x l) (y lb) (y l) (y x))
  (gen-st (pv b lb) (pv self l))
  (facts (neq (exp (gen) y) (gen)) (neq (exp (gen) x) (gen)) (trans 3 1)
    (trans 1 1) (trans 3 0) (trans 1 0) (neq self b))
  (operation nonce-test (displaced 4 2 resp 4) (exp (gen) y-0) (0 3))
  (traces
    ((load priv-stor-0 (cat pt-2 (pv self l)))
      (recv
        (sig (body b (exp (gen) lb) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na self b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb self b
            (hash (exp (gen) (mul lb l)) (exp (gen) (mul x y))))))
      (send nb))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv b lb)))
      (send
        (sig (body b (exp (gen) lb) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt-0 (pv b lb)))
      (recv
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self))) (recv (cat na self b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb self b
            (hash (exp (gen) (mul lb l)) (exp (gen) (mul x y)))))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv self l)))
      (send
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self)))))
  (label 601)
  (parent 585)
  (realized)
  (shape)
  (maps
    ((0)
      ((a self) (b b) (la l) (x x) (beta lb) (upsilon y) (na na) (nb nb)
        (priv-stor priv-stor-0) (pt pt-2))))
  (origs (nb (2 3)) (l (3 1)) (pt-2 (3 1)) (lb (1 1)) (pt-0 (1 1))
    (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (b self name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn) (x rndx)
    (upsilon expt) (l l-0 rndx))
  (defstrand init 5 (na na) (nb nb) (a self) (b b)
    (priv-stor priv-stor-0) (la l-0) (x x) (beta l) (upsilon upsilon))
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
  (facts (neq (exp (gen) upsilon) (gen)) (trans 3 1) (trans 1 1)
    (trans 3 0) (trans 1 0) (trans 2 1) (trans 2 0) (neq self b))
  (operation generalization deleted (2 0))
  (traces
    ((load priv-stor-0 (cat pt-3 (pv self l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na self b (exp (gen) x)))
      (recv
        (cat (exp (gen) upsilon)
          (enc na nb self b
            (hash (exp (gen) (mul l l-0))
              (exp (gen) (mul x upsilon)))))) (send nb))
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
  (label 787)
  (parent 585)
  (realized)
  (shape)
  (maps
    ((0)
      ((a self) (b b) (la l-0) (x x) (beta l) (upsilon upsilon) (na na)
        (nb nb) (priv-stor priv-stor-0) (pt pt-3))))
  (origs (l-0 (3 1)) (pt-3 (3 1)) (pt-1 (2 1)) (l (1 1)) (pt-0 (1 1))
    (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn) (x rndx)
    (upsilon expt) (l l-0 rndx))
  (defstrand init 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (la l) (x x) (beta l-0) (upsilon upsilon))
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
  (facts (neq (exp (gen) upsilon) (gen)) (trans 2 1) (trans 1 1)
    (trans 2 0) (trans 1 0) (trans 3 1) (trans 3 0) (neq a b))
  (operation generalization deleted (3 0))
  (traces
    ((load priv-stor (cat pt (pv a l)))
      (recv
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) upsilon)
          (enc na nb a b
            (hash (exp (gen) (mul l l-0))
              (exp (gen) (mul x upsilon)))))) (send nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l-0)))
      (send
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt (pv a l)))
      (stor priv-stor (cat pt-3 "nil")) (send l)))
  (label 790)
  (parent 585)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (la l) (x x) (beta l-0) (upsilon upsilon) (na na)
        (nb nb) (priv-stor priv-stor) (pt pt))))
  (origs (l-0 (2 1)) (pt-2 (2 1)) (pt-3 (3 1)) (l (1 1)) (pt (1 1))
    (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (lb l x y rndx))
  (defstrand init 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (la l) (x x) (beta lb) (upsilon y))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l lb))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (precedes ((1 1) (0 0)) ((1 1) (3 0)) ((2 2) (0 1)) ((3 2) (0 3)))
  (non-orig (privk "sig" b))
  (uniq-orig na lb l)
  (uniq-gen x y)
  (absent (x lb) (x l) (y lb) (y l) (y x))
  (gen-st (pv a l) (pv b lb))
  (facts (neq (exp (gen) y) (gen)) (trans 2 1) (trans 1 1) (trans 2 0)
    (trans 1 0) (trans 3 1) (trans 3 0) (neq a b))
  (operation generalization forgot nb)
  (traces
    ((load priv-stor (cat pt (pv a l)))
      (recv
        (sig (body b (exp (gen) lb) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul lb l)) (exp (gen) (mul x y))))))
      (send nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b lb)))
      (send
        (sig (body b (exp (gen) lb) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt (pv a l)))
      (stor priv-stor (cat pt-3 "nil")) (send l)))
  (label 793)
  (parent 585)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (la l) (x x) (beta lb) (upsilon y) (na na) (nb nb)
        (priv-stor priv-stor) (pt pt))))
  (origs (pt-3 (3 1)) (lb (2 1)) (pt-2 (2 1)) (l (1 1)) (pt (1 1))
    (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn) (x rndx)
    (upsilon expt) (l l-0 rndx))
  (defstrand init 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (la l-0) (x x) (beta l) (upsilon upsilon))
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
  (facts (neq (exp (gen) upsilon) (gen)) (trans 2 1) (trans 1 1)
    (trans 2 0) (trans 1 0) (trans 3 1) (trans 3 0) (neq a b))
  (operation generalization deleted (3 0))
  (traces
    ((load priv-stor (cat pt (pv a l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) upsilon)
          (enc na nb a b
            (hash (exp (gen) (mul l l-0))
              (exp (gen) (mul x upsilon)))))) (send nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l-0))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt (pv a l-0)))
      (stor priv-stor (cat pt-3 "nil")) (send l-0)))
  (label 1192)
  (parent 585)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (la l-0) (x x) (beta l) (upsilon upsilon) (na na)
        (nb nb) (priv-stor priv-stor) (pt pt))))
  (origs (pt-3 (3 1)) (l (2 1)) (pt-2 (2 1)) (l-0 (1 1)) (pt (1 1))
    (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 ignore-1 mesg) (na nb data) (b self name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (l l-0 lb x y rndx))
  (defstrand init 5 (na na) (nb nb) (a self) (b b)
    (priv-stor priv-stor-1) (la l-0) (x x) (beta l) (upsilon y))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 2 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l lb))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l))
  (defstrand ltx-gen 3 (ignore ignore-1) (self self)
    (priv-stor priv-stor-1) (l l-0))
  (precedes ((1 1) (3 0)) ((1 2) (0 1)) ((3 2) (0 3)) ((4 1) (0 0))
    ((4 2) (0 3)))
  (non-orig (privk "sig" b))
  (uniq-orig na l l-0 lb)
  (uniq-gen x y)
  (absent (x l) (x l-0) (y (mul l l-0 (rec lb))) (y lb) (y x))
  (gen-st (pv b l) (pv b lb) (pv self l-0))
  (facts (neq (exp (gen) y) (gen)) (trans 4 1) (trans 2 1) (trans 1 1)
    (trans 4 0) (trans 2 0) (trans 1 0) (trans 3 1) (trans 3 0)
    (neq self b))
  (operation generalization forgot nb)
  (traces
    ((load priv-stor-1 (cat pt-5 (pv self l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na self b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb self b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y))))))
      (send nb))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-0 (cat pt-2 ignore-0))
      (stor priv-stor-0 (cat pt-1 (pv b lb))))
    ((load priv-stor (cat pt-0 (pv b l)))
      (stor priv-stor (cat pt-3 "nil")) (send l))
    ((load priv-stor-1 (cat pt-4 ignore-1))
      (stor priv-stor-1 (cat pt-5 (pv self l-0)))
      (send
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self)))))
  (label 1253)
  (parent 585)
  (realized)
  (shape)
  (maps
    ((0)
      ((a self) (b b) (la l-0) (x x) (beta l) (upsilon y) (na na)
        (nb nb) (priv-stor priv-stor-1) (pt pt-5))))
  (origs (l-0 (4 1)) (pt-5 (4 1)) (pt-3 (3 1)) (lb (2 1)) (pt-1 (2 1))
    (l (1 1)) (pt-0 (1 1)) (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 ignore-1 mesg) (na nb data) (a b b-0 name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (l l-0 lb x y rndx))
  (defstrand init 5 (na na) (nb nb) (a a) (b b-0) (priv-stor priv-stor)
    (la l) (x x) (beta l-0) (upsilon y))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b-0)
    (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-gen 2 (ignore ignore-1) (self b)
    (priv-stor priv-stor-1) (l lb))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (precedes ((1 1) (0 0)) ((1 1) (4 0)) ((2 2) (0 1)) ((4 2) (0 3)))
  (non-orig (privk "sig" b-0))
  (uniq-orig na l l-0 lb)
  (uniq-gen x y)
  (absent (x l) (x l-0) (y (mul l l-0 (rec lb))) (y lb) (y x))
  (gen-st (pv a l) (pv b lb))
  (facts (neq (exp (gen) y) (gen)) (trans 3 1) (trans 2 1) (trans 1 1)
    (trans 3 0) (trans 2 0) (trans 1 0) (trans 4 1) (trans 4 0)
    (neq a b-0))
  (operation generalization forgot (privk "sig" b))
  (traces
    ((load priv-stor (cat pt (pv a l)))
      (recv
        (sig (body b-0 (exp (gen) l-0) (pubk "sig" b-0))
          (privk "sig" b-0))) (send (cat na a b-0 (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b-0
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y))))))
      (send nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b-0 l-0)))
      (send
        (sig (body b-0 (exp (gen) l-0) (pubk "sig" b-0))
          (privk "sig" b-0))))
    ((load priv-stor-1 (cat pt-4 ignore-1))
      (stor priv-stor-1 (cat pt-3 (pv b lb))))
    ((load priv-stor (cat pt (pv a l)))
      (stor priv-stor (cat pt-5 "nil")) (send l)))
  (label 1293)
  (parent 585)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b-0) (la l) (x x) (beta l-0) (upsilon y) (na na) (nb nb)
        (priv-stor priv-stor) (pt pt))))
  (origs (l-0 (2 1)) (pt-2 (2 1)) (pt-5 (4 1)) (lb (3 1)) (pt-3 (3 1))
    (l (1 1)) (pt (1 1)) (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (lb l x rndx) (w expt) (y rndx))
  (defstrand init 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (la l) (x x) (beta lb) (upsilon (mul w y)))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l lb))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (deflistener (cat (exp (gen) y) w))
  (precedes ((1 1) (0 0)) ((1 1) (3 0)) ((2 2) (0 1)) ((3 2) (0 3)))
  (non-orig (privk "sig" b))
  (uniq-orig na lb l)
  (uniq-gen x y)
  (absent (x lb) (x l) (y lb) (y l) (y (mul x w)))
  (precur (4 0))
  (gen-st (pv a l) (pv b lb))
  (facts (neq (exp (gen) (mul w y)) (gen)) (trans 2 1) (trans 1 1)
    (trans 2 0) (trans 1 0) (trans 3 1) (trans 3 0) (neq a b))
  (operation generalization forgot nb)
  (traces
    ((load priv-stor (cat pt (pv a l)))
      (recv
        (sig (body b (exp (gen) lb) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul w y))
          (enc na nb a b
            (hash (exp (gen) (mul lb l)) (exp (gen) (mul x w y))))))
      (send nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b lb)))
      (send
        (sig (body b (exp (gen) lb) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt (pv a l)))
      (stor priv-stor (cat pt-3 "nil")) (send l))
    ((recv (cat (exp (gen) y) w))))
  (label 1300)
  (parent 585)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (la l) (x x) (beta lb) (upsilon (mul w y)) (na na)
        (nb nb) (priv-stor priv-stor) (pt pt))))
  (origs (pt-3 (3 1)) (lb (2 1)) (pt-2 (2 1)) (l (1 1)) (pt (1 1))
    (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 ignore-1 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (l l-0 lb x y rndx))
  (defstrand init 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (la l-0) (x x) (beta l) (upsilon y))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-gen 2 (ignore ignore-1) (self b)
    (priv-stor priv-stor-1) (l lb))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l-0))
  (precedes ((1 1) (0 0)) ((1 1) (4 0)) ((2 2) (0 1)) ((4 2) (0 3)))
  (non-orig (privk "sig" b))
  (uniq-orig na l l-0 lb)
  (uniq-gen x y)
  (absent (x l) (x l-0) (y (mul l l-0 (rec lb))) (y lb) (y x))
  (gen-st (pv a l-0) (pv b l) (pv b lb))
  (facts (neq (exp (gen) y) (gen)) (trans 3 1) (trans 2 1) (trans 1 1)
    (trans 3 0) (trans 2 0) (trans 1 0) (trans 4 1) (trans 4 0)
    (neq a b))
  (operation generalization forgot nb)
  (traces
    ((load priv-stor (cat pt (pv a l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y))))))
      (send nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l-0))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-1 (cat pt-4 ignore-1))
      (stor priv-stor-1 (cat pt-3 (pv b lb))))
    ((load priv-stor (cat pt (pv a l-0)))
      (stor priv-stor (cat pt-5 "nil")) (send l-0)))
  (label 1309)
  (parent 585)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (la l-0) (x x) (beta l) (upsilon y) (na na) (nb nb)
        (priv-stor priv-stor) (pt pt))))
  (origs (pt-5 (4 1)) (lb (3 1)) (pt-3 (3 1)) (l (2 1)) (pt-2 (2 1))
    (l-0 (1 1)) (pt (1 1)) (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 ignore-1 mesg) (na nb data) (b self name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (l l-0 lb x rndx) (w expt)
    (y rndx))
  (defstrand init 5 (na na) (nb nb) (a self) (b b)
    (priv-stor priv-stor-1) (la l-0) (x x) (beta l) (upsilon (mul w y)))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 2 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l lb))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l))
  (defstrand ltx-gen 3 (ignore ignore-1) (self self)
    (priv-stor priv-stor-1) (l l-0))
  (deflistener (cat (exp (gen) y) w))
  (precedes ((1 1) (3 0)) ((1 2) (0 1)) ((3 2) (0 3)) ((4 1) (0 0))
    ((4 2) (0 3)))
  (non-orig (privk "sig" b))
  (uniq-orig na l l-0 lb)
  (uniq-gen x y)
  (absent (x l) (x l-0) (y (mul l l-0 (rec lb))) (y lb) (y (mul x w)))
  (precur (5 0))
  (gen-st (pv b l) (pv b lb) (pv self l-0))
  (facts (neq (exp (gen) (mul w y)) (gen)) (trans 4 1) (trans 2 1)
    (trans 1 1) (trans 4 0) (trans 2 0) (trans 1 0) (trans 3 1)
    (trans 3 0) (neq self b))
  (operation generalization forgot nb)
  (traces
    ((load priv-stor-1 (cat pt-5 (pv self l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na self b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul w y))
          (enc na nb self b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x w y))))))
      (send nb))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-0 (cat pt-2 ignore-0))
      (stor priv-stor-0 (cat pt-1 (pv b lb))))
    ((load priv-stor (cat pt-0 (pv b l)))
      (stor priv-stor (cat pt-3 "nil")) (send l))
    ((load priv-stor-1 (cat pt-4 ignore-1))
      (stor priv-stor-1 (cat pt-5 (pv self l-0)))
      (send
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self)))) ((recv (cat (exp (gen) y) w))))
  (label 1328)
  (parent 585)
  (realized)
  (shape)
  (maps
    ((0)
      ((a self) (b b) (la l-0) (x x) (beta l) (upsilon (mul w y))
        (na na) (nb nb) (priv-stor priv-stor-1) (pt pt-5))))
  (origs (l-0 (4 1)) (pt-5 (4 1)) (pt-3 (3 1)) (lb (2 1)) (pt-1 (2 1))
    (l (1 1)) (pt-0 (1 1)) (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 ignore-1 mesg) (na nb data) (a b b-0 name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (l l-0 lb x rndx) (w expt)
    (y rndx))
  (defstrand init 5 (na na) (nb nb) (a a) (b b-0) (priv-stor priv-stor)
    (la l) (x x) (beta l-0) (upsilon (mul w y)))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b-0)
    (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-gen 2 (ignore ignore-1) (self b)
    (priv-stor priv-stor-1) (l lb))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (deflistener (cat (exp (gen) y) w))
  (precedes ((1 1) (0 0)) ((1 1) (4 0)) ((2 2) (0 1)) ((4 2) (0 3)))
  (non-orig (privk "sig" b-0))
  (uniq-orig na l l-0 lb)
  (uniq-gen x y)
  (absent (x l) (x l-0) (y (mul l l-0 (rec lb))) (y lb) (y (mul x w)))
  (precur (5 0))
  (gen-st (pv a l) (pv b lb))
  (facts (neq (exp (gen) (mul w y)) (gen)) (trans 3 1) (trans 2 1)
    (trans 1 1) (trans 3 0) (trans 2 0) (trans 1 0) (trans 4 1)
    (trans 4 0) (neq a b-0))
  (operation generalization forgot (privk "sig" b))
  (traces
    ((load priv-stor (cat pt (pv a l)))
      (recv
        (sig (body b-0 (exp (gen) l-0) (pubk "sig" b-0))
          (privk "sig" b-0))) (send (cat na a b-0 (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul w y))
          (enc na nb a b-0
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x w y))))))
      (send nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b-0 l-0)))
      (send
        (sig (body b-0 (exp (gen) l-0) (pubk "sig" b-0))
          (privk "sig" b-0))))
    ((load priv-stor-1 (cat pt-4 ignore-1))
      (stor priv-stor-1 (cat pt-3 (pv b lb))))
    ((load priv-stor (cat pt (pv a l)))
      (stor priv-stor (cat pt-5 "nil")) (send l))
    ((recv (cat (exp (gen) y) w))))
  (label 1332)
  (parent 585)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b-0) (la l) (x x) (beta l-0) (upsilon (mul w y)) (na na)
        (nb nb) (priv-stor priv-stor) (pt pt))))
  (origs (l-0 (2 1)) (pt-2 (2 1)) (pt-5 (4 1)) (lb (3 1)) (pt-3 (3 1))
    (l (1 1)) (pt (1 1)) (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 ignore-1 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (l l-0 lb x rndx) (w expt)
    (y rndx))
  (defstrand init 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (la l-0) (x x) (beta l) (upsilon (mul w y)))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-gen 2 (ignore ignore-1) (self b)
    (priv-stor priv-stor-1) (l lb))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l-0))
  (deflistener (cat (exp (gen) y) w))
  (precedes ((1 1) (0 0)) ((1 1) (4 0)) ((2 2) (0 1)) ((4 2) (0 3)))
  (non-orig (privk "sig" b))
  (uniq-orig na l l-0 lb)
  (uniq-gen x y)
  (absent (x l) (x l-0) (y (mul l l-0 (rec lb))) (y lb) (y (mul x w)))
  (precur (5 0))
  (gen-st (pv a l-0) (pv b l) (pv b lb))
  (facts (neq (exp (gen) (mul w y)) (gen)) (trans 3 1) (trans 2 1)
    (trans 1 1) (trans 3 0) (trans 2 0) (trans 1 0) (trans 4 1)
    (trans 4 0) (neq a b))
  (operation generalization forgot nb)
  (traces
    ((load priv-stor (cat pt (pv a l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul w y))
          (enc na nb a b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x w y))))))
      (send nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l-0))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-1 (cat pt-4 ignore-1))
      (stor priv-stor-1 (cat pt-3 (pv b lb))))
    ((load priv-stor (cat pt (pv a l-0)))
      (stor priv-stor (cat pt-5 "nil")) (send l-0))
    ((recv (cat (exp (gen) y) w))))
  (label 1334)
  (parent 585)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (la l-0) (x x) (beta l) (upsilon (mul w y)) (na na)
        (nb nb) (priv-stor priv-stor) (pt pt))))
  (origs (pt-5 (4 1)) (lb (3 1)) (pt-3 (3 1)) (l (2 1)) (pt-2 (2 1))
    (l-0 (1 1)) (pt (1 1)) (na (0 2))))

(comment "Nothing left to do")

(defprotocol dhcr-um diffie-hellman
  (defrole init
    (vars (la x rndx) (beta upsilon expt) (a b name) (na nb data)
      (priv-stor locn))
    (trace (load priv-stor (pv a la))
      (recv
        (sig (body b (exp (gen) beta) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) upsilon)
          (enc na nb a b
            (hash (exp (gen) (mul la beta))
              (exp (gen) (mul x upsilon)))))) (send nb))
    (uniq-orig na)
    (uniq-gen x)
    (absent (x la) (x beta))
    (assume (fact neq (exp (gen) upsilon) (gen)))
    (gen-st (pv a la)))
  (defrole resp
    (vars (lb y rndx) (alpha zeta expt) (a b name) (na nb data)
      (priv-stor locn))
    (trace (load priv-stor (pv b lb))
      (recv
        (sig (body a (exp (gen) alpha) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) zeta)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul lb alpha))
              (exp (gen) (mul y zeta)))))) (recv nb))
    (uniq-orig nb)
    (uniq-gen y)
    (absent (y lb) (y alpha) (y zeta))
    (assume (fact neq (exp (gen) zeta) (gen)))
    (gen-st (pv b lb)))
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
        (and (fact undisclosed l) (p "ltx-disclose" z 2)
          (p "ltx-disclose" "l" z l))
        (false))))
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
  (defgenrule assume-init-0
    (forall ((z strd) (upsilon expt))
      (implies (and (p "init" z 4) (p "init" "upsilon" z upsilon))
        (fact neq (exp (gen) upsilon) (gen)))))
  (defgenrule assume-resp-0
    (forall ((z strd) (zeta expt))
      (implies (and (p "resp" z 3) (p "resp" "zeta" z zeta))
        (fact neq (exp (gen) zeta) (gen)))))
  (defgenrule trRl_ltx-gen-at-1
    (forall ((z strd)) (implies (p "ltx-gen" z 2) (trans z 1))))
  (defgenrule trRl_ltx-gen-at-0
    (forall ((z strd)) (implies (p "ltx-gen" z 2) (trans z 0))))
  (defgenrule trRl_ltx-disclose-at-1
    (forall ((z strd)) (implies (p "ltx-disclose" z 2) (trans z 1))))
  (defgenrule trRl_ltx-disclose-at-0
    (forall ((z strd)) (implies (p "ltx-disclose" z 2) (trans z 0))))
  (defgenrule gen-st-init-0
    (forall ((z strd) (la rndx) (a name))
      (implies
        (and (p "init" z 1) (p "init" "la" z la) (p "init" "a" z a))
        (gen-st (pv a la)))))
  (defgenrule gen-st-resp-0
    (forall ((z strd) (lb rndx) (b name))
      (implies
        (and (p "resp" z 1) (p "resp" "lb" z lb) (p "resp" "b" z b))
        (gen-st (pv b lb)))))
  (defgenrule gen-st-ltx-disclose-0
    (forall ((z strd) (l rndx) (self name))
      (implies
        (and (p "ltx-disclose" z 1) (p "ltx-disclose" "l" z l)
          (p "ltx-disclose" "self" z self)) (gen-st (pv self l)))))
  (lang (sig sign) (body (tuple 3)) (pv (tuple 2))))

(defskeleton dhcr-um
  (vars (na nb na-0 nb-0 data) (a b name) (pt pt-0 pval)
    (priv-stor priv-stor-0 locn) (la lb rndx) (alpha beta expt) (y rndx)
    (zeta expt) (x rndx) (upsilon expt))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (lb lb) (y y) (alpha alpha) (zeta zeta))
  (defstrand init 5 (na na-0) (nb nb-0) (a a) (b b)
    (priv-stor priv-stor-0) (la la) (x x) (beta beta) (upsilon upsilon))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig nb na-0)
  (uniq-gen y x)
  (absent (y lb) (y alpha) (y zeta) (x la) (x beta))
  (facts (neq a b) (undisclosed la) (undisclosed lb))
  (traces
    ((load priv-stor (cat pt (pv b lb)))
      (recv
        (sig (body a (exp (gen) alpha) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) zeta)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul lb alpha))
              (exp (gen) (mul y zeta)))))) (recv nb))
    ((load priv-stor-0 (cat pt-0 (pv a la)))
      (recv
        (sig (body b (exp (gen) beta) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na-0 a b (exp (gen) x)))
      (recv
        (cat (exp (gen) upsilon)
          (enc na-0 nb-0 a b
            (hash (exp (gen) (mul la beta))
              (exp (gen) (mul x upsilon)))))) (send nb-0)))
  (label 1335)
  (unrealized (0 1) (1 1))
  (origs (na-0 (1 2)) (nb (0 3)))
  (comment "Not closed under rules"))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn)
    (l y la x rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (lb l) (y y) (alpha la) (zeta x))
  (defstrand init 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor-0)
    (la la) (x x) (beta l) (upsilon y))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l la))
  (precedes ((0 3) (1 3)) ((1 2) (0 2)) ((1 4) (0 4)) ((2 1) (0 0))
    ((2 2) (1 1)) ((3 1) (1 0)) ((3 2) (0 1)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig na nb l la)
  (uniq-gen y x)
  (absent (y l) (y la) (y x) (x l) (x la))
  (gen-st (pv a la) (pv b l))
  (facts (neq (exp (gen) y) (gen)) (neq (exp (gen) x) (gen)) (trans 3 1)
    (trans 2 1) (trans 3 0) (trans 2 0) (neq a b) (undisclosed la)
    (undisclosed l))
  (operation nonce-test (displaced 4 1 init 5) nb (0 4)
    (enc na nb a b
      (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x-0 y)))))
  (traces
    ((load priv-stor (cat pt-0 (pv b l)))
      (recv
        (sig (body a (exp (gen) la) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul l la)) (exp (gen) (mul y x))))))
      (recv nb))
    ((load priv-stor-0 (cat pt-2 (pv a la)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul l la)) (exp (gen) (mul y x))))))
      (send nb))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv b l)))
      (send
        (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a la)))
      (send
        (sig (body a (exp (gen) la) (pubk "sig" a)) (privk "sig" a)))))
  (label 1372)
  (parent 1335)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((a a) (b b) (la la) (lb l) (alpha la) (beta l) (y y) (zeta x)
        (na na) (nb nb) (priv-stor priv-stor) (pt pt-0) (x x)
        (upsilon y) (na-0 na) (nb-0 nb) (priv-stor-0 priv-stor-0)
        (pt-0 pt-2))))
  (origs (na (1 2)) (la (3 1)) (pt-2 (3 1)) (l (2 1)) (pt-0 (2 1))
    (nb (0 3))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 ignore-1 mesg) (na nb na-0 nb-0 data)
    (a b name) (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (y rndx) (zeta expt)
    (l x y-0 l-0 l-1 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (lb l-1) (y y) (alpha l-0) (zeta zeta))
  (defstrand init 5 (na na-0) (nb nb-0) (a a) (b b)
    (priv-stor priv-stor-0) (la l) (x x) (beta l-1) (upsilon y-0))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l-1))
  (defstrand resp 4 (na na-0) (nb nb-0) (a a) (b b)
    (priv-stor priv-stor) (lb l-1) (y y-0) (alpha l) (zeta x))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-gen 3 (ignore ignore-1) (self a)
    (priv-stor priv-stor-1) (l l-0))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor-1) (l l-0))
  (precedes ((1 2) (3 2)) ((2 1) (0 0)) ((2 1) (3 0)) ((2 2) (0 4))
    ((2 2) (1 1)) ((3 3) (1 3)) ((4 1) (1 0)) ((4 2) (3 1))
    ((5 1) (6 0)) ((5 2) (0 1)) ((6 2) (0 4)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig nb na-0 nb-0 l l-0 l-1)
  (uniq-gen y x y-0)
  (absent (y zeta) (y l-0) (y l-1) (x l) (x l-1) (y-0 l) (y-0 x)
    (y-0 l-1))
  (gen-st (pv a l) (pv a l-0) (pv b l-1))
  (facts (neq (exp (gen) y-0) (gen)) (neq (exp (gen) x) (gen))
    (neq (exp (gen) zeta) (gen)) (trans 5 1) (trans 4 1) (trans 2 1)
    (trans 5 0) (trans 4 0) (trans 2 0) (trans 6 1) (trans 6 0)
    (neq a b) (undisclosed l) (undisclosed l-1))
  (operation generalization deleted (6 0))
  (traces
    ((load priv-stor (cat pt-0 (pv b l-1)))
      (recv
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) zeta)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul l-0 l-1)) (exp (gen) (mul y zeta))))))
      (recv nb))
    ((load priv-stor-0 (cat pt-2 (pv a l)))
      (recv
        (sig (body b (exp (gen) l-1) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na-0 a b (exp (gen) x)))
      (recv
        (cat (exp (gen) y-0)
          (enc na-0 nb-0 a b
            (hash (exp (gen) (mul l l-1)) (exp (gen) (mul x y-0))))))
      (send nb-0))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv b l-1)))
      (send
        (sig (body b (exp (gen) l-1) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt-0 (pv b l-1)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na-0 a b (exp (gen) x)))
      (send
        (cat (exp (gen) y-0)
          (enc na-0 nb-0 a b
            (hash (exp (gen) (mul l l-1)) (exp (gen) (mul x y-0)))))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l)))
      (send
        (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor-1 (cat pt-3 ignore-1))
      (stor priv-stor-1 (cat pt-4 (pv a l-0)))
      (send
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor-1 (cat pt-4 (pv a l-0)))
      (stor priv-stor-1 (cat pt-5 "nil")) (send l-0)))
  (label 1656)
  (parent 1335)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((a a) (b b) (la l) (lb l-1) (alpha l-0) (beta l-1) (y y)
        (zeta zeta) (na na) (nb nb) (priv-stor priv-stor) (pt pt-0)
        (x x) (upsilon y-0) (na-0 na-0) (nb-0 nb-0)
        (priv-stor-0 priv-stor-0) (pt-0 pt-2))))
  (origs (l-1 (2 1)) (pt-0 (2 1)) (pt-5 (6 1)) (l-0 (5 1)) (pt-4 (5 1))
    (nb-0 (3 3)) (l (4 1)) (pt-2 (4 1)) (na-0 (1 2)) (nb (0 3))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 ignore-1 ignore-2 mesg) (na nb na-0 nb-0 data)
    (a self name) (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pt-6 pt-7 pval)
    (priv-stor priv-stor-0 priv-stor-1 priv-stor-2 locn) (y rndx)
    (zeta expt) (lb l x y-0 l-0 l-1 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b self)
    (priv-stor priv-stor-2) (lb l-1) (y y) (alpha l-0) (zeta zeta))
  (defstrand init 5 (na na-0) (nb nb-0) (a a) (b self)
    (priv-stor priv-stor-0) (la l) (x x) (beta lb) (upsilon y-0))
  (defstrand ltx-gen 3 (ignore ignore) (self self) (priv-stor priv-stor)
    (l lb))
  (defstrand resp 4 (na na-0) (nb nb-0) (a a) (b self)
    (priv-stor priv-stor) (lb lb) (y y-0) (alpha l) (zeta x))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-gen 3 (ignore ignore-1) (self a)
    (priv-stor priv-stor-1) (l l-0))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor-1) (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-2) (self self)
    (priv-stor priv-stor-2) (l l-1))
  (precedes ((1 2) (3 2)) ((2 1) (3 0)) ((2 2) (1 1)) ((3 3) (1 3))
    ((4 1) (1 0)) ((4 2) (3 1)) ((5 1) (6 0)) ((5 2) (0 1))
    ((6 2) (0 4)) ((7 1) (0 0)) ((7 2) (0 4)))
  (non-orig (privk "sig" a) (privk "sig" self))
  (uniq-orig nb na-0 nb-0 lb l l-0 l-1)
  (uniq-gen y x y-0)
  (absent (y zeta) (y l-0) (y l-1) (x lb) (x l) (y-0 lb) (y-0 l)
    (y-0 x))
  (gen-st (pv a l) (pv a l-0) (pv self lb) (pv self l-1))
  (facts (neq (exp (gen) y-0) (gen)) (neq (exp (gen) x) (gen))
    (neq (exp (gen) zeta) (gen)) (trans 7 1) (trans 5 1) (trans 4 1)
    (trans 2 1) (trans 7 0) (trans 5 0) (trans 4 0) (trans 2 0)
    (trans 6 1) (trans 6 0) (neq a self) (undisclosed l)
    (undisclosed l-1))
  (operation generalization deleted (6 0))
  (traces
    ((load priv-stor-2 (cat pt-7 (pv self l-1)))
      (recv
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a self (exp (gen) zeta)))
      (send
        (cat (exp (gen) y)
          (enc na nb a self
            (hash (exp (gen) (mul l-0 l-1)) (exp (gen) (mul y zeta))))))
      (recv nb))
    ((load priv-stor-0 (cat pt-2 (pv a l)))
      (recv
        (sig (body self (exp (gen) lb) (pubk "sig" self))
          (privk "sig" self))) (send (cat na-0 a self (exp (gen) x)))
      (recv
        (cat (exp (gen) y-0)
          (enc na-0 nb-0 a self
            (hash (exp (gen) (mul lb l)) (exp (gen) (mul x y-0))))))
      (send nb-0))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv self lb)))
      (send
        (sig (body self (exp (gen) lb) (pubk "sig" self))
          (privk "sig" self))))
    ((load priv-stor (cat pt-0 (pv self lb)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na-0 a self (exp (gen) x)))
      (send
        (cat (exp (gen) y-0)
          (enc na-0 nb-0 a self
            (hash (exp (gen) (mul lb l)) (exp (gen) (mul x y-0)))))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l)))
      (send
        (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor-1 (cat pt-3 ignore-1))
      (stor priv-stor-1 (cat pt-4 (pv a l-0)))
      (send
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor-1 (cat pt-4 (pv a l-0)))
      (stor priv-stor-1 (cat pt-5 "nil")) (send l-0))
    ((load priv-stor-2 (cat pt-6 ignore-2))
      (stor priv-stor-2 (cat pt-7 (pv self l-1)))
      (send
        (sig (body self (exp (gen) l-1) (pubk "sig" self))
          (privk "sig" self)))))
  (label 1658)
  (parent 1335)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((a a) (b self) (la l) (lb l-1) (alpha l-0) (beta lb) (y y)
        (zeta zeta) (na na) (nb nb) (priv-stor priv-stor-2) (pt pt-7)
        (x x) (upsilon y-0) (na-0 na-0) (nb-0 nb-0)
        (priv-stor-0 priv-stor-0) (pt-0 pt-2))))
  (origs (l-1 (7 1)) (pt-7 (7 1)) (pt-5 (6 1)) (l-0 (5 1)) (pt-4 (5 1))
    (nb-0 (3 3)) (l (4 1)) (pt-2 (4 1)) (lb (2 1)) (pt-0 (2 1))
    (na-0 (1 2)) (nb (0 3))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 ignore-1 mesg) (na nb na-0 nb-0 data)
    (a b name) (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (y rndx) (zeta expt)
    (l x rndx) (w expt) (y-0 l-0 l-1 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (lb l-1) (y y) (alpha l-0) (zeta zeta))
  (defstrand init 5 (na na-0) (nb nb-0) (a a) (b b)
    (priv-stor priv-stor-0) (la l) (x x) (beta l-1)
    (upsilon (mul w y-0)))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l-1))
  (defstrand resp 4 (na na-0) (nb nb-0) (a a) (b b)
    (priv-stor priv-stor) (lb l-1) (y y-0) (alpha l) (zeta (mul x w)))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-gen 3 (ignore ignore-1) (self a)
    (priv-stor priv-stor-1) (l l-0))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor-1) (l l-0))
  (precedes ((1 2) (3 2)) ((2 1) (0 0)) ((2 1) (3 0)) ((2 2) (0 4))
    ((2 2) (1 1)) ((3 3) (1 3)) ((4 1) (1 0)) ((4 2) (3 1))
    ((5 1) (6 0)) ((5 2) (0 1)) ((6 2) (0 4)))
  (non-orig (privk "sig" a) (privk "sig" b))
  (uniq-orig nb na-0 nb-0 l l-0 l-1)
  (uniq-gen y x y-0)
  (absent (y zeta) (y l-0) (y l-1) (x l) (x l-1) (y-0 l) (y-0 (mul x w))
    (y-0 l-1))
  (gen-st (pv a l) (pv a l-0) (pv b l-1))
  (facts (neq (exp (gen) (mul w y-0)) (gen))
    (neq (exp (gen) (mul x w)) (gen)) (neq (exp (gen) zeta) (gen))
    (trans 5 1) (trans 4 1) (trans 2 1) (trans 5 0) (trans 4 0)
    (trans 2 0) (trans 6 1) (trans 6 0) (neq a b) (undisclosed l)
    (undisclosed l-1))
  (operation generalization deleted (6 0))
  (traces
    ((load priv-stor (cat pt-0 (pv b l-1)))
      (recv
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) zeta)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul l-0 l-1)) (exp (gen) (mul y zeta))))))
      (recv nb))
    ((load priv-stor-0 (cat pt-2 (pv a l)))
      (recv
        (sig (body b (exp (gen) l-1) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na-0 a b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul w y-0))
          (enc na-0 nb-0 a b
            (hash (exp (gen) (mul l l-1)) (exp (gen) (mul x w y-0))))))
      (send nb-0))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv b l-1)))
      (send
        (sig (body b (exp (gen) l-1) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt-0 (pv b l-1)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na-0 a b (exp (gen) (mul x w))))
      (send
        (cat (exp (gen) y-0)
          (enc na-0 nb-0 a b
            (hash (exp (gen) (mul l l-1)) (exp (gen) (mul x w y-0)))))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l)))
      (send
        (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor-1 (cat pt-3 ignore-1))
      (stor priv-stor-1 (cat pt-4 (pv a l-0)))
      (send
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor-1 (cat pt-4 (pv a l-0)))
      (stor priv-stor-1 (cat pt-5 "nil")) (send l-0)))
  (label 1725)
  (parent 1335)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((a a) (b b) (la l) (lb l-1) (alpha l-0) (beta l-1) (y y)
        (zeta zeta) (na na) (nb nb) (priv-stor priv-stor) (pt pt-0)
        (x x) (upsilon (mul w y-0)) (na-0 na-0) (nb-0 nb-0)
        (priv-stor-0 priv-stor-0) (pt-0 pt-2))))
  (origs (l-1 (2 1)) (pt-0 (2 1)) (pt-5 (6 1)) (l-0 (5 1)) (pt-4 (5 1))
    (nb-0 (3 3)) (l (4 1)) (pt-2 (4 1)) (na-0 (1 2)) (nb (0 3))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 ignore-1 ignore-2 mesg) (na nb na-0 nb-0 data)
    (a self name) (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pt-6 pt-7 pval)
    (priv-stor priv-stor-0 priv-stor-1 priv-stor-2 locn) (y rndx)
    (zeta expt) (lb l x rndx) (w expt) (y-0 l-0 l-1 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b self)
    (priv-stor priv-stor-2) (lb l-1) (y y) (alpha l-0) (zeta zeta))
  (defstrand init 5 (na na-0) (nb nb-0) (a a) (b self)
    (priv-stor priv-stor-0) (la l) (x x) (beta lb)
    (upsilon (mul w y-0)))
  (defstrand ltx-gen 3 (ignore ignore) (self self) (priv-stor priv-stor)
    (l lb))
  (defstrand resp 4 (na na-0) (nb nb-0) (a a) (b self)
    (priv-stor priv-stor) (lb lb) (y y-0) (alpha l) (zeta (mul x w)))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-gen 3 (ignore ignore-1) (self a)
    (priv-stor priv-stor-1) (l l-0))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor-1) (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-2) (self self)
    (priv-stor priv-stor-2) (l l-1))
  (precedes ((1 2) (3 2)) ((2 1) (3 0)) ((2 2) (1 1)) ((3 3) (1 3))
    ((4 1) (1 0)) ((4 2) (3 1)) ((5 1) (6 0)) ((5 2) (0 1))
    ((6 2) (0 4)) ((7 1) (0 0)) ((7 2) (0 4)))
  (non-orig (privk "sig" a) (privk "sig" self))
  (uniq-orig nb na-0 nb-0 lb l l-0 l-1)
  (uniq-gen y x y-0)
  (absent (y zeta) (y l-0) (y l-1) (x lb) (x l) (y-0 lb) (y-0 l)
    (y-0 (mul x w)))
  (gen-st (pv a l) (pv a l-0) (pv self lb) (pv self l-1))
  (facts (neq (exp (gen) (mul w y-0)) (gen))
    (neq (exp (gen) (mul x w)) (gen)) (neq (exp (gen) zeta) (gen))
    (trans 7 1) (trans 5 1) (trans 4 1) (trans 2 1) (trans 7 0)
    (trans 5 0) (trans 4 0) (trans 2 0) (trans 6 1) (trans 6 0)
    (neq a self) (undisclosed l) (undisclosed l-1))
  (operation generalization deleted (6 0))
  (traces
    ((load priv-stor-2 (cat pt-7 (pv self l-1)))
      (recv
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a self (exp (gen) zeta)))
      (send
        (cat (exp (gen) y)
          (enc na nb a self
            (hash (exp (gen) (mul l-0 l-1)) (exp (gen) (mul y zeta))))))
      (recv nb))
    ((load priv-stor-0 (cat pt-2 (pv a l)))
      (recv
        (sig (body self (exp (gen) lb) (pubk "sig" self))
          (privk "sig" self))) (send (cat na-0 a self (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul w y-0))
          (enc na-0 nb-0 a self
            (hash (exp (gen) (mul lb l)) (exp (gen) (mul x w y-0))))))
      (send nb-0))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv self lb)))
      (send
        (sig (body self (exp (gen) lb) (pubk "sig" self))
          (privk "sig" self))))
    ((load priv-stor (cat pt-0 (pv self lb)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na-0 a self (exp (gen) (mul x w))))
      (send
        (cat (exp (gen) y-0)
          (enc na-0 nb-0 a self
            (hash (exp (gen) (mul lb l)) (exp (gen) (mul x w y-0)))))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l)))
      (send
        (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor-1 (cat pt-3 ignore-1))
      (stor priv-stor-1 (cat pt-4 (pv a l-0)))
      (send
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor-1 (cat pt-4 (pv a l-0)))
      (stor priv-stor-1 (cat pt-5 "nil")) (send l-0))
    ((load priv-stor-2 (cat pt-6 ignore-2))
      (stor priv-stor-2 (cat pt-7 (pv self l-1)))
      (send
        (sig (body self (exp (gen) l-1) (pubk "sig" self))
          (privk "sig" self)))))
  (label 1727)
  (parent 1335)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((a a) (b self) (la l) (lb l-1) (alpha l-0) (beta lb) (y y)
        (zeta zeta) (na na) (nb nb) (priv-stor priv-stor-2) (pt pt-7)
        (x x) (upsilon (mul w y-0)) (na-0 na-0) (nb-0 nb-0)
        (priv-stor-0 priv-stor-0) (pt-0 pt-2))))
  (origs (l-1 (7 1)) (pt-7 (7 1)) (pt-5 (6 1)) (l-0 (5 1)) (pt-4 (5 1))
    (nb-0 (3 3)) (l (4 1)) (pt-2 (4 1)) (lb (2 1)) (pt-0 (2 1))
    (na-0 (1 2)) (nb (0 3))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 ignore-1 ignore-2 mesg) (na nb na-0 nb-0 data)
    (self self-0 name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pt-6 pt-7 pt-8 pval)
    (priv-stor priv-stor-0 priv-stor-1 priv-stor-2 locn) (y rndx)
    (zeta expt) (x rndx) (upsilon expt) (l l-0 l-1 l-2 rndx))
  (defstrand resp 5 (na na) (nb nb) (a self) (b self-0)
    (priv-stor priv-stor-2) (lb l-2) (y y) (alpha l-1) (zeta zeta))
  (defstrand init 5 (na na-0) (nb nb-0) (a self) (b self-0)
    (priv-stor priv-stor-0) (la l-0) (x x) (beta l) (upsilon upsilon))
  (defstrand ltx-gen 3 (ignore ignore) (self self-0)
    (priv-stor priv-stor) (l l))
  (defstrand ltx-disclose 3 (self self-0) (priv-stor priv-stor) (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-1) (self self)
    (priv-stor priv-stor-1) (l l-1))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor-1) (l l-1))
  (defstrand ltx-gen 3 (ignore ignore-2) (self self-0)
    (priv-stor priv-stor-2) (l l-2))
  (precedes ((2 1) (3 0)) ((2 2) (1 1)) ((3 2) (1 3)) ((4 1) (1 0))
    ((4 2) (1 3)) ((5 1) (6 0)) ((5 2) (0 1)) ((6 2) (0 4))
    ((7 1) (0 0)) ((7 2) (0 4)))
  (non-orig (privk "sig" self) (privk "sig" self-0))
  (uniq-orig nb na-0 l l-0 l-1 l-2)
  (uniq-gen y x)
  (absent (y zeta) (y l-1) (y l-2) (x l) (x l-0))
  (gen-st (pv self l-0) (pv self l-1) (pv self-0 l) (pv self-0 l-2))
  (facts (neq (exp (gen) upsilon) (gen)) (neq (exp (gen) zeta) (gen))
    (trans 7 1) (trans 5 1) (trans 4 1) (trans 2 1) (trans 7 0)
    (trans 5 0) (trans 4 0) (trans 2 0) (trans 6 1) (trans 3 1)
    (trans 6 0) (trans 3 0) (neq self self-0) (undisclosed l-0)
    (undisclosed l-2))
  (operation generalization deleted (6 0))
  (traces
    ((load priv-stor-2 (cat pt-8 (pv self-0 l-2)))
      (recv
        (sig (body self (exp (gen) l-1) (pubk "sig" self))
          (privk "sig" self)))
      (recv (cat na self self-0 (exp (gen) zeta)))
      (send
        (cat (exp (gen) y)
          (enc na nb self self-0
            (hash (exp (gen) (mul l-1 l-2)) (exp (gen) (mul y zeta))))))
      (recv nb))
    ((load priv-stor-0 (cat pt-3 (pv self l-0)))
      (recv
        (sig (body self-0 (exp (gen) l) (pubk "sig" self-0))
          (privk "sig" self-0)))
      (send (cat na-0 self self-0 (exp (gen) x)))
      (recv
        (cat (exp (gen) upsilon)
          (enc na-0 nb-0 self self-0
            (hash (exp (gen) (mul l l-0))
              (exp (gen) (mul x upsilon)))))) (send nb-0))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv self-0 l)))
      (send
        (sig (body self-0 (exp (gen) l) (pubk "sig" self-0))
          (privk "sig" self-0))))
    ((load priv-stor (cat pt-0 (pv self-0 l)))
      (stor priv-stor (cat pt-1 "nil")) (send l))
    ((load priv-stor-0 (cat pt-2 ignore-0))
      (stor priv-stor-0 (cat pt-3 (pv self l-0)))
      (send
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self))))
    ((load priv-stor-1 (cat pt-4 ignore-1))
      (stor priv-stor-1 (cat pt-5 (pv self l-1)))
      (send
        (sig (body self (exp (gen) l-1) (pubk "sig" self))
          (privk "sig" self))))
    ((load priv-stor-1 (cat pt-5 (pv self l-1)))
      (stor priv-stor-1 (cat pt-6 "nil")) (send l-1))
    ((load priv-stor-2 (cat pt-7 ignore-2))
      (stor priv-stor-2 (cat pt-8 (pv self-0 l-2)))
      (send
        (sig (body self-0 (exp (gen) l-2) (pubk "sig" self-0))
          (privk "sig" self-0)))))
  (label 1738)
  (parent 1335)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((a self) (b self-0) (la l-0) (lb l-2) (alpha l-1) (beta l) (y y)
        (zeta zeta) (na na) (nb nb) (priv-stor priv-stor-2) (pt pt-8)
        (x x) (upsilon upsilon) (na-0 na-0) (nb-0 nb-0)
        (priv-stor-0 priv-stor-0) (pt-0 pt-3))))
  (origs (l-2 (7 1)) (pt-8 (7 1)) (pt-6 (6 1)) (l-1 (5 1)) (pt-5 (5 1))
    (l-0 (4 1)) (pt-3 (4 1)) (pt-1 (3 1)) (l (2 1)) (pt-0 (2 1))
    (na-0 (1 2)) (nb (0 3))))

(comment "Nothing left to do")

(defprotocol dhcr-um diffie-hellman
  (defrole init
    (vars (la x rndx) (beta upsilon expt) (a b name) (na nb data)
      (priv-stor locn))
    (trace (load priv-stor (pv a la))
      (recv
        (sig (body b (exp (gen) beta) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) upsilon)
          (enc na nb a b
            (hash (exp (gen) (mul la beta))
              (exp (gen) (mul x upsilon)))))) (send nb))
    (uniq-orig na)
    (uniq-gen x)
    (absent (x la) (x beta))
    (assume (fact neq (exp (gen) upsilon) (gen)))
    (gen-st (pv a la)))
  (defrole resp
    (vars (lb y rndx) (alpha zeta expt) (a b name) (na nb data)
      (priv-stor locn))
    (trace (load priv-stor (pv b lb))
      (recv
        (sig (body a (exp (gen) alpha) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) zeta)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul lb alpha))
              (exp (gen) (mul y zeta)))))) (recv nb))
    (uniq-orig nb)
    (uniq-gen y)
    (absent (y lb) (y alpha) (y zeta))
    (assume (fact neq (exp (gen) zeta) (gen)))
    (gen-st (pv b lb)))
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
        (and (fact undisclosed l) (p "ltx-disclose" z 2)
          (p "ltx-disclose" "l" z l))
        (false))))
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
  (defgenrule assume-init-0
    (forall ((z strd) (upsilon expt))
      (implies (and (p "init" z 4) (p "init" "upsilon" z upsilon))
        (fact neq (exp (gen) upsilon) (gen)))))
  (defgenrule assume-resp-0
    (forall ((z strd) (zeta expt))
      (implies (and (p "resp" z 3) (p "resp" "zeta" z zeta))
        (fact neq (exp (gen) zeta) (gen)))))
  (defgenrule trRl_ltx-gen-at-1
    (forall ((z strd)) (implies (p "ltx-gen" z 2) (trans z 1))))
  (defgenrule trRl_ltx-gen-at-0
    (forall ((z strd)) (implies (p "ltx-gen" z 2) (trans z 0))))
  (defgenrule trRl_ltx-disclose-at-1
    (forall ((z strd)) (implies (p "ltx-disclose" z 2) (trans z 1))))
  (defgenrule trRl_ltx-disclose-at-0
    (forall ((z strd)) (implies (p "ltx-disclose" z 2) (trans z 0))))
  (defgenrule gen-st-init-0
    (forall ((z strd) (la rndx) (a name))
      (implies
        (and (p "init" z 1) (p "init" "la" z la) (p "init" "a" z a))
        (gen-st (pv a la)))))
  (defgenrule gen-st-resp-0
    (forall ((z strd) (lb rndx) (b name))
      (implies
        (and (p "resp" z 1) (p "resp" "lb" z lb) (p "resp" "b" z b))
        (gen-st (pv b lb)))))
  (defgenrule gen-st-ltx-disclose-0
    (forall ((z strd) (l rndx) (self name))
      (implies
        (and (p "ltx-disclose" z 1) (p "ltx-disclose" "l" z l)
          (p "ltx-disclose" "self" z self)) (gen-st (pv self l)))))
  (lang (sig sign) (body (tuple 3)) (pv (tuple 2))))

(defskeleton dhcr-um
  (vars (na nb data) (a b name) (pt pval) (priv-stor locn) (lb rndx)
    (alpha expt) (y rndx) (zeta expt))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (lb lb) (y y) (alpha alpha) (zeta zeta))
  (non-orig (privk "sig" a))
  (uniq-orig nb)
  (uniq-gen y)
  (absent (y lb) (y alpha) (y zeta))
  (facts (neq a b) (undisclosed lb) (undisclosed alpha))
  (traces
    ((load priv-stor (cat pt (pv b lb)))
      (recv
        (sig (body a (exp (gen) alpha) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) zeta)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul lb alpha))
              (exp (gen) (mul y zeta)))))) (recv nb)))
  (label 1741)
  (unrealized (0 1))
  (origs (nb (0 3)))
  (comment "Not closed under rules"))

(comment "Nothing left to do")

(defprotocol dhcr-um diffie-hellman
  (defrole init
    (vars (la x rndx) (beta upsilon expt) (a b name) (na nb data)
      (priv-stor locn))
    (trace (load priv-stor (pv a la))
      (recv
        (sig (body b (exp (gen) beta) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) upsilon)
          (enc na nb a b
            (hash (exp (gen) (mul la beta))
              (exp (gen) (mul x upsilon)))))) (send nb))
    (uniq-orig na)
    (uniq-gen x)
    (absent (x la) (x beta))
    (assume (fact neq (exp (gen) upsilon) (gen)))
    (gen-st (pv a la)))
  (defrole resp
    (vars (lb y rndx) (alpha zeta expt) (a b name) (na nb data)
      (priv-stor locn))
    (trace (load priv-stor (pv b lb))
      (recv
        (sig (body a (exp (gen) alpha) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) zeta)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul lb alpha))
              (exp (gen) (mul y zeta)))))) (recv nb))
    (uniq-orig nb)
    (uniq-gen y)
    (absent (y lb) (y alpha) (y zeta))
    (assume (fact neq (exp (gen) zeta) (gen)))
    (gen-st (pv b lb)))
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
        (and (fact undisclosed l) (p "ltx-disclose" z 2)
          (p "ltx-disclose" "l" z l))
        (false))))
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
  (defgenrule assume-init-0
    (forall ((z strd) (upsilon expt))
      (implies (and (p "init" z 4) (p "init" "upsilon" z upsilon))
        (fact neq (exp (gen) upsilon) (gen)))))
  (defgenrule assume-resp-0
    (forall ((z strd) (zeta expt))
      (implies (and (p "resp" z 3) (p "resp" "zeta" z zeta))
        (fact neq (exp (gen) zeta) (gen)))))
  (defgenrule trRl_ltx-gen-at-1
    (forall ((z strd)) (implies (p "ltx-gen" z 2) (trans z 1))))
  (defgenrule trRl_ltx-gen-at-0
    (forall ((z strd)) (implies (p "ltx-gen" z 2) (trans z 0))))
  (defgenrule trRl_ltx-disclose-at-1
    (forall ((z strd)) (implies (p "ltx-disclose" z 2) (trans z 1))))
  (defgenrule trRl_ltx-disclose-at-0
    (forall ((z strd)) (implies (p "ltx-disclose" z 2) (trans z 0))))
  (defgenrule gen-st-init-0
    (forall ((z strd) (la rndx) (a name))
      (implies
        (and (p "init" z 1) (p "init" "la" z la) (p "init" "a" z a))
        (gen-st (pv a la)))))
  (defgenrule gen-st-resp-0
    (forall ((z strd) (lb rndx) (b name))
      (implies
        (and (p "resp" z 1) (p "resp" "lb" z lb) (p "resp" "b" z b))
        (gen-st (pv b lb)))))
  (defgenrule gen-st-ltx-disclose-0
    (forall ((z strd) (l rndx) (self name))
      (implies
        (and (p "ltx-disclose" z 1) (p "ltx-disclose" "l" z l)
          (p "ltx-disclose" "self" z self)) (gen-st (pv self l)))))
  (lang (sig sign) (body (tuple 3)) (pv (tuple 2))))

(defskeleton dhcr-um
  (vars (na nb data) (a b name) (pt pval) (priv-stor locn) (lb rndx)
    (alpha expt) (y rndx) (zeta expt))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (lb lb) (y y) (alpha alpha) (zeta zeta))
  (non-orig (privk "sig" a))
  (uniq-orig nb)
  (uniq-gen y)
  (absent (y lb) (y alpha) (y zeta))
  (facts (neq a b) (undisclosed alpha))
  (traces
    ((load priv-stor (cat pt (pv b lb)))
      (recv
        (sig (body a (exp (gen) alpha) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) zeta)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul lb alpha))
              (exp (gen) (mul y zeta)))))) (recv nb)))
  (label 1776)
  (unrealized (0 1))
  (origs (nb (0 3)))
  (comment "Not closed under rules"))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn) (y rndx)
    (zeta expt) (l l-0 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (lb l) (y y) (alpha l-0) (zeta zeta))
  (defstrand ltx-gen 2 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l))
  (precedes ((1 1) (0 0)) ((1 1) (3 0)) ((2 2) (0 1)) ((3 2) (0 4)))
  (non-orig (privk "sig" a))
  (uniq-orig nb l l-0)
  (uniq-gen y)
  (absent (y zeta) (y l) (y l-0))
  (gen-st (pv b l))
  (facts (neq (exp (gen) zeta) (gen)) (trans 2 1) (trans 1 1)
    (trans 2 0) (trans 1 0) (trans 3 1) (trans 3 0) (neq a b)
    (undisclosed l-0))
  (operation generalization deleted (3 0))
  (traces
    ((load priv-stor (cat pt (pv b l)))
      (recv
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) zeta)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul y zeta))))))
      (recv nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv b l))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l-0)))
      (send
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor (cat pt (pv b l)))
      (stor priv-stor (cat pt-3 "nil")) (send l)))
  (label 1860)
  (parent 1776)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (lb l) (alpha l-0) (y y) (zeta zeta) (na na) (nb nb)
        (priv-stor priv-stor) (pt pt))))
  (origs (l-0 (2 1)) (pt-2 (2 1)) (pt-3 (3 1)) (l (1 1)) (pt (1 1))
    (nb (0 3))))

(comment "Nothing left to do")

(defprotocol dhcr-um diffie-hellman
  (defrole init
    (vars (la x rndx) (beta upsilon expt) (a b name) (na nb data)
      (priv-stor locn))
    (trace (load priv-stor (pv a la))
      (recv
        (sig (body b (exp (gen) beta) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) upsilon)
          (enc na nb a b
            (hash (exp (gen) (mul la beta))
              (exp (gen) (mul x upsilon)))))) (send nb))
    (uniq-orig na)
    (uniq-gen x)
    (absent (x la) (x beta))
    (assume (fact neq (exp (gen) upsilon) (gen)))
    (gen-st (pv a la)))
  (defrole resp
    (vars (lb y rndx) (alpha zeta expt) (a b name) (na nb data)
      (priv-stor locn))
    (trace (load priv-stor (pv b lb))
      (recv
        (sig (body a (exp (gen) alpha) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) zeta)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul lb alpha))
              (exp (gen) (mul y zeta)))))) (recv nb))
    (uniq-orig nb)
    (uniq-gen y)
    (absent (y lb) (y alpha) (y zeta))
    (assume (fact neq (exp (gen) zeta) (gen)))
    (gen-st (pv b lb)))
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
        (and (fact undisclosed l) (p "ltx-disclose" z 2)
          (p "ltx-disclose" "l" z l))
        (false))))
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
  (defgenrule assume-init-0
    (forall ((z strd) (upsilon expt))
      (implies (and (p "init" z 4) (p "init" "upsilon" z upsilon))
        (fact neq (exp (gen) upsilon) (gen)))))
  (defgenrule assume-resp-0
    (forall ((z strd) (zeta expt))
      (implies (and (p "resp" z 3) (p "resp" "zeta" z zeta))
        (fact neq (exp (gen) zeta) (gen)))))
  (defgenrule trRl_ltx-gen-at-1
    (forall ((z strd)) (implies (p "ltx-gen" z 2) (trans z 1))))
  (defgenrule trRl_ltx-gen-at-0
    (forall ((z strd)) (implies (p "ltx-gen" z 2) (trans z 0))))
  (defgenrule trRl_ltx-disclose-at-1
    (forall ((z strd)) (implies (p "ltx-disclose" z 2) (trans z 1))))
  (defgenrule trRl_ltx-disclose-at-0
    (forall ((z strd)) (implies (p "ltx-disclose" z 2) (trans z 0))))
  (defgenrule gen-st-init-0
    (forall ((z strd) (la rndx) (a name))
      (implies
        (and (p "init" z 1) (p "init" "la" z la) (p "init" "a" z a))
        (gen-st (pv a la)))))
  (defgenrule gen-st-resp-0
    (forall ((z strd) (lb rndx) (b name))
      (implies
        (and (p "resp" z 1) (p "resp" "lb" z lb) (p "resp" "b" z b))
        (gen-st (pv b lb)))))
  (defgenrule gen-st-ltx-disclose-0
    (forall ((z strd) (l rndx) (self name))
      (implies
        (and (p "ltx-disclose" z 1) (p "ltx-disclose" "l" z l)
          (p "ltx-disclose" "self" z self)) (gen-st (pv self l)))))
  (lang (sig sign) (body (tuple 3)) (pv (tuple 2))))

(defskeleton dhcr-um
  (vars (na nb data) (a b name) (pt pval) (priv-stor locn) (lb y rndx)
    (alpha zeta expt))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (lb lb) (y y) (alpha alpha) (zeta zeta))
  (non-orig (privk "sig" a))
  (uniq-orig nb)
  (uniq-gen y)
  (absent (y lb) (y alpha) (y zeta))
  (facts (neq a b) (undisclosed lb))
  (traces
    ((load priv-stor (cat pt (pv b lb)))
      (recv
        (sig (body a (exp (gen) alpha) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) zeta)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul lb alpha))
              (exp (gen) (mul y zeta)))))) (recv nb)))
  (label 1883)
  (unrealized (0 1))
  (origs (nb (0 3)))
  (comment "Not closed under rules"))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a self name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn) (y rndx)
    (zeta expt) (l l-0 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b self)
    (priv-stor priv-stor-0) (lb l-0) (y y) (alpha l) (zeta zeta))
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
  (absent (y zeta) (y l) (y l-0))
  (gen-st (pv a l) (pv self l-0))
  (facts (neq (exp (gen) zeta) (gen)) (trans 3 1) (trans 1 1)
    (trans 3 0) (trans 1 0) (trans 2 1) (trans 2 0) (neq a self)
    (undisclosed l-0))
  (operation generalization deleted (2 0))
  (traces
    ((load priv-stor-0 (cat pt-3 (pv self l-0)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a self (exp (gen) zeta)))
      (send
        (cat (exp (gen) y)
          (enc na nb a self
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul y zeta))))))
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
  (label 1964)
  (parent 1883)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b self) (lb l-0) (y y) (alpha l) (zeta zeta) (na na)
        (nb nb) (priv-stor priv-stor-0) (pt pt-3))))
  (origs (l-0 (3 1)) (pt-3 (3 1)) (pt-1 (2 1)) (l (1 1)) (pt-0 (1 1))
    (nb (0 3))))

(comment "Nothing left to do")

(defprotocol dhcr-um diffie-hellman
  (defrole init
    (vars (la x rndx) (beta upsilon expt) (a b name) (na nb data)
      (priv-stor locn))
    (trace (load priv-stor (pv a la))
      (recv
        (sig (body b (exp (gen) beta) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) upsilon)
          (enc na nb a b
            (hash (exp (gen) (mul la beta))
              (exp (gen) (mul x upsilon)))))) (send nb))
    (uniq-orig na)
    (uniq-gen x)
    (absent (x la) (x beta))
    (assume (fact neq (exp (gen) upsilon) (gen)))
    (gen-st (pv a la)))
  (defrole resp
    (vars (lb y rndx) (alpha zeta expt) (a b name) (na nb data)
      (priv-stor locn))
    (trace (load priv-stor (pv b lb))
      (recv
        (sig (body a (exp (gen) alpha) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) zeta)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul lb alpha))
              (exp (gen) (mul y zeta)))))) (recv nb))
    (uniq-orig nb)
    (uniq-gen y)
    (absent (y lb) (y alpha) (y zeta))
    (assume (fact neq (exp (gen) zeta) (gen)))
    (gen-st (pv b lb)))
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
        (and (fact undisclosed l) (p "ltx-disclose" z 2)
          (p "ltx-disclose" "l" z l))
        (false))))
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
  (defgenrule assume-init-0
    (forall ((z strd) (upsilon expt))
      (implies (and (p "init" z 4) (p "init" "upsilon" z upsilon))
        (fact neq (exp (gen) upsilon) (gen)))))
  (defgenrule assume-resp-0
    (forall ((z strd) (zeta expt))
      (implies (and (p "resp" z 3) (p "resp" "zeta" z zeta))
        (fact neq (exp (gen) zeta) (gen)))))
  (defgenrule trRl_ltx-gen-at-1
    (forall ((z strd)) (implies (p "ltx-gen" z 2) (trans z 1))))
  (defgenrule trRl_ltx-gen-at-0
    (forall ((z strd)) (implies (p "ltx-gen" z 2) (trans z 0))))
  (defgenrule trRl_ltx-disclose-at-1
    (forall ((z strd)) (implies (p "ltx-disclose" z 2) (trans z 1))))
  (defgenrule trRl_ltx-disclose-at-0
    (forall ((z strd)) (implies (p "ltx-disclose" z 2) (trans z 0))))
  (defgenrule gen-st-init-0
    (forall ((z strd) (la rndx) (a name))
      (implies
        (and (p "init" z 1) (p "init" "la" z la) (p "init" "a" z a))
        (gen-st (pv a la)))))
  (defgenrule gen-st-resp-0
    (forall ((z strd) (lb rndx) (b name))
      (implies
        (and (p "resp" z 1) (p "resp" "lb" z lb) (p "resp" "b" z b))
        (gen-st (pv b lb)))))
  (defgenrule gen-st-ltx-disclose-0
    (forall ((z strd) (l rndx) (self name))
      (implies
        (and (p "ltx-disclose" z 1) (p "ltx-disclose" "l" z l)
          (p "ltx-disclose" "self" z self)) (gen-st (pv self l)))))
  (lang (sig sign) (body (tuple 3)) (pv (tuple 2))))

(defskeleton dhcr-um
  (vars (na nb data) (a b name) (pt pval) (priv-stor locn) (lb y rndx)
    (alpha zeta expt))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (lb lb) (y y) (alpha alpha) (zeta zeta))
  (non-orig (privk "sig" a))
  (uniq-orig nb)
  (uniq-gen y)
  (absent (y lb) (y alpha) (y zeta))
  (facts (neq a b))
  (traces
    ((load priv-stor (cat pt (pv b lb)))
      (recv
        (sig (body a (exp (gen) alpha) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) zeta)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul lb alpha))
              (exp (gen) (mul y zeta)))))) (recv nb)))
  (label 1987)
  (unrealized (0 1))
  (origs (nb (0 3)))
  (comment "Not closed under rules"))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a self name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn) (y rndx)
    (zeta expt) (l l-0 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b self)
    (priv-stor priv-stor-0) (lb l-0) (y y) (alpha l) (zeta zeta))
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
  (absent (y zeta) (y l) (y l-0))
  (gen-st (pv a l) (pv self l-0))
  (facts (neq (exp (gen) zeta) (gen)) (trans 3 1) (trans 1 1)
    (trans 3 0) (trans 1 0) (trans 2 1) (trans 2 0) (neq a self))
  (operation generalization deleted (2 0))
  (traces
    ((load priv-stor-0 (cat pt-3 (pv self l-0)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a self (exp (gen) zeta)))
      (send
        (cat (exp (gen) y)
          (enc na nb a self
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul y zeta))))))
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
  (label 2137)
  (parent 1987)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b self) (lb l-0) (y y) (alpha l) (zeta zeta) (na na)
        (nb nb) (priv-stor priv-stor-0) (pt pt-3))))
  (origs (l-0 (3 1)) (pt-3 (3 1)) (pt-1 (2 1)) (l (1 1)) (pt-0 (1 1))
    (nb (0 3))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn) (y rndx)
    (zeta expt) (l l-0 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (lb l) (y y) (alpha l-0) (zeta zeta))
  (defstrand ltx-gen 2 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l))
  (precedes ((1 1) (0 0)) ((1 1) (3 0)) ((2 2) (0 1)) ((3 2) (0 4)))
  (non-orig (privk "sig" a))
  (uniq-orig nb l l-0)
  (uniq-gen y)
  (absent (y zeta) (y l) (y l-0))
  (gen-st (pv b l))
  (facts (neq (exp (gen) zeta) (gen)) (trans 2 1) (trans 1 1)
    (trans 2 0) (trans 1 0) (trans 3 1) (trans 3 0) (neq a b))
  (operation generalization deleted (3 0))
  (traces
    ((load priv-stor (cat pt (pv b l)))
      (recv
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) zeta)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul y zeta))))))
      (recv nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv b l))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l-0)))
      (send
        (sig (body a (exp (gen) l-0) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor (cat pt (pv b l)))
      (stor priv-stor (cat pt-3 "nil")) (send l)))
  (label 2140)
  (parent 1987)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (lb l) (y y) (alpha l-0) (zeta zeta) (na na) (nb nb)
        (priv-stor priv-stor) (pt pt))))
  (origs (l-0 (2 1)) (pt-2 (2 1)) (pt-3 (3 1)) (l (1 1)) (pt (1 1))
    (nb (0 3))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn) (y rndx)
    (zeta expt) (l l-0 rndx))
  (defstrand resp 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (lb l-0) (y y) (alpha l) (zeta zeta))
  (defstrand ltx-gen 2 (ignore ignore) (self b) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 3 (ignore ignore-0) (self a)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-disclose 3 (self b) (priv-stor priv-stor) (l l-0))
  (precedes ((1 1) (0 0)) ((1 1) (3 0)) ((2 2) (0 1)) ((3 2) (0 4)))
  (non-orig (privk "sig" a))
  (uniq-orig nb l l-0)
  (uniq-gen y)
  (absent (y zeta) (y l) (y l-0))
  (gen-st (pv a l) (pv b l-0))
  (facts (neq (exp (gen) zeta) (gen)) (trans 2 1) (trans 1 1)
    (trans 2 0) (trans 1 0) (trans 3 1) (trans 3 0) (neq a b))
  (operation generalization deleted (3 0))
  (traces
    ((load priv-stor (cat pt (pv b l-0)))
      (recv (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) zeta)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul y zeta))))))
      (recv nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv b l-0))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv a l)))
      (send
        (sig (body a (exp (gen) l) (pubk "sig" a)) (privk "sig" a))))
    ((load priv-stor (cat pt (pv b l-0)))
      (stor priv-stor (cat pt-3 "nil")) (send l-0)))
  (label 2235)
  (parent 1987)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (lb l-0) (y y) (alpha l) (zeta zeta) (na na) (nb nb)
        (priv-stor priv-stor) (pt pt))))
  (origs (pt-3 (3 1)) (l (2 1)) (pt-2 (2 1)) (l-0 (1 1)) (pt (1 1))
    (nb (0 3))))

(comment "Nothing left to do")

(defprotocol dhcr-um diffie-hellman
  (defrole init
    (vars (la x rndx) (beta upsilon expt) (a b name) (na nb data)
      (priv-stor locn))
    (trace (load priv-stor (pv a la))
      (recv
        (sig (body b (exp (gen) beta) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) upsilon)
          (enc na nb a b
            (hash (exp (gen) (mul la beta))
              (exp (gen) (mul x upsilon)))))) (send nb))
    (uniq-orig na)
    (uniq-gen x)
    (absent (x la) (x beta))
    (assume (fact neq (exp (gen) upsilon) (gen)))
    (gen-st (pv a la)))
  (defrole resp
    (vars (lb y rndx) (alpha zeta expt) (a b name) (na nb data)
      (priv-stor locn))
    (trace (load priv-stor (pv b lb))
      (recv
        (sig (body a (exp (gen) alpha) (pubk "sig" a)) (privk "sig" a)))
      (recv (cat na a b (exp (gen) zeta)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul lb alpha))
              (exp (gen) (mul y zeta)))))) (recv nb))
    (uniq-orig nb)
    (uniq-gen y)
    (absent (y lb) (y alpha) (y zeta))
    (assume (fact neq (exp (gen) zeta) (gen)))
    (gen-st (pv b lb)))
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
        (and (fact undisclosed l) (p "ltx-disclose" z 2)
          (p "ltx-disclose" "l" z l))
        (false))))
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
  (defgenrule assume-init-0
    (forall ((z strd) (upsilon expt))
      (implies (and (p "init" z 4) (p "init" "upsilon" z upsilon))
        (fact neq (exp (gen) upsilon) (gen)))))
  (defgenrule assume-resp-0
    (forall ((z strd) (zeta expt))
      (implies (and (p "resp" z 3) (p "resp" "zeta" z zeta))
        (fact neq (exp (gen) zeta) (gen)))))
  (defgenrule trRl_ltx-gen-at-1
    (forall ((z strd)) (implies (p "ltx-gen" z 2) (trans z 1))))
  (defgenrule trRl_ltx-gen-at-0
    (forall ((z strd)) (implies (p "ltx-gen" z 2) (trans z 0))))
  (defgenrule trRl_ltx-disclose-at-1
    (forall ((z strd)) (implies (p "ltx-disclose" z 2) (trans z 1))))
  (defgenrule trRl_ltx-disclose-at-0
    (forall ((z strd)) (implies (p "ltx-disclose" z 2) (trans z 0))))
  (defgenrule gen-st-init-0
    (forall ((z strd) (la rndx) (a name))
      (implies
        (and (p "init" z 1) (p "init" "la" z la) (p "init" "a" z a))
        (gen-st (pv a la)))))
  (defgenrule gen-st-resp-0
    (forall ((z strd) (lb rndx) (b name))
      (implies
        (and (p "resp" z 1) (p "resp" "lb" z lb) (p "resp" "b" z b))
        (gen-st (pv b lb)))))
  (defgenrule gen-st-ltx-disclose-0
    (forall ((z strd) (l rndx) (self name))
      (implies
        (and (p "ltx-disclose" z 1) (p "ltx-disclose" "l" z l)
          (p "ltx-disclose" "self" z self)) (gen-st (pv self l)))))
  (lang (sig sign) (body (tuple 3)) (pv (tuple 2))))

(defskeleton dhcr-um
  (vars (ignore mesg) (na nb data) (a b self name) (pt pt-0 pt-1 pval)
    (priv-stor priv-stor-0 locn) (la beta x rndx) (upsilon expt))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (la la) (x x) (beta beta) (upsilon upsilon))
  (defstrand ltx-gen 3 (ignore ignore) (self self)
    (priv-stor priv-stor-0) (l beta))
  (uniq-orig na beta)
  (uniq-gen x)
  (absent (x la) (x beta))
  (facts (neq a b))
  (traces
    ((load priv-stor (cat pt (pv a la)))
      (recv
        (sig (body b (exp (gen) beta) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) upsilon)
          (enc na nb a b
            (hash (exp (gen) (mul la beta))
              (exp (gen) (mul x upsilon)))))))
    ((load priv-stor-0 (cat pt-0 ignore))
      (stor priv-stor-0 (cat pt-1 (pv self beta)))
      (send
        (sig (body self (exp (gen) beta) (pubk "sig" self))
          (privk "sig" self)))))
  (label 2236)
  (unrealized (0 1) (0 3))
  (origs (pt-1 (1 1)) (na (0 2)) (beta (1 1)))
  (comment "Not closed under rules"))

(defskeleton dhcr-um
  (vars (ignore mesg) (na nb data) (b self name) (pt pt-0 pt-1 pval)
    (priv-stor locn) (x rndx) (upsilon expt) (l rndx))
  (defstrand init 4 (na na) (nb nb) (a self) (b b) (priv-stor priv-stor)
    (la l) (x x) (beta l) (upsilon upsilon))
  (defstrand ltx-gen 3 (ignore ignore) (self self) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor) (l l))
  (precedes ((1 1) (0 0)) ((1 1) (2 0)) ((2 2) (0 1)))
  (uniq-orig na l)
  (uniq-gen x)
  (absent (x l))
  (gen-st (pv self l))
  (facts (neq (exp (gen) upsilon) (gen)) (trans 1 1) (trans 1 0)
    (trans 2 1) (trans 2 0) (neq self b))
  (operation generalization deleted (2 0))
  (traces
    ((load priv-stor (cat pt-0 (pv self l)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na self b (exp (gen) x)))
      (recv
        (cat (exp (gen) upsilon)
          (enc na nb self b
            (hash (exp (gen) (mul l l)) (exp (gen) (mul x upsilon)))))))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv self l)))
      (send
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self))))
    ((load priv-stor (cat pt-0 (pv self l)))
      (stor priv-stor (cat pt-1 "nil")) (send l)))
  (label 2283)
  (parent 2236)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((la l) (beta l) (a self) (b b) (x x) (upsilon upsilon) (na na)
        (nb nb) (priv-stor priv-stor) (pt pt-0) (self self)
        (priv-stor-0 priv-stor) (ignore ignore) (pt-0 pt) (pt-1 pt-0))))
  (origs (pt-1 (2 1)) (l (1 1)) (pt-0 (1 1)) (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (self self-0 name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn)
    (lb l x y rndx))
  (defstrand init 4 (na na) (nb nb) (a self-0) (b self)
    (priv-stor priv-stor-0) (la l) (x x) (beta lb) (upsilon y))
  (defstrand ltx-gen 3 (ignore ignore) (self self) (priv-stor priv-stor)
    (l lb))
  (defstrand resp 4 (na na) (nb nb) (a self-0) (b self)
    (priv-stor priv-stor) (lb lb) (y y) (alpha l) (zeta x))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self-0)
    (priv-stor priv-stor-0) (l l))
  (precedes ((0 2) (2 2)) ((1 1) (2 0)) ((1 2) (0 1)) ((2 3) (0 3))
    ((3 1) (0 0)) ((3 2) (2 1)))
  (uniq-orig na nb lb l)
  (uniq-gen x y)
  (absent (x lb) (x l) (y lb) (y l) (y x))
  (gen-st (pv self lb) (pv self-0 l))
  (facts (neq (exp (gen) y) (gen)) (neq (exp (gen) x) (gen)) (trans 3 1)
    (trans 1 1) (trans 3 0) (trans 1 0) (neq self-0 self))
  (operation nonce-test (displaced 4 2 resp 4) (exp (gen) y-0) (0 3))
  (traces
    ((load priv-stor-0 (cat pt-2 (pv self-0 l)))
      (recv
        (sig (body self (exp (gen) lb) (pubk "sig" self))
          (privk "sig" self))) (send (cat na self-0 self (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb self-0 self
            (hash (exp (gen) (mul lb l)) (exp (gen) (mul x y)))))))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv self lb)))
      (send
        (sig (body self (exp (gen) lb) (pubk "sig" self))
          (privk "sig" self))))
    ((load priv-stor (cat pt-0 (pv self lb)))
      (recv
        (sig (body self-0 (exp (gen) l) (pubk "sig" self-0))
          (privk "sig" self-0)))
      (recv (cat na self-0 self (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb self-0 self
            (hash (exp (gen) (mul lb l)) (exp (gen) (mul x y)))))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv self-0 l)))
      (send
        (sig (body self-0 (exp (gen) l) (pubk "sig" self-0))
          (privk "sig" self-0)))))
  (label 2309)
  (parent 2236)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((la l) (beta lb) (a self-0) (b self) (x x) (upsilon y) (na na)
        (nb nb) (priv-stor priv-stor-0) (pt pt-2) (self self)
        (priv-stor-0 priv-stor) (ignore ignore) (pt-0 pt) (pt-1 pt-0))))
  (origs (nb (2 3)) (l (3 1)) (pt-2 (3 1)) (lb (1 1)) (pt-0 (1 1))
    (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore mesg) (na nb data) (b self name) (pt pt-0 pt-1 pval)
    (priv-stor locn) (x rndx) (upsilon expt) (l rndx))
  (defstrand init 4 (na na) (nb nb) (a self) (b b) (priv-stor priv-stor)
    (la l) (x x) (beta l) (upsilon upsilon))
  (defstrand ltx-gen 3 (ignore ignore) (self self) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor) (l l))
  (precedes ((1 1) (0 0)) ((1 1) (2 0)) ((1 2) (0 1)) ((2 2) (0 3)))
  (uniq-orig na l)
  (uniq-gen x)
  (absent (x l))
  (gen-st (pv self l))
  (facts (neq (exp (gen) upsilon) (gen)) (trans 1 1) (trans 1 0)
    (trans 2 1) (trans 2 0) (neq self b))
  (operation generalization deleted (2 0))
  (traces
    ((load priv-stor (cat pt-0 (pv self l)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na self b (exp (gen) x)))
      (recv
        (cat (exp (gen) upsilon)
          (enc na nb self b
            (hash (exp (gen) (mul l l)) (exp (gen) (mul x upsilon)))))))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv self l)))
      (send
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self))))
    ((load priv-stor (cat pt-0 (pv self l)))
      (stor priv-stor (cat pt-1 "nil")) (send l)))
  (label 2646)
  (parent 2236)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((la l) (beta l) (a self) (b b) (x x) (upsilon upsilon) (na na)
        (nb nb) (priv-stor priv-stor) (pt pt-0) (self self)
        (priv-stor-0 priv-stor) (ignore ignore) (pt-0 pt) (pt-1 pt-0))))
  (origs (pt-1 (2 1)) (l (1 1)) (pt-0 (1 1)) (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (b self self-0 name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn) (x rndx)
    (upsilon expt) (l l-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a self-0) (b b)
    (priv-stor priv-stor-0) (la l-0) (x x) (beta l) (upsilon upsilon))
  (defstrand ltx-gen 3 (ignore ignore) (self self) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor) (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self-0)
    (priv-stor priv-stor-0) (l l-0))
  (precedes ((1 1) (2 0)) ((1 2) (0 1)) ((2 2) (0 3)) ((3 1) (0 0))
    ((3 2) (0 3)))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0))
  (gen-st (pv self l) (pv self-0 l-0))
  (facts (neq (exp (gen) upsilon) (gen)) (trans 3 1) (trans 1 1)
    (trans 3 0) (trans 1 0) (trans 2 1) (trans 2 0) (neq self-0 b))
  (operation generalization deleted (2 0))
  (traces
    ((load priv-stor-0 (cat pt-3 (pv self-0 l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na self-0 b (exp (gen) x)))
      (recv
        (cat (exp (gen) upsilon)
          (enc na nb self-0 b
            (hash (exp (gen) (mul l l-0))
              (exp (gen) (mul x upsilon)))))))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv self l)))
      (send
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self))))
    ((load priv-stor (cat pt-0 (pv self l)))
      (stor priv-stor (cat pt-1 "nil")) (send l))
    ((load priv-stor-0 (cat pt-2 ignore-0))
      (stor priv-stor-0 (cat pt-3 (pv self-0 l-0)))
      (send
        (sig (body self-0 (exp (gen) l-0) (pubk "sig" self-0))
          (privk "sig" self-0)))))
  (label 2727)
  (parent 2236)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((la l-0) (beta l) (a self-0) (b b) (x x) (upsilon upsilon)
        (na na) (nb nb) (priv-stor priv-stor-0) (pt pt-3) (self self)
        (priv-stor-0 priv-stor) (ignore ignore) (pt-0 pt) (pt-1 pt-0))))
  (origs (l-0 (3 1)) (pt-3 (3 1)) (pt-1 (2 1)) (l (1 1)) (pt-0 (1 1))
    (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a b self name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn) (x rndx)
    (upsilon expt) (l l-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (la l) (x x) (beta l-0) (upsilon upsilon))
  (defstrand ltx-gen 3 (ignore ignore) (self self)
    (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-gen 2 (ignore ignore-0) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (precedes ((1 2) (0 1)) ((2 1) (0 0)) ((2 1) (3 0)) ((3 2) (0 3)))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0))
  (gen-st (pv a l))
  (facts (neq (exp (gen) upsilon) (gen)) (trans 2 1) (trans 1 1)
    (trans 2 0) (trans 1 0) (trans 3 1) (trans 3 0) (neq a b))
  (operation generalization deleted (3 0))
  (traces
    ((load priv-stor (cat pt (pv a l)))
      (recv
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) upsilon)
          (enc na nb a b
            (hash (exp (gen) (mul l l-0))
              (exp (gen) (mul x upsilon)))))))
    ((load priv-stor-0 (cat pt-0 ignore))
      (stor priv-stor-0 (cat pt-1 (pv self l-0)))
      (send
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self))))
    ((load priv-stor (cat pt-2 ignore-0))
      (stor priv-stor (cat pt (pv a l))))
    ((load priv-stor (cat pt (pv a l)))
      (stor priv-stor (cat pt-3 "nil")) (send l)))
  (label 2730)
  (parent 2236)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((la l) (beta l-0) (a a) (b b) (x x) (upsilon upsilon) (na na)
        (nb nb) (priv-stor priv-stor) (pt pt) (self self)
        (priv-stor-0 priv-stor-0) (ignore ignore) (pt-0 pt-0)
        (pt-1 pt-1))))
  (origs (l-0 (1 1)) (pt-1 (1 1)) (pt-3 (3 1)) (l (2 1)) (pt (2 1))
    (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a self self-0 name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (lb l x y rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b self-0)
    (priv-stor priv-stor) (la l) (x x) (beta lb) (upsilon y))
  (defstrand ltx-gen 3 (ignore ignore) (self self)
    (priv-stor priv-stor-0) (l lb))
  (defstrand ltx-gen 2 (ignore ignore-0) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (precedes ((1 2) (0 1)) ((2 1) (0 0)) ((2 1) (3 0)) ((3 2) (0 3)))
  (uniq-orig na lb l)
  (uniq-gen x y)
  (absent (x lb) (x l) (y lb) (y l) (y x))
  (gen-st (pv a l) (pv self lb))
  (facts (neq (exp (gen) y) (gen)) (trans 2 1) (trans 1 1) (trans 2 0)
    (trans 1 0) (trans 3 1) (trans 3 0) (neq a self-0))
  (operation generalization separated self-0)
  (traces
    ((load priv-stor (cat pt (pv a l)))
      (recv
        (sig (body self-0 (exp (gen) lb) (pubk "sig" self-0))
          (privk "sig" self-0))) (send (cat na a self-0 (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a self-0
            (hash (exp (gen) (mul lb l)) (exp (gen) (mul x y)))))))
    ((load priv-stor-0 (cat pt-0 ignore))
      (stor priv-stor-0 (cat pt-1 (pv self lb)))
      (send
        (sig (body self (exp (gen) lb) (pubk "sig" self))
          (privk "sig" self))))
    ((load priv-stor (cat pt-2 ignore-0))
      (stor priv-stor (cat pt (pv a l))))
    ((load priv-stor (cat pt (pv a l)))
      (stor priv-stor (cat pt-3 "nil")) (send l)))
  (label 3102)
  (parent 2236)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((la l) (beta lb) (a a) (b self-0) (x x) (upsilon y) (na na)
        (nb nb) (priv-stor priv-stor) (pt pt) (self self)
        (priv-stor-0 priv-stor-0) (ignore ignore) (pt-0 pt-0)
        (pt-1 pt-1))))
  (origs (pt-3 (3 1)) (lb (1 1)) (pt-1 (1 1)) (l (2 1)) (pt (2 1))
    (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (self self-0 self-1 name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (lb l x y rndx))
  (defstrand init 4 (na na) (nb nb) (a self-0) (b self-1)
    (priv-stor priv-stor-0) (la l) (x x) (beta lb) (upsilon y))
  (defstrand ltx-gen 3 (ignore ignore) (self self) (priv-stor priv-stor)
    (l lb))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor) (l lb))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self-0)
    (priv-stor priv-stor-0) (l l))
  (precedes ((1 1) (2 0)) ((2 2) (0 1)) ((3 1) (0 0)) ((3 2) (0 3)))
  (uniq-orig na lb l)
  (uniq-gen x y)
  (absent (x lb) (x l) (y lb) (y l) (y x))
  (gen-st (pv self lb) (pv self-0 l))
  (facts (neq (exp (gen) y) (gen)) (trans 3 1) (trans 1 1) (trans 3 0)
    (trans 1 0) (trans 2 1) (trans 2 0) (neq self-0 self-1))
  (operation generalization separated self-1)
  (traces
    ((load priv-stor-0 (cat pt-3 (pv self-0 l)))
      (recv
        (sig (body self-1 (exp (gen) lb) (pubk "sig" self-1))
          (privk "sig" self-1)))
      (send (cat na self-0 self-1 (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb self-0 self-1
            (hash (exp (gen) (mul lb l)) (exp (gen) (mul x y)))))))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv self lb)))
      (send
        (sig (body self (exp (gen) lb) (pubk "sig" self))
          (privk "sig" self))))
    ((load priv-stor (cat pt-0 (pv self lb)))
      (stor priv-stor (cat pt-1 "nil")) (send lb))
    ((load priv-stor-0 (cat pt-2 ignore-0))
      (stor priv-stor-0 (cat pt-3 (pv self-0 l)))
      (send
        (sig (body self-0 (exp (gen) l) (pubk "sig" self-0))
          (privk "sig" self-0)))))
  (label 3198)
  (parent 2236)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((la l) (beta lb) (a self-0) (b self-1) (x x) (upsilon y) (na na)
        (nb nb) (priv-stor priv-stor-0) (pt pt-3) (self self)
        (priv-stor-0 priv-stor) (ignore ignore) (pt-0 pt) (pt-1 pt-0))))
  (origs (l (3 1)) (pt-3 (3 1)) (lb (1 1)) (pt-0 (1 1)) (pt-1 (2 1))
    (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (b self self-0 name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn) (x rndx)
    (upsilon expt) (l l-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a self-0) (b b)
    (priv-stor priv-stor-0) (la l-0) (x x) (beta l) (upsilon upsilon))
  (defstrand ltx-gen 3 (ignore ignore) (self self) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor) (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self-0)
    (priv-stor priv-stor-0) (l l-0))
  (precedes ((1 1) (2 0)) ((2 2) (0 1)) ((3 1) (0 0)) ((3 2) (0 3)))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0))
  (gen-st (pv self l) (pv self-0 l-0))
  (facts (neq (exp (gen) upsilon) (gen)) (trans 3 1) (trans 1 1)
    (trans 3 0) (trans 1 0) (trans 2 1) (trans 2 0) (neq self-0 b))
  (operation generalization deleted (3 0))
  (traces
    ((load priv-stor-0 (cat pt-3 (pv self-0 l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na self-0 b (exp (gen) x)))
      (recv
        (cat (exp (gen) upsilon)
          (enc na nb self-0 b
            (hash (exp (gen) (mul l l-0))
              (exp (gen) (mul x upsilon)))))))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv self l)))
      (send
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self))))
    ((load priv-stor (cat pt-0 (pv self l)))
      (stor priv-stor (cat pt-1 "nil")) (send l))
    ((load priv-stor-0 (cat pt-2 ignore-0))
      (stor priv-stor-0 (cat pt-3 (pv self-0 l-0)))
      (send
        (sig (body self-0 (exp (gen) l-0) (pubk "sig" self-0))
          (privk "sig" self-0)))))
  (label 3635)
  (parent 2236)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((la l-0) (beta l) (a self-0) (b b) (x x) (upsilon upsilon)
        (na na) (nb nb) (priv-stor priv-stor-0) (pt pt-3) (self self)
        (priv-stor-0 priv-stor) (ignore ignore) (pt-0 pt) (pt-1 pt-0))))
  (origs (l-0 (3 1)) (pt-3 (3 1)) (pt-1 (2 1)) (pt-0 (1 1)) (na (0 2))
    (l (1 1))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a b self name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn) (x rndx)
    (upsilon expt) (l l-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (la l-0) (x x) (beta l) (upsilon upsilon))
  (defstrand ltx-gen 3 (ignore ignore) (self self)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-gen 2 (ignore ignore-0) (self a) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l-0))
  (precedes ((1 2) (0 1)) ((2 1) (0 0)) ((2 1) (3 0)) ((3 2) (0 3)))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0))
  (gen-st (pv a l-0) (pv self l))
  (facts (neq (exp (gen) upsilon) (gen)) (trans 2 1) (trans 1 1)
    (trans 2 0) (trans 1 0) (trans 3 1) (trans 3 0) (neq a b))
  (operation generalization deleted (3 0))
  (traces
    ((load priv-stor (cat pt (pv a l-0)))
      (recv (sig (body b (exp (gen) l) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) upsilon)
          (enc na nb a b
            (hash (exp (gen) (mul l l-0))
              (exp (gen) (mul x upsilon)))))))
    ((load priv-stor-0 (cat pt-0 ignore))
      (stor priv-stor-0 (cat pt-1 (pv self l)))
      (send
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self))))
    ((load priv-stor (cat pt-2 ignore-0))
      (stor priv-stor (cat pt (pv a l-0))))
    ((load priv-stor (cat pt (pv a l-0)))
      (stor priv-stor (cat pt-3 "nil")) (send l-0)))
  (label 3842)
  (parent 2236)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((la l-0) (beta l) (a a) (b b) (x x) (upsilon upsilon) (na na)
        (nb nb) (priv-stor priv-stor) (pt pt) (self self)
        (priv-stor-0 priv-stor-0) (ignore ignore) (pt-0 pt-0)
        (pt-1 pt-1))))
  (origs (pt-3 (3 1)) (l (1 1)) (pt-1 (1 1)) (l-0 (2 1)) (pt (2 1))
    (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a b self name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (priv-stor priv-stor-0 locn)
    (x rndx) (upsilon expt) (l l-0 rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (la l) (x x) (beta l-0) (upsilon upsilon))
  (defstrand ltx-gen 3 (ignore ignore) (self self)
    (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-gen 2 (ignore ignore-0) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (precedes ((1 1) (3 0)) ((2 1) (0 0)) ((2 1) (4 0)) ((3 2) (0 1))
    ((4 2) (0 3)))
  (uniq-orig na l l-0)
  (uniq-gen x)
  (absent (x l) (x l-0))
  (gen-st (pv a l) (pv self l-0))
  (facts (neq (exp (gen) upsilon) (gen)) (trans 2 1) (trans 1 1)
    (trans 2 0) (trans 1 0) (trans 4 1) (trans 3 1) (trans 4 0)
    (trans 3 0) (neq a b))
  (operation generalization weakened ((1 2) (0 3)))
  (traces
    ((load priv-stor (cat pt (pv a l)))
      (recv
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) upsilon)
          (enc na nb a b
            (hash (exp (gen) (mul l l-0))
              (exp (gen) (mul x upsilon)))))))
    ((load priv-stor-0 (cat pt-0 ignore))
      (stor priv-stor-0 (cat pt-1 (pv self l-0)))
      (send
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self))))
    ((load priv-stor (cat pt-2 ignore-0))
      (stor priv-stor (cat pt (pv a l))))
    ((load priv-stor-0 (cat pt-1 (pv self l-0)))
      (stor priv-stor-0 (cat pt-3 "nil")) (send l-0))
    ((load priv-stor (cat pt (pv a l)))
      (stor priv-stor (cat pt-4 "nil")) (send l)))
  (label 3940)
  (parent 2236)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((la l) (beta l-0) (a a) (b b) (x x) (upsilon upsilon) (na na)
        (nb nb) (priv-stor priv-stor) (pt pt) (self self)
        (priv-stor-0 priv-stor-0) (ignore ignore) (pt-0 pt-0)
        (pt-1 pt-1))))
  (origs (l-0 (1 1)) (pt-1 (1 1)) (pt-4 (4 1)) (pt-3 (3 1)) (l (2 1))
    (pt (2 1)) (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a self self-0 name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (priv-stor priv-stor-0 locn)
    (lb l x y rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b self-0)
    (priv-stor priv-stor) (la l) (x x) (beta lb) (upsilon y))
  (defstrand ltx-gen 3 (ignore ignore) (self self)
    (priv-stor priv-stor-0) (l lb))
  (defstrand ltx-gen 2 (ignore ignore-0) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor-0) (l lb))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (precedes ((1 1) (3 0)) ((2 1) (0 0)) ((2 1) (4 0)) ((3 2) (0 1))
    ((4 2) (0 3)))
  (uniq-orig na lb l)
  (uniq-gen x y)
  (absent (x lb) (x l) (y lb) (y l) (y x))
  (gen-st (pv a l) (pv self lb))
  (facts (neq (exp (gen) y) (gen)) (trans 2 1) (trans 1 1) (trans 2 0)
    (trans 1 0) (trans 4 1) (trans 3 1) (trans 4 0) (trans 3 0)
    (neq a self-0))
  (operation generalization separated self-0)
  (traces
    ((load priv-stor (cat pt (pv a l)))
      (recv
        (sig (body self-0 (exp (gen) lb) (pubk "sig" self-0))
          (privk "sig" self-0))) (send (cat na a self-0 (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a self-0
            (hash (exp (gen) (mul lb l)) (exp (gen) (mul x y)))))))
    ((load priv-stor-0 (cat pt-0 ignore))
      (stor priv-stor-0 (cat pt-1 (pv self lb)))
      (send
        (sig (body self (exp (gen) lb) (pubk "sig" self))
          (privk "sig" self))))
    ((load priv-stor (cat pt-2 ignore-0))
      (stor priv-stor (cat pt (pv a l))))
    ((load priv-stor-0 (cat pt-1 (pv self lb)))
      (stor priv-stor-0 (cat pt-3 "nil")) (send lb))
    ((load priv-stor (cat pt (pv a l)))
      (stor priv-stor (cat pt-4 "nil")) (send l)))
  (label 4086)
  (parent 2236)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((la l) (beta lb) (a a) (b self-0) (x x) (upsilon y) (na na)
        (nb nb) (priv-stor priv-stor) (pt pt) (self self)
        (priv-stor-0 priv-stor-0) (ignore ignore) (pt-0 pt-0)
        (pt-1 pt-1))))
  (origs (pt-4 (4 1)) (lb (1 1)) (pt-1 (1 1)) (pt-3 (3 1)) (l (2 1))
    (pt (2 1)) (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (b self b-0 name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (l lb x y rndx))
  (defstrand init 4 (na na) (nb nb) (a self) (b b-0)
    (priv-stor priv-stor) (la l) (x x) (beta l) (upsilon y))
  (defstrand ltx-gen 3 (ignore ignore) (self self) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 2 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l lb))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor) (l l))
  (precedes ((1 1) (0 0)) ((1 1) (3 0)) ((1 2) (0 1)) ((3 2) (0 3)))
  (uniq-orig na l lb)
  (uniq-gen x y)
  (absent (x l) (y (mul l l (rec lb))) (y lb) (y x))
  (gen-st (pv b lb) (pv self l))
  (facts (neq (exp (gen) y) (gen)) (trans 2 1) (trans 1 1) (trans 2 0)
    (trans 1 0) (trans 3 1) (trans 3 0) (neq self b-0))
  (operation generalization separated b-0)
  (traces
    ((load priv-stor (cat pt-0 (pv self l)))
      (recv
        (sig (body b-0 (exp (gen) l) (pubk "sig" b-0))
          (privk "sig" b-0))) (send (cat na self b-0 (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb self b-0
            (hash (exp (gen) (mul l l)) (exp (gen) (mul x y)))))))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv self l)))
      (send
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self))))
    ((load priv-stor-0 (cat pt-2 ignore-0))
      (stor priv-stor-0 (cat pt-1 (pv b lb))))
    ((load priv-stor (cat pt-0 (pv self l)))
      (stor priv-stor (cat pt-3 "nil")) (send l)))
  (label 4410)
  (parent 2236)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((la l) (beta l) (a self) (b b-0) (x x) (upsilon y) (na na)
        (nb nb) (priv-stor priv-stor) (pt pt-0) (self self)
        (priv-stor-0 priv-stor) (ignore ignore) (pt-0 pt) (pt-1 pt-0))))
  (origs (pt-3 (3 1)) (l (1 1)) (pt-0 (1 1)) (lb (2 1)) (pt-1 (2 1))
    (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 ignore-1 mesg) (na nb data)
    (b self self-0 b-0 name) (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (l l-0 lb x y rndx))
  (defstrand init 4 (na na) (nb nb) (a self-0) (b b-0)
    (priv-stor priv-stor-1) (la l-0) (x x) (beta l) (upsilon y))
  (defstrand ltx-gen 3 (ignore ignore) (self self) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 2 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l lb))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor) (l l))
  (defstrand ltx-gen 3 (ignore ignore-1) (self self-0)
    (priv-stor priv-stor-1) (l l-0))
  (precedes ((1 1) (3 0)) ((1 2) (0 1)) ((3 2) (0 3)) ((4 1) (0 0))
    ((4 2) (0 3)))
  (uniq-orig na l l-0 lb)
  (uniq-gen x y)
  (absent (x l) (x l-0) (y (mul l l-0 (rec lb))) (y lb) (y x))
  (gen-st (pv b lb) (pv self l) (pv self-0 l-0))
  (facts (neq (exp (gen) y) (gen)) (trans 4 1) (trans 2 1) (trans 1 1)
    (trans 4 0) (trans 2 0) (trans 1 0) (trans 3 1) (trans 3 0)
    (neq self-0 b-0))
  (operation generalization separated b-0)
  (traces
    ((load priv-stor-1 (cat pt-5 (pv self-0 l-0)))
      (recv
        (sig (body b-0 (exp (gen) l) (pubk "sig" b-0))
          (privk "sig" b-0))) (send (cat na self-0 b-0 (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb self-0 b-0
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y)))))))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv self l)))
      (send
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self))))
    ((load priv-stor-0 (cat pt-2 ignore-0))
      (stor priv-stor-0 (cat pt-1 (pv b lb))))
    ((load priv-stor (cat pt-0 (pv self l)))
      (stor priv-stor (cat pt-3 "nil")) (send l))
    ((load priv-stor-1 (cat pt-4 ignore-1))
      (stor priv-stor-1 (cat pt-5 (pv self-0 l-0)))
      (send
        (sig (body self-0 (exp (gen) l-0) (pubk "sig" self-0))
          (privk "sig" self-0)))))
  (label 4413)
  (parent 2236)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((la l-0) (beta l) (a self-0) (b b-0) (x x) (upsilon y) (na na)
        (nb nb) (priv-stor priv-stor-1) (pt pt-5) (self self)
        (priv-stor-0 priv-stor) (ignore ignore) (pt-0 pt) (pt-1 pt-0))))
  (origs (l-0 (4 1)) (pt-5 (4 1)) (pt-3 (3 1)) (lb (2 1)) (pt-1 (2 1))
    (l (1 1)) (pt-0 (1 1)) (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 ignore-1 mesg) (na nb data) (a b self b-0 name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (l l-0 lb x y rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b-0) (priv-stor priv-stor)
    (la l) (x x) (beta l-0) (upsilon y))
  (defstrand ltx-gen 3 (ignore ignore) (self self)
    (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-gen 2 (ignore ignore-0) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 2 (ignore ignore-1) (self b)
    (priv-stor priv-stor-1) (l lb))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (precedes ((1 2) (0 1)) ((2 1) (0 0)) ((2 1) (4 0)) ((4 2) (0 3)))
  (uniq-orig na l l-0 lb)
  (uniq-gen x y)
  (absent (x l) (x l-0) (y (mul l l-0 (rec lb))) (y lb) (y x))
  (gen-st (pv a l) (pv b lb))
  (facts (neq (exp (gen) y) (gen)) (trans 3 1) (trans 2 1) (trans 1 1)
    (trans 3 0) (trans 2 0) (trans 1 0) (trans 4 1) (trans 4 0)
    (neq a b-0))
  (operation generalization separated b-0)
  (traces
    ((load priv-stor (cat pt (pv a l)))
      (recv
        (sig (body b-0 (exp (gen) l-0) (pubk "sig" b-0))
          (privk "sig" b-0))) (send (cat na a b-0 (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b-0
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y)))))))
    ((load priv-stor-0 (cat pt-0 ignore))
      (stor priv-stor-0 (cat pt-1 (pv self l-0)))
      (send
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self))))
    ((load priv-stor (cat pt-2 ignore-0))
      (stor priv-stor (cat pt (pv a l))))
    ((load priv-stor-1 (cat pt-4 ignore-1))
      (stor priv-stor-1 (cat pt-3 (pv b lb))))
    ((load priv-stor (cat pt (pv a l)))
      (stor priv-stor (cat pt-5 "nil")) (send l)))
  (label 4417)
  (parent 2236)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((la l) (beta l-0) (a a) (b b-0) (x x) (upsilon y) (na na) (nb nb)
        (priv-stor priv-stor) (pt pt) (self self)
        (priv-stor-0 priv-stor-0) (ignore ignore) (pt-0 pt-0)
        (pt-1 pt-1))))
  (origs (l-0 (1 1)) (pt-1 (1 1)) (pt-5 (4 1)) (lb (3 1)) (pt-3 (3 1))
    (l (2 1)) (pt (2 1)) (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a self self-0 name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (lb l x rndx) (w expt) (y rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b self-0)
    (priv-stor priv-stor) (la l) (x x) (beta lb) (upsilon (mul w y)))
  (defstrand ltx-gen 3 (ignore ignore) (self self)
    (priv-stor priv-stor-0) (l lb))
  (defstrand ltx-gen 2 (ignore ignore-0) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (deflistener (cat (exp (gen) y) w))
  (precedes ((1 2) (0 1)) ((2 1) (0 0)) ((2 1) (3 0)) ((3 2) (0 3)))
  (uniq-orig na lb l)
  (uniq-gen x y)
  (absent (x lb) (x l) (y lb) (y l) (y (mul x w)))
  (precur (4 0))
  (gen-st (pv a l) (pv self lb))
  (facts (neq (exp (gen) (mul w y)) (gen)) (trans 2 1) (trans 1 1)
    (trans 2 0) (trans 1 0) (trans 3 1) (trans 3 0) (neq a self-0))
  (operation generalization separated self-0)
  (traces
    ((load priv-stor (cat pt (pv a l)))
      (recv
        (sig (body self-0 (exp (gen) lb) (pubk "sig" self-0))
          (privk "sig" self-0))) (send (cat na a self-0 (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul w y))
          (enc na nb a self-0
            (hash (exp (gen) (mul lb l)) (exp (gen) (mul x w y)))))))
    ((load priv-stor-0 (cat pt-0 ignore))
      (stor priv-stor-0 (cat pt-1 (pv self lb)))
      (send
        (sig (body self (exp (gen) lb) (pubk "sig" self))
          (privk "sig" self))))
    ((load priv-stor (cat pt-2 ignore-0))
      (stor priv-stor (cat pt (pv a l))))
    ((load priv-stor (cat pt (pv a l)))
      (stor priv-stor (cat pt-3 "nil")) (send l))
    ((recv (cat (exp (gen) y) w))))
  (label 4561)
  (parent 2236)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((la l) (beta lb) (a a) (b self-0) (x x) (upsilon (mul w y))
        (na na) (nb nb) (priv-stor priv-stor) (pt pt) (self self)
        (priv-stor-0 priv-stor-0) (ignore ignore) (pt-0 pt-0)
        (pt-1 pt-1))))
  (origs (pt-3 (3 1)) (lb (1 1)) (pt-1 (1 1)) (l (2 1)) (pt (2 1))
    (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (self self-0 self-1 name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (lb l x rndx) (w expt) (y rndx))
  (defstrand init 4 (na na) (nb nb) (a self-0) (b self-1)
    (priv-stor priv-stor-0) (la l) (x x) (beta lb) (upsilon (mul w y)))
  (defstrand ltx-gen 3 (ignore ignore) (self self) (priv-stor priv-stor)
    (l lb))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor) (l lb))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self-0)
    (priv-stor priv-stor-0) (l l))
  (deflistener (cat (exp (gen) y) w))
  (precedes ((1 1) (2 0)) ((2 2) (0 1)) ((3 1) (0 0)) ((3 2) (0 3)))
  (uniq-orig na lb l)
  (uniq-gen x y)
  (absent (x lb) (x l) (y lb) (y l) (y (mul x w)))
  (precur (4 0))
  (gen-st (pv self lb) (pv self-0 l))
  (facts (neq (exp (gen) (mul w y)) (gen)) (trans 3 1) (trans 1 1)
    (trans 3 0) (trans 1 0) (trans 2 1) (trans 2 0) (neq self-0 self-1))
  (operation generalization separated self-1)
  (traces
    ((load priv-stor-0 (cat pt-3 (pv self-0 l)))
      (recv
        (sig (body self-1 (exp (gen) lb) (pubk "sig" self-1))
          (privk "sig" self-1)))
      (send (cat na self-0 self-1 (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul w y))
          (enc na nb self-0 self-1
            (hash (exp (gen) (mul lb l)) (exp (gen) (mul x w y)))))))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv self lb)))
      (send
        (sig (body self (exp (gen) lb) (pubk "sig" self))
          (privk "sig" self))))
    ((load priv-stor (cat pt-0 (pv self lb)))
      (stor priv-stor (cat pt-1 "nil")) (send lb))
    ((load priv-stor-0 (cat pt-2 ignore-0))
      (stor priv-stor-0 (cat pt-3 (pv self-0 l)))
      (send
        (sig (body self-0 (exp (gen) l) (pubk "sig" self-0))
          (privk "sig" self-0)))) ((recv (cat (exp (gen) y) w))))
  (label 4567)
  (parent 2236)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((la l) (beta lb) (a self-0) (b self-1) (x x) (upsilon (mul w y))
        (na na) (nb nb) (priv-stor priv-stor-0) (pt pt-3) (self self)
        (priv-stor-0 priv-stor) (ignore ignore) (pt-0 pt) (pt-1 pt-0))))
  (origs (l (3 1)) (pt-3 (3 1)) (lb (1 1)) (pt-0 (1 1)) (pt-1 (2 1))
    (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 ignore-1 mesg) (na nb data)
    (b self self-0 b-0 name) (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (l l-0 lb x y rndx))
  (defstrand init 4 (na na) (nb nb) (a self-0) (b b-0)
    (priv-stor priv-stor-1) (la l-0) (x x) (beta l) (upsilon y))
  (defstrand ltx-gen 3 (ignore ignore) (self self) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor) (l l))
  (defstrand ltx-gen 2 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l lb))
  (defstrand ltx-gen 3 (ignore ignore-1) (self self-0)
    (priv-stor priv-stor-1) (l l-0))
  (precedes ((1 1) (2 0)) ((2 2) (0 1)) ((4 1) (0 0)) ((4 2) (0 3)))
  (uniq-orig na l l-0 lb)
  (uniq-gen x y)
  (absent (x l) (x l-0) (y (mul l l-0 (rec lb))) (y lb) (y x))
  (gen-st (pv b lb) (pv self l) (pv self-0 l-0))
  (facts (neq (exp (gen) y) (gen)) (trans 4 1) (trans 3 1) (trans 1 1)
    (trans 4 0) (trans 3 0) (trans 1 0) (trans 2 1) (trans 2 0)
    (neq self-0 b-0))
  (operation generalization separated b-0)
  (traces
    ((load priv-stor-1 (cat pt-5 (pv self-0 l-0)))
      (recv
        (sig (body b-0 (exp (gen) l) (pubk "sig" b-0))
          (privk "sig" b-0))) (send (cat na self-0 b-0 (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb self-0 b-0
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y)))))))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv self l)))
      (send
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self))))
    ((load priv-stor (cat pt-0 (pv self l)))
      (stor priv-stor (cat pt-1 "nil")) (send l))
    ((load priv-stor-0 (cat pt-3 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b lb))))
    ((load priv-stor-1 (cat pt-4 ignore-1))
      (stor priv-stor-1 (cat pt-5 (pv self-0 l-0)))
      (send
        (sig (body self-0 (exp (gen) l-0) (pubk "sig" self-0))
          (privk "sig" self-0)))))
  (label 4569)
  (parent 2236)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((la l-0) (beta l) (a self-0) (b b-0) (x x) (upsilon y) (na na)
        (nb nb) (priv-stor priv-stor-1) (pt pt-5) (self self)
        (priv-stor-0 priv-stor) (ignore ignore) (pt-0 pt) (pt-1 pt-0))))
  (origs (l-0 (4 1)) (pt-5 (4 1)) (pt-1 (2 1)) (lb (3 1)) (pt-2 (3 1))
    (pt-0 (1 1)) (na (0 2)) (l (1 1))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 ignore-1 mesg) (na nb data) (a b self b-0 name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (l l-0 lb x y rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b-0) (priv-stor priv-stor)
    (la l-0) (x x) (beta l) (upsilon y))
  (defstrand ltx-gen 3 (ignore ignore) (self self)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-gen 2 (ignore ignore-0) (self a) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 2 (ignore ignore-1) (self b)
    (priv-stor priv-stor-1) (l lb))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l-0))
  (precedes ((1 2) (0 1)) ((2 1) (0 0)) ((2 1) (4 0)) ((4 2) (0 3)))
  (uniq-orig na l l-0 lb)
  (uniq-gen x y)
  (absent (x l) (x l-0) (y (mul l l-0 (rec lb))) (y lb) (y x))
  (gen-st (pv a l-0) (pv b lb) (pv self l))
  (facts (neq (exp (gen) y) (gen)) (trans 3 1) (trans 2 1) (trans 1 1)
    (trans 3 0) (trans 2 0) (trans 1 0) (trans 4 1) (trans 4 0)
    (neq a b-0))
  (operation generalization separated b-0)
  (traces
    ((load priv-stor (cat pt (pv a l-0)))
      (recv
        (sig (body b-0 (exp (gen) l) (pubk "sig" b-0))
          (privk "sig" b-0))) (send (cat na a b-0 (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b-0
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y)))))))
    ((load priv-stor-0 (cat pt-0 ignore))
      (stor priv-stor-0 (cat pt-1 (pv self l)))
      (send
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self))))
    ((load priv-stor (cat pt-2 ignore-0))
      (stor priv-stor (cat pt (pv a l-0))))
    ((load priv-stor-1 (cat pt-4 ignore-1))
      (stor priv-stor-1 (cat pt-3 (pv b lb))))
    ((load priv-stor (cat pt (pv a l-0)))
      (stor priv-stor (cat pt-5 "nil")) (send l-0)))
  (label 4581)
  (parent 2236)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((la l-0) (beta l) (a a) (b b-0) (x x) (upsilon y) (na na) (nb nb)
        (priv-stor priv-stor) (pt pt) (self self)
        (priv-stor-0 priv-stor-0) (ignore ignore) (pt-0 pt-0)
        (pt-1 pt-1))))
  (origs (pt-5 (4 1)) (lb (3 1)) (pt-3 (3 1)) (l (1 1)) (pt-1 (1 1))
    (l-0 (2 1)) (pt (2 1)) (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 ignore-1 mesg) (na nb data) (a b self b-0 name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pt-6 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (l l-0 lb x y rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b-0) (priv-stor priv-stor)
    (la l) (x x) (beta l-0) (upsilon y))
  (defstrand ltx-gen 3 (ignore ignore) (self self)
    (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-gen 2 (ignore ignore-0) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-gen 2 (ignore ignore-1) (self b)
    (priv-stor priv-stor-1) (l lb))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (precedes ((1 1) (3 0)) ((2 1) (0 0)) ((2 1) (5 0)) ((3 2) (0 1))
    ((5 2) (0 3)))
  (uniq-orig na l l-0 lb)
  (uniq-gen x y)
  (absent (x l) (x l-0) (y (mul l l-0 (rec lb))) (y lb) (y x))
  (gen-st (pv a l) (pv b lb) (pv self l-0))
  (facts (neq (exp (gen) y) (gen)) (trans 4 1) (trans 2 1) (trans 1 1)
    (trans 4 0) (trans 2 0) (trans 1 0) (trans 5 1) (trans 3 1)
    (trans 5 0) (trans 3 0) (neq a b-0))
  (operation generalization separated b-0)
  (traces
    ((load priv-stor (cat pt (pv a l)))
      (recv
        (sig (body b-0 (exp (gen) l-0) (pubk "sig" b-0))
          (privk "sig" b-0))) (send (cat na a b-0 (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb a b-0
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x y)))))))
    ((load priv-stor-0 (cat pt-0 ignore))
      (stor priv-stor-0 (cat pt-1 (pv self l-0)))
      (send
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self))))
    ((load priv-stor (cat pt-2 ignore-0))
      (stor priv-stor (cat pt (pv a l))))
    ((load priv-stor-0 (cat pt-1 (pv self l-0)))
      (stor priv-stor-0 (cat pt-3 "nil")) (send l-0))
    ((load priv-stor-1 (cat pt-5 ignore-1))
      (stor priv-stor-1 (cat pt-4 (pv b lb))))
    ((load priv-stor (cat pt (pv a l)))
      (stor priv-stor (cat pt-6 "nil")) (send l)))
  (label 4587)
  (parent 2236)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((la l) (beta l-0) (a a) (b b-0) (x x) (upsilon y) (na na) (nb nb)
        (priv-stor priv-stor) (pt pt) (self self)
        (priv-stor-0 priv-stor-0) (ignore ignore) (pt-0 pt-0)
        (pt-1 pt-1))))
  (origs (l-0 (1 1)) (pt-1 (1 1)) (pt-6 (5 1)) (lb (4 1)) (pt-4 (4 1))
    (pt-3 (3 1)) (l (2 1)) (pt (2 1)) (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a self self-0 name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (priv-stor priv-stor-0 locn)
    (lb l x rndx) (w expt) (y rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b self-0)
    (priv-stor priv-stor) (la l) (x x) (beta lb) (upsilon (mul w y)))
  (defstrand ltx-gen 3 (ignore ignore) (self self)
    (priv-stor priv-stor-0) (l lb))
  (defstrand ltx-gen 2 (ignore ignore-0) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor-0) (l lb))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (deflistener (cat (exp (gen) y) w))
  (precedes ((1 1) (3 0)) ((2 1) (0 0)) ((2 1) (4 0)) ((3 2) (0 1))
    ((4 2) (0 3)))
  (uniq-orig na lb l)
  (uniq-gen x y)
  (absent (x lb) (x l) (y lb) (y l) (y (mul x w)))
  (precur (5 0))
  (gen-st (pv a l) (pv self lb))
  (facts (neq (exp (gen) (mul w y)) (gen)) (trans 2 1) (trans 1 1)
    (trans 2 0) (trans 1 0) (trans 4 1) (trans 3 1) (trans 4 0)
    (trans 3 0) (neq a self-0))
  (operation generalization separated self-0)
  (traces
    ((load priv-stor (cat pt (pv a l)))
      (recv
        (sig (body self-0 (exp (gen) lb) (pubk "sig" self-0))
          (privk "sig" self-0))) (send (cat na a self-0 (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul w y))
          (enc na nb a self-0
            (hash (exp (gen) (mul lb l)) (exp (gen) (mul x w y)))))))
    ((load priv-stor-0 (cat pt-0 ignore))
      (stor priv-stor-0 (cat pt-1 (pv self lb)))
      (send
        (sig (body self (exp (gen) lb) (pubk "sig" self))
          (privk "sig" self))))
    ((load priv-stor (cat pt-2 ignore-0))
      (stor priv-stor (cat pt (pv a l))))
    ((load priv-stor-0 (cat pt-1 (pv self lb)))
      (stor priv-stor-0 (cat pt-3 "nil")) (send lb))
    ((load priv-stor (cat pt (pv a l)))
      (stor priv-stor (cat pt-4 "nil")) (send l))
    ((recv (cat (exp (gen) y) w))))
  (label 4613)
  (parent 2236)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((la l) (beta lb) (a a) (b self-0) (x x) (upsilon (mul w y))
        (na na) (nb nb) (priv-stor priv-stor) (pt pt) (self self)
        (priv-stor-0 priv-stor-0) (ignore ignore) (pt-0 pt-0)
        (pt-1 pt-1))))
  (origs (pt-4 (4 1)) (lb (1 1)) (pt-1 (1 1)) (pt-3 (3 1)) (l (2 1))
    (pt (2 1)) (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (b self b-0 name)
    (pt pt-0 pt-1 pt-2 pt-3 pval) (priv-stor priv-stor-0 locn)
    (l lb x rndx) (w expt) (y rndx))
  (defstrand init 4 (na na) (nb nb) (a self) (b b-0)
    (priv-stor priv-stor) (la l) (x x) (beta l) (upsilon (mul w y)))
  (defstrand ltx-gen 3 (ignore ignore) (self self) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 2 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l lb))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor) (l l))
  (deflistener (cat (exp (gen) y) w))
  (precedes ((1 1) (0 0)) ((1 1) (3 0)) ((1 2) (0 1)) ((3 2) (0 3)))
  (uniq-orig na l lb)
  (uniq-gen x y)
  (absent (x l) (y (mul l l (rec lb))) (y lb) (y (mul x w)))
  (precur (4 0))
  (gen-st (pv b lb) (pv self l))
  (facts (neq (exp (gen) (mul w y)) (gen)) (trans 2 1) (trans 1 1)
    (trans 2 0) (trans 1 0) (trans 3 1) (trans 3 0) (neq self b-0))
  (operation generalization separated b-0)
  (traces
    ((load priv-stor (cat pt-0 (pv self l)))
      (recv
        (sig (body b-0 (exp (gen) l) (pubk "sig" b-0))
          (privk "sig" b-0))) (send (cat na self b-0 (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul w y))
          (enc na nb self b-0
            (hash (exp (gen) (mul l l)) (exp (gen) (mul x w y)))))))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv self l)))
      (send
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self))))
    ((load priv-stor-0 (cat pt-2 ignore-0))
      (stor priv-stor-0 (cat pt-1 (pv b lb))))
    ((load priv-stor (cat pt-0 (pv self l)))
      (stor priv-stor (cat pt-3 "nil")) (send l))
    ((recv (cat (exp (gen) y) w))))
  (label 4617)
  (parent 2236)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((la l) (beta l) (a self) (b b-0) (x x) (upsilon (mul w y))
        (na na) (nb nb) (priv-stor priv-stor) (pt pt-0) (self self)
        (priv-stor-0 priv-stor) (ignore ignore) (pt-0 pt) (pt-1 pt-0))))
  (origs (pt-3 (3 1)) (l (1 1)) (pt-0 (1 1)) (lb (2 1)) (pt-1 (2 1))
    (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 ignore-1 mesg) (na nb data) (a b self b-0 name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (l l-0 lb x rndx) (w expt)
    (y rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b-0) (priv-stor priv-stor)
    (la l) (x x) (beta l-0) (upsilon (mul w y)))
  (defstrand ltx-gen 3 (ignore ignore) (self self)
    (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-gen 2 (ignore ignore-0) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 2 (ignore ignore-1) (self b)
    (priv-stor priv-stor-1) (l lb))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (deflistener (cat (exp (gen) y) w))
  (precedes ((1 2) (0 1)) ((2 1) (0 0)) ((2 1) (4 0)) ((4 2) (0 3)))
  (uniq-orig na l l-0 lb)
  (uniq-gen x y)
  (absent (x l) (x l-0) (y (mul l l-0 (rec lb))) (y lb) (y (mul x w)))
  (precur (5 0))
  (gen-st (pv a l) (pv b lb))
  (facts (neq (exp (gen) (mul w y)) (gen)) (trans 3 1) (trans 2 1)
    (trans 1 1) (trans 3 0) (trans 2 0) (trans 1 0) (trans 4 1)
    (trans 4 0) (neq a b-0))
  (operation generalization separated b-0)
  (traces
    ((load priv-stor (cat pt (pv a l)))
      (recv
        (sig (body b-0 (exp (gen) l-0) (pubk "sig" b-0))
          (privk "sig" b-0))) (send (cat na a b-0 (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul w y))
          (enc na nb a b-0
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x w y)))))))
    ((load priv-stor-0 (cat pt-0 ignore))
      (stor priv-stor-0 (cat pt-1 (pv self l-0)))
      (send
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self))))
    ((load priv-stor (cat pt-2 ignore-0))
      (stor priv-stor (cat pt (pv a l))))
    ((load priv-stor-1 (cat pt-4 ignore-1))
      (stor priv-stor-1 (cat pt-3 (pv b lb))))
    ((load priv-stor (cat pt (pv a l)))
      (stor priv-stor (cat pt-5 "nil")) (send l))
    ((recv (cat (exp (gen) y) w))))
  (label 4625)
  (parent 2236)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((la l) (beta l-0) (a a) (b b-0) (x x) (upsilon (mul w y)) (na na)
        (nb nb) (priv-stor priv-stor) (pt pt) (self self)
        (priv-stor-0 priv-stor-0) (ignore ignore) (pt-0 pt-0)
        (pt-1 pt-1))))
  (origs (l-0 (1 1)) (pt-1 (1 1)) (pt-5 (4 1)) (lb (3 1)) (pt-3 (3 1))
    (l (2 1)) (pt (2 1)) (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 ignore-1 mesg) (na nb data)
    (b self self-0 b-0 name) (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (l l-0 lb x rndx) (w expt)
    (y rndx))
  (defstrand init 4 (na na) (nb nb) (a self-0) (b b-0)
    (priv-stor priv-stor-1) (la l-0) (x x) (beta l) (upsilon (mul w y)))
  (defstrand ltx-gen 3 (ignore ignore) (self self) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 2 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l lb))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor) (l l))
  (defstrand ltx-gen 3 (ignore ignore-1) (self self-0)
    (priv-stor priv-stor-1) (l l-0))
  (deflistener (cat (exp (gen) y) w))
  (precedes ((1 1) (3 0)) ((1 2) (0 1)) ((3 2) (0 3)) ((4 1) (0 0))
    ((4 2) (0 3)))
  (uniq-orig na l l-0 lb)
  (uniq-gen x y)
  (absent (x l) (x l-0) (y (mul l l-0 (rec lb))) (y lb) (y (mul x w)))
  (precur (5 0))
  (gen-st (pv b lb) (pv self l) (pv self-0 l-0))
  (facts (neq (exp (gen) (mul w y)) (gen)) (trans 4 1) (trans 2 1)
    (trans 1 1) (trans 4 0) (trans 2 0) (trans 1 0) (trans 3 1)
    (trans 3 0) (neq self-0 b-0))
  (operation generalization separated b-0)
  (traces
    ((load priv-stor-1 (cat pt-5 (pv self-0 l-0)))
      (recv
        (sig (body b-0 (exp (gen) l) (pubk "sig" b-0))
          (privk "sig" b-0))) (send (cat na self-0 b-0 (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul w y))
          (enc na nb self-0 b-0
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x w y)))))))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv self l)))
      (send
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self))))
    ((load priv-stor-0 (cat pt-2 ignore-0))
      (stor priv-stor-0 (cat pt-1 (pv b lb))))
    ((load priv-stor (cat pt-0 (pv self l)))
      (stor priv-stor (cat pt-3 "nil")) (send l))
    ((load priv-stor-1 (cat pt-4 ignore-1))
      (stor priv-stor-1 (cat pt-5 (pv self-0 l-0)))
      (send
        (sig (body self-0 (exp (gen) l-0) (pubk "sig" self-0))
          (privk "sig" self-0)))) ((recv (cat (exp (gen) y) w))))
  (label 4628)
  (parent 2236)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((la l-0) (beta l) (a self-0) (b b-0) (x x) (upsilon (mul w y))
        (na na) (nb nb) (priv-stor priv-stor-1) (pt pt-5) (self self)
        (priv-stor-0 priv-stor) (ignore ignore) (pt-0 pt) (pt-1 pt-0))))
  (origs (l-0 (4 1)) (pt-5 (4 1)) (pt-3 (3 1)) (lb (2 1)) (pt-1 (2 1))
    (l (1 1)) (pt-0 (1 1)) (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 ignore-1 mesg) (na nb data)
    (b self self-0 b-0 name) (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (l l-0 lb x rndx) (w expt)
    (y rndx))
  (defstrand init 4 (na na) (nb nb) (a self-0) (b b-0)
    (priv-stor priv-stor-1) (la l-0) (x x) (beta l) (upsilon (mul w y)))
  (defstrand ltx-gen 3 (ignore ignore) (self self) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor) (l l))
  (defstrand ltx-gen 2 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l lb))
  (defstrand ltx-gen 3 (ignore ignore-1) (self self-0)
    (priv-stor priv-stor-1) (l l-0))
  (deflistener (cat (exp (gen) y) w))
  (precedes ((1 1) (2 0)) ((2 2) (0 1)) ((4 1) (0 0)) ((4 2) (0 3)))
  (uniq-orig na l l-0 lb)
  (uniq-gen x y)
  (absent (x l) (x l-0) (y (mul l l-0 (rec lb))) (y lb) (y (mul x w)))
  (precur (5 0))
  (gen-st (pv b lb) (pv self l) (pv self-0 l-0))
  (facts (neq (exp (gen) (mul w y)) (gen)) (trans 4 1) (trans 3 1)
    (trans 1 1) (trans 4 0) (trans 3 0) (trans 1 0) (trans 2 1)
    (trans 2 0) (neq self-0 b-0))
  (operation generalization separated b-0)
  (traces
    ((load priv-stor-1 (cat pt-5 (pv self-0 l-0)))
      (recv
        (sig (body b-0 (exp (gen) l) (pubk "sig" b-0))
          (privk "sig" b-0))) (send (cat na self-0 b-0 (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul w y))
          (enc na nb self-0 b-0
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x w y)))))))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv self l)))
      (send
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self))))
    ((load priv-stor (cat pt-0 (pv self l)))
      (stor priv-stor (cat pt-1 "nil")) (send l))
    ((load priv-stor-0 (cat pt-3 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b lb))))
    ((load priv-stor-1 (cat pt-4 ignore-1))
      (stor priv-stor-1 (cat pt-5 (pv self-0 l-0)))
      (send
        (sig (body self-0 (exp (gen) l-0) (pubk "sig" self-0))
          (privk "sig" self-0)))) ((recv (cat (exp (gen) y) w))))
  (label 4636)
  (parent 2236)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((la l-0) (beta l) (a self-0) (b b-0) (x x) (upsilon (mul w y))
        (na na) (nb nb) (priv-stor priv-stor-1) (pt pt-5) (self self)
        (priv-stor-0 priv-stor) (ignore ignore) (pt-0 pt) (pt-1 pt-0))))
  (origs (l-0 (4 1)) (pt-5 (4 1)) (pt-1 (2 1)) (lb (3 1)) (pt-2 (3 1))
    (pt-0 (1 1)) (na (0 2)) (l (1 1))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 ignore-1 mesg) (na nb data) (a b self b-0 name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (l l-0 lb x rndx) (w expt)
    (y rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b-0) (priv-stor priv-stor)
    (la l-0) (x x) (beta l) (upsilon (mul w y)))
  (defstrand ltx-gen 3 (ignore ignore) (self self)
    (priv-stor priv-stor-0) (l l))
  (defstrand ltx-gen 2 (ignore ignore-0) (self a) (priv-stor priv-stor)
    (l l-0))
  (defstrand ltx-gen 2 (ignore ignore-1) (self b)
    (priv-stor priv-stor-1) (l lb))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l-0))
  (deflistener (cat (exp (gen) y) w))
  (precedes ((1 2) (0 1)) ((2 1) (0 0)) ((2 1) (4 0)) ((4 2) (0 3)))
  (uniq-orig na l l-0 lb)
  (uniq-gen x y)
  (absent (x l) (x l-0) (y (mul l l-0 (rec lb))) (y lb) (y (mul x w)))
  (precur (5 0))
  (gen-st (pv a l-0) (pv b lb) (pv self l))
  (facts (neq (exp (gen) (mul w y)) (gen)) (trans 3 1) (trans 2 1)
    (trans 1 1) (trans 3 0) (trans 2 0) (trans 1 0) (trans 4 1)
    (trans 4 0) (neq a b-0))
  (operation generalization separated b-0)
  (traces
    ((load priv-stor (cat pt (pv a l-0)))
      (recv
        (sig (body b-0 (exp (gen) l) (pubk "sig" b-0))
          (privk "sig" b-0))) (send (cat na a b-0 (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul w y))
          (enc na nb a b-0
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x w y)))))))
    ((load priv-stor-0 (cat pt-0 ignore))
      (stor priv-stor-0 (cat pt-1 (pv self l)))
      (send
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self))))
    ((load priv-stor (cat pt-2 ignore-0))
      (stor priv-stor (cat pt (pv a l-0))))
    ((load priv-stor-1 (cat pt-4 ignore-1))
      (stor priv-stor-1 (cat pt-3 (pv b lb))))
    ((load priv-stor (cat pt (pv a l-0)))
      (stor priv-stor (cat pt-5 "nil")) (send l-0))
    ((recv (cat (exp (gen) y) w))))
  (label 4638)
  (parent 2236)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((la l-0) (beta l) (a a) (b b-0) (x x) (upsilon (mul w y)) (na na)
        (nb nb) (priv-stor priv-stor) (pt pt) (self self)
        (priv-stor-0 priv-stor-0) (ignore ignore) (pt-0 pt-0)
        (pt-1 pt-1))))
  (origs (pt-5 (4 1)) (lb (3 1)) (pt-3 (3 1)) (l (1 1)) (pt-1 (1 1))
    (l-0 (2 1)) (pt (2 1)) (na (0 2))))

(defskeleton dhcr-um
  (vars (ignore ignore-0 ignore-1 mesg) (na nb data) (a b self b-0 name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pt-5 pt-6 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (l l-0 lb x rndx) (w expt)
    (y rndx))
  (defstrand init 4 (na na) (nb nb) (a a) (b b-0) (priv-stor priv-stor)
    (la l) (x x) (beta l-0) (upsilon (mul w y)))
  (defstrand ltx-gen 3 (ignore ignore) (self self)
    (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-gen 2 (ignore ignore-0) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-disclose 3 (self self) (priv-stor priv-stor-0) (l l-0))
  (defstrand ltx-gen 2 (ignore ignore-1) (self b)
    (priv-stor priv-stor-1) (l lb))
  (defstrand ltx-disclose 3 (self a) (priv-stor priv-stor) (l l))
  (deflistener (cat (exp (gen) y) w))
  (precedes ((1 1) (3 0)) ((2 1) (0 0)) ((2 1) (5 0)) ((3 2) (0 1))
    ((5 2) (0 3)))
  (uniq-orig na l l-0 lb)
  (uniq-gen x y)
  (absent (x l) (x l-0) (y (mul l l-0 (rec lb))) (y lb) (y (mul x w)))
  (precur (6 0))
  (gen-st (pv a l) (pv b lb) (pv self l-0))
  (facts (neq (exp (gen) (mul w y)) (gen)) (trans 4 1) (trans 2 1)
    (trans 1 1) (trans 4 0) (trans 2 0) (trans 1 0) (trans 5 1)
    (trans 3 1) (trans 5 0) (trans 3 0) (neq a b-0))
  (operation generalization separated b-0)
  (traces
    ((load priv-stor (cat pt (pv a l)))
      (recv
        (sig (body b-0 (exp (gen) l-0) (pubk "sig" b-0))
          (privk "sig" b-0))) (send (cat na a b-0 (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul w y))
          (enc na nb a b-0
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul x w y)))))))
    ((load priv-stor-0 (cat pt-0 ignore))
      (stor priv-stor-0 (cat pt-1 (pv self l-0)))
      (send
        (sig (body self (exp (gen) l-0) (pubk "sig" self))
          (privk "sig" self))))
    ((load priv-stor (cat pt-2 ignore-0))
      (stor priv-stor (cat pt (pv a l))))
    ((load priv-stor-0 (cat pt-1 (pv self l-0)))
      (stor priv-stor-0 (cat pt-3 "nil")) (send l-0))
    ((load priv-stor-1 (cat pt-5 ignore-1))
      (stor priv-stor-1 (cat pt-4 (pv b lb))))
    ((load priv-stor (cat pt (pv a l)))
      (stor priv-stor (cat pt-6 "nil")) (send l))
    ((recv (cat (exp (gen) y) w))))
  (label 4641)
  (parent 2236)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((la l) (beta l-0) (a a) (b b-0) (x x) (upsilon (mul w y)) (na na)
        (nb nb) (priv-stor priv-stor) (pt pt) (self self)
        (priv-stor-0 priv-stor-0) (ignore ignore) (pt-0 pt-0)
        (pt-1 pt-1))))
  (origs (l-0 (1 1)) (pt-1 (1 1)) (pt-6 (5 1)) (lb (4 1)) (pt-4 (4 1))
    (pt-3 (3 1)) (l (2 1)) (pt (2 1)) (na (0 2))))

(comment "Nothing left to do")
