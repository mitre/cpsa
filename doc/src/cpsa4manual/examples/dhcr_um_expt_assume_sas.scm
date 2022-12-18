(herald "DHCR: unified model (UM) original" (bound 20) (limit 12000)
  (algebra diffie-hellman))

(comment "CPSA 4.4.0")
(comment "Coherent logic")

(comment "CPSA 4.4.0")

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
        (and (fact undisclosed l) (p "ltx-disclose" z (idx 2))
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
      (implies (and (p "init" z (idx 4)) (p "init" "upsilon" z upsilon))
        (fact neq (exp (gen) upsilon) (gen)))))
  (defgenrule assume-resp-0
    (forall ((z strd) (zeta expt))
      (implies (and (p "resp" z (idx 3)) (p "resp" "zeta" z zeta))
        (fact neq (exp (gen) zeta) (gen)))))
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
    (forall ((z strd) (la rndx) (a name))
      (implies
        (and (p "init" z (idx 1)) (p "init" "la" z la)
          (p "init" "a" z a)) (gen-st (pv a la)))))
  (defgenrule gen-st-resp-0
    (forall ((z strd) (lb rndx) (b name))
      (implies
        (and (p "resp" z (idx 1)) (p "resp" "lb" z lb)
          (p "resp" "b" z b)) (gen-st (pv b lb)))))
  (defgenrule gen-st-ltx-disclose-0
    (forall ((z strd) (l rndx) (self name))
      (implies
        (and (p "ltx-disclose" z (idx 1)) (p "ltx-disclose" "l" z l)
          (p "ltx-disclose" "self" z self)) (gen-st (pv self l)))))
  (lang (sig sign) (body (tuple 3)) (pv (tuple 2))))

(defgoal dhcr-um
  (forall
    ((na nb data) (a b name) (priv-stor locn) (la rndx) (beta expt)
      (x rndx) (upsilon expt) (z strd))
    (implies
      (and (p "init" z 5) (p "init" "na" z na) (p "init" "nb" z nb)
        (p "init" "a" z a) (p "init" "b" z b)
        (p "init" "priv-stor" z priv-stor) (p "init" "la" z la)
        (p "init" "x" z x) (p "init" "beta" z beta)
        (p "init" "upsilon" z upsilon) (non (privk "sig" b)) (ugen x)
        (uniq-at na z 2) (fact neq a b) (fact undisclosed la)
        (fact undisclosed beta))
      (exists
        ((ignore ignore-0 mesg) (priv-stor-0 locn) (lb y rndx)
          (z-0 z-1 z-2 strd))
        (and (= beta lb) (= upsilon y) (p "ltx-gen" z-0 3)
          (p "resp" z-1 4) (p "ltx-gen" z-2 3) (p "init" "beta" z lb)
          (p "init" "upsilon" z y) (p "ltx-gen" "ignore" z-0 ignore)
          (p "ltx-gen" "self" z-0 b)
          (p "ltx-gen" "priv-stor" z-0 priv-stor-0)
          (p "ltx-gen" "l" z-0 lb) (p "resp" "na" z-1 na)
          (p "resp" "nb" z-1 nb) (p "resp" "a" z-1 a)
          (p "resp" "b" z-1 b) (p "resp" "priv-stor" z-1 priv-stor-0)
          (p "resp" "lb" z-1 lb) (p "resp" "y" z-1 y)
          (p "resp" "alpha" z-1 la) (p "resp" "zeta" z-1 x)
          (p "ltx-gen" "ignore" z-2 ignore-0) (p "ltx-gen" "self" z-2 a)
          (p "ltx-gen" "priv-stor" z-2 priv-stor)
          (p "ltx-gen" "l" z-2 la) (prec z 2 z-1 2) (prec z-0 1 z-1 0)
          (prec z-0 2 z 1) (prec z-1 3 z 3) (prec z-2 1 z 0)
          (prec z-2 2 z-1 1) (ugen y) (uniq-at nb z-1 3)
          (uniq-at la z-2 1) (uniq-at lb z-0 1) (gen-st (pv b lb))
          (gen-st (pv a la)) (leads-to z-0 1 z-1 0) (leads-to z-2 1 z 0)
          (fact neq (exp (gen) y) (gen)) (fact neq (exp (gen) x) (gen))
          (fact undisclosed lb))))))

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
        (and (fact undisclosed l) (p "ltx-disclose" z (idx 2))
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
      (implies (and (p "init" z (idx 4)) (p "init" "upsilon" z upsilon))
        (fact neq (exp (gen) upsilon) (gen)))))
  (defgenrule assume-resp-0
    (forall ((z strd) (zeta expt))
      (implies (and (p "resp" z (idx 3)) (p "resp" "zeta" z zeta))
        (fact neq (exp (gen) zeta) (gen)))))
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
    (forall ((z strd) (la rndx) (a name))
      (implies
        (and (p "init" z (idx 1)) (p "init" "la" z la)
          (p "init" "a" z a)) (gen-st (pv a la)))))
  (defgenrule gen-st-resp-0
    (forall ((z strd) (lb rndx) (b name))
      (implies
        (and (p "resp" z (idx 1)) (p "resp" "lb" z lb)
          (p "resp" "b" z b)) (gen-st (pv b lb)))))
  (defgenrule gen-st-ltx-disclose-0
    (forall ((z strd) (l rndx) (self name))
      (implies
        (and (p "ltx-disclose" z (idx 1)) (p "ltx-disclose" "l" z l)
          (p "ltx-disclose" "self" z self)) (gen-st (pv self l)))))
  (lang (sig sign) (body (tuple 3)) (pv (tuple 2))))

(defgoal dhcr-um
  (forall
    ((na nb data) (a b name) (priv-stor locn) (la rndx) (beta expt)
      (x rndx) (upsilon expt) (z strd))
    (implies
      (and (p "init" z 5) (p "init" "na" z na) (p "init" "nb" z nb)
        (p "init" "a" z a) (p "init" "b" z b)
        (p "init" "priv-stor" z priv-stor) (p "init" "la" z la)
        (p "init" "x" z x) (p "init" "beta" z beta)
        (p "init" "upsilon" z upsilon) (non (privk "sig" b)) (ugen x)
        (uniq-at na z 2) (fact neq a b) (fact undisclosed beta))
      (or
        (exists
          ((ignore ignore-0 mesg) (priv-stor-0 locn) (lb y rndx)
            (z-0 z-1 z-2 strd))
          (and (= beta lb) (= upsilon y) (p "ltx-gen" z-0 3)
            (p "resp" z-1 4) (p "ltx-gen" z-2 3) (p "init" "beta" z lb)
            (p "init" "upsilon" z y) (p "ltx-gen" "ignore" z-0 ignore)
            (p "ltx-gen" "self" z-0 b)
            (p "ltx-gen" "priv-stor" z-0 priv-stor-0)
            (p "ltx-gen" "l" z-0 lb) (p "resp" "na" z-1 na)
            (p "resp" "nb" z-1 nb) (p "resp" "a" z-1 a)
            (p "resp" "b" z-1 b) (p "resp" "priv-stor" z-1 priv-stor-0)
            (p "resp" "lb" z-1 lb) (p "resp" "y" z-1 y)
            (p "resp" "alpha" z-1 la) (p "resp" "zeta" z-1 x)
            (p "ltx-gen" "ignore" z-2 ignore-0)
            (p "ltx-gen" "self" z-2 a)
            (p "ltx-gen" "priv-stor" z-2 priv-stor)
            (p "ltx-gen" "l" z-2 la) (prec z 2 z-1 2) (prec z-0 1 z-1 0)
            (prec z-0 2 z 1) (prec z-1 3 z 3) (prec z-2 1 z 0)
            (prec z-2 2 z-1 1) (ugen y) (uniq-at nb z-1 3)
            (uniq-at la z-2 1) (uniq-at lb z-0 1) (gen-st (pv b lb))
            (gen-st (pv a la)) (leads-to z-0 1 z-1 0)
            (leads-to z-2 1 z 0) (fact neq (exp (gen) y) (gen))
            (fact neq (exp (gen) x) (gen)) (fact undisclosed lb)))
        (exists
          ((ignore ignore-0 mesg) (priv-stor-0 locn) (l rndx)
            (z-0 z-1 z-2 strd))
          (and (= beta l) (p "ltx-gen" z-0 2) (p "ltx-gen" z-1 3)
            (p "ltx-disclose" z-2 3) (p "init" "beta" z l)
            (p "ltx-gen" "ignore" z-0 ignore) (p "ltx-gen" "self" z-0 a)
            (p "ltx-gen" "priv-stor" z-0 priv-stor)
            (p "ltx-gen" "l" z-0 la) (p "ltx-gen" "ignore" z-1 ignore-0)
            (p "ltx-gen" "self" z-1 b)
            (p "ltx-gen" "priv-stor" z-1 priv-stor-0)
            (p "ltx-gen" "l" z-1 l) (p "ltx-disclose" "self" z-2 a)
            (p "ltx-disclose" "priv-stor" z-2 priv-stor)
            (p "ltx-disclose" "l" z-2 la) (prec z-0 1 z 0)
            (prec z-0 1 z-2 0) (prec z-1 2 z 1) (prec z-2 2 z 3)
            (uniq-at l z-1 1) (uniq-at la z-0 1) (gen-st (pv a la))
            (leads-to z-0 1 z 0) (leads-to z-0 1 z-2 0)
            (fact neq (exp (gen) upsilon) (gen)) (fact undisclosed l)))
        (exists
          ((ignore ignore-0 mesg) (priv-stor-0 locn) (lb y rndx)
            (z-0 z-1 z-2 strd))
          (and (= beta lb) (= upsilon y) (p "ltx-gen" z-0 2)
            (p "ltx-gen" z-1 3) (p "ltx-disclose" z-2 3)
            (p "init" "beta" z lb) (p "init" "upsilon" z y)
            (p "ltx-gen" "ignore" z-0 ignore) (p "ltx-gen" "self" z-0 a)
            (p "ltx-gen" "priv-stor" z-0 priv-stor)
            (p "ltx-gen" "l" z-0 la) (p "ltx-gen" "ignore" z-1 ignore-0)
            (p "ltx-gen" "self" z-1 b)
            (p "ltx-gen" "priv-stor" z-1 priv-stor-0)
            (p "ltx-gen" "l" z-1 lb) (p "ltx-disclose" "self" z-2 a)
            (p "ltx-disclose" "priv-stor" z-2 priv-stor)
            (p "ltx-disclose" "l" z-2 la) (prec z-0 1 z 0)
            (prec z-0 1 z-2 0) (prec z-1 2 z 1) (prec z-2 2 z 3)
            (uniq-at lb z-1 1) (uniq-at la z-0 1) (gen-st (pv a la))
            (gen-st (pv b lb)) (leads-to z-0 1 z 0)
            (leads-to z-0 1 z-2 0) (fact neq (exp (gen) y) (gen))
            (fact undisclosed lb)))
        (exists
          ((ignore ignore-0 mesg) (priv-stor-0 locn) (lb rndx) (w expt)
            (y rndx) (z-0 z-1 z-2 strd))
          (and (= beta lb) (= upsilon (mul w y)) (p "ltx-gen" z-0 2)
            (p "ltx-gen" z-1 3) (p "ltx-disclose" z-2 3)
            (p "init" "beta" z lb) (p "init" "upsilon" z (mul w y))
            (p "ltx-gen" "ignore" z-0 ignore) (p "ltx-gen" "self" z-0 a)
            (p "ltx-gen" "priv-stor" z-0 priv-stor)
            (p "ltx-gen" "l" z-0 la) (p "ltx-gen" "ignore" z-1 ignore-0)
            (p "ltx-gen" "self" z-1 b)
            (p "ltx-gen" "priv-stor" z-1 priv-stor-0)
            (p "ltx-gen" "l" z-1 lb) (p "ltx-disclose" "self" z-2 a)
            (p "ltx-disclose" "priv-stor" z-2 priv-stor)
            (p "ltx-disclose" "l" z-2 la) (prec z-0 1 z 0)
            (prec z-0 1 z-2 0) (prec z-1 2 z 1) (prec z-2 2 z 3)
            (uniq-at lb z-1 1) (uniq-at la z-0 1) (gen-st (pv a la))
            (gen-st (pv b lb)) (leads-to z-0 1 z 0)
            (leads-to z-0 1 z-2 0)
            (fact neq (exp (gen) (mul w y)) (gen))
            (fact undisclosed lb)))
        (exists
          ((ignore ignore-0 mesg) (priv-stor-0 locn) (l y rndx)
            (z-0 z-1 z-2 strd))
          (and (= beta l) (= upsilon y) (p "ltx-gen" z-0 2)
            (p "ltx-gen" z-1 3) (p "ltx-disclose" z-2 3)
            (p "init" "beta" z l) (p "init" "upsilon" z y)
            (p "ltx-gen" "ignore" z-0 ignore) (p "ltx-gen" "self" z-0 a)
            (p "ltx-gen" "priv-stor" z-0 priv-stor)
            (p "ltx-gen" "l" z-0 la) (p "ltx-gen" "ignore" z-1 ignore-0)
            (p "ltx-gen" "self" z-1 b)
            (p "ltx-gen" "priv-stor" z-1 priv-stor-0)
            (p "ltx-gen" "l" z-1 l) (p "ltx-disclose" "self" z-2 a)
            (p "ltx-disclose" "priv-stor" z-2 priv-stor)
            (p "ltx-disclose" "l" z-2 la) (prec z-0 1 z 0)
            (prec z-0 1 z-2 0) (prec z-1 2 z 1) (prec z-2 2 z 3)
            (uniq-at l z-1 1) (uniq-at la z-0 1) (gen-st (pv a la))
            (leads-to z-0 1 z 0) (leads-to z-0 1 z-2 0)
            (fact neq (exp (gen) y) (gen)) (fact undisclosed l)))))))

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
        (and (fact undisclosed l) (p "ltx-disclose" z (idx 2))
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
      (implies (and (p "init" z (idx 4)) (p "init" "upsilon" z upsilon))
        (fact neq (exp (gen) upsilon) (gen)))))
  (defgenrule assume-resp-0
    (forall ((z strd) (zeta expt))
      (implies (and (p "resp" z (idx 3)) (p "resp" "zeta" z zeta))
        (fact neq (exp (gen) zeta) (gen)))))
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
    (forall ((z strd) (la rndx) (a name))
      (implies
        (and (p "init" z (idx 1)) (p "init" "la" z la)
          (p "init" "a" z a)) (gen-st (pv a la)))))
  (defgenrule gen-st-resp-0
    (forall ((z strd) (lb rndx) (b name))
      (implies
        (and (p "resp" z (idx 1)) (p "resp" "lb" z lb)
          (p "resp" "b" z b)) (gen-st (pv b lb)))))
  (defgenrule gen-st-ltx-disclose-0
    (forall ((z strd) (l rndx) (self name))
      (implies
        (and (p "ltx-disclose" z (idx 1)) (p "ltx-disclose" "l" z l)
          (p "ltx-disclose" "self" z self)) (gen-st (pv self l)))))
  (lang (sig sign) (body (tuple 3)) (pv (tuple 2))))

(defgoal dhcr-um
  (forall
    ((na nb data) (a b name) (priv-stor locn) (la x rndx)
      (beta upsilon expt) (z strd))
    (implies
      (and (p "init" z 5) (p "init" "na" z na) (p "init" "nb" z nb)
        (p "init" "a" z a) (p "init" "b" z b)
        (p "init" "priv-stor" z priv-stor) (p "init" "la" z la)
        (p "init" "x" z x) (p "init" "beta" z beta)
        (p "init" "upsilon" z upsilon) (non (privk "sig" b)) (ugen x)
        (uniq-at na z 2) (fact neq a b) (fact undisclosed la))
      (or
        (exists
          ((ignore ignore-0 mesg) (priv-stor-0 locn) (lb y rndx)
            (z-0 z-1 z-2 strd))
          (and (= beta lb) (= upsilon y) (p "ltx-gen" z-0 3)
            (p "resp" z-1 4) (p "ltx-gen" z-2 3) (p "init" "beta" z lb)
            (p "init" "upsilon" z y) (p "ltx-gen" "ignore" z-0 ignore)
            (p "ltx-gen" "self" z-0 b)
            (p "ltx-gen" "priv-stor" z-0 priv-stor-0)
            (p "ltx-gen" "l" z-0 lb) (p "resp" "na" z-1 na)
            (p "resp" "nb" z-1 nb) (p "resp" "a" z-1 a)
            (p "resp" "b" z-1 b) (p "resp" "priv-stor" z-1 priv-stor-0)
            (p "resp" "lb" z-1 lb) (p "resp" "y" z-1 y)
            (p "resp" "alpha" z-1 la) (p "resp" "zeta" z-1 x)
            (p "ltx-gen" "ignore" z-2 ignore-0)
            (p "ltx-gen" "self" z-2 a)
            (p "ltx-gen" "priv-stor" z-2 priv-stor)
            (p "ltx-gen" "l" z-2 la) (prec z 2 z-1 2) (prec z-0 1 z-1 0)
            (prec z-0 2 z 1) (prec z-1 3 z 3) (prec z-2 1 z 0)
            (prec z-2 2 z-1 1) (ugen y) (uniq-at nb z-1 3)
            (uniq-at la z-2 1) (uniq-at lb z-0 1) (gen-st (pv b lb))
            (gen-st (pv a la)) (leads-to z-0 1 z-1 0)
            (leads-to z-2 1 z 0) (fact neq (exp (gen) y) (gen))
            (fact neq (exp (gen) x) (gen))))
        (exists
          ((ignore ignore-0 mesg) (priv-stor-0 locn) (l rndx)
            (z-0 z-1 z-2 strd))
          (and (= beta l) (p "ltx-gen" z-0 3) (p "ltx-disclose" z-1 3)
            (p "ltx-gen" z-2 3) (p "init" "beta" z l)
            (p "ltx-gen" "ignore" z-0 ignore) (p "ltx-gen" "self" z-0 b)
            (p "ltx-gen" "priv-stor" z-0 priv-stor-0)
            (p "ltx-gen" "l" z-0 l) (p "ltx-disclose" "self" z-1 b)
            (p "ltx-disclose" "priv-stor" z-1 priv-stor-0)
            (p "ltx-disclose" "l" z-1 l)
            (p "ltx-gen" "ignore" z-2 ignore-0)
            (p "ltx-gen" "self" z-2 a)
            (p "ltx-gen" "priv-stor" z-2 priv-stor)
            (p "ltx-gen" "l" z-2 la) (prec z-0 1 z-1 0) (prec z-0 2 z 1)
            (prec z-1 2 z 3) (prec z-2 1 z 0) (prec z-2 2 z 3)
            (uniq-at la z-2 1) (uniq-at l z-0 1) (gen-st (pv b l))
            (gen-st (pv a la)) (leads-to z-0 1 z-1 0)
            (leads-to z-2 1 z 0) (fact neq (exp (gen) upsilon) (gen))))
        (exists
          ((ignore ignore-0 mesg) (priv-stor-0 locn) (l y rndx)
            (z-0 z-1 z-2 strd))
          (and (= beta l) (= upsilon y) (p "ltx-gen" z-0 3)
            (p "ltx-disclose" z-1 3) (p "ltx-gen" z-2 3)
            (p "init" "beta" z l) (p "init" "upsilon" z y)
            (p "ltx-gen" "ignore" z-0 ignore) (p "ltx-gen" "self" z-0 b)
            (p "ltx-gen" "priv-stor" z-0 priv-stor-0)
            (p "ltx-gen" "l" z-0 l) (p "ltx-disclose" "self" z-1 b)
            (p "ltx-disclose" "priv-stor" z-1 priv-stor-0)
            (p "ltx-disclose" "l" z-1 l)
            (p "ltx-gen" "ignore" z-2 ignore-0)
            (p "ltx-gen" "self" z-2 a)
            (p "ltx-gen" "priv-stor" z-2 priv-stor)
            (p "ltx-gen" "l" z-2 la) (prec z-0 1 z-1 0) (prec z-0 2 z 1)
            (prec z-1 2 z 3) (prec z-2 1 z 0) (prec z-2 2 z 3)
            (uniq-at la z-2 1) (uniq-at l z-0 1) (gen-st (pv b l))
            (gen-st (pv a la)) (leads-to z-0 1 z-1 0)
            (leads-to z-2 1 z 0) (fact neq (exp (gen) y) (gen))))))))

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
        (and (fact undisclosed l) (p "ltx-disclose" z (idx 2))
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
      (implies (and (p "init" z (idx 4)) (p "init" "upsilon" z upsilon))
        (fact neq (exp (gen) upsilon) (gen)))))
  (defgenrule assume-resp-0
    (forall ((z strd) (zeta expt))
      (implies (and (p "resp" z (idx 3)) (p "resp" "zeta" z zeta))
        (fact neq (exp (gen) zeta) (gen)))))
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
    (forall ((z strd) (la rndx) (a name))
      (implies
        (and (p "init" z (idx 1)) (p "init" "la" z la)
          (p "init" "a" z a)) (gen-st (pv a la)))))
  (defgenrule gen-st-resp-0
    (forall ((z strd) (lb rndx) (b name))
      (implies
        (and (p "resp" z (idx 1)) (p "resp" "lb" z lb)
          (p "resp" "b" z b)) (gen-st (pv b lb)))))
  (defgenrule gen-st-ltx-disclose-0
    (forall ((z strd) (l rndx) (self name))
      (implies
        (and (p "ltx-disclose" z (idx 1)) (p "ltx-disclose" "l" z l)
          (p "ltx-disclose" "self" z self)) (gen-st (pv self l)))))
  (lang (sig sign) (body (tuple 3)) (pv (tuple 2))))

(defgoal dhcr-um
  (forall
    ((na nb data) (a b name) (priv-stor locn) (la x rndx)
      (beta upsilon expt) (z strd))
    (implies
      (and (p "init" z 5) (p "init" "na" z na) (p "init" "nb" z nb)
        (p "init" "a" z a) (p "init" "b" z b)
        (p "init" "priv-stor" z priv-stor) (p "init" "la" z la)
        (p "init" "x" z x) (p "init" "beta" z beta)
        (p "init" "upsilon" z upsilon) (non (privk "sig" b)) (ugen x)
        (uniq-at na z 2) (fact neq a b))
      (or
        (exists
          ((ignore ignore-0 mesg) (priv-stor-0 locn) (lb y rndx)
            (z-0 z-1 z-2 strd))
          (and (= beta lb) (= upsilon y) (p "ltx-gen" z-0 3)
            (p "resp" z-1 4) (p "ltx-gen" z-2 3) (p "init" "beta" z lb)
            (p "init" "upsilon" z y) (p "ltx-gen" "ignore" z-0 ignore)
            (p "ltx-gen" "self" z-0 b)
            (p "ltx-gen" "priv-stor" z-0 priv-stor-0)
            (p "ltx-gen" "l" z-0 lb) (p "resp" "na" z-1 na)
            (p "resp" "nb" z-1 nb) (p "resp" "a" z-1 a)
            (p "resp" "b" z-1 b) (p "resp" "priv-stor" z-1 priv-stor-0)
            (p "resp" "lb" z-1 lb) (p "resp" "y" z-1 y)
            (p "resp" "alpha" z-1 la) (p "resp" "zeta" z-1 x)
            (p "ltx-gen" "ignore" z-2 ignore-0)
            (p "ltx-gen" "self" z-2 a)
            (p "ltx-gen" "priv-stor" z-2 priv-stor)
            (p "ltx-gen" "l" z-2 la) (prec z 2 z-1 2) (prec z-0 1 z-1 0)
            (prec z-0 2 z 1) (prec z-1 3 z 3) (prec z-2 1 z 0)
            (prec z-2 2 z-1 1) (ugen y) (uniq-at nb z-1 3)
            (uniq-at la z-2 1) (uniq-at lb z-0 1) (gen-st (pv b lb))
            (gen-st (pv a la)) (leads-to z-0 1 z-1 0)
            (leads-to z-2 1 z 0) (fact neq (exp (gen) y) (gen))
            (fact neq (exp (gen) x) (gen))))
        (exists
          ((ignore ignore-0 mesg) (priv-stor-0 locn) (l rndx)
            (z-0 z-1 z-2 strd))
          (and (= beta l) (p "ltx-gen" z-0 3) (p "ltx-disclose" z-1 3)
            (p "ltx-gen" z-2 3) (p "init" "beta" z l)
            (p "ltx-gen" "ignore" z-0 ignore) (p "ltx-gen" "self" z-0 b)
            (p "ltx-gen" "priv-stor" z-0 priv-stor-0)
            (p "ltx-gen" "l" z-0 l) (p "ltx-disclose" "self" z-1 b)
            (p "ltx-disclose" "priv-stor" z-1 priv-stor-0)
            (p "ltx-disclose" "l" z-1 l)
            (p "ltx-gen" "ignore" z-2 ignore-0)
            (p "ltx-gen" "self" z-2 a)
            (p "ltx-gen" "priv-stor" z-2 priv-stor)
            (p "ltx-gen" "l" z-2 la) (prec z-0 1 z-1 0) (prec z-0 2 z 1)
            (prec z-1 2 z 3) (prec z-2 1 z 0) (prec z-2 2 z 3)
            (uniq-at la z-2 1) (uniq-at l z-0 1) (gen-st (pv b l))
            (gen-st (pv a la)) (leads-to z-0 1 z-1 0)
            (leads-to z-2 1 z 0) (fact neq (exp (gen) upsilon) (gen))))
        (exists
          ((ignore ignore-0 mesg) (priv-stor-0 locn) (l rndx)
            (z-0 z-1 z-2 strd))
          (and (= beta l) (p "ltx-gen" z-0 2) (p "ltx-gen" z-1 3)
            (p "ltx-disclose" z-2 3) (p "init" "beta" z l)
            (p "ltx-gen" "ignore" z-0 ignore) (p "ltx-gen" "self" z-0 a)
            (p "ltx-gen" "priv-stor" z-0 priv-stor)
            (p "ltx-gen" "l" z-0 la) (p "ltx-gen" "ignore" z-1 ignore-0)
            (p "ltx-gen" "self" z-1 b)
            (p "ltx-gen" "priv-stor" z-1 priv-stor-0)
            (p "ltx-gen" "l" z-1 l) (p "ltx-disclose" "self" z-2 a)
            (p "ltx-disclose" "priv-stor" z-2 priv-stor)
            (p "ltx-disclose" "l" z-2 la) (prec z-0 1 z 0)
            (prec z-0 1 z-2 0) (prec z-1 2 z 1) (prec z-2 2 z 3)
            (uniq-at l z-1 1) (uniq-at la z-0 1) (gen-st (pv a la))
            (leads-to z-0 1 z 0) (leads-to z-0 1 z-2 0)
            (fact neq (exp (gen) upsilon) (gen))))
        (exists
          ((ignore ignore-0 mesg) (priv-stor-0 locn) (lb y rndx)
            (z-0 z-1 z-2 strd))
          (and (= beta lb) (= upsilon y) (p "ltx-gen" z-0 2)
            (p "ltx-gen" z-1 3) (p "ltx-disclose" z-2 3)
            (p "init" "beta" z lb) (p "init" "upsilon" z y)
            (p "ltx-gen" "ignore" z-0 ignore) (p "ltx-gen" "self" z-0 a)
            (p "ltx-gen" "priv-stor" z-0 priv-stor)
            (p "ltx-gen" "l" z-0 la) (p "ltx-gen" "ignore" z-1 ignore-0)
            (p "ltx-gen" "self" z-1 b)
            (p "ltx-gen" "priv-stor" z-1 priv-stor-0)
            (p "ltx-gen" "l" z-1 lb) (p "ltx-disclose" "self" z-2 a)
            (p "ltx-disclose" "priv-stor" z-2 priv-stor)
            (p "ltx-disclose" "l" z-2 la) (prec z-0 1 z 0)
            (prec z-0 1 z-2 0) (prec z-1 2 z 1) (prec z-2 2 z 3)
            (uniq-at lb z-1 1) (uniq-at la z-0 1) (gen-st (pv a la))
            (gen-st (pv b lb)) (leads-to z-0 1 z 0)
            (leads-to z-0 1 z-2 0) (fact neq (exp (gen) y) (gen))))
        (exists
          ((ignore ignore-0 mesg) (priv-stor-0 locn) (lb rndx) (w expt)
            (y rndx) (z-0 z-1 z-2 strd))
          (and (= beta lb) (= upsilon (mul w y)) (p "ltx-gen" z-0 2)
            (p "ltx-gen" z-1 3) (p "ltx-disclose" z-2 3)
            (p "init" "beta" z lb) (p "init" "upsilon" z (mul w y))
            (p "ltx-gen" "ignore" z-0 ignore) (p "ltx-gen" "self" z-0 a)
            (p "ltx-gen" "priv-stor" z-0 priv-stor)
            (p "ltx-gen" "l" z-0 la) (p "ltx-gen" "ignore" z-1 ignore-0)
            (p "ltx-gen" "self" z-1 b)
            (p "ltx-gen" "priv-stor" z-1 priv-stor-0)
            (p "ltx-gen" "l" z-1 lb) (p "ltx-disclose" "self" z-2 a)
            (p "ltx-disclose" "priv-stor" z-2 priv-stor)
            (p "ltx-disclose" "l" z-2 la) (prec z-0 1 z 0)
            (prec z-0 1 z-2 0) (prec z-1 2 z 1) (prec z-2 2 z 3)
            (uniq-at lb z-1 1) (uniq-at la z-0 1) (gen-st (pv a la))
            (gen-st (pv b lb)) (leads-to z-0 1 z 0)
            (leads-to z-0 1 z-2 0)
            (fact neq (exp (gen) (mul w y)) (gen))))
        (exists
          ((ignore ignore-0 mesg) (priv-stor-0 locn) (l y rndx)
            (z-0 z-1 z-2 strd))
          (and (= beta l) (= upsilon y) (p "ltx-gen" z-0 3)
            (p "ltx-disclose" z-1 3) (p "ltx-gen" z-2 3)
            (p "init" "beta" z l) (p "init" "upsilon" z y)
            (p "ltx-gen" "ignore" z-0 ignore) (p "ltx-gen" "self" z-0 b)
            (p "ltx-gen" "priv-stor" z-0 priv-stor-0)
            (p "ltx-gen" "l" z-0 l) (p "ltx-disclose" "self" z-1 b)
            (p "ltx-disclose" "priv-stor" z-1 priv-stor-0)
            (p "ltx-disclose" "l" z-1 l)
            (p "ltx-gen" "ignore" z-2 ignore-0)
            (p "ltx-gen" "self" z-2 a)
            (p "ltx-gen" "priv-stor" z-2 priv-stor)
            (p "ltx-gen" "l" z-2 la) (prec z-0 1 z-1 0) (prec z-0 2 z 1)
            (prec z-1 2 z 3) (prec z-2 1 z 0) (prec z-2 2 z 3)
            (uniq-at la z-2 1) (uniq-at l z-0 1) (gen-st (pv b l))
            (gen-st (pv a la)) (leads-to z-0 1 z-1 0)
            (leads-to z-2 1 z 0) (fact neq (exp (gen) y) (gen))))
        (exists
          ((ignore ignore-0 mesg) (priv-stor-0 locn) (l y rndx)
            (z-0 z-1 z-2 strd))
          (and (= beta l) (= upsilon y) (p "ltx-gen" z-0 2)
            (p "ltx-gen" z-1 3) (p "ltx-disclose" z-2 3)
            (p "init" "beta" z l) (p "init" "upsilon" z y)
            (p "ltx-gen" "ignore" z-0 ignore) (p "ltx-gen" "self" z-0 a)
            (p "ltx-gen" "priv-stor" z-0 priv-stor)
            (p "ltx-gen" "l" z-0 la) (p "ltx-gen" "ignore" z-1 ignore-0)
            (p "ltx-gen" "self" z-1 b)
            (p "ltx-gen" "priv-stor" z-1 priv-stor-0)
            (p "ltx-gen" "l" z-1 l) (p "ltx-disclose" "self" z-2 a)
            (p "ltx-disclose" "priv-stor" z-2 priv-stor)
            (p "ltx-disclose" "l" z-2 la) (prec z-0 1 z 0)
            (prec z-0 1 z-2 0) (prec z-1 2 z 1) (prec z-2 2 z 3)
            (uniq-at l z-1 1) (uniq-at la z-0 1) (gen-st (pv a la))
            (leads-to z-0 1 z 0) (leads-to z-0 1 z-2 0)
            (fact neq (exp (gen) y) (gen))))))))

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
        (and (fact undisclosed l) (p "ltx-disclose" z (idx 2))
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
      (implies (and (p "init" z (idx 4)) (p "init" "upsilon" z upsilon))
        (fact neq (exp (gen) upsilon) (gen)))))
  (defgenrule assume-resp-0
    (forall ((z strd) (zeta expt))
      (implies (and (p "resp" z (idx 3)) (p "resp" "zeta" z zeta))
        (fact neq (exp (gen) zeta) (gen)))))
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
    (forall ((z strd) (la rndx) (a name))
      (implies
        (and (p "init" z (idx 1)) (p "init" "la" z la)
          (p "init" "a" z a)) (gen-st (pv a la)))))
  (defgenrule gen-st-resp-0
    (forall ((z strd) (lb rndx) (b name))
      (implies
        (and (p "resp" z (idx 1)) (p "resp" "lb" z lb)
          (p "resp" "b" z b)) (gen-st (pv b lb)))))
  (defgenrule gen-st-ltx-disclose-0
    (forall ((z strd) (l rndx) (self name))
      (implies
        (and (p "ltx-disclose" z (idx 1)) (p "ltx-disclose" "l" z l)
          (p "ltx-disclose" "self" z self)) (gen-st (pv self l)))))
  (lang (sig sign) (body (tuple 3)) (pv (tuple 2))))

(defgoal dhcr-um
  (forall
    ((na nb na-0 nb-0 data) (a b name) (priv-stor priv-stor-0 locn)
      (la lb rndx) (alpha beta expt) (y rndx) (zeta expt) (x rndx)
      (upsilon expt) (z z-0 strd))
    (implies
      (and (p "resp" z 5) (p "init" z-0 5) (p "resp" "na" z na)
        (p "resp" "nb" z nb) (p "resp" "a" z a) (p "resp" "b" z b)
        (p "resp" "priv-stor" z priv-stor) (p "resp" "lb" z lb)
        (p "resp" "y" z y) (p "resp" "alpha" z alpha)
        (p "resp" "zeta" z zeta) (p "init" "na" z-0 na-0)
        (p "init" "nb" z-0 nb-0) (p "init" "a" z-0 a)
        (p "init" "b" z-0 b) (p "init" "priv-stor" z-0 priv-stor-0)
        (p "init" "la" z-0 la) (p "init" "x" z-0 x)
        (p "init" "beta" z-0 beta) (p "init" "upsilon" z-0 upsilon)
        (non (privk "sig" a)) (non (privk "sig" b)) (ugen y) (ugen x)
        (uniq-at na-0 z-0 2) (uniq-at nb z 3) (fact neq a b)
        (fact undisclosed la) (fact undisclosed lb))
      (or
        (exists
          ((ignore ignore-0 ignore-1 mesg) (priv-stor-1 locn)
            (y-0 l rndx) (z-1 z-2 z-3 z-4 z-5 strd))
          (and (= alpha l) (= beta lb) (= upsilon y-0)
            (p "ltx-gen" z-1 3) (p "resp" z-2 4) (p "ltx-gen" z-3 3)
            (p "ltx-gen" z-4 3) (p "ltx-disclose" z-5 3)
            (p "resp" "alpha" z l) (p "init" "beta" z-0 lb)
            (p "init" "upsilon" z-0 y-0)
            (p "ltx-gen" "ignore" z-1 ignore) (p "ltx-gen" "self" z-1 b)
            (p "ltx-gen" "priv-stor" z-1 priv-stor)
            (p "ltx-gen" "l" z-1 lb) (p "resp" "na" z-2 na-0)
            (p "resp" "nb" z-2 nb-0) (p "resp" "a" z-2 a)
            (p "resp" "b" z-2 b) (p "resp" "priv-stor" z-2 priv-stor)
            (p "resp" "lb" z-2 lb) (p "resp" "y" z-2 y-0)
            (p "resp" "alpha" z-2 la) (p "resp" "zeta" z-2 x)
            (p "ltx-gen" "ignore" z-3 ignore-0)
            (p "ltx-gen" "self" z-3 a)
            (p "ltx-gen" "priv-stor" z-3 priv-stor-0)
            (p "ltx-gen" "l" z-3 la) (p "ltx-gen" "ignore" z-4 ignore-1)
            (p "ltx-gen" "self" z-4 a)
            (p "ltx-gen" "priv-stor" z-4 priv-stor-1)
            (p "ltx-gen" "l" z-4 l) (p "ltx-disclose" "self" z-5 a)
            (p "ltx-disclose" "priv-stor" z-5 priv-stor-1)
            (p "ltx-disclose" "l" z-5 l) (prec z-0 2 z-2 2)
            (prec z-1 1 z 0) (prec z-1 1 z-2 0) (prec z-1 2 z 4)
            (prec z-1 2 z-0 1) (prec z-2 3 z-0 3) (prec z-3 1 z-0 0)
            (prec z-3 2 z-2 1) (prec z-4 1 z-5 0) (prec z-4 2 z 1)
            (prec z-5 2 z 4) (ugen y-0) (uniq-at lb z-1 1)
            (uniq-at l z-4 1) (uniq-at nb-0 z-2 3) (uniq-at la z-3 1)
            (gen-st (pv a la)) (gen-st (pv a l)) (gen-st (pv b lb))
            (leads-to z-1 1 z 0) (leads-to z-1 1 z-2 0)
            (leads-to z-3 1 z-0 0) (leads-to z-4 1 z-5 0)
            (fact neq (exp (gen) y-0) (gen))
            (fact neq (exp (gen) x) (gen))
            (fact neq (exp (gen) zeta) (gen))))
        (exists
          ((ignore ignore-0 ignore-1 ignore-2 mesg)
            (priv-stor-1 priv-stor-2 locn) (lb-0 y-0 l rndx)
            (z-1 z-2 z-3 z-4 z-5 z-6 strd))
          (and (= alpha l) (= beta lb-0) (= upsilon y-0)
            (p "ltx-gen" z-1 3) (p "resp" z-2 4) (p "ltx-gen" z-3 3)
            (p "ltx-gen" z-4 3) (p "ltx-disclose" z-5 3)
            (p "ltx-gen" z-6 3) (p "resp" "alpha" z l)
            (p "init" "beta" z-0 lb-0) (p "init" "upsilon" z-0 y-0)
            (p "ltx-gen" "ignore" z-1 ignore) (p "ltx-gen" "self" z-1 b)
            (p "ltx-gen" "priv-stor" z-1 priv-stor-1)
            (p "ltx-gen" "l" z-1 lb-0) (p "resp" "na" z-2 na-0)
            (p "resp" "nb" z-2 nb-0) (p "resp" "a" z-2 a)
            (p "resp" "b" z-2 b) (p "resp" "priv-stor" z-2 priv-stor-1)
            (p "resp" "lb" z-2 lb-0) (p "resp" "y" z-2 y-0)
            (p "resp" "alpha" z-2 la) (p "resp" "zeta" z-2 x)
            (p "ltx-gen" "ignore" z-3 ignore-0)
            (p "ltx-gen" "self" z-3 a)
            (p "ltx-gen" "priv-stor" z-3 priv-stor-0)
            (p "ltx-gen" "l" z-3 la) (p "ltx-gen" "ignore" z-4 ignore-1)
            (p "ltx-gen" "self" z-4 a)
            (p "ltx-gen" "priv-stor" z-4 priv-stor-2)
            (p "ltx-gen" "l" z-4 l) (p "ltx-disclose" "self" z-5 a)
            (p "ltx-disclose" "priv-stor" z-5 priv-stor-2)
            (p "ltx-disclose" "l" z-5 l)
            (p "ltx-gen" "ignore" z-6 ignore-2)
            (p "ltx-gen" "self" z-6 b)
            (p "ltx-gen" "priv-stor" z-6 priv-stor)
            (p "ltx-gen" "l" z-6 lb) (prec z-0 2 z-2 2)
            (prec z-1 1 z-2 0) (prec z-1 2 z-0 1) (prec z-2 3 z-0 3)
            (prec z-3 1 z-0 0) (prec z-3 2 z-2 1) (prec z-4 1 z-5 0)
            (prec z-4 2 z 1) (prec z-5 2 z 4) (prec z-6 1 z 0)
            (prec z-6 2 z 4) (ugen y-0) (uniq-at lb z-6 1)
            (uniq-at l z-4 1) (uniq-at nb-0 z-2 3) (uniq-at la z-3 1)
            (uniq-at lb-0 z-1 1) (gen-st (pv a la)) (gen-st (pv a l))
            (gen-st (pv b lb-0)) (gen-st (pv b lb))
            (leads-to z-1 1 z-2 0) (leads-to z-3 1 z-0 0)
            (leads-to z-4 1 z-5 0) (leads-to z-6 1 z 0)
            (fact neq (exp (gen) y-0) (gen))
            (fact neq (exp (gen) x) (gen))
            (fact neq (exp (gen) zeta) (gen))))
        (exists
          ((ignore ignore-0 ignore-1 mesg) (priv-stor-1 locn) (w expt)
            (y-0 l rndx) (z-1 z-2 z-3 z-4 z-5 strd))
          (and (= alpha l) (= beta lb) (= upsilon (mul w y-0))
            (p "ltx-gen" z-1 3) (p "resp" z-2 4) (p "ltx-gen" z-3 3)
            (p "ltx-gen" z-4 3) (p "ltx-disclose" z-5 3)
            (p "resp" "alpha" z l) (p "init" "beta" z-0 lb)
            (p "init" "upsilon" z-0 (mul w y-0))
            (p "ltx-gen" "ignore" z-1 ignore) (p "ltx-gen" "self" z-1 b)
            (p "ltx-gen" "priv-stor" z-1 priv-stor)
            (p "ltx-gen" "l" z-1 lb) (p "resp" "na" z-2 na-0)
            (p "resp" "nb" z-2 nb-0) (p "resp" "a" z-2 a)
            (p "resp" "b" z-2 b) (p "resp" "priv-stor" z-2 priv-stor)
            (p "resp" "lb" z-2 lb) (p "resp" "y" z-2 y-0)
            (p "resp" "alpha" z-2 la) (p "resp" "zeta" z-2 (mul x w))
            (p "ltx-gen" "ignore" z-3 ignore-0)
            (p "ltx-gen" "self" z-3 a)
            (p "ltx-gen" "priv-stor" z-3 priv-stor-0)
            (p "ltx-gen" "l" z-3 la) (p "ltx-gen" "ignore" z-4 ignore-1)
            (p "ltx-gen" "self" z-4 a)
            (p "ltx-gen" "priv-stor" z-4 priv-stor-1)
            (p "ltx-gen" "l" z-4 l) (p "ltx-disclose" "self" z-5 a)
            (p "ltx-disclose" "priv-stor" z-5 priv-stor-1)
            (p "ltx-disclose" "l" z-5 l) (prec z-0 2 z-2 2)
            (prec z-1 1 z 0) (prec z-1 1 z-2 0) (prec z-1 2 z 4)
            (prec z-1 2 z-0 1) (prec z-2 3 z-0 3) (prec z-3 1 z-0 0)
            (prec z-3 2 z-2 1) (prec z-4 1 z-5 0) (prec z-4 2 z 1)
            (prec z-5 2 z 4) (ugen y-0) (uniq-at lb z-1 1)
            (uniq-at l z-4 1) (uniq-at nb-0 z-2 3) (uniq-at la z-3 1)
            (gen-st (pv a la)) (gen-st (pv a l)) (gen-st (pv b lb))
            (leads-to z-1 1 z 0) (leads-to z-1 1 z-2 0)
            (leads-to z-3 1 z-0 0) (leads-to z-4 1 z-5 0)
            (fact neq (exp (gen) (mul w y-0)) (gen))
            (fact neq (exp (gen) (mul x w)) (gen))
            (fact neq (exp (gen) zeta) (gen))))
        (exists
          ((ignore ignore-0 ignore-1 ignore-2 mesg)
            (priv-stor-1 priv-stor-2 locn) (lb-0 rndx) (w expt)
            (y-0 l rndx) (z-1 z-2 z-3 z-4 z-5 z-6 strd))
          (and (= alpha l) (= beta lb-0) (= upsilon (mul w y-0))
            (p "ltx-gen" z-1 3) (p "resp" z-2 4) (p "ltx-gen" z-3 3)
            (p "ltx-gen" z-4 3) (p "ltx-disclose" z-5 3)
            (p "ltx-gen" z-6 3) (p "resp" "alpha" z l)
            (p "init" "beta" z-0 lb-0)
            (p "init" "upsilon" z-0 (mul w y-0))
            (p "ltx-gen" "ignore" z-1 ignore) (p "ltx-gen" "self" z-1 b)
            (p "ltx-gen" "priv-stor" z-1 priv-stor-1)
            (p "ltx-gen" "l" z-1 lb-0) (p "resp" "na" z-2 na-0)
            (p "resp" "nb" z-2 nb-0) (p "resp" "a" z-2 a)
            (p "resp" "b" z-2 b) (p "resp" "priv-stor" z-2 priv-stor-1)
            (p "resp" "lb" z-2 lb-0) (p "resp" "y" z-2 y-0)
            (p "resp" "alpha" z-2 la) (p "resp" "zeta" z-2 (mul x w))
            (p "ltx-gen" "ignore" z-3 ignore-0)
            (p "ltx-gen" "self" z-3 a)
            (p "ltx-gen" "priv-stor" z-3 priv-stor-0)
            (p "ltx-gen" "l" z-3 la) (p "ltx-gen" "ignore" z-4 ignore-1)
            (p "ltx-gen" "self" z-4 a)
            (p "ltx-gen" "priv-stor" z-4 priv-stor-2)
            (p "ltx-gen" "l" z-4 l) (p "ltx-disclose" "self" z-5 a)
            (p "ltx-disclose" "priv-stor" z-5 priv-stor-2)
            (p "ltx-disclose" "l" z-5 l)
            (p "ltx-gen" "ignore" z-6 ignore-2)
            (p "ltx-gen" "self" z-6 b)
            (p "ltx-gen" "priv-stor" z-6 priv-stor)
            (p "ltx-gen" "l" z-6 lb) (prec z-0 2 z-2 2)
            (prec z-1 1 z-2 0) (prec z-1 2 z-0 1) (prec z-2 3 z-0 3)
            (prec z-3 1 z-0 0) (prec z-3 2 z-2 1) (prec z-4 1 z-5 0)
            (prec z-4 2 z 1) (prec z-5 2 z 4) (prec z-6 1 z 0)
            (prec z-6 2 z 4) (ugen y-0) (uniq-at lb z-6 1)
            (uniq-at l z-4 1) (uniq-at nb-0 z-2 3) (uniq-at la z-3 1)
            (uniq-at lb-0 z-1 1) (gen-st (pv a la)) (gen-st (pv a l))
            (gen-st (pv b lb-0)) (gen-st (pv b lb))
            (leads-to z-1 1 z-2 0) (leads-to z-3 1 z-0 0)
            (leads-to z-4 1 z-5 0) (leads-to z-6 1 z 0)
            (fact neq (exp (gen) (mul w y-0)) (gen))
            (fact neq (exp (gen) (mul x w)) (gen))
            (fact neq (exp (gen) zeta) (gen))))
        (exists
          ((ignore ignore-0 ignore-1 ignore-2 mesg)
            (priv-stor-1 priv-stor-2 locn) (l l-0 rndx)
            (z-1 z-2 z-3 z-4 z-5 z-6 strd))
          (and (= alpha l-0) (= beta l) (p "ltx-gen" z-1 3)
            (p "ltx-disclose" z-2 3) (p "ltx-gen" z-3 3)
            (p "ltx-gen" z-4 3) (p "ltx-disclose" z-5 3)
            (p "ltx-gen" z-6 3) (p "resp" "alpha" z l-0)
            (p "init" "beta" z-0 l) (p "ltx-gen" "ignore" z-1 ignore)
            (p "ltx-gen" "self" z-1 b)
            (p "ltx-gen" "priv-stor" z-1 priv-stor-1)
            (p "ltx-gen" "l" z-1 l) (p "ltx-disclose" "self" z-2 b)
            (p "ltx-disclose" "priv-stor" z-2 priv-stor-1)
            (p "ltx-disclose" "l" z-2 l)
            (p "ltx-gen" "ignore" z-3 ignore-0)
            (p "ltx-gen" "self" z-3 a)
            (p "ltx-gen" "priv-stor" z-3 priv-stor-0)
            (p "ltx-gen" "l" z-3 la) (p "ltx-gen" "ignore" z-4 ignore-1)
            (p "ltx-gen" "self" z-4 a)
            (p "ltx-gen" "priv-stor" z-4 priv-stor-2)
            (p "ltx-gen" "l" z-4 l-0) (p "ltx-disclose" "self" z-5 a)
            (p "ltx-disclose" "priv-stor" z-5 priv-stor-2)
            (p "ltx-disclose" "l" z-5 l-0)
            (p "ltx-gen" "ignore" z-6 ignore-2)
            (p "ltx-gen" "self" z-6 b)
            (p "ltx-gen" "priv-stor" z-6 priv-stor)
            (p "ltx-gen" "l" z-6 lb) (prec z-1 1 z-2 0)
            (prec z-1 2 z-0 1) (prec z-2 2 z-0 3) (prec z-3 1 z-0 0)
            (prec z-3 2 z-0 3) (prec z-4 1 z-5 0) (prec z-4 2 z 1)
            (prec z-5 2 z 4) (prec z-6 1 z 0) (prec z-6 2 z 4)
            (uniq-at lb z-6 1) (uniq-at l-0 z-4 1) (uniq-at la z-3 1)
            (uniq-at l z-1 1) (gen-st (pv a la)) (gen-st (pv a l-0))
            (gen-st (pv b l)) (gen-st (pv b lb)) (leads-to z-1 1 z-2 0)
            (leads-to z-3 1 z-0 0) (leads-to z-4 1 z-5 0)
            (leads-to z-6 1 z 0) (fact neq (exp (gen) upsilon) (gen))
            (fact neq (exp (gen) zeta) (gen))))))))

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
        (and (fact undisclosed l) (p "ltx-disclose" z (idx 2))
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
      (implies (and (p "init" z (idx 4)) (p "init" "upsilon" z upsilon))
        (fact neq (exp (gen) upsilon) (gen)))))
  (defgenrule assume-resp-0
    (forall ((z strd) (zeta expt))
      (implies (and (p "resp" z (idx 3)) (p "resp" "zeta" z zeta))
        (fact neq (exp (gen) zeta) (gen)))))
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
    (forall ((z strd) (la rndx) (a name))
      (implies
        (and (p "init" z (idx 1)) (p "init" "la" z la)
          (p "init" "a" z a)) (gen-st (pv a la)))))
  (defgenrule gen-st-resp-0
    (forall ((z strd) (lb rndx) (b name))
      (implies
        (and (p "resp" z (idx 1)) (p "resp" "lb" z lb)
          (p "resp" "b" z b)) (gen-st (pv b lb)))))
  (defgenrule gen-st-ltx-disclose-0
    (forall ((z strd) (l rndx) (self name))
      (implies
        (and (p "ltx-disclose" z (idx 1)) (p "ltx-disclose" "l" z l)
          (p "ltx-disclose" "self" z self)) (gen-st (pv self l)))))
  (lang (sig sign) (body (tuple 3)) (pv (tuple 2))))

(defgoal dhcr-um
  (forall
    ((na nb data) (a b name) (priv-stor locn) (lb rndx) (alpha expt)
      (y rndx) (zeta expt) (z strd))
    (implies
      (and (p "resp" z 5) (p "resp" "na" z na) (p "resp" "nb" z nb)
        (p "resp" "a" z a) (p "resp" "b" z b)
        (p "resp" "priv-stor" z priv-stor) (p "resp" "lb" z lb)
        (p "resp" "y" z y) (p "resp" "alpha" z alpha)
        (p "resp" "zeta" z zeta) (non (privk "sig" a)) (ugen y)
        (uniq-at nb z 3) (fact neq a b) (fact undisclosed lb)
        (fact undisclosed alpha))
      (false))))

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
        (and (fact undisclosed l) (p "ltx-disclose" z (idx 2))
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
      (implies (and (p "init" z (idx 4)) (p "init" "upsilon" z upsilon))
        (fact neq (exp (gen) upsilon) (gen)))))
  (defgenrule assume-resp-0
    (forall ((z strd) (zeta expt))
      (implies (and (p "resp" z (idx 3)) (p "resp" "zeta" z zeta))
        (fact neq (exp (gen) zeta) (gen)))))
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
    (forall ((z strd) (la rndx) (a name))
      (implies
        (and (p "init" z (idx 1)) (p "init" "la" z la)
          (p "init" "a" z a)) (gen-st (pv a la)))))
  (defgenrule gen-st-resp-0
    (forall ((z strd) (lb rndx) (b name))
      (implies
        (and (p "resp" z (idx 1)) (p "resp" "lb" z lb)
          (p "resp" "b" z b)) (gen-st (pv b lb)))))
  (defgenrule gen-st-ltx-disclose-0
    (forall ((z strd) (l rndx) (self name))
      (implies
        (and (p "ltx-disclose" z (idx 1)) (p "ltx-disclose" "l" z l)
          (p "ltx-disclose" "self" z self)) (gen-st (pv self l)))))
  (lang (sig sign) (body (tuple 3)) (pv (tuple 2))))

(defgoal dhcr-um
  (forall
    ((na nb data) (a b name) (priv-stor locn) (lb rndx) (alpha expt)
      (y rndx) (zeta expt) (z strd))
    (implies
      (and (p "resp" z 5) (p "resp" "na" z na) (p "resp" "nb" z nb)
        (p "resp" "a" z a) (p "resp" "b" z b)
        (p "resp" "priv-stor" z priv-stor) (p "resp" "lb" z lb)
        (p "resp" "y" z y) (p "resp" "alpha" z alpha)
        (p "resp" "zeta" z zeta) (non (privk "sig" a)) (ugen y)
        (uniq-at nb z 3) (fact neq a b) (fact undisclosed alpha))
      (exists
        ((ignore ignore-0 mesg) (priv-stor-0 locn) (l rndx)
          (z-0 z-1 z-2 strd))
        (and (= alpha l) (p "ltx-gen" z-0 2) (p "ltx-gen" z-1 3)
          (p "ltx-disclose" z-2 3) (p "resp" "alpha" z l)
          (p "ltx-gen" "ignore" z-0 ignore) (p "ltx-gen" "self" z-0 b)
          (p "ltx-gen" "priv-stor" z-0 priv-stor)
          (p "ltx-gen" "l" z-0 lb) (p "ltx-gen" "ignore" z-1 ignore-0)
          (p "ltx-gen" "self" z-1 a)
          (p "ltx-gen" "priv-stor" z-1 priv-stor-0)
          (p "ltx-gen" "l" z-1 l) (p "ltx-disclose" "self" z-2 b)
          (p "ltx-disclose" "priv-stor" z-2 priv-stor)
          (p "ltx-disclose" "l" z-2 lb) (prec z-0 1 z 0)
          (prec z-0 1 z-2 0) (prec z-1 2 z 1) (prec z-2 2 z 4)
          (uniq-at l z-1 1) (uniq-at lb z-0 1) (gen-st (pv b lb))
          (leads-to z-0 1 z 0) (leads-to z-0 1 z-2 0)
          (fact neq (exp (gen) zeta) (gen)) (fact undisclosed l))))))

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
        (and (fact undisclosed l) (p "ltx-disclose" z (idx 2))
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
      (implies (and (p "init" z (idx 4)) (p "init" "upsilon" z upsilon))
        (fact neq (exp (gen) upsilon) (gen)))))
  (defgenrule assume-resp-0
    (forall ((z strd) (zeta expt))
      (implies (and (p "resp" z (idx 3)) (p "resp" "zeta" z zeta))
        (fact neq (exp (gen) zeta) (gen)))))
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
    (forall ((z strd) (la rndx) (a name))
      (implies
        (and (p "init" z (idx 1)) (p "init" "la" z la)
          (p "init" "a" z a)) (gen-st (pv a la)))))
  (defgenrule gen-st-resp-0
    (forall ((z strd) (lb rndx) (b name))
      (implies
        (and (p "resp" z (idx 1)) (p "resp" "lb" z lb)
          (p "resp" "b" z b)) (gen-st (pv b lb)))))
  (defgenrule gen-st-ltx-disclose-0
    (forall ((z strd) (l rndx) (self name))
      (implies
        (and (p "ltx-disclose" z (idx 1)) (p "ltx-disclose" "l" z l)
          (p "ltx-disclose" "self" z self)) (gen-st (pv self l)))))
  (lang (sig sign) (body (tuple 3)) (pv (tuple 2))))

(defgoal dhcr-um
  (forall
    ((na nb data) (a b name) (priv-stor locn) (lb y rndx)
      (alpha zeta expt) (z strd))
    (implies
      (and (p "resp" z 5) (p "resp" "na" z na) (p "resp" "nb" z nb)
        (p "resp" "a" z a) (p "resp" "b" z b)
        (p "resp" "priv-stor" z priv-stor) (p "resp" "lb" z lb)
        (p "resp" "y" z y) (p "resp" "alpha" z alpha)
        (p "resp" "zeta" z zeta) (non (privk "sig" a)) (ugen y)
        (uniq-at nb z 3) (fact neq a b) (fact undisclosed lb))
      (exists
        ((ignore ignore-0 mesg) (priv-stor-0 locn) (l rndx)
          (z-0 z-1 z-2 strd))
        (and (= alpha l) (p "ltx-gen" z-0 3) (p "ltx-disclose" z-1 3)
          (p "ltx-gen" z-2 3) (p "resp" "alpha" z l)
          (p "ltx-gen" "ignore" z-0 ignore) (p "ltx-gen" "self" z-0 a)
          (p "ltx-gen" "priv-stor" z-0 priv-stor-0)
          (p "ltx-gen" "l" z-0 l) (p "ltx-disclose" "self" z-1 a)
          (p "ltx-disclose" "priv-stor" z-1 priv-stor-0)
          (p "ltx-disclose" "l" z-1 l)
          (p "ltx-gen" "ignore" z-2 ignore-0) (p "ltx-gen" "self" z-2 b)
          (p "ltx-gen" "priv-stor" z-2 priv-stor)
          (p "ltx-gen" "l" z-2 lb) (prec z-0 1 z-1 0) (prec z-0 2 z 1)
          (prec z-1 2 z 4) (prec z-2 1 z 0) (prec z-2 2 z 4)
          (uniq-at lb z-2 1) (uniq-at l z-0 1) (gen-st (pv a l))
          (gen-st (pv b lb)) (leads-to z-0 1 z-1 0) (leads-to z-2 1 z 0)
          (fact neq (exp (gen) zeta) (gen)))))))

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
        (and (fact undisclosed l) (p "ltx-disclose" z (idx 2))
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
      (implies (and (p "init" z (idx 4)) (p "init" "upsilon" z upsilon))
        (fact neq (exp (gen) upsilon) (gen)))))
  (defgenrule assume-resp-0
    (forall ((z strd) (zeta expt))
      (implies (and (p "resp" z (idx 3)) (p "resp" "zeta" z zeta))
        (fact neq (exp (gen) zeta) (gen)))))
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
    (forall ((z strd) (la rndx) (a name))
      (implies
        (and (p "init" z (idx 1)) (p "init" "la" z la)
          (p "init" "a" z a)) (gen-st (pv a la)))))
  (defgenrule gen-st-resp-0
    (forall ((z strd) (lb rndx) (b name))
      (implies
        (and (p "resp" z (idx 1)) (p "resp" "lb" z lb)
          (p "resp" "b" z b)) (gen-st (pv b lb)))))
  (defgenrule gen-st-ltx-disclose-0
    (forall ((z strd) (l rndx) (self name))
      (implies
        (and (p "ltx-disclose" z (idx 1)) (p "ltx-disclose" "l" z l)
          (p "ltx-disclose" "self" z self)) (gen-st (pv self l)))))
  (lang (sig sign) (body (tuple 3)) (pv (tuple 2))))

(defgoal dhcr-um
  (forall
    ((na nb data) (a b name) (priv-stor locn) (lb y rndx)
      (alpha zeta expt) (z strd))
    (implies
      (and (p "resp" z 5) (p "resp" "na" z na) (p "resp" "nb" z nb)
        (p "resp" "a" z a) (p "resp" "b" z b)
        (p "resp" "priv-stor" z priv-stor) (p "resp" "lb" z lb)
        (p "resp" "y" z y) (p "resp" "alpha" z alpha)
        (p "resp" "zeta" z zeta) (non (privk "sig" a)) (ugen y)
        (uniq-at nb z 3) (fact neq a b))
      (or
        (exists
          ((ignore ignore-0 mesg) (priv-stor-0 locn) (l rndx)
            (z-0 z-1 z-2 strd))
          (and (= alpha l) (p "ltx-gen" z-0 3) (p "ltx-disclose" z-1 3)
            (p "ltx-gen" z-2 3) (p "resp" "alpha" z l)
            (p "ltx-gen" "ignore" z-0 ignore) (p "ltx-gen" "self" z-0 a)
            (p "ltx-gen" "priv-stor" z-0 priv-stor-0)
            (p "ltx-gen" "l" z-0 l) (p "ltx-disclose" "self" z-1 a)
            (p "ltx-disclose" "priv-stor" z-1 priv-stor-0)
            (p "ltx-disclose" "l" z-1 l)
            (p "ltx-gen" "ignore" z-2 ignore-0)
            (p "ltx-gen" "self" z-2 b)
            (p "ltx-gen" "priv-stor" z-2 priv-stor)
            (p "ltx-gen" "l" z-2 lb) (prec z-0 1 z-1 0) (prec z-0 2 z 1)
            (prec z-1 2 z 4) (prec z-2 1 z 0) (prec z-2 2 z 4)
            (uniq-at lb z-2 1) (uniq-at l z-0 1) (gen-st (pv a l))
            (gen-st (pv b lb)) (leads-to z-0 1 z-1 0)
            (leads-to z-2 1 z 0) (fact neq (exp (gen) zeta) (gen))))
        (exists
          ((ignore ignore-0 mesg) (priv-stor-0 locn) (l rndx)
            (z-0 z-1 z-2 strd))
          (and (= alpha l) (p "ltx-gen" z-0 2) (p "ltx-gen" z-1 3)
            (p "ltx-disclose" z-2 3) (p "resp" "alpha" z l)
            (p "ltx-gen" "ignore" z-0 ignore) (p "ltx-gen" "self" z-0 b)
            (p "ltx-gen" "priv-stor" z-0 priv-stor)
            (p "ltx-gen" "l" z-0 lb) (p "ltx-gen" "ignore" z-1 ignore-0)
            (p "ltx-gen" "self" z-1 a)
            (p "ltx-gen" "priv-stor" z-1 priv-stor-0)
            (p "ltx-gen" "l" z-1 l) (p "ltx-disclose" "self" z-2 b)
            (p "ltx-disclose" "priv-stor" z-2 priv-stor)
            (p "ltx-disclose" "l" z-2 lb) (prec z-0 1 z 0)
            (prec z-0 1 z-2 0) (prec z-1 2 z 1) (prec z-2 2 z 4)
            (uniq-at l z-1 1) (uniq-at lb z-0 1) (gen-st (pv b lb))
            (leads-to z-0 1 z 0) (leads-to z-0 1 z-2 0)
            (fact neq (exp (gen) zeta) (gen))))
        (exists
          ((ignore ignore-0 mesg) (priv-stor-0 locn) (l rndx)
            (z-0 z-1 z-2 strd))
          (and (= alpha l) (p "ltx-gen" z-0 2) (p "ltx-gen" z-1 3)
            (p "ltx-disclose" z-2 3) (p "resp" "alpha" z l)
            (p "ltx-gen" "ignore" z-0 ignore) (p "ltx-gen" "self" z-0 b)
            (p "ltx-gen" "priv-stor" z-0 priv-stor)
            (p "ltx-gen" "l" z-0 lb) (p "ltx-gen" "ignore" z-1 ignore-0)
            (p "ltx-gen" "self" z-1 a)
            (p "ltx-gen" "priv-stor" z-1 priv-stor-0)
            (p "ltx-gen" "l" z-1 l) (p "ltx-disclose" "self" z-2 b)
            (p "ltx-disclose" "priv-stor" z-2 priv-stor)
            (p "ltx-disclose" "l" z-2 lb) (prec z-0 1 z 0)
            (prec z-0 1 z-2 0) (prec z-1 2 z 1) (prec z-2 2 z 4)
            (uniq-at l z-1 1) (uniq-at lb z-0 1) (gen-st (pv a l))
            (gen-st (pv b lb)) (leads-to z-0 1 z 0)
            (leads-to z-0 1 z-2 0)
            (fact neq (exp (gen) zeta) (gen))))))))

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
        (and (fact undisclosed l) (p "ltx-disclose" z (idx 2))
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
      (implies (and (p "init" z (idx 4)) (p "init" "upsilon" z upsilon))
        (fact neq (exp (gen) upsilon) (gen)))))
  (defgenrule assume-resp-0
    (forall ((z strd) (zeta expt))
      (implies (and (p "resp" z (idx 3)) (p "resp" "zeta" z zeta))
        (fact neq (exp (gen) zeta) (gen)))))
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
    (forall ((z strd) (la rndx) (a name))
      (implies
        (and (p "init" z (idx 1)) (p "init" "la" z la)
          (p "init" "a" z a)) (gen-st (pv a la)))))
  (defgenrule gen-st-resp-0
    (forall ((z strd) (lb rndx) (b name))
      (implies
        (and (p "resp" z (idx 1)) (p "resp" "lb" z lb)
          (p "resp" "b" z b)) (gen-st (pv b lb)))))
  (defgenrule gen-st-ltx-disclose-0
    (forall ((z strd) (l rndx) (self name))
      (implies
        (and (p "ltx-disclose" z (idx 1)) (p "ltx-disclose" "l" z l)
          (p "ltx-disclose" "self" z self)) (gen-st (pv self l)))))
  (lang (sig sign) (body (tuple 3)) (pv (tuple 2))))

(defgoal dhcr-um
  (forall
    ((ignore mesg) (na nb data) (a b self name)
      (priv-stor priv-stor-0 locn) (la beta x rndx) (upsilon expt)
      (z z-0 strd))
    (implies
      (and (p "init" z 4) (p "ltx-gen" z-0 3) (p "init" "na" z na)
        (p "init" "nb" z nb) (p "init" "a" z a) (p "init" "b" z b)
        (p "init" "priv-stor" z priv-stor) (p "init" "la" z la)
        (p "init" "x" z x) (p "init" "beta" z beta)
        (p "init" "upsilon" z upsilon) (p "ltx-gen" "ignore" z-0 ignore)
        (p "ltx-gen" "self" z-0 self)
        (p "ltx-gen" "priv-stor" z-0 priv-stor-0)
        (p "ltx-gen" "l" z-0 beta) (ugen x) (uniq-at na z 2)
        (uniq-at beta z-0 1) (fact neq a b))
      (or
        (exists ((z-1 strd))
          (and (= beta la) (= self a) (= priv-stor-0 priv-stor)
            (p "ltx-disclose" z-1 3) (p "init" "beta" z la)
            (p "ltx-gen" "self" z-0 a)
            (p "ltx-gen" "priv-stor" z-0 priv-stor)
            (p "ltx-gen" "l" z-0 la) (p "ltx-disclose" "self" z-1 a)
            (p "ltx-disclose" "priv-stor" z-1 priv-stor)
            (p "ltx-disclose" "l" z-1 la) (prec z-0 1 z 0)
            (prec z-0 1 z-1 0) (prec z-1 2 z 1) (uniq-at la z-0 1)
            (gen-st (pv a la)) (leads-to z-0 1 z 0)
            (leads-to z-0 1 z-1 0)
            (fact neq (exp (gen) upsilon) (gen))))
        (exists ((ignore-0 mesg) (y rndx) (z-1 z-2 strd))
          (and (= upsilon y) (= self b) (p "resp" z-1 4)
            (p "ltx-gen" z-2 3) (p "init" "upsilon" z y)
            (p "ltx-gen" "self" z-0 b) (p "resp" "na" z-1 na)
            (p "resp" "nb" z-1 nb) (p "resp" "a" z-1 a)
            (p "resp" "b" z-1 b) (p "resp" "priv-stor" z-1 priv-stor-0)
            (p "resp" "lb" z-1 beta) (p "resp" "y" z-1 y)
            (p "resp" "alpha" z-1 la) (p "resp" "zeta" z-1 x)
            (p "ltx-gen" "ignore" z-2 ignore-0)
            (p "ltx-gen" "self" z-2 a)
            (p "ltx-gen" "priv-stor" z-2 priv-stor)
            (p "ltx-gen" "l" z-2 la) (prec z 2 z-1 2) (prec z-0 1 z-1 0)
            (prec z-0 2 z 1) (prec z-1 3 z 3) (prec z-2 1 z 0)
            (prec z-2 2 z-1 1) (ugen y) (uniq-at nb z-1 3)
            (uniq-at la z-2 1) (gen-st (pv b beta)) (gen-st (pv a la))
            (leads-to z-0 1 z-1 0) (leads-to z-2 1 z 0)
            (fact neq (exp (gen) y) (gen))
            (fact neq (exp (gen) x) (gen))))
        (exists ((z-1 strd))
          (and (= beta la) (= self a) (= priv-stor-0 priv-stor)
            (p "ltx-disclose" z-1 3) (p "init" "beta" z la)
            (p "ltx-gen" "self" z-0 a)
            (p "ltx-gen" "priv-stor" z-0 priv-stor)
            (p "ltx-gen" "l" z-0 la) (p "ltx-disclose" "self" z-1 a)
            (p "ltx-disclose" "priv-stor" z-1 priv-stor)
            (p "ltx-disclose" "l" z-1 la) (prec z-0 1 z 0)
            (prec z-0 1 z-1 0) (prec z-0 2 z 1) (prec z-1 2 z 3)
            (uniq-at la z-0 1) (gen-st (pv a la)) (leads-to z-0 1 z 0)
            (leads-to z-0 1 z-1 0)
            (fact neq (exp (gen) upsilon) (gen))))
        (exists ((ignore-0 mesg) (z-1 z-2 strd))
          (and (p "ltx-disclose" z-1 3) (p "ltx-gen" z-2 3)
            (p "ltx-disclose" "self" z-1 self)
            (p "ltx-disclose" "priv-stor" z-1 priv-stor-0)
            (p "ltx-disclose" "l" z-1 beta)
            (p "ltx-gen" "ignore" z-2 ignore-0)
            (p "ltx-gen" "self" z-2 a)
            (p "ltx-gen" "priv-stor" z-2 priv-stor)
            (p "ltx-gen" "l" z-2 la) (prec z-0 1 z-1 0) (prec z-0 2 z 1)
            (prec z-1 2 z 3) (prec z-2 1 z 0) (prec z-2 2 z 3)
            (uniq-at la z-2 1) (gen-st (pv self beta))
            (gen-st (pv a la)) (leads-to z-0 1 z-1 0)
            (leads-to z-2 1 z 0) (fact neq (exp (gen) upsilon) (gen))))
        (exists ((ignore-0 mesg) (z-1 z-2 strd))
          (and (p "ltx-gen" z-1 2) (p "ltx-disclose" z-2 3)
            (p "ltx-gen" "ignore" z-1 ignore-0)
            (p "ltx-gen" "self" z-1 a)
            (p "ltx-gen" "priv-stor" z-1 priv-stor)
            (p "ltx-gen" "l" z-1 la) (p "ltx-disclose" "self" z-2 a)
            (p "ltx-disclose" "priv-stor" z-2 priv-stor)
            (p "ltx-disclose" "l" z-2 la) (prec z-0 2 z 1)
            (prec z-1 1 z 0) (prec z-1 1 z-2 0) (prec z-2 2 z 3)
            (uniq-at la z-1 1) (gen-st (pv a la)) (leads-to z-1 1 z 0)
            (leads-to z-1 1 z-2 0)
            (fact neq (exp (gen) upsilon) (gen))))
        (exists ((ignore-0 mesg) (y rndx) (z-1 z-2 strd))
          (and (= upsilon y) (p "ltx-gen" z-1 2)
            (p "ltx-disclose" z-2 3) (p "init" "upsilon" z y)
            (p "ltx-gen" "ignore" z-1 ignore-0)
            (p "ltx-gen" "self" z-1 a)
            (p "ltx-gen" "priv-stor" z-1 priv-stor)
            (p "ltx-gen" "l" z-1 la) (p "ltx-disclose" "self" z-2 a)
            (p "ltx-disclose" "priv-stor" z-2 priv-stor)
            (p "ltx-disclose" "l" z-2 la) (prec z-0 2 z 1)
            (prec z-1 1 z 0) (prec z-1 1 z-2 0) (prec z-2 2 z 3)
            (uniq-at la z-1 1) (gen-st (pv a la))
            (gen-st (pv self beta)) (leads-to z-1 1 z 0)
            (leads-to z-1 1 z-2 0) (fact neq (exp (gen) y) (gen))))
        (exists ((ignore-0 mesg) (y rndx) (z-1 z-2 strd))
          (and (= upsilon y) (p "ltx-disclose" z-1 3)
            (p "ltx-gen" z-2 3) (p "init" "upsilon" z y)
            (p "ltx-disclose" "self" z-1 self)
            (p "ltx-disclose" "priv-stor" z-1 priv-stor-0)
            (p "ltx-disclose" "l" z-1 beta)
            (p "ltx-gen" "ignore" z-2 ignore-0)
            (p "ltx-gen" "self" z-2 a)
            (p "ltx-gen" "priv-stor" z-2 priv-stor)
            (p "ltx-gen" "l" z-2 la) (prec z-0 1 z-1 0) (prec z-1 2 z 1)
            (prec z-2 1 z 0) (prec z-2 2 z 3) (uniq-at la z-2 1)
            (gen-st (pv self beta)) (gen-st (pv a la))
            (leads-to z-0 1 z-1 0) (leads-to z-2 1 z 0)
            (fact neq (exp (gen) y) (gen))))
        (exists ((ignore-0 mesg) (z-1 z-2 strd))
          (and (p "ltx-disclose" z-1 3) (p "ltx-gen" z-2 3)
            (p "ltx-disclose" "self" z-1 self)
            (p "ltx-disclose" "priv-stor" z-1 priv-stor-0)
            (p "ltx-disclose" "l" z-1 beta)
            (p "ltx-gen" "ignore" z-2 ignore-0)
            (p "ltx-gen" "self" z-2 a)
            (p "ltx-gen" "priv-stor" z-2 priv-stor)
            (p "ltx-gen" "l" z-2 la) (prec z-0 1 z-1 0) (prec z-1 2 z 1)
            (prec z-2 1 z 0) (prec z-2 2 z 3) (uniq-at la z-2 1)
            (gen-st (pv self beta)) (gen-st (pv a la))
            (leads-to z-0 1 z-1 0) (leads-to z-2 1 z 0)
            (fact neq (exp (gen) upsilon) (gen))))
        (exists ((ignore-0 mesg) (w expt) (y rndx) (z-1 z-2 strd))
          (and (= upsilon (mul w y)) (p "ltx-gen" z-1 2)
            (p "ltx-disclose" z-2 3) (p "init" "upsilon" z (mul w y))
            (p "ltx-gen" "ignore" z-1 ignore-0)
            (p "ltx-gen" "self" z-1 a)
            (p "ltx-gen" "priv-stor" z-1 priv-stor)
            (p "ltx-gen" "l" z-1 la) (p "ltx-disclose" "self" z-2 a)
            (p "ltx-disclose" "priv-stor" z-2 priv-stor)
            (p "ltx-disclose" "l" z-2 la) (prec z-0 2 z 1)
            (prec z-1 1 z 0) (prec z-1 1 z-2 0) (prec z-2 2 z 3)
            (uniq-at la z-1 1) (gen-st (pv a la))
            (gen-st (pv self beta)) (leads-to z-1 1 z 0)
            (leads-to z-1 1 z-2 0)
            (fact neq (exp (gen) (mul w y)) (gen))))
        (exists ((ignore-0 mesg) (z-1 z-2 z-3 strd))
          (and (p "ltx-gen" z-1 2) (p "ltx-disclose" z-2 3)
            (p "ltx-disclose" z-3 3) (p "ltx-gen" "ignore" z-1 ignore-0)
            (p "ltx-gen" "self" z-1 a)
            (p "ltx-gen" "priv-stor" z-1 priv-stor)
            (p "ltx-gen" "l" z-1 la) (p "ltx-disclose" "self" z-2 self)
            (p "ltx-disclose" "priv-stor" z-2 priv-stor-0)
            (p "ltx-disclose" "l" z-2 beta)
            (p "ltx-disclose" "self" z-3 a)
            (p "ltx-disclose" "priv-stor" z-3 priv-stor)
            (p "ltx-disclose" "l" z-3 la) (prec z-0 1 z-2 0)
            (prec z-1 1 z 0) (prec z-1 1 z-3 0) (prec z-2 2 z 1)
            (prec z-3 2 z 3) (uniq-at la z-1 1) (gen-st (pv a la))
            (gen-st (pv self beta)) (leads-to z-0 1 z-2 0)
            (leads-to z-1 1 z 0) (leads-to z-1 1 z-3 0)
            (fact neq (exp (gen) upsilon) (gen))))
        (exists ((ignore-0 mesg) (y rndx) (z-1 z-2 z-3 strd))
          (and (= upsilon y) (p "ltx-gen" z-1 2)
            (p "ltx-disclose" z-2 3) (p "ltx-disclose" z-3 3)
            (p "init" "upsilon" z y) (p "ltx-gen" "ignore" z-1 ignore-0)
            (p "ltx-gen" "self" z-1 a)
            (p "ltx-gen" "priv-stor" z-1 priv-stor)
            (p "ltx-gen" "l" z-1 la) (p "ltx-disclose" "self" z-2 self)
            (p "ltx-disclose" "priv-stor" z-2 priv-stor-0)
            (p "ltx-disclose" "l" z-2 beta)
            (p "ltx-disclose" "self" z-3 a)
            (p "ltx-disclose" "priv-stor" z-3 priv-stor)
            (p "ltx-disclose" "l" z-3 la) (prec z-0 1 z-2 0)
            (prec z-1 1 z 0) (prec z-1 1 z-3 0) (prec z-2 2 z 1)
            (prec z-3 2 z 3) (uniq-at la z-1 1) (gen-st (pv a la))
            (gen-st (pv self beta)) (leads-to z-0 1 z-2 0)
            (leads-to z-1 1 z 0) (leads-to z-1 1 z-3 0)
            (fact neq (exp (gen) y) (gen))))
        (exists ((y rndx) (z-1 strd))
          (and (= beta la) (= upsilon y) (= self a)
            (= priv-stor-0 priv-stor) (p "ltx-disclose" z-1 3)
            (p "init" "beta" z la) (p "init" "upsilon" z y)
            (p "ltx-gen" "self" z-0 a)
            (p "ltx-gen" "priv-stor" z-0 priv-stor)
            (p "ltx-gen" "l" z-0 la) (p "ltx-disclose" "self" z-1 a)
            (p "ltx-disclose" "priv-stor" z-1 priv-stor)
            (p "ltx-disclose" "l" z-1 la) (prec z-0 1 z 0)
            (prec z-0 1 z-1 0) (prec z-0 2 z 1) (prec z-1 2 z 3)
            (uniq-at la z-0 1) (gen-st (pv a la)) (leads-to z-0 1 z 0)
            (leads-to z-0 1 z-1 0) (fact neq (exp (gen) y) (gen))))
        (exists ((ignore-0 mesg) (y rndx) (z-1 z-2 strd))
          (and (= upsilon y) (p "ltx-disclose" z-1 3)
            (p "ltx-gen" z-2 3) (p "init" "upsilon" z y)
            (p "ltx-disclose" "self" z-1 self)
            (p "ltx-disclose" "priv-stor" z-1 priv-stor-0)
            (p "ltx-disclose" "l" z-1 beta)
            (p "ltx-gen" "ignore" z-2 ignore-0)
            (p "ltx-gen" "self" z-2 a)
            (p "ltx-gen" "priv-stor" z-2 priv-stor)
            (p "ltx-gen" "l" z-2 la) (prec z-0 1 z-1 0) (prec z-0 2 z 1)
            (prec z-1 2 z 3) (prec z-2 1 z 0) (prec z-2 2 z 3)
            (uniq-at la z-2 1) (gen-st (pv self beta))
            (gen-st (pv a la)) (leads-to z-0 1 z-1 0)
            (leads-to z-2 1 z 0) (fact neq (exp (gen) y) (gen))))
        (exists ((ignore-0 mesg) (y rndx) (z-1 z-2 strd))
          (and (= upsilon y) (p "ltx-gen" z-1 2)
            (p "ltx-disclose" z-2 3) (p "init" "upsilon" z y)
            (p "ltx-gen" "ignore" z-1 ignore-0)
            (p "ltx-gen" "self" z-1 a)
            (p "ltx-gen" "priv-stor" z-1 priv-stor)
            (p "ltx-gen" "l" z-1 la) (p "ltx-disclose" "self" z-2 a)
            (p "ltx-disclose" "priv-stor" z-2 priv-stor)
            (p "ltx-disclose" "l" z-2 la) (prec z-0 2 z 1)
            (prec z-1 1 z 0) (prec z-1 1 z-2 0) (prec z-2 2 z 3)
            (uniq-at la z-1 1) (gen-st (pv a la)) (leads-to z-1 1 z 0)
            (leads-to z-1 1 z-2 0) (fact neq (exp (gen) y) (gen))))))))
