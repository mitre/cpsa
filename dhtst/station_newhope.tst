(herald "Station-to-station protocol" (algebra diffie-hellman))

(comment "CPSA 4.3.0")
(comment "All input read from dhtst/station_newhope.scm")

(defprotocol station-to-station diffie-hellman
  (defrole init
    (vars (xi rndx) (xr expt) (i r name) (hint mesg))
    (trace (send (exp (gen) xi))
      (recv
        (cat (exp (gen) xr) hint
          (enc (enc (exp (gen) xr) (exp (gen) xi) hint (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi)
              hint))))
      (send
        (cat
          (enc (enc (exp (gen) xi) (exp (gen) xr) hint (privk i))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xr) hint))
          (enc (enc (exp (gen) xi) (exp (gen) xr) hint (privk i))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi)
              hint))))))
  (defrole resp
    (vars (xr rndx) (xi expt) (i r name))
    (trace (recv (exp (gen) xi))
      (send
        (cat (exp (gen) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
          (enc
            (enc (exp (gen) xr) (exp (gen) xi)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
              (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
          (enc
            (enc (exp (gen) xr) (exp (gen) xi)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
              (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xi)
              (hash "hint"
                (hash "share" (exp (gen) (mul xr xi)) xr))))))
      (recv
        (enc
          (enc (exp (gen) xi) (exp (gen) xr)
            (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
            (privk i))
          (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
            (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr)))))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defgenrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2)) (false))))
  (defgenrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defgenrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1)))))
  (defgenrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2))))))

(defskeleton station-to-station
  (vars (hint mesg) (i r name) (xi rndx) (xr expt))
  (defstrand init 3 (hint hint) (i i) (r r) (xi xi) (xr xr))
  (non-orig (privk i) (privk r))
  (uniq-gen xi)
  (traces
    ((send (exp (gen) xi))
      (recv
        (cat (exp (gen) xr) hint
          (enc (enc (exp (gen) xr) (exp (gen) xi) hint (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi)
              hint))))
      (send
        (cat
          (enc (enc (exp (gen) xi) (exp (gen) xr) hint (privk i))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xr) hint))
          (enc (enc (exp (gen) xi) (exp (gen) xr) hint (privk i))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi)
              hint))))))
  (label 0)
  (unrealized (0 1))
  (origs)
  (comment "3 in cohort - 3 not yet seen"))

(defskeleton station-to-station
  (vars (hint mesg) (i r r-0 name) (xi xi-0 rndx))
  (defstrand init 3 (hint hint) (i i) (r r) (xi xi-0) (xr xi))
  (defstrand init 3 (hint hint) (i r) (r r-0) (xi xi) (xr xi-0))
  (precedes ((0 0) (1 1)) ((1 2) (0 1)))
  (non-orig (privk i) (privk r))
  (uniq-gen xi-0)
  (operation encryption-test (added-strand init 3)
    (enc (enc (exp (gen) xi) (exp (gen) xi-0) hint (privk r))
      (hash "key" (hash "share" (exp (gen) (mul xi xi-0)) xi-0) hint))
    (0 1))
  (traces
    ((send (exp (gen) xi-0))
      (recv
        (cat (exp (gen) xi) hint
          (enc (enc (exp (gen) xi) (exp (gen) xi-0) hint (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xi xi-0)) xi-0)
              hint))))
      (send
        (cat
          (enc (enc (exp (gen) xi-0) (exp (gen) xi) hint (privk i))
            (hash "key" (hash "share" (exp (gen) (mul xi xi-0)) xi)
              hint))
          (enc (enc (exp (gen) xi-0) (exp (gen) xi) hint (privk i))
            (hash "key" (hash "share" (exp (gen) (mul xi xi-0)) xi-0)
              hint)))))
    ((send (exp (gen) xi))
      (recv
        (cat (exp (gen) xi-0) hint
          (enc (enc (exp (gen) xi-0) (exp (gen) xi) hint (privk r-0))
            (hash "key" (hash "share" (exp (gen) (mul xi xi-0)) xi)
              hint))))
      (send
        (cat
          (enc (enc (exp (gen) xi) (exp (gen) xi-0) hint (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xi xi-0)) xi-0)
              hint))
          (enc (enc (exp (gen) xi) (exp (gen) xi-0) hint (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xi xi-0)) xi)
              hint))))))
  (label 1)
  (parent 0)
  (unrealized)
  (shape)
  (maps ((0) ((i i) (r r) (xi xi-0) (xr xi) (hint hint))))
  (origs))

(defskeleton station-to-station
  (vars (i r name) (xr xi rndx))
  (defstrand init 3
    (hint (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))) (i i)
    (r r) (xi xi) (xr xr))
  (defstrand resp 2 (r r) (xr xr) (xi xi))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk i) (privk r))
  (uniq-gen xi)
  (operation encryption-test (added-strand resp 2)
    (enc
      (enc (exp (gen) xr) (exp (gen) xi)
        (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
        (privk r))
      (hash "key" (hash "share" (exp (gen) (mul xr xi)) xi)
        (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr)))) (0 1))
  (traces
    ((send (exp (gen) xi))
      (recv
        (cat (exp (gen) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
          (enc
            (enc (exp (gen) xr) (exp (gen) xi)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
              (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xi)
              (hash "hint"
                (hash "share" (exp (gen) (mul xr xi)) xr))))))
      (send
        (cat
          (enc
            (enc (exp (gen) xi) (exp (gen) xr)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
              (privk i))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
          (enc
            (enc (exp (gen) xi) (exp (gen) xr)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
              (privk i))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xi)
              (hash "hint"
                (hash "share" (exp (gen) (mul xr xi)) xr)))))))
    ((recv (exp (gen) xi))
      (send
        (cat (exp (gen) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
          (enc
            (enc (exp (gen) xr) (exp (gen) xi)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
              (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
          (enc
            (enc (exp (gen) xr) (exp (gen) xi)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
              (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xi)
              (hash "hint"
                (hash "share" (exp (gen) (mul xr xi)) xr))))))))
  (label 2)
  (parent 0)
  (unrealized)
  (shape)
  (maps
    ((0)
      ((i i) (r r) (xi xi) (xr xr)
        (hint
          (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))))
  (origs))

(defskeleton station-to-station
  (vars (hint mesg) (i r name) (xi rndx) (xr expt))
  (defstrand init 3 (hint hint) (i i) (r r) (xi xi) (xr xr))
  (deflistener
    (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi) hint))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk i) (privk r))
  (uniq-gen xi)
  (operation encryption-test
    (added-listener
      (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi) hint))
    (enc (enc (exp (gen) xr) (exp (gen) xi) hint (privk r))
      (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi) hint))
    (0 1))
  (traces
    ((send (exp (gen) xi))
      (recv
        (cat (exp (gen) xr) hint
          (enc (enc (exp (gen) xr) (exp (gen) xi) hint (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi)
              hint))))
      (send
        (cat
          (enc (enc (exp (gen) xi) (exp (gen) xr) hint (privk i))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xr) hint))
          (enc (enc (exp (gen) xi) (exp (gen) xr) hint (privk i))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi)
              hint)))))
    ((recv (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi) hint))
      (send
        (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi) hint))))
  (label 3)
  (parent 0)
  (unrealized (0 1) (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton station-to-station
  (vars (hint mesg) (i r name) (xi rndx) (xr expt))
  (defstrand init 3 (hint hint) (i i) (r r) (xi xi) (xr xr))
  (deflistener
    (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi) hint))
  (deflistener
    (cat "key" (hash "share" (exp (gen) (mul xi xr)) xi) hint))
  (precedes ((0 0) (2 0)) ((1 1) (0 1)) ((2 1) (1 0)))
  (non-orig (privk i) (privk r))
  (uniq-gen xi)
  (operation encryption-test
    (added-listener
      (cat "key" (hash "share" (exp (gen) (mul xi xr)) xi) hint))
    (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi) hint) (1 0))
  (traces
    ((send (exp (gen) xi))
      (recv
        (cat (exp (gen) xr) hint
          (enc (enc (exp (gen) xr) (exp (gen) xi) hint (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi)
              hint))))
      (send
        (cat
          (enc (enc (exp (gen) xi) (exp (gen) xr) hint (privk i))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xr) hint))
          (enc (enc (exp (gen) xi) (exp (gen) xr) hint (privk i))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi)
              hint)))))
    ((recv (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi) hint))
      (send
        (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi) hint)))
    ((recv (cat "key" (hash "share" (exp (gen) (mul xi xr)) xi) hint))
      (send
        (cat "key" (hash "share" (exp (gen) (mul xi xr)) xi) hint))))
  (label 4)
  (parent 3)
  (unrealized (0 1) (2 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton station-to-station
  (vars (hint mesg) (i r name) (xi rndx) (xr expt))
  (defstrand init 3 (hint hint) (i i) (r r) (xi xi) (xr xr))
  (deflistener
    (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi) hint))
  (deflistener
    (cat "key" (hash "share" (exp (gen) (mul xi xr)) xi) hint))
  (deflistener (cat "share" (exp (gen) (mul xi xr)) xi))
  (precedes ((0 0) (3 0)) ((1 1) (0 1)) ((2 1) (1 0)) ((3 1) (2 0)))
  (non-orig (privk i) (privk r))
  (uniq-gen xi)
  (operation encryption-test
    (added-listener (cat "share" (exp (gen) (mul xi xr)) xi))
    (hash "share" (exp (gen) (mul xi xr)) xi) (2 0))
  (traces
    ((send (exp (gen) xi))
      (recv
        (cat (exp (gen) xr) hint
          (enc (enc (exp (gen) xr) (exp (gen) xi) hint (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi)
              hint))))
      (send
        (cat
          (enc (enc (exp (gen) xi) (exp (gen) xr) hint (privk i))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xr) hint))
          (enc (enc (exp (gen) xi) (exp (gen) xr) hint (privk i))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi)
              hint)))))
    ((recv (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi) hint))
      (send
        (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi) hint)))
    ((recv (cat "key" (hash "share" (exp (gen) (mul xi xr)) xi) hint))
      (send (cat "key" (hash "share" (exp (gen) (mul xi xr)) xi) hint)))
    ((recv (cat "share" (exp (gen) (mul xi xr)) xi))
      (send (cat "share" (exp (gen) (mul xi xr)) xi))))
  (label 5)
  (parent 4)
  (unrealized (0 1) (3 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol station-to-station diffie-hellman
  (defrole init
    (vars (xi rndx) (xr expt) (i r name) (hint mesg))
    (trace (send (exp (gen) xi))
      (recv
        (cat (exp (gen) xr) hint
          (enc (enc (exp (gen) xr) (exp (gen) xi) hint (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi)
              hint))))
      (send
        (cat
          (enc (enc (exp (gen) xi) (exp (gen) xr) hint (privk i))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xr) hint))
          (enc (enc (exp (gen) xi) (exp (gen) xr) hint (privk i))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi)
              hint))))))
  (defrole resp
    (vars (xr rndx) (xi expt) (i r name))
    (trace (recv (exp (gen) xi))
      (send
        (cat (exp (gen) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
          (enc
            (enc (exp (gen) xr) (exp (gen) xi)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
              (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
          (enc
            (enc (exp (gen) xr) (exp (gen) xi)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
              (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xi)
              (hash "hint"
                (hash "share" (exp (gen) (mul xr xi)) xr))))))
      (recv
        (enc
          (enc (exp (gen) xi) (exp (gen) xr)
            (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
            (privk i))
          (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
            (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr)))))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defgenrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2)) (false))))
  (defgenrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defgenrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1)))))
  (defgenrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2))))))

(defskeleton station-to-station
  (vars (i r name) (xr rndx) (xi expt))
  (defstrand resp 3 (i i) (r r) (xr xr) (xi xi))
  (non-orig (privk i) (privk r))
  (uniq-gen xr)
  (absent (xr xi))
  (traces
    ((recv (exp (gen) xi))
      (send
        (cat (exp (gen) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
          (enc
            (enc (exp (gen) xr) (exp (gen) xi)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
              (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
          (enc
            (enc (exp (gen) xr) (exp (gen) xi)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
              (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xi)
              (hash "hint"
                (hash "share" (exp (gen) (mul xr xi)) xr))))))
      (recv
        (enc
          (enc (exp (gen) xi) (exp (gen) xr)
            (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
            (privk i))
          (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
            (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr)))))))
  (label 6)
  (unrealized (0 2))
  (origs)
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-to-station
  (vars (i r r-0 name) (xi xr rndx))
  (defstrand resp 3 (i i) (r r) (xr xr) (xi xi))
  (defstrand init 3
    (hint (hash "hint" (hash "share" (exp (gen) (mul xi xr)) xr))) (i i)
    (r r-0) (xi xi) (xr xr))
  (precedes ((0 1) (1 1)) ((1 2) (0 2)))
  (non-orig (privk i) (privk r))
  (uniq-gen xr)
  (absent (xr xi))
  (operation encryption-test (added-strand init 3)
    (enc
      (enc (exp (gen) xi) (exp (gen) xr)
        (hash "hint" (hash "share" (exp (gen) (mul xi xr)) xr))
        (privk i))
      (hash "key" (hash "share" (exp (gen) (mul xi xr)) xr)
        (hash "hint" (hash "share" (exp (gen) (mul xi xr)) xr)))) (0 2))
  (traces
    ((recv (exp (gen) xi))
      (send
        (cat (exp (gen) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xi xr)) xr))
          (enc
            (enc (exp (gen) xr) (exp (gen) xi)
              (hash "hint" (hash "share" (exp (gen) (mul xi xr)) xr))
              (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xr)
              (hash "hint" (hash "share" (exp (gen) (mul xi xr)) xr))))
          (enc
            (enc (exp (gen) xr) (exp (gen) xi)
              (hash "hint" (hash "share" (exp (gen) (mul xi xr)) xr))
              (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi)
              (hash "hint"
                (hash "share" (exp (gen) (mul xi xr)) xr))))))
      (recv
        (enc
          (enc (exp (gen) xi) (exp (gen) xr)
            (hash "hint" (hash "share" (exp (gen) (mul xi xr)) xr))
            (privk i))
          (hash "key" (hash "share" (exp (gen) (mul xi xr)) xr)
            (hash "hint" (hash "share" (exp (gen) (mul xi xr)) xr))))))
    ((send (exp (gen) xi))
      (recv
        (cat (exp (gen) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xi xr)) xr))
          (enc
            (enc (exp (gen) xr) (exp (gen) xi)
              (hash "hint" (hash "share" (exp (gen) (mul xi xr)) xr))
              (privk r-0))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi)
              (hash "hint"
                (hash "share" (exp (gen) (mul xi xr)) xr))))))
      (send
        (cat
          (enc
            (enc (exp (gen) xi) (exp (gen) xr)
              (hash "hint" (hash "share" (exp (gen) (mul xi xr)) xr))
              (privk i))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xr)
              (hash "hint" (hash "share" (exp (gen) (mul xi xr)) xr))))
          (enc
            (enc (exp (gen) xi) (exp (gen) xr)
              (hash "hint" (hash "share" (exp (gen) (mul xi xr)) xr))
              (privk i))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi)
              (hash "hint"
                (hash "share" (exp (gen) (mul xi xr)) xr))))))))
  (label 7)
  (parent 6)
  (unrealized)
  (shape)
  (maps ((0) ((i i) (r r) (xr xr) (xi xi))))
  (origs))

(defskeleton station-to-station
  (vars (i r name) (xr rndx) (xi expt))
  (defstrand resp 3 (i i) (r r) (xr xr) (xi xi))
  (deflistener
    (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
      (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
  (precedes ((0 1) (1 0)) ((1 1) (0 2)))
  (non-orig (privk i) (privk r))
  (uniq-gen xr)
  (absent (xr xi))
  (operation encryption-test
    (added-listener
      (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
        (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
    (enc
      (enc (exp (gen) xi) (exp (gen) xr)
        (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
        (privk i))
      (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
        (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr)))) (0 2))
  (traces
    ((recv (exp (gen) xi))
      (send
        (cat (exp (gen) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
          (enc
            (enc (exp (gen) xr) (exp (gen) xi)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
              (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
          (enc
            (enc (exp (gen) xr) (exp (gen) xi)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
              (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xi)
              (hash "hint"
                (hash "share" (exp (gen) (mul xr xi)) xr))))))
      (recv
        (enc
          (enc (exp (gen) xi) (exp (gen) xr)
            (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
            (privk i))
          (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
            (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))))
    ((recv
       (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
         (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
      (send
        (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))))
  (label 8)
  (parent 6)
  (unrealized (0 2) (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton station-to-station
  (vars (i r name) (xr rndx) (xi expt))
  (defstrand resp 3 (i i) (r r) (xr xr) (xi xi))
  (deflistener
    (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
      (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
  (deflistener
    (cat "key" (hash "share" (exp (gen) (mul xr xi)) xr)
      (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
  (precedes ((0 1) (2 0)) ((1 1) (0 2)) ((2 1) (1 0)))
  (non-orig (privk i) (privk r))
  (uniq-gen xr)
  (absent (xr xi))
  (operation encryption-test
    (added-listener
      (cat "key" (hash "share" (exp (gen) (mul xr xi)) xr)
        (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
    (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
      (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))) (1 0))
  (traces
    ((recv (exp (gen) xi))
      (send
        (cat (exp (gen) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
          (enc
            (enc (exp (gen) xr) (exp (gen) xi)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
              (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
          (enc
            (enc (exp (gen) xr) (exp (gen) xi)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
              (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xi)
              (hash "hint"
                (hash "share" (exp (gen) (mul xr xi)) xr))))))
      (recv
        (enc
          (enc (exp (gen) xi) (exp (gen) xr)
            (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
            (privk i))
          (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
            (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))))
    ((recv
       (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
         (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
      (send
        (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr)))))
    ((recv
       (cat "key" (hash "share" (exp (gen) (mul xr xi)) xr)
         (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
      (send
        (cat "key" (hash "share" (exp (gen) (mul xr xi)) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))))
  (label 9)
  (parent 8)
  (unrealized (0 2) (2 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton station-to-station
  (vars (i r name) (xr rndx) (xi expt))
  (defstrand resp 3 (i i) (r r) (xr xr) (xi xi))
  (deflistener
    (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
      (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
  (deflistener
    (cat "key" (hash "share" (exp (gen) (mul xr xi)) xr)
      (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
  (deflistener (cat "share" (exp (gen) (mul xr xi)) xr))
  (precedes ((0 1) (3 0)) ((1 1) (0 2)) ((2 1) (1 0)) ((3 1) (2 0)))
  (non-orig (privk i) (privk r))
  (uniq-gen xr)
  (absent (xr xi))
  (operation encryption-test
    (added-listener (cat "share" (exp (gen) (mul xr xi)) xr))
    (hash "share" (exp (gen) (mul xr xi)) xr) (2 0))
  (traces
    ((recv (exp (gen) xi))
      (send
        (cat (exp (gen) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
          (enc
            (enc (exp (gen) xr) (exp (gen) xi)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
              (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
          (enc
            (enc (exp (gen) xr) (exp (gen) xi)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
              (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xi)
              (hash "hint"
                (hash "share" (exp (gen) (mul xr xi)) xr))))))
      (recv
        (enc
          (enc (exp (gen) xi) (exp (gen) xr)
            (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
            (privk i))
          (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
            (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))))
    ((recv
       (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
         (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
      (send
        (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr)))))
    ((recv
       (cat "key" (hash "share" (exp (gen) (mul xr xi)) xr)
         (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
      (send
        (cat "key" (hash "share" (exp (gen) (mul xr xi)) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr)))))
    ((recv (cat "share" (exp (gen) (mul xr xi)) xr))
      (send (cat "share" (exp (gen) (mul xr xi)) xr))))
  (label 10)
  (parent 9)
  (unrealized (0 2) (3 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol station-to-station diffie-hellman
  (defrole init
    (vars (xi rndx) (xr expt) (i r name) (hint mesg))
    (trace (send (exp (gen) xi))
      (recv
        (cat (exp (gen) xr) hint
          (enc (enc (exp (gen) xr) (exp (gen) xi) hint (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi)
              hint))))
      (send
        (cat
          (enc (enc (exp (gen) xi) (exp (gen) xr) hint (privk i))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xr) hint))
          (enc (enc (exp (gen) xi) (exp (gen) xr) hint (privk i))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi)
              hint))))))
  (defrole resp
    (vars (xr rndx) (xi expt) (i r name))
    (trace (recv (exp (gen) xi))
      (send
        (cat (exp (gen) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
          (enc
            (enc (exp (gen) xr) (exp (gen) xi)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
              (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
          (enc
            (enc (exp (gen) xr) (exp (gen) xi)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
              (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xi)
              (hash "hint"
                (hash "share" (exp (gen) (mul xr xi)) xr))))))
      (recv
        (enc
          (enc (exp (gen) xi) (exp (gen) xr)
            (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
            (privk i))
          (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
            (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr)))))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defgenrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2)) (false))))
  (defgenrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defgenrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1)))))
  (defgenrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2))))))

(defskeleton station-to-station
  (vars (i r name) (xr rndx) (xi expt))
  (defstrand resp 3 (i i) (r r) (xr xr) (xi xi))
  (non-orig (privk i) (privk r))
  (uniq-gen xr)
  (traces
    ((recv (exp (gen) xi))
      (send
        (cat (exp (gen) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
          (enc
            (enc (exp (gen) xr) (exp (gen) xi)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
              (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
          (enc
            (enc (exp (gen) xr) (exp (gen) xi)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
              (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xi)
              (hash "hint"
                (hash "share" (exp (gen) (mul xr xi)) xr))))))
      (recv
        (enc
          (enc (exp (gen) xi) (exp (gen) xr)
            (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
            (privk i))
          (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
            (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr)))))))
  (label 11)
  (unrealized (0 2))
  (origs)
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-to-station
  (vars (i r r-0 name) (xi xr rndx))
  (defstrand resp 3 (i i) (r r) (xr xr) (xi xi))
  (defstrand init 3
    (hint (hash "hint" (hash "share" (exp (gen) (mul xi xr)) xr))) (i i)
    (r r-0) (xi xi) (xr xr))
  (precedes ((0 1) (1 1)) ((1 2) (0 2)))
  (non-orig (privk i) (privk r))
  (uniq-gen xr)
  (operation encryption-test (added-strand init 3)
    (enc
      (enc (exp (gen) xi) (exp (gen) xr)
        (hash "hint" (hash "share" (exp (gen) (mul xi xr)) xr))
        (privk i))
      (hash "key" (hash "share" (exp (gen) (mul xi xr)) xr)
        (hash "hint" (hash "share" (exp (gen) (mul xi xr)) xr)))) (0 2))
  (traces
    ((recv (exp (gen) xi))
      (send
        (cat (exp (gen) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xi xr)) xr))
          (enc
            (enc (exp (gen) xr) (exp (gen) xi)
              (hash "hint" (hash "share" (exp (gen) (mul xi xr)) xr))
              (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xr)
              (hash "hint" (hash "share" (exp (gen) (mul xi xr)) xr))))
          (enc
            (enc (exp (gen) xr) (exp (gen) xi)
              (hash "hint" (hash "share" (exp (gen) (mul xi xr)) xr))
              (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi)
              (hash "hint"
                (hash "share" (exp (gen) (mul xi xr)) xr))))))
      (recv
        (enc
          (enc (exp (gen) xi) (exp (gen) xr)
            (hash "hint" (hash "share" (exp (gen) (mul xi xr)) xr))
            (privk i))
          (hash "key" (hash "share" (exp (gen) (mul xi xr)) xr)
            (hash "hint" (hash "share" (exp (gen) (mul xi xr)) xr))))))
    ((send (exp (gen) xi))
      (recv
        (cat (exp (gen) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xi xr)) xr))
          (enc
            (enc (exp (gen) xr) (exp (gen) xi)
              (hash "hint" (hash "share" (exp (gen) (mul xi xr)) xr))
              (privk r-0))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi)
              (hash "hint"
                (hash "share" (exp (gen) (mul xi xr)) xr))))))
      (send
        (cat
          (enc
            (enc (exp (gen) xi) (exp (gen) xr)
              (hash "hint" (hash "share" (exp (gen) (mul xi xr)) xr))
              (privk i))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xr)
              (hash "hint" (hash "share" (exp (gen) (mul xi xr)) xr))))
          (enc
            (enc (exp (gen) xi) (exp (gen) xr)
              (hash "hint" (hash "share" (exp (gen) (mul xi xr)) xr))
              (privk i))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi)
              (hash "hint"
                (hash "share" (exp (gen) (mul xi xr)) xr))))))))
  (label 12)
  (parent 11)
  (unrealized)
  (shape)
  (maps ((0) ((i i) (r r) (xr xr) (xi xi))))
  (origs))

(defskeleton station-to-station
  (vars (i r name) (xr rndx) (xi expt))
  (defstrand resp 3 (i i) (r r) (xr xr) (xi xi))
  (deflistener
    (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
      (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
  (precedes ((0 1) (1 0)) ((1 1) (0 2)))
  (non-orig (privk i) (privk r))
  (uniq-gen xr)
  (operation encryption-test
    (added-listener
      (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
        (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
    (enc
      (enc (exp (gen) xi) (exp (gen) xr)
        (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
        (privk i))
      (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
        (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr)))) (0 2))
  (traces
    ((recv (exp (gen) xi))
      (send
        (cat (exp (gen) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
          (enc
            (enc (exp (gen) xr) (exp (gen) xi)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
              (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
          (enc
            (enc (exp (gen) xr) (exp (gen) xi)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
              (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xi)
              (hash "hint"
                (hash "share" (exp (gen) (mul xr xi)) xr))))))
      (recv
        (enc
          (enc (exp (gen) xi) (exp (gen) xr)
            (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
            (privk i))
          (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
            (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))))
    ((recv
       (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
         (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
      (send
        (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))))
  (label 13)
  (parent 11)
  (unrealized (0 2) (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton station-to-station
  (vars (i r name) (xr rndx) (xi expt))
  (defstrand resp 3 (i i) (r r) (xr xr) (xi xi))
  (deflistener
    (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
      (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
  (deflistener
    (cat "key" (hash "share" (exp (gen) (mul xr xi)) xr)
      (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
  (precedes ((0 1) (2 0)) ((1 1) (0 2)) ((2 1) (1 0)))
  (non-orig (privk i) (privk r))
  (uniq-gen xr)
  (operation encryption-test
    (added-listener
      (cat "key" (hash "share" (exp (gen) (mul xr xi)) xr)
        (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
    (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
      (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))) (1 0))
  (traces
    ((recv (exp (gen) xi))
      (send
        (cat (exp (gen) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
          (enc
            (enc (exp (gen) xr) (exp (gen) xi)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
              (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
          (enc
            (enc (exp (gen) xr) (exp (gen) xi)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
              (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xi)
              (hash "hint"
                (hash "share" (exp (gen) (mul xr xi)) xr))))))
      (recv
        (enc
          (enc (exp (gen) xi) (exp (gen) xr)
            (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
            (privk i))
          (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
            (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))))
    ((recv
       (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
         (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
      (send
        (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr)))))
    ((recv
       (cat "key" (hash "share" (exp (gen) (mul xr xi)) xr)
         (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
      (send
        (cat "key" (hash "share" (exp (gen) (mul xr xi)) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))))
  (label 14)
  (parent 13)
  (unrealized (0 2) (2 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton station-to-station
  (vars (i r name) (xr rndx) (xi expt))
  (defstrand resp 3 (i i) (r r) (xr xr) (xi xi))
  (deflistener
    (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
      (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
  (deflistener
    (cat "key" (hash "share" (exp (gen) (mul xr xi)) xr)
      (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
  (deflistener (cat "share" (exp (gen) (mul xr xi)) xr))
  (precedes ((0 1) (3 0)) ((1 1) (0 2)) ((2 1) (1 0)) ((3 1) (2 0)))
  (non-orig (privk i) (privk r))
  (uniq-gen xr)
  (operation encryption-test
    (added-listener (cat "share" (exp (gen) (mul xr xi)) xr))
    (hash "share" (exp (gen) (mul xr xi)) xr) (2 0))
  (traces
    ((recv (exp (gen) xi))
      (send
        (cat (exp (gen) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
          (enc
            (enc (exp (gen) xr) (exp (gen) xi)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
              (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
          (enc
            (enc (exp (gen) xr) (exp (gen) xi)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
              (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xi)
              (hash "hint"
                (hash "share" (exp (gen) (mul xr xi)) xr))))))
      (recv
        (enc
          (enc (exp (gen) xi) (exp (gen) xr)
            (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
            (privk i))
          (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
            (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))))
    ((recv
       (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
         (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
      (send
        (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr)))))
    ((recv
       (cat "key" (hash "share" (exp (gen) (mul xr xi)) xr)
         (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
      (send
        (cat "key" (hash "share" (exp (gen) (mul xr xi)) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr)))))
    ((recv (cat "share" (exp (gen) (mul xr xi)) xr))
      (send (cat "share" (exp (gen) (mul xr xi)) xr))))
  (label 15)
  (parent 14)
  (unrealized (0 2) (3 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol station-nohint diffie-hellman
  (defrole init
    (vars (xi rndx) (xr expt) (i r name) (hint mesg))
    (trace (send (exp (gen) xi))
      (recv
        (cat (exp (gen) xr) hint
          (enc (enc "resp" (exp (gen) xr) (exp (gen) xi) (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi)
              hint))))
      (send
        (cat
          (enc (enc (exp (gen) xi) (exp (gen) xr) (privk i))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xr) hint))
          (enc (enc (exp (gen) xi) (exp (gen) xr) (privk i))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi)
              hint))))))
  (defrole resp
    (vars (xr rndx) (xi expt) (i r name))
    (trace (recv (exp (gen) xi))
      (send
        (cat (exp (gen) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
          (enc (enc "resp" (exp (gen) xr) (exp (gen) xi) (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
          (enc (enc "resp" (exp (gen) xr) (exp (gen) xi) (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xi)
              (hash "hint"
                (hash "share" (exp (gen) (mul xr xi)) xr))))))
      (recv
        (enc (enc (exp (gen) xi) (exp (gen) xr) (privk i))
          (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
            (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr)))))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defgenrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2)) (false))))
  (defgenrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defgenrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1)))))
  (defgenrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2))))))

(defskeleton station-nohint
  (vars (hint mesg) (i r name) (xi rndx) (xr expt))
  (defstrand init 3 (hint hint) (i i) (r r) (xi xi) (xr xr))
  (non-orig (privk i) (privk r))
  (uniq-gen xi)
  (traces
    ((send (exp (gen) xi))
      (recv
        (cat (exp (gen) xr) hint
          (enc (enc "resp" (exp (gen) xr) (exp (gen) xi) (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi)
              hint))))
      (send
        (cat
          (enc (enc (exp (gen) xi) (exp (gen) xr) (privk i))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xr) hint))
          (enc (enc (exp (gen) xi) (exp (gen) xr) (privk i))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi)
              hint))))))
  (label 16)
  (unrealized (0 1))
  (origs)
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-nohint
  (vars (i r name) (xr xi rndx))
  (defstrand init 3
    (hint (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))) (i i)
    (r r) (xi xi) (xr xr))
  (defstrand resp 2 (r r) (xr xr) (xi xi))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk i) (privk r))
  (uniq-gen xi)
  (operation encryption-test (added-strand resp 2)
    (enc (enc "resp" (exp (gen) xr) (exp (gen) xi) (privk r))
      (hash "key" (hash "share" (exp (gen) (mul xr xi)) xi)
        (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr)))) (0 1))
  (traces
    ((send (exp (gen) xi))
      (recv
        (cat (exp (gen) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
          (enc (enc "resp" (exp (gen) xr) (exp (gen) xi) (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xi)
              (hash "hint"
                (hash "share" (exp (gen) (mul xr xi)) xr))))))
      (send
        (cat
          (enc (enc (exp (gen) xi) (exp (gen) xr) (privk i))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
          (enc (enc (exp (gen) xi) (exp (gen) xr) (privk i))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xi)
              (hash "hint"
                (hash "share" (exp (gen) (mul xr xi)) xr)))))))
    ((recv (exp (gen) xi))
      (send
        (cat (exp (gen) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
          (enc (enc "resp" (exp (gen) xr) (exp (gen) xi) (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
          (enc (enc "resp" (exp (gen) xr) (exp (gen) xi) (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xi)
              (hash "hint"
                (hash "share" (exp (gen) (mul xr xi)) xr))))))))
  (label 17)
  (parent 16)
  (unrealized)
  (shape)
  (maps
    ((0)
      ((i i) (r r) (xi xi) (xr xr)
        (hint
          (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))))
  (origs))

(defskeleton station-nohint
  (vars (hint mesg) (i r name) (xi rndx) (xr expt))
  (defstrand init 3 (hint hint) (i i) (r r) (xi xi) (xr xr))
  (deflistener
    (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi) hint))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk i) (privk r))
  (uniq-gen xi)
  (operation encryption-test
    (added-listener
      (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi) hint))
    (enc (enc "resp" (exp (gen) xr) (exp (gen) xi) (privk r))
      (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi) hint))
    (0 1))
  (traces
    ((send (exp (gen) xi))
      (recv
        (cat (exp (gen) xr) hint
          (enc (enc "resp" (exp (gen) xr) (exp (gen) xi) (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi)
              hint))))
      (send
        (cat
          (enc (enc (exp (gen) xi) (exp (gen) xr) (privk i))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xr) hint))
          (enc (enc (exp (gen) xi) (exp (gen) xr) (privk i))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi)
              hint)))))
    ((recv (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi) hint))
      (send
        (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi) hint))))
  (label 18)
  (parent 16)
  (unrealized (0 1) (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton station-nohint
  (vars (hint mesg) (i r name) (xi rndx) (xr expt))
  (defstrand init 3 (hint hint) (i i) (r r) (xi xi) (xr xr))
  (deflistener
    (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi) hint))
  (deflistener
    (cat "key" (hash "share" (exp (gen) (mul xi xr)) xi) hint))
  (precedes ((0 0) (2 0)) ((1 1) (0 1)) ((2 1) (1 0)))
  (non-orig (privk i) (privk r))
  (uniq-gen xi)
  (operation encryption-test
    (added-listener
      (cat "key" (hash "share" (exp (gen) (mul xi xr)) xi) hint))
    (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi) hint) (1 0))
  (traces
    ((send (exp (gen) xi))
      (recv
        (cat (exp (gen) xr) hint
          (enc (enc "resp" (exp (gen) xr) (exp (gen) xi) (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi)
              hint))))
      (send
        (cat
          (enc (enc (exp (gen) xi) (exp (gen) xr) (privk i))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xr) hint))
          (enc (enc (exp (gen) xi) (exp (gen) xr) (privk i))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi)
              hint)))))
    ((recv (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi) hint))
      (send
        (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi) hint)))
    ((recv (cat "key" (hash "share" (exp (gen) (mul xi xr)) xi) hint))
      (send
        (cat "key" (hash "share" (exp (gen) (mul xi xr)) xi) hint))))
  (label 19)
  (parent 18)
  (unrealized (0 1) (2 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton station-nohint
  (vars (hint mesg) (i r name) (xi rndx) (xr expt))
  (defstrand init 3 (hint hint) (i i) (r r) (xi xi) (xr xr))
  (deflistener
    (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi) hint))
  (deflistener
    (cat "key" (hash "share" (exp (gen) (mul xi xr)) xi) hint))
  (deflistener (cat "share" (exp (gen) (mul xi xr)) xi))
  (precedes ((0 0) (3 0)) ((1 1) (0 1)) ((2 1) (1 0)) ((3 1) (2 0)))
  (non-orig (privk i) (privk r))
  (uniq-gen xi)
  (operation encryption-test
    (added-listener (cat "share" (exp (gen) (mul xi xr)) xi))
    (hash "share" (exp (gen) (mul xi xr)) xi) (2 0))
  (traces
    ((send (exp (gen) xi))
      (recv
        (cat (exp (gen) xr) hint
          (enc (enc "resp" (exp (gen) xr) (exp (gen) xi) (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi)
              hint))))
      (send
        (cat
          (enc (enc (exp (gen) xi) (exp (gen) xr) (privk i))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xr) hint))
          (enc (enc (exp (gen) xi) (exp (gen) xr) (privk i))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi)
              hint)))))
    ((recv (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi) hint))
      (send
        (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi) hint)))
    ((recv (cat "key" (hash "share" (exp (gen) (mul xi xr)) xi) hint))
      (send (cat "key" (hash "share" (exp (gen) (mul xi xr)) xi) hint)))
    ((recv (cat "share" (exp (gen) (mul xi xr)) xi))
      (send (cat "share" (exp (gen) (mul xi xr)) xi))))
  (label 20)
  (parent 19)
  (unrealized (0 1) (3 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol station-nohint diffie-hellman
  (defrole init
    (vars (xi rndx) (xr expt) (i r name) (hint mesg))
    (trace (send (exp (gen) xi))
      (recv
        (cat (exp (gen) xr) hint
          (enc (enc "resp" (exp (gen) xr) (exp (gen) xi) (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi)
              hint))))
      (send
        (cat
          (enc (enc (exp (gen) xi) (exp (gen) xr) (privk i))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xr) hint))
          (enc (enc (exp (gen) xi) (exp (gen) xr) (privk i))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi)
              hint))))))
  (defrole resp
    (vars (xr rndx) (xi expt) (i r name))
    (trace (recv (exp (gen) xi))
      (send
        (cat (exp (gen) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
          (enc (enc "resp" (exp (gen) xr) (exp (gen) xi) (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
          (enc (enc "resp" (exp (gen) xr) (exp (gen) xi) (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xi)
              (hash "hint"
                (hash "share" (exp (gen) (mul xr xi)) xr))))))
      (recv
        (enc (enc (exp (gen) xi) (exp (gen) xr) (privk i))
          (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
            (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr)))))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defgenrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2)) (false))))
  (defgenrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defgenrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1)))))
  (defgenrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2))))))

(defskeleton station-nohint
  (vars (i r name) (xr rndx) (xi expt))
  (defstrand resp 3 (i i) (r r) (xr xr) (xi xi))
  (non-orig (privk i) (privk r))
  (uniq-gen xr)
  (absent (xr xi))
  (traces
    ((recv (exp (gen) xi))
      (send
        (cat (exp (gen) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
          (enc (enc "resp" (exp (gen) xr) (exp (gen) xi) (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
          (enc (enc "resp" (exp (gen) xr) (exp (gen) xi) (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xi)
              (hash "hint"
                (hash "share" (exp (gen) (mul xr xi)) xr))))))
      (recv
        (enc (enc (exp (gen) xi) (exp (gen) xr) (privk i))
          (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
            (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr)))))))
  (label 21)
  (unrealized (0 2))
  (origs)
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton station-nohint
  (vars (i r r-0 name) (xi xr rndx))
  (defstrand resp 3 (i i) (r r) (xr xr) (xi xi))
  (defstrand init 3
    (hint (hash "hint" (hash "share" (exp (gen) (mul xi xr)) xr))) (i i)
    (r r-0) (xi xi) (xr xr))
  (precedes ((0 1) (1 1)) ((1 2) (0 2)))
  (non-orig (privk i) (privk r))
  (uniq-gen xr)
  (absent (xr xi))
  (operation encryption-test (added-strand init 3)
    (enc (enc (exp (gen) xi) (exp (gen) xr) (privk i))
      (hash "key" (hash "share" (exp (gen) (mul xi xr)) xr)
        (hash "hint" (hash "share" (exp (gen) (mul xi xr)) xr)))) (0 2))
  (traces
    ((recv (exp (gen) xi))
      (send
        (cat (exp (gen) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xi xr)) xr))
          (enc (enc "resp" (exp (gen) xr) (exp (gen) xi) (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xr)
              (hash "hint" (hash "share" (exp (gen) (mul xi xr)) xr))))
          (enc (enc "resp" (exp (gen) xr) (exp (gen) xi) (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi)
              (hash "hint"
                (hash "share" (exp (gen) (mul xi xr)) xr))))))
      (recv
        (enc (enc (exp (gen) xi) (exp (gen) xr) (privk i))
          (hash "key" (hash "share" (exp (gen) (mul xi xr)) xr)
            (hash "hint" (hash "share" (exp (gen) (mul xi xr)) xr))))))
    ((send (exp (gen) xi))
      (recv
        (cat (exp (gen) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xi xr)) xr))
          (enc (enc "resp" (exp (gen) xr) (exp (gen) xi) (privk r-0))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi)
              (hash "hint"
                (hash "share" (exp (gen) (mul xi xr)) xr))))))
      (send
        (cat
          (enc (enc (exp (gen) xi) (exp (gen) xr) (privk i))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xr)
              (hash "hint" (hash "share" (exp (gen) (mul xi xr)) xr))))
          (enc (enc (exp (gen) xi) (exp (gen) xr) (privk i))
            (hash "key" (hash "share" (exp (gen) (mul xi xr)) xi)
              (hash "hint"
                (hash "share" (exp (gen) (mul xi xr)) xr))))))))
  (label 22)
  (parent 21)
  (unrealized)
  (shape)
  (maps ((0) ((i i) (r r) (xr xr) (xi xi))))
  (origs))

(defskeleton station-nohint
  (vars (i r name) (xr rndx) (xi expt))
  (defstrand resp 3 (i i) (r r) (xr xr) (xi xi))
  (deflistener
    (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
      (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
  (precedes ((0 1) (1 0)) ((1 1) (0 2)))
  (non-orig (privk i) (privk r))
  (uniq-gen xr)
  (absent (xr xi))
  (operation encryption-test
    (added-listener
      (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
        (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
    (enc (enc (exp (gen) xi) (exp (gen) xr) (privk i))
      (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
        (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr)))) (0 2))
  (traces
    ((recv (exp (gen) xi))
      (send
        (cat (exp (gen) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
          (enc (enc "resp" (exp (gen) xr) (exp (gen) xi) (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
          (enc (enc "resp" (exp (gen) xr) (exp (gen) xi) (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xi)
              (hash "hint"
                (hash "share" (exp (gen) (mul xr xi)) xr))))))
      (recv
        (enc (enc (exp (gen) xi) (exp (gen) xr) (privk i))
          (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
            (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))))
    ((recv
       (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
         (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
      (send
        (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))))
  (label 23)
  (parent 21)
  (unrealized (0 2) (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton station-nohint
  (vars (i r name) (xr rndx) (xi expt))
  (defstrand resp 3 (i i) (r r) (xr xr) (xi xi))
  (deflistener
    (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
      (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
  (deflistener
    (cat "key" (hash "share" (exp (gen) (mul xr xi)) xr)
      (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
  (precedes ((0 1) (2 0)) ((1 1) (0 2)) ((2 1) (1 0)))
  (non-orig (privk i) (privk r))
  (uniq-gen xr)
  (absent (xr xi))
  (operation encryption-test
    (added-listener
      (cat "key" (hash "share" (exp (gen) (mul xr xi)) xr)
        (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
    (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
      (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))) (1 0))
  (traces
    ((recv (exp (gen) xi))
      (send
        (cat (exp (gen) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
          (enc (enc "resp" (exp (gen) xr) (exp (gen) xi) (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
          (enc (enc "resp" (exp (gen) xr) (exp (gen) xi) (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xi)
              (hash "hint"
                (hash "share" (exp (gen) (mul xr xi)) xr))))))
      (recv
        (enc (enc (exp (gen) xi) (exp (gen) xr) (privk i))
          (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
            (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))))
    ((recv
       (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
         (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
      (send
        (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr)))))
    ((recv
       (cat "key" (hash "share" (exp (gen) (mul xr xi)) xr)
         (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
      (send
        (cat "key" (hash "share" (exp (gen) (mul xr xi)) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))))
  (label 24)
  (parent 23)
  (unrealized (0 2) (2 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton station-nohint
  (vars (i r name) (xr rndx) (xi expt))
  (defstrand resp 3 (i i) (r r) (xr xr) (xi xi))
  (deflistener
    (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
      (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
  (deflistener
    (cat "key" (hash "share" (exp (gen) (mul xr xi)) xr)
      (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
  (deflistener (cat "share" (exp (gen) (mul xr xi)) xr))
  (precedes ((0 1) (3 0)) ((1 1) (0 2)) ((2 1) (1 0)) ((3 1) (2 0)))
  (non-orig (privk i) (privk r))
  (uniq-gen xr)
  (absent (xr xi))
  (operation encryption-test
    (added-listener (cat "share" (exp (gen) (mul xr xi)) xr))
    (hash "share" (exp (gen) (mul xr xi)) xr) (2 0))
  (traces
    ((recv (exp (gen) xi))
      (send
        (cat (exp (gen) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))
          (enc (enc "resp" (exp (gen) xr) (exp (gen) xi) (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
              (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
          (enc (enc "resp" (exp (gen) xr) (exp (gen) xi) (privk r))
            (hash "key" (hash "share" (exp (gen) (mul xr xi)) xi)
              (hash "hint"
                (hash "share" (exp (gen) (mul xr xi)) xr))))))
      (recv
        (enc (enc (exp (gen) xi) (exp (gen) xr) (privk i))
          (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
            (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))))
    ((recv
       (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
         (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
      (send
        (hash "key" (hash "share" (exp (gen) (mul xr xi)) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr)))))
    ((recv
       (cat "key" (hash "share" (exp (gen) (mul xr xi)) xr)
         (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr))))
      (send
        (cat "key" (hash "share" (exp (gen) (mul xr xi)) xr)
          (hash "hint" (hash "share" (exp (gen) (mul xr xi)) xr)))))
    ((recv (cat "share" (exp (gen) (mul xr xi)) xr))
      (send (cat "share" (exp (gen) (mul xr xi)) xr))))
  (label 25)
  (parent 24)
  (unrealized (0 2) (3 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")
