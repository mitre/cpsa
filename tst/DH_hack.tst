(herald "DH Hack" (bound 15))

(comment "CPSA 4.3.1")
(comment "All input read from tst/DH_hack.scm")
(comment "Strand count bounded at 15")

(defprotocol DH_hack basic
  (defrole init1
    (vars (gcs name) (cek skey) (x y akey) (d data))
    (trace
      (send
        (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs))))
    (uniq-orig d cek x))
  (defrole resp
    (vars (gcs name) (cek skey) (x y akey) (d data))
    (trace
      (recv
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    (non-orig (privk gcs)))
  (defrole commute
    (vars (gcs name) (cek skey) (x y akey) (d data))
    (trace
      (recv (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))
      (send
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    (non-orig (privk gcs)))
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

(defskeleton DH_hack
  (vars (d data) (cek skey) (x y akey) (gcs name))
  (defstrand resp 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (non-orig (invk x) (invk y) (privk gcs))
  (traces
    ((recv
       (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs)))))
  (label 0)
  (unrealized (0 0))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton DH_hack
  (vars (d data) (cek skey) (x y akey) (gcs name))
  (defstrand resp 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (defstrand commute 2 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (precedes ((1 1) (0 0)))
  (non-orig (invk x) (invk y) (privk gcs))
  (operation encryption-test (added-strand commute 2)
    (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs)) (0 0))
  (traces
    ((recv (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((recv (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))
      (send
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs)))))
  (label 1)
  (parent 0)
  (unrealized (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton DH_hack
  (vars (d data) (cek skey) (x y akey) (gcs name))
  (defstrand resp 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (defstrand commute 2 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (defstrand init1 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (precedes ((1 1) (0 0)) ((2 0) (1 0)))
  (non-orig (invk x) (invk y) (privk gcs))
  (uniq-orig d cek x)
  (operation encryption-test (added-strand init1 1)
    (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)) (1 0))
  (traces
    ((recv (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((recv (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))
      (send
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((send
       (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))))
  (label 2)
  (parent 1)
  (realized)
  (shape)
  (maps ((0) ((x x) (y y) (gcs gcs) (cek cek) (d d))))
  (origs (cek (2 0)) (d (2 0)) (x (2 0))))

(comment "Nothing left to do")

(defprotocol DH_hack basic
  (defrole init1
    (vars (gcs name) (cek skey) (x y akey) (d data))
    (trace
      (send
        (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs))))
    (uniq-orig d cek x))
  (defrole resp
    (vars (gcs name) (cek skey) (x y akey) (d data))
    (trace
      (recv
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    (non-orig (privk gcs)))
  (defrole commute
    (vars (gcs name) (cek skey) (x y akey) (d data))
    (trace
      (recv (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))
      (send
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    (non-orig (privk gcs)))
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

(defskeleton DH_hack
  (vars (d data) (cek skey) (x y akey) (gcs name))
  (defstrand resp 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (non-orig (invk x) (privk gcs))
  (traces
    ((recv
       (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs)))))
  (label 3)
  (unrealized (0 0))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton DH_hack
  (vars (d data) (cek skey) (x y akey) (gcs name))
  (defstrand resp 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (defstrand commute 2 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (precedes ((1 1) (0 0)))
  (non-orig (invk x) (privk gcs))
  (operation encryption-test (added-strand commute 2)
    (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs)) (0 0))
  (traces
    ((recv (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((recv (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))
      (send
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs)))))
  (label 4)
  (parent 3)
  (unrealized (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton DH_hack
  (vars (d data) (cek skey) (x y akey) (gcs name))
  (defstrand resp 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (defstrand commute 2 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (defstrand init1 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (precedes ((1 1) (0 0)) ((2 0) (1 0)))
  (non-orig (invk x) (privk gcs))
  (uniq-orig d cek x)
  (operation encryption-test (added-strand init1 1)
    (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)) (1 0))
  (traces
    ((recv (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((recv (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))
      (send
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((send
       (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))))
  (label 5)
  (parent 4)
  (realized)
  (shape)
  (maps ((0) ((cek cek) (x x) (gcs gcs) (y y) (d d))))
  (origs (cek (2 0)) (d (2 0)) (x (2 0))))

(comment "Nothing left to do")

(defprotocol DH_hack basic
  (defrole init1
    (vars (gcs name) (cek skey) (x y akey) (d data))
    (trace
      (send
        (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs))))
    (uniq-orig d cek x))
  (defrole resp
    (vars (gcs name) (cek skey) (x y akey) (d data))
    (trace
      (recv
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    (non-orig (privk gcs)))
  (defrole commute
    (vars (gcs name) (cek skey) (x y akey) (d data))
    (trace
      (recv (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))
      (send
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    (non-orig (privk gcs)))
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

(defskeleton DH_hack
  (vars (d data) (cek skey) (y x akey) (gcs name))
  (defstrand resp 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (non-orig (invk y) (privk gcs))
  (traces
    ((recv
       (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs)))))
  (label 6)
  (unrealized (0 0))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton DH_hack
  (vars (d data) (cek skey) (y x akey) (gcs name))
  (defstrand resp 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (defstrand commute 2 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (precedes ((1 1) (0 0)))
  (non-orig (invk y) (privk gcs))
  (operation encryption-test (added-strand commute 2)
    (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs)) (0 0))
  (traces
    ((recv (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((recv (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))
      (send
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs)))))
  (label 7)
  (parent 6)
  (unrealized (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton DH_hack
  (vars (d data) (cek skey) (y x akey) (gcs name))
  (defstrand resp 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (defstrand commute 2 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (defstrand init1 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (precedes ((1 1) (0 0)) ((2 0) (1 0)))
  (non-orig (invk y) (privk gcs))
  (uniq-orig d cek x)
  (operation encryption-test (added-strand init1 1)
    (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)) (1 0))
  (traces
    ((recv (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((recv (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))
      (send
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((send
       (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))))
  (label 8)
  (parent 7)
  (realized)
  (shape)
  (maps ((0) ((cek cek) (y y) (gcs gcs) (x x) (d d))))
  (origs (cek (2 0)) (d (2 0)) (x (2 0))))

(comment "Nothing left to do")

(defprotocol DH_hack basic
  (defrole init1
    (vars (gcs name) (cek skey) (x y akey) (d data))
    (trace
      (send
        (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs))))
    (uniq-orig d cek x))
  (defrole resp
    (vars (gcs name) (cek skey) (x y akey) (d data))
    (trace
      (recv
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    (non-orig (privk gcs)))
  (defrole commute
    (vars (gcs name) (cek skey) (x y akey) (d data))
    (trace
      (recv (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))
      (send
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    (non-orig (privk gcs)))
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

(defskeleton DH_hack
  (vars (d data) (cek skey) (x y akey) (gcs name))
  (defstrand resp 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (deflistener cek)
  (non-orig (invk x) (invk y) (privk gcs))
  (traces
    ((recv (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((recv cek) (send cek)))
  (label 9)
  (unrealized (0 0))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton DH_hack
  (vars (d data) (cek skey) (x y akey) (gcs name))
  (defstrand resp 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (deflistener cek)
  (defstrand commute 2 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (precedes ((2 1) (0 0)))
  (non-orig (invk x) (invk y) (privk gcs))
  (operation encryption-test (added-strand commute 2)
    (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs)) (0 0))
  (traces
    ((recv (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((recv cek) (send cek))
    ((recv (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))
      (send
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs)))))
  (label 10)
  (parent 9)
  (unrealized (2 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton DH_hack
  (vars (d data) (cek skey) (x y akey) (gcs name))
  (defstrand resp 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (deflistener cek)
  (defstrand commute 2 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (defstrand init1 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (precedes ((2 1) (0 0)) ((3 0) (1 0)) ((3 0) (2 0)))
  (non-orig (invk x) (invk y) (privk gcs))
  (uniq-orig d cek x)
  (operation encryption-test (added-strand init1 1)
    (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)) (2 0))
  (traces
    ((recv (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((recv cek) (send cek))
    ((recv (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))
      (send
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((send
       (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))))
  (label 11)
  (parent 10)
  (unrealized (1 0))
  (comment "3 in cohort - 3 not yet seen"))

(defskeleton DH_hack
  (vars (d data) (cek skey) (x y akey) (gcs name))
  (defstrand resp 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (deflistener cek)
  (defstrand commute 2 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (defstrand init1 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (precedes ((2 1) (0 0)) ((2 1) (1 0)) ((3 0) (2 0)))
  (non-orig (invk x) (invk y) (privk gcs))
  (uniq-orig d cek x)
  (operation nonce-test (displaced 4 2 commute 2) cek (1 0)
    (enc cek (hash (invk x) y)))
  (traces
    ((recv (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((recv cek) (send cek))
    ((recv (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))
      (send
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((send
       (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))))
  (label 12)
  (parent 11)
  (unrealized (1 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton DH_hack
  (vars (d d-0 data) (cek skey) (x y akey) (gcs gcs-0 name))
  (defstrand resp 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (deflistener cek)
  (defstrand commute 2 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (defstrand init1 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (defstrand commute 2 (d d-0) (cek cek) (x x) (y y) (gcs gcs-0))
  (precedes ((2 1) (0 0)) ((3 0) (2 0)) ((3 0) (4 0)) ((4 1) (1 0)))
  (non-orig (invk x) (invk y) (privk gcs) (privk gcs-0))
  (uniq-orig d cek x)
  (operation nonce-test (added-strand commute 2) cek (1 0)
    (enc cek (hash (invk x) y)))
  (traces
    ((recv (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((recv cek) (send cek))
    ((recv (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))
      (send
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((send (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs))))
    ((recv
       (enc x (enc cek (hash (invk x) y)) (enc d-0 cek) (privk gcs-0)))
      (send
        (enc x (enc cek (hash x (invk y))) (enc d-0 cek)
          (privk gcs-0)))))
  (label 13)
  (parent 11)
  (unrealized (1 0) (4 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton DH_hack
  (vars (d data) (cek skey) (x y akey) (gcs name))
  (defstrand resp 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (deflistener cek)
  (defstrand commute 2 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (defstrand init1 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (deflistener (hash (invk x) y))
  (precedes ((2 1) (0 0)) ((3 0) (1 0)) ((3 0) (2 0)) ((4 1) (1 0)))
  (non-orig (invk x) (invk y) (privk gcs))
  (uniq-orig d cek x)
  (operation nonce-test (added-listener (hash (invk x) y)) cek (1 0)
    (enc cek (hash (invk x) y)))
  (traces
    ((recv (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((recv cek) (send cek))
    ((recv (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))
      (send
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((send (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs))))
    ((recv (hash (invk x) y)) (send (hash (invk x) y))))
  (label 14)
  (parent 11)
  (unrealized (4 0))
  (dead)
  (comment "empty cohort"))

(defskeleton DH_hack
  (vars (d data) (cek skey) (x y akey) (gcs name))
  (defstrand resp 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (deflistener cek)
  (defstrand commute 2 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (defstrand init1 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (deflistener (hash x (invk y)))
  (precedes ((2 1) (0 0)) ((2 1) (1 0)) ((3 0) (2 0)) ((4 1) (1 0)))
  (non-orig (invk x) (invk y) (privk gcs))
  (uniq-orig d cek x)
  (operation nonce-test (added-listener (hash x (invk y))) cek (1 0)
    (enc cek (hash x (invk y))) (enc cek (hash (invk x) y)))
  (traces
    ((recv (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((recv cek) (send cek))
    ((recv (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))
      (send
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((send (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs))))
    ((recv (hash x (invk y))) (send (hash x (invk y)))))
  (label 15)
  (parent 12)
  (unrealized (4 0))
  (dead)
  (comment "empty cohort"))

(defskeleton DH_hack
  (vars (d data) (cek skey) (x y akey) (gcs name))
  (defstrand resp 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (deflistener cek)
  (defstrand commute 2 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (defstrand init1 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (deflistener (hash (invk x) y))
  (precedes ((2 1) (0 0)) ((2 1) (1 0)) ((3 0) (2 0)) ((4 1) (1 0)))
  (non-orig (invk x) (invk y) (privk gcs))
  (uniq-orig d cek x)
  (operation nonce-test (added-listener (hash (invk x) y)) cek (1 0)
    (enc cek (hash x (invk y))) (enc cek (hash (invk x) y)))
  (traces
    ((recv (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((recv cek) (send cek))
    ((recv (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))
      (send
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((send (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs))))
    ((recv (hash (invk x) y)) (send (hash (invk x) y))))
  (label 16)
  (parent 12)
  (unrealized (4 0))
  (dead)
  (comment "empty cohort"))

(defskeleton DH_hack
  (vars (d data) (cek skey) (x y akey) (gcs name))
  (defstrand resp 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (deflistener cek)
  (defstrand commute 2 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (defstrand init1 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (defstrand commute 2 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (precedes ((2 1) (0 0)) ((3 0) (2 0)) ((3 0) (4 0)) ((4 1) (1 0)))
  (non-orig (invk x) (invk y) (privk gcs))
  (uniq-orig d cek x)
  (operation encryption-test (displaced 5 3 init1 1)
    (enc x (enc cek (hash (invk x) y)) (enc d-0 cek) (privk gcs-0))
    (4 0))
  (traces
    ((recv (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((recv cek) (send cek))
    ((recv (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))
      (send
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((send (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs))))
    ((recv (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))
      (send
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs)))))
  (label 17)
  (parent 13)
  (unrealized (1 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton DH_hack
  (vars (d data) (cek skey) (x y akey) (gcs name))
  (defstrand resp 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (deflistener cek)
  (defstrand commute 2 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (defstrand init1 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (defstrand commute 2 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (deflistener (hash x (invk y)))
  (precedes ((2 1) (0 0)) ((3 0) (2 0)) ((3 0) (4 0)) ((4 1) (1 0))
    ((5 1) (1 0)))
  (non-orig (invk x) (invk y) (privk gcs))
  (uniq-orig d cek x)
  (operation nonce-test (added-listener (hash x (invk y))) cek (1 0)
    (enc cek (hash x (invk y))) (enc cek (hash (invk x) y)))
  (traces
    ((recv (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((recv cek) (send cek))
    ((recv (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))
      (send
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((send (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs))))
    ((recv (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))
      (send
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((recv (hash x (invk y))) (send (hash x (invk y)))))
  (label 18)
  (parent 17)
  (unrealized (5 0))
  (dead)
  (comment "empty cohort"))

(defskeleton DH_hack
  (vars (d data) (cek skey) (x y akey) (gcs name))
  (defstrand resp 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (deflistener cek)
  (defstrand commute 2 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (defstrand init1 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (defstrand commute 2 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (deflistener (hash (invk x) y))
  (precedes ((2 1) (0 0)) ((3 0) (2 0)) ((3 0) (4 0)) ((4 1) (1 0))
    ((5 1) (1 0)))
  (non-orig (invk x) (invk y) (privk gcs))
  (uniq-orig d cek x)
  (operation nonce-test (added-listener (hash (invk x) y)) cek (1 0)
    (enc cek (hash x (invk y))) (enc cek (hash (invk x) y)))
  (traces
    ((recv (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((recv cek) (send cek))
    ((recv (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))
      (send
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((send (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs))))
    ((recv (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))
      (send
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((recv (hash (invk x) y)) (send (hash (invk x) y))))
  (label 19)
  (parent 17)
  (unrealized (5 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol DH_hack basic
  (defrole init1
    (vars (gcs name) (cek skey) (x y akey) (d data))
    (trace
      (send
        (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs))))
    (uniq-orig d cek x))
  (defrole resp
    (vars (gcs name) (cek skey) (x y akey) (d data))
    (trace
      (recv
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    (non-orig (privk gcs)))
  (defrole commute
    (vars (gcs name) (cek skey) (x y akey) (d data))
    (trace
      (recv (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))
      (send
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    (non-orig (privk gcs)))
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

(defskeleton DH_hack
  (vars (d data) (cek skey) (x y akey) (gcs name))
  (defstrand resp 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (deflistener cek)
  (non-orig (invk x) (privk gcs))
  (traces
    ((recv (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((recv cek) (send cek)))
  (label 20)
  (unrealized (0 0))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton DH_hack
  (vars (d data) (cek skey) (x y akey) (gcs name))
  (defstrand resp 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (deflistener cek)
  (defstrand commute 2 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (precedes ((2 1) (0 0)))
  (non-orig (invk x) (privk gcs))
  (operation encryption-test (added-strand commute 2)
    (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs)) (0 0))
  (traces
    ((recv (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((recv cek) (send cek))
    ((recv (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))
      (send
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs)))))
  (label 21)
  (parent 20)
  (unrealized (2 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton DH_hack
  (vars (d data) (cek skey) (x y akey) (gcs name))
  (defstrand resp 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (deflistener cek)
  (defstrand commute 2 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (defstrand init1 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (precedes ((2 1) (0 0)) ((3 0) (1 0)) ((3 0) (2 0)))
  (non-orig (invk x) (privk gcs))
  (uniq-orig d cek x)
  (operation encryption-test (added-strand init1 1)
    (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)) (2 0))
  (traces
    ((recv (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((recv cek) (send cek))
    ((recv (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))
      (send
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((send
       (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))))
  (label 22)
  (parent 21)
  (unrealized (1 0))
  (comment "3 in cohort - 3 not yet seen"))

(defskeleton DH_hack
  (vars (d data) (cek skey) (x y akey) (gcs name))
  (defstrand resp 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (deflistener cek)
  (defstrand commute 2 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (defstrand init1 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (precedes ((2 1) (0 0)) ((2 1) (1 0)) ((3 0) (2 0)))
  (non-orig (invk x) (privk gcs))
  (uniq-orig d cek x)
  (operation nonce-test (displaced 4 2 commute 2) cek (1 0)
    (enc cek (hash (invk x) y)))
  (traces
    ((recv (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((recv cek) (send cek))
    ((recv (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))
      (send
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((send
       (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))))
  (label 23)
  (parent 22)
  (realized)
  (shape)
  (maps ((0 1) ((cek cek) (x x) (gcs gcs) (y y) (d d))))
  (origs (cek (3 0)) (d (3 0)) (x (3 0))))

(defskeleton DH_hack
  (vars (d d-0 data) (cek skey) (x y akey) (gcs gcs-0 name))
  (defstrand resp 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (deflistener cek)
  (defstrand commute 2 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (defstrand init1 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (defstrand commute 2 (d d-0) (cek cek) (x x) (y y) (gcs gcs-0))
  (precedes ((2 1) (0 0)) ((3 0) (2 0)) ((3 0) (4 0)) ((4 1) (1 0)))
  (non-orig (invk x) (privk gcs) (privk gcs-0))
  (uniq-orig d cek x)
  (operation nonce-test (added-strand commute 2) cek (1 0)
    (enc cek (hash (invk x) y)))
  (traces
    ((recv (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((recv cek) (send cek))
    ((recv (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))
      (send
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((send (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs))))
    ((recv
       (enc x (enc cek (hash (invk x) y)) (enc d-0 cek) (privk gcs-0)))
      (send
        (enc x (enc cek (hash x (invk y))) (enc d-0 cek)
          (privk gcs-0)))))
  (label 24)
  (parent 22)
  (unrealized (4 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton DH_hack
  (vars (d data) (cek skey) (x y akey) (gcs name))
  (defstrand resp 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (deflistener cek)
  (defstrand commute 2 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (defstrand init1 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (deflistener (hash (invk x) y))
  (precedes ((2 1) (0 0)) ((3 0) (1 0)) ((3 0) (2 0)) ((4 1) (1 0)))
  (non-orig (invk x) (privk gcs))
  (uniq-orig d cek x)
  (operation nonce-test (added-listener (hash (invk x) y)) cek (1 0)
    (enc cek (hash (invk x) y)))
  (traces
    ((recv (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((recv cek) (send cek))
    ((recv (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))
      (send
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((send (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs))))
    ((recv (hash (invk x) y)) (send (hash (invk x) y))))
  (label 25)
  (parent 22)
  (unrealized (4 0))
  (dead)
  (comment "empty cohort"))

(defskeleton DH_hack
  (vars (d data) (cek skey) (x y akey) (gcs name))
  (defstrand resp 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (deflistener cek)
  (defstrand commute 2 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (defstrand init1 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (defstrand commute 2 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (precedes ((2 1) (0 0)) ((3 0) (2 0)) ((3 0) (4 0)) ((4 1) (1 0)))
  (non-orig (invk x) (privk gcs))
  (uniq-orig d cek x)
  (operation encryption-test (displaced 5 3 init1 1)
    (enc x (enc cek (hash (invk x) y)) (enc d-0 cek) (privk gcs-0))
    (4 0))
  (traces
    ((recv (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((recv cek) (send cek))
    ((recv (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))
      (send
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((send (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs))))
    ((recv (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))
      (send
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs)))))
  (label 26)
  (parent 24)
  (realized)
  (shape)
  (maps ((0 1) ((cek cek) (x x) (gcs gcs) (y y) (d d))))
  (origs (cek (3 0)) (d (3 0)) (x (3 0))))

(comment "Nothing left to do")

(defprotocol DH_hack basic
  (defrole init1
    (vars (gcs name) (cek skey) (x y akey) (d data))
    (trace
      (send
        (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs))))
    (uniq-orig d cek x))
  (defrole resp
    (vars (gcs name) (cek skey) (x y akey) (d data))
    (trace
      (recv
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    (non-orig (privk gcs)))
  (defrole commute
    (vars (gcs name) (cek skey) (x y akey) (d data))
    (trace
      (recv (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))
      (send
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    (non-orig (privk gcs)))
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

(defskeleton DH_hack
  (vars (d data) (cek skey) (y x akey) (gcs name))
  (defstrand resp 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (deflistener cek)
  (non-orig (invk y) (privk gcs))
  (traces
    ((recv (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((recv cek) (send cek)))
  (label 27)
  (unrealized (0 0))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton DH_hack
  (vars (d data) (cek skey) (y x akey) (gcs name))
  (defstrand resp 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (deflistener cek)
  (defstrand commute 2 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (precedes ((2 1) (0 0)))
  (non-orig (invk y) (privk gcs))
  (operation encryption-test (added-strand commute 2)
    (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs)) (0 0))
  (traces
    ((recv (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((recv cek) (send cek))
    ((recv (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))
      (send
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs)))))
  (label 28)
  (parent 27)
  (unrealized (2 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton DH_hack
  (vars (d data) (cek skey) (y x akey) (gcs name))
  (defstrand resp 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (deflistener cek)
  (defstrand commute 2 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (defstrand init1 1 (d d) (cek cek) (x x) (y y) (gcs gcs))
  (precedes ((2 1) (0 0)) ((3 0) (1 0)) ((3 0) (2 0)))
  (non-orig (invk y) (privk gcs))
  (uniq-orig d cek x)
  (operation encryption-test (added-strand init1 1)
    (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)) (2 0))
  (traces
    ((recv (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((recv cek) (send cek))
    ((recv (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))
      (send
        (enc x (enc cek (hash x (invk y))) (enc d cek) (privk gcs))))
    ((send
       (enc x (enc cek (hash (invk x) y)) (enc d cek) (privk gcs)))))
  (label 29)
  (parent 28)
  (realized)
  (shape)
  (maps ((0 1) ((cek cek) (y y) (gcs gcs) (x x) (d d))))
  (origs (cek (3 0)) (d (3 0)) (x (3 0))))

(comment "Nothing left to do")
