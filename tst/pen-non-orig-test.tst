(herald "pen-non-orig test")

(comment "CPSA 4.3.0")
(comment "All input read from tst/pen-non-orig-test.scm")

(defprotocol pennonorigtest basic
  (defrole client
    (vars (userid name) (pwd text))
    (trace (send (cat userid pwd))))
  (defrole server
    (vars (userid name) (pwd text))
    (trace (recv (cat userid pwd)))
    (pen-non-orig pwd))
  (defrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2))
        (false))))
  (defrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1))))))

(defskeleton pennonorigtest
  (vars (pwd text) (userid name))
  (defstrand server 1 (pwd pwd) (userid userid))
  (pen-non-orig pwd)
  (traces ((recv (cat userid pwd))))
  (label 0)
  (unrealized (0 0))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton pennonorigtest
  (vars (pwd text) (userid userid-0 name))
  (defstrand server 1 (pwd pwd) (userid userid))
  (defstrand client 1 (pwd pwd) (userid userid-0))
  (precedes ((1 0) (0 0)))
  (pen-non-orig pwd)
  (operation nonce-test (added-strand client 1) pwd (0 0))
  (traces ((recv (cat userid pwd))) ((send (cat userid-0 pwd))))
  (label 1)
  (parent 0)
  (unrealized)
  (shape)
  (maps ((0) ((pwd pwd) (userid userid))))
  (origs))

(comment "Nothing left to do")

(defprotocol pennonorigtest basic
  (defrole client
    (vars (userid name) (pwd text))
    (trace (send (cat userid pwd))))
  (defrole server
    (vars (userid name) (pwd text))
    (trace (recv (cat userid pwd)))
    (pen-non-orig pwd))
  (defrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2))
        (false))))
  (defrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1))))))

(defskeleton pennonorigtest
  (vars (pwd text) (userid name))
  (defstrand server 1 (pwd pwd) (userid userid))
  (deflistener pwd)
  (pen-non-orig pwd)
  (traces ((recv (cat userid pwd))) ((recv pwd) (send pwd)))
  (label 2)
  (unrealized (0 0) (1 0))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton pennonorigtest
  (vars (pwd text) (userid userid-0 name))
  (defstrand server 1 (pwd pwd) (userid userid))
  (deflistener pwd)
  (defstrand client 1 (pwd pwd) (userid userid-0))
  (precedes ((2 0) (1 0)))
  (pen-non-orig pwd)
  (operation nonce-test (added-strand client 1) pwd (1 0))
  (traces ((recv (cat userid pwd))) ((recv pwd) (send pwd))
    ((send (cat userid-0 pwd))))
  (label 3)
  (parent 2)
  (unrealized (0 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton pennonorigtest
  (vars (pwd text) (userid userid-0 name))
  (defstrand server 1 (pwd pwd) (userid userid))
  (deflistener pwd)
  (defstrand client 1 (pwd pwd) (userid userid-0))
  (precedes ((2 0) (0 0)) ((2 0) (1 0)))
  (pen-non-orig pwd)
  (operation nonce-test (displaced 3 2 client 1) pwd (0 0))
  (traces ((recv (cat userid pwd))) ((recv pwd) (send pwd))
    ((send (cat userid-0 pwd))))
  (label 4)
  (parent 3)
  (unrealized)
  (shape)
  (maps ((0 1) ((pwd pwd) (userid userid))))
  (origs))

(defskeleton pennonorigtest
  (vars (pwd text) (userid userid-0 userid-1 name))
  (defstrand server 1 (pwd pwd) (userid userid))
  (deflistener pwd)
  (defstrand client 1 (pwd pwd) (userid userid-0))
  (defstrand client 1 (pwd pwd) (userid userid-1))
  (precedes ((2 0) (1 0)) ((3 0) (0 0)))
  (pen-non-orig pwd)
  (operation nonce-test (added-strand client 1) pwd (0 0))
  (traces ((recv (cat userid pwd))) ((recv pwd) (send pwd))
    ((send (cat userid-0 pwd))) ((send (cat userid-1 pwd))))
  (label 5)
  (parent 3)
  (unrealized)
  (shape)
  (maps ((0 1) ((pwd pwd) (userid userid))))
  (origs))

(comment "Nothing left to do")
