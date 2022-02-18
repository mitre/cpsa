(herald "Blanchet's Simple Example Protocol"
  (comment "There is a flaw in this protocol by design")
  (comment "It also shows how variable renaming works"))

(comment "CPSA 4.3.0")
(comment "All input read from tst/renamings.scm")

(defprotocol blanchet basic
  (defrole init
    (vars (a b name) (s skey) (d data))
    (trace (send (enc (enc s (privk a)) (pubk b))) (recv (enc d s))))
  (defrole resp
    (vars (d a name) (b skey) (s data))
    (trace (recv (enc (enc b (privk d)) (pubk a))) (send (enc s b))))
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
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (comment "Blanchet's protocol using named asymmetric keys"))

(defskeleton blanchet
  (vars (b data) (a skey) (s d name))
  (defstrand resp 2 (s b) (b a) (d s) (a d))
  (non-orig (privk s) (privk d))
  (uniq-orig a)
  (comment "Analyze from the responder's perspective")
  (traces ((recv (enc (enc a (privk s)) (pubk d))) (send (enc b a))))
  (label 0)
  (unrealized (0 0))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton blanchet
  (vars (b data) (a skey) (s d b-0 name))
  (defstrand resp 2 (s b) (b a) (d s) (a d))
  (defstrand init 1 (s a) (a s) (b b-0))
  (precedes ((1 0) (0 0)))
  (non-orig (privk s) (privk d))
  (uniq-orig a)
  (operation encryption-test (added-strand init 1) (enc a (privk s))
    (0 0))
  (traces ((recv (enc (enc a (privk s)) (pubk d))) (send (enc b a)))
    ((send (enc (enc a (privk s)) (pubk b-0)))))
  (label 1)
  (parent 0)
  (realized)
  (shape)
  (maps ((0) ((s s) (d d) (a a) (b b))))
  (origs (a (1 0))))

(comment "Nothing left to do")

(defprotocol blanchet basic
  (defrole init
    (vars (a b name) (s skey) (d data))
    (trace (send (enc (enc s (privk a)) (pubk b))) (recv (enc d s))))
  (defrole resp
    (vars (d a name) (b skey) (s data))
    (trace (recv (enc (enc b (privk d)) (pubk a))) (send (enc s b))))
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
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (comment "Blanchet's protocol using named asymmetric keys"))

(defskeleton blanchet
  (vars (b data) (a skey) (s d name))
  (defstrand init 2 (d b) (s a) (a s) (b d))
  (non-orig (privk d))
  (uniq-orig a)
  (comment "Analyze from the initiator's perspective")
  (traces ((send (enc (enc a (privk s)) (pubk d))) (recv (enc b a))))
  (label 2)
  (unrealized (0 1))
  (origs (a (0 0)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton blanchet
  (vars (b data) (a skey) (s d d-0 a-0 name))
  (defstrand init 2 (d b) (s a) (a s) (b d))
  (defstrand resp 2 (s b) (b a) (d d-0) (a a-0))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk d))
  (uniq-orig a)
  (operation encryption-test (added-strand resp 2) (enc b a) (0 1))
  (traces ((send (enc (enc a (privk s)) (pubk d))) (recv (enc b a)))
    ((recv (enc (enc a (privk d-0)) (pubk a-0))) (send (enc b a))))
  (label 3)
  (parent 2)
  (unrealized (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton blanchet
  (vars (b data) (a skey) (s d name))
  (defstrand init 2 (d b) (s a) (a s) (b d))
  (deflistener a)
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk d))
  (uniq-orig a)
  (operation encryption-test (added-listener a) (enc b a) (0 1))
  (traces ((send (enc (enc a (privk s)) (pubk d))) (recv (enc b a)))
    ((recv a) (send a)))
  (label 4)
  (parent 2)
  (unrealized (1 0))
  (dead)
  (comment "empty cohort"))

(defskeleton blanchet
  (vars (b data) (a skey) (s d name))
  (defstrand init 2 (d b) (s a) (a s) (b d))
  (defstrand resp 2 (s b) (b a) (d s) (a d))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk d))
  (uniq-orig a)
  (operation nonce-test (contracted (d-0 s) (a-0 d)) a (1 0)
    (enc (enc a (privk s)) (pubk d)))
  (traces ((send (enc (enc a (privk s)) (pubk d))) (recv (enc b a)))
    ((recv (enc (enc a (privk s)) (pubk d))) (send (enc b a))))
  (label 5)
  (parent 3)
  (realized)
  (shape)
  (maps ((0) ((s s) (d d) (a a) (b b))))
  (origs (a (0 0))))

(comment "Nothing left to do")
