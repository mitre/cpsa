(herald "Distributed Authentication Security Service Protocol Variants")

(comment "CPSA 4.3.1")
(comment "All input read from tst/dass_simple.scm")

(defprotocol dass-simple basic
  (defrole init
    (vars (a b name) (k skey) (ta text) (kp akey) (tb text))
    (trace
      (send
        (cat (enc "init" ta k) (enc a kp (privk a))
          (enc (enc k (pubk b)) (invk kp)))) (recv (enc "resp" tb k))))
  (defrole resp
    (vars (a b name) (k skey) (ta text) (kp akey) (tb text))
    (trace
      (recv
        (cat (enc "init" ta k) (enc a kp (privk a))
          (enc (enc k (pubk b)) (invk kp)))) (send (enc "resp" tb k))))
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
  (comment "In this version of the protocol ")
  (comment "b might interact with a compromised initiator.")
  (comment "That is why a is not authenticated to b."))

(defskeleton dass-simple
  (vars (k skey) (ta tb text) (kp akey) (a b name))
  (defstrand init 2 (k k) (ta ta) (tb tb) (kp kp) (a a) (b b))
  (non-orig (invk kp) (privk a) (privk b))
  (uniq-orig k kp)
  (traces
    ((send
       (cat (enc "init" ta k) (enc a kp (privk a))
         (enc (enc k (pubk b)) (invk kp)))) (recv (enc "resp" tb k))))
  (label 0)
  (unrealized (0 1))
  (origs (k (0 0)) (kp (0 0)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton dass-simple
  (vars (k skey) (ta tb ta-0 text) (kp kp-0 akey) (a b a-0 b-0 name))
  (defstrand init 2 (k k) (ta ta) (tb tb) (kp kp) (a a) (b b))
  (defstrand resp 2 (k k) (ta ta-0) (tb tb) (kp kp-0) (a a-0) (b b-0))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (invk kp) (privk a) (privk b))
  (uniq-orig k kp)
  (operation encryption-test (added-strand resp 2) (enc "resp" tb k)
    (0 1))
  (traces
    ((send
       (cat (enc "init" ta k) (enc a kp (privk a))
         (enc (enc k (pubk b)) (invk kp)))) (recv (enc "resp" tb k)))
    ((recv
       (cat (enc "init" ta-0 k) (enc a-0 kp-0 (privk a-0))
         (enc (enc k (pubk b-0)) (invk kp-0))))
      (send (enc "resp" tb k))))
  (label 1)
  (parent 0)
  (unrealized (1 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton dass-simple
  (vars (k skey) (ta tb text) (kp akey) (a b name))
  (defstrand init 2 (k k) (ta ta) (tb tb) (kp kp) (a a) (b b))
  (deflistener k)
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (invk kp) (privk a) (privk b))
  (uniq-orig k kp)
  (operation encryption-test (added-listener k) (enc "resp" tb k) (0 1))
  (traces
    ((send
       (cat (enc "init" ta k) (enc a kp (privk a))
         (enc (enc k (pubk b)) (invk kp)))) (recv (enc "resp" tb k)))
    ((recv k) (send k)))
  (label 2)
  (parent 0)
  (unrealized (1 0))
  (dead)
  (comment "empty cohort"))

(defskeleton dass-simple
  (vars (k skey) (ta tb text) (kp kp-0 akey) (a b a-0 b-0 name))
  (defstrand init 2 (k k) (ta ta) (tb tb) (kp kp) (a a) (b b))
  (defstrand resp 2 (k k) (ta ta) (tb tb) (kp kp-0) (a a-0) (b b-0))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (invk kp) (privk a) (privk b))
  (uniq-orig k kp)
  (operation encryption-test (displaced 2 0 init 1) (enc "init" ta-0 k)
    (1 0))
  (traces
    ((send
       (cat (enc "init" ta k) (enc a kp (privk a))
         (enc (enc k (pubk b)) (invk kp)))) (recv (enc "resp" tb k)))
    ((recv
       (cat (enc "init" ta k) (enc a-0 kp-0 (privk a-0))
         (enc (enc k (pubk b-0)) (invk kp-0))))
      (send (enc "resp" tb k))))
  (label 3)
  (parent 1)
  (unrealized (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dass-simple
  (vars (k skey) (ta tb ta-0 text) (kp kp-0 akey) (a b a-0 b-0 name))
  (defstrand init 2 (k k) (ta ta) (tb tb) (kp kp) (a a) (b b))
  (defstrand resp 2 (k k) (ta ta-0) (tb tb) (kp kp-0) (a a-0) (b b-0))
  (deflistener k)
  (precedes ((0 0) (2 0)) ((1 1) (0 1)) ((2 1) (1 0)))
  (non-orig (invk kp) (privk a) (privk b))
  (uniq-orig k kp)
  (operation encryption-test (added-listener k) (enc "init" ta-0 k)
    (1 0))
  (traces
    ((send
       (cat (enc "init" ta k) (enc a kp (privk a))
         (enc (enc k (pubk b)) (invk kp)))) (recv (enc "resp" tb k)))
    ((recv
       (cat (enc "init" ta-0 k) (enc a-0 kp-0 (privk a-0))
         (enc (enc k (pubk b-0)) (invk kp-0))))
      (send (enc "resp" tb k))) ((recv k) (send k)))
  (label 4)
  (parent 1)
  (unrealized (2 0))
  (dead)
  (comment "empty cohort"))

(defskeleton dass-simple
  (vars (k skey) (ta tb text) (kp kp-0 akey) (a b a-0 name))
  (defstrand init 2 (k k) (ta ta) (tb tb) (kp kp) (a a) (b b))
  (defstrand resp 2 (k k) (ta ta) (tb tb) (kp kp-0) (a a-0) (b b))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (invk kp) (privk a) (privk b))
  (uniq-orig k kp)
  (operation nonce-test (contracted (b-0 b)) k (1 0) (enc k (pubk b)))
  (traces
    ((send
       (cat (enc "init" ta k) (enc a kp (privk a))
         (enc (enc k (pubk b)) (invk kp)))) (recv (enc "resp" tb k)))
    ((recv
       (cat (enc "init" ta k) (enc a-0 kp-0 (privk a-0))
         (enc (enc k (pubk b)) (invk kp-0)))) (send (enc "resp" tb k))))
  (label 5)
  (parent 3)
  (realized)
  (shape)
  (maps ((0) ((a a) (b b) (k k) (kp kp) (ta ta) (tb tb))))
  (origs (k (0 0)) (kp (0 0))))

(comment "Nothing left to do")

(defprotocol dass+ basic
  (defrole init
    (vars (a b name) (k skey) (ta text) (kp akey) (tb text))
    (trace
      (send
        (cat (enc "init" ta k) (enc a kp (privk a))
          (enc (enc k (pubk b)) (invk kp)))) (recv (enc "resp" tb k))))
  (defrole resp
    (vars (a b name) (k skey) (ta text) (kp akey) (tb text))
    (trace
      (recv
        (cat (enc "init" ta k) (enc a kp (privk a))
          (enc (enc k (pubk b)) (invk kp)))) (send (enc "resp" tb k)))
    (non-orig (privk a)))
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
  (comment "In this version of the protocol ")
  (comment "b never interacts with a compromised initiator.")
  (comment "That is why a is properly authenticated to b."))

(defskeleton dass+
  (vars (k skey) (ta tb text) (kp akey) (a b name))
  (defstrand init 2 (k k) (ta ta) (tb tb) (kp kp) (a a) (b b))
  (non-orig (invk kp) (privk a) (privk b))
  (uniq-orig k kp)
  (traces
    ((send
       (cat (enc "init" ta k) (enc a kp (privk a))
         (enc (enc k (pubk b)) (invk kp)))) (recv (enc "resp" tb k))))
  (label 6)
  (unrealized (0 1))
  (origs (k (0 0)) (kp (0 0)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton dass+
  (vars (k skey) (ta tb ta-0 text) (kp kp-0 akey) (a b a-0 b-0 name))
  (defstrand init 2 (k k) (ta ta) (tb tb) (kp kp) (a a) (b b))
  (defstrand resp 2 (k k) (ta ta-0) (tb tb) (kp kp-0) (a a-0) (b b-0))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (invk kp) (privk a) (privk b) (privk a-0))
  (uniq-orig k kp)
  (operation encryption-test (added-strand resp 2) (enc "resp" tb k)
    (0 1))
  (traces
    ((send
       (cat (enc "init" ta k) (enc a kp (privk a))
         (enc (enc k (pubk b)) (invk kp)))) (recv (enc "resp" tb k)))
    ((recv
       (cat (enc "init" ta-0 k) (enc a-0 kp-0 (privk a-0))
         (enc (enc k (pubk b-0)) (invk kp-0))))
      (send (enc "resp" tb k))))
  (label 7)
  (parent 6)
  (unrealized (1 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton dass+
  (vars (k skey) (ta tb text) (kp akey) (a b name))
  (defstrand init 2 (k k) (ta ta) (tb tb) (kp kp) (a a) (b b))
  (deflistener k)
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (invk kp) (privk a) (privk b))
  (uniq-orig k kp)
  (operation encryption-test (added-listener k) (enc "resp" tb k) (0 1))
  (traces
    ((send
       (cat (enc "init" ta k) (enc a kp (privk a))
         (enc (enc k (pubk b)) (invk kp)))) (recv (enc "resp" tb k)))
    ((recv k) (send k)))
  (label 8)
  (parent 6)
  (unrealized (1 0))
  (dead)
  (comment "empty cohort"))

(defskeleton dass+
  (vars (k skey) (ta tb text) (kp kp-0 akey) (a b a-0 b-0 name))
  (defstrand init 2 (k k) (ta ta) (tb tb) (kp kp) (a a) (b b))
  (defstrand resp 2 (k k) (ta ta) (tb tb) (kp kp-0) (a a-0) (b b-0))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (invk kp) (privk a) (privk b) (privk a-0))
  (uniq-orig k kp)
  (operation encryption-test (displaced 2 0 init 1) (enc "init" ta-0 k)
    (1 0))
  (traces
    ((send
       (cat (enc "init" ta k) (enc a kp (privk a))
         (enc (enc k (pubk b)) (invk kp)))) (recv (enc "resp" tb k)))
    ((recv
       (cat (enc "init" ta k) (enc a-0 kp-0 (privk a-0))
         (enc (enc k (pubk b-0)) (invk kp-0))))
      (send (enc "resp" tb k))))
  (label 9)
  (parent 7)
  (unrealized (1 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton dass+
  (vars (k skey) (ta tb ta-0 text) (kp kp-0 akey) (a b a-0 b-0 name))
  (defstrand init 2 (k k) (ta ta) (tb tb) (kp kp) (a a) (b b))
  (defstrand resp 2 (k k) (ta ta-0) (tb tb) (kp kp-0) (a a-0) (b b-0))
  (deflistener k)
  (precedes ((0 0) (2 0)) ((1 1) (0 1)) ((2 1) (1 0)))
  (non-orig (invk kp) (privk a) (privk b) (privk a-0))
  (uniq-orig k kp)
  (operation encryption-test (added-listener k) (enc "init" ta-0 k)
    (1 0))
  (traces
    ((send
       (cat (enc "init" ta k) (enc a kp (privk a))
         (enc (enc k (pubk b)) (invk kp)))) (recv (enc "resp" tb k)))
    ((recv
       (cat (enc "init" ta-0 k) (enc a-0 kp-0 (privk a-0))
         (enc (enc k (pubk b-0)) (invk kp-0))))
      (send (enc "resp" tb k))) ((recv k) (send k)))
  (label 10)
  (parent 7)
  (unrealized (1 0) (2 0))
  (dead)
  (comment "empty cohort"))

(defskeleton dass+
  (vars (k skey) (ta tb text) (kp akey) (a b b-0 name))
  (defstrand init 2 (k k) (ta ta) (tb tb) (kp kp) (a a) (b b))
  (defstrand resp 2 (k k) (ta ta) (tb tb) (kp kp) (a a) (b b-0))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (invk kp) (privk a) (privk b))
  (uniq-orig k kp)
  (operation encryption-test (displaced 2 0 init 1)
    (enc a-0 kp-0 (privk a-0)) (1 0))
  (traces
    ((send
       (cat (enc "init" ta k) (enc a kp (privk a))
         (enc (enc k (pubk b)) (invk kp)))) (recv (enc "resp" tb k)))
    ((recv
       (cat (enc "init" ta k) (enc a kp (privk a))
         (enc (enc k (pubk b-0)) (invk kp)))) (send (enc "resp" tb k))))
  (label 11)
  (parent 9)
  (unrealized (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dass+
  (vars (k k-0 skey) (ta tb ta-0 text) (kp kp-0 akey)
    (a b a-0 b-0 b-1 name))
  (defstrand init 2 (k k) (ta ta) (tb tb) (kp kp) (a a) (b b))
  (defstrand resp 2 (k k) (ta ta) (tb tb) (kp kp-0) (a a-0) (b b-0))
  (defstrand init 1 (k k-0) (ta ta-0) (kp kp-0) (a a-0) (b b-1))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)) ((2 0) (1 0)))
  (non-orig (invk kp) (privk a) (privk b) (privk a-0))
  (uniq-orig k kp)
  (operation encryption-test (added-strand init 1)
    (enc a-0 kp-0 (privk a-0)) (1 0))
  (traces
    ((send
       (cat (enc "init" ta k) (enc a kp (privk a))
         (enc (enc k (pubk b)) (invk kp)))) (recv (enc "resp" tb k)))
    ((recv
       (cat (enc "init" ta k) (enc a-0 kp-0 (privk a-0))
         (enc (enc k (pubk b-0)) (invk kp-0))))
      (send (enc "resp" tb k)))
    ((send
       (cat (enc "init" ta-0 k-0) (enc a-0 kp-0 (privk a-0))
         (enc (enc k-0 (pubk b-1)) (invk kp-0))))))
  (label 12)
  (parent 9)
  (unrealized (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dass+
  (vars (k skey) (ta tb text) (kp akey) (a b name))
  (defstrand init 2 (k k) (ta ta) (tb tb) (kp kp) (a a) (b b))
  (defstrand resp 2 (k k) (ta ta) (tb tb) (kp kp) (a a) (b b))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (invk kp) (privk a) (privk b))
  (uniq-orig k kp)
  (operation encryption-test (displaced 2 0 init 1)
    (enc (enc k (pubk b-0)) (invk kp)) (1 0))
  (traces
    ((send
       (cat (enc "init" ta k) (enc a kp (privk a))
         (enc (enc k (pubk b)) (invk kp)))) (recv (enc "resp" tb k)))
    ((recv
       (cat (enc "init" ta k) (enc a kp (privk a))
         (enc (enc k (pubk b)) (invk kp)))) (send (enc "resp" tb k))))
  (label 13)
  (parent 11)
  (realized)
  (shape)
  (maps ((0) ((a a) (b b) (k k) (kp kp) (ta ta) (tb tb))))
  (origs (k (0 0)) (kp (0 0))))

(defskeleton dass+
  (vars (k k-0 skey) (ta tb ta-0 text) (kp kp-0 akey)
    (a b a-0 b-0 name))
  (defstrand init 2 (k k) (ta ta) (tb tb) (kp kp) (a a) (b b))
  (defstrand resp 2 (k k) (ta ta) (tb tb) (kp kp-0) (a a-0) (b b))
  (defstrand init 1 (k k-0) (ta ta-0) (kp kp-0) (a a-0) (b b-0))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)) ((2 0) (1 0)))
  (non-orig (invk kp) (privk a) (privk b) (privk a-0))
  (uniq-orig k kp)
  (operation nonce-test (contracted (b-1 b)) k (1 0) (enc k (pubk b)))
  (traces
    ((send
       (cat (enc "init" ta k) (enc a kp (privk a))
         (enc (enc k (pubk b)) (invk kp)))) (recv (enc "resp" tb k)))
    ((recv
       (cat (enc "init" ta k) (enc a-0 kp-0 (privk a-0))
         (enc (enc k (pubk b)) (invk kp-0)))) (send (enc "resp" tb k)))
    ((send
       (cat (enc "init" ta-0 k-0) (enc a-0 kp-0 (privk a-0))
         (enc (enc k-0 (pubk b-0)) (invk kp-0))))))
  (label 14)
  (parent 12)
  (realized)
  (shape)
  (maps ((0) ((a a) (b b) (k k) (kp kp) (ta ta) (tb tb))))
  (origs (k (0 0)) (kp (0 0))))

(comment "Nothing left to do")
