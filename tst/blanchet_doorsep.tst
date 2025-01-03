(comment "CPSA 4.4.5")
(comment "All input read")

(defprotocol blanchet basic
  (defrole init
    (vars (a b akey) (s skey) (d data))
    (trace (send (enc (enc s (invk a)) b)) (recv (enc d s)))
    (uniq-orig s))
  (defrole resp
    (vars (a b akey) (s skey) (d data))
    (trace (recv (enc (enc s (invk a)) b)) (send (enc d s)))
    (uniq_orig d))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (comment "Blanchet's protocol"))

(defskeleton blanchet
  (vars (d data) (s skey) (a b akey))
  (defstrand init 2 (d d) (s s) (a a) (b b))
  (non-orig (invk b))
  (uniq-orig s)
  (comment "Analyze from the initiator's perspective")
  (traces ((send (enc (enc s (invk a)) b)) (recv (enc d s))))
  (label 0)
  (unrealized (0 1))
  (origs (s (0 0)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton blanchet
  (vars (d data) (s skey) (a b a-0 b-0 akey))
  (defstrand init 2 (d d) (s s) (a a) (b b))
  (defstrand resp 2 (d d) (s s) (a a-0) (b b-0))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (invk b))
  (uniq-orig s)
  (operation encryption-test (added-strand resp 2) (enc d s) (0 1))
  (strand-map 0)
  (traces ((send (enc (enc s (invk a)) b)) (recv (enc d s)))
    ((recv (enc (enc s (invk a-0)) b-0)) (send (enc d s))))
  (label 1)
  (parent 0)
  (unrealized (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton blanchet
  (vars (d data) (s skey) (a b akey))
  (defstrand init 2 (d d) (s s) (a a) (b b))
  (deflistener s)
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (invk b))
  (uniq-orig s)
  (operation encryption-test (added-listener s) (enc d s) (0 1))
  (strand-map 0)
  (traces ((send (enc (enc s (invk a)) b)) (recv (enc d s)))
    ((recv s) (send s)))
  (label 2)
  (parent 0)
  (unrealized (1 0))
  (dead)
  (comment "empty cohort"))

(defskeleton blanchet
  (vars (d data) (s skey) (a b akey))
  (defstrand init 2 (d d) (s s) (a a) (b b))
  (defstrand resp 2 (d d) (s s) (a a) (b b))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (invk b))
  (uniq-orig s)
  (operation nonce-test (contracted (a-0 a) (b-0 b)) s (1 0)
    (enc (enc s (invk a)) b))
  (strand-map 0 1)
  (traces ((send (enc (enc s (invk a)) b)) (recv (enc d s)))
    ((recv (enc (enc s (invk a)) b)) (send (enc d s))))
  (label 3)
  (parent 1)
  (realized)
  (shape)
  (maps ((0) ((a a) (b b) (s s) (d d))))
  (origs (s (0 0))))

(comment "Nothing left to do")

(defprotocol doorsep basic
  (defrole person
    (vars (p d akey) (k skey) (t text))
    (trace (send (enc (enc k (invk p)) d)) (recv (enc t k)) (send t))
    (uniq-orig k))
  (defrole door
    (vars (p d akey) (k skey) (t text))
    (trace (recv (enc (enc k (invk p)) d)) (send (enc t k)) (recv t)))
  (defrule trust
    (forall ((z strd) (p d akey) (k skey))
      (implies
        (and (p "person" z (idx 1)) (p "person" "p" z p)
          (p "person" "d" z d) (p "person" "k" z k) (fact trust p))
        (and (non (invk d)) (uniq k)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton doorsep
  (vars (k skey) (t text) (p d akey))
  (defstrand door 3 (k k) (t t) (p p) (d d))
  (non-orig (invk p))
  (uniq-orig t)
  (facts (trust p))
  (comment "Analyze from the door's perspective")
  (traces ((recv (enc (enc k (invk p)) d)) (send (enc t k)) (recv t)))
  (label 4)
  (unrealized (0 0))
  (origs (t (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton doorsep
  (vars (k skey) (t text) (p d d-0 akey))
  (defstrand door 3 (k k) (t t) (p p) (d d))
  (defstrand person 1 (k k) (p p) (d d-0))
  (precedes ((1 0) (0 0)))
  (non-orig (invk p) (invk d-0))
  (uniq-orig k t)
  (facts (trust p))
  (rule trust)
  (operation encryption-test (added-strand person 1) (enc k (invk p))
    (0 0))
  (strand-map 0)
  (traces ((recv (enc (enc k (invk p)) d)) (send (enc t k)) (recv t))
    ((send (enc (enc k (invk p)) d-0))))
  (label 5)
  (parent 4)
  (unrealized (0 0) (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton doorsep
  (vars (k skey) (t text) (p d akey))
  (defstrand door 3 (k k) (t t) (p p) (d d))
  (defstrand person 1 (k k) (p p) (d d))
  (precedes ((1 0) (0 0)))
  (non-orig (invk p) (invk d))
  (uniq-orig k t)
  (facts (trust p))
  (operation encryption-test (contracted (d-0 d)) (enc k (invk p)) (0 0)
    (enc (enc k (invk p)) d))
  (strand-map 0 1)
  (traces ((recv (enc (enc k (invk p)) d)) (send (enc t k)) (recv t))
    ((send (enc (enc k (invk p)) d))))
  (label 6)
  (parent 5)
  (unrealized (0 2))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton doorsep
  (vars (k skey) (t text) (p d akey))
  (defstrand door 3 (k k) (t t) (p p) (d d))
  (defstrand person 3 (k k) (t t) (p p) (d d))
  (precedes ((0 1) (1 1)) ((1 0) (0 0)) ((1 2) (0 2)))
  (non-orig (invk p) (invk d))
  (uniq-orig k t)
  (facts (trust p))
  (operation nonce-test (displaced 1 2 person 3) t (0 2) (enc t k))
  (strand-map 0 1)
  (traces ((recv (enc (enc k (invk p)) d)) (send (enc t k)) (recv t))
    ((send (enc (enc k (invk p)) d)) (recv (enc t k)) (send t)))
  (label 7)
  (parent 6)
  (realized)
  (shape)
  (maps ((0) ((p p) (t t) (d d) (k k))))
  (origs (k (1 0)) (t (0 1))))

(defskeleton doorsep
  (vars (k skey) (t text) (p d akey))
  (defstrand door 3 (k k) (t t) (p p) (d d))
  (defstrand person 1 (k k) (p p) (d d))
  (deflistener k)
  (precedes ((1 0) (0 0)) ((1 0) (2 0)) ((2 1) (0 2)))
  (non-orig (invk p) (invk d))
  (uniq-orig k t)
  (facts (trust p))
  (operation nonce-test (added-listener k) t (0 2) (enc t k))
  (strand-map 0 1)
  (traces ((recv (enc (enc k (invk p)) d)) (send (enc t k)) (recv t))
    ((send (enc (enc k (invk p)) d))) ((recv k) (send k)))
  (label 8)
  (parent 6)
  (unrealized (2 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol doorsep basic
  (defrole person
    (vars (p d akey) (k skey) (t text))
    (trace (send (enc (enc k (invk p)) d)) (recv (enc t k)) (send t))
    (uniq-orig k))
  (defrole door
    (vars (p d akey) (k skey) (t text))
    (trace (recv (enc (enc k (invk p)) d)) (send (enc t k)) (recv t)))
  (defrule trust
    (forall ((z strd) (p d akey) (k skey))
      (implies
        (and (p "person" z (idx 1)) (p "person" "p" z p)
          (p "person" "d" z d) (p "person" "k" z k) (fact trust p))
        (and (non (invk d)) (uniq k)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton doorsep
  (vars (k skey) (t text) (p d akey))
  (defstrand door 3 (k k) (t t) (p p) (d d))
  (non-orig (invk p))
  (uniq-orig t)
  (comment "Analyze from the door's perspective when we don't trust p")
  (traces ((recv (enc (enc k (invk p)) d)) (send (enc t k)) (recv t)))
  (label 9)
  (unrealized (0 0))
  (origs (t (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton doorsep
  (vars (k skey) (t text) (p d d-0 akey))
  (defstrand door 3 (k k) (t t) (p p) (d d))
  (defstrand person 1 (k k) (p p) (d d-0))
  (precedes ((1 0) (0 0)))
  (non-orig (invk p))
  (uniq-orig k t)
  (operation encryption-test (added-strand person 1) (enc k (invk p))
    (0 0))
  (strand-map 0)
  (traces ((recv (enc (enc k (invk p)) d)) (send (enc t k)) (recv t))
    ((send (enc (enc k (invk p)) d-0))))
  (label 10)
  (parent 9)
  (realized)
  (shape)
  (maps ((0) ((p p) (t t) (d d) (k k))))
  (origs (k (1 0)) (t (0 1))))

(comment "Nothing left to do")
