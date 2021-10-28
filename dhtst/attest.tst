(herald attest-door)

(comment "CPSA 4.3.0")
(comment "All input read from dhtst/attest.scm")

(defprotocol attest-door basic
  (defrole appraise
    (vars (d p a akey) (n text))
    (trace (recv (enc (enc d n (invk p)) a)) (send (enc n a p)))
    (comment "The appraiser for the door"))
  (defrole person
    (vars (d p a akey) (k skey) (n t text))
    (trace (send (enc (enc d n (invk p)) a)) (recv (enc n a p))
      (send (enc (enc k (invk p)) d)) (recv (enc t k)) (send t))
    (uniq-orig k n)
    (comment "Person requesting door entry"))
  (defrole door
    (vars (d p akey) (k skey) (t text))
    (trace (recv (enc (enc k (invk p)) d)) (send (enc t k)) (recv t))
    (uniq-orig t))
  (defrole squealer
    (vars (d p akey) (k skey))
    (trace (recv (enc (enc k (invk p)) d)) (send k))
    (comment "Fake door"))
  (defrule yes
    (forall ((z strd) (a akey))
      (implies
        (and (p "appraise" z 2) (p "appraise" "a" z a) (non (invk a)))
        (exists ((d akey))
          (and (p "appraise" "d" z d) (non (invk d))))))
    (comment "Appraisal succeeded"))
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
  (comment "Door attestations protocol"))

(defskeleton attest-door
  (vars (k skey) (n t text) (p a d akey))
  (defstrand person 5 (k k) (n n) (t t) (d d) (p p) (a a))
  (non-orig (invk p) (invk a))
  (uniq-orig k n)
  (comment "Analyze from the person's perspective")
  (traces
    ((send (enc (enc d n (invk p)) a)) (recv (enc n a p))
      (send (enc (enc k (invk p)) d)) (recv (enc t k)) (send t)))
  (label 0)
  (unrealized (0 1))
  (origs (k (0 2)) (n (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton attest-door
  (vars (k skey) (n t text) (p a d akey))
  (defstrand person 5 (k k) (n n) (t t) (d d) (p p) (a a))
  (defstrand appraise 2 (n n) (d d) (p p) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (invk p) (invk a) (invk d))
  (uniq-orig k n)
  (rule yes)
  (operation nonce-test (added-strand appraise 2) n (0 1)
    (enc (enc d n (invk p)) a))
  (traces
    ((send (enc (enc d n (invk p)) a)) (recv (enc n a p))
      (send (enc (enc k (invk p)) d)) (recv (enc t k)) (send t))
    ((recv (enc (enc d n (invk p)) a)) (send (enc n a p))))
  (label 1)
  (parent 0)
  (unrealized (0 3))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton attest-door
  (vars (k skey) (n t text) (p a d d-0 p-0 akey))
  (defstrand person 5 (k k) (n n) (t t) (d d) (p p) (a a))
  (defstrand appraise 2 (n n) (d d) (p p) (a a))
  (defstrand door 2 (k k) (t t) (d d-0) (p p-0))
  (precedes ((0 0) (1 0)) ((0 2) (2 0)) ((1 1) (0 1)) ((2 1) (0 3)))
  (non-orig (invk p) (invk a) (invk d))
  (uniq-orig k n t)
  (operation encryption-test (added-strand door 2) (enc t k) (0 3))
  (traces
    ((send (enc (enc d n (invk p)) a)) (recv (enc n a p))
      (send (enc (enc k (invk p)) d)) (recv (enc t k)) (send t))
    ((recv (enc (enc d n (invk p)) a)) (send (enc n a p)))
    ((recv (enc (enc k (invk p-0)) d-0)) (send (enc t k))))
  (label 2)
  (parent 1)
  (unrealized (2 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton attest-door
  (vars (k skey) (n t text) (p a d akey))
  (defstrand person 5 (k k) (n n) (t t) (d d) (p p) (a a))
  (defstrand appraise 2 (n n) (d d) (p p) (a a))
  (deflistener k)
  (precedes ((0 0) (1 0)) ((0 2) (2 0)) ((1 1) (0 1)) ((2 1) (0 3)))
  (non-orig (invk p) (invk a) (invk d))
  (uniq-orig k n)
  (operation encryption-test (added-listener k) (enc t k) (0 3))
  (traces
    ((send (enc (enc d n (invk p)) a)) (recv (enc n a p))
      (send (enc (enc k (invk p)) d)) (recv (enc t k)) (send t))
    ((recv (enc (enc d n (invk p)) a)) (send (enc n a p)))
    ((recv k) (send k)))
  (label 3)
  (parent 1)
  (unrealized (2 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton attest-door
  (vars (k skey) (n t text) (p a d akey))
  (defstrand person 5 (k k) (n n) (t t) (d d) (p p) (a a))
  (defstrand appraise 2 (n n) (d d) (p p) (a a))
  (defstrand door 2 (k k) (t t) (d d) (p p))
  (precedes ((0 0) (1 0)) ((0 2) (2 0)) ((1 1) (0 1)) ((2 1) (0 3)))
  (non-orig (invk p) (invk a) (invk d))
  (uniq-orig k n t)
  (operation nonce-test (contracted (d-0 d) (p-0 p)) k (2 0)
    (enc (enc k (invk p)) d))
  (traces
    ((send (enc (enc d n (invk p)) a)) (recv (enc n a p))
      (send (enc (enc k (invk p)) d)) (recv (enc t k)) (send t))
    ((recv (enc (enc d n (invk p)) a)) (send (enc n a p)))
    ((recv (enc (enc k (invk p)) d)) (send (enc t k))))
  (label 4)
  (parent 2)
  (unrealized)
  (shape)
  (maps ((0) ((p p) (a a) (d d) (k k) (n n) (t t))))
  (origs (t (2 1)) (k (0 2)) (n (0 0))))

(defskeleton attest-door
  (vars (k skey) (n t text) (p a d d-0 p-0 akey))
  (defstrand person 5 (k k) (n n) (t t) (d d) (p p) (a a))
  (defstrand appraise 2 (n n) (d d) (p p) (a a))
  (defstrand door 2 (k k) (t t) (d d-0) (p p-0))
  (defstrand squealer 2 (k k) (d d) (p p))
  (precedes ((0 0) (1 0)) ((0 2) (3 0)) ((1 1) (0 1)) ((2 1) (0 3))
    ((3 1) (2 0)))
  (non-orig (invk p) (invk a) (invk d))
  (uniq-orig k n t)
  (operation nonce-test (added-strand squealer 2) k (2 0)
    (enc (enc k (invk p)) d))
  (traces
    ((send (enc (enc d n (invk p)) a)) (recv (enc n a p))
      (send (enc (enc k (invk p)) d)) (recv (enc t k)) (send t))
    ((recv (enc (enc d n (invk p)) a)) (send (enc n a p)))
    ((recv (enc (enc k (invk p-0)) d-0)) (send (enc t k)))
    ((recv (enc (enc k (invk p)) d)) (send k)))
  (label 5)
  (parent 2)
  (unrealized)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton attest-door
  (vars (k skey) (n t text) (p a d akey))
  (defstrand person 5 (k k) (n n) (t t) (d d) (p p) (a a))
  (defstrand appraise 2 (n n) (d d) (p p) (a a))
  (deflistener k)
  (defstrand squealer 2 (k k) (d d) (p p))
  (precedes ((0 0) (1 0)) ((0 2) (3 0)) ((1 1) (0 1)) ((2 1) (0 3))
    ((3 1) (2 0)))
  (non-orig (invk p) (invk a) (invk d))
  (uniq-orig k n)
  (operation nonce-test (added-strand squealer 2) k (2 0)
    (enc (enc k (invk p)) d))
  (traces
    ((send (enc (enc d n (invk p)) a)) (recv (enc n a p))
      (send (enc (enc k (invk p)) d)) (recv (enc t k)) (send t))
    ((recv (enc (enc d n (invk p)) a)) (send (enc n a p)))
    ((recv k) (send k)) ((recv (enc (enc k (invk p)) d)) (send k)))
  (label 6)
  (parent 3)
  (unrealized)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton attest-door
  (vars (k skey) (n t text) (p a d akey))
  (defstrand person 5 (k k) (n n) (t t) (d d) (p p) (a a))
  (defstrand appraise 2 (n n) (d d) (p p) (a a))
  (defstrand squealer 2 (k k) (d d) (p p))
  (precedes ((0 0) (1 0)) ((0 2) (2 0)) ((1 1) (0 1)) ((2 1) (0 3)))
  (non-orig (invk p) (invk a) (invk d))
  (uniq-orig k n t)
  (operation generalization deleted (2 0))
  (traces
    ((send (enc (enc d n (invk p)) a)) (recv (enc n a p))
      (send (enc (enc k (invk p)) d)) (recv (enc t k)) (send t))
    ((recv (enc (enc d n (invk p)) a)) (send (enc n a p)))
    ((recv (enc (enc k (invk p)) d)) (send k)))
  (label 7)
  (parent 5)
  (seen 8)
  (unrealized)
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton attest-door
  (vars (k skey) (n t text) (p a d akey))
  (defstrand person 5 (k k) (n n) (t t) (d d) (p p) (a a))
  (defstrand appraise 2 (n n) (d d) (p p) (a a))
  (defstrand squealer 2 (k k) (d d) (p p))
  (precedes ((0 0) (1 0)) ((0 2) (2 0)) ((1 1) (0 1)) ((2 1) (0 3)))
  (non-orig (invk p) (invk a) (invk d))
  (uniq-orig k n)
  (operation generalization deleted (2 0))
  (traces
    ((send (enc (enc d n (invk p)) a)) (recv (enc n a p))
      (send (enc (enc k (invk p)) d)) (recv (enc t k)) (send t))
    ((recv (enc (enc d n (invk p)) a)) (send (enc n a p)))
    ((recv (enc (enc k (invk p)) d)) (send k)))
  (label 8)
  (parent 6)
  (unrealized)
  (shape)
  (maps ((0) ((p p) (a a) (d d) (k k) (n n) (t t))))
  (origs (k (0 2)) (n (0 0))))

(comment "Nothing left to do")

(defprotocol attest-door-trust basic
  (defrole appraise
    (vars (d p a akey) (n text))
    (trace (recv (enc (enc d n (invk p)) a)) (send (enc n a p)))
    (comment "The appraiser for the door"))
  (defrole person
    (vars (d p a akey) (k skey) (n t text))
    (trace (send (enc (enc d n (invk p)) a)) (recv (enc n a p))
      (send (enc (enc k (invk p)) d)) (recv (enc t k)) (send t))
    (uniq-orig k n)
    (comment "Person requesting door entry"))
  (defrole door
    (vars (d p akey) (k skey) (t text))
    (trace (recv (enc (enc k (invk p)) d)) (send (enc t k)) (recv t))
    (uniq-orig t))
  (defrole squealer
    (vars (d p akey) (k skey))
    (trace (recv (enc (enc k (invk p)) d)) (send k))
    (comment "Fake door"))
  (defrule yes
    (forall ((z strd) (a akey))
      (implies
        (and (p "appraise" z 2) (p "appraise" "a" z a) (non (invk a)))
        (exists ((d akey))
          (and (p "appraise" "d" z d) (non (invk d))))))
    (comment "Appraisal succeeded"))
  (defrule trust
    (forall ((z w strd) (d akey))
      (implies
        (and (p "appraise" z 2) (p "appraise" "d" z d)
          (p "squealer" w 2) (p "squealer" "d" w d))
        (false)))
    (comment "Squealer prohibited due to attestation"))
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
  (comment "Door attestations protocol with attestation"))

(defskeleton attest-door-trust
  (vars (k skey) (n t text) (p a d akey))
  (defstrand person 5 (k k) (n n) (t t) (d d) (p p) (a a))
  (non-orig (invk p) (invk a))
  (uniq-orig k n)
  (comment "Analyze from the person's perspective")
  (traces
    ((send (enc (enc d n (invk p)) a)) (recv (enc n a p))
      (send (enc (enc k (invk p)) d)) (recv (enc t k)) (send t)))
  (label 9)
  (unrealized (0 1))
  (origs (k (0 2)) (n (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton attest-door-trust
  (vars (k skey) (n t text) (p a d akey))
  (defstrand person 5 (k k) (n n) (t t) (d d) (p p) (a a))
  (defstrand appraise 2 (n n) (d d) (p p) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (invk p) (invk a) (invk d))
  (uniq-orig k n)
  (rule yes)
  (operation nonce-test (added-strand appraise 2) n (0 1)
    (enc (enc d n (invk p)) a))
  (traces
    ((send (enc (enc d n (invk p)) a)) (recv (enc n a p))
      (send (enc (enc k (invk p)) d)) (recv (enc t k)) (send t))
    ((recv (enc (enc d n (invk p)) a)) (send (enc n a p))))
  (label 10)
  (parent 9)
  (unrealized (0 3))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton attest-door-trust
  (vars (k skey) (n t text) (p a d d-0 p-0 akey))
  (defstrand person 5 (k k) (n n) (t t) (d d) (p p) (a a))
  (defstrand appraise 2 (n n) (d d) (p p) (a a))
  (defstrand door 2 (k k) (t t) (d d-0) (p p-0))
  (precedes ((0 0) (1 0)) ((0 2) (2 0)) ((1 1) (0 1)) ((2 1) (0 3)))
  (non-orig (invk p) (invk a) (invk d))
  (uniq-orig k n t)
  (operation encryption-test (added-strand door 2) (enc t k) (0 3))
  (traces
    ((send (enc (enc d n (invk p)) a)) (recv (enc n a p))
      (send (enc (enc k (invk p)) d)) (recv (enc t k)) (send t))
    ((recv (enc (enc d n (invk p)) a)) (send (enc n a p)))
    ((recv (enc (enc k (invk p-0)) d-0)) (send (enc t k))))
  (label 11)
  (parent 10)
  (unrealized (2 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton attest-door-trust
  (vars (k skey) (n t text) (p a d akey))
  (defstrand person 5 (k k) (n n) (t t) (d d) (p p) (a a))
  (defstrand appraise 2 (n n) (d d) (p p) (a a))
  (deflistener k)
  (precedes ((0 0) (1 0)) ((0 2) (2 0)) ((1 1) (0 1)) ((2 1) (0 3)))
  (non-orig (invk p) (invk a) (invk d))
  (uniq-orig k n)
  (operation encryption-test (added-listener k) (enc t k) (0 3))
  (traces
    ((send (enc (enc d n (invk p)) a)) (recv (enc n a p))
      (send (enc (enc k (invk p)) d)) (recv (enc t k)) (send t))
    ((recv (enc (enc d n (invk p)) a)) (send (enc n a p)))
    ((recv k) (send k)))
  (label 12)
  (parent 10)
  (unrealized (2 0))
  (dead)
  (comment "empty cohort"))

(defskeleton attest-door-trust
  (vars (k skey) (n t text) (p a d akey))
  (defstrand person 5 (k k) (n n) (t t) (d d) (p p) (a a))
  (defstrand appraise 2 (n n) (d d) (p p) (a a))
  (defstrand door 2 (k k) (t t) (d d) (p p))
  (precedes ((0 0) (1 0)) ((0 2) (2 0)) ((1 1) (0 1)) ((2 1) (0 3)))
  (non-orig (invk p) (invk a) (invk d))
  (uniq-orig k n t)
  (operation nonce-test (contracted (d-0 d) (p-0 p)) k (2 0)
    (enc (enc k (invk p)) d))
  (traces
    ((send (enc (enc d n (invk p)) a)) (recv (enc n a p))
      (send (enc (enc k (invk p)) d)) (recv (enc t k)) (send t))
    ((recv (enc (enc d n (invk p)) a)) (send (enc n a p)))
    ((recv (enc (enc k (invk p)) d)) (send (enc t k))))
  (label 13)
  (parent 11)
  (unrealized)
  (shape)
  (maps ((0) ((p p) (a a) (d d) (k k) (n n) (t t))))
  (origs (t (2 1)) (k (0 2)) (n (0 0))))

(comment "Nothing left to do")
