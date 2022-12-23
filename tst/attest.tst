(herald attest-door)

(comment "CPSA 4.4.2")
(comment "All input read from tst/attest.scm")

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
        (and (p "appraise" z (idx 2)) (p "appraise" "a" z a)
          (non (invk a)))
        (exists ((d akey))
          (and (p "appraise" "d" z d) (non (invk d))))))
    (comment "Appraisal succeeded"))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
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
  (realized)
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
  (realized)
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
  (realized)
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
  (realized)
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
  (realized)
  (shape)
  (maps ((0) ((p p) (a a) (d d) (k k) (n n) (t t))))
  (origs (k (0 2)) (n (0 0))))

(comment "Nothing left to do")

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
        (and (p "appraise" z (idx 2)) (p "appraise" "a" z a)
          (non (invk a)))
        (exists ((d akey))
          (and (p "appraise" "d" z d) (non (invk d))))))
    (comment "Appraisal succeeded"))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (comment "Door attestations protocol"))

(defskeleton attest-door
  (vars (k skey) (t text) (p d akey))
  (defstrand door 3 (k k) (t t) (d d) (p p))
  (non-orig (invk p) (invk d))
  (uniq-orig t)
  (comment "Analyze from the door's perspective")
  (traces ((recv (enc (enc k (invk p)) d)) (send (enc t k)) (recv t)))
  (label 9)
  (unrealized (0 0))
  (origs (t (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton attest-door
  (vars (k skey) (t n text) (p d d-0 a akey))
  (defstrand door 3 (k k) (t t) (d d) (p p))
  (defstrand person 3 (k k) (n n) (d d-0) (p p) (a a))
  (precedes ((1 2) (0 0)))
  (non-orig (invk p) (invk d))
  (uniq-orig k t n)
  (operation encryption-test (added-strand person 3) (enc k (invk p))
    (0 0))
  (traces ((recv (enc (enc k (invk p)) d)) (send (enc t k)) (recv t))
    ((send (enc (enc d-0 n (invk p)) a)) (recv (enc n a p))
      (send (enc (enc k (invk p)) d-0))))
  (label 10)
  (parent 9)
  (realized)
  (shape)
  (maps ((0) ((p p) (d d) (k k) (t t))))
  (origs (n (1 0)) (k (1 2)) (t (0 1))))

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
        (and (p "appraise" z (idx 2)) (p "appraise" "a" z a)
          (non (invk a)))
        (exists ((d akey))
          (and (p "appraise" "d" z d) (non (invk d))))))
    (comment "Appraisal succeeded"))
  (defrule trust
    (forall ((z w strd) (d akey))
      (implies
        (and (p "appraise" z (idx 2)) (p "appraise" "d" z d)
          (p "squealer" w (idx 2)) (p "squealer" "d" w d))
        (false)))
    (comment "Passing attestation means not a squealer"))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
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
  (label 11)
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
  (label 12)
  (parent 11)
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
  (label 13)
  (parent 12)
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
  (label 14)
  (parent 12)
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
  (label 15)
  (parent 13)
  (realized)
  (shape)
  (maps ((0) ((p p) (a a) (d d) (k k) (n n) (t t))))
  (origs (t (2 1)) (k (0 2)) (n (0 0))))

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
        (and (p "appraise" z (idx 2)) (p "appraise" "a" z a)
          (non (invk a)))
        (exists ((d akey))
          (and (p "appraise" "d" z d) (non (invk d))))))
    (comment "Appraisal succeeded"))
  (defrule trust
    (forall ((z w strd) (d akey))
      (implies
        (and (p "appraise" z (idx 2)) (p "appraise" "d" z d)
          (p "squealer" w (idx 2)) (p "squealer" "d" w d))
        (false)))
    (comment "Passing attestation means not a squealer"))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (comment "Door attestations protocol with attestation"))

(defskeleton attest-door-trust
  (vars (k skey) (t text) (p d akey))
  (defstrand door 3 (k k) (t t) (d d) (p p))
  (non-orig (invk p) (invk d))
  (uniq-orig t)
  (comment "Analyze from the door's perspective")
  (traces ((recv (enc (enc k (invk p)) d)) (send (enc t k)) (recv t)))
  (label 16)
  (unrealized (0 0))
  (origs (t (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton attest-door-trust
  (vars (k skey) (t n text) (p d d-0 a akey))
  (defstrand door 3 (k k) (t t) (d d) (p p))
  (defstrand person 3 (k k) (n n) (d d-0) (p p) (a a))
  (precedes ((1 2) (0 0)))
  (non-orig (invk p) (invk d))
  (uniq-orig k t n)
  (operation encryption-test (added-strand person 3) (enc k (invk p))
    (0 0))
  (traces ((recv (enc (enc k (invk p)) d)) (send (enc t k)) (recv t))
    ((send (enc (enc d-0 n (invk p)) a)) (recv (enc n a p))
      (send (enc (enc k (invk p)) d-0))))
  (label 17)
  (parent 16)
  (realized)
  (shape)
  (maps ((0) ((p p) (d d) (k k) (t t))))
  (origs (n (1 0)) (k (1 2)) (t (0 1))))

(comment "Nothing left to do")

(defprotocol attest-door-trust-attest basic
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
        (and (p "appraise" z (idx 2)) (p "appraise" "a" z a)
          (non (invk a)))
        (exists ((d akey))
          (and (p "appraise" "d" z d) (non (invk d))))))
    (comment "Appraisal succeeded"))
  (defrule trust
    (forall ((z w strd) (d akey))
      (implies
        (and (p "appraise" z (idx 2)) (p "appraise" "d" z d)
          (p "squealer" w (idx 2)) (p "squealer" "d" w d))
        (false)))
    (comment "Passing attestation means not a squealer"))
  (defrule uncompromised-people-choose-uncompromised-appraisers
    (forall ((z strd) (a p akey))
      (implies
        (and (p "person" z (idx 3)) (p "person" "p" z p)
          (p "person" "a" z a) (non (invk p)))
        (non (invk a)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (comment
    "Door attestations protocol with attestation and reliable persons"))

(defskeleton attest-door-trust-attest
  (vars (k skey) (n t text) (p a d akey))
  (defstrand person 5 (k k) (n n) (t t) (d d) (p p) (a a))
  (non-orig (invk p) (invk a))
  (uniq-orig k n)
  (comment "Analyze from the person's perspective")
  (traces
    ((send (enc (enc d n (invk p)) a)) (recv (enc n a p))
      (send (enc (enc k (invk p)) d)) (recv (enc t k)) (send t)))
  (label 18)
  (unrealized (0 1))
  (origs (k (0 2)) (n (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton attest-door-trust-attest
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
  (label 19)
  (parent 18)
  (unrealized (0 3))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton attest-door-trust-attest
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
  (label 20)
  (parent 19)
  (unrealized (2 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton attest-door-trust-attest
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
  (label 21)
  (parent 19)
  (unrealized (2 0))
  (dead)
  (comment "empty cohort"))

(defskeleton attest-door-trust-attest
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
  (label 22)
  (parent 20)
  (realized)
  (shape)
  (maps ((0) ((p p) (a a) (d d) (k k) (n n) (t t))))
  (origs (t (2 1)) (k (0 2)) (n (0 0))))

(comment "Nothing left to do")

(defprotocol attest-door-trust-attest basic
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
        (and (p "appraise" z (idx 2)) (p "appraise" "a" z a)
          (non (invk a)))
        (exists ((d akey))
          (and (p "appraise" "d" z d) (non (invk d))))))
    (comment "Appraisal succeeded"))
  (defrule trust
    (forall ((z w strd) (d akey))
      (implies
        (and (p "appraise" z (idx 2)) (p "appraise" "d" z d)
          (p "squealer" w (idx 2)) (p "squealer" "d" w d))
        (false)))
    (comment "Passing attestation means not a squealer"))
  (defrule uncompromised-people-choose-uncompromised-appraisers
    (forall ((z strd) (a p akey))
      (implies
        (and (p "person" z (idx 3)) (p "person" "p" z p)
          (p "person" "a" z a) (non (invk p)))
        (non (invk a)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (comment
    "Door attestations protocol with attestation and reliable persons"))

(defskeleton attest-door-trust-attest
  (vars (k skey) (t text) (p d akey))
  (defstrand door 3 (k k) (t t) (d d) (p p))
  (non-orig (invk p) (invk d))
  (uniq-orig t)
  (comment "Analyze from the door's perspective")
  (traces ((recv (enc (enc k (invk p)) d)) (send (enc t k)) (recv t)))
  (label 23)
  (unrealized (0 0))
  (origs (t (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton attest-door-trust-attest
  (vars (k skey) (t n text) (p d d-0 a akey))
  (defstrand door 3 (k k) (t t) (d d) (p p))
  (defstrand person 3 (k k) (n n) (d d-0) (p p) (a a))
  (precedes ((1 2) (0 0)))
  (non-orig (invk p) (invk d) (invk a))
  (uniq-orig k t n)
  (rule uncompromised-people-choose-uncompromised-appraisers)
  (operation encryption-test (added-strand person 3) (enc k (invk p))
    (0 0))
  (traces ((recv (enc (enc k (invk p)) d)) (send (enc t k)) (recv t))
    ((send (enc (enc d-0 n (invk p)) a)) (recv (enc n a p))
      (send (enc (enc k (invk p)) d-0))))
  (label 24)
  (parent 23)
  (unrealized (1 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton attest-door-trust-attest
  (vars (k skey) (t n text) (p d d-0 a akey))
  (defstrand door 3 (k k) (t t) (d d) (p p))
  (defstrand person 3 (k k) (n n) (d d-0) (p p) (a a))
  (defstrand appraise 2 (n n) (d d-0) (p p) (a a))
  (precedes ((1 0) (2 0)) ((1 2) (0 0)) ((2 1) (1 1)))
  (non-orig (invk p) (invk d) (invk d-0) (invk a))
  (uniq-orig k t n)
  (rule yes)
  (operation nonce-test (added-strand appraise 2) n (1 1)
    (enc (enc d-0 n (invk p)) a))
  (traces ((recv (enc (enc k (invk p)) d)) (send (enc t k)) (recv t))
    ((send (enc (enc d-0 n (invk p)) a)) (recv (enc n a p))
      (send (enc (enc k (invk p)) d-0)))
    ((recv (enc (enc d-0 n (invk p)) a)) (send (enc n a p))))
  (label 25)
  (parent 24)
  (unrealized (0 0) (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton attest-door-trust-attest
  (vars (k skey) (t n text) (p d a akey))
  (defstrand door 3 (k k) (t t) (d d) (p p))
  (defstrand person 3 (k k) (n n) (d d) (p p) (a a))
  (defstrand appraise 2 (n n) (d d) (p p) (a a))
  (precedes ((1 0) (2 0)) ((1 2) (0 0)) ((2 1) (1 1)))
  (non-orig (invk p) (invk d) (invk a))
  (uniq-orig k t n)
  (operation encryption-test (contracted (d-0 d)) (enc k (invk p)) (0 0)
    (enc (enc k (invk p)) d))
  (traces ((recv (enc (enc k (invk p)) d)) (send (enc t k)) (recv t))
    ((send (enc (enc d n (invk p)) a)) (recv (enc n a p))
      (send (enc (enc k (invk p)) d)))
    ((recv (enc (enc d n (invk p)) a)) (send (enc n a p))))
  (label 26)
  (parent 25)
  (unrealized (0 2))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton attest-door-trust-attest
  (vars (k skey) (t n text) (d p a akey))
  (defstrand door 3 (k k) (t t) (d d) (p p))
  (defstrand appraise 2 (n n) (d d) (p p) (a a))
  (defstrand person 5 (k k) (n n) (t t) (d d) (p p) (a a))
  (precedes ((0 1) (2 3)) ((1 1) (2 1)) ((2 0) (1 0)) ((2 2) (0 0))
    ((2 4) (0 2)))
  (non-orig (invk d) (invk p) (invk a))
  (uniq-orig k t n)
  (operation nonce-test (displaced 1 3 person 5) t (0 2) (enc t k))
  (traces ((recv (enc (enc k (invk p)) d)) (send (enc t k)) (recv t))
    ((recv (enc (enc d n (invk p)) a)) (send (enc n a p)))
    ((send (enc (enc d n (invk p)) a)) (recv (enc n a p))
      (send (enc (enc k (invk p)) d)) (recv (enc t k)) (send t)))
  (label 27)
  (parent 26)
  (realized)
  (shape)
  (maps ((0) ((p p) (d d) (k k) (t t))))
  (origs (n (2 0)) (k (2 2)) (t (0 1))))

(defskeleton attest-door-trust-attest
  (vars (k skey) (t n text) (p d a akey))
  (defstrand door 3 (k k) (t t) (d d) (p p))
  (defstrand person 3 (k k) (n n) (d d) (p p) (a a))
  (defstrand appraise 2 (n n) (d d) (p p) (a a))
  (deflistener k)
  (precedes ((1 0) (2 0)) ((1 2) (0 0)) ((1 2) (3 0)) ((2 1) (1 1))
    ((3 1) (0 2)))
  (non-orig (invk p) (invk d) (invk a))
  (uniq-orig k t n)
  (operation nonce-test (added-listener k) t (0 2) (enc t k))
  (traces ((recv (enc (enc k (invk p)) d)) (send (enc t k)) (recv t))
    ((send (enc (enc d n (invk p)) a)) (recv (enc n a p))
      (send (enc (enc k (invk p)) d)))
    ((recv (enc (enc d n (invk p)) a)) (send (enc n a p)))
    ((recv k) (send k)))
  (label 28)
  (parent 26)
  (unrealized (3 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")
