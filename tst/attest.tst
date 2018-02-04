(herald attest-door)

(comment "CPSA 4.1.0")
(comment "All input read from attest.scm")

(defprotocol attest-door basic
  (defrole appraise
    (vars (d p a akey) (n text))
    (trace (recv (enc (enc d n (invk p)) a)) (send (enc n a p)))
    (comment "The appraiser for the door"))
  (defrole person
    (vars (d p a akey) (k skey) (n t text))
    (trace (send (enc (enc d n (invk p)) a)) (recv (enc n a p))
      (send (enc (enc k (invk p)) d)) (recv (enc t k)) (send t))
    (uniq-orig n k)
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
  (comment "Door attestations protocol"))

(defskeleton attest-door
  (vars (n t text) (k skey) (p a d akey))
  (defstrand person 5 (n n) (t t) (k k) (d d) (p p) (a a))
  (non-orig (invk p) (invk a))
  (uniq-orig n k)
  (comment "Analyze from the person's perspective")
  (traces
    ((send (enc (enc d n (invk p)) a)) (recv (enc n a p))
      (send (enc (enc k (invk p)) d)) (recv (enc t k)) (send t)))
  (label 0)
  (unrealized (0 1))
  (origs (k (0 2)) (n (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton attest-door
  (vars (n t text) (k skey) (p a d akey))
  (defstrand person 5 (n n) (t t) (k k) (d d) (p p) (a a))
  (defstrand appraise 2 (n n) (d d) (p p) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (invk p) (invk a))
  (uniq-orig n k)
  (operation nonce-test (added-strand appraise 2) n (0 1)
    (enc (enc d n (invk p)) a))
  (traces
    ((send (enc (enc d n (invk p)) a)) (recv (enc n a p))
      (send (enc (enc k (invk p)) d)) (recv (enc t k)) (send t))
    ((recv (enc (enc d n (invk p)) a)) (send (enc n a p))))
  (label 1)
  (parent 0)
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
    (uniq-orig n k)
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
          (p "squealer" w 2) (p "squealer" "d" w d)) (false)))
    (comment "Squealer prohibited due to attestation"))
  (comment "Door attestations protocol with attestation"))

(defskeleton attest-door-trust
  (vars (n t text) (k skey) (p a d akey))
  (defstrand person 5 (n n) (t t) (k k) (d d) (p p) (a a))
  (non-orig (invk p) (invk a))
  (uniq-orig n k)
  (comment "Analyze from the person's perspective")
  (traces
    ((send (enc (enc d n (invk p)) a)) (recv (enc n a p))
      (send (enc (enc k (invk p)) d)) (recv (enc t k)) (send t)))
  (label 2)
  (unrealized (0 1))
  (origs (k (0 2)) (n (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton attest-door-trust
  (vars (n t text) (k skey) (p a d akey))
  (defstrand person 5 (n n) (t t) (k k) (d d) (p p) (a a))
  (defstrand appraise 2 (n n) (d d) (p p) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (invk p) (invk a))
  (uniq-orig n k)
  (operation nonce-test (added-strand appraise 2) n (0 1)
    (enc (enc d n (invk p)) a))
  (traces
    ((send (enc (enc d n (invk p)) a)) (recv (enc n a p))
      (send (enc (enc k (invk p)) d)) (recv (enc t k)) (send t))
    ((recv (enc (enc d n (invk p)) a)) (send (enc n a p))))
  (label 3)
  (parent 2)
  (unrealized)
  (shape)
  (maps ((0) ((p p) (a a) (d d) (k k) (n n) (t t))))
  (origs (k (0 2)) (n (0 0))))

(comment "Nothing left to do")
