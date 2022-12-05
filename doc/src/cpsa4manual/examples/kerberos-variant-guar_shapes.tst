(comment "CPSA 4.3.1")
(comment "Extracted shapes")

(comment "CPSA 4.3.1")

(comment "All input read from kerberos-variant-guar.scm")

(defprotocol kerberos-variant basic
  (defrole init
    (vars (a b ks name) (t n t-prime l text) (a-ks-lt k skey)
      (ticket mesg))
    (trace (send (cat a b ks))
      (recv (cat (enc t l k a b ks a-ks-lt) ticket))
      (send (cat (enc a t n k) ticket)) (recv (enc n t-prime k))))
  (defrole resp
    (vars (a b ks name) (t n t-prime l text) (b-ks-lt k skey))
    (trace
      (recv (cat (enc a t n k) (enc "ticket" t l k a b ks b-ks-lt)))
      (send (enc n t-prime k))))
  (defrole keyserver
    (vars (a b ks name) (t l text) (a-ks-lt b-ks-lt k skey))
    (trace (recv (cat a b ks))
      (send
        (cat (enc t l k a b ks a-ks-lt)
          (enc "ticket" t l k a b ks b-ks-lt))))
    (uniq-orig k))
  (defrule long-term-key-non
    (forall ((p ks name) (k-lt skey))
      (implies (fact long-term p ks k-lt) (non k-lt))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule guar-keyserver-2
    (forall ((z strd) (a-ks-lt b-ks-lt skey) (ks a b name))
      (implies
        (and (p "keyserver" z 2) (p "keyserver" "a-ks-lt" z a-ks-lt)
          (p "keyserver" "b-ks-lt" z b-ks-lt) (p "keyserver" "ks" z ks)
          (p "keyserver" "a" z a) (p "keyserver" "b" z b))
        (and (fact long-term a ks a-ks-lt)
          (fact long-term b ks b-ks-lt))))))

(defskeleton kerberos-variant
  (vars (ticket mesg) (a-ks-lt k skey) (n t t-prime l text)
    (a b ks name))
  (defstrand init 4 (ticket ticket) (a-ks-lt a-ks-lt) (k k) (t t) (n n)
    (t-prime t-prime) (l l) (a a) (b b) (ks ks))
  (non-orig a-ks-lt)
  (uniq-orig n)
  (traces
    ((send (cat a b ks)) (recv (cat (enc t l k a b ks a-ks-lt) ticket))
      (send (cat (enc a t n k) ticket)) (recv (enc n t-prime k))))
  (label 0)
  (unrealized (0 1))
  (origs (n (0 2)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton kerberos-variant
  (vars (ticket mesg) (a-ks-lt k b-ks-lt skey) (n t t-prime l text)
    (a b ks name))
  (defstrand init 4 (ticket ticket) (a-ks-lt a-ks-lt) (k k) (t t) (n n)
    (t-prime t-prime) (l l) (a a) (b b) (ks ks))
  (defstrand keyserver 2 (a-ks-lt a-ks-lt) (b-ks-lt b-ks-lt) (k k) (t t)
    (l l) (a a) (b b) (ks ks))
  (defstrand resp 2 (b-ks-lt b-ks-lt) (k k) (t t) (n n)
    (t-prime t-prime) (l l) (a a) (b b) (ks ks))
  (precedes ((0 2) (2 0)) ((1 1) (0 1)) ((2 1) (0 3)))
  (non-orig a-ks-lt b-ks-lt)
  (uniq-orig k n)
  (facts (long-term b ks b-ks-lt) (long-term a ks a-ks-lt))
  (operation nonce-test
    (contracted (b-0 b) (ks-0 ks) (l-0 l) (b-ks-lt-0 b-ks-lt)) k (2 0)
    (enc "ticket" t l k a b ks b-ks-lt) (enc t l k a b ks a-ks-lt))
  (traces
    ((send (cat a b ks)) (recv (cat (enc t l k a b ks a-ks-lt) ticket))
      (send (cat (enc a t n k) ticket)) (recv (enc n t-prime k)))
    ((recv (cat a b ks))
      (send
        (cat (enc t l k a b ks a-ks-lt)
          (enc "ticket" t l k a b ks b-ks-lt))))
    ((recv (cat (enc a t n k) (enc "ticket" t l k a b ks b-ks-lt)))
      (send (enc n t-prime k))))
  (label 6)
  (parent 0)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (ks ks) (n n) (a-ks-lt a-ks-lt) (t t)
        (t-prime t-prime) (l l) (k k) (ticket ticket))))
  (origs (k (1 1)) (n (0 2))))

(comment "Nothing left to do")

(defprotocol kerberos-variant basic
  (defrole init
    (vars (a b ks name) (t n t-prime l text) (a-ks-lt k skey)
      (ticket mesg))
    (trace (send (cat a b ks))
      (recv (cat (enc t l k a b ks a-ks-lt) ticket))
      (send (cat (enc a t n k) ticket)) (recv (enc n t-prime k))))
  (defrole resp
    (vars (a b ks name) (t n t-prime l text) (b-ks-lt k skey))
    (trace
      (recv (cat (enc a t n k) (enc "ticket" t l k a b ks b-ks-lt)))
      (send (enc n t-prime k))))
  (defrole keyserver
    (vars (a b ks name) (t l text) (a-ks-lt b-ks-lt k skey))
    (trace (recv (cat a b ks))
      (send
        (cat (enc t l k a b ks a-ks-lt)
          (enc "ticket" t l k a b ks b-ks-lt))))
    (uniq-orig k))
  (defrule long-term-key-non
    (forall ((p ks name) (k-lt skey))
      (implies (fact long-term p ks k-lt) (non k-lt))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule guar-keyserver-2
    (forall ((z strd) (a-ks-lt b-ks-lt skey) (ks a b name))
      (implies
        (and (p "keyserver" z 2) (p "keyserver" "a-ks-lt" z a-ks-lt)
          (p "keyserver" "b-ks-lt" z b-ks-lt) (p "keyserver" "ks" z ks)
          (p "keyserver" "a" z a) (p "keyserver" "b" z b))
        (and (fact long-term a ks a-ks-lt)
          (fact long-term b ks b-ks-lt))))))

(defskeleton kerberos-variant
  (vars (b-ks-lt k skey) (t n t-prime l text) (a b ks name))
  (defstrand resp 2 (b-ks-lt b-ks-lt) (k k) (t t) (n n)
    (t-prime t-prime) (l l) (a a) (b b) (ks ks))
  (non-orig b-ks-lt)
  (traces
    ((recv (cat (enc a t n k) (enc "ticket" t l k a b ks b-ks-lt)))
      (send (enc n t-prime k))))
  (label 7)
  (unrealized (0 0))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton kerberos-variant
  (vars (ticket mesg) (b-ks-lt k a-ks-lt skey) (t n t-prime l text)
    (a b ks name))
  (defstrand resp 2 (b-ks-lt b-ks-lt) (k k) (t t) (n n)
    (t-prime t-prime) (l l) (a a) (b b) (ks ks))
  (defstrand keyserver 2 (a-ks-lt a-ks-lt) (b-ks-lt b-ks-lt) (k k) (t t)
    (l l) (a a) (b b) (ks ks))
  (defstrand init 3 (ticket ticket) (a-ks-lt a-ks-lt) (k k) (t t) (n n)
    (l l) (a a) (b b) (ks ks))
  (precedes ((1 1) (2 1)) ((2 2) (0 0)))
  (non-orig b-ks-lt a-ks-lt)
  (uniq-orig k)
  (facts (long-term b ks b-ks-lt) (long-term a ks a-ks-lt))
  (operation nonce-test
    (contracted (b-0 b) (ks-0 ks) (l-0 l) (a-ks-lt-0 a-ks-lt)) k (2 1)
    (enc "ticket" t l k a b ks b-ks-lt) (enc t l k a b ks a-ks-lt))
  (traces
    ((recv (cat (enc a t n k) (enc "ticket" t l k a b ks b-ks-lt)))
      (send (enc n t-prime k)))
    ((recv (cat a b ks))
      (send
        (cat (enc t l k a b ks a-ks-lt)
          (enc "ticket" t l k a b ks b-ks-lt))))
    ((send (cat a b ks)) (recv (cat (enc t l k a b ks a-ks-lt) ticket))
      (send (cat (enc a t n k) ticket))))
  (label 11)
  (parent 7)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (ks ks) (b-ks-lt b-ks-lt) (t t) (n n)
        (t-prime t-prime) (l l) (k k))))
  (origs (k (1 1))))

(comment "Nothing left to do")

(defprotocol kerberos-variant basic
  (defrole init
    (vars (a b ks name) (t n t-prime l text) (a-ks-lt k skey)
      (ticket mesg))
    (trace (send (cat a b ks))
      (recv (cat (enc t l k a b ks a-ks-lt) ticket))
      (send (cat (enc a t n k) ticket)) (recv (enc n t-prime k))))
  (defrole resp
    (vars (a b ks name) (t n t-prime l text) (b-ks-lt k skey))
    (trace
      (recv (cat (enc a t n k) (enc "ticket" t l k a b ks b-ks-lt)))
      (send (enc n t-prime k))))
  (defrole keyserver
    (vars (a b ks name) (t l text) (a-ks-lt b-ks-lt k skey))
    (trace (recv (cat a b ks))
      (send
        (cat (enc t l k a b ks a-ks-lt)
          (enc "ticket" t l k a b ks b-ks-lt))))
    (uniq-orig k))
  (defrule long-term-key-non
    (forall ((p ks name) (k-lt skey))
      (implies (fact long-term p ks k-lt) (non k-lt))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule guar-keyserver-2
    (forall ((z strd) (a-ks-lt b-ks-lt skey) (ks a b name))
      (implies
        (and (p "keyserver" z 2) (p "keyserver" "a-ks-lt" z a-ks-lt)
          (p "keyserver" "b-ks-lt" z b-ks-lt) (p "keyserver" "ks" z ks)
          (p "keyserver" "a" z a) (p "keyserver" "b" z b))
        (and (fact long-term a ks a-ks-lt)
          (fact long-term b ks b-ks-lt))))))

(defskeleton kerberos-variant
  (vars (a-ks-lt b-ks-lt k skey) (t l text) (a b ks name))
  (defstrand keyserver 2 (a-ks-lt a-ks-lt) (b-ks-lt b-ks-lt) (k k) (t t)
    (l l) (a a) (b b) (ks ks))
  (uniq-orig k)
  (traces
    ((recv (cat a b ks))
      (send
        (cat (enc t l k a b ks a-ks-lt)
          (enc "ticket" t l k a b ks b-ks-lt)))))
  (label 12)
  (realized)
  (origs (k (0 1)))
  (comment "Not closed under rules"))

(defskeleton kerberos-variant
  (vars (a-ks-lt b-ks-lt k skey) (t l text) (a b ks name))
  (defstrand keyserver 2 (a-ks-lt a-ks-lt) (b-ks-lt b-ks-lt) (k k) (t t)
    (l l) (a a) (b b) (ks ks))
  (non-orig a-ks-lt b-ks-lt)
  (uniq-orig k)
  (facts (long-term b ks b-ks-lt) (long-term a ks a-ks-lt))
  (traces
    ((recv (cat a b ks))
      (send
        (cat (enc t l k a b ks a-ks-lt)
          (enc "ticket" t l k a b ks b-ks-lt)))))
  (label 13)
  (parent 12)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (ks ks) (a-ks-lt a-ks-lt) (b-ks-lt b-ks-lt) (t t)
        (l l) (k k))))
  (origs (k (0 1))))

(comment "Nothing left to do")
