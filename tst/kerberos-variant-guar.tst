(comment "CPSA 4.4.2")
(comment "All input read from tst/kerberos-variant-guar.scm")

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
  (defrule guar-keyserver-2
    (forall
      ((z strd) (b-ks-lt skey) (b name) (a-ks-lt skey) (ks a name))
      (implies
        (and (p "keyserver" z (idx 2)) (p "keyserver" "a" z a)
          (p "keyserver" "ks" z ks) (p "keyserver" "a-ks-lt" z a-ks-lt)
          (p "keyserver" "b" z b) (p "keyserver" "b-ks-lt" z b-ks-lt))
        (and (fact long-term a ks a-ks-lt)
          (fact long-term b ks b-ks-lt)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

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
  (ugens)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton kerberos-variant
  (vars (ticket mesg) (a-ks-lt k b-ks-lt skey) (n t t-prime l text)
    (a b ks name))
  (defstrand init 4 (ticket ticket) (a-ks-lt a-ks-lt) (k k) (t t) (n n)
    (t-prime t-prime) (l l) (a a) (b b) (ks ks))
  (defstrand keyserver 2 (a-ks-lt a-ks-lt) (b-ks-lt b-ks-lt) (k k) (t t)
    (l l) (a a) (b b) (ks ks))
  (precedes ((1 1) (0 1)))
  (non-orig a-ks-lt b-ks-lt)
  (uniq-orig k n)
  (facts (long-term b ks b-ks-lt) (long-term a ks a-ks-lt))
  (rule guar-keyserver-2 long-term-key-non)
  (operation encryption-test (added-strand keyserver 2)
    (enc t l k a b ks a-ks-lt) (0 1))
  (traces
    ((send (cat a b ks)) (recv (cat (enc t l k a b ks a-ks-lt) ticket))
      (send (cat (enc a t n k) ticket)) (recv (enc n t-prime k)))
    ((recv (cat a b ks))
      (send
        (cat (enc t l k a b ks a-ks-lt)
          (enc "ticket" t l k a b ks b-ks-lt)))))
  (label 1)
  (parent 0)
  (unrealized (0 3))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton kerberos-variant
  (vars (ticket mesg) (a-ks-lt k b-ks-lt b-ks-lt-0 skey)
    (n t t-prime l t-0 l-0 text) (a b ks a-0 b-0 ks-0 name))
  (defstrand init 4 (ticket ticket) (a-ks-lt a-ks-lt) (k k) (t t) (n n)
    (t-prime t-prime) (l l) (a a) (b b) (ks ks))
  (defstrand keyserver 2 (a-ks-lt a-ks-lt) (b-ks-lt b-ks-lt) (k k) (t t)
    (l l) (a a) (b b) (ks ks))
  (defstrand resp 2 (b-ks-lt b-ks-lt-0) (k k) (t t-0) (n n)
    (t-prime t-prime) (l l-0) (a a-0) (b b-0) (ks ks-0))
  (precedes ((0 2) (2 0)) ((1 1) (0 1)) ((2 1) (0 3)))
  (non-orig a-ks-lt b-ks-lt)
  (uniq-orig k n)
  (facts (long-term b ks b-ks-lt) (long-term a ks a-ks-lt))
  (rule guar-keyserver-2)
  (operation encryption-test (added-strand resp 2) (enc n t-prime k)
    (0 3))
  (traces
    ((send (cat a b ks)) (recv (cat (enc t l k a b ks a-ks-lt) ticket))
      (send (cat (enc a t n k) ticket)) (recv (enc n t-prime k)))
    ((recv (cat a b ks))
      (send
        (cat (enc t l k a b ks a-ks-lt)
          (enc "ticket" t l k a b ks b-ks-lt))))
    ((recv
       (cat (enc a-0 t-0 n k)
         (enc "ticket" t-0 l-0 k a-0 b-0 ks-0 b-ks-lt-0)))
      (send (enc n t-prime k))))
  (label 2)
  (parent 1)
  (unrealized (2 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton kerberos-variant
  (vars (ticket mesg) (a-ks-lt k b-ks-lt skey) (n t t-prime l text)
    (a b ks name))
  (defstrand init 4 (ticket ticket) (a-ks-lt a-ks-lt) (k k) (t t) (n n)
    (t-prime t-prime) (l l) (a a) (b b) (ks ks))
  (defstrand keyserver 2 (a-ks-lt a-ks-lt) (b-ks-lt b-ks-lt) (k k) (t t)
    (l l) (a a) (b b) (ks ks))
  (deflistener k)
  (precedes ((1 1) (0 1)) ((1 1) (2 0)) ((2 1) (0 3)))
  (non-orig a-ks-lt b-ks-lt)
  (uniq-orig k n)
  (facts (long-term b ks b-ks-lt) (long-term a ks a-ks-lt))
  (rule guar-keyserver-2)
  (operation encryption-test (added-listener k) (enc n t-prime k) (0 3))
  (traces
    ((send (cat a b ks)) (recv (cat (enc t l k a b ks a-ks-lt) ticket))
      (send (cat (enc a t n k) ticket)) (recv (enc n t-prime k)))
    ((recv (cat a b ks))
      (send
        (cat (enc t l k a b ks a-ks-lt)
          (enc "ticket" t l k a b ks b-ks-lt)))) ((recv k) (send k)))
  (label 3)
  (parent 1)
  (unrealized (2 0))
  (dead)
  (comment "empty cohort"))

(defskeleton kerberos-variant
  (vars (ticket mesg) (a-ks-lt k b-ks-lt b-ks-lt-0 skey)
    (n t t-prime l l-0 text) (a b ks b-0 ks-0 name))
  (defstrand init 4 (ticket ticket) (a-ks-lt a-ks-lt) (k k) (t t) (n n)
    (t-prime t-prime) (l l) (a a) (b b) (ks ks))
  (defstrand keyserver 2 (a-ks-lt a-ks-lt) (b-ks-lt b-ks-lt) (k k) (t t)
    (l l) (a a) (b b) (ks ks))
  (defstrand resp 2 (b-ks-lt b-ks-lt-0) (k k) (t t) (n n)
    (t-prime t-prime) (l l-0) (a a) (b b-0) (ks ks-0))
  (precedes ((0 2) (2 0)) ((1 1) (0 1)) ((2 1) (0 3)))
  (non-orig a-ks-lt b-ks-lt)
  (uniq-orig k n)
  (facts (long-term b ks b-ks-lt) (long-term a ks a-ks-lt))
  (rule guar-keyserver-2)
  (operation encryption-test (displaced 3 0 init 3) (enc a-0 t-0 n k)
    (2 0))
  (traces
    ((send (cat a b ks)) (recv (cat (enc t l k a b ks a-ks-lt) ticket))
      (send (cat (enc a t n k) ticket)) (recv (enc n t-prime k)))
    ((recv (cat a b ks))
      (send
        (cat (enc t l k a b ks a-ks-lt)
          (enc "ticket" t l k a b ks b-ks-lt))))
    ((recv
       (cat (enc a t n k) (enc "ticket" t l-0 k a b-0 ks-0 b-ks-lt-0)))
      (send (enc n t-prime k))))
  (label 4)
  (parent 2)
  (unrealized (2 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton kerberos-variant
  (vars (ticket mesg) (a-ks-lt k b-ks-lt b-ks-lt-0 skey)
    (n t t-prime l t-0 l-0 text) (a b ks a-0 b-0 ks-0 name))
  (defstrand init 4 (ticket ticket) (a-ks-lt a-ks-lt) (k k) (t t) (n n)
    (t-prime t-prime) (l l) (a a) (b b) (ks ks))
  (defstrand keyserver 2 (a-ks-lt a-ks-lt) (b-ks-lt b-ks-lt) (k k) (t t)
    (l l) (a a) (b b) (ks ks))
  (defstrand resp 2 (b-ks-lt b-ks-lt-0) (k k) (t t-0) (n n)
    (t-prime t-prime) (l l-0) (a a-0) (b b-0) (ks ks-0))
  (deflistener k)
  (precedes ((0 2) (2 0)) ((1 1) (0 1)) ((1 1) (3 0)) ((2 1) (0 3))
    ((3 1) (2 0)))
  (non-orig a-ks-lt b-ks-lt)
  (uniq-orig k n)
  (facts (long-term b ks b-ks-lt) (long-term a ks a-ks-lt))
  (rule guar-keyserver-2)
  (operation encryption-test (added-listener k) (enc a-0 t-0 n k) (2 0))
  (traces
    ((send (cat a b ks)) (recv (cat (enc t l k a b ks a-ks-lt) ticket))
      (send (cat (enc a t n k) ticket)) (recv (enc n t-prime k)))
    ((recv (cat a b ks))
      (send
        (cat (enc t l k a b ks a-ks-lt)
          (enc "ticket" t l k a b ks b-ks-lt))))
    ((recv
       (cat (enc a-0 t-0 n k)
         (enc "ticket" t-0 l-0 k a-0 b-0 ks-0 b-ks-lt-0)))
      (send (enc n t-prime k))) ((recv k) (send k)))
  (label 5)
  (parent 2)
  (unrealized (3 0))
  (dead)
  (comment "empty cohort"))

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
  (rule guar-keyserver-2)
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
  (parent 4)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (ks ks) (n n) (a-ks-lt a-ks-lt) (t t)
        (t-prime t-prime) (l l) (k k) (ticket ticket))))
  (origs (k (1 1)) (n (0 2)))
  (ugens))

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
  (defrule guar-keyserver-2
    (forall
      ((z strd) (b-ks-lt skey) (b name) (a-ks-lt skey) (ks a name))
      (implies
        (and (p "keyserver" z (idx 2)) (p "keyserver" "a" z a)
          (p "keyserver" "ks" z ks) (p "keyserver" "a-ks-lt" z a-ks-lt)
          (p "keyserver" "b" z b) (p "keyserver" "b-ks-lt" z b-ks-lt))
        (and (fact long-term a ks a-ks-lt)
          (fact long-term b ks b-ks-lt)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

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
  (ugens)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton kerberos-variant
  (vars (b-ks-lt k a-ks-lt skey) (t n t-prime l text) (a b ks name))
  (defstrand resp 2 (b-ks-lt b-ks-lt) (k k) (t t) (n n)
    (t-prime t-prime) (l l) (a a) (b b) (ks ks))
  (defstrand keyserver 2 (a-ks-lt a-ks-lt) (b-ks-lt b-ks-lt) (k k) (t t)
    (l l) (a a) (b b) (ks ks))
  (precedes ((1 1) (0 0)))
  (non-orig b-ks-lt a-ks-lt)
  (uniq-orig k)
  (facts (long-term b ks b-ks-lt) (long-term a ks a-ks-lt))
  (rule guar-keyserver-2 long-term-key-non)
  (operation encryption-test (added-strand keyserver 2)
    (enc "ticket" t l k a b ks b-ks-lt) (0 0))
  (traces
    ((recv (cat (enc a t n k) (enc "ticket" t l k a b ks b-ks-lt)))
      (send (enc n t-prime k)))
    ((recv (cat a b ks))
      (send
        (cat (enc t l k a b ks a-ks-lt)
          (enc "ticket" t l k a b ks b-ks-lt)))))
  (label 8)
  (parent 7)
  (unrealized (0 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton kerberos-variant
  (vars (ticket mesg) (b-ks-lt k a-ks-lt a-ks-lt-0 skey)
    (t n t-prime l l-0 text) (a b ks b-0 ks-0 name))
  (defstrand resp 2 (b-ks-lt b-ks-lt) (k k) (t t) (n n)
    (t-prime t-prime) (l l) (a a) (b b) (ks ks))
  (defstrand keyserver 2 (a-ks-lt a-ks-lt) (b-ks-lt b-ks-lt) (k k) (t t)
    (l l) (a a) (b b) (ks ks))
  (defstrand init 3 (ticket ticket) (a-ks-lt a-ks-lt-0) (k k) (t t)
    (n n) (l l-0) (a a) (b b-0) (ks ks-0))
  (precedes ((1 1) (2 1)) ((2 2) (0 0)))
  (non-orig b-ks-lt a-ks-lt)
  (uniq-orig k)
  (facts (long-term b ks b-ks-lt) (long-term a ks a-ks-lt))
  (rule guar-keyserver-2)
  (operation encryption-test (added-strand init 3) (enc a t n k) (0 0))
  (traces
    ((recv (cat (enc a t n k) (enc "ticket" t l k a b ks b-ks-lt)))
      (send (enc n t-prime k)))
    ((recv (cat a b ks))
      (send
        (cat (enc t l k a b ks a-ks-lt)
          (enc "ticket" t l k a b ks b-ks-lt))))
    ((send (cat a b-0 ks-0))
      (recv (cat (enc t l-0 k a b-0 ks-0 a-ks-lt-0) ticket))
      (send (cat (enc a t n k) ticket))))
  (label 9)
  (parent 8)
  (unrealized (2 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton kerberos-variant
  (vars (b-ks-lt k a-ks-lt skey) (t n t-prime l text) (a b ks name))
  (defstrand resp 2 (b-ks-lt b-ks-lt) (k k) (t t) (n n)
    (t-prime t-prime) (l l) (a a) (b b) (ks ks))
  (defstrand keyserver 2 (a-ks-lt a-ks-lt) (b-ks-lt b-ks-lt) (k k) (t t)
    (l l) (a a) (b b) (ks ks))
  (deflistener k)
  (precedes ((1 1) (2 0)) ((2 1) (0 0)))
  (non-orig b-ks-lt a-ks-lt)
  (uniq-orig k)
  (facts (long-term b ks b-ks-lt) (long-term a ks a-ks-lt))
  (rule guar-keyserver-2)
  (operation encryption-test (added-listener k) (enc a t n k) (0 0))
  (traces
    ((recv (cat (enc a t n k) (enc "ticket" t l k a b ks b-ks-lt)))
      (send (enc n t-prime k)))
    ((recv (cat a b ks))
      (send
        (cat (enc t l k a b ks a-ks-lt)
          (enc "ticket" t l k a b ks b-ks-lt)))) ((recv k) (send k)))
  (label 10)
  (parent 8)
  (unrealized (2 0))
  (dead)
  (comment "empty cohort"))

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
  (rule guar-keyserver-2)
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
  (parent 9)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (ks ks) (b-ks-lt b-ks-lt) (t t) (n n)
        (t-prime t-prime) (l l) (k k))))
  (origs (k (1 1)))
  (ugens))

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
  (defrule guar-keyserver-2
    (forall
      ((z strd) (b-ks-lt skey) (b name) (a-ks-lt skey) (ks a name))
      (implies
        (and (p "keyserver" z (idx 2)) (p "keyserver" "a" z a)
          (p "keyserver" "ks" z ks) (p "keyserver" "a-ks-lt" z a-ks-lt)
          (p "keyserver" "b" z b) (p "keyserver" "b-ks-lt" z b-ks-lt))
        (and (fact long-term a ks a-ks-lt)
          (fact long-term b ks b-ks-lt)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton kerberos-variant
  (vars (a-ks-lt b-ks-lt k skey) (t l text) (a b ks name))
  (defstrand keyserver 2 (a-ks-lt a-ks-lt) (b-ks-lt b-ks-lt) (k k) (t t)
    (l l) (a a) (b b) (ks ks))
  (non-orig a-ks-lt b-ks-lt)
  (uniq-orig k)
  (traces
    ((recv (cat a b ks))
      (send
        (cat (enc t l k a b ks a-ks-lt)
          (enc "ticket" t l k a b ks b-ks-lt)))))
  (label 12)
  (realized)
  (origs (k (0 1)))
  (ugens)
  (comment "Not closed under rules"))

(defskeleton kerberos-variant
  (vars (a-ks-lt b-ks-lt k skey) (t l text) (a b ks name))
  (defstrand keyserver 2 (a-ks-lt a-ks-lt) (b-ks-lt b-ks-lt) (k k) (t t)
    (l l) (a a) (b b) (ks ks))
  (non-orig a-ks-lt b-ks-lt)
  (uniq-orig k)
  (facts (long-term b ks b-ks-lt) (long-term a ks a-ks-lt))
  (rule guar-keyserver-2)
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
  (origs (k (0 1)))
  (ugens))

(comment "Nothing left to do")
