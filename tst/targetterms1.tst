(comment "CPSA 4.2.3")
(comment "All input read from tst/targetterms1.scm")

(defprotocol targetterms basic
  (defrole init
    (vars (a skey) (n1 n2 text) (k akey))
    (trace (send (enc n1 (enc a n2 k) k)) (recv (enc a n1 k))))
  (defrole resp
    (vars (n1 text) (m mesg) (k akey))
    (trace (recv (enc n1 m k)) (send m))))

(defskeleton targetterms
  (vars (n1 n2 text) (a skey) (k akey))
  (defstrand init 2 (n1 n1) (n2 n2) (a a) (k k))
  (non-orig (invk k))
  (uniq-orig n1)
  (traces ((send (enc n1 (enc a n2 k) k)) (recv (enc a n1 k))))
  (label 0)
  (unrealized (0 1))
  (origs (n1 (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton targetterms
  (vars (n2 text) (a skey) (k akey))
  (defstrand init 2 (n1 n2) (n2 n2) (a a) (k k))
  (non-orig (invk k))
  (uniq-orig n2)
  (operation nonce-test (displaced 1 0 init 1) n1 (0 1)
    (enc n1 (enc a n2 k) k))
  (traces ((send (enc n2 (enc a n2 k) k)) (recv (enc a n2 k))))
  (label 1)
  (parent 0)
  (unrealized (0 1))
  (origs (n2 (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton targetterms
  (vars (n2 text) (a skey) (k akey))
  (defstrand init 2 (n1 n2) (n2 n2) (a a) (k k))
  (defstrand resp 2 (m (enc a n2 k)) (n1 n2) (k k))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (invk k))
  (uniq-orig n2)
  (operation nonce-test (added-strand resp 2) n2 (0 1)
    (enc n2 (enc a n2 k) k))
  (traces ((send (enc n2 (enc a n2 k) k)) (recv (enc a n2 k)))
    ((recv (enc n2 (enc a n2 k) k)) (send (enc a n2 k))))
  (label 2)
  (parent 1)
  (unrealized)
  (shape)
  (maps ((0) ((n1 n2) (k k) (a a) (n2 n2))))
  (origs (n2 (0 0))))

(comment "Nothing left to do")
