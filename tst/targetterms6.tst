(comment "CPSA 4.4.3")
(comment "All input read from tst/targetterms6.scm")

(defprotocol targetterms6 basic
  (defrole init
    (vars (a name) (n text))
    (trace (send (enc n (pubk a)))
      (recv
        (cat (enc n (enc n (enc n (pubk a)) (pubk a)) (pubk a))
          (enc n (enc n (pubk a)) (pubk a)))))
    (non-orig (privk a))
    (uniq-orig n))
  (defrole trans
    (vars (a name) (n text) (m mesg))
    (trace (recv (enc n (pubk a))) (recv m) (send (enc n m (pubk a)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton targetterms6
  (vars (n text) (a name))
  (defstrand init 2 (n n) (a a))
  (non-orig (privk a))
  (uniq-orig n)
  (traces
    ((send (enc n (pubk a)))
      (recv
        (cat (enc n (enc n (enc n (pubk a)) (pubk a)) (pubk a))
          (enc n (enc n (pubk a)) (pubk a))))))
  (label 0)
  (unrealized (0 1))
  (origs (n (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton targetterms6
  (vars (m mesg) (n text) (a name))
  (defstrand init 2 (n n) (a a))
  (defstrand trans 3 (m m) (n n) (a a))
  (precedes ((0 0) (1 0)) ((1 2) (0 1)))
  (non-orig (privk a))
  (uniq-orig n)
  (operation nonce-test (added-strand trans 3) n (0 1) (enc n (pubk a)))
  (traces
    ((send (enc n (pubk a)))
      (recv
        (cat (enc n (enc n (enc n (pubk a)) (pubk a)) (pubk a))
          (enc n (enc n (pubk a)) (pubk a)))))
    ((recv (enc n (pubk a))) (recv m) (send (enc n m (pubk a)))))
  (label 1)
  (parent 0)
  (unrealized (0 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton targetterms6
  (vars (n text) (a name))
  (defstrand init 2 (n n) (a a))
  (defstrand trans 3 (m (enc n (pubk a))) (n n) (a a))
  (precedes ((0 0) (1 0)) ((1 2) (0 1)))
  (non-orig (privk a))
  (uniq-orig n)
  (operation nonce-test (contracted (m (enc n (pubk a)))) n (0 1)
    (enc n (pubk a)) (enc n (enc n (pubk a)) (pubk a)))
  (traces
    ((send (enc n (pubk a)))
      (recv
        (cat (enc n (enc n (enc n (pubk a)) (pubk a)) (pubk a))
          (enc n (enc n (pubk a)) (pubk a)))))
    ((recv (enc n (pubk a))) (recv (enc n (pubk a)))
      (send (enc n (enc n (pubk a)) (pubk a)))))
  (label 2)
  (parent 1)
  (unrealized (0 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton targetterms6
  (vars (m mesg) (n text) (a name))
  (defstrand init 2 (n n) (a a))
  (defstrand trans 3 (m (enc n (pubk a))) (n n) (a a))
  (defstrand trans 3 (m m) (n n) (a a))
  (precedes ((0 0) (1 0)) ((0 0) (2 0)) ((1 2) (0 1)) ((2 2) (0 1)))
  (non-orig (privk a))
  (uniq-orig n)
  (operation nonce-test (added-strand trans 3) n (0 1) (enc n (pubk a))
    (enc n (enc n (pubk a)) (pubk a)))
  (traces
    ((send (enc n (pubk a)))
      (recv
        (cat (enc n (enc n (enc n (pubk a)) (pubk a)) (pubk a))
          (enc n (enc n (pubk a)) (pubk a)))))
    ((recv (enc n (pubk a))) (recv (enc n (pubk a)))
      (send (enc n (enc n (pubk a)) (pubk a))))
    ((recv (enc n (pubk a))) (recv m) (send (enc n m (pubk a)))))
  (label 3)
  (parent 2)
  (unrealized (0 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton targetterms6
  (vars (n text) (a name))
  (defstrand init 2 (n n) (a a))
  (defstrand trans 3 (m (enc n (pubk a))) (n n) (a a))
  (defstrand trans 3 (m (enc n (enc n (pubk a)) (pubk a))) (n n) (a a))
  (precedes ((0 0) (1 0)) ((0 0) (2 0)) ((1 2) (0 1)) ((2 2) (0 1)))
  (non-orig (privk a))
  (uniq-orig n)
  (operation nonce-test
    (contracted (m (enc n (enc n (pubk a)) (pubk a)))) n (0 1)
    (enc n (pubk a)) (enc n (enc n (pubk a)) (pubk a))
    (enc n (enc n (enc n (pubk a)) (pubk a)) (pubk a)))
  (traces
    ((send (enc n (pubk a)))
      (recv
        (cat (enc n (enc n (enc n (pubk a)) (pubk a)) (pubk a))
          (enc n (enc n (pubk a)) (pubk a)))))
    ((recv (enc n (pubk a))) (recv (enc n (pubk a)))
      (send (enc n (enc n (pubk a)) (pubk a))))
    ((recv (enc n (pubk a))) (recv (enc n (enc n (pubk a)) (pubk a)))
      (send (enc n (enc n (enc n (pubk a)) (pubk a)) (pubk a)))))
  (label 4)
  (parent 3)
  (unrealized (2 1))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton targetterms6
  (vars (n text) (a name))
  (defstrand init 2 (n n) (a a))
  (defstrand trans 3 (m (enc n (pubk a))) (n n) (a a))
  (defstrand trans 3 (m (enc n (enc n (pubk a)) (pubk a))) (n n) (a a))
  (precedes ((0 0) (1 0)) ((0 0) (2 0)) ((1 2) (2 1)) ((2 2) (0 1)))
  (non-orig (privk a))
  (uniq-orig n)
  (operation nonce-test (displaced 3 1 trans 3) n (2 1)
    (enc n (pubk a)))
  (traces
    ((send (enc n (pubk a)))
      (recv
        (cat (enc n (enc n (enc n (pubk a)) (pubk a)) (pubk a))
          (enc n (enc n (pubk a)) (pubk a)))))
    ((recv (enc n (pubk a))) (recv (enc n (pubk a)))
      (send (enc n (enc n (pubk a)) (pubk a))))
    ((recv (enc n (pubk a))) (recv (enc n (enc n (pubk a)) (pubk a)))
      (send (enc n (enc n (enc n (pubk a)) (pubk a)) (pubk a)))))
  (label 5)
  (parent 4)
  (realized)
  (shape)
  (maps ((0) ((a a) (n n))))
  (origs (n (0 0))))

(defskeleton targetterms6
  (vars (m mesg) (n text) (a name))
  (defstrand init 2 (n n) (a a))
  (defstrand trans 3 (m (enc n (pubk a))) (n n) (a a))
  (defstrand trans 3 (m (enc n (enc n (pubk a)) (pubk a))) (n n) (a a))
  (defstrand trans 3 (m m) (n n) (a a))
  (precedes ((0 0) (1 0)) ((0 0) (2 0)) ((0 0) (3 0)) ((1 2) (0 1))
    ((2 2) (0 1)) ((3 2) (2 1)))
  (non-orig (privk a))
  (uniq-orig n)
  (operation nonce-test (added-strand trans 3) n (2 1) (enc n (pubk a)))
  (traces
    ((send (enc n (pubk a)))
      (recv
        (cat (enc n (enc n (enc n (pubk a)) (pubk a)) (pubk a))
          (enc n (enc n (pubk a)) (pubk a)))))
    ((recv (enc n (pubk a))) (recv (enc n (pubk a)))
      (send (enc n (enc n (pubk a)) (pubk a))))
    ((recv (enc n (pubk a))) (recv (enc n (enc n (pubk a)) (pubk a)))
      (send (enc n (enc n (enc n (pubk a)) (pubk a)) (pubk a))))
    ((recv (enc n (pubk a))) (recv m) (send (enc n m (pubk a)))))
  (label 6)
  (parent 4)
  (unrealized (2 1))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton targetterms6
  (vars (n text) (a name))
  (defstrand init 2 (n n) (a a))
  (defstrand trans 3 (m (enc n (pubk a))) (n n) (a a))
  (defstrand trans 3 (m (enc n (enc n (pubk a)) (pubk a))) (n n) (a a))
  (defstrand trans 3 (m (enc n (pubk a))) (n n) (a a))
  (precedes ((0 0) (1 0)) ((0 0) (2 0)) ((0 0) (3 0)) ((1 2) (0 1))
    ((2 2) (0 1)) ((3 2) (2 1)))
  (non-orig (privk a))
  (uniq-orig n)
  (operation nonce-test (contracted (m (enc n (pubk a)))) n (2 1)
    (enc n (pubk a)) (enc n (enc n (pubk a)) (pubk a)))
  (traces
    ((send (enc n (pubk a)))
      (recv
        (cat (enc n (enc n (enc n (pubk a)) (pubk a)) (pubk a))
          (enc n (enc n (pubk a)) (pubk a)))))
    ((recv (enc n (pubk a))) (recv (enc n (pubk a)))
      (send (enc n (enc n (pubk a)) (pubk a))))
    ((recv (enc n (pubk a))) (recv (enc n (enc n (pubk a)) (pubk a)))
      (send (enc n (enc n (enc n (pubk a)) (pubk a)) (pubk a))))
    ((recv (enc n (pubk a))) (recv (enc n (pubk a)))
      (send (enc n (enc n (pubk a)) (pubk a)))))
  (label 7)
  (parent 6)
  (seen 5)
  (seen-ops (5 (operation generalization deleted (1 0))))
  (realized)
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton targetterms6
  (vars (m mesg) (n text) (a name))
  (defstrand init 2 (n n) (a a))
  (defstrand trans 3 (m (enc n (pubk a))) (n n) (a a))
  (defstrand trans 3 (m (enc n (enc n (pubk a)) (pubk a))) (n n) (a a))
  (defstrand trans 3 (m m) (n n) (a a))
  (precedes ((0 0) (1 0)) ((0 0) (2 0)) ((0 0) (3 0)) ((1 2) (2 1))
    ((2 2) (0 1)) ((3 2) (2 1)))
  (non-orig (privk a))
  (uniq-orig n)
  (operation nonce-test (displaced 4 1 trans 3) n (2 1) (enc n (pubk a))
    (enc n m (pubk a)))
  (traces
    ((send (enc n (pubk a)))
      (recv
        (cat (enc n (enc n (enc n (pubk a)) (pubk a)) (pubk a))
          (enc n (enc n (pubk a)) (pubk a)))))
    ((recv (enc n (pubk a))) (recv (enc n (pubk a)))
      (send (enc n (enc n (pubk a)) (pubk a))))
    ((recv (enc n (pubk a))) (recv (enc n (enc n (pubk a)) (pubk a)))
      (send (enc n (enc n (enc n (pubk a)) (pubk a)) (pubk a))))
    ((recv (enc n (pubk a))) (recv m) (send (enc n m (pubk a)))))
  (label 8)
  (parent 6)
  (seen 5)
  (seen-ops (5 (operation generalization deleted (3 0))))
  (realized)
  (comment "1 in cohort - 0 not yet seen"))

(comment "Nothing left to do")

(defprotocol targetterms6 basic
  (defrole init
    (vars (a name) (n text))
    (trace (send (enc n (pubk a)))
      (recv
        (cat (enc n (enc n (enc n (pubk a)) (pubk a)) (pubk a))
          (enc n (enc n (pubk a)) (pubk a)))))
    (non-orig (privk a))
    (uniq-orig n))
  (defrole trans
    (vars (a name) (n text) (m mesg))
    (trace (recv (enc n (pubk a))) (recv m) (send (enc n m (pubk a)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton targetterms6
  (vars (n text) (a name))
  (defstrand init 2 (n n) (a a))
  (defstrand trans 3 (m (enc n (pubk a))) (n n) (a a))
  (defstrand trans 3 (m (enc n (enc n (pubk a)) (pubk a))) (n n) (a a))
  (precedes ((0 0) (1 0)) ((0 0) (2 0)) ((1 2) (2 1)) ((2 2) (0 1)))
  (non-orig (privk a))
  (uniq-orig n)
  (traces
    ((send (enc n (pubk a)))
      (recv
        (cat (enc n (enc n (enc n (pubk a)) (pubk a)) (pubk a))
          (enc n (enc n (pubk a)) (pubk a)))))
    ((recv (enc n (pubk a))) (recv (enc n (pubk a)))
      (send (enc n (enc n (pubk a)) (pubk a))))
    ((recv (enc n (pubk a))) (recv (enc n (enc n (pubk a)) (pubk a)))
      (send (enc n (enc n (enc n (pubk a)) (pubk a)) (pubk a)))))
  (label 9)
  (realized)
  (shape)
  (maps ((0 1 2) ((n n) (a a))))
  (origs (n (0 0))))

(comment "Nothing left to do")
