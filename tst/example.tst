(herald example)

(comment "CPSA 4.4.2")
(comment "All input read from tst/example.scm")

(defprotocol version-1 basic
  (defrole init
    (vars (a b name) (m text) (s skey))
    (trace (send (enc s (ltk a b))) (recv (enc m a s))))
  (defrole resp
    (vars (a b name) (m text) (s skey))
    (trace (recv (enc s (ltk a b))) (send (enc m a s))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton version-1
  (vars (s skey) (m text) (a b name))
  (defstrand init 2 (s s) (m m) (a a) (b b))
  (non-orig (ltk a b))
  (uniq-orig s)
  (traces ((send (enc s (ltk a b))) (recv (enc m a s))))
  (label 0)
  (unrealized (0 1))
  (origs (s (0 0)))
  (ugens)
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton version-1
  (vars (s skey) (m text) (a b b-0 name))
  (defstrand init 2 (s s) (m m) (a a) (b b))
  (defstrand resp 2 (s s) (m m) (a a) (b b-0))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (ltk a b))
  (uniq-orig s)
  (operation encryption-test (added-strand resp 2) (enc m a s) (0 1))
  (traces ((send (enc s (ltk a b))) (recv (enc m a s)))
    ((recv (enc s (ltk a b-0))) (send (enc m a s))))
  (label 1)
  (parent 0)
  (unrealized (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton version-1
  (vars (s skey) (m text) (a b name))
  (defstrand init 2 (s s) (m m) (a a) (b b))
  (deflistener s)
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (ltk a b))
  (uniq-orig s)
  (operation encryption-test (added-listener s) (enc m a s) (0 1))
  (traces ((send (enc s (ltk a b))) (recv (enc m a s)))
    ((recv s) (send s)))
  (label 2)
  (parent 0)
  (unrealized (1 0))
  (dead)
  (comment "empty cohort"))

(defskeleton version-1
  (vars (s skey) (m text) (a b name))
  (defstrand init 2 (s s) (m m) (a a) (b b))
  (defstrand resp 2 (s s) (m m) (a a) (b b))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (ltk a b))
  (uniq-orig s)
  (operation nonce-test (contracted (b-0 b)) s (1 0) (enc s (ltk a b)))
  (traces ((send (enc s (ltk a b))) (recv (enc m a s)))
    ((recv (enc s (ltk a b))) (send (enc m a s))))
  (label 3)
  (parent 1)
  (realized)
  (shape)
  (maps ((0) ((a a) (b b) (m m) (s s))))
  (origs (s (0 0)))
  (ugens))

(comment "Nothing left to do")

(defprotocol version-1 basic
  (defrole init
    (vars (a b name) (m text) (s skey))
    (trace (send (enc s (ltk a b))) (recv (enc m a s))))
  (defrole resp
    (vars (a b name) (m text) (s skey))
    (trace (recv (enc s (ltk a b))) (send (enc m a s))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton version-1
  (vars (s skey) (m text) (a b name))
  (defstrand resp 2 (s s) (m m) (a a) (b b))
  (non-orig (ltk a b))
  (traces ((recv (enc s (ltk a b))) (send (enc m a s))))
  (label 4)
  (unrealized (0 0))
  (origs)
  (ugens)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton version-1
  (vars (s skey) (m text) (a b name))
  (defstrand resp 2 (s s) (m m) (a a) (b b))
  (defstrand init 1 (s s) (a a) (b b))
  (precedes ((1 0) (0 0)))
  (non-orig (ltk a b))
  (operation encryption-test (added-strand init 1) (enc s (ltk a b))
    (0 0))
  (traces ((recv (enc s (ltk a b))) (send (enc m a s)))
    ((send (enc s (ltk a b)))))
  (label 5)
  (parent 4)
  (realized)
  (shape)
  (maps ((0) ((a a) (b b) (m m) (s s))))
  (origs)
  (ugens))

(comment "Nothing left to do")

(defprotocol version-1 basic
  (defrole init
    (vars (a b name) (m text) (s skey))
    (trace (send (enc s (ltk a b))) (recv (enc m a s))))
  (defrole resp
    (vars (a b name) (m text) (s skey))
    (trace (recv (enc s (ltk a b))) (send (enc m a s))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton version-1
  (vars (s skey) (m text) (a b name))
  (defstrand resp 2 (s s) (m m) (a a) (b b))
  (defstrand init 1 (s s) (a a) (b b))
  (deflistener m)
  (precedes ((1 0) (0 0)))
  (non-orig (ltk a b))
  (uniq-orig s m)
  (traces ((recv (enc s (ltk a b))) (send (enc m a s)))
    ((send (enc s (ltk a b)))) ((recv m) (send m)))
  (label 6)
  (unrealized (2 0))
  (preskeleton)
  (origs (m (0 1)) (s (1 0)))
  (ugens)
  (comment "Not a skeleton"))

(defskeleton version-1
  (vars (s skey) (m text) (a b name))
  (defstrand resp 2 (s s) (m m) (a a) (b b))
  (defstrand init 1 (s s) (a a) (b b))
  (deflistener m)
  (precedes ((0 1) (2 0)) ((1 0) (0 0)))
  (non-orig (ltk a b))
  (uniq-orig s m)
  (traces ((recv (enc s (ltk a b))) (send (enc m a s)))
    ((send (enc s (ltk a b)))) ((recv m) (send m)))
  (label 7)
  (parent 6)
  (unrealized (2 0))
  (origs (m (0 1)) (s (1 0)))
  (ugens)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton version-1
  (vars (s skey) (m text) (a b name))
  (defstrand resp 2 (s s) (m m) (a a) (b b))
  (defstrand init 1 (s s) (a a) (b b))
  (deflistener m)
  (deflistener s)
  (precedes ((0 1) (2 0)) ((1 0) (0 0)) ((1 0) (3 0)) ((3 1) (2 0)))
  (non-orig (ltk a b))
  (uniq-orig s m)
  (operation nonce-test (added-listener s) m (2 0) (enc m a s))
  (traces ((recv (enc s (ltk a b))) (send (enc m a s)))
    ((send (enc s (ltk a b)))) ((recv m) (send m)) ((recv s) (send s)))
  (label 8)
  (parent 7)
  (unrealized (3 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol version-1 basic
  (defrole init
    (vars (a b name) (m text) (s skey))
    (trace (send (enc s (ltk a b))) (recv (enc m a s))))
  (defrole resp
    (vars (a b name) (m text) (s skey))
    (trace (recv (enc s (ltk a b))) (send (enc m a s))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton version-1
  (vars (s skey) (m text) (a b name))
  (defstrand resp 2 (s s) (m m) (a a) (b b))
  (defstrand init 1 (s s) (a a) (b b))
  (deflistener m)
  (precedes ((1 0) (0 0)))
  (non-orig (ltk a b))
  (uniq-orig m)
  (traces ((recv (enc s (ltk a b))) (send (enc m a s)))
    ((send (enc s (ltk a b)))) ((recv m) (send m)))
  (label 9)
  (unrealized (2 0))
  (preskeleton)
  (origs (m (0 1)))
  (ugens)
  (comment "Not a skeleton"))

(defskeleton version-1
  (vars (s skey) (m text) (a b name))
  (defstrand resp 2 (s s) (m m) (a a) (b b))
  (defstrand init 1 (s s) (a a) (b b))
  (deflistener m)
  (precedes ((0 1) (2 0)) ((1 0) (0 0)))
  (non-orig (ltk a b))
  (uniq-orig m)
  (traces ((recv (enc s (ltk a b))) (send (enc m a s)))
    ((send (enc s (ltk a b)))) ((recv m) (send m)))
  (label 10)
  (parent 9)
  (realized)
  (shape)
  (maps ((0 1 2) ((m m) (a a) (b b) (s s))))
  (origs (m (0 1)))
  (ugens))

(comment "Nothing left to do")

(defprotocol version-2 basic
  (defrole init
    (vars (a b name) (m n1 text) (s skey))
    (trace (send (enc s n1 (ltk a b))) (recv (enc m a n1 s))))
  (defrole resp
    (vars (a b name) (m n1 text) (s skey))
    (trace (recv (enc s n1 (ltk a b))) (send (enc m a n1 s))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton version-2
  (vars (s skey) (m n1 text) (a b name))
  (defstrand init 2 (s s) (m m) (n1 n1) (a a) (b b))
  (non-orig (ltk a b))
  (uniq-orig s)
  (traces ((send (enc s n1 (ltk a b))) (recv (enc m a n1 s))))
  (label 11)
  (unrealized (0 1))
  (origs (s (0 0)))
  (ugens)
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton version-2
  (vars (s skey) (m n1 text) (a b b-0 name))
  (defstrand init 2 (s s) (m m) (n1 n1) (a a) (b b))
  (defstrand resp 2 (s s) (m m) (n1 n1) (a a) (b b-0))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (ltk a b))
  (uniq-orig s)
  (operation encryption-test (added-strand resp 2) (enc m a n1 s) (0 1))
  (traces ((send (enc s n1 (ltk a b))) (recv (enc m a n1 s)))
    ((recv (enc s n1 (ltk a b-0))) (send (enc m a n1 s))))
  (label 12)
  (parent 11)
  (unrealized (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton version-2
  (vars (s skey) (m n1 text) (a b name))
  (defstrand init 2 (s s) (m m) (n1 n1) (a a) (b b))
  (deflistener s)
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (ltk a b))
  (uniq-orig s)
  (operation encryption-test (added-listener s) (enc m a n1 s) (0 1))
  (traces ((send (enc s n1 (ltk a b))) (recv (enc m a n1 s)))
    ((recv s) (send s)))
  (label 13)
  (parent 11)
  (unrealized (1 0))
  (dead)
  (comment "empty cohort"))

(defskeleton version-2
  (vars (s skey) (m n1 text) (a b name))
  (defstrand init 2 (s s) (m m) (n1 n1) (a a) (b b))
  (defstrand resp 2 (s s) (m m) (n1 n1) (a a) (b b))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (ltk a b))
  (uniq-orig s)
  (operation nonce-test (contracted (b-0 b)) s (1 0)
    (enc s n1 (ltk a b)))
  (traces ((send (enc s n1 (ltk a b))) (recv (enc m a n1 s)))
    ((recv (enc s n1 (ltk a b))) (send (enc m a n1 s))))
  (label 14)
  (parent 12)
  (realized)
  (shape)
  (maps ((0) ((a a) (b b) (m m) (s s) (n1 n1))))
  (origs (s (0 0)))
  (ugens))

(comment "Nothing left to do")

(defprotocol version-2 basic
  (defrole init
    (vars (a b name) (m n1 text) (s skey))
    (trace (send (enc s n1 (ltk a b))) (recv (enc m a n1 s))))
  (defrole resp
    (vars (a b name) (m n1 text) (s skey))
    (trace (recv (enc s n1 (ltk a b))) (send (enc m a n1 s))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton version-2
  (vars (s skey) (m n1 text) (a b name))
  (defstrand resp 2 (s s) (m m) (n1 n1) (a a) (b b))
  (non-orig (ltk a b))
  (uniq-orig n1)
  (traces ((recv (enc s n1 (ltk a b))) (send (enc m a n1 s))))
  (label 15)
  (unrealized (0 0))
  (origs)
  (ugens)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton version-2
  (vars (s skey) (m n1 text) (a b name))
  (defstrand resp 2 (s s) (m m) (n1 n1) (a a) (b b))
  (defstrand init 1 (s s) (n1 n1) (a a) (b b))
  (precedes ((1 0) (0 0)))
  (non-orig (ltk a b))
  (uniq-orig n1)
  (operation encryption-test (added-strand init 1) (enc s n1 (ltk a b))
    (0 0))
  (traces ((recv (enc s n1 (ltk a b))) (send (enc m a n1 s)))
    ((send (enc s n1 (ltk a b)))))
  (label 16)
  (parent 15)
  (realized)
  (shape)
  (maps ((0) ((a a) (b b) (m m) (n1 n1) (s s))))
  (origs (n1 (1 0)))
  (ugens))

(comment "Nothing left to do")
