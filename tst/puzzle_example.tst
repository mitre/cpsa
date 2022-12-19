(herald puzzle_example)

(comment "CPSA 4.4.1")
(comment "All input read from tst/puzzle_example.scm")

(defprotocol puzzle basic
  (defrole init
    (vars (a b name) (na payload text) (s skey))
    (trace (send na) (recv (enc na s (ltk a b)))
      (send (enc payload s))))
  (defrole resp
    (vars (a b name) (na payload text) (s skey))
    (trace (recv na) (send (enc na s (ltk a b)))
      (recv (enc payload s))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton puzzle
  (vars (s skey) (na payload text) (a b name))
  (defstrand init 3 (s s) (na na) (payload payload) (a a) (b b))
  (non-orig (ltk a b))
  (uniq-orig na payload)
  (traces
    ((send na) (recv (enc na s (ltk a b))) (send (enc payload s))))
  (label 0)
  (unrealized (0 1))
  (origs (na (0 0)) (payload (0 2)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton puzzle
  (vars (s skey) (na payload text) (a b name))
  (defstrand init 3 (s s) (na na) (payload payload) (a a) (b b))
  (defstrand resp 2 (s s) (na na) (a a) (b b))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (ltk a b))
  (uniq-orig na payload)
  (operation encryption-test (added-strand resp 2) (enc na s (ltk a b))
    (0 1))
  (traces ((send na) (recv (enc na s (ltk a b))) (send (enc payload s)))
    ((recv na) (send (enc na s (ltk a b)))))
  (label 1)
  (parent 0)
  (realized)
  (shape)
  (maps ((0) ((a a) (b b) (na na) (payload payload) (s s))))
  (origs (na (0 0)) (payload (0 2))))

(comment "Nothing left to do")

(defprotocol puzzle basic
  (defrole init
    (vars (a b name) (na payload text) (s skey))
    (trace (send na) (recv (enc na s (ltk a b)))
      (send (enc payload s))))
  (defrole resp
    (vars (a b name) (na payload text) (s skey))
    (trace (recv na) (send (enc na s (ltk a b)))
      (recv (enc payload s))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton puzzle
  (vars (s skey) (na payload text) (a b name))
  (defstrand init 3 (s s) (na na) (payload payload) (a a) (b b))
  (deflistener payload)
  (non-orig (ltk a b))
  (uniq-orig na payload)
  (traces ((send na) (recv (enc na s (ltk a b))) (send (enc payload s)))
    ((recv payload) (send payload)))
  (label 2)
  (unrealized (0 1) (1 0))
  (preskeleton)
  (origs (na (0 0)) (payload (0 2)))
  (comment "Not a skeleton"))

(defskeleton puzzle
  (vars (s skey) (na payload text) (a b name))
  (defstrand init 3 (s s) (na na) (payload payload) (a a) (b b))
  (deflistener payload)
  (precedes ((0 2) (1 0)))
  (non-orig (ltk a b))
  (uniq-orig na payload)
  (traces ((send na) (recv (enc na s (ltk a b))) (send (enc payload s)))
    ((recv payload) (send payload)))
  (label 3)
  (parent 2)
  (unrealized (0 1))
  (origs (na (0 0)) (payload (0 2)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton puzzle
  (vars (s skey) (na payload text) (a b name))
  (defstrand init 3 (s s) (na na) (payload payload) (a a) (b b))
  (deflistener payload)
  (defstrand resp 2 (s s) (na na) (a a) (b b))
  (precedes ((0 0) (2 0)) ((0 2) (1 0)) ((2 1) (0 1)))
  (non-orig (ltk a b))
  (uniq-orig na payload)
  (operation encryption-test (added-strand resp 2) (enc na s (ltk a b))
    (0 1))
  (traces ((send na) (recv (enc na s (ltk a b))) (send (enc payload s)))
    ((recv payload) (send payload))
    ((recv na) (send (enc na s (ltk a b)))))
  (label 4)
  (parent 3)
  (realized)
  (shape)
  (maps ((0 1) ((a a) (b b) (na na) (payload payload) (s s))))
  (origs (na (0 0)) (payload (0 2))))

(comment "Nothing left to do")

(defprotocol puzzle basic
  (defrole init
    (vars (a b name) (na payload text) (s skey))
    (trace (send na) (recv (enc na s (ltk a b)))
      (send (enc payload s))))
  (defrole resp
    (vars (a b name) (na payload text) (s skey))
    (trace (recv na) (send (enc na s (ltk a b)))
      (recv (enc payload s))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton puzzle
  (vars (s skey) (na payload text) (a b name))
  (defstrand init 3 (s s) (na na) (payload payload) (a a) (b b))
  (defstrand resp 2 (s s) (na na) (a a) (b b))
  (deflistener s)
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (ltk a b))
  (uniq-orig s na payload)
  (traces ((send na) (recv (enc na s (ltk a b))) (send (enc payload s)))
    ((recv na) (send (enc na s (ltk a b)))) ((recv s) (send s)))
  (label 5)
  (unrealized (2 0))
  (preskeleton)
  (origs (s (1 1)) (na (0 0)) (payload (0 2)))
  (comment "Not a skeleton"))

(defskeleton puzzle
  (vars (s skey) (na payload text) (a b name))
  (defstrand init 3 (s s) (na na) (payload payload) (a a) (b b))
  (defstrand resp 2 (s s) (na na) (a a) (b b))
  (deflistener s)
  (precedes ((0 0) (1 0)) ((1 1) (0 1)) ((1 1) (2 0)))
  (non-orig (ltk a b))
  (uniq-orig s na payload)
  (traces ((send na) (recv (enc na s (ltk a b))) (send (enc payload s)))
    ((recv na) (send (enc na s (ltk a b)))) ((recv s) (send s)))
  (label 6)
  (parent 5)
  (unrealized (2 0))
  (dead)
  (origs (s (1 1)) (na (0 0)) (payload (0 2)))
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol puzzle basic
  (defrole init
    (vars (a b name) (na payload text) (s skey))
    (trace (send na) (recv (enc na s (ltk a b)))
      (send (enc payload s))))
  (defrole resp
    (vars (a b name) (na payload text) (s skey))
    (trace (recv na) (send (enc na s (ltk a b)))
      (recv (enc payload s))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton puzzle
  (vars (s skey) (na payload text) (a b name))
  (defstrand init 3 (s s) (na na) (payload payload) (a a) (b b))
  (defstrand resp 2 (s s) (na na) (a a) (b b))
  (deflistener payload)
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (ltk a b))
  (uniq-orig s na payload)
  (traces ((send na) (recv (enc na s (ltk a b))) (send (enc payload s)))
    ((recv na) (send (enc na s (ltk a b))))
    ((recv payload) (send payload)))
  (label 7)
  (unrealized (2 0))
  (preskeleton)
  (origs (s (1 1)) (na (0 0)) (payload (0 2)))
  (comment "Not a skeleton"))

(defskeleton puzzle
  (vars (s skey) (na payload text) (a b name))
  (defstrand init 3 (s s) (na na) (payload payload) (a a) (b b))
  (defstrand resp 2 (s s) (na na) (a a) (b b))
  (deflistener payload)
  (precedes ((0 0) (1 0)) ((0 2) (2 0)) ((1 1) (0 1)))
  (non-orig (ltk a b))
  (uniq-orig s na payload)
  (traces ((send na) (recv (enc na s (ltk a b))) (send (enc payload s)))
    ((recv na) (send (enc na s (ltk a b))))
    ((recv payload) (send payload)))
  (label 8)
  (parent 7)
  (unrealized (2 0))
  (origs (s (1 1)) (na (0 0)) (payload (0 2)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton puzzle
  (vars (s skey) (na payload text) (a b name))
  (defstrand init 3 (s s) (na na) (payload payload) (a a) (b b))
  (defstrand resp 2 (s s) (na na) (a a) (b b))
  (deflistener payload)
  (deflistener s)
  (precedes ((0 0) (1 0)) ((0 2) (2 0)) ((1 1) (0 1)) ((1 1) (3 0))
    ((3 1) (2 0)))
  (non-orig (ltk a b))
  (uniq-orig s na payload)
  (operation nonce-test (added-listener s) payload (2 0)
    (enc payload s))
  (traces ((send na) (recv (enc na s (ltk a b))) (send (enc payload s)))
    ((recv na) (send (enc na s (ltk a b))))
    ((recv payload) (send payload)) ((recv s) (send s)))
  (label 9)
  (parent 8)
  (unrealized (3 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol puzzle basic
  (defrole init
    (vars (a b name) (na payload text) (s skey))
    (trace (send na) (recv (enc na s (ltk a b)))
      (send (enc payload s))))
  (defrole resp
    (vars (a b name) (na payload text) (s skey))
    (trace (recv na) (send (enc na s (ltk a b)))
      (recv (enc payload s))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton puzzle
  (vars (s skey) (payload na text) (a b name))
  (defstrand resp 3 (s s) (na na) (payload payload) (a a) (b b))
  (non-orig (ltk a b))
  (uniq-orig s)
  (traces
    ((recv na) (send (enc na s (ltk a b))) (recv (enc payload s))))
  (label 10)
  (unrealized (0 2))
  (origs (s (0 1)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton puzzle
  (vars (s skey) (payload na na-0 text) (a b a-0 b-0 name))
  (defstrand resp 3 (s s) (na na) (payload payload) (a a) (b b))
  (defstrand init 3 (s s) (na na-0) (payload payload) (a a-0) (b b-0))
  (precedes ((0 1) (1 1)) ((1 2) (0 2)))
  (non-orig (ltk a b))
  (uniq-orig s)
  (operation encryption-test (added-strand init 3) (enc payload s)
    (0 2))
  (traces ((recv na) (send (enc na s (ltk a b))) (recv (enc payload s)))
    ((send na-0) (recv (enc na-0 s (ltk a-0 b-0)))
      (send (enc payload s))))
  (label 11)
  (parent 10)
  (unrealized (1 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton puzzle
  (vars (s skey) (payload na text) (a b name))
  (defstrand resp 3 (s s) (na na) (payload payload) (a a) (b b))
  (deflistener s)
  (precedes ((0 1) (1 0)) ((1 1) (0 2)))
  (non-orig (ltk a b))
  (uniq-orig s)
  (operation encryption-test (added-listener s) (enc payload s) (0 2))
  (traces ((recv na) (send (enc na s (ltk a b))) (recv (enc payload s)))
    ((recv s) (send s)))
  (label 12)
  (parent 10)
  (unrealized (1 0))
  (dead)
  (comment "empty cohort"))

(defskeleton puzzle
  (vars (s skey) (payload na text) (a b name))
  (defstrand resp 3 (s s) (na na) (payload payload) (a a) (b b))
  (defstrand init 3 (s s) (na na) (payload payload) (a a) (b b))
  (precedes ((0 1) (1 1)) ((1 2) (0 2)))
  (non-orig (ltk a b))
  (uniq-orig s)
  (operation nonce-test (contracted (a-0 a) (b-0 b) (na-0 na)) s (1 1)
    (enc na s (ltk a b)))
  (traces ((recv na) (send (enc na s (ltk a b))) (recv (enc payload s)))
    ((send na) (recv (enc na s (ltk a b))) (send (enc payload s))))
  (label 13)
  (parent 11)
  (realized)
  (shape)
  (maps ((0) ((a a) (b b) (payload payload) (s s) (na na))))
  (origs (s (0 1))))

(comment "Nothing left to do")

(defprotocol puzzle basic
  (defrole init
    (vars (a b name) (na payload text) (s skey))
    (trace (send na) (recv (enc na s (ltk a b)))
      (send (enc payload s))))
  (defrole resp
    (vars (a b name) (na payload text) (s skey))
    (trace (recv na) (send (enc na s (ltk a b)))
      (recv (enc payload s))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton puzzle
  (vars (s skey) (payload na text) (a b name))
  (defstrand resp 3 (s s) (na na) (payload payload) (a a) (b b))
  (deflistener s)
  (non-orig (ltk a b))
  (uniq-orig s)
  (traces ((recv na) (send (enc na s (ltk a b))) (recv (enc payload s)))
    ((recv s) (send s)))
  (label 14)
  (unrealized (0 2) (1 0))
  (preskeleton)
  (origs (s (0 1)))
  (comment "Not a skeleton"))

(defskeleton puzzle
  (vars (s skey) (payload na text) (a b name))
  (defstrand resp 3 (s s) (na na) (payload payload) (a a) (b b))
  (deflistener s)
  (precedes ((0 1) (1 0)))
  (non-orig (ltk a b))
  (uniq-orig s)
  (traces ((recv na) (send (enc na s (ltk a b))) (recv (enc payload s)))
    ((recv s) (send s)))
  (label 15)
  (parent 14)
  (unrealized (0 2) (1 0))
  (dead)
  (origs (s (0 1)))
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol puzzle basic
  (defrole init
    (vars (a b name) (na payload text) (s skey))
    (trace (send na) (recv (enc na s (ltk a b)))
      (send (enc payload s))))
  (defrole resp
    (vars (a b name) (na payload text) (s skey))
    (trace (recv na) (send (enc na s (ltk a b)))
      (recv (enc payload s))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton puzzle
  (vars (s skey) (payload na text) (a b name))
  (defstrand resp 3 (s s) (na na) (payload payload) (a a) (b b))
  (defstrand init 3 (s s) (na na) (payload payload) (a a) (b b))
  (deflistener payload)
  (precedes ((0 1) (1 1)) ((1 2) (0 2)))
  (non-orig (ltk a b))
  (uniq-orig s payload)
  (traces ((recv na) (send (enc na s (ltk a b))) (recv (enc payload s)))
    ((send na) (recv (enc na s (ltk a b))) (send (enc payload s)))
    ((recv payload) (send payload)))
  (label 16)
  (unrealized (2 0))
  (preskeleton)
  (origs (s (0 1)) (payload (1 2)))
  (comment "Not a skeleton"))

(defskeleton puzzle
  (vars (s skey) (payload na text) (a b name))
  (defstrand resp 3 (s s) (na na) (payload payload) (a a) (b b))
  (defstrand init 3 (s s) (na na) (payload payload) (a a) (b b))
  (deflistener payload)
  (precedes ((0 1) (1 1)) ((1 2) (0 2)) ((1 2) (2 0)))
  (non-orig (ltk a b))
  (uniq-orig s payload)
  (traces ((recv na) (send (enc na s (ltk a b))) (recv (enc payload s)))
    ((send na) (recv (enc na s (ltk a b))) (send (enc payload s)))
    ((recv payload) (send payload)))
  (label 17)
  (parent 16)
  (unrealized (2 0))
  (origs (s (0 1)) (payload (1 2)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton puzzle
  (vars (s skey) (payload na text) (a b name))
  (defstrand resp 3 (s s) (na na) (payload payload) (a a) (b b))
  (defstrand init 3 (s s) (na na) (payload payload) (a a) (b b))
  (deflistener payload)
  (deflistener s)
  (precedes ((0 1) (1 1)) ((0 1) (3 0)) ((1 2) (0 2)) ((1 2) (2 0))
    ((3 1) (2 0)))
  (non-orig (ltk a b))
  (uniq-orig s payload)
  (operation nonce-test (added-listener s) payload (2 0)
    (enc payload s))
  (traces ((recv na) (send (enc na s (ltk a b))) (recv (enc payload s)))
    ((send na) (recv (enc na s (ltk a b))) (send (enc payload s)))
    ((recv payload) (send payload)) ((recv s) (send s)))
  (label 18)
  (parent 17)
  (unrealized (3 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")
