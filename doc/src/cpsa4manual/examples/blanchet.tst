(herald "Blanchet's Simple Example Protocol"
  (comment "There is a flaw in this protocol by design"))

(comment "CPSA 4.4.0")
(comment "All input read from blanchet.scm")

(defprotocol blanchet basic
  (defrole init
    (vars (a b akey) (s skey) (d data))
    (trace (send (enc (enc s (invk a)) b)) (recv (enc d s)))
    (uniq-orig s))
  (defrole resp
    (vars (a b akey) (s skey) (d data))
    (trace (recv (enc (enc s (invk a)) b)) (send (enc d s)))
    (uniq-orig d))
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
  (uniq-orig d s)
  (operation encryption-test (added-strand resp 2) (enc d s) (0 1))
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
  (uniq-orig d s)
  (operation nonce-test (contracted (a-0 a) (b-0 b)) s (1 0)
    (enc (enc s (invk a)) b))
  (traces ((send (enc (enc s (invk a)) b)) (recv (enc d s)))
    ((recv (enc (enc s (invk a)) b)) (send (enc d s))))
  (label 3)
  (parent 1)
  (realized)
  (shape)
  (maps ((0) ((a a) (b b) (s s) (d d))))
  (origs (d (1 1)) (s (0 0))))

(comment "Nothing left to do")

(defprotocol blanchet basic
  (defrole init
    (vars (a b akey) (s skey) (d data))
    (trace (send (enc (enc s (invk a)) b)) (recv (enc d s)))
    (uniq-orig s))
  (defrole resp
    (vars (a b akey) (s skey) (d data))
    (trace (recv (enc (enc s (invk a)) b)) (send (enc d s)))
    (uniq-orig d))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (comment "Blanchet's protocol"))

(defskeleton blanchet
  (vars (d data) (s skey) (a b akey))
  (defstrand resp 2 (d d) (s s) (a a) (b b))
  (non-orig (invk a) (invk b))
  (uniq-orig d)
  (comment "Analyze from the responder's perspective")
  (traces ((recv (enc (enc s (invk a)) b)) (send (enc d s))))
  (label 4)
  (unrealized (0 0))
  (origs (d (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton blanchet
  (vars (d data) (s skey) (a b b-0 akey))
  (defstrand resp 2 (d d) (s s) (a a) (b b))
  (defstrand init 1 (s s) (a a) (b b-0))
  (precedes ((1 0) (0 0)))
  (non-orig (invk a) (invk b))
  (uniq-orig d s)
  (operation encryption-test (added-strand init 1) (enc s (invk a))
    (0 0))
  (traces ((recv (enc (enc s (invk a)) b)) (send (enc d s)))
    ((send (enc (enc s (invk a)) b-0))))
  (label 5)
  (parent 4)
  (realized)
  (shape)
  (maps ((0) ((a a) (b b) (s s) (d d))))
  (origs (s (1 0)) (d (0 1))))

(comment "Nothing left to do")

(defprotocol blanchet basic
  (defrole init
    (vars (a b akey) (s skey) (d data))
    (trace (send (enc (enc s (invk a)) b)) (recv (enc d s)))
    (uniq-orig s))
  (defrole resp
    (vars (a b akey) (s skey) (d data))
    (trace (recv (enc (enc s (invk a)) b)) (send (enc d s)))
    (uniq-orig d))
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
  (deflistener d)
  (non-orig (invk b))
  (uniq-orig s)
  (comment "From the initiator's perspective, is the secret leaked?")
  (traces ((send (enc (enc s (invk a)) b)) (recv (enc d s)))
    ((recv d) (send d)))
  (label 6)
  (unrealized (0 1))
  (origs (s (0 0)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton blanchet
  (vars (d data) (s skey) (a b a-0 b-0 akey))
  (defstrand init 2 (d d) (s s) (a a) (b b))
  (deflistener d)
  (defstrand resp 2 (d d) (s s) (a a-0) (b b-0))
  (precedes ((0 0) (2 0)) ((2 1) (0 1)) ((2 1) (1 0)))
  (non-orig (invk b))
  (uniq-orig d s)
  (operation encryption-test (added-strand resp 2) (enc d s) (0 1))
  (traces ((send (enc (enc s (invk a)) b)) (recv (enc d s)))
    ((recv d) (send d))
    ((recv (enc (enc s (invk a-0)) b-0)) (send (enc d s))))
  (label 7)
  (parent 6)
  (unrealized (1 0) (2 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton blanchet
  (vars (d data) (s skey) (a b akey))
  (defstrand init 2 (d d) (s s) (a a) (b b))
  (deflistener d)
  (deflistener s)
  (precedes ((0 0) (2 0)) ((2 1) (0 1)))
  (non-orig (invk b))
  (uniq-orig s)
  (operation encryption-test (added-listener s) (enc d s) (0 1))
  (traces ((send (enc (enc s (invk a)) b)) (recv (enc d s)))
    ((recv d) (send d)) ((recv s) (send s)))
  (label 8)
  (parent 6)
  (unrealized (2 0))
  (dead)
  (comment "empty cohort"))

(defskeleton blanchet
  (vars (d data) (s skey) (a b akey))
  (defstrand init 2 (d d) (s s) (a a) (b b))
  (deflistener d)
  (defstrand resp 2 (d d) (s s) (a a) (b b))
  (precedes ((0 0) (2 0)) ((2 1) (0 1)) ((2 1) (1 0)))
  (non-orig (invk b))
  (uniq-orig d s)
  (operation nonce-test (contracted (a-0 a) (b-0 b)) s (2 0)
    (enc (enc s (invk a)) b))
  (traces ((send (enc (enc s (invk a)) b)) (recv (enc d s)))
    ((recv d) (send d))
    ((recv (enc (enc s (invk a)) b)) (send (enc d s))))
  (label 9)
  (parent 7)
  (unrealized (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton blanchet
  (vars (d data) (s skey) (a b akey))
  (defstrand init 2 (d d) (s s) (a a) (b b))
  (deflistener d)
  (defstrand resp 2 (d d) (s s) (a a) (b b))
  (deflistener s)
  (precedes ((0 0) (2 0)) ((0 0) (3 0)) ((2 1) (0 1)) ((2 1) (1 0))
    ((3 1) (1 0)))
  (non-orig (invk b))
  (uniq-orig d s)
  (operation nonce-test (added-listener s) d (1 0) (enc d s))
  (traces ((send (enc (enc s (invk a)) b)) (recv (enc d s)))
    ((recv d) (send d))
    ((recv (enc (enc s (invk a)) b)) (send (enc d s)))
    ((recv s) (send s)))
  (label 10)
  (parent 9)
  (unrealized (3 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol blanchet basic
  (defrole init
    (vars (a b akey) (s skey) (d data))
    (trace (send (enc (enc s (invk a)) b)) (recv (enc d s)))
    (uniq-orig s))
  (defrole resp
    (vars (a b akey) (s skey) (d data))
    (trace (recv (enc (enc s (invk a)) b)) (send (enc d s)))
    (uniq-orig d))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (comment "Blanchet's protocol"))

(defskeleton blanchet
  (vars (d data) (s skey) (a b akey))
  (defstrand resp 2 (d d) (s s) (a a) (b b))
  (deflistener d)
  (non-orig (invk a) (invk b))
  (uniq-orig d)
  (comment "From the responders's perspective, is the secret leaked?")
  (traces ((recv (enc (enc s (invk a)) b)) (send (enc d s)))
    ((recv d) (send d)))
  (label 11)
  (unrealized (0 0) (1 0))
  (preskeleton)
  (origs (d (0 1)))
  (comment "Not a skeleton"))

(defskeleton blanchet
  (vars (d data) (s skey) (a b akey))
  (defstrand resp 2 (d d) (s s) (a a) (b b))
  (deflistener d)
  (precedes ((0 1) (1 0)))
  (non-orig (invk a) (invk b))
  (uniq-orig d)
  (traces ((recv (enc (enc s (invk a)) b)) (send (enc d s)))
    ((recv d) (send d)))
  (label 12)
  (parent 11)
  (unrealized (0 0))
  (origs (d (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton blanchet
  (vars (d data) (s skey) (a b b-0 akey))
  (defstrand resp 2 (d d) (s s) (a a) (b b))
  (deflistener d)
  (defstrand init 1 (s s) (a a) (b b-0))
  (precedes ((0 1) (1 0)) ((2 0) (0 0)))
  (non-orig (invk a) (invk b))
  (uniq-orig d s)
  (operation encryption-test (added-strand init 1) (enc s (invk a))
    (0 0))
  (traces ((recv (enc (enc s (invk a)) b)) (send (enc d s)))
    ((recv d) (send d)) ((send (enc (enc s (invk a)) b-0))))
  (label 13)
  (parent 12)
  (realized)
  (shape)
  (maps ((0 1) ((a a) (b b) (s s) (d d))))
  (origs (s (2 0)) (d (0 1))))

(comment "Nothing left to do")

(defprotocol blanchet-corrected basic
  (defrole init
    (vars (a b akey) (s skey) (d data))
    (trace (send (enc (enc s b (invk a)) b)) (recv (enc d s)))
    (uniq-orig s))
  (defrole resp
    (vars (a b akey) (s skey) (d data))
    (trace (recv (enc (enc s b (invk a)) b)) (send (enc d s)))
    (uniq-orig d))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (comment "Corrected Blanchet's protocol"))

(defskeleton blanchet-corrected
  (vars (d data) (s skey) (a b akey))
  (defstrand init 2 (d d) (s s) (a a) (b b))
  (non-orig (invk b))
  (uniq-orig s)
  (comment "Analyze from the initiator's perspective")
  (traces ((send (enc (enc s b (invk a)) b)) (recv (enc d s))))
  (label 14)
  (unrealized (0 1))
  (origs (s (0 0)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton blanchet-corrected
  (vars (d data) (s skey) (a b a-0 b-0 akey))
  (defstrand init 2 (d d) (s s) (a a) (b b))
  (defstrand resp 2 (d d) (s s) (a a-0) (b b-0))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (invk b))
  (uniq-orig d s)
  (operation encryption-test (added-strand resp 2) (enc d s) (0 1))
  (traces ((send (enc (enc s b (invk a)) b)) (recv (enc d s)))
    ((recv (enc (enc s b-0 (invk a-0)) b-0)) (send (enc d s))))
  (label 15)
  (parent 14)
  (unrealized (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton blanchet-corrected
  (vars (d data) (s skey) (a b akey))
  (defstrand init 2 (d d) (s s) (a a) (b b))
  (deflistener s)
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (invk b))
  (uniq-orig s)
  (operation encryption-test (added-listener s) (enc d s) (0 1))
  (traces ((send (enc (enc s b (invk a)) b)) (recv (enc d s)))
    ((recv s) (send s)))
  (label 16)
  (parent 14)
  (unrealized (1 0))
  (dead)
  (comment "empty cohort"))

(defskeleton blanchet-corrected
  (vars (d data) (s skey) (a b akey))
  (defstrand init 2 (d d) (s s) (a a) (b b))
  (defstrand resp 2 (d d) (s s) (a a) (b b))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (invk b))
  (uniq-orig d s)
  (operation nonce-test (contracted (a-0 a) (b-0 b)) s (1 0)
    (enc (enc s b (invk a)) b))
  (traces ((send (enc (enc s b (invk a)) b)) (recv (enc d s)))
    ((recv (enc (enc s b (invk a)) b)) (send (enc d s))))
  (label 17)
  (parent 15)
  (realized)
  (shape)
  (maps ((0) ((a a) (b b) (s s) (d d))))
  (origs (d (1 1)) (s (0 0))))

(comment "Nothing left to do")

(defprotocol blanchet-corrected basic
  (defrole init
    (vars (a b akey) (s skey) (d data))
    (trace (send (enc (enc s b (invk a)) b)) (recv (enc d s)))
    (uniq-orig s))
  (defrole resp
    (vars (a b akey) (s skey) (d data))
    (trace (recv (enc (enc s b (invk a)) b)) (send (enc d s)))
    (uniq-orig d))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (comment "Corrected Blanchet's protocol"))

(defskeleton blanchet-corrected
  (vars (d data) (s skey) (a b akey))
  (defstrand init 2 (d d) (s s) (a a) (b b))
  (deflistener d)
  (non-orig (invk b))
  (uniq-orig s)
  (comment "From the initiator's perspective, is the secret leaked?")
  (traces ((send (enc (enc s b (invk a)) b)) (recv (enc d s)))
    ((recv d) (send d)))
  (label 18)
  (unrealized (0 1))
  (origs (s (0 0)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton blanchet-corrected
  (vars (d data) (s skey) (a b a-0 b-0 akey))
  (defstrand init 2 (d d) (s s) (a a) (b b))
  (deflistener d)
  (defstrand resp 2 (d d) (s s) (a a-0) (b b-0))
  (precedes ((0 0) (2 0)) ((2 1) (0 1)) ((2 1) (1 0)))
  (non-orig (invk b))
  (uniq-orig d s)
  (operation encryption-test (added-strand resp 2) (enc d s) (0 1))
  (traces ((send (enc (enc s b (invk a)) b)) (recv (enc d s)))
    ((recv d) (send d))
    ((recv (enc (enc s b-0 (invk a-0)) b-0)) (send (enc d s))))
  (label 19)
  (parent 18)
  (unrealized (1 0) (2 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton blanchet-corrected
  (vars (d data) (s skey) (a b akey))
  (defstrand init 2 (d d) (s s) (a a) (b b))
  (deflistener d)
  (deflistener s)
  (precedes ((0 0) (2 0)) ((2 1) (0 1)))
  (non-orig (invk b))
  (uniq-orig s)
  (operation encryption-test (added-listener s) (enc d s) (0 1))
  (traces ((send (enc (enc s b (invk a)) b)) (recv (enc d s)))
    ((recv d) (send d)) ((recv s) (send s)))
  (label 20)
  (parent 18)
  (unrealized (2 0))
  (dead)
  (comment "empty cohort"))

(defskeleton blanchet-corrected
  (vars (d data) (s skey) (a b akey))
  (defstrand init 2 (d d) (s s) (a a) (b b))
  (deflistener d)
  (defstrand resp 2 (d d) (s s) (a a) (b b))
  (precedes ((0 0) (2 0)) ((2 1) (0 1)) ((2 1) (1 0)))
  (non-orig (invk b))
  (uniq-orig d s)
  (operation nonce-test (contracted (a-0 a) (b-0 b)) s (2 0)
    (enc (enc s b (invk a)) b))
  (traces ((send (enc (enc s b (invk a)) b)) (recv (enc d s)))
    ((recv d) (send d))
    ((recv (enc (enc s b (invk a)) b)) (send (enc d s))))
  (label 21)
  (parent 19)
  (unrealized (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton blanchet-corrected
  (vars (d data) (s skey) (a b akey))
  (defstrand init 2 (d d) (s s) (a a) (b b))
  (deflistener d)
  (defstrand resp 2 (d d) (s s) (a a) (b b))
  (deflistener s)
  (precedes ((0 0) (2 0)) ((0 0) (3 0)) ((2 1) (0 1)) ((2 1) (1 0))
    ((3 1) (1 0)))
  (non-orig (invk b))
  (uniq-orig d s)
  (operation nonce-test (added-listener s) d (1 0) (enc d s))
  (traces ((send (enc (enc s b (invk a)) b)) (recv (enc d s)))
    ((recv d) (send d))
    ((recv (enc (enc s b (invk a)) b)) (send (enc d s)))
    ((recv s) (send s)))
  (label 22)
  (parent 21)
  (unrealized (3 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol blanchet-corrected basic
  (defrole init
    (vars (a b akey) (s skey) (d data))
    (trace (send (enc (enc s b (invk a)) b)) (recv (enc d s)))
    (uniq-orig s))
  (defrole resp
    (vars (a b akey) (s skey) (d data))
    (trace (recv (enc (enc s b (invk a)) b)) (send (enc d s)))
    (uniq-orig d))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (comment "Corrected Blanchet's protocol"))

(defskeleton blanchet-corrected
  (vars (d data) (s skey) (a b akey))
  (defstrand resp 2 (d d) (s s) (a a) (b b))
  (non-orig (invk a) (invk b))
  (uniq-orig d)
  (comment "Analyze from the responder's perspective")
  (traces ((recv (enc (enc s b (invk a)) b)) (send (enc d s))))
  (label 23)
  (unrealized (0 0))
  (origs (d (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton blanchet-corrected
  (vars (d data) (s skey) (a b akey))
  (defstrand resp 2 (d d) (s s) (a a) (b b))
  (defstrand init 1 (s s) (a a) (b b))
  (precedes ((1 0) (0 0)))
  (non-orig (invk a) (invk b))
  (uniq-orig d s)
  (operation encryption-test (added-strand init 1) (enc s b (invk a))
    (0 0))
  (traces ((recv (enc (enc s b (invk a)) b)) (send (enc d s)))
    ((send (enc (enc s b (invk a)) b))))
  (label 24)
  (parent 23)
  (realized)
  (shape)
  (maps ((0) ((a a) (b b) (s s) (d d))))
  (origs (s (1 0)) (d (0 1))))

(comment "Nothing left to do")

(defprotocol blanchet-corrected basic
  (defrole init
    (vars (a b akey) (s skey) (d data))
    (trace (send (enc (enc s b (invk a)) b)) (recv (enc d s)))
    (uniq-orig s))
  (defrole resp
    (vars (a b akey) (s skey) (d data))
    (trace (recv (enc (enc s b (invk a)) b)) (send (enc d s)))
    (uniq-orig d))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (comment "Corrected Blanchet's protocol"))

(defskeleton blanchet-corrected
  (vars (d data) (s skey) (a b akey))
  (defstrand resp 2 (d d) (s s) (a a) (b b))
  (deflistener d)
  (non-orig (invk a) (invk b))
  (uniq-orig d)
  (comment "From the responders's perspective, is the secret leaked?")
  (traces ((recv (enc (enc s b (invk a)) b)) (send (enc d s)))
    ((recv d) (send d)))
  (label 25)
  (unrealized (0 0) (1 0))
  (preskeleton)
  (origs (d (0 1)))
  (comment "Not a skeleton"))

(defskeleton blanchet-corrected
  (vars (d data) (s skey) (a b akey))
  (defstrand resp 2 (d d) (s s) (a a) (b b))
  (deflistener d)
  (precedes ((0 1) (1 0)))
  (non-orig (invk a) (invk b))
  (uniq-orig d)
  (traces ((recv (enc (enc s b (invk a)) b)) (send (enc d s)))
    ((recv d) (send d)))
  (label 26)
  (parent 25)
  (unrealized (0 0))
  (origs (d (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton blanchet-corrected
  (vars (d data) (s skey) (a b akey))
  (defstrand resp 2 (d d) (s s) (a a) (b b))
  (deflistener d)
  (defstrand init 1 (s s) (a a) (b b))
  (precedes ((0 1) (1 0)) ((2 0) (0 0)))
  (non-orig (invk a) (invk b))
  (uniq-orig d s)
  (operation encryption-test (added-strand init 1) (enc s b (invk a))
    (0 0))
  (traces ((recv (enc (enc s b (invk a)) b)) (send (enc d s)))
    ((recv d) (send d)) ((send (enc (enc s b (invk a)) b))))
  (label 27)
  (parent 26)
  (unrealized (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton blanchet-corrected
  (vars (d data) (s skey) (a b akey))
  (defstrand resp 2 (d d) (s s) (a a) (b b))
  (deflistener d)
  (defstrand init 1 (s s) (a a) (b b))
  (deflistener s)
  (precedes ((0 1) (1 0)) ((2 0) (0 0)) ((2 0) (3 0)) ((3 1) (1 0)))
  (non-orig (invk a) (invk b))
  (uniq-orig d s)
  (operation nonce-test (added-listener s) d (1 0) (enc d s))
  (traces ((recv (enc (enc s b (invk a)) b)) (send (enc d s)))
    ((recv d) (send d)) ((send (enc (enc s b (invk a)) b)))
    ((recv s) (send s)))
  (label 28)
  (parent 27)
  (unrealized (3 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")
