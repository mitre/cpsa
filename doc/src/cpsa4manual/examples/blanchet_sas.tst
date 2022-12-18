(herald "Blanchet's Simple Example Protocol"
  (comment "There is a flaw in this protocol by design"))

(comment "CPSA 4.4.0")
(comment "All input read from blanchet_sas.scm")

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
  (goals
    (forall ((d data) (s skey) (a b akey) (z strd))
      (implies
        (and (p "init" z 2) (p "init" "d" z d) (p "init" "s" z s)
          (p "init" "a" z a) (p "init" "b" z b) (non (invk b))
          (uniq-at s z 0))
        (exists ((z-0 strd))
          (and (p "resp" z-0 2) (p "resp" "d" z-0 d)
            (p "resp" "s" z-0 s) (p "resp" "a" z-0 a)
            (p "resp" "b" z-0 b) (prec z 0 z-0 0) (prec z-0 1 z 1)
            (uniq-at d z-0 1))))))
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
  (satisfies yes)
  (maps ((0) ((d d) (s s) (a a) (b b))))
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
  (goals
    (forall ((d data) (s skey) (a b akey) (z strd))
      (implies
        (and (p "resp" z 2) (p "resp" "d" z d) (p "resp" "s" z s)
          (p "resp" "a" z a) (p "resp" "b" z b) (non (invk a))
          (non (invk b)) (uniq-at d z 1))
        (exists ((b-0 akey) (z-0 strd))
          (and (p "init" z-0 1) (p "init" "s" z-0 s)
            (p "init" "a" z-0 a) (p "init" "b" z-0 b-0) (prec z-0 0 z 0)
            (uniq-at s z-0 0))))))
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
  (satisfies yes)
  (maps ((0) ((d d) (s s) (a a) (b b))))
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
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (comment "Blanchet's protocol"))

(defskeleton blanchet
  (vars (d data) (s skey) (a b akey))
  (deflistener d)
  (defstrand init 2 (d d) (s s) (a a) (b b))
  (non-orig (invk b))
  (uniq-orig s)
  (goals
    (forall ((d data) (s skey) (a b akey) (z z-0 strd))
      (implies
        (and (p "init" z 2) (p "" z-0 2) (p "init" "d" z d)
          (p "init" "s" z s) (p "init" "a" z a) (p "init" "b" z b)
          (p "" "x" z-0 d) (non (invk b)) (uniq-at s z 0)) (false))))
  (traces ((recv d) (send d))
    ((send (enc (enc s (invk a)) b)) (recv (enc d s))))
  (label 6)
  (unrealized (1 1))
  (origs (s (1 0)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton blanchet
  (vars (d data) (s skey) (a b a-0 b-0 akey))
  (deflistener d)
  (defstrand init 2 (d d) (s s) (a a) (b b))
  (defstrand resp 2 (d d) (s s) (a a-0) (b b-0))
  (precedes ((1 0) (2 0)) ((2 1) (0 0)) ((2 1) (1 1)))
  (non-orig (invk b))
  (uniq-orig d s)
  (operation encryption-test (added-strand resp 2) (enc d s) (1 1))
  (traces ((recv d) (send d))
    ((send (enc (enc s (invk a)) b)) (recv (enc d s)))
    ((recv (enc (enc s (invk a-0)) b-0)) (send (enc d s))))
  (label 7)
  (parent 6)
  (unrealized (0 0) (2 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton blanchet
  (vars (d data) (s skey) (a b akey))
  (deflistener d)
  (defstrand init 2 (d d) (s s) (a a) (b b))
  (deflistener s)
  (precedes ((1 0) (2 0)) ((2 1) (1 1)))
  (non-orig (invk b))
  (uniq-orig s)
  (operation encryption-test (added-listener s) (enc d s) (1 1))
  (traces ((recv d) (send d))
    ((send (enc (enc s (invk a)) b)) (recv (enc d s)))
    ((recv s) (send s)))
  (label 8)
  (parent 6)
  (unrealized (2 0))
  (dead)
  (comment "empty cohort"))

(defskeleton blanchet
  (vars (d data) (s skey) (a b akey))
  (deflistener d)
  (defstrand init 2 (d d) (s s) (a a) (b b))
  (defstrand resp 2 (d d) (s s) (a a) (b b))
  (precedes ((1 0) (2 0)) ((2 1) (0 0)) ((2 1) (1 1)))
  (non-orig (invk b))
  (uniq-orig d s)
  (operation nonce-test (contracted (a-0 a) (b-0 b)) s (2 0)
    (enc (enc s (invk a)) b))
  (traces ((recv d) (send d))
    ((send (enc (enc s (invk a)) b)) (recv (enc d s)))
    ((recv (enc (enc s (invk a)) b)) (send (enc d s))))
  (label 9)
  (parent 7)
  (unrealized (0 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton blanchet
  (vars (d data) (s skey) (a b akey))
  (deflistener d)
  (defstrand init 2 (d d) (s s) (a a) (b b))
  (defstrand resp 2 (d d) (s s) (a a) (b b))
  (deflistener s)
  (precedes ((1 0) (2 0)) ((1 0) (3 0)) ((2 1) (0 0)) ((2 1) (1 1))
    ((3 1) (0 0)))
  (non-orig (invk b))
  (uniq-orig d s)
  (operation nonce-test (added-listener s) d (0 0) (enc d s))
  (traces ((recv d) (send d))
    ((send (enc (enc s (invk a)) b)) (recv (enc d s)))
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
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (comment "Blanchet's protocol"))

(defskeleton blanchet
  (vars (d data) (s skey) (a b akey))
  (deflistener d)
  (defstrand resp 2 (d d) (s s) (a a) (b b))
  (non-orig (invk a) (invk b))
  (uniq-orig d)
  (goals
    (forall ((d data) (s skey) (a b akey) (z z-0 strd))
      (implies
        (and (p "resp" z 2) (p "" z-0 2) (p "resp" "d" z d)
          (p "resp" "s" z s) (p "resp" "a" z a) (p "resp" "b" z b)
          (p "" "x" z-0 d) (non (invk a)) (non (invk b))
          (uniq-at d z 1))
        (exists ((b-0 akey) (z-1 strd))
          (and (p "init" z-1 1) (p "init" "s" z-1 s)
            (p "init" "a" z-1 a) (p "init" "b" z-1 b-0) (prec z 1 z-0 0)
            (prec z-1 0 z 0) (uniq-at s z-1 0))))))
  (traces ((recv d) (send d))
    ((recv (enc (enc s (invk a)) b)) (send (enc d s))))
  (label 11)
  (unrealized (0 0) (1 0))
  (preskeleton)
  (origs (d (1 1)))
  (comment "Not a skeleton"))

(defskeleton blanchet
  (vars (d data) (s skey) (a b akey))
  (deflistener d)
  (defstrand resp 2 (d d) (s s) (a a) (b b))
  (precedes ((1 1) (0 0)))
  (non-orig (invk a) (invk b))
  (uniq-orig d)
  (traces ((recv d) (send d))
    ((recv (enc (enc s (invk a)) b)) (send (enc d s))))
  (label 12)
  (parent 11)
  (unrealized (1 0))
  (origs (d (1 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton blanchet
  (vars (d data) (s skey) (a b b-0 akey))
  (deflistener d)
  (defstrand resp 2 (d d) (s s) (a a) (b b))
  (defstrand init 1 (s s) (a a) (b b-0))
  (precedes ((1 1) (0 0)) ((2 0) (1 0)))
  (non-orig (invk a) (invk b))
  (uniq-orig d s)
  (operation encryption-test (added-strand init 1) (enc s (invk a))
    (1 0))
  (traces ((recv d) (send d))
    ((recv (enc (enc s (invk a)) b)) (send (enc d s)))
    ((send (enc (enc s (invk a)) b-0))))
  (label 13)
  (parent 12)
  (realized)
  (shape)
  (satisfies yes)
  (maps ((0 1) ((d d) (s s) (a a) (b b))))
  (origs (s (2 0)) (d (1 1))))

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
  (goals
    (forall ((d data) (s skey) (a b akey) (z strd))
      (implies
        (and (p "init" z 2) (p "init" "d" z d) (p "init" "s" z s)
          (p "init" "a" z a) (p "init" "b" z b) (non (invk b))
          (uniq-at s z 0))
        (exists ((z-0 strd))
          (and (p "resp" z-0 2) (p "resp" "d" z-0 d)
            (p "resp" "s" z-0 s) (p "resp" "a" z-0 a)
            (p "resp" "b" z-0 b) (prec z 0 z-0 0) (prec z-0 1 z 1)
            (uniq-at d z-0 1))))))
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
  (satisfies yes)
  (maps ((0) ((d d) (s s) (a a) (b b))))
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
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (comment "Corrected Blanchet's protocol"))

(defskeleton blanchet-corrected
  (vars (d data) (s skey) (a b akey))
  (deflistener d)
  (defstrand init 2 (d d) (s s) (a a) (b b))
  (non-orig (invk b))
  (uniq-orig s)
  (goals
    (forall ((d data) (s skey) (a b akey) (z z-0 strd))
      (implies
        (and (p "init" z 2) (p "" z-0 2) (p "init" "d" z d)
          (p "init" "s" z s) (p "init" "a" z a) (p "init" "b" z b)
          (p "" "x" z-0 d) (non (invk b)) (uniq-at s z 0)) (false))))
  (traces ((recv d) (send d))
    ((send (enc (enc s b (invk a)) b)) (recv (enc d s))))
  (label 18)
  (unrealized (1 1))
  (origs (s (1 0)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton blanchet-corrected
  (vars (d data) (s skey) (a b a-0 b-0 akey))
  (deflistener d)
  (defstrand init 2 (d d) (s s) (a a) (b b))
  (defstrand resp 2 (d d) (s s) (a a-0) (b b-0))
  (precedes ((1 0) (2 0)) ((2 1) (0 0)) ((2 1) (1 1)))
  (non-orig (invk b))
  (uniq-orig d s)
  (operation encryption-test (added-strand resp 2) (enc d s) (1 1))
  (traces ((recv d) (send d))
    ((send (enc (enc s b (invk a)) b)) (recv (enc d s)))
    ((recv (enc (enc s b-0 (invk a-0)) b-0)) (send (enc d s))))
  (label 19)
  (parent 18)
  (unrealized (0 0) (2 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton blanchet-corrected
  (vars (d data) (s skey) (a b akey))
  (deflistener d)
  (defstrand init 2 (d d) (s s) (a a) (b b))
  (deflistener s)
  (precedes ((1 0) (2 0)) ((2 1) (1 1)))
  (non-orig (invk b))
  (uniq-orig s)
  (operation encryption-test (added-listener s) (enc d s) (1 1))
  (traces ((recv d) (send d))
    ((send (enc (enc s b (invk a)) b)) (recv (enc d s)))
    ((recv s) (send s)))
  (label 20)
  (parent 18)
  (unrealized (2 0))
  (dead)
  (comment "empty cohort"))

(defskeleton blanchet-corrected
  (vars (d data) (s skey) (a b akey))
  (deflistener d)
  (defstrand init 2 (d d) (s s) (a a) (b b))
  (defstrand resp 2 (d d) (s s) (a a) (b b))
  (precedes ((1 0) (2 0)) ((2 1) (0 0)) ((2 1) (1 1)))
  (non-orig (invk b))
  (uniq-orig d s)
  (operation nonce-test (contracted (a-0 a) (b-0 b)) s (2 0)
    (enc (enc s b (invk a)) b))
  (traces ((recv d) (send d))
    ((send (enc (enc s b (invk a)) b)) (recv (enc d s)))
    ((recv (enc (enc s b (invk a)) b)) (send (enc d s))))
  (label 21)
  (parent 19)
  (unrealized (0 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton blanchet-corrected
  (vars (d data) (s skey) (a b akey))
  (deflistener d)
  (defstrand init 2 (d d) (s s) (a a) (b b))
  (defstrand resp 2 (d d) (s s) (a a) (b b))
  (deflistener s)
  (precedes ((1 0) (2 0)) ((1 0) (3 0)) ((2 1) (0 0)) ((2 1) (1 1))
    ((3 1) (0 0)))
  (non-orig (invk b))
  (uniq-orig d s)
  (operation nonce-test (added-listener s) d (0 0) (enc d s))
  (traces ((recv d) (send d))
    ((send (enc (enc s b (invk a)) b)) (recv (enc d s)))
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
  (goals
    (forall ((d data) (s skey) (a b akey) (z strd))
      (implies
        (and (p "resp" z 2) (p "resp" "d" z d) (p "resp" "s" z s)
          (p "resp" "a" z a) (p "resp" "b" z b) (non (invk a))
          (non (invk b)) (uniq-at d z 1))
        (exists ((z-0 strd))
          (and (p "init" z-0 1) (p "init" "s" z-0 s)
            (p "init" "a" z-0 a) (p "init" "b" z-0 b) (prec z-0 0 z 0)
            (uniq-at s z-0 0))))))
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
  (satisfies yes)
  (maps ((0) ((d d) (s s) (a a) (b b))))
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
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (comment "Corrected Blanchet's protocol"))

(defskeleton blanchet-corrected
  (vars (d data) (s skey) (a b akey))
  (deflistener d)
  (defstrand resp 2 (d d) (s s) (a a) (b b))
  (non-orig (invk a) (invk b))
  (uniq-orig d)
  (goals
    (forall ((d data) (s skey) (a b akey) (z z-0 strd))
      (implies
        (and (p "resp" z 2) (p "" z-0 2) (p "resp" "d" z d)
          (p "resp" "s" z s) (p "resp" "a" z a) (p "resp" "b" z b)
          (p "" "x" z-0 d) (non (invk a)) (non (invk b))
          (uniq-at d z 1)) (false))))
  (traces ((recv d) (send d))
    ((recv (enc (enc s b (invk a)) b)) (send (enc d s))))
  (label 25)
  (unrealized (0 0) (1 0))
  (preskeleton)
  (origs (d (1 1)))
  (comment "Not a skeleton"))

(defskeleton blanchet-corrected
  (vars (d data) (s skey) (a b akey))
  (deflistener d)
  (defstrand resp 2 (d d) (s s) (a a) (b b))
  (precedes ((1 1) (0 0)))
  (non-orig (invk a) (invk b))
  (uniq-orig d)
  (traces ((recv d) (send d))
    ((recv (enc (enc s b (invk a)) b)) (send (enc d s))))
  (label 26)
  (parent 25)
  (unrealized (1 0))
  (origs (d (1 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton blanchet-corrected
  (vars (d data) (s skey) (a b akey))
  (deflistener d)
  (defstrand resp 2 (d d) (s s) (a a) (b b))
  (defstrand init 1 (s s) (a a) (b b))
  (precedes ((1 1) (0 0)) ((2 0) (1 0)))
  (non-orig (invk a) (invk b))
  (uniq-orig d s)
  (operation encryption-test (added-strand init 1) (enc s b (invk a))
    (1 0))
  (traces ((recv d) (send d))
    ((recv (enc (enc s b (invk a)) b)) (send (enc d s)))
    ((send (enc (enc s b (invk a)) b))))
  (label 27)
  (parent 26)
  (unrealized (0 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton blanchet-corrected
  (vars (d data) (s skey) (a b akey))
  (deflistener d)
  (defstrand resp 2 (d d) (s s) (a a) (b b))
  (defstrand init 1 (s s) (a a) (b b))
  (deflistener s)
  (precedes ((1 1) (0 0)) ((2 0) (1 0)) ((2 0) (3 0)) ((3 1) (0 0)))
  (non-orig (invk a) (invk b))
  (uniq-orig d s)
  (operation nonce-test (added-listener s) d (0 0) (enc d s))
  (traces ((recv d) (send d))
    ((recv (enc (enc s b (invk a)) b)) (send (enc d s)))
    ((send (enc (enc s b (invk a)) b))) ((recv s) (send s)))
  (label 28)
  (parent 27)
  (unrealized (3 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")
