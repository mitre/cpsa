(herald "ALternate Needham-Schroeder Public-Key Protocol Variants")

(comment "CPSA 4.4.3")
(comment "All input read from tst/ns-rebinding.scm")

(defprotocol ns basic
  (defrole init
    (vars (a b name) (n1 n2 text))
    (trace (send (enc n1 a (pubk b))) (recv (enc n1 n2 b (pubk a)))
      (send (enc n2 (pubk b))))
    (facts (rel1 n1 n2) (rel2 n1 n2)))
  (defrole resp
    (vars (b a name) (n2 n1 text))
    (trace (recv (enc n1 a (pubk b))) (send (enc n1 n2 b (pubk a)))
      (recv (enc n2 (pubk b)))))
  (defrule rebind-x
    (forall ((x y text))
      (implies
        (fact rel1 x y)
        (exists ((x-0 name)) (fact rel2 x-0 y)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule fact-init-rel11
    (forall ((z strd) (n2 n1 text))
      (implies
        (and (p "init" z (idx 2)) (p "init" "n1" z n1)
          (p "init" "n2" z n2)) (fact rel1 n1 n2))))
  (defgenrule fact-init-rel20
    (forall ((z strd) (n2 n1 text))
      (implies
        (and (p "init" z (idx 2)) (p "init" "n1" z n1)
          (p "init" "n2" z n2)) (fact rel2 n1 n2))))
  (comment "Needham-Schroeder with no role origination assumptions"))

(defskeleton ns
  (vars (n1 n2 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (non-orig (privk a) (privk b))
  (uniq-orig n1)
  (comment "Initiator point-of-view")
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 b (pubk a)))
      (send (enc n2 (pubk b)))))
  (label 0)
  (unrealized (0 1))
  (origs (n1 (0 0)))
  (comment "Not closed under rules"))

(defskeleton ns
  (vars (x name) (n1 n2 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (non-orig (privk a) (privk b))
  (uniq-orig n1)
  (facts (rel2 x n2) (rel1 n1 n2) (rel2 n1 n2))
  (rule fact-init-rel11 fact-init-rel20 rebind-x)
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 b (pubk a)))
      (send (enc n2 (pubk b)))))
  (label 1)
  (parent 0)
  (unrealized (0 1))
  (origs (n1 (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (x name) (n1 n2 n2-0 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (defstrand resp 2 (n2 n2-0) (n1 n1) (b b) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a) (privk b))
  (uniq-orig n1)
  (facts (rel2 x n2) (rel1 n1 n2) (rel2 n1 n2))
  (rule fact-init-rel11 fact-init-rel20 rebind-x)
  (operation nonce-test (added-strand resp 2) n1 (0 1)
    (enc n1 a (pubk b)))
  (strand-map 0)
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 b (pubk a)))
      (send (enc n2 (pubk b))))
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2-0 b (pubk a)))))
  (label 2)
  (parent 1)
  (unrealized (0 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (x name) (n1 n2 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (defstrand resp 2 (n2 n2) (n1 n1) (b b) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a) (privk b))
  (uniq-orig n1)
  (facts (rel2 x n2) (rel1 n1 n2) (rel2 n1 n2))
  (rule fact-init-rel11 fact-init-rel20 rebind-x)
  (operation nonce-test (contracted (n2-0 n2)) n1 (0 1)
    (enc n1 a (pubk b)) (enc n1 n2 b (pubk a)))
  (strand-map 0 1)
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 b (pubk a)))
      (send (enc n2 (pubk b))))
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2 b (pubk a)))))
  (label 3)
  (parent 2)
  (realized)
  (shape)
  (maps ((0) ((a a) (b b) (n1 n1) (n2 n2))))
  (origs (n1 (0 0))))

(comment "Nothing left to do")

(defprotocol ns basic
  (defrole init
    (vars (a b name) (n1 n2 text))
    (trace (send (enc n1 a (pubk b))) (recv (enc n1 n2 b (pubk a)))
      (send (enc n2 (pubk b))))
    (facts (rel1 n1 n2) (rel2 n1 n2)))
  (defrole resp
    (vars (b a name) (n2 n1 text))
    (trace (recv (enc n1 a (pubk b))) (send (enc n1 n2 b (pubk a)))
      (recv (enc n2 (pubk b)))))
  (defrule rebind-x
    (forall ((x y text))
      (implies
        (fact rel1 x y)
        (exists ((x-0 name)) (fact rel2 x-0 y)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule fact-init-rel11
    (forall ((z strd) (n2 n1 text))
      (implies
        (and (p "init" z (idx 2)) (p "init" "n1" z n1)
          (p "init" "n2" z n2)) (fact rel1 n1 n2))))
  (defgenrule fact-init-rel20
    (forall ((z strd) (n2 n1 text))
      (implies
        (and (p "init" z (idx 2)) (p "init" "n1" z n1)
          (p "init" "n2" z n2)) (fact rel2 n1 n2))))
  (comment "Needham-Schroeder with no role origination assumptions"))

(defskeleton ns
  (vars (n1 n2 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (non-orig (privk a) (privk b))
  (uniq-orig n1)
  (facts (rel n1 n1))
  (comment "Initiator point-of-view")
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 b (pubk a)))
      (send (enc n2 (pubk b)))))
  (label 4)
  (unrealized (0 1))
  (origs (n1 (0 0)))
  (comment "Not closed under rules"))

(defskeleton ns
  (vars (x name) (n1 n2 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (non-orig (privk a) (privk b))
  (uniq-orig n1)
  (facts (rel2 x n2) (rel1 n1 n2) (rel2 n1 n2) (rel n1 n1))
  (rule fact-init-rel11 fact-init-rel20 rebind-x)
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 b (pubk a)))
      (send (enc n2 (pubk b)))))
  (label 5)
  (parent 4)
  (unrealized (0 1))
  (origs (n1 (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (x name) (n1 n2 n2-0 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (defstrand resp 2 (n2 n2-0) (n1 n1) (b b) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a) (privk b))
  (uniq-orig n1)
  (facts (rel2 x n2) (rel1 n1 n2) (rel2 n1 n2) (rel n1 n1))
  (rule fact-init-rel11 fact-init-rel20 rebind-x)
  (operation nonce-test (added-strand resp 2) n1 (0 1)
    (enc n1 a (pubk b)))
  (strand-map 0)
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 b (pubk a)))
      (send (enc n2 (pubk b))))
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2-0 b (pubk a)))))
  (label 6)
  (parent 5)
  (unrealized (0 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (x name) (n1 n2 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (defstrand resp 2 (n2 n2) (n1 n1) (b b) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a) (privk b))
  (uniq-orig n1)
  (facts (rel2 x n2) (rel1 n1 n2) (rel2 n1 n2) (rel n1 n1))
  (rule fact-init-rel11 fact-init-rel20 rebind-x)
  (operation nonce-test (contracted (n2-0 n2)) n1 (0 1)
    (enc n1 a (pubk b)) (enc n1 n2 b (pubk a)))
  (strand-map 0 1)
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 b (pubk a)))
      (send (enc n2 (pubk b))))
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2 b (pubk a)))))
  (label 7)
  (parent 6)
  (realized)
  (shape)
  (maps ((0) ((a a) (b b) (n1 n1) (n2 n2))))
  (origs (n1 (0 0))))

(comment "Nothing left to do")

(defprotocol ns basic
  (defrole init
    (vars (a b name) (n1 n2 text))
    (trace (send (enc n1 a (pubk b))) (recv (enc n1 n2 b (pubk a)))
      (send (enc n2 (pubk b))))
    (facts (rel1 n1 n2) (rel2 n1 n2)))
  (defrole resp
    (vars (b a name) (n2 n1 text))
    (trace (recv (enc n1 a (pubk b))) (send (enc n1 n2 b (pubk a)))
      (recv (enc n2 (pubk b)))))
  (defrule rebind-x
    (forall ((x y text))
      (implies
        (fact rel1 x y)
        (exists ((x-0 name)) (fact rel2 x-0 y)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule fact-init-rel11
    (forall ((z strd) (n2 n1 text))
      (implies
        (and (p "init" z (idx 2)) (p "init" "n1" z n1)
          (p "init" "n2" z n2)) (fact rel1 n1 n2))))
  (defgenrule fact-init-rel20
    (forall ((z strd) (n2 n1 text))
      (implies
        (and (p "init" z (idx 2)) (p "init" "n1" z n1)
          (p "init" "n2" z n2)) (fact rel2 n1 n2))))
  (comment "Needham-Schroeder with no role origination assumptions"))

(defskeleton ns
  (vars (n1 n2 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (non-orig (privk b))
  (uniq-orig n1)
  (comment "Initiator point-of-view")
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 b (pubk a)))
      (send (enc n2 (pubk b)))))
  (label 8)
  (unrealized (0 1))
  (origs (n1 (0 0)))
  (comment "Not closed under rules"))

(defskeleton ns
  (vars (x name) (n1 n2 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (non-orig (privk b))
  (uniq-orig n1)
  (facts (rel2 x n2) (rel1 n1 n2) (rel2 n1 n2))
  (rule fact-init-rel11 fact-init-rel20 rebind-x)
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 b (pubk a)))
      (send (enc n2 (pubk b)))))
  (label 9)
  (parent 8)
  (unrealized (0 1))
  (origs (n1 (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (x name) (n1 n2 n2-0 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (defstrand resp 2 (n2 n2-0) (n1 n1) (b b) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk b))
  (uniq-orig n1)
  (facts (rel2 x n2) (rel1 n1 n2) (rel2 n1 n2))
  (rule fact-init-rel11 fact-init-rel20 rebind-x)
  (operation nonce-test (added-strand resp 2) n1 (0 1)
    (enc n1 a (pubk b)))
  (strand-map 0)
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 b (pubk a)))
      (send (enc n2 (pubk b))))
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2-0 b (pubk a)))))
  (label 10)
  (parent 9)
  (realized)
  (shape)
  (maps ((0) ((a a) (b b) (n1 n1) (n2 n2))))
  (origs (n1 (0 0))))

(comment "Nothing left to do")

(defprotocol ns basic
  (defrole init
    (vars (a b name) (n1 n2 text))
    (trace (send (enc n1 a (pubk b))) (recv (enc n1 n2 b (pubk a)))
      (send (enc n2 (pubk b))))
    (facts (rel1 n1 n2) (rel2 n1 n2)))
  (defrole resp
    (vars (b a name) (n2 n1 text))
    (trace (recv (enc n1 a (pubk b))) (send (enc n1 n2 b (pubk a)))
      (recv (enc n2 (pubk b)))))
  (defrule rebind-x
    (forall ((x y text))
      (implies
        (fact rel1 x y)
        (exists ((x-0 name)) (fact rel2 x-0 y)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule fact-init-rel11
    (forall ((z strd) (n2 n1 text))
      (implies
        (and (p "init" z (idx 2)) (p "init" "n1" z n1)
          (p "init" "n2" z n2)) (fact rel1 n1 n2))))
  (defgenrule fact-init-rel20
    (forall ((z strd) (n2 n1 text))
      (implies
        (and (p "init" z (idx 2)) (p "init" "n1" z n1)
          (p "init" "n2" z n2)) (fact rel2 n1 n2))))
  (comment "Needham-Schroeder with no role origination assumptions"))

(defskeleton ns
  (vars (n1 n2 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (deflistener n1)
  (non-orig (privk a) (privk b))
  (uniq-orig n1)
  (comment "Initiator point-of-view")
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 b (pubk a)))
      (send (enc n2 (pubk b)))) ((recv n1) (send n1)))
  (label 11)
  (unrealized (0 1) (1 0))
  (preskeleton)
  (origs (n1 (0 0)))
  (comment "Not a skeleton"))

(defskeleton ns
  (vars (n1 n2 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (deflistener n1)
  (precedes ((0 0) (1 0)))
  (non-orig (privk a) (privk b))
  (uniq-orig n1)
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 b (pubk a)))
      (send (enc n2 (pubk b)))) ((recv n1) (send n1)))
  (label 12)
  (parent 11)
  (unrealized (0 1) (1 0))
  (origs (n1 (0 0)))
  (comment "Not closed under rules"))

(defskeleton ns
  (vars (x name) (n1 n2 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (deflistener n1)
  (precedes ((0 0) (1 0)))
  (non-orig (privk a) (privk b))
  (uniq-orig n1)
  (facts (rel2 x n2) (rel1 n1 n2) (rel2 n1 n2))
  (rule fact-init-rel11 fact-init-rel20 rebind-x)
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 b (pubk a)))
      (send (enc n2 (pubk b)))) ((recv n1) (send n1)))
  (label 13)
  (parent 12)
  (unrealized (0 1) (1 0))
  (origs (n1 (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (x name) (n1 n2 n2-0 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (deflistener n1)
  (defstrand resp 2 (n2 n2-0) (n1 n1) (b b) (a a))
  (precedes ((0 0) (2 0)) ((2 1) (1 0)))
  (non-orig (privk a) (privk b))
  (uniq-orig n1)
  (facts (rel2 x n2) (rel1 n1 n2) (rel2 n1 n2))
  (rule fact-init-rel11 fact-init-rel20 rebind-x)
  (operation nonce-test (added-strand resp 2) n1 (1 0)
    (enc n1 a (pubk b)))
  (strand-map 0 1)
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 b (pubk a)))
      (send (enc n2 (pubk b)))) ((recv n1) (send n1))
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2-0 b (pubk a)))))
  (label 14)
  (parent 13)
  (unrealized (0 1) (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (x name) (n2 text) (a b name))
  (defstrand init 3 (n1 n2) (n2 n2) (a a) (b b))
  (deflistener n2)
  (defstrand resp 2 (n2 n2) (n1 n2) (b b) (a a))
  (precedes ((0 0) (2 0)) ((0 2) (1 0)) ((2 1) (1 0)))
  (non-orig (privk a) (privk b))
  (uniq-orig n2)
  (facts (rel2 x n2) (rel1 n2 n2) (rel2 n2 n2))
  (rule fact-init-rel11 fact-init-rel20 rebind-x)
  (operation nonce-test (displaced 3 0 init 3) n2-0 (1 0)
    (enc n2-0 a (pubk b)) (enc n2-0 n2-0 b (pubk a)))
  (strand-map 0 1 2)
  (traces
    ((send (enc n2 a (pubk b))) (recv (enc n2 n2 b (pubk a)))
      (send (enc n2 (pubk b)))) ((recv n2) (send n2))
    ((recv (enc n2 a (pubk b))) (send (enc n2 n2 b (pubk a)))))
  (label 15)
  (parent 14)
  (unrealized (0 1) (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (x name) (n2 n2-0 text) (a b name))
  (defstrand init 3 (n1 n2) (n2 n2) (a a) (b b))
  (deflistener n2)
  (defstrand resp 2 (n2 n2) (n1 n2) (b b) (a a))
  (defstrand resp 2 (n2 n2-0) (n1 n2) (b b) (a a))
  (precedes ((0 0) (2 0)) ((0 0) (3 0)) ((0 2) (1 0)) ((2 1) (1 0))
    ((3 1) (1 0)))
  (non-orig (privk a) (privk b))
  (uniq-orig n2)
  (facts (rel2 x n2) (rel1 n2 n2) (rel2 n2 n2))
  (rule fact-init-rel11 fact-init-rel20 rebind-x)
  (operation nonce-test (added-strand resp 2) n2 (1 0) (enc n2 (pubk b))
    (enc n2 a (pubk b)) (enc n2 n2 b (pubk a)))
  (strand-map 0 1 2)
  (traces
    ((send (enc n2 a (pubk b))) (recv (enc n2 n2 b (pubk a)))
      (send (enc n2 (pubk b)))) ((recv n2) (send n2))
    ((recv (enc n2 a (pubk b))) (send (enc n2 n2 b (pubk a))))
    ((recv (enc n2 a (pubk b))) (send (enc n2 n2-0 b (pubk a)))))
  (label 16)
  (parent 15)
  (unrealized (0 1) (1 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol ns basic
  (defrole init
    (vars (a b name) (n1 n2 text))
    (trace (send (enc n1 a (pubk b))) (recv (enc n1 n2 b (pubk a)))
      (send (enc n2 (pubk b))))
    (facts (rel1 n1 n2) (rel2 n1 n2)))
  (defrole resp
    (vars (b a name) (n2 n1 text))
    (trace (recv (enc n1 a (pubk b))) (send (enc n1 n2 b (pubk a)))
      (recv (enc n2 (pubk b)))))
  (defrule rebind-x
    (forall ((x y text))
      (implies
        (fact rel1 x y)
        (exists ((x-0 name)) (fact rel2 x-0 y)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule fact-init-rel11
    (forall ((z strd) (n2 n1 text))
      (implies
        (and (p "init" z (idx 2)) (p "init" "n1" z n1)
          (p "init" "n2" z n2)) (fact rel1 n1 n2))))
  (defgenrule fact-init-rel20
    (forall ((z strd) (n2 n1 text))
      (implies
        (and (p "init" z (idx 2)) (p "init" "n1" z n1)
          (p "init" "n2" z n2)) (fact rel2 n1 n2))))
  (comment "Needham-Schroeder with no role origination assumptions"))

(defskeleton ns
  (vars (n1 n1-0 n2 n2-0 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (defstrand init 3 (n1 n1-0) (n2 n2-0) (a a) (b b))
  (non-orig (privk a) (privk b))
  (uniq-orig n1 n1-0)
  (comment "Double initiator point-of-view")
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 b (pubk a)))
      (send (enc n2 (pubk b))))
    ((send (enc n1-0 a (pubk b))) (recv (enc n1-0 n2-0 b (pubk a)))
      (send (enc n2-0 (pubk b)))))
  (label 17)
  (unrealized (0 1) (1 1))
  (origs (n1 (0 0)) (n1-0 (1 0)))
  (comment "Not closed under rules"))

(defskeleton ns
  (vars (x x-0 name) (n1 n1-0 n2 n2-0 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (defstrand init 3 (n1 n1-0) (n2 n2-0) (a a) (b b))
  (non-orig (privk a) (privk b))
  (uniq-orig n1 n1-0)
  (facts (rel2 x-0 n2-0) (rel2 x n2) (rel1 n1-0 n2-0) (rel1 n1 n2)
    (rel2 n1-0 n2-0) (rel2 n1 n2))
  (rule fact-init-rel11 fact-init-rel20 rebind-x)
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 b (pubk a)))
      (send (enc n2 (pubk b))))
    ((send (enc n1-0 a (pubk b))) (recv (enc n1-0 n2-0 b (pubk a)))
      (send (enc n2-0 (pubk b)))))
  (label 18)
  (parent 17)
  (seen 20)
  (seen-ops
    (20
      (operation nonce-test (added-strand resp 2) n1-0 (1 1)
        (enc n1-0 a (pubk b))) (strand-map 0 1)))
  (unrealized (0 1) (1 1))
  (origs (n1 (0 0)) (n1-0 (1 0)))
  (comment "2 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (x name) (n1 n2 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (non-orig (privk a) (privk b))
  (uniq-orig n1)
  (facts (rel2 x n2) (rel1 n1 n2) (rel2 n1 n2))
  (rule fact-init-rel11 fact-init-rel20 rebind-x)
  (operation collapsed 1 0)
  (strand-map 0 0)
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 b (pubk a)))
      (send (enc n2 (pubk b)))))
  (label 19)
  (parent 18)
  (unrealized (0 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (x x-0 name) (n1 n1-0 n2 n2-0 n2-1 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (defstrand init 3 (n1 n1-0) (n2 n2-0) (a a) (b b))
  (defstrand resp 2 (n2 n2-1) (n1 n1-0) (b b) (a a))
  (precedes ((1 0) (2 0)) ((2 1) (1 1)))
  (non-orig (privk a) (privk b))
  (uniq-orig n1 n1-0)
  (facts (rel2 x-0 n2) (rel2 x n2-0) (rel1 n1-0 n2-0) (rel1 n1 n2)
    (rel2 n1-0 n2-0) (rel2 n1 n2))
  (rule fact-init-rel11 fact-init-rel20 rebind-x)
  (operation nonce-test (added-strand resp 2) n1-0 (1 1)
    (enc n1-0 a (pubk b)))
  (strand-map 0 1)
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 b (pubk a)))
      (send (enc n2 (pubk b))))
    ((send (enc n1-0 a (pubk b))) (recv (enc n1-0 n2-0 b (pubk a)))
      (send (enc n2-0 (pubk b))))
    ((recv (enc n1-0 a (pubk b))) (send (enc n1-0 n2-1 b (pubk a)))))
  (label 20)
  (parent 18)
  (seen 22)
  (seen-ops
    (22
      (operation nonce-test (contracted (n2-1 n2-0)) n1-0 (1 1)
        (enc n1-0 a (pubk b)) (enc n1-0 n2-0 b (pubk a)))
      (strand-map 0 1 2)))
  (unrealized (0 1) (1 1))
  (comment "2 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (x name) (n1 n2 n2-0 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (defstrand resp 2 (n2 n2-0) (n1 n1) (b b) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a) (privk b))
  (uniq-orig n1)
  (facts (rel2 x n2) (rel1 n1 n2) (rel2 n1 n2))
  (rule fact-init-rel11 fact-init-rel20 rebind-x)
  (operation nonce-test (added-strand resp 2) n1 (0 1)
    (enc n1 a (pubk b)))
  (strand-map 0)
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 b (pubk a)))
      (send (enc n2 (pubk b))))
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2-0 b (pubk a)))))
  (label 21)
  (parent 19)
  (unrealized (0 1))
  (origs (n1 (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (x x-0 name) (n1 n1-0 n2 n2-0 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (defstrand init 3 (n1 n1-0) (n2 n2-0) (a a) (b b))
  (defstrand resp 2 (n2 n2-0) (n1 n1-0) (b b) (a a))
  (precedes ((1 0) (2 0)) ((2 1) (1 1)))
  (non-orig (privk a) (privk b))
  (uniq-orig n1 n1-0)
  (facts (rel2 x-0 n2) (rel2 x n2-0) (rel1 n1-0 n2-0) (rel1 n1 n2)
    (rel2 n1-0 n2-0) (rel2 n1 n2))
  (rule fact-init-rel11 fact-init-rel20 rebind-x)
  (operation nonce-test (contracted (n2-1 n2-0)) n1-0 (1 1)
    (enc n1-0 a (pubk b)) (enc n1-0 n2-0 b (pubk a)))
  (strand-map 0 1 2)
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 b (pubk a)))
      (send (enc n2 (pubk b))))
    ((send (enc n1-0 a (pubk b))) (recv (enc n1-0 n2-0 b (pubk a)))
      (send (enc n2-0 (pubk b))))
    ((recv (enc n1-0 a (pubk b))) (send (enc n1-0 n2-0 b (pubk a)))))
  (label 22)
  (parent 20)
  (seen 24)
  (seen-ops
    (24
      (operation nonce-test (added-strand resp 2) n1 (0 1)
        (enc n1 a (pubk b))) (strand-map 0 1 2)))
  (unrealized (0 1))
  (comment "2 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (x name) (n1 n2 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (defstrand resp 2 (n2 n2) (n1 n1) (b b) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a) (privk b))
  (uniq-orig n1)
  (facts (rel2 x n2) (rel1 n1 n2) (rel2 n1 n2))
  (rule fact-init-rel11 fact-init-rel20 rebind-x)
  (operation nonce-test (contracted (n2-0 n2)) n1 (0 1)
    (enc n1 a (pubk b)) (enc n1 n2 b (pubk a)))
  (strand-map 0 1)
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 b (pubk a)))
      (send (enc n2 (pubk b))))
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2 b (pubk a)))))
  (label 23)
  (parent 21)
  (realized)
  (shape)
  (maps ((0 0) ((a a) (b b) (n1 n1) (n1-0 n1) (n2 n2) (n2-0 n2))))
  (origs (n1 (0 0))))

(defskeleton ns
  (vars (x x-0 name) (n1 n1-0 n2 n2-0 n2-1 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (defstrand init 3 (n1 n1-0) (n2 n2-0) (a a) (b b))
  (defstrand resp 2 (n2 n2-0) (n1 n1-0) (b b) (a a))
  (defstrand resp 2 (n2 n2-1) (n1 n1) (b b) (a a))
  (precedes ((0 0) (3 0)) ((1 0) (2 0)) ((2 1) (1 1)) ((3 1) (0 1)))
  (non-orig (privk a) (privk b))
  (uniq-orig n1 n1-0)
  (facts (rel2 x-0 n2) (rel2 x n2-0) (rel1 n1-0 n2-0) (rel1 n1 n2)
    (rel2 n1-0 n2-0) (rel2 n1 n2))
  (rule fact-init-rel11 fact-init-rel20 rebind-x)
  (operation nonce-test (added-strand resp 2) n1 (0 1)
    (enc n1 a (pubk b)))
  (strand-map 0 1 2)
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 b (pubk a)))
      (send (enc n2 (pubk b))))
    ((send (enc n1-0 a (pubk b))) (recv (enc n1-0 n2-0 b (pubk a)))
      (send (enc n2-0 (pubk b))))
    ((recv (enc n1-0 a (pubk b))) (send (enc n1-0 n2-0 b (pubk a))))
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2-1 b (pubk a)))))
  (label 24)
  (parent 22)
  (unrealized (0 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (x x-0 name) (n1 n1-0 n2 n2-0 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2-0) (a a) (b b))
  (defstrand init 3 (n1 n1-0) (n2 n2) (a a) (b b))
  (defstrand resp 2 (n2 n2) (n1 n1-0) (b b) (a a))
  (defstrand resp 2 (n2 n2-0) (n1 n1) (b b) (a a))
  (precedes ((0 0) (3 0)) ((1 0) (2 0)) ((2 1) (1 1)) ((3 1) (0 1)))
  (non-orig (privk a) (privk b))
  (uniq-orig n1 n1-0)
  (facts (rel2 x-0 n2) (rel2 x n2-0) (rel1 n1-0 n2) (rel1 n1 n2-0)
    (rel2 n1-0 n2) (rel2 n1 n2-0))
  (rule fact-init-rel11 fact-init-rel20 rebind-x)
  (operation nonce-test (contracted (n2-1 n2-0)) n1 (0 1)
    (enc n1 a (pubk b)) (enc n1 n2-0 b (pubk a)))
  (strand-map 0 1 2 3)
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2-0 b (pubk a)))
      (send (enc n2-0 (pubk b))))
    ((send (enc n1-0 a (pubk b))) (recv (enc n1-0 n2 b (pubk a)))
      (send (enc n2 (pubk b))))
    ((recv (enc n1-0 a (pubk b))) (send (enc n1-0 n2 b (pubk a))))
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2-0 b (pubk a)))))
  (label 25)
  (parent 24)
  (realized)
  (shape)
  (maps ((0 1) ((a a) (b b) (n1 n1) (n1-0 n1-0) (n2 n2-0) (n2-0 n2))))
  (origs (n1 (0 0)) (n1-0 (1 0))))

(comment "Nothing left to do")

(defprotocol ns basic
  (defrole init
    (vars (a b name) (n1 n2 text))
    (trace (send (enc n1 a (pubk b))) (recv (enc n1 n2 b (pubk a)))
      (send (enc n2 (pubk b))))
    (facts (rel1 n1 n2) (rel2 n1 n2)))
  (defrole resp
    (vars (b a name) (n2 n1 text))
    (trace (recv (enc n1 a (pubk b))) (send (enc n1 n2 b (pubk a)))
      (recv (enc n2 (pubk b)))))
  (defrule rebind-x
    (forall ((x y text))
      (implies
        (fact rel1 x y)
        (exists ((x-0 name)) (fact rel2 x-0 y)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule fact-init-rel11
    (forall ((z strd) (n2 n1 text))
      (implies
        (and (p "init" z (idx 2)) (p "init" "n1" z n1)
          (p "init" "n2" z n2)) (fact rel1 n1 n2))))
  (defgenrule fact-init-rel20
    (forall ((z strd) (n2 n1 text))
      (implies
        (and (p "init" z (idx 2)) (p "init" "n1" z n1)
          (p "init" "n2" z n2)) (fact rel2 n1 n2))))
  (comment "Needham-Schroeder with no role origination assumptions"))

(defskeleton ns
  (vars (n1 n2 n2-0 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (defstrand init 3 (n1 n1) (n2 n2-0) (a a) (b b))
  (non-orig (privk a) (privk b))
  (uniq-orig n1)
  (comment "Double initiator point-of-view, same nonce")
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 b (pubk a)))
      (send (enc n2 (pubk b))))
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2-0 b (pubk a)))
      (send (enc n2-0 (pubk b)))))
  (label 26)
  (realized)
  (preskeleton)
  (origs (n1 (1 0)) (n1 (0 0)))
  (comment "Not a skeleton"))

(defskeleton ns
  (vars (n1 n2 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (non-orig (privk a) (privk b))
  (uniq-orig n1)
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 b (pubk a)))
      (send (enc n2 (pubk b)))))
  (label 27)
  (parent 26)
  (unrealized (0 1))
  (origs (n1 (0 0)))
  (comment "Not closed under rules"))

(defskeleton ns
  (vars (x name) (n1 n2 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (non-orig (privk a) (privk b))
  (uniq-orig n1)
  (facts (rel2 x n2) (rel1 n1 n2) (rel2 n1 n2))
  (rule fact-init-rel11 fact-init-rel20 rebind-x)
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 b (pubk a)))
      (send (enc n2 (pubk b)))))
  (label 28)
  (parent 27)
  (unrealized (0 1))
  (origs (n1 (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (x name) (n1 n2 n2-0 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (defstrand resp 2 (n2 n2-0) (n1 n1) (b b) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a) (privk b))
  (uniq-orig n1)
  (facts (rel2 x n2) (rel1 n1 n2) (rel2 n1 n2))
  (rule fact-init-rel11 fact-init-rel20 rebind-x)
  (operation nonce-test (added-strand resp 2) n1 (0 1)
    (enc n1 a (pubk b)))
  (strand-map 0)
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 b (pubk a)))
      (send (enc n2 (pubk b))))
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2-0 b (pubk a)))))
  (label 29)
  (parent 28)
  (unrealized (0 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (x name) (n1 n2 text) (a b name))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (defstrand resp 2 (n2 n2) (n1 n1) (b b) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a) (privk b))
  (uniq-orig n1)
  (facts (rel2 x n2) (rel1 n1 n2) (rel2 n1 n2))
  (rule fact-init-rel11 fact-init-rel20 rebind-x)
  (operation nonce-test (contracted (n2-0 n2)) n1 (0 1)
    (enc n1 a (pubk b)) (enc n1 n2 b (pubk a)))
  (strand-map 0 1)
  (traces
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 b (pubk a)))
      (send (enc n2 (pubk b))))
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2 b (pubk a)))))
  (label 30)
  (parent 29)
  (realized)
  (shape)
  (maps ((0 0) ((a a) (b b) (n1 n1) (n2 n2))))
  (origs (n1 (0 0))))

(comment "Nothing left to do")

(defprotocol ns basic
  (defrole init
    (vars (a b name) (n1 n2 text))
    (trace (send (enc n1 a (pubk b))) (recv (enc n1 n2 b (pubk a)))
      (send (enc n2 (pubk b))))
    (facts (rel1 n1 n2) (rel2 n1 n2)))
  (defrole resp
    (vars (b a name) (n2 n1 text))
    (trace (recv (enc n1 a (pubk b))) (send (enc n1 n2 b (pubk a)))
      (recv (enc n2 (pubk b)))))
  (defrule rebind-x
    (forall ((x y text))
      (implies
        (fact rel1 x y)
        (exists ((x-0 name)) (fact rel2 x-0 y)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule fact-init-rel11
    (forall ((z strd) (n2 n1 text))
      (implies
        (and (p "init" z (idx 2)) (p "init" "n1" z n1)
          (p "init" "n2" z n2)) (fact rel1 n1 n2))))
  (defgenrule fact-init-rel20
    (forall ((z strd) (n2 n1 text))
      (implies
        (and (p "init" z (idx 2)) (p "init" "n1" z n1)
          (p "init" "n2" z n2)) (fact rel2 n1 n2))))
  (comment "Needham-Schroeder with no role origination assumptions"))

(defskeleton ns
  (vars (n2 n1 text) (a b name))
  (defstrand resp 3 (n2 n2) (n1 n1) (b b) (a a))
  (non-orig (privk a))
  (uniq-orig n2)
  (comment "Responder point-of-view")
  (traces
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2 b (pubk a)))
      (recv (enc n2 (pubk b)))))
  (label 31)
  (unrealized (0 2))
  (origs (n2 (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton ns
  (vars (x name) (n2 n1 text) (a b name))
  (defstrand resp 3 (n2 n2) (n1 n1) (b b) (a a))
  (defstrand init 3 (n1 n1) (n2 n2) (a a) (b b))
  (precedes ((0 1) (1 1)) ((1 2) (0 2)))
  (non-orig (privk a))
  (uniq-orig n2)
  (facts (rel2 x n2) (rel1 n1 n2) (rel2 n1 n2))
  (rule fact-init-rel11 fact-init-rel20 rebind-x)
  (operation nonce-test (added-strand init 3) n2 (0 2)
    (enc n1 n2 b (pubk a)))
  (strand-map 0)
  (traces
    ((recv (enc n1 a (pubk b))) (send (enc n1 n2 b (pubk a)))
      (recv (enc n2 (pubk b))))
    ((send (enc n1 a (pubk b))) (recv (enc n1 n2 b (pubk a)))
      (send (enc n2 (pubk b)))))
  (label 32)
  (parent 31)
  (realized)
  (shape)
  (maps ((0) ((a a) (n2 n2) (b b) (n1 n1))))
  (origs (n2 (0 1))))

(comment "Nothing left to do")
