(herald tickle-unique)

(comment "CPSA 4.4.5")
(comment "All input read from tst/tickle-unique.scm")

(defprotocol tickle basic
  (defrole init
    (vars (a b name) (na nb text))
    (trace (send (enc a na (pubk b))) (recv (enc b na na nb (pubk a)))
      (send nb))
    (uniq-orig na))
  (defrole resp
    (vars (a b name) (na nb0 nb text))
    (trace (recv (enc a na (pubk b))) (send (enc b na nb0 nb (pubk a)))
      (recv nb)))
  (defrule uniq-tickle
    (forall ((z strd) (nb0 text))
      (implies
        (and (fact guard-me) (p "resp" z (idx 2))
          (p "resp" "nb0" z nb0))
        (uniq nb0))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton tickle
  (vars (nb0 nb na text) (a b name))
  (defstrand resp 3 (na na) (nb0 nb0) (nb nb) (a a) (b b))
  (non-orig (privk a))
  (uniq-orig nb)
  (traces
    ((recv (enc a na (pubk b))) (send (enc b na nb0 nb (pubk a)))
      (recv nb)))
  (label 0)
  (unrealized (0 2))
  (origs (nb (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton tickle
  (vars (nb0 nb text) (a b name))
  (defstrand resp 3 (na nb0) (nb0 nb0) (nb nb) (a a) (b b))
  (defstrand init 3 (na nb0) (nb nb) (a a) (b b))
  (precedes ((0 1) (1 1)) ((1 0) (0 0)) ((1 2) (0 2)))
  (non-orig (privk a))
  (uniq-orig nb0 nb)
  (operation nonce-test (added-strand init 3) nb (0 2)
    (enc b nb0 nb0 nb (pubk a)))
  (strand-map 0)
  (traces
    ((recv (enc a nb0 (pubk b))) (send (enc b nb0 nb0 nb (pubk a)))
      (recv nb))
    ((send (enc a nb0 (pubk b))) (recv (enc b nb0 nb0 nb (pubk a)))
      (send nb)))
  (label 1)
  (parent 0)
  (realized)
  (shape)
  (maps ((0) ((a a) (b b) (nb0 nb0) (nb nb) (na nb0))))
  (origs (nb0 (1 0)) (nb (0 1))))

(comment "Nothing left to do")

(defprotocol tickle basic
  (defrole init
    (vars (a b name) (na nb text))
    (trace (send (enc a na (pubk b))) (recv (enc b na na nb (pubk a)))
      (send nb))
    (uniq-orig na))
  (defrole resp
    (vars (a b name) (na nb0 nb text))
    (trace (recv (enc a na (pubk b))) (send (enc b na nb0 nb (pubk a)))
      (recv nb)))
  (defrule uniq-tickle
    (forall ((z strd) (nb0 text))
      (implies
        (and (fact guard-me) (p "resp" z (idx 2))
          (p "resp" "nb0" z nb0))
        (uniq nb0))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton tickle
  (vars (nb0 nb na text) (a b name))
  (defstrand resp 3 (na na) (nb0 nb0) (nb nb) (a a) (b b))
  (non-orig (privk a))
  (uniq-orig nb)
  (facts (guard-me))
  (traces
    ((recv (enc a na (pubk b))) (send (enc b na nb0 nb (pubk a)))
      (recv nb)))
  (label 2)
  (unrealized (0 2))
  (origs (nb (0 1)))
  (comment "Not closed under rules"))

(defskeleton tickle
  (vars (nb0 nb na text) (a b name))
  (defstrand resp 3 (na na) (nb0 nb0) (nb nb) (a a) (b b))
  (non-orig (privk a))
  (uniq-orig nb0 nb)
  (facts (guard-me))
  (rule uniq-tickle)
  (traces
    ((recv (enc a na (pubk b))) (send (enc b na nb0 nb (pubk a)))
      (recv nb)))
  (label 3)
  (parent 2)
  (unrealized (0 2))
  (dead)
  (origs (nb0 (0 1)) (nb (0 1)))
  (comment "empty cohort"))

(comment "Nothing left to do")
