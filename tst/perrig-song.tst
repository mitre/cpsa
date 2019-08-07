(herald perrig-song)

(comment "CPSA 4.1.2")
(comment "All input read from perrig-song.scm")

(defprotocol perrig-song basic
  (defrole init
    (vars (na nb text) (a b name) (c chan))
    (trace (send na) (recv c (cat na nb a b)) (send nb)))
  (defrole resp
    (vars (na nb text) (a b name) (c chan))
    (trace (recv na) (send c (cat na nb a b)) (recv nb))))

(defskeleton perrig-song
  (vars (na nb text) (a b name) (c chan))
  (defstrand init 2 (na na) (nb nb) (a a) (b b) (c c))
  (uniq-orig na)
  (auth c)
  (traces ((send na) (recv c (cat na nb a b))))
  (label 0)
  (unrealized (0 1))
  (origs (na (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton perrig-song
  (vars (na nb text) (a b name) (c chan))
  (defstrand init 2 (na na) (nb nb) (a a) (b b) (c c))
  (defstrand resp 2 (na na) (nb nb) (a a) (b b) (c c))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (uniq-orig na)
  (auth c)
  (operation nonce-test (added-strand resp 2) (ch-msg c (cat na nb a b))
    (0 1))
  (traces ((send na) (recv c (cat na nb a b)))
    ((recv na) (send c (cat na nb a b))))
  (label 1)
  (parent 0)
  (unrealized)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton perrig-song
  (vars (na nb text) (a b name) (c c-0 chan))
  (defstrand init 2 (na na) (nb nb) (a a) (b b) (c c-0))
  (defstrand resp 2 (na na) (nb nb) (a a) (b b) (c c))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (uniq-orig na)
  (auth c)
  (operation generalization separated c-0)
  (traces ((send na) (recv c-0 (cat na nb a b)))
    ((recv na) (send c (cat na nb a b))))
  (label 2)
  (parent 1)
  (seen 0)
  (unrealized)
  (comment "1 in cohort - 0 not yet seen"))

(comment "Nothing left to do")

(defprotocol perrig-song basic
  (defrole init
    (vars (na nb text) (a b name) (c chan))
    (trace (send na) (recv c (cat na nb a b)) (send nb)))
  (defrole resp
    (vars (na nb text) (a b name) (c chan))
    (trace (recv na) (send c (cat na nb a b)) (recv nb))))

(defskeleton perrig-song
  (vars (nb na text) (a b name) (c chan))
  (defstrand resp 3 (na na) (nb nb) (a a) (b b) (c c))
  (uniq-orig nb)
  (conf c)
  (traces ((recv na) (send c (cat na nb a b)) (recv nb)))
  (label 3)
  (unrealized (0 2))
  (origs (nb (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton perrig-song
  (vars (nb na text) (a b name) (c chan))
  (defstrand resp 3 (na na) (nb nb) (a a) (b b) (c c))
  (defstrand init 3 (na na) (nb nb) (a a) (b b) (c c))
  (precedes ((0 1) (1 1)) ((1 2) (0 2)))
  (uniq-orig nb)
  (conf c)
  (operation nonce-test (added-strand init 3) nb (0 2)
    (ch-msg c (cat na nb a b)))
  (traces ((recv na) (send c (cat na nb a b)) (recv nb))
    ((send na) (recv c (cat na nb a b)) (send nb)))
  (label 4)
  (parent 3)
  (unrealized)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton perrig-song
  (vars (nb na text) (a b name) (c c-0 chan))
  (defstrand resp 3 (na na) (nb nb) (a a) (b b) (c c-0))
  (defstrand init 3 (na na) (nb nb) (a a) (b b) (c c))
  (precedes ((0 1) (1 1)) ((1 2) (0 2)))
  (uniq-orig nb)
  (conf c)
  (operation generalization separated c-0)
  (traces ((recv na) (send c-0 (cat na nb a b)) (recv nb))
    ((send na) (recv c (cat na nb a b)) (send nb)))
  (label 5)
  (parent 4)
  (seen 3)
  (unrealized)
  (comment "1 in cohort - 0 not yet seen"))

(comment "Nothing left to do")

(defprotocol perrig-song basic
  (defrole init
    (vars (na nb text) (a b name) (c chan))
    (trace (send na) (recv c (cat na nb a b)) (send nb)))
  (defrole resp
    (vars (na nb text) (a b name) (c chan))
    (trace (recv na) (send c (cat na nb a b)) (recv nb))))

(defskeleton perrig-song
  (vars (na nb text) (a b name) (c chan))
  (defstrand init 2 (na na) (nb nb) (a a) (b b) (c c))
  (uniq-orig na)
  (conf c)
  (traces ((send na) (recv c (cat na nb a b))))
  (label 6)
  (unrealized)
  (shape)
  (maps ((0) ((na na) (c c) (nb nb) (a a) (b b))))
  (origs (na (0 0))))

(comment "Nothing left to do")

(defprotocol perrig-song basic
  (defrole init
    (vars (na nb text) (a b name) (c chan))
    (trace (send na) (recv c (cat na nb a b)) (send nb)))
  (defrole resp
    (vars (na nb text) (a b name) (c chan))
    (trace (recv na) (send c (cat na nb a b)) (recv nb))))

(defskeleton perrig-song
  (vars (nb na text) (a b name) (c chan))
  (defstrand resp 3 (na na) (nb nb) (a a) (b b) (c c))
  (uniq-orig nb)
  (auth c)
  (traces ((recv na) (send c (cat na nb a b)) (recv nb)))
  (label 7)
  (unrealized)
  (shape)
  (maps ((0) ((nb nb) (c c) (na na) (a a) (b b))))
  (origs (nb (0 1))))

(comment "Nothing left to do")
