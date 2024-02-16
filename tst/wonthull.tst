(herald wonthull (bound 9))

(comment "CPSA 4.4.3")
(comment "All input read from tst/wonthull.scm")
(comment "Strand count bounded at 9")

(defprotocol wonthull basic
  (defrole init
    (vars (a name) (x1 x2 x3 x4 text))
    (trace (send (cat (enc x1 x2 (pubk a)) (enc x3 x2 (pubk a))))
      (recv (enc "okay" x3 x4 (pubk a))))
    (non-orig (privk a))
    (uniq-orig x1 x2 x3))
  (defrole resp
    (vars (a name) (y1 y2 y3 text))
    (trace (recv (enc y1 y2 (pubk a)))
      (send (enc "okay" y3 y1 (pubk a)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton wonthull
  (vars (x1 x2 x3 x4 text) (a name))
  (defstrand init 2 (x1 x1) (x2 x2) (x3 x3) (x4 x4) (a a))
  (non-orig (privk a))
  (uniq-orig x1 x2 x3)
  (traces
    ((send (cat (enc x1 x2 (pubk a)) (enc x3 x2 (pubk a))))
      (recv (enc "okay" x3 x4 (pubk a)))))
  (label 0)
  (unrealized (0 1))
  (origs (x3 (0 0)) (x2 (0 0)) (x1 (0 0)))
  (ugens)
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton wonthull
  (vars (x1 x2 x4 text) (a name))
  (defstrand init 2 (x1 x1) (x2 x2) (x3 x2) (x4 x4) (a a))
  (non-orig (privk a))
  (uniq-orig x1 x2)
  (operation nonce-test (displaced 1 0 init 1) x3 (0 1)
    (enc x3 x2 (pubk a)))
  (traces
    ((send (cat (enc x1 x2 (pubk a)) (enc x2 x2 (pubk a))))
      (recv (enc "okay" x2 x4 (pubk a)))))
  (label 1)
  (parent 0)
  (unrealized (0 1))
  (origs (x1 (0 0)) (x2 (0 0)))
  (ugens)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton wonthull
  (vars (x1 x2 x3 x4 y3 text) (a name))
  (defstrand init 2 (x1 x1) (x2 x2) (x3 x3) (x4 x4) (a a))
  (defstrand resp 2 (y1 x3) (y2 x2) (y3 y3) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a))
  (uniq-orig x1 x2 x3)
  (operation nonce-test (added-strand resp 2) x3 (0 1)
    (enc x3 x2 (pubk a)))
  (traces
    ((send (cat (enc x1 x2 (pubk a)) (enc x3 x2 (pubk a))))
      (recv (enc "okay" x3 x4 (pubk a))))
    ((recv (enc x3 x2 (pubk a))) (send (enc "okay" y3 x3 (pubk a)))))
  (label 2)
  (parent 0)
  (seen 3)
  (seen-opts
    (3
      (operation nonce-test (displaced 2 0 init 1) x3 (0 1)
        (enc "okay" y3 x3 (pubk a)) (enc x3 x2 (pubk a)))))
  (unrealized (0 1))
  (comment "2 in cohort - 1 not yet seen"))

(defskeleton wonthull
  (vars (x1 x2 x4 y3 text) (a name))
  (defstrand init 2 (x1 x1) (x2 x2) (x3 x2) (x4 x4) (a a))
  (defstrand resp 2 (y1 x2) (y2 x2) (y3 y3) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a))
  (uniq-orig x1 x2)
  (operation nonce-test (added-strand resp 2) x2 (0 1)
    (enc x1 x2 (pubk a)) (enc x2 x2 (pubk a)))
  (traces
    ((send (cat (enc x1 x2 (pubk a)) (enc x2 x2 (pubk a))))
      (recv (enc "okay" x2 x4 (pubk a))))
    ((recv (enc x2 x2 (pubk a))) (send (enc "okay" y3 x2 (pubk a)))))
  (label 3)
  (parent 1)
  (unrealized (0 1))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton wonthull
  (vars (x1 x2 y3 text) (a name))
  (defstrand init 2 (x1 x1) (x2 x2) (x3 y3) (x4 y3) (a a))
  (defstrand resp 2 (y1 y3) (y2 x2) (y3 y3) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a))
  (uniq-orig x1 x2 y3)
  (operation nonce-test (contracted (x3 y3) (x4 y3)) y3 (0 1)
    (enc "okay" y3 y3 (pubk a)) (enc y3 x2 (pubk a)))
  (traces
    ((send (cat (enc x1 x2 (pubk a)) (enc y3 x2 (pubk a))))
      (recv (enc "okay" y3 y3 (pubk a))))
    ((recv (enc y3 x2 (pubk a))) (send (enc "okay" y3 y3 (pubk a)))))
  (label 4)
  (parent 2)
  (realized)
  (shape)
  (maps ((0) ((a a) (x1 x1) (x2 x2) (x3 y3) (x4 y3))))
  (origs (y3 (0 0)) (x2 (0 0)) (x1 (0 0)))
  (ugens))

(defskeleton wonthull
  (vars (x1 y3 text) (a name))
  (defstrand init 2 (x1 x1) (x2 y3) (x3 y3) (x4 y3) (a a))
  (defstrand resp 2 (y1 y3) (y2 y3) (y3 y3) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a))
  (uniq-orig x1 y3)
  (operation nonce-test (contracted (x2 y3) (x4 y3)) y3 (0 1)
    (enc "okay" y3 y3 (pubk a)) (enc x1 y3 (pubk a))
    (enc y3 y3 (pubk a)))
  (traces
    ((send (cat (enc x1 y3 (pubk a)) (enc y3 y3 (pubk a))))
      (recv (enc "okay" y3 y3 (pubk a))))
    ((recv (enc y3 y3 (pubk a))) (send (enc "okay" y3 y3 (pubk a)))))
  (label 5)
  (parent 3)
  (seen 4)
  (seen-opts (4 (operation generalization separated y3-0)))
  (realized)
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton wonthull
  (vars (x1 x2 x4 y3 text) (a name))
  (defstrand init 2 (x1 x1) (x2 x2) (x3 x2) (x4 x4) (a a))
  (defstrand resp 2 (y1 x2) (y2 x2) (y3 y3) (a a))
  (defstrand resp 2 (y1 x2) (y2 x2) (y3 x2) (a a))
  (precedes ((0 0) (1 0)) ((0 0) (2 0)) ((1 1) (0 1)) ((2 1) (0 1)))
  (non-orig (privk a))
  (uniq-orig x1 x2)
  (operation nonce-test (added-strand resp 2) x2 (0 1)
    (enc "okay" y3 x2 (pubk a)) (enc x1 x2 (pubk a))
    (enc x2 x2 (pubk a)))
  (traces
    ((send (cat (enc x1 x2 (pubk a)) (enc x2 x2 (pubk a))))
      (recv (enc "okay" x2 x4 (pubk a))))
    ((recv (enc x2 x2 (pubk a))) (send (enc "okay" y3 x2 (pubk a))))
    ((recv (enc x2 x2 (pubk a))) (send (enc "okay" x2 x2 (pubk a)))))
  (label 6)
  (parent 3)
  (unrealized (0 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton wonthull
  (vars (x1 x2 y3 text) (a name))
  (defstrand init 2 (x1 x1) (x2 x2) (x3 x2) (x4 x2) (a a))
  (defstrand resp 2 (y1 x2) (y2 x2) (y3 y3) (a a))
  (defstrand resp 2 (y1 x2) (y2 x2) (y3 x2) (a a))
  (precedes ((0 0) (1 0)) ((0 0) (2 0)) ((1 1) (0 1)) ((2 1) (0 1)))
  (non-orig (privk a))
  (uniq-orig x1 x2)
  (operation nonce-test (contracted (x4 x2)) x2 (0 1)
    (enc "okay" x2 x2 (pubk a)) (enc "okay" y3 x2 (pubk a))
    (enc x1 x2 (pubk a)) (enc x2 x2 (pubk a)))
  (traces
    ((send (cat (enc x1 x2 (pubk a)) (enc x2 x2 (pubk a))))
      (recv (enc "okay" x2 x2 (pubk a))))
    ((recv (enc x2 x2 (pubk a))) (send (enc "okay" y3 x2 (pubk a))))
    ((recv (enc x2 x2 (pubk a))) (send (enc "okay" x2 x2 (pubk a)))))
  (label 7)
  (parent 6)
  (seen 5)
  (seen-opts (5 (operation generalization deleted (1 0))))
  (realized)
  (comment "1 in cohort - 0 not yet seen"))

(comment "Nothing left to do")

(defprotocol wonthull basic
  (defrole init
    (vars (a name) (x1 x2 x3 x4 text))
    (trace (send (cat (enc x1 x2 (pubk a)) (enc x3 x2 (pubk a))))
      (recv (enc "okay" x3 x4 (pubk a))))
    (non-orig (privk a))
    (uniq-orig x1 x2 x3))
  (defrole resp
    (vars (a name) (y1 y2 y3 text))
    (trace (recv (enc y1 y2 (pubk a)))
      (send (enc "okay" y3 y1 (pubk a)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton wonthull
  (vars (x1 x3 text) (a name))
  (defstrand init 2 (x1 x1) (x2 x3) (x3 x3) (x4 x1) (a a))
  (defstrand resp 2 (y1 x1) (y2 x3) (y3 x3) (a a))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk a))
  (uniq-orig x1 x3)
  (traces
    ((send (cat (enc x1 x3 (pubk a)) (enc x3 x3 (pubk a))))
      (recv (enc "okay" x3 x1 (pubk a))))
    ((recv (enc x1 x3 (pubk a))) (send (enc "okay" x3 x1 (pubk a)))))
  (label 8)
  (realized)
  (shape)
  (maps ((0 1) ((a a) (x1 x1) (x3 x3))))
  (origs (x3 (0 0)) (x1 (0 0)))
  (ugens))

(comment "Nothing left to do")
