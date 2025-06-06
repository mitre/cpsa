(herald "Wide-Mouth Frog Protocol from Scyther" (bound 8)
  (comment "This protocol has an infinite number of shapes"))

(comment "CPSA 4.4.5")
(comment "All input read from tst/wide-mouth-frog-scyther.lsp")
(comment "Strand count bounded at 8")

(defprotocol wide-mouth-frog basic
  (defrole init
    (vars (a b t name) (ta text) (k skey))
    (trace (send (cat a (enc a ta b k (ltk a t))))))
  (defrole resp
    (vars (a b t name) (k skey) (tb text))
    (trace (recv (enc t tb a k (ltk b t)))))
  (defrole ks
    (vars (a b t name) (k skey) (ta tb text))
    (trace (recv (cat a (enc a ta b k (ltk a t))))
      (send (enc t tb a k (ltk b t)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton wide-mouth-frog
  (vars (k skey) (ta text) (a t b name))
  (defstrand init 1 (k k) (ta ta) (a a) (b b) (t t))
  (non-orig (ltk a t))
  (uniq-orig k)
  (traces ((send (cat a (enc a ta b k (ltk a t))))))
  (label 0)
  (realized)
  (shape)
  (maps ((0) ((a a) (t t) (k k) (b b) (ta ta))))
  (origs (k (0 0))))

(comment "Nothing left to do")

(defprotocol wide-mouth-frog basic
  (defrole init
    (vars (a b t name) (ta text) (k skey))
    (trace (send (cat a (enc a ta b k (ltk a t))))))
  (defrole resp
    (vars (a b t name) (k skey) (tb text))
    (trace (recv (enc t tb a k (ltk b t)))))
  (defrole ks
    (vars (a b t name) (k skey) (ta tb text))
    (trace (recv (cat a (enc a ta b k (ltk a t))))
      (send (enc t tb a k (ltk b t)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton wide-mouth-frog
  (vars (k skey) (tb text) (b t a name))
  (defstrand resp 1 (k k) (tb tb) (a a) (b b) (t t))
  (non-orig (ltk b t))
  (uniq-orig k)
  (traces ((recv (enc t tb a k (ltk b t)))))
  (label 1)
  (unrealized (0 0))
  (origs)
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton wide-mouth-frog
  (vars (k skey) (tb text) (b a name))
  (defstrand resp 1 (k k) (tb tb) (a a) (b b) (t b))
  (defstrand init 1 (k k) (ta tb) (a b) (b a) (t b))
  (precedes ((1 0) (0 0)))
  (non-orig (ltk b b))
  (uniq-orig k)
  (operation encryption-test (added-strand init 1)
    (enc b tb a k (ltk b b)) (0 0))
  (strand-map 0)
  (traces ((recv (enc b tb a k (ltk b b))))
    ((send (cat b (enc b tb a k (ltk b b))))))
  (label 2)
  (parent 1)
  (realized)
  (shape)
  (maps ((0) ((b b) (t b) (k k) (a a) (tb tb))))
  (origs (k (1 0))))

(defskeleton wide-mouth-frog
  (vars (k skey) (tb ta text) (b t a name))
  (defstrand resp 1 (k k) (tb tb) (a a) (b b) (t t))
  (defstrand ks 2 (k k) (ta ta) (tb tb) (a a) (b b) (t t))
  (precedes ((1 1) (0 0)))
  (non-orig (ltk b t))
  (uniq-orig k)
  (operation encryption-test (added-strand ks 2)
    (enc t tb a k (ltk b t)) (0 0))
  (strand-map 0)
  (traces ((recv (enc t tb a k (ltk b t))))
    ((recv (cat a (enc a ta b k (ltk a t))))
      (send (enc t tb a k (ltk b t)))))
  (label 3)
  (parent 1)
  (realized)
  (shape)
  (maps ((0) ((b b) (t t) (k k) (a a) (tb tb))))
  (origs))

(comment "Nothing left to do")

(defprotocol wide-mouth-frog basic
  (defrole init
    (vars (a b t name) (ta text) (k skey))
    (trace (send (cat a (enc a ta b k (ltk a t))))))
  (defrole resp
    (vars (a b t name) (k skey) (tb text))
    (trace (recv (enc t tb a k (ltk b t)))))
  (defrole ks
    (vars (a b t name) (k skey) (ta tb text))
    (trace (recv (cat a (enc a ta b k (ltk a t))))
      (send (enc t tb a k (ltk b t)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton wide-mouth-frog
  (vars (k skey) (ta tb text) (a b t name))
  (defstrand ks 2 (k k) (ta ta) (tb tb) (a a) (b b) (t t))
  (non-orig (ltk a t) (ltk b t))
  (uniq-orig k)
  (traces
    ((recv (cat a (enc a ta b k (ltk a t))))
      (send (enc t tb a k (ltk b t)))))
  (label 4)
  (unrealized (0 0))
  (origs)
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton wide-mouth-frog
  (vars (k skey) (ta tb text) (a b t name))
  (defstrand ks 2 (k k) (ta ta) (tb tb) (a a) (b b) (t t))
  (defstrand init 1 (k k) (ta ta) (a a) (b b) (t t))
  (precedes ((1 0) (0 0)))
  (non-orig (ltk a t) (ltk b t))
  (uniq-orig k)
  (operation encryption-test (added-strand init 1)
    (enc a ta b k (ltk a t)) (0 0))
  (strand-map 0)
  (traces
    ((recv (cat a (enc a ta b k (ltk a t))))
      (send (enc t tb a k (ltk b t))))
    ((send (cat a (enc a ta b k (ltk a t))))))
  (label 5)
  (parent 4)
  (realized)
  (shape)
  (maps ((0) ((a a) (b b) (t t) (k k) (ta ta) (tb tb))))
  (origs (k (1 0))))

(defskeleton wide-mouth-frog
  (vars (k skey) (ta tb ta-0 text) (b t name))
  (defstrand ks 2 (k k) (ta ta) (tb tb) (a t) (b b) (t t))
  (defstrand ks 2 (k k) (ta ta-0) (tb ta) (a b) (b t) (t t))
  (precedes ((1 1) (0 0)))
  (non-orig (ltk b t) (ltk t t))
  (uniq-orig k)
  (operation encryption-test (added-strand ks 2)
    (enc t ta b k (ltk t t)) (0 0))
  (strand-map 0)
  (traces
    ((recv (cat t (enc t ta b k (ltk t t))))
      (send (enc t tb t k (ltk b t))))
    ((recv (cat b (enc b ta-0 t k (ltk b t))))
      (send (enc t ta b k (ltk t t)))))
  (label 6)
  (parent 4)
  (unrealized (1 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton wide-mouth-frog
  (vars (k skey) (ta tb ta-0 text) (b t name))
  (defstrand ks 2 (k k) (ta ta) (tb tb) (a t) (b b) (t t))
  (defstrand ks 2 (k k) (ta ta-0) (tb ta) (a b) (b t) (t t))
  (defstrand init 1 (k k) (ta ta-0) (a b) (b t) (t t))
  (precedes ((1 1) (0 0)) ((2 0) (1 0)))
  (non-orig (ltk b t) (ltk t t))
  (uniq-orig k)
  (operation encryption-test (added-strand init 1)
    (enc b ta-0 t k (ltk b t)) (1 0))
  (strand-map 0 1)
  (traces
    ((recv (cat t (enc t ta b k (ltk t t))))
      (send (enc t tb t k (ltk b t))))
    ((recv (cat b (enc b ta-0 t k (ltk b t))))
      (send (enc t ta b k (ltk t t))))
    ((send (cat b (enc b ta-0 t k (ltk b t))))))
  (label 7)
  (parent 6)
  (realized)
  (shape)
  (maps ((0) ((a t) (b b) (t t) (k k) (ta ta) (tb tb))))
  (origs (k (2 0))))

(defskeleton wide-mouth-frog
  (vars (k skey) (ta tb ta-0 ta-1 text) (t name))
  (defstrand ks 2 (k k) (ta ta) (tb tb) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-0) (tb ta) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-1) (tb ta-0) (a t) (b t) (t t))
  (precedes ((1 1) (0 0)) ((2 1) (1 0)))
  (non-orig (ltk t t))
  (uniq-orig k)
  (operation encryption-test (added-strand ks 2)
    (enc t ta-0 t k (ltk t t)) (1 0))
  (strand-map 0 1)
  (traces
    ((recv (cat t (enc t ta t k (ltk t t))))
      (send (enc t tb t k (ltk t t))))
    ((recv (cat t (enc t ta-0 t k (ltk t t))))
      (send (enc t ta t k (ltk t t))))
    ((recv (cat t (enc t ta-1 t k (ltk t t))))
      (send (enc t ta-0 t k (ltk t t)))))
  (label 8)
  (parent 6)
  (unrealized (2 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton wide-mouth-frog
  (vars (k skey) (ta tb ta-0 ta-1 text) (t name))
  (defstrand ks 2 (k k) (ta ta) (tb tb) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-0) (tb ta) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-1) (tb ta-0) (a t) (b t) (t t))
  (defstrand init 1 (k k) (ta ta-1) (a t) (b t) (t t))
  (precedes ((1 1) (0 0)) ((2 1) (1 0)) ((3 0) (2 0)))
  (non-orig (ltk t t))
  (uniq-orig k)
  (operation encryption-test (added-strand init 1)
    (enc t ta-1 t k (ltk t t)) (2 0))
  (strand-map 0 1 2)
  (traces
    ((recv (cat t (enc t ta t k (ltk t t))))
      (send (enc t tb t k (ltk t t))))
    ((recv (cat t (enc t ta-0 t k (ltk t t))))
      (send (enc t ta t k (ltk t t))))
    ((recv (cat t (enc t ta-1 t k (ltk t t))))
      (send (enc t ta-0 t k (ltk t t))))
    ((send (cat t (enc t ta-1 t k (ltk t t))))))
  (label 9)
  (parent 8)
  (realized)
  (shape)
  (maps ((0) ((a t) (b t) (t t) (k k) (ta ta) (tb tb))))
  (origs (k (3 0))))

(defskeleton wide-mouth-frog
  (vars (k skey) (ta tb ta-0 ta-1 ta-2 text) (t name))
  (defstrand ks 2 (k k) (ta ta) (tb tb) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-0) (tb ta) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-1) (tb ta-0) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-2) (tb ta-1) (a t) (b t) (t t))
  (precedes ((1 1) (0 0)) ((2 1) (1 0)) ((3 1) (2 0)))
  (non-orig (ltk t t))
  (uniq-orig k)
  (operation encryption-test (added-strand ks 2)
    (enc t ta-1 t k (ltk t t)) (2 0))
  (strand-map 0 1 2)
  (traces
    ((recv (cat t (enc t ta t k (ltk t t))))
      (send (enc t tb t k (ltk t t))))
    ((recv (cat t (enc t ta-0 t k (ltk t t))))
      (send (enc t ta t k (ltk t t))))
    ((recv (cat t (enc t ta-1 t k (ltk t t))))
      (send (enc t ta-0 t k (ltk t t))))
    ((recv (cat t (enc t ta-2 t k (ltk t t))))
      (send (enc t ta-1 t k (ltk t t)))))
  (label 10)
  (parent 8)
  (unrealized (3 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton wide-mouth-frog
  (vars (k skey) (ta tb ta-0 ta-1 ta-2 text) (t name))
  (defstrand ks 2 (k k) (ta ta) (tb tb) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-0) (tb ta) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-1) (tb ta-0) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-2) (tb ta-1) (a t) (b t) (t t))
  (defstrand init 1 (k k) (ta ta-2) (a t) (b t) (t t))
  (precedes ((1 1) (0 0)) ((2 1) (1 0)) ((3 1) (2 0)) ((4 0) (3 0)))
  (non-orig (ltk t t))
  (uniq-orig k)
  (operation encryption-test (added-strand init 1)
    (enc t ta-2 t k (ltk t t)) (3 0))
  (strand-map 0 1 2 3)
  (traces
    ((recv (cat t (enc t ta t k (ltk t t))))
      (send (enc t tb t k (ltk t t))))
    ((recv (cat t (enc t ta-0 t k (ltk t t))))
      (send (enc t ta t k (ltk t t))))
    ((recv (cat t (enc t ta-1 t k (ltk t t))))
      (send (enc t ta-0 t k (ltk t t))))
    ((recv (cat t (enc t ta-2 t k (ltk t t))))
      (send (enc t ta-1 t k (ltk t t))))
    ((send (cat t (enc t ta-2 t k (ltk t t))))))
  (label 11)
  (parent 10)
  (realized)
  (shape)
  (maps ((0) ((a t) (b t) (t t) (k k) (ta ta) (tb tb))))
  (origs (k (4 0))))

(defskeleton wide-mouth-frog
  (vars (k skey) (ta tb ta-0 ta-1 ta-2 ta-3 text) (t name))
  (defstrand ks 2 (k k) (ta ta) (tb tb) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-0) (tb ta) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-1) (tb ta-0) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-2) (tb ta-1) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-3) (tb ta-2) (a t) (b t) (t t))
  (precedes ((1 1) (0 0)) ((2 1) (1 0)) ((3 1) (2 0)) ((4 1) (3 0)))
  (non-orig (ltk t t))
  (uniq-orig k)
  (operation encryption-test (added-strand ks 2)
    (enc t ta-2 t k (ltk t t)) (3 0))
  (strand-map 0 1 2 3)
  (traces
    ((recv (cat t (enc t ta t k (ltk t t))))
      (send (enc t tb t k (ltk t t))))
    ((recv (cat t (enc t ta-0 t k (ltk t t))))
      (send (enc t ta t k (ltk t t))))
    ((recv (cat t (enc t ta-1 t k (ltk t t))))
      (send (enc t ta-0 t k (ltk t t))))
    ((recv (cat t (enc t ta-2 t k (ltk t t))))
      (send (enc t ta-1 t k (ltk t t))))
    ((recv (cat t (enc t ta-3 t k (ltk t t))))
      (send (enc t ta-2 t k (ltk t t)))))
  (label 12)
  (parent 10)
  (unrealized (4 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton wide-mouth-frog
  (vars (k skey) (ta tb ta-0 ta-1 ta-2 ta-3 text) (t name))
  (defstrand ks 2 (k k) (ta ta) (tb tb) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-0) (tb ta) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-1) (tb ta-0) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-2) (tb ta-1) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-3) (tb ta-2) (a t) (b t) (t t))
  (defstrand init 1 (k k) (ta ta-3) (a t) (b t) (t t))
  (precedes ((1 1) (0 0)) ((2 1) (1 0)) ((3 1) (2 0)) ((4 1) (3 0))
    ((5 0) (4 0)))
  (non-orig (ltk t t))
  (uniq-orig k)
  (operation encryption-test (added-strand init 1)
    (enc t ta-3 t k (ltk t t)) (4 0))
  (strand-map 0 1 2 3 4)
  (traces
    ((recv (cat t (enc t ta t k (ltk t t))))
      (send (enc t tb t k (ltk t t))))
    ((recv (cat t (enc t ta-0 t k (ltk t t))))
      (send (enc t ta t k (ltk t t))))
    ((recv (cat t (enc t ta-1 t k (ltk t t))))
      (send (enc t ta-0 t k (ltk t t))))
    ((recv (cat t (enc t ta-2 t k (ltk t t))))
      (send (enc t ta-1 t k (ltk t t))))
    ((recv (cat t (enc t ta-3 t k (ltk t t))))
      (send (enc t ta-2 t k (ltk t t))))
    ((send (cat t (enc t ta-3 t k (ltk t t))))))
  (label 13)
  (parent 12)
  (realized)
  (shape)
  (maps ((0) ((a t) (b t) (t t) (k k) (ta ta) (tb tb))))
  (origs (k (5 0))))

(defskeleton wide-mouth-frog
  (vars (k skey) (ta tb ta-0 ta-1 ta-2 ta-3 ta-4 text) (t name))
  (defstrand ks 2 (k k) (ta ta) (tb tb) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-0) (tb ta) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-1) (tb ta-0) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-2) (tb ta-1) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-3) (tb ta-2) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-4) (tb ta-3) (a t) (b t) (t t))
  (precedes ((1 1) (0 0)) ((2 1) (1 0)) ((3 1) (2 0)) ((4 1) (3 0))
    ((5 1) (4 0)))
  (non-orig (ltk t t))
  (uniq-orig k)
  (operation encryption-test (added-strand ks 2)
    (enc t ta-3 t k (ltk t t)) (4 0))
  (strand-map 0 1 2 3 4)
  (traces
    ((recv (cat t (enc t ta t k (ltk t t))))
      (send (enc t tb t k (ltk t t))))
    ((recv (cat t (enc t ta-0 t k (ltk t t))))
      (send (enc t ta t k (ltk t t))))
    ((recv (cat t (enc t ta-1 t k (ltk t t))))
      (send (enc t ta-0 t k (ltk t t))))
    ((recv (cat t (enc t ta-2 t k (ltk t t))))
      (send (enc t ta-1 t k (ltk t t))))
    ((recv (cat t (enc t ta-3 t k (ltk t t))))
      (send (enc t ta-2 t k (ltk t t))))
    ((recv (cat t (enc t ta-4 t k (ltk t t))))
      (send (enc t ta-3 t k (ltk t t)))))
  (label 14)
  (parent 12)
  (unrealized (5 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton wide-mouth-frog
  (vars (k skey) (ta tb ta-0 ta-1 ta-2 ta-3 ta-4 text) (t name))
  (defstrand ks 2 (k k) (ta ta) (tb tb) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-0) (tb ta) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-1) (tb ta-0) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-2) (tb ta-1) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-3) (tb ta-2) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-4) (tb ta-3) (a t) (b t) (t t))
  (defstrand init 1 (k k) (ta ta-4) (a t) (b t) (t t))
  (precedes ((1 1) (0 0)) ((2 1) (1 0)) ((3 1) (2 0)) ((4 1) (3 0))
    ((5 1) (4 0)) ((6 0) (5 0)))
  (non-orig (ltk t t))
  (uniq-orig k)
  (operation encryption-test (added-strand init 1)
    (enc t ta-4 t k (ltk t t)) (5 0))
  (strand-map 0 1 2 3 4 5)
  (traces
    ((recv (cat t (enc t ta t k (ltk t t))))
      (send (enc t tb t k (ltk t t))))
    ((recv (cat t (enc t ta-0 t k (ltk t t))))
      (send (enc t ta t k (ltk t t))))
    ((recv (cat t (enc t ta-1 t k (ltk t t))))
      (send (enc t ta-0 t k (ltk t t))))
    ((recv (cat t (enc t ta-2 t k (ltk t t))))
      (send (enc t ta-1 t k (ltk t t))))
    ((recv (cat t (enc t ta-3 t k (ltk t t))))
      (send (enc t ta-2 t k (ltk t t))))
    ((recv (cat t (enc t ta-4 t k (ltk t t))))
      (send (enc t ta-3 t k (ltk t t))))
    ((send (cat t (enc t ta-4 t k (ltk t t))))))
  (label 15)
  (parent 14)
  (realized)
  (shape)
  (maps ((0) ((a t) (b t) (t t) (k k) (ta ta) (tb tb))))
  (origs (k (6 0))))

(defskeleton wide-mouth-frog
  (vars (k skey) (ta tb ta-0 ta-1 ta-2 ta-3 ta-4 ta-5 text) (t name))
  (defstrand ks 2 (k k) (ta ta) (tb tb) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-0) (tb ta) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-1) (tb ta-0) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-2) (tb ta-1) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-3) (tb ta-2) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-4) (tb ta-3) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-5) (tb ta-4) (a t) (b t) (t t))
  (precedes ((1 1) (0 0)) ((2 1) (1 0)) ((3 1) (2 0)) ((4 1) (3 0))
    ((5 1) (4 0)) ((6 1) (5 0)))
  (non-orig (ltk t t))
  (uniq-orig k)
  (operation encryption-test (added-strand ks 2)
    (enc t ta-4 t k (ltk t t)) (5 0))
  (strand-map 0 1 2 3 4 5)
  (traces
    ((recv (cat t (enc t ta t k (ltk t t))))
      (send (enc t tb t k (ltk t t))))
    ((recv (cat t (enc t ta-0 t k (ltk t t))))
      (send (enc t ta t k (ltk t t))))
    ((recv (cat t (enc t ta-1 t k (ltk t t))))
      (send (enc t ta-0 t k (ltk t t))))
    ((recv (cat t (enc t ta-2 t k (ltk t t))))
      (send (enc t ta-1 t k (ltk t t))))
    ((recv (cat t (enc t ta-3 t k (ltk t t))))
      (send (enc t ta-2 t k (ltk t t))))
    ((recv (cat t (enc t ta-4 t k (ltk t t))))
      (send (enc t ta-3 t k (ltk t t))))
    ((recv (cat t (enc t ta-5 t k (ltk t t))))
      (send (enc t ta-4 t k (ltk t t)))))
  (label 16)
  (parent 14)
  (unrealized (6 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton wide-mouth-frog
  (vars (k skey) (ta tb ta-0 ta-1 ta-2 ta-3 ta-4 ta-5 text) (t name))
  (defstrand ks 2 (k k) (ta ta) (tb tb) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-0) (tb ta) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-1) (tb ta-0) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-2) (tb ta-1) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-3) (tb ta-2) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-4) (tb ta-3) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-5) (tb ta-4) (a t) (b t) (t t))
  (defstrand init 1 (k k) (ta ta-5) (a t) (b t) (t t))
  (precedes ((1 1) (0 0)) ((2 1) (1 0)) ((3 1) (2 0)) ((4 1) (3 0))
    ((5 1) (4 0)) ((6 1) (5 0)) ((7 0) (6 0)))
  (non-orig (ltk t t))
  (uniq-orig k)
  (operation encryption-test (added-strand init 1)
    (enc t ta-5 t k (ltk t t)) (6 0))
  (strand-map 0 1 2 3 4 5 6)
  (traces
    ((recv (cat t (enc t ta t k (ltk t t))))
      (send (enc t tb t k (ltk t t))))
    ((recv (cat t (enc t ta-0 t k (ltk t t))))
      (send (enc t ta t k (ltk t t))))
    ((recv (cat t (enc t ta-1 t k (ltk t t))))
      (send (enc t ta-0 t k (ltk t t))))
    ((recv (cat t (enc t ta-2 t k (ltk t t))))
      (send (enc t ta-1 t k (ltk t t))))
    ((recv (cat t (enc t ta-3 t k (ltk t t))))
      (send (enc t ta-2 t k (ltk t t))))
    ((recv (cat t (enc t ta-4 t k (ltk t t))))
      (send (enc t ta-3 t k (ltk t t))))
    ((recv (cat t (enc t ta-5 t k (ltk t t))))
      (send (enc t ta-4 t k (ltk t t))))
    ((send (cat t (enc t ta-5 t k (ltk t t))))))
  (label 17)
  (parent 16)
  (realized)
  (shape)
  (maps ((0) ((a t) (b t) (t t) (k k) (ta ta) (tb tb))))
  (origs (k (7 0))))

(comment "Strand bound exceeded--aborting run")

(defskeleton wide-mouth-frog
  (vars (k skey) (ta tb ta-0 ta-1 ta-2 ta-3 ta-4 ta-5 ta-6 text)
    (t name))
  (defstrand ks 2 (k k) (ta ta) (tb tb) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-0) (tb ta) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-1) (tb ta-0) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-2) (tb ta-1) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-3) (tb ta-2) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-4) (tb ta-3) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-5) (tb ta-4) (a t) (b t) (t t))
  (defstrand ks 2 (k k) (ta ta-6) (tb ta-5) (a t) (b t) (t t))
  (precedes ((1 1) (0 0)) ((2 1) (1 0)) ((3 1) (2 0)) ((4 1) (3 0))
    ((5 1) (4 0)) ((6 1) (5 0)) ((7 1) (6 0)))
  (non-orig (ltk t t))
  (uniq-orig k)
  (operation encryption-test (added-strand ks 2)
    (enc t ta-5 t k (ltk t t)) (6 0))
  (strand-map 0 1 2 3 4 5 6)
  (traces
    ((recv (cat t (enc t ta t k (ltk t t))))
      (send (enc t tb t k (ltk t t))))
    ((recv (cat t (enc t ta-0 t k (ltk t t))))
      (send (enc t ta t k (ltk t t))))
    ((recv (cat t (enc t ta-1 t k (ltk t t))))
      (send (enc t ta-0 t k (ltk t t))))
    ((recv (cat t (enc t ta-2 t k (ltk t t))))
      (send (enc t ta-1 t k (ltk t t))))
    ((recv (cat t (enc t ta-3 t k (ltk t t))))
      (send (enc t ta-2 t k (ltk t t))))
    ((recv (cat t (enc t ta-4 t k (ltk t t))))
      (send (enc t ta-3 t k (ltk t t))))
    ((recv (cat t (enc t ta-5 t k (ltk t t))))
      (send (enc t ta-4 t k (ltk t t))))
    ((recv (cat t (enc t ta-6 t k (ltk t t))))
      (send (enc t ta-5 t k (ltk t t)))))
  (label 18)
  (parent 16)
  (unrealized (7 0))
  (aborted)
  (comment "aborted"))
