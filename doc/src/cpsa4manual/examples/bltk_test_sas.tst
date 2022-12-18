(herald "bltk Test File" (algebra diffie-hellman) (bound 12))

(comment "CPSA 4.4.0")
(comment "All input read from bltk_test_sas.scm")
(comment "Strand count bounded at 12")

(defprotocol test diffie-hellman
  (defrole r
    (vars (a b name) (n text))
    (trace (send (enc n (bltk a b))) (recv (enc n (bltk a b))))
    (uniq-orig n))
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
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton test
  (vars (n text) (a b name))
  (deflistener n)
  (defstrand r 2 (n n) (a a) (b b))
  (non-orig (bltk a b))
  (uniq-orig n)
  (goals
    (forall ((n text) (a b name) (z z-0 strd))
      (implies
        (and (p "r" z 2) (p "" z-0 2) (p "r" "n" z n) (p "r" "a" z a)
          (p "r" "b" z b) (p "" "x" z-0 n) (non (bltk a b))
          (uniq-at n z 0)) (false))))
  (traces ((recv n) (send n))
    ((send (enc n (bltk a b))) (recv (enc n (bltk a b)))))
  (label 0)
  (unrealized (0 0))
  (preskeleton)
  (origs (n (1 0)))
  (comment "Not a skeleton"))

(defskeleton test
  (vars (n text) (a b name))
  (deflistener n)
  (defstrand r 2 (n n) (a a) (b b))
  (precedes ((1 0) (0 0)))
  (non-orig (bltk a b))
  (uniq-orig n)
  (traces ((recv n) (send n))
    ((send (enc n (bltk a b))) (recv (enc n (bltk a b)))))
  (label 1)
  (parent 0)
  (unrealized (0 0))
  (dead)
  (origs (n (1 0)))
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol test diffie-hellman
  (defrole r
    (vars (a b name) (n text))
    (trace (send (enc n (bltk a b))) (recv (enc n (bltk a b))))
    (uniq-orig n))
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
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton test
  (vars (n text) (a b name))
  (deflistener n)
  (defstrand r 2 (n n) (a a) (b b))
  (non-orig (bltk a b))
  (uniq-orig n)
  (goals
    (forall ((n text) (a b name) (z z-0 strd))
      (implies
        (and (p "r" z 2) (p "" z-0 2) (p "r" "n" z n) (p "r" "a" z a)
          (p "r" "b" z b) (p "" "x" z-0 n) (non (bltk a b))
          (uniq-at n z 0)) (false))))
  (traces ((recv n) (send n))
    ((send (enc n (bltk a b))) (recv (enc n (bltk a b)))))
  (label 2)
  (unrealized (0 0))
  (preskeleton)
  (origs (n (1 0)))
  (comment "Not a skeleton"))

(defskeleton test
  (vars (n text) (a b name))
  (deflistener n)
  (defstrand r 2 (n n) (a a) (b b))
  (precedes ((1 0) (0 0)))
  (non-orig (bltk a b))
  (uniq-orig n)
  (traces ((recv n) (send n))
    ((send (enc n (bltk a b))) (recv (enc n (bltk a b)))))
  (label 3)
  (parent 2)
  (unrealized (0 0))
  (dead)
  (origs (n (1 0)))
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol test2 diffie-hellman
  (defrole r
    (vars (a b name) (n text))
    (trace (send (enc n (ltk a b))) (recv (enc n (ltk b a))))
    (uniq-orig n))
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
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton test2
  (vars (n text) (a b name))
  (defstrand r 2 (n n) (a a) (b b))
  (non-orig (ltk a b))
  (uniq-orig n)
  (goals
    (forall ((n text) (a b name) (z strd))
      (implies
        (and (p "r" z 2) (p "r" "n" z n) (p "r" "a" z a) (p "r" "b" z b)
          (non (ltk a b)) (uniq-at n z 0))
        (and (= b a) (p "r" "b" z a) (non (ltk a a))))))
  (traces ((send (enc n (ltk a b))) (recv (enc n (ltk b a)))))
  (label 4)
  (unrealized (0 1))
  (origs (n (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton test2
  (vars (n text) (a name))
  (defstrand r 2 (n n) (a a) (b a))
  (non-orig (ltk a a))
  (uniq-orig n)
  (operation nonce-test (contracted (b a)) n (0 1) (enc n (ltk a a)))
  (traces ((send (enc n (ltk a a))) (recv (enc n (ltk a a)))))
  (label 5)
  (parent 4)
  (realized)
  (shape)
  (satisfies yes)
  (maps ((0) ((n n) (a a) (b a))))
  (origs (n (0 0))))

(comment "Nothing left to do")

(defprotocol test3 diffie-hellman
  (defrole recvr
    (vars (a b name) (n text))
    (trace (send (cat "i am" a "you are" b)) (recv (enc n (bltk a b)))))
  (defrole sender
    (vars (a b name) (n text))
    (trace (send (cat "i am" b "you are" a)) (send (enc n (bltk a b))))
    (uniq-orig n))
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
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton test3
  (vars (n text) (a b name))
  (defstrand recvr 2 (n n) (a a) (b b))
  (non-orig (bltk a b))
  (goals
    (forall ((n text) (a b name) (z strd))
      (implies
        (and (p "recvr" z 2) (p "recvr" "n" z n) (p "recvr" "a" z a)
          (p "recvr" "b" z b) (non (bltk a b)))
        (or
          (exists ((z-0 strd))
            (and (p "sender" z-0 2) (p "sender" "n" z-0 n)
              (p "sender" "a" z-0 b) (p "sender" "b" z-0 a)
              (prec z-0 1 z 1) (uniq-at n z-0 1)))
          (exists ((z-0 strd))
            (and (p "sender" z-0 2) (p "sender" "n" z-0 n)
              (p "sender" "a" z-0 a) (p "sender" "b" z-0 b)
              (prec z-0 1 z 1) (uniq-at n z-0 1)))))))
  (traces ((send (cat "i am" a "you are" b)) (recv (enc n (bltk a b)))))
  (label 6)
  (unrealized (0 1))
  (origs)
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton test3
  (vars (n text) (a b name))
  (defstrand recvr 2 (n n) (a a) (b b))
  (defstrand sender 2 (n n) (a b) (b a))
  (precedes ((1 1) (0 1)))
  (non-orig (bltk a b))
  (uniq-orig n)
  (operation encryption-test (added-strand sender 2) (enc n (bltk a b))
    (0 1))
  (traces ((send (cat "i am" a "you are" b)) (recv (enc n (bltk a b))))
    ((send (cat "i am" a "you are" b)) (send (enc n (bltk a b)))))
  (label 7)
  (parent 6)
  (realized)
  (shape)
  (satisfies yes)
  (maps ((0) ((n n) (a a) (b b))))
  (origs (n (1 1))))

(defskeleton test3
  (vars (n text) (a b name))
  (defstrand recvr 2 (n n) (a a) (b b))
  (defstrand sender 2 (n n) (a a) (b b))
  (precedes ((1 1) (0 1)))
  (non-orig (bltk a b))
  (uniq-orig n)
  (operation encryption-test (added-strand sender 2) (enc n (bltk a b))
    (0 1))
  (traces ((send (cat "i am" a "you are" b)) (recv (enc n (bltk a b))))
    ((send (cat "i am" b "you are" a)) (send (enc n (bltk a b)))))
  (label 8)
  (parent 6)
  (realized)
  (shape)
  (satisfies yes)
  (maps ((0) ((n n) (a a) (b b))))
  (origs (n (1 1))))

(comment "Nothing left to do")
