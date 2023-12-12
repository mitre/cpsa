(comment "CPSA 4.4.3")
(comment "All input read from tst/weird.scm")

(defprotocol weird basic
  (defrole originator (vars (k skey)) (trace (send k)) (uniq-orig k))
  (defrole guesser (vars (k skey) (a name)) (trace (send (enc a k))))
  (defrole encryptor (vars (k skey) (a name)) (trace (recv (enc a k))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton weird
  (vars (k skey) (a name))
  (defstrand originator 1 (k k))
  (defstrand guesser 1 (k k) (a a))
  (uniq-orig k)
  (traces ((send k)) ((send (enc a k))))
  (label 0)
  (realized)
  (shape)
  (maps ((0 1) ((k k) (a a))))
  (origs (k (0 0)))
  (ugens))

(comment "Nothing left to do")

(defprotocol weird basic
  (defrole originator (vars (k skey)) (trace (send k)) (uniq-orig k))
  (defrole guesser (vars (k skey) (a name)) (trace (send (enc a k))))
  (defrole encryptor (vars (k skey) (a name)) (trace (recv (enc a k))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton weird
  (vars (k skey) (a name))
  (defstrand originator 1 (k k))
  (defstrand encryptor 1 (k k) (a a))
  (uniq-orig k)
  (traces ((send k)) ((recv (enc a k))))
  (label 1)
  (unrealized (1 0))
  (origs (k (0 0)))
  (ugens)
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton weird
  (vars (k skey) (a name))
  (defstrand originator 1 (k k))
  (defstrand encryptor 1 (k k) (a a))
  (defstrand guesser 1 (k k) (a a))
  (precedes ((2 0) (1 0)))
  (uniq-orig k)
  (operation encryption-test (added-strand guesser 1) (enc a k) (1 0))
  (traces ((send k)) ((recv (enc a k))) ((send (enc a k))))
  (label 2)
  (parent 1)
  (realized)
  (shape)
  (maps ((0 1) ((k k) (a a))))
  (origs (k (0 0)))
  (ugens))

(defskeleton weird
  (vars (k skey) (a name))
  (defstrand originator 1 (k k))
  (defstrand encryptor 1 (k k) (a a))
  (deflistener k)
  (precedes ((0 0) (2 0)) ((2 1) (1 0)))
  (uniq-orig k)
  (operation encryption-test (added-listener k) (enc a k) (1 0))
  (traces ((send k)) ((recv (enc a k))) ((recv k) (send k)))
  (label 3)
  (parent 1)
  (realized)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton weird
  (vars (k skey) (a name))
  (defstrand originator 1 (k k))
  (defstrand encryptor 1 (k k) (a a))
  (precedes ((0 0) (1 0)))
  (uniq-orig k)
  (operation generalization deleted (2 0))
  (traces ((send k)) ((recv (enc a k))))
  (label 4)
  (parent 3)
  (realized)
  (shape)
  (maps ((0 1) ((k k) (a a))))
  (origs (k (0 0)))
  (ugens))

(comment "Nothing left to do")

(defprotocol weird basic
  (defrole originator (vars (k skey)) (trace (send k)) (uniq-orig k))
  (defrole guesser (vars (k skey) (a name)) (trace (send (enc a k))))
  (defrole encryptor (vars (k skey) (a name)) (trace (recv (enc a k))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton weird
  (vars (k skey) (a name))
  (defstrand originator 1 (k k))
  (defstrand encryptor 1 (k k) (a a))
  (precedes ((0 0) (1 0)))
  (uniq-orig k)
  (traces ((send k)) ((recv (enc a k))))
  (label 5)
  (realized)
  (shape)
  (maps ((0 1) ((k k) (a a))))
  (origs (k (0 0)))
  (ugens))

(comment "Nothing left to do")

(defprotocol weird-gen basic
  (defrole originator (vars (k skey)) (trace (send k)) (uniq-gen k))
  (defrole guesser (vars (k skey) (a name)) (trace (send (enc a k))))
  (defrole encryptor (vars (k skey) (a name)) (trace (recv (enc a k))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton weird-gen
  (vars (k skey) (a name))
  (defstrand originator 1 (k k))
  (defstrand guesser 1 (k k) (a a))
  (uniq-gen k)
  (traces ((send k)) ((send (enc a k))))
  (label 6)
  (realized)
  (dead)
  (origs)
  (ugens (k (1 0)) (k (0 0)))
  (comment "Input cannot be made into a skeleton--nothing to do"))

(defprotocol weird-gen basic
  (defrole originator (vars (k skey)) (trace (send k)) (uniq-gen k))
  (defrole guesser (vars (k skey) (a name)) (trace (send (enc a k))))
  (defrole encryptor (vars (k skey) (a name)) (trace (recv (enc a k))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton weird-gen
  (vars (k skey) (a name))
  (defstrand originator 1 (k k))
  (defstrand encryptor 1 (k k) (a a))
  (uniq-gen k)
  (traces ((send k)) ((recv (enc a k))))
  (label 7)
  (unrealized (1 0))
  (preskeleton)
  (origs)
  (ugens (k (0 0)))
  (comment "Not a skeleton"))

(defskeleton weird-gen
  (vars (k skey) (a name))
  (defstrand originator 1 (k k))
  (defstrand encryptor 1 (k k) (a a))
  (precedes ((0 0) (1 0)))
  (uniq-gen k)
  (traces ((send k)) ((recv (enc a k))))
  (label 8)
  (parent 7)
  (realized)
  (shape)
  (maps ((0 1) ((k k) (a a))))
  (origs)
  (ugens (k (0 0))))

(comment "Nothing left to do")

(defprotocol weird-gen basic
  (defrole originator (vars (k skey)) (trace (send k)) (uniq-gen k))
  (defrole guesser (vars (k skey) (a name)) (trace (send (enc a k))))
  (defrole encryptor (vars (k skey) (a name)) (trace (recv (enc a k))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton weird-gen
  (vars (k skey) (a name))
  (defstrand originator 1 (k k))
  (defstrand encryptor 1 (k k) (a a))
  (precedes ((0 0) (1 0)))
  (uniq-gen k)
  (traces ((send k)) ((recv (enc a k))))
  (label 9)
  (realized)
  (shape)
  (maps ((0 1) ((k k) (a a))))
  (origs)
  (ugens (k (0 0))))

(comment "Nothing left to do")
