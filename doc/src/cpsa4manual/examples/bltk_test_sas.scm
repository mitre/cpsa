(herald "bltk Test File" (algebra diffie-hellman) (bound 12))

(comment "CPSA 4.4.0")
(comment "Coherent logic")

(comment "CPSA 4.4.0")

(comment "All input read from bltk_test.scm")

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
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

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
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defgoal test
  (forall ((n text) (a b name) (z z-0 strd))
    (implies
      (and (p "r" z 2) (p "" z-0 2) (p "r" "n" z n) (p "r" "a" z a)
        (p "r" "b" z b) (p "" "x" z-0 n) (non (bltk a b))
        (uniq-at n z 0))
      (false))))

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
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defgoal test
  (forall ((n text) (a b name) (z z-0 strd))
    (implies
      (and (p "r" z 2) (p "" z-0 2) (p "r" "n" z n) (p "r" "a" z a)
        (p "r" "b" z b) (p "" "x" z-0 n) (non (bltk a b))
        (uniq-at n z 0))
      (false))))

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
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defgoal test2
  (forall ((n text) (a b name) (z strd))
    (implies
      (and (p "r" z 2) (p "r" "n" z n) (p "r" "a" z a) (p "r" "b" z b)
        (non (ltk a b)) (uniq-at n z 0))
      (and (= b a) (p "r" "b" z a) (non (ltk a a))))))

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
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defgoal test3
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
