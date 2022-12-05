(comment "CPSA 4.3.1")
(comment "Extracted shapes")

(herald "Plain diffie-hellman protocol with challenge-response"
  (algebra diffie-hellman))

(comment "CPSA 4.3.1")

(comment "All input read from plaindh.scm")

(defprotocol plaindh diffie-hellman
  (defrole init
    (vars (x rndx) (h base) (n text))
    (trace (send (exp (gen) x)) (recv h) (send (enc n (exp h x)))
      (recv n))
    (uniq-orig n)
    (uniq-gen x))
  (defrole resp
    (vars (y rndx) (h base) (n text))
    (trace (recv h) (send (exp (gen) y)) (recv (enc n (exp h y)))
      (send n))
    (uniq-gen y))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (comment "Diffie-hellman key exchange followed by an encryption"))

(defskeleton plaindh
  (vars (n text) (h base) (x rndx))
  (defstrand init 4 (n n) (h h) (x x))
  (uniq-orig n)
  (uniq-gen x)
  (traces
    ((send (exp (gen) x)) (recv h) (send (enc n (exp h x))) (recv n)))
  (label 0)
  (unrealized (0 3))
  (origs (n (0 2)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton plaindh
  (vars (n text) (y x rndx))
  (defstrand init 4 (n n) (h (exp (gen) y)) (x x))
  (uniq-orig n)
  (uniq-gen y x)
  (operation generalization deleted (1 0))
  (traces
    ((send (exp (gen) x)) (recv (exp (gen) y))
      (send (enc n (exp (gen) (mul y x)))) (recv n)))
  (label 13)
  (parent 0)
  (realized)
  (shape)
  (maps ((0) ((x x) (h (exp (gen) y)) (n n))))
  (origs (n (0 2))))

(defskeleton plaindh
  (vars (n text) (x rndx))
  (defstrand init 4 (n n) (h (gen)) (x x))
  (uniq-orig n)
  (uniq-gen x)
  (operation generalization deleted (1 0))
  (traces
    ((send (exp (gen) x)) (recv (gen)) (send (enc n (exp (gen) x)))
      (recv n)))
  (label 26)
  (parent 0)
  (realized)
  (shape)
  (maps ((0) ((x x) (h (gen)) (n n))))
  (origs (n (0 2))))

(defskeleton plaindh
  (vars (n text) (y rndx) (w expt) (x rndx))
  (defstrand init 4 (n n) (h (exp (gen) (mul y w))) (x x))
  (deflistener (cat (exp (gen) x) w))
  (precedes ((0 0) (1 0)))
  (uniq-orig n)
  (uniq-gen y x)
  (precur (1 0))
  (operation generalization deleted (1 1))
  (traces
    ((send (exp (gen) x)) (recv (exp (gen) (mul y w)))
      (send (enc n (exp (gen) (mul y w x)))) (recv n))
    ((recv (cat (exp (gen) x) w))))
  (label 65)
  (parent 0)
  (realized)
  (shape)
  (maps ((0) ((x x) (h (exp (gen) (mul y w))) (n n))))
  (origs (n (0 2))))

(defskeleton plaindh
  (vars (n text) (w expt) (x rndx))
  (defstrand init 4 (n n) (h (exp (gen) w)) (x x))
  (uniq-orig n)
  (uniq-gen x)
  (operation generalization deleted (1 0))
  (traces
    ((send (exp (gen) x)) (recv (exp (gen) w))
      (send (enc n (exp (gen) (mul w x)))) (recv n)))
  (label 71)
  (parent 0)
  (realized)
  (shape)
  (maps ((0) ((x x) (h (exp (gen) w)) (n n))))
  (origs (n (0 2))))

(comment "Nothing left to do")
