(herald "Plain diffie-hellman protocol with challenge-response"
  (algebra diffie-hellman))

(comment "CPSA 4.4.0")
(comment "Coherent logic")

(comment "CPSA 4.4.0")

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

(defgoal plaindh
  (forall ((n text) (h base) (x rndx) (z strd))
    (implies
      (and (p "init" z 4) (p "init" "n" z n) (p "init" "h" z h)
        (p "init" "x" z x) (ugen x) (uniq-at n z 2))
      (or
        (exists ((y rndx))
          (and (= h (exp (gen) y)) (p "init" "h" z (exp (gen) y))))
        (and (= h (gen)) (p "init" "h" z (gen)))
        (exists ((y rndx) (w expt))
          (and (= h (exp (gen) (mul y w)))
            (p "init" "h" z (exp (gen) (mul y w)))))))))
