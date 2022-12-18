(herald "Otway-Rees Protocol"
  (comment "Standard version using variables of sort mesg"))

(comment "CPSA 4.4.0")
(comment "Coherent logic")

(comment "CPSA 4.4.0")

(comment "All input read from or.scm")

(defprotocol or basic
  (defrole init
    (vars (a b s name) (na text) (k skey) (m text))
    (trace (send (cat m a b (enc na m a b (ltk a s))))
      (recv (cat m (enc na k (ltk a s))))))
  (defrole resp
    (vars (a b s name) (nb text) (k skey) (m text) (x y mesg))
    (trace (recv (cat m a b x))
      (send (cat m a b x (enc nb m a b (ltk b s))))
      (recv (cat m y (enc nb k (ltk b s)))) (send y)))
  (defrole serv
    (vars (a b s name) (na nb text) (k skey) (m text))
    (trace
      (recv
        (cat m a b (enc na m a b (ltk a s)) (enc nb m a b (ltk b s))))
      (send (cat m (enc na k (ltk a s)) (enc nb k (ltk b s)))))
    (uniq-orig k))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defgoal or
  (forall ((x y mesg) (k skey) (nb m text) (s a b name) (z strd))
    (implies
      (and (p "resp" z 4) (p "resp" "x" z x) (p "resp" "y" z y)
        (p "resp" "k" z k) (p "resp" "nb" z nb) (p "resp" "m" z m)
        (p "resp" "a" z a) (p "resp" "b" z b) (p "resp" "s" z s)
        (non (ltk a s)) (non (ltk b s)) (uniq-at nb z 1))
      (or
        (exists ((na text) (z-0 z-1 strd))
          (and (p "serv" z-0 2) (p "init" z-1 1) (p "serv" "k" z-0 k)
            (p "serv" "na" z-0 na) (p "serv" "nb" z-0 nb)
            (p "serv" "m" z-0 m) (p "serv" "a" z-0 a)
            (p "serv" "b" z-0 b) (p "serv" "s" z-0 s)
            (p "init" "na" z-1 na) (p "init" "m" z-1 m)
            (p "init" "a" z-1 a) (p "init" "b" z-1 b)
            (p "init" "s" z-1 s) (prec z 1 z-0 0) (prec z-0 1 z 2)
            (prec z-1 0 z-0 0) (uniq-at k z-0 1)))
        (exists ((z-0 strd))
          (and (= b a) (p "serv" z-0 2) (p "resp" "b" z a)
            (p "serv" "k" z-0 k) (p "serv" "na" z-0 nb)
            (p "serv" "nb" z-0 nb) (p "serv" "m" z-0 m)
            (p "serv" "a" z-0 a) (p "serv" "b" z-0 a)
            (p "serv" "s" z-0 s) (prec z 1 z-0 0) (prec z-0 1 z 2)
            (uniq-at k z-0 1)))
        (exists ((x-0 mesg) (na text) (z-0 z-1 strd))
          (and (= b a) (p "serv" z-0 2) (p "resp" z-1 2)
            (p "resp" "b" z a) (p "serv" "k" z-0 k)
            (p "serv" "na" z-0 na) (p "serv" "nb" z-0 nb)
            (p "serv" "m" z-0 m) (p "serv" "a" z-0 a)
            (p "serv" "b" z-0 a) (p "serv" "s" z-0 s)
            (p "resp" "x" z-1 x-0) (p "resp" "nb" z-1 na)
            (p "resp" "m" z-1 m) (p "resp" "a" z-1 a)
            (p "resp" "b" z-1 a) (p "resp" "s" z-1 s) (prec z 1 z-0 0)
            (prec z-0 1 z 2) (prec z-1 1 z-0 0) (uniq-at k z-0 1)))
        (exists ((nb-0 text) (z-0 z-1 strd))
          (and (= b a) (p "serv" z-0 2) (p "init" z-1 1)
            (p "resp" "b" z a) (p "serv" "k" z-0 k)
            (p "serv" "na" z-0 nb) (p "serv" "nb" z-0 nb-0)
            (p "serv" "m" z-0 m) (p "serv" "a" z-0 a)
            (p "serv" "b" z-0 a) (p "serv" "s" z-0 s)
            (p "init" "na" z-1 nb-0) (p "init" "m" z-1 m)
            (p "init" "a" z-1 a) (p "init" "b" z-1 a)
            (p "init" "s" z-1 s) (prec z 1 z-0 0) (prec z-0 1 z 2)
            (prec z-1 0 z-0 0) (uniq-at k z-0 1)))
        (exists ((x-0 mesg) (nb-0 text) (z-0 z-1 strd))
          (and (= b a) (p "serv" z-0 2) (p "resp" z-1 2)
            (p "resp" "b" z a) (p "serv" "k" z-0 k)
            (p "serv" "na" z-0 nb) (p "serv" "nb" z-0 nb-0)
            (p "serv" "m" z-0 m) (p "serv" "a" z-0 a)
            (p "serv" "b" z-0 a) (p "serv" "s" z-0 s)
            (p "resp" "x" z-1 x-0) (p "resp" "nb" z-1 nb-0)
            (p "resp" "m" z-1 m) (p "resp" "a" z-1 a)
            (p "resp" "b" z-1 a) (p "resp" "s" z-1 s) (prec z 1 z-0 0)
            (prec z-0 1 z 2) (prec z-1 1 z-0 0) (uniq-at k z-0 1)))))))
