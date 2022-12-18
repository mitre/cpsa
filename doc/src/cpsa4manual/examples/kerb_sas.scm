(comment "CPSA 4.4.0")
(comment "Coherent logic")

(defprotocol kerb-flawed basic
  (defrole init
    (vars (a b s name) (m n text) (k skey))
    (trace (send (cat a b n))
      (recv (cat (enc k n (ltk a s)) (enc k a b (ltk b s))))
      (send (cat (enc m k) (enc k a b (ltk b s)))))
    (uniq-orig n))
  (defrole resp
    (vars (a b s name) (m text) (k skey))
    (trace (recv (cat (enc m k) (enc k a b (ltk b s))))))
  (defrole keyserv
    (vars (a b s name) (n text) (k skey))
    (trace (recv (cat a b n))
      (send (cat (enc k n (ltk a s)) (enc k a b (ltk b s)))))
    (uniq-orig k))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defgoal kerb-flawed
  (forall ((k skey) (m n text) (a b s name) (z z-0 strd))
    (implies
      (and (p "init" z 3) (p "" z-0 2) (p "init" "k" z k)
        (p "init" "m" z m) (p "init" "n" z n) (p "init" "a" z a)
        (p "init" "b" z b) (p "init" "s" z s) (p "" "x" z-0 m)
        (non (ltk a s)) (non (ltk b s)) (uniq-at n z 0) (uniq-at m z 2))
      (false))))

(defprotocol kerb-flawed2 basic
  (defrole init
    (vars (a b s name) (ticket mesg) (m n text) (k skey))
    (trace (send (cat a b n)) (recv (cat (enc k n (ltk a s)) ticket))
      (send (cat (enc m k) ticket)))
    (uniq-orig n))
  (defrole resp
    (vars (a b s name) (m text) (k skey))
    (trace (recv (cat (enc m k) (enc k a b (ltk b s))))))
  (defrole keyserv
    (vars (a b s name) (n text) (k skey))
    (trace (recv (cat a b n))
      (send (cat (enc k n (ltk a s)) (enc k a b (ltk b s)))))
    (uniq-orig k))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defgoal kerb-flawed2
  (forall ((ticket mesg) (k skey) (m n text) (a b s name) (z z-0 strd))
    (implies
      (and (p "init" z 3) (p "" z-0 2) (p "init" "ticket" z ticket)
        (p "init" "k" z k) (p "init" "m" z m) (p "init" "n" z n)
        (p "init" "a" z a) (p "init" "b" z b) (p "init" "s" z s)
        (p "" "x" z-0 m) (non (ltk a s)) (non (ltk b s)) (uniq-at n z 0)
        (uniq-at m z 2))
      (exists ((b-0 name) (z-1 strd))
        (and (p "keyserv" z-1 2) (p "keyserv" "k" z-1 k)
          (p "keyserv" "n" z-1 n) (p "keyserv" "a" z-1 a)
          (p "keyserv" "b" z-1 b-0) (p "keyserv" "s" z-1 s)
          (prec z 0 z-1 0) (prec z 2 z-0 0) (prec z-1 1 z 1)
          (uniq-at k z-1 1))))))
