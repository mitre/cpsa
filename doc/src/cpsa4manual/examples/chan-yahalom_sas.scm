(herald "Yahalom Protocol Without Forwarding" (bound 15))

(comment "CPSA 4.4.0")
(comment "Coherent logic")

(comment "CPSA 4.4.0")

(comment "All input read from chan-yahalom.scm")

(comment "Strand count bounded at 15")

(defprotocol yahalom basic
  (defrole init
    (vars (a b name) (n-a n-b text) (k skey) (ch3 chan))
    (trace (send (cat a n-a)) (recv ch3 (cat a b k n-a n-b))
      (send (enc n-b k))))
  (defrole resp
    (vars (b a name) (n-a n-b text) (k skey) (ch1 ch2 chan))
    (trace (recv (cat a n-a)) (send ch1 (cat a b n-a n-b))
      (recv ch2 (cat a b k)) (recv (enc n-b k))))
  (defrole serv
    (vars (a b name) (n-a n-b text) (k skey) (ch1 ch2 ch3 chan))
    (trace (recv ch1 (cat a b n-a n-b)) (send ch3 (cat a b k n-a n-b))
      (send ch2 (cat a b k)))
    (uniq-orig k))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defgoal yahalom
  (forall ((k skey) (n-b n-a text) (a b name) (ch1 ch2 chan) (z strd))
    (implies
      (and (p "resp" z 4) (p "resp" "k" z k) (p "resp" "n-a" z n-a)
        (p "resp" "n-b" z n-b) (p "resp" "b" z b) (p "resp" "a" z a)
        (p "resp" "ch1" z ch1) (p "resp" "ch2" z ch2) (uniq-at n-b z 1)
        (auth ch2))
      (exists ((n-a-0 n-b-0 text) (ch1-0 ch3 chan) (z-0 strd))
        (and (p "serv" z-0 3) (p "serv" "k" z-0 k)
          (p "serv" "n-a" z-0 n-a-0) (p "serv" "n-b" z-0 n-b-0)
          (p "serv" "a" z-0 a) (p "serv" "b" z-0 b)
          (p "serv" "ch1" z-0 ch1-0) (p "serv" "ch2" z-0 ch2)
          (p "serv" "ch3" z-0 ch3) (prec z-0 2 z 2)
          (uniq-at k z-0 1))))))

(defprotocol yahalom basic
  (defrole init
    (vars (a b name) (n-a n-b text) (k skey) (ch3 chan))
    (trace (send (cat a n-a)) (recv ch3 (cat a b k n-a n-b))
      (send (enc n-b k))))
  (defrole resp
    (vars (b a name) (n-a n-b text) (k skey) (ch1 ch2 chan))
    (trace (recv (cat a n-a)) (send ch1 (cat a b n-a n-b))
      (recv ch2 (cat a b k)) (recv (enc n-b k))))
  (defrole serv
    (vars (a b name) (n-a n-b text) (k skey) (ch1 ch2 ch3 chan))
    (trace (recv ch1 (cat a b n-a n-b)) (send ch3 (cat a b k n-a n-b))
      (send ch2 (cat a b k)))
    (uniq-orig k))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defgoal yahalom
  (forall
    ((k skey) (n-b n-a n-a-0 n-b-0 text) (a b name)
      (ch1 ch2 ch1-0 ch3 chan) (z z-0 strd))
    (implies
      (and (p "resp" z 4) (p "serv" z-0 3) (p "resp" "k" z k)
        (p "resp" "n-a" z n-a) (p "resp" "n-b" z n-b) (p "resp" "b" z b)
        (p "resp" "a" z a) (p "resp" "ch1" z ch1) (p "resp" "ch2" z ch2)
        (p "serv" "k" z-0 k) (p "serv" "n-a" z-0 n-a-0)
        (p "serv" "n-b" z-0 n-b-0) (p "serv" "a" z-0 a)
        (p "serv" "b" z-0 b) (p "serv" "ch1" z-0 ch1-0)
        (p "serv" "ch2" z-0 ch2) (p "serv" "ch3" z-0 ch3)
        (prec z-0 2 z 2) (uniq-at k z-0 1) (uniq-at n-b z 1) (auth ch2)
        (conf ch2) (conf ch3))
      (exists ((z-1 strd))
        (and (= n-b-0 n-b) (p "init" z-1 3) (p "serv" "n-b" z-0 n-b)
          (p "init" "k" z-1 k) (p "init" "n-a" z-1 n-a-0)
          (p "init" "n-b" z-1 n-b) (p "init" "a" z-1 a)
          (p "init" "b" z-1 b) (p "init" "ch3" z-1 ch3) (prec z 1 z-0 0)
          (prec z-0 1 z-1 1) (prec z-1 2 z 3))))))

(defprotocol yahalom basic
  (defrole init
    (vars (a b name) (n-a n-b text) (k skey) (ch3 chan))
    (trace (send (cat a n-a)) (recv ch3 (cat a b k n-a n-b))
      (send (enc n-b k))))
  (defrole resp
    (vars (b a name) (n-a n-b text) (k skey) (ch1 ch2 chan))
    (trace (recv (cat a n-a)) (send ch1 (cat a b n-a n-b))
      (recv ch2 (cat a b k)) (recv (enc n-b k))))
  (defrole serv
    (vars (a b name) (n-a n-b text) (k skey) (ch1 ch2 ch3 chan))
    (trace (recv ch1 (cat a b n-a n-b)) (send ch3 (cat a b k n-a n-b))
      (send ch2 (cat a b k)))
    (uniq-orig k))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defgoal yahalom
  (forall
    ((k skey) (n-b n-a n-a-0 n-b-0 text) (a b name)
      (ch1 ch2 ch1-0 ch3 chan) (z z-0 strd))
    (implies
      (and (p "resp" z 4) (p "serv" z-0 3) (p "resp" "k" z k)
        (p "resp" "n-a" z n-a) (p "resp" "n-b" z n-b) (p "resp" "b" z b)
        (p "resp" "a" z a) (p "resp" "ch1" z ch1) (p "resp" "ch2" z ch2)
        (p "serv" "k" z-0 k) (p "serv" "n-a" z-0 n-a-0)
        (p "serv" "n-b" z-0 n-b-0) (p "serv" "a" z-0 a)
        (p "serv" "b" z-0 b) (p "serv" "ch1" z-0 ch1-0)
        (p "serv" "ch2" z-0 ch2) (p "serv" "ch3" z-0 ch3)
        (uniq-at k z-0 1) (uniq-at n-b z 1) (auth ch2) (auth ch1-0)
        (conf ch2) (conf ch3))
      (exists ((z-1 strd))
        (and (= n-a-0 n-a) (= n-b-0 n-b) (= ch1-0 ch1) (p "init" z-1 3)
          (p "serv" "n-a" z-0 n-a) (p "serv" "n-b" z-0 n-b)
          (p "serv" "ch1" z-0 ch1) (p "init" "k" z-1 k)
          (p "init" "n-a" z-1 n-a) (p "init" "n-b" z-1 n-b)
          (p "init" "a" z-1 a) (p "init" "b" z-1 b)
          (p "init" "ch3" z-1 ch3) (prec z 1 z-0 0) (prec z-0 1 z-1 1)
          (prec z-0 2 z 2) (prec z-1 2 z 3) (auth ch1))))))

(defprotocol yahalom basic
  (defrole init
    (vars (a b name) (n-a n-b text) (k skey) (ch3 chan))
    (trace (send (cat a n-a)) (recv ch3 (cat a b k n-a n-b))
      (send (enc n-b k))))
  (defrole resp
    (vars (b a name) (n-a n-b text) (k skey) (ch1 ch2 chan))
    (trace (recv (cat a n-a)) (send ch1 (cat a b n-a n-b))
      (recv ch2 (cat a b k)) (recv (enc n-b k))))
  (defrole serv
    (vars (a b name) (n-a n-b text) (k skey) (ch1 ch2 ch3 chan))
    (trace (recv ch1 (cat a b n-a n-b)) (send ch3 (cat a b k n-a n-b))
      (send ch2 (cat a b k)))
    (uniq-orig k))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defgoal yahalom
  (forall
    ((k skey) (n-b n-a n-a-0 n-b-0 text) (a b name)
      (ch1 ch2 ch1-0 ch3 chan) (z z-0 z-1 strd))
    (implies
      (and (p "resp" z 4) (p "serv" z-0 3) (p "" z-1 2)
        (p "resp" "k" z k) (p "resp" "n-a" z n-a) (p "resp" "n-b" z n-b)
        (p "resp" "b" z b) (p "resp" "a" z a) (p "resp" "ch1" z ch1)
        (p "resp" "ch2" z ch2) (p "serv" "k" z-0 k)
        (p "serv" "n-a" z-0 n-a-0) (p "serv" "n-b" z-0 n-b-0)
        (p "serv" "a" z-0 a) (p "serv" "b" z-0 b)
        (p "serv" "ch1" z-0 ch1-0) (p "serv" "ch2" z-0 ch2)
        (p "serv" "ch3" z-0 ch3) (p "" "x" z-1 k) (uniq-at k z-0 1)
        (uniq-at n-b z 1) (auth ch2) (auth ch1-0) (conf ch2) (conf ch3))
      (false))))

(defprotocol yahalom basic
  (defrole init
    (vars (a b name) (n-a n-b text) (k skey) (ch3 chan))
    (trace (send (cat a n-a)) (recv ch3 (cat a b k n-a n-b))
      (send (enc n-b k))))
  (defrole resp
    (vars (b a name) (n-a n-b text) (k skey) (ch1 ch2 chan))
    (trace (recv (cat a n-a)) (send ch1 (cat a b n-a n-b))
      (recv ch2 (cat a b k)) (recv (enc n-b k))))
  (defrole serv
    (vars (a b name) (n-a n-b text) (k skey) (ch1 ch2 ch3 chan))
    (trace (recv ch1 (cat a b n-a n-b)) (send ch3 (cat a b k n-a n-b))
      (send ch2 (cat a b k)))
    (uniq-orig k))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defgoal yahalom
  (forall ((k skey) (n-a n-b text) (a b name) (ch3 chan) (z strd))
    (implies
      (and (p "init" z 3) (p "init" "k" z k) (p "init" "n-a" z n-a)
        (p "init" "n-b" z n-b) (p "init" "a" z a) (p "init" "b" z b)
        (p "init" "ch3" z ch3) (uniq-at n-a z 0) (auth ch3))
      (exists ((ch1 chan) (z-0 strd))
        (and (p "serv" z-0 2) (p "serv" "k" z-0 k)
          (p "serv" "n-a" z-0 n-a) (p "serv" "n-b" z-0 n-b)
          (p "serv" "a" z-0 a) (p "serv" "b" z-0 b)
          (p "serv" "ch1" z-0 ch1) (p "serv" "ch3" z-0 ch3)
          (prec z 0 z-0 0) (prec z-0 1 z 1) (uniq-at k z-0 1))))))

(defprotocol yahalom basic
  (defrole init
    (vars (a b name) (n-a n-b text) (k skey) (ch3 chan))
    (trace (send (cat a n-a)) (recv ch3 (cat a b k n-a n-b))
      (send (enc n-b k))))
  (defrole resp
    (vars (b a name) (n-a n-b text) (k skey) (ch1 ch2 chan))
    (trace (recv (cat a n-a)) (send ch1 (cat a b n-a n-b))
      (recv ch2 (cat a b k)) (recv (enc n-b k))))
  (defrole serv
    (vars (a b name) (n-a n-b text) (k skey) (ch1 ch2 ch3 chan))
    (trace (recv ch1 (cat a b n-a n-b)) (send ch3 (cat a b k n-a n-b))
      (send ch2 (cat a b k)))
    (uniq-orig k))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defgoal yahalom
  (forall
    ((k skey) (n-a n-b text) (a b name) (ch3 ch3-0 ch1 chan)
      (z z-0 strd))
    (implies
      (and (p "init" z 3) (p "serv" z-0 2) (p "init" "k" z k)
        (p "init" "n-a" z n-a) (p "init" "n-b" z n-b) (p "init" "a" z a)
        (p "init" "b" z b) (p "init" "ch3" z ch3) (p "serv" "k" z-0 k)
        (p "serv" "n-a" z-0 n-a) (p "serv" "n-b" z-0 n-b)
        (p "serv" "a" z-0 a) (p "serv" "b" z-0 b)
        (p "serv" "ch1" z-0 ch1) (p "serv" "ch3" z-0 ch3-0)
        (prec z 0 z-0 0) (prec z-0 1 z 1) (uniq-at k z-0 1)
        (uniq-at n-a z 0) (auth ch3) (auth ch1) (conf ch3-0))
      (exists ((z-1 strd))
        (and (= ch3-0 ch3) (p "resp" z-1 2) (p "serv" "ch3" z-0 ch3)
          (p "resp" "n-a" z-1 n-a) (p "resp" "n-b" z-1 n-b)
          (p "resp" "b" z-1 b) (p "resp" "a" z-1 a)
          (p "resp" "ch1" z-1 ch1) (prec z 0 z-1 0) (prec z-1 1 z-0 0)
          (conf ch3))))))

(defprotocol yahalom basic
  (defrole init
    (vars (a b name) (n-a n-b text) (k skey) (ch3 chan))
    (trace (send (cat a n-a)) (recv ch3 (cat a b k n-a n-b))
      (send (enc n-b k))))
  (defrole resp
    (vars (b a name) (n-a n-b text) (k skey) (ch1 ch2 chan))
    (trace (recv (cat a n-a)) (send ch1 (cat a b n-a n-b))
      (recv ch2 (cat a b k)) (recv (enc n-b k))))
  (defrole serv
    (vars (a b name) (n-a n-b text) (k skey) (ch1 ch2 ch3 chan))
    (trace (recv ch1 (cat a b n-a n-b)) (send ch3 (cat a b k n-a n-b))
      (send ch2 (cat a b k)))
    (uniq-orig k))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defgoal yahalom
  (forall
    ((k skey) (n-a n-b text) (a b name) (ch1 ch2 ch3 chan) (z strd))
    (implies
      (and (p "serv" z 3) (p "serv" "k" z k) (p "serv" "n-a" z n-a)
        (p "serv" "n-b" z n-b) (p "serv" "a" z a) (p "serv" "b" z b)
        (p "serv" "ch1" z ch1) (p "serv" "ch2" z ch2)
        (p "serv" "ch3" z ch3) (uniq-at k z 1) (auth ch1) (conf ch2)
        (conf ch3))
      (exists ((z-0 strd))
        (and (p "resp" z-0 2) (p "resp" "n-a" z-0 n-a)
          (p "resp" "n-b" z-0 n-b) (p "resp" "b" z-0 b)
          (p "resp" "a" z-0 a) (p "resp" "ch1" z-0 ch1)
          (prec z-0 1 z 0))))))

(defprotocol yahalom basic
  (defrole init
    (vars (a b name) (n-a n-b text) (k skey) (ch3 chan))
    (trace (send (cat a n-a)) (recv ch3 (cat a b k n-a n-b))
      (send (enc n-b k))))
  (defrole resp
    (vars (b a name) (n-a n-b text) (k skey) (ch1 ch2 chan))
    (trace (recv (cat a n-a)) (send ch1 (cat a b n-a n-b))
      (recv ch2 (cat a b k)) (recv (enc n-b k))))
  (defrole serv
    (vars (a b name) (n-a n-b text) (k skey) (ch1 ch2 ch3 chan))
    (trace (recv ch1 (cat a b n-a n-b)) (send ch3 (cat a b k n-a n-b))
      (send ch2 (cat a b k)))
    (uniq-orig k))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defgoal yahalom
  (forall
    ((k skey) (n-a n-b text) (a b name) (ch1 ch2 ch3 chan) (z z-0 strd))
    (implies
      (and (p "serv" z 3) (p "" z-0 2) (p "serv" "k" z k)
        (p "serv" "n-a" z n-a) (p "serv" "n-b" z n-b) (p "serv" "a" z a)
        (p "serv" "b" z b) (p "serv" "ch1" z ch1) (p "serv" "ch2" z ch2)
        (p "serv" "ch3" z ch3) (p "" "x" z-0 k) (uniq-at k z 1)
        (auth ch1) (conf ch2) (conf ch3))
      (false))))
