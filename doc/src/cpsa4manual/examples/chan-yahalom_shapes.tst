(comment "CPSA 4.3.1")
(comment "Extracted shapes")

(herald "Yahalom Protocol Without Forwarding" (bound 15))

(comment "CPSA 4.3.1")

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

(defskeleton yahalom
  (vars (k skey) (n-b n-a text) (a b name) (ch1 ch2 chan))
  (defstrand resp 4 (k k) (n-a n-a) (n-b n-b) (b b) (a a) (ch1 ch1)
    (ch2 ch2))
  (uniq-orig n-b)
  (auth ch2)
  (traces
    ((recv (cat a n-a)) (send ch1 (cat a b n-a n-b))
      (recv ch2 (cat a b k)) (recv (enc n-b k))))
  (label 0)
  (unrealized (0 2))
  (origs (n-b (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton yahalom
  (vars (k skey) (n-b n-a n-a-0 n-b-0 text) (a b name)
    (ch1 ch2 ch1-0 ch3 chan))
  (defstrand resp 4 (k k) (n-a n-a) (n-b n-b) (b b) (a a) (ch1 ch1)
    (ch2 ch2))
  (defstrand serv 3 (k k) (n-a n-a-0) (n-b n-b-0) (a a) (b b)
    (ch1 ch1-0) (ch2 ch2) (ch3 ch3))
  (precedes ((1 2) (0 2)))
  (uniq-orig k n-b)
  (auth ch2)
  (operation channel-test (added-strand serv 3) (ch-msg ch2 (cat a b k))
    (0 2))
  (traces
    ((recv (cat a n-a)) (send ch1 (cat a b n-a n-b))
      (recv ch2 (cat a b k)) (recv (enc n-b k)))
    ((recv ch1-0 (cat a b n-a-0 n-b-0))
      (send ch3 (cat a b k n-a-0 n-b-0)) (send ch2 (cat a b k))))
  (label 1)
  (parent 0)
  (realized)
  (shape)
  (maps
    ((0) ((a a) (b b) (n-b n-b) (ch1 ch1) (ch2 ch2) (n-a n-a) (k k))))
  (origs (k (1 1)) (n-b (0 1))))

(comment "Nothing left to do")

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

(defskeleton yahalom
  (vars (k skey) (n-b n-a n-a-0 n-b-0 text) (a b name)
    (ch1 ch2 ch1-0 ch3 chan))
  (defstrand resp 4 (k k) (n-a n-a) (n-b n-b) (b b) (a a) (ch1 ch1)
    (ch2 ch2))
  (defstrand serv 3 (k k) (n-a n-a-0) (n-b n-b-0) (a a) (b b)
    (ch1 ch1-0) (ch2 ch2) (ch3 ch3))
  (precedes ((1 2) (0 2)))
  (uniq-orig k n-b)
  (conf ch2 ch3)
  (auth ch2)
  (traces
    ((recv (cat a n-a)) (send ch1 (cat a b n-a n-b))
      (recv ch2 (cat a b k)) (recv (enc n-b k)))
    ((recv ch1-0 (cat a b n-a-0 n-b-0))
      (send ch3 (cat a b k n-a-0 n-b-0)) (send ch2 (cat a b k))))
  (label 2)
  (unrealized (0 3))
  (origs (k (1 1)) (n-b (0 1)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton yahalom
  (vars (k skey) (n-a n-a-0 n-b text) (a b name)
    (ch1 ch2 ch1-0 ch3 chan))
  (defstrand resp 4 (k k) (n-a n-a) (n-b n-b) (b b) (a a) (ch1 ch1)
    (ch2 ch2))
  (defstrand serv 3 (k k) (n-a n-a-0) (n-b n-b) (a a) (b b) (ch1 ch1-0)
    (ch2 ch2) (ch3 ch3))
  (defstrand init 3 (k k) (n-a n-a-0) (n-b n-b) (a a) (b b) (ch3 ch3))
  (precedes ((0 1) (1 0)) ((1 1) (2 1)) ((1 2) (0 2)) ((2 2) (0 3)))
  (uniq-orig k n-b)
  (conf ch2 ch3)
  (auth ch2)
  (operation nonce-test
    (contracted (n-b-0 n-b) (a-0 a) (b-0 b) (n-a-1 n-a-0) (ch3-0 ch3)) k
    (2 1) (ch-msg ch3 (cat a b k n-a-0 n-b)))
  (traces
    ((recv (cat a n-a)) (send ch1 (cat a b n-a n-b))
      (recv ch2 (cat a b k)) (recv (enc n-b k)))
    ((recv ch1-0 (cat a b n-a-0 n-b)) (send ch3 (cat a b k n-a-0 n-b))
      (send ch2 (cat a b k)))
    ((send (cat a n-a-0)) (recv ch3 (cat a b k n-a-0 n-b))
      (send (enc n-b k))))
  (label 5)
  (parent 2)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((k k) (n-b n-b) (n-a n-a) (n-a-0 n-a-0) (n-b-0 n-b) (a a) (b b)
        (ch1 ch1) (ch2 ch2) (ch1-0 ch1-0) (ch3 ch3))))
  (origs (k (1 1)) (n-b (0 1))))

(comment "Nothing left to do")

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

(defskeleton yahalom
  (vars (k skey) (n-b n-a n-a-0 n-b-0 text) (a b name)
    (ch1 ch2 ch1-0 ch3 chan))
  (defstrand resp 4 (k k) (n-a n-a) (n-b n-b) (b b) (a a) (ch1 ch1)
    (ch2 ch2))
  (defstrand serv 3 (k k) (n-a n-a-0) (n-b n-b-0) (a a) (b b)
    (ch1 ch1-0) (ch2 ch2) (ch3 ch3))
  (uniq-orig k n-b)
  (conf ch2 ch3)
  (auth ch2 ch1-0)
  (traces
    ((recv (cat a n-a)) (send ch1 (cat a b n-a n-b))
      (recv ch2 (cat a b k)) (recv (enc n-b k)))
    ((recv ch1-0 (cat a b n-a-0 n-b-0))
      (send ch3 (cat a b k n-a-0 n-b-0)) (send ch2 (cat a b k))))
  (label 9)
  (unrealized (0 2) (0 3) (1 0))
  (preskeleton)
  (origs (k (1 1)) (n-b (0 1)))
  (comment "Not a skeleton"))

(defskeleton yahalom
  (vars (k skey) (n-b n-a text) (a b name) (ch1 ch2 ch3 chan))
  (defstrand resp 4 (k k) (n-a n-a) (n-b n-b) (b b) (a a) (ch1 ch1)
    (ch2 ch2))
  (defstrand serv 3 (k k) (n-a n-a) (n-b n-b) (a a) (b b) (ch1 ch1)
    (ch2 ch2) (ch3 ch3))
  (defstrand init 3 (k k) (n-a n-a) (n-b n-b) (a a) (b b) (ch3 ch3))
  (precedes ((0 1) (1 0)) ((1 1) (2 1)) ((1 2) (0 2)) ((2 2) (0 3)))
  (uniq-orig k n-b)
  (conf ch2 ch3)
  (auth ch1 ch2)
  (operation nonce-test
    (contracted (a-0 a) (b-0 b) (n-a-0 n-a) (ch3-0 ch3)) k (2 1)
    (ch-msg ch3 (cat a b k n-a n-b)))
  (traces
    ((recv (cat a n-a)) (send ch1 (cat a b n-a n-b))
      (recv ch2 (cat a b k)) (recv (enc n-b k)))
    ((recv ch1 (cat a b n-a n-b)) (send ch3 (cat a b k n-a n-b))
      (send ch2 (cat a b k)))
    ((send (cat a n-a)) (recv ch3 (cat a b k n-a n-b))
      (send (enc n-b k))))
  (label 19)
  (parent 9)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((k k) (n-b n-b) (n-a n-a) (n-a-0 n-a) (n-b-0 n-b) (a a) (b b)
        (ch1 ch1) (ch2 ch2) (ch1-0 ch1) (ch3 ch3))))
  (origs (k (1 1)) (n-b (0 1))))

(comment "Nothing left to do")

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

(defskeleton yahalom
  (vars (k skey) (n-b n-a n-a-0 n-b-0 text) (a b name)
    (ch1 ch2 ch1-0 ch3 chan))
  (defstrand resp 4 (k k) (n-a n-a) (n-b n-b) (b b) (a a) (ch1 ch1)
    (ch2 ch2))
  (defstrand serv 3 (k k) (n-a n-a-0) (n-b n-b-0) (a a) (b b)
    (ch1 ch1-0) (ch2 ch2) (ch3 ch3))
  (deflistener k)
  (uniq-orig k n-b)
  (conf ch2 ch3)
  (auth ch2 ch1-0)
  (traces
    ((recv (cat a n-a)) (send ch1 (cat a b n-a n-b))
      (recv ch2 (cat a b k)) (recv (enc n-b k)))
    ((recv ch1-0 (cat a b n-a-0 n-b-0))
      (send ch3 (cat a b k n-a-0 n-b-0)) (send ch2 (cat a b k)))
    ((recv k) (send k)))
  (label 25)
  (unrealized (0 2) (0 3) (1 0) (2 0))
  (preskeleton)
  (origs (k (1 1)) (n-b (0 1)))
  (comment "Not a skeleton"))

(comment "Nothing left to do")

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

(defskeleton yahalom
  (vars (k skey) (n-a n-b text) (a b name) (ch3 chan))
  (defstrand init 3 (k k) (n-a n-a) (n-b n-b) (a a) (b b) (ch3 ch3))
  (uniq-orig n-a)
  (auth ch3)
  (traces
    ((send (cat a n-a)) (recv ch3 (cat a b k n-a n-b))
      (send (enc n-b k))))
  (label 28)
  (unrealized (0 1))
  (origs (n-a (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton yahalom
  (vars (k skey) (n-a n-b text) (a b name) (ch3 ch1 chan))
  (defstrand init 3 (k k) (n-a n-a) (n-b n-b) (a a) (b b) (ch3 ch3))
  (defstrand serv 2 (k k) (n-a n-a) (n-b n-b) (a a) (b b) (ch1 ch1)
    (ch3 ch3))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (uniq-orig k n-a)
  (auth ch3)
  (operation channel-test (added-strand serv 2)
    (ch-msg ch3 (cat a b k n-a n-b)) (0 1))
  (traces
    ((send (cat a n-a)) (recv ch3 (cat a b k n-a n-b))
      (send (enc n-b k)))
    ((recv ch1 (cat a b n-a n-b)) (send ch3 (cat a b k n-a n-b))))
  (label 29)
  (parent 28)
  (realized)
  (shape)
  (maps ((0) ((n-a n-a) (ch3 ch3) (a a) (b b) (n-b n-b) (k k))))
  (origs (k (1 1)) (n-a (0 0))))

(comment "Nothing left to do")

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

(defskeleton yahalom
  (vars (k skey) (n-a n-b text) (a b name) (ch3 ch3-0 ch1 chan))
  (defstrand init 3 (k k) (n-a n-a) (n-b n-b) (a a) (b b) (ch3 ch3))
  (defstrand serv 2 (k k) (n-a n-a) (n-b n-b) (a a) (b b) (ch1 ch1)
    (ch3 ch3-0))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (uniq-orig k n-a)
  (conf ch3-0)
  (auth ch3 ch1)
  (traces
    ((send (cat a n-a)) (recv ch3 (cat a b k n-a n-b))
      (send (enc n-b k)))
    ((recv ch1 (cat a b n-a n-b)) (send ch3-0 (cat a b k n-a n-b))))
  (label 30)
  (unrealized (0 1) (1 0))
  (origs (k (1 1)) (n-a (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton yahalom
  (vars (k skey) (n-a n-b text) (a b name) (ch3 ch1 chan))
  (defstrand init 3 (k k) (n-a n-a) (n-b n-b) (a a) (b b) (ch3 ch3))
  (defstrand serv 2 (k k) (n-a n-a) (n-b n-b) (a a) (b b) (ch1 ch1)
    (ch3 ch3))
  (defstrand resp 2 (n-a n-a) (n-b n-b) (b b) (a a) (ch1 ch1))
  (precedes ((0 0) (2 0)) ((1 1) (0 1)) ((2 1) (1 0)))
  (uniq-orig k n-a)
  (conf ch3)
  (auth ch3 ch1)
  (operation channel-test (displaced 3 1 serv 2)
    (ch-msg ch3-0 (cat a b k n-a n-b)) (0 1))
  (traces
    ((send (cat a n-a)) (recv ch3 (cat a b k n-a n-b))
      (send (enc n-b k)))
    ((recv ch1 (cat a b n-a n-b)) (send ch3 (cat a b k n-a n-b)))
    ((recv (cat a n-a)) (send ch1 (cat a b n-a n-b))))
  (label 32)
  (parent 30)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((k k) (n-a n-a) (n-b n-b) (a a) (b b) (ch3 ch3) (ch3-0 ch3)
        (ch1 ch1))))
  (origs (k (1 1)) (n-a (0 0))))

(comment "Nothing left to do")

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

(defskeleton yahalom
  (vars (k skey) (n-a n-b text) (a b name) (ch1 ch2 ch3 chan))
  (defstrand serv 3 (k k) (n-a n-a) (n-b n-b) (a a) (b b) (ch1 ch1)
    (ch2 ch2) (ch3 ch3))
  (uniq-orig k)
  (conf ch2 ch3)
  (auth ch1)
  (traces
    ((recv ch1 (cat a b n-a n-b)) (send ch3 (cat a b k n-a n-b))
      (send ch2 (cat a b k))))
  (label 33)
  (unrealized (0 0))
  (origs (k (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton yahalom
  (vars (k skey) (n-a n-b text) (a b name) (ch1 ch2 ch3 chan))
  (defstrand serv 3 (k k) (n-a n-a) (n-b n-b) (a a) (b b) (ch1 ch1)
    (ch2 ch2) (ch3 ch3))
  (defstrand resp 2 (n-a n-a) (n-b n-b) (b b) (a a) (ch1 ch1))
  (precedes ((1 1) (0 0)))
  (uniq-orig k)
  (conf ch2 ch3)
  (auth ch1)
  (operation channel-test (added-strand resp 2)
    (ch-msg ch1 (cat a b n-a n-b)) (0 0))
  (traces
    ((recv ch1 (cat a b n-a n-b)) (send ch3 (cat a b k n-a n-b))
      (send ch2 (cat a b k)))
    ((recv (cat a n-a)) (send ch1 (cat a b n-a n-b))))
  (label 34)
  (parent 33)
  (realized)
  (shape)
  (maps
    ((0)
      ((ch1 ch1) (ch2 ch2) (ch3 ch3) (a a) (b b) (n-a n-a) (n-b n-b)
        (k k))))
  (origs (k (0 1))))

(comment "Nothing left to do")

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

(defskeleton yahalom
  (vars (k skey) (n-a n-b text) (a b name) (ch1 ch2 ch3 chan))
  (defstrand serv 3 (k k) (n-a n-a) (n-b n-b) (a a) (b b) (ch1 ch1)
    (ch2 ch2) (ch3 ch3))
  (deflistener k)
  (uniq-orig k)
  (conf ch2 ch3)
  (auth ch1)
  (traces
    ((recv ch1 (cat a b n-a n-b)) (send ch3 (cat a b k n-a n-b))
      (send ch2 (cat a b k))) ((recv k) (send k)))
  (label 35)
  (unrealized (0 0) (1 0))
  (preskeleton)
  (origs (k (0 1)))
  (comment "Not a skeleton"))

(comment "Nothing left to do")