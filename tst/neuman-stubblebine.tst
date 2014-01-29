(comment "CPSA 2.3.1")
(comment "All input read from neuman-stubblebine.scm")

(defprotocol neuman-stubblebine basic
  (defrole init
    (vars (a b ks name) (ra rb text) (k skey) (tb text))
    (trace (send (cat a ra))
      (recv (cat (enc b ra k tb (ltk a ks)) (enc a k tb (ltk b ks)) rb))
      (send (cat (enc a k tb (ltk b ks)) (enc rb k)))))
  (defrole resp
    (vars (a b ks name) (ra rb text) (k skey) (tb text))
    (trace (recv (cat a ra)) (send (cat b rb (enc a ra tb (ltk b ks))))
      (recv (cat (enc a k tb (ltk b ks)) (enc rb k)))))
  (defrole keyserver
    (vars (a b ks name) (ra rb text) (k skey) (tb text))
    (trace (recv (cat b rb (enc a ra tb (ltk b ks))))
      (send
        (cat (enc b ra k tb (ltk a ks)) (enc a k tb (ltk b ks)) rb)))
    (uniq-orig k)))

(defskeleton neuman-stubblebine
  (vars (ra rb tb text) (a b ks name) (k skey))
  (defstrand init 3 (ra ra) (rb rb) (tb tb) (a a) (b b) (ks ks) (k k))
  (non-orig (ltk a ks) (ltk b ks))
  (uniq-orig ra rb)
  (traces
    ((send (cat a ra))
      (recv (cat (enc b ra k tb (ltk a ks)) (enc a k tb (ltk b ks)) rb))
      (send (cat (enc a k tb (ltk b ks)) (enc rb k)))))
  (label 0)
  (unrealized (0 1))
  (origs (ra (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton neuman-stubblebine
  (vars (ra rb tb rb-0 text) (a b ks name) (k skey))
  (defstrand init 3 (ra ra) (rb rb) (tb tb) (a a) (b b) (ks ks) (k k))
  (defstrand keyserver 2 (ra ra) (rb rb-0) (tb tb) (a a) (b b) (ks ks)
    (k k))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (ltk a ks) (ltk b ks))
  (uniq-orig ra rb k)
  (operation encryption-test (added-strand keyserver 2)
    (enc b ra k tb (ltk a ks)) (0 1))
  (traces
    ((send (cat a ra))
      (recv (cat (enc b ra k tb (ltk a ks)) (enc a k tb (ltk b ks)) rb))
      (send (cat (enc a k tb (ltk b ks)) (enc rb k))))
    ((recv (cat b rb-0 (enc a ra tb (ltk b ks))))
      (send
        (cat (enc b ra k tb (ltk a ks)) (enc a k tb (ltk b ks)) rb-0))))
  (label 1)
  (parent 0)
  (unrealized (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton neuman-stubblebine
  (vars (ra rb tb rb-0 rb-1 text) (a b ks name) (k skey))
  (defstrand init 3 (ra ra) (rb rb) (tb tb) (a a) (b b) (ks ks) (k k))
  (defstrand keyserver 2 (ra ra) (rb rb-0) (tb tb) (a a) (b b) (ks ks)
    (k k))
  (defstrand resp 2 (ra ra) (rb rb-1) (tb tb) (a a) (b b) (ks ks))
  (precedes ((0 0) (2 0)) ((1 1) (0 1)) ((2 1) (1 0)))
  (non-orig (ltk a ks) (ltk b ks))
  (uniq-orig ra rb k)
  (operation encryption-test (added-strand resp 2)
    (enc a ra tb (ltk b ks)) (1 0))
  (traces
    ((send (cat a ra))
      (recv (cat (enc b ra k tb (ltk a ks)) (enc a k tb (ltk b ks)) rb))
      (send (cat (enc a k tb (ltk b ks)) (enc rb k))))
    ((recv (cat b rb-0 (enc a ra tb (ltk b ks))))
      (send
        (cat (enc b ra k tb (ltk a ks)) (enc a k tb (ltk b ks)) rb-0)))
    ((recv (cat a ra)) (send (cat b rb-1 (enc a ra tb (ltk b ks))))))
  (label 2)
  (parent 1)
  (unrealized)
  (shape)
  (maps ((0) ((a a) (b b) (ks ks) (ra ra) (rb rb) (k k) (tb tb))))
  (origs (k (1 1)) (ra (0 0))))

(comment "Nothing left to do")

(defprotocol neuman-stubblebine basic
  (defrole init
    (vars (a b ks name) (ra rb text) (k skey) (tb text))
    (trace (send (cat a ra))
      (recv (cat (enc b ra k tb (ltk a ks)) (enc a k tb (ltk b ks)) rb))
      (send (cat (enc a k tb (ltk b ks)) (enc rb k)))))
  (defrole resp
    (vars (a b ks name) (ra rb text) (k skey) (tb text))
    (trace (recv (cat a ra)) (send (cat b rb (enc a ra tb (ltk b ks))))
      (recv (cat (enc a k tb (ltk b ks)) (enc rb k)))))
  (defrole keyserver
    (vars (a b ks name) (ra rb text) (k skey) (tb text))
    (trace (recv (cat b rb (enc a ra tb (ltk b ks))))
      (send
        (cat (enc b ra k tb (ltk a ks)) (enc a k tb (ltk b ks)) rb)))
    (uniq-orig k)))

(defskeleton neuman-stubblebine
  (vars (ra rb tb text) (a b ks name) (k skey))
  (defstrand resp 3 (ra ra) (rb rb) (tb tb) (a a) (b b) (ks ks) (k k))
  (non-orig (ltk a ks) (ltk b ks))
  (uniq-orig ra rb)
  (traces
    ((recv (cat a ra)) (send (cat b rb (enc a ra tb (ltk b ks))))
      (recv (cat (enc a k tb (ltk b ks)) (enc rb k)))))
  (label 3)
  (unrealized (0 2))
  (origs (rb (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton neuman-stubblebine
  (vars (ra rb tb ra-0 rb-0 text) (a b ks name) (k skey))
  (defstrand resp 3 (ra ra) (rb rb) (tb tb) (a a) (b b) (ks ks) (k k))
  (defstrand keyserver 2 (ra ra-0) (rb rb-0) (tb tb) (a a) (b b) (ks ks)
    (k k))
  (precedes ((1 1) (0 2)))
  (non-orig (ltk a ks) (ltk b ks))
  (uniq-orig ra rb k)
  (operation encryption-test (added-strand keyserver 2)
    (enc a k tb (ltk b ks)) (0 2))
  (traces
    ((recv (cat a ra)) (send (cat b rb (enc a ra tb (ltk b ks))))
      (recv (cat (enc a k tb (ltk b ks)) (enc rb k))))
    ((recv (cat b rb-0 (enc a ra-0 tb (ltk b ks))))
      (send
        (cat (enc b ra-0 k tb (ltk a ks)) (enc a k tb (ltk b ks))
          rb-0))))
  (label 4)
  (parent 3)
  (unrealized (0 2) (1 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton neuman-stubblebine
  (vars (ra rb tb rb-0 text) (a b ks name) (k skey))
  (defstrand resp 3 (ra ra) (rb rb) (tb tb) (a a) (b b) (ks ks) (k k))
  (defstrand keyserver 2 (ra ra) (rb rb-0) (tb tb) (a a) (b b) (ks ks)
    (k k))
  (precedes ((0 1) (1 0)) ((1 1) (0 2)))
  (non-orig (ltk a ks) (ltk b ks))
  (uniq-orig ra rb k)
  (operation encryption-test (displaced 2 0 resp 2)
    (enc a ra-0 tb (ltk b ks)) (1 0))
  (traces
    ((recv (cat a ra)) (send (cat b rb (enc a ra tb (ltk b ks))))
      (recv (cat (enc a k tb (ltk b ks)) (enc rb k))))
    ((recv (cat b rb-0 (enc a ra tb (ltk b ks))))
      (send
        (cat (enc b ra k tb (ltk a ks)) (enc a k tb (ltk b ks)) rb-0))))
  (label 5)
  (parent 4)
  (unrealized (0 2))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton neuman-stubblebine
  (vars (ra rb tb ra-0 rb-0 rb-1 text) (a b ks name) (k skey))
  (defstrand resp 3 (ra ra) (rb rb) (tb tb) (a a) (b b) (ks ks) (k k))
  (defstrand keyserver 2 (ra ra-0) (rb rb-0) (tb tb) (a a) (b b) (ks ks)
    (k k))
  (defstrand resp 2 (ra ra-0) (rb rb-1) (tb tb) (a a) (b b) (ks ks))
  (precedes ((1 1) (0 2)) ((2 1) (1 0)))
  (non-orig (ltk a ks) (ltk b ks))
  (uniq-orig ra rb k)
  (operation encryption-test (added-strand resp 2)
    (enc a ra-0 tb (ltk b ks)) (1 0))
  (traces
    ((recv (cat a ra)) (send (cat b rb (enc a ra tb (ltk b ks))))
      (recv (cat (enc a k tb (ltk b ks)) (enc rb k))))
    ((recv (cat b rb-0 (enc a ra-0 tb (ltk b ks))))
      (send
        (cat (enc b ra-0 k tb (ltk a ks)) (enc a k tb (ltk b ks))
          rb-0)))
    ((recv (cat a ra-0))
      (send (cat b rb-1 (enc a ra-0 tb (ltk b ks))))))
  (label 6)
  (parent 4)
  (unrealized (0 2))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton neuman-stubblebine
  (vars (ra rb tb rb-0 ra-0 tb-0 text) (a b ks a-0 b-0 ks-0 name)
    (k skey))
  (defstrand resp 3 (ra ra) (rb rb) (tb tb) (a a) (b b) (ks ks) (k k))
  (defstrand keyserver 2 (ra ra) (rb rb-0) (tb tb) (a a) (b b) (ks ks)
    (k k))
  (defstrand init 3 (ra ra-0) (rb rb) (tb tb-0) (a a-0) (b b-0)
    (ks ks-0) (k k))
  (precedes ((0 1) (1 0)) ((1 1) (2 1)) ((2 2) (0 2)))
  (non-orig (ltk a ks) (ltk b ks))
  (uniq-orig ra rb k)
  (operation encryption-test (added-strand init 3) (enc rb k) (0 2))
  (traces
    ((recv (cat a ra)) (send (cat b rb (enc a ra tb (ltk b ks))))
      (recv (cat (enc a k tb (ltk b ks)) (enc rb k))))
    ((recv (cat b rb-0 (enc a ra tb (ltk b ks))))
      (send
        (cat (enc b ra k tb (ltk a ks)) (enc a k tb (ltk b ks)) rb-0)))
    ((send (cat a-0 ra-0))
      (recv
        (cat (enc b-0 ra-0 k tb-0 (ltk a-0 ks-0))
          (enc a-0 k tb-0 (ltk b-0 ks-0)) rb))
      (send (cat (enc a-0 k tb-0 (ltk b-0 ks-0)) (enc rb k)))))
  (label 7)
  (parent 5)
  (unrealized (2 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton neuman-stubblebine
  (vars (ra rb tb rb-0 text) (a b ks name) (k skey))
  (defstrand resp 3 (ra ra) (rb rb) (tb tb) (a a) (b b) (ks ks) (k k))
  (defstrand keyserver 2 (ra ra) (rb rb-0) (tb tb) (a a) (b b) (ks ks)
    (k k))
  (deflistener k)
  (precedes ((0 1) (1 0)) ((1 1) (2 0)) ((2 1) (0 2)))
  (non-orig (ltk a ks) (ltk b ks))
  (uniq-orig ra rb k)
  (operation encryption-test (added-listener k) (enc rb k) (0 2))
  (traces
    ((recv (cat a ra)) (send (cat b rb (enc a ra tb (ltk b ks))))
      (recv (cat (enc a k tb (ltk b ks)) (enc rb k))))
    ((recv (cat b rb-0 (enc a ra tb (ltk b ks))))
      (send
        (cat (enc b ra k tb (ltk a ks)) (enc a k tb (ltk b ks)) rb-0)))
    ((recv k) (send k)))
  (label 8)
  (parent 5)
  (unrealized (2 0))
  (comment "empty cohort"))

(defskeleton neuman-stubblebine
  (vars (ra rb tb ra-0 rb-0 rb-1 ra-1 tb-0 text)
    (a b ks a-0 b-0 ks-0 name) (k skey))
  (defstrand resp 3 (ra ra) (rb rb) (tb tb) (a a) (b b) (ks ks) (k k))
  (defstrand keyserver 2 (ra ra-0) (rb rb-0) (tb tb) (a a) (b b) (ks ks)
    (k k))
  (defstrand resp 2 (ra ra-0) (rb rb-1) (tb tb) (a a) (b b) (ks ks))
  (defstrand init 3 (ra ra-1) (rb rb) (tb tb-0) (a a-0) (b b-0)
    (ks ks-0) (k k))
  (precedes ((0 1) (3 1)) ((1 1) (3 1)) ((2 1) (1 0)) ((3 2) (0 2)))
  (non-orig (ltk a ks) (ltk b ks))
  (uniq-orig ra rb k)
  (operation encryption-test (added-strand init 3) (enc rb k) (0 2))
  (traces
    ((recv (cat a ra)) (send (cat b rb (enc a ra tb (ltk b ks))))
      (recv (cat (enc a k tb (ltk b ks)) (enc rb k))))
    ((recv (cat b rb-0 (enc a ra-0 tb (ltk b ks))))
      (send
        (cat (enc b ra-0 k tb (ltk a ks)) (enc a k tb (ltk b ks))
          rb-0)))
    ((recv (cat a ra-0)) (send (cat b rb-1 (enc a ra-0 tb (ltk b ks)))))
    ((send (cat a-0 ra-1))
      (recv
        (cat (enc b-0 ra-1 k tb-0 (ltk a-0 ks-0))
          (enc a-0 k tb-0 (ltk b-0 ks-0)) rb))
      (send (cat (enc a-0 k tb-0 (ltk b-0 ks-0)) (enc rb k)))))
  (label 9)
  (parent 6)
  (unrealized (3 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton neuman-stubblebine
  (vars (ra rb tb ra-0 rb-0 rb-1 text) (a b ks name) (k skey))
  (defstrand resp 3 (ra ra) (rb rb) (tb tb) (a a) (b b) (ks ks) (k k))
  (defstrand keyserver 2 (ra ra-0) (rb rb-0) (tb tb) (a a) (b b) (ks ks)
    (k k))
  (defstrand resp 2 (ra ra-0) (rb rb-1) (tb tb) (a a) (b b) (ks ks))
  (deflistener k)
  (precedes ((1 1) (3 0)) ((2 1) (1 0)) ((3 1) (0 2)))
  (non-orig (ltk a ks) (ltk b ks))
  (uniq-orig ra rb k)
  (operation encryption-test (added-listener k) (enc rb k) (0 2))
  (traces
    ((recv (cat a ra)) (send (cat b rb (enc a ra tb (ltk b ks))))
      (recv (cat (enc a k tb (ltk b ks)) (enc rb k))))
    ((recv (cat b rb-0 (enc a ra-0 tb (ltk b ks))))
      (send
        (cat (enc b ra-0 k tb (ltk a ks)) (enc a k tb (ltk b ks))
          rb-0)))
    ((recv (cat a ra-0)) (send (cat b rb-1 (enc a ra-0 tb (ltk b ks)))))
    ((recv k) (send k)))
  (label 10)
  (parent 6)
  (unrealized (3 0))
  (comment "empty cohort"))

(defskeleton neuman-stubblebine
  (vars (ra rb tb rb-0 ra-0 text) (a b ks name) (k skey))
  (defstrand resp 3 (ra ra) (rb rb) (tb tb) (a a) (b b) (ks ks) (k k))
  (defstrand keyserver 2 (ra ra) (rb rb-0) (tb tb) (a a) (b b) (ks ks)
    (k k))
  (defstrand init 3 (ra ra-0) (rb rb) (tb tb) (a a) (b b) (ks ks) (k k))
  (precedes ((0 1) (1 0)) ((1 1) (2 1)) ((2 2) (0 2)))
  (non-orig (ltk a ks) (ltk b ks))
  (uniq-orig ra rb k)
  (operation nonce-test (contracted (a-0 a) (b-0 b) (ks-0 ks) (tb-0 tb))
    k (2 1) (enc a k tb (ltk b ks)) (enc b ra k tb (ltk a ks)))
  (traces
    ((recv (cat a ra)) (send (cat b rb (enc a ra tb (ltk b ks))))
      (recv (cat (enc a k tb (ltk b ks)) (enc rb k))))
    ((recv (cat b rb-0 (enc a ra tb (ltk b ks))))
      (send
        (cat (enc b ra k tb (ltk a ks)) (enc a k tb (ltk b ks)) rb-0)))
    ((send (cat a ra-0))
      (recv
        (cat (enc b ra-0 k tb (ltk a ks)) (enc a k tb (ltk b ks)) rb))
      (send (cat (enc a k tb (ltk b ks)) (enc rb k)))))
  (label 11)
  (parent 7)
  (unrealized (2 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton neuman-stubblebine
  (vars (ra rb tb ra-0 rb-0 rb-1 ra-1 text) (a b ks name) (k skey))
  (defstrand resp 3 (ra ra) (rb rb) (tb tb) (a a) (b b) (ks ks) (k k))
  (defstrand keyserver 2 (ra ra-0) (rb rb-0) (tb tb) (a a) (b b) (ks ks)
    (k k))
  (defstrand resp 2 (ra ra-0) (rb rb-1) (tb tb) (a a) (b b) (ks ks))
  (defstrand init 3 (ra ra-1) (rb rb) (tb tb) (a a) (b b) (ks ks) (k k))
  (precedes ((0 1) (3 1)) ((1 1) (3 1)) ((2 1) (1 0)) ((3 2) (0 2)))
  (non-orig (ltk a ks) (ltk b ks))
  (uniq-orig ra rb k)
  (operation nonce-test (contracted (a-0 a) (b-0 b) (ks-0 ks) (tb-0 tb))
    k (3 1) (enc a k tb (ltk b ks)) (enc b ra-0 k tb (ltk a ks)))
  (traces
    ((recv (cat a ra)) (send (cat b rb (enc a ra tb (ltk b ks))))
      (recv (cat (enc a k tb (ltk b ks)) (enc rb k))))
    ((recv (cat b rb-0 (enc a ra-0 tb (ltk b ks))))
      (send
        (cat (enc b ra-0 k tb (ltk a ks)) (enc a k tb (ltk b ks))
          rb-0)))
    ((recv (cat a ra-0)) (send (cat b rb-1 (enc a ra-0 tb (ltk b ks)))))
    ((send (cat a ra-1))
      (recv
        (cat (enc b ra-1 k tb (ltk a ks)) (enc a k tb (ltk b ks)) rb))
      (send (cat (enc a k tb (ltk b ks)) (enc rb k)))))
  (label 12)
  (parent 9)
  (unrealized (3 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton neuman-stubblebine
  (vars (ra rb tb rb-0 text) (a b ks name) (k skey))
  (defstrand resp 3 (ra ra) (rb rb) (tb tb) (a a) (b b) (ks ks) (k k))
  (defstrand keyserver 2 (ra ra) (rb rb-0) (tb tb) (a a) (b b) (ks ks)
    (k k))
  (defstrand init 3 (ra ra) (rb rb) (tb tb) (a a) (b b) (ks ks) (k k))
  (precedes ((0 1) (1 0)) ((1 1) (2 1)) ((2 0) (0 0)) ((2 2) (0 2)))
  (non-orig (ltk a ks) (ltk b ks))
  (uniq-orig ra rb k)
  (operation encryption-test (displaced 3 1 keyserver 2)
    (enc b ra-0 k tb (ltk a ks)) (2 1))
  (traces
    ((recv (cat a ra)) (send (cat b rb (enc a ra tb (ltk b ks))))
      (recv (cat (enc a k tb (ltk b ks)) (enc rb k))))
    ((recv (cat b rb-0 (enc a ra tb (ltk b ks))))
      (send
        (cat (enc b ra k tb (ltk a ks)) (enc a k tb (ltk b ks)) rb-0)))
    ((send (cat a ra))
      (recv (cat (enc b ra k tb (ltk a ks)) (enc a k tb (ltk b ks)) rb))
      (send (cat (enc a k tb (ltk b ks)) (enc rb k)))))
  (label 13)
  (parent 11)
  (unrealized)
  (shape)
  (maps ((0) ((a a) (b b) (ks ks) (ra ra) (rb rb) (k k) (tb tb))))
  (origs (k (1 1)) (ra (2 0)) (rb (0 1))))

(defskeleton neuman-stubblebine
  (vars (ra rb tb ra-0 rb-0 rb-1 text) (a b ks name) (k skey))
  (defstrand resp 3 (ra ra) (rb rb) (tb tb) (a a) (b b) (ks ks) (k k))
  (defstrand keyserver 2 (ra ra-0) (rb rb-0) (tb tb) (a a) (b b) (ks ks)
    (k k))
  (defstrand resp 2 (ra ra-0) (rb rb-1) (tb tb) (a a) (b b) (ks ks))
  (defstrand init 3 (ra ra-0) (rb rb) (tb tb) (a a) (b b) (ks ks) (k k))
  (precedes ((0 1) (3 1)) ((1 1) (3 1)) ((2 1) (1 0)) ((3 2) (0 2)))
  (non-orig (ltk a ks) (ltk b ks))
  (uniq-orig ra rb k)
  (operation encryption-test (displaced 4 1 keyserver 2)
    (enc b ra-1 k tb (ltk a ks)) (3 1))
  (traces
    ((recv (cat a ra)) (send (cat b rb (enc a ra tb (ltk b ks))))
      (recv (cat (enc a k tb (ltk b ks)) (enc rb k))))
    ((recv (cat b rb-0 (enc a ra-0 tb (ltk b ks))))
      (send
        (cat (enc b ra-0 k tb (ltk a ks)) (enc a k tb (ltk b ks))
          rb-0)))
    ((recv (cat a ra-0)) (send (cat b rb-1 (enc a ra-0 tb (ltk b ks)))))
    ((send (cat a ra-0))
      (recv
        (cat (enc b ra-0 k tb (ltk a ks)) (enc a k tb (ltk b ks)) rb))
      (send (cat (enc a k tb (ltk b ks)) (enc rb k)))))
  (label 14)
  (parent 12)
  (unrealized)
  (shape)
  (maps ((0) ((a a) (b b) (ks ks) (ra ra) (rb rb) (k k) (tb tb))))
  (origs (k (1 1)) (rb (0 1))))

(comment "Nothing left to do")

(defprotocol neuman-stubblebine basic
  (defrole init
    (vars (a b ks name) (ra rb text) (k skey) (tb text))
    (trace (send (cat a ra))
      (recv (cat (enc b ra k tb (ltk a ks)) (enc a k tb (ltk b ks)) rb))
      (send (cat (enc a k tb (ltk b ks)) (enc rb k)))))
  (defrole resp
    (vars (a b ks name) (ra rb text) (k skey) (tb text))
    (trace (recv (cat a ra)) (send (cat b rb (enc a ra tb (ltk b ks))))
      (recv (cat (enc a k tb (ltk b ks)) (enc rb k)))))
  (defrole keyserver
    (vars (a b ks name) (ra rb text) (k skey) (tb text))
    (trace (recv (cat b rb (enc a ra tb (ltk b ks))))
      (send
        (cat (enc b ra k tb (ltk a ks)) (enc a k tb (ltk b ks)) rb)))
    (uniq-orig k)))

(defskeleton neuman-stubblebine
  (vars (ra rb tb text) (a b ks name) (k skey))
  (defstrand keyserver 2 (ra ra) (rb rb) (tb tb) (a a) (b b) (ks ks)
    (k k))
  (non-orig (ltk a ks) (ltk b ks))
  (uniq-orig ra rb k)
  (traces
    ((recv (cat b rb (enc a ra tb (ltk b ks))))
      (send
        (cat (enc b ra k tb (ltk a ks)) (enc a k tb (ltk b ks)) rb))))
  (label 15)
  (unrealized (0 0))
  (origs (k (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton neuman-stubblebine
  (vars (ra rb tb rb-0 text) (a b ks name) (k skey))
  (defstrand keyserver 2 (ra ra) (rb rb) (tb tb) (a a) (b b) (ks ks)
    (k k))
  (defstrand resp 2 (ra ra) (rb rb-0) (tb tb) (a a) (b b) (ks ks))
  (precedes ((1 1) (0 0)))
  (non-orig (ltk a ks) (ltk b ks))
  (uniq-orig ra rb k)
  (operation encryption-test (added-strand resp 2)
    (enc a ra tb (ltk b ks)) (0 0))
  (traces
    ((recv (cat b rb (enc a ra tb (ltk b ks))))
      (send
        (cat (enc b ra k tb (ltk a ks)) (enc a k tb (ltk b ks)) rb)))
    ((recv (cat a ra)) (send (cat b rb-0 (enc a ra tb (ltk b ks))))))
  (label 16)
  (parent 15)
  (unrealized)
  (shape)
  (maps ((0) ((a a) (b b) (ks ks) (ra ra) (rb rb) (k k) (tb tb))))
  (origs (k (0 1))))

(comment "Nothing left to do")
