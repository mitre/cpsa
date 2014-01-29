(herald "Denning-Sacco Protocol")

(comment "CPSA 2.3.1")
(comment "All input read from denning-sacco.scm")

(defprotocol denning-sacco basic
  (defrole init
    (vars (a b ks name) (k skey) (ta text))
    (trace (send (cat a b))
      (recv
        (cat (enc b (pubk b) (privk ks)) (enc a (pubk a) (privk ks))))
      (send
        (enc (enc a b k ta (privk a)) (enc b (pubk b) (privk ks))
          (enc a (pubk a) (privk ks)) (pubk b)))))
  (defrole resp
    (vars (a b ks name) (k skey) (ta text))
    (trace
      (recv
        (enc (enc a b k ta (privk a)) (enc b (pubk b) (privk ks))
          (enc a (pubk a) (privk ks)) (pubk b)))))
  (defrole keyserver
    (vars (a b ks name))
    (trace (recv (cat a b))
      (send
        (cat (enc b (pubk b) (privk ks))
          (enc a (pubk a) (privk ks)))))))

(defskeleton denning-sacco
  (vars (ta text) (a b ks name) (k skey))
  (defstrand resp 1 (ta ta) (a a) (b b) (ks ks) (k k))
  (non-orig (privk a) (privk b) (privk ks))
  (uniq-orig k)
  (traces
    ((recv
       (enc (enc a b k ta (privk a)) (enc b (pubk b) (privk ks))
         (enc a (pubk a) (privk ks)) (pubk b)))))
  (label 0)
  (unrealized (0 0))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton denning-sacco
  (vars (ta text) (a b ks ks-0 name) (k skey))
  (defstrand resp 1 (ta ta) (a a) (b b) (ks ks) (k k))
  (defstrand init 3 (ta ta) (a a) (b b) (ks ks-0) (k k))
  (precedes ((1 2) (0 0)))
  (non-orig (privk a) (privk b) (privk ks))
  (uniq-orig k)
  (operation encryption-test (added-strand init 3)
    (enc a b k ta (privk a)) (0 0))
  (traces
    ((recv
       (enc (enc a b k ta (privk a)) (enc b (pubk b) (privk ks))
         (enc a (pubk a) (privk ks)) (pubk b))))
    ((send (cat a b))
      (recv
        (cat (enc b (pubk b) (privk ks-0))
          (enc a (pubk a) (privk ks-0))))
      (send
        (enc (enc a b k ta (privk a)) (enc b (pubk b) (privk ks-0))
          (enc a (pubk a) (privk ks-0)) (pubk b)))))
  (label 1)
  (parent 0)
  (unrealized (0 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton denning-sacco
  (vars (ta text) (a b ks name) (k skey))
  (defstrand resp 1 (ta ta) (a a) (b b) (ks ks) (k k))
  (defstrand init 3 (ta ta) (a a) (b b) (ks ks) (k k))
  (precedes ((1 2) (0 0)))
  (non-orig (privk a) (privk b) (privk ks))
  (uniq-orig k)
  (operation encryption-test (contracted (ks-0 ks))
    (enc a b k ta (privk a)) (0 0)
    (enc (enc a b k ta (privk a)) (enc b (pubk b) (privk ks))
      (enc a (pubk a) (privk ks)) (pubk b)))
  (traces
    ((recv
       (enc (enc a b k ta (privk a)) (enc b (pubk b) (privk ks))
         (enc a (pubk a) (privk ks)) (pubk b))))
    ((send (cat a b))
      (recv
        (cat (enc b (pubk b) (privk ks)) (enc a (pubk a) (privk ks))))
      (send
        (enc (enc a b k ta (privk a)) (enc b (pubk b) (privk ks))
          (enc a (pubk a) (privk ks)) (pubk b)))))
  (label 2)
  (parent 1)
  (unrealized (1 1))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton denning-sacco
  (vars (ta text) (a b ks a-0 name) (k skey))
  (defstrand resp 1 (ta ta) (a a) (b b) (ks ks) (k k))
  (defstrand init 3 (ta ta) (a a) (b b) (ks ks) (k k))
  (defstrand keyserver 2 (a a-0) (b b) (ks ks))
  (precedes ((1 2) (0 0)) ((2 1) (1 1)))
  (non-orig (privk a) (privk b) (privk ks))
  (uniq-orig k)
  (operation encryption-test (added-strand keyserver 2)
    (enc b (pubk b) (privk ks)) (1 1))
  (traces
    ((recv
       (enc (enc a b k ta (privk a)) (enc b (pubk b) (privk ks))
         (enc a (pubk a) (privk ks)) (pubk b))))
    ((send (cat a b))
      (recv
        (cat (enc b (pubk b) (privk ks)) (enc a (pubk a) (privk ks))))
      (send
        (enc (enc a b k ta (privk a)) (enc b (pubk b) (privk ks))
          (enc a (pubk a) (privk ks)) (pubk b))))
    ((recv (cat a-0 b))
      (send
        (cat (enc b (pubk b) (privk ks))
          (enc a-0 (pubk a-0) (privk ks))))))
  (label 3)
  (parent 2)
  (unrealized (1 1))
  (comment "4 in cohort - 4 not yet seen"))

(defskeleton denning-sacco
  (vars (ta text) (a b ks b-0 name) (k skey))
  (defstrand resp 1 (ta ta) (a a) (b b) (ks ks) (k k))
  (defstrand init 3 (ta ta) (a a) (b b) (ks ks) (k k))
  (defstrand keyserver 2 (a b) (b b-0) (ks ks))
  (precedes ((1 2) (0 0)) ((2 1) (1 1)))
  (non-orig (privk a) (privk b) (privk ks))
  (uniq-orig k)
  (operation encryption-test (added-strand keyserver 2)
    (enc b (pubk b) (privk ks)) (1 1))
  (traces
    ((recv
       (enc (enc a b k ta (privk a)) (enc b (pubk b) (privk ks))
         (enc a (pubk a) (privk ks)) (pubk b))))
    ((send (cat a b))
      (recv
        (cat (enc b (pubk b) (privk ks)) (enc a (pubk a) (privk ks))))
      (send
        (enc (enc a b k ta (privk a)) (enc b (pubk b) (privk ks))
          (enc a (pubk a) (privk ks)) (pubk b))))
    ((recv (cat b b-0))
      (send
        (cat (enc b-0 (pubk b-0) (privk ks))
          (enc b (pubk b) (privk ks))))))
  (label 4)
  (parent 2)
  (unrealized (1 1))
  (comment "4 in cohort - 4 not yet seen"))

(defskeleton denning-sacco
  (vars (ta text) (b ks a name) (k skey))
  (defstrand resp 1 (ta ta) (a b) (b b) (ks ks) (k k))
  (defstrand init 3 (ta ta) (a b) (b b) (ks ks) (k k))
  (defstrand keyserver 2 (a a) (b b) (ks ks))
  (precedes ((1 2) (0 0)) ((2 1) (1 1)))
  (non-orig (privk b) (privk ks))
  (uniq-orig k)
  (operation encryption-test (displaced 3 2 keyserver 2)
    (enc a-0 (pubk a-0) (privk ks)) (1 1))
  (traces
    ((recv
       (enc (enc b b k ta (privk b)) (enc b (pubk b) (privk ks))
         (enc b (pubk b) (privk ks)) (pubk b))))
    ((send (cat b b))
      (recv
        (cat (enc b (pubk b) (privk ks)) (enc b (pubk b) (privk ks))))
      (send
        (enc (enc b b k ta (privk b)) (enc b (pubk b) (privk ks))
          (enc b (pubk b) (privk ks)) (pubk b))))
    ((recv (cat a b))
      (send
        (cat (enc b (pubk b) (privk ks)) (enc a (pubk a) (privk ks))))))
  (label 5)
  (parent 3)
  (unrealized)
  (shape)
  (maps ((0) ((a b) (b b) (ks ks) (k k) (ta ta))))
  (origs (k (1 2))))

(defskeleton denning-sacco
  (vars (ta text) (a b ks a-0 a-1 name) (k skey))
  (defstrand resp 1 (ta ta) (a a) (b b) (ks ks) (k k))
  (defstrand init 3 (ta ta) (a a) (b b) (ks ks) (k k))
  (defstrand keyserver 2 (a a-0) (b b) (ks ks))
  (defstrand keyserver 2 (a a-1) (b a) (ks ks))
  (precedes ((1 2) (0 0)) ((2 1) (1 1)) ((3 1) (1 1)))
  (non-orig (privk a) (privk b) (privk ks))
  (uniq-orig k)
  (operation encryption-test (added-strand keyserver 2)
    (enc a (pubk a) (privk ks)) (1 1))
  (traces
    ((recv
       (enc (enc a b k ta (privk a)) (enc b (pubk b) (privk ks))
         (enc a (pubk a) (privk ks)) (pubk b))))
    ((send (cat a b))
      (recv
        (cat (enc b (pubk b) (privk ks)) (enc a (pubk a) (privk ks))))
      (send
        (enc (enc a b k ta (privk a)) (enc b (pubk b) (privk ks))
          (enc a (pubk a) (privk ks)) (pubk b))))
    ((recv (cat a-0 b))
      (send
        (cat (enc b (pubk b) (privk ks))
          (enc a-0 (pubk a-0) (privk ks)))))
    ((recv (cat a-1 a))
      (send
        (cat (enc a (pubk a) (privk ks))
          (enc a-1 (pubk a-1) (privk ks))))))
  (label 6)
  (parent 3)
  (unrealized)
  (shape)
  (maps ((0) ((a a) (b b) (ks ks) (k k) (ta ta))))
  (origs (k (1 2))))

(defskeleton denning-sacco
  (vars (ta text) (b ks a name) (k skey))
  (defstrand resp 1 (ta ta) (a a) (b b) (ks ks) (k k))
  (defstrand init 3 (ta ta) (a a) (b b) (ks ks) (k k))
  (defstrand keyserver 2 (a a) (b b) (ks ks))
  (precedes ((1 2) (0 0)) ((2 1) (1 1)))
  (non-orig (privk b) (privk ks) (privk a))
  (uniq-orig k)
  (operation encryption-test (displaced 3 2 keyserver 2)
    (enc a-0 (pubk a-0) (privk ks)) (1 1))
  (traces
    ((recv
       (enc (enc a b k ta (privk a)) (enc b (pubk b) (privk ks))
         (enc a (pubk a) (privk ks)) (pubk b))))
    ((send (cat a b))
      (recv
        (cat (enc b (pubk b) (privk ks)) (enc a (pubk a) (privk ks))))
      (send
        (enc (enc a b k ta (privk a)) (enc b (pubk b) (privk ks))
          (enc a (pubk a) (privk ks)) (pubk b))))
    ((recv (cat a b))
      (send
        (cat (enc b (pubk b) (privk ks)) (enc a (pubk a) (privk ks))))))
  (label 7)
  (parent 3)
  (unrealized)
  (shape)
  (maps ((0) ((a a) (b b) (ks ks) (k k) (ta ta))))
  (origs (k (1 2))))

(defskeleton denning-sacco
  (vars (ta text) (a b ks a-0 b-0 name) (k skey))
  (defstrand resp 1 (ta ta) (a a) (b b) (ks ks) (k k))
  (defstrand init 3 (ta ta) (a a) (b b) (ks ks) (k k))
  (defstrand keyserver 2 (a a-0) (b b) (ks ks))
  (defstrand keyserver 2 (a a) (b b-0) (ks ks))
  (precedes ((1 2) (0 0)) ((2 1) (1 1)) ((3 1) (1 1)))
  (non-orig (privk a) (privk b) (privk ks))
  (uniq-orig k)
  (operation encryption-test (added-strand keyserver 2)
    (enc a (pubk a) (privk ks)) (1 1))
  (traces
    ((recv
       (enc (enc a b k ta (privk a)) (enc b (pubk b) (privk ks))
         (enc a (pubk a) (privk ks)) (pubk b))))
    ((send (cat a b))
      (recv
        (cat (enc b (pubk b) (privk ks)) (enc a (pubk a) (privk ks))))
      (send
        (enc (enc a b k ta (privk a)) (enc b (pubk b) (privk ks))
          (enc a (pubk a) (privk ks)) (pubk b))))
    ((recv (cat a-0 b))
      (send
        (cat (enc b (pubk b) (privk ks))
          (enc a-0 (pubk a-0) (privk ks)))))
    ((recv (cat a b-0))
      (send
        (cat (enc b-0 (pubk b-0) (privk ks))
          (enc a (pubk a) (privk ks))))))
  (label 8)
  (parent 3)
  (unrealized)
  (shape)
  (maps ((0) ((a a) (b b) (ks ks) (k k) (ta ta))))
  (origs (k (1 2))))

(defskeleton denning-sacco
  (vars (ta text) (b ks b-0 name) (k skey))
  (defstrand resp 1 (ta ta) (a b-0) (b b) (ks ks) (k k))
  (defstrand init 3 (ta ta) (a b-0) (b b) (ks ks) (k k))
  (defstrand keyserver 2 (a b) (b b-0) (ks ks))
  (precedes ((1 2) (0 0)) ((2 1) (1 1)))
  (non-orig (privk b) (privk ks) (privk b-0))
  (uniq-orig k)
  (operation encryption-test (displaced 3 2 keyserver 2)
    (enc a (pubk a) (privk ks)) (1 1))
  (traces
    ((recv
       (enc (enc b-0 b k ta (privk b-0)) (enc b (pubk b) (privk ks))
         (enc b-0 (pubk b-0) (privk ks)) (pubk b))))
    ((send (cat b-0 b))
      (recv
        (cat (enc b (pubk b) (privk ks))
          (enc b-0 (pubk b-0) (privk ks))))
      (send
        (enc (enc b-0 b k ta (privk b-0)) (enc b (pubk b) (privk ks))
          (enc b-0 (pubk b-0) (privk ks)) (pubk b))))
    ((recv (cat b b-0))
      (send
        (cat (enc b-0 (pubk b-0) (privk ks))
          (enc b (pubk b) (privk ks))))))
  (label 9)
  (parent 4)
  (unrealized)
  (shape)
  (maps ((0) ((a b-0) (b b) (ks ks) (k k) (ta ta))))
  (origs (k (1 2))))

(defskeleton denning-sacco
  (vars (ta text) (a b ks b-0 a-0 name) (k skey))
  (defstrand resp 1 (ta ta) (a a) (b b) (ks ks) (k k))
  (defstrand init 3 (ta ta) (a a) (b b) (ks ks) (k k))
  (defstrand keyserver 2 (a b) (b b-0) (ks ks))
  (defstrand keyserver 2 (a a-0) (b a) (ks ks))
  (precedes ((1 2) (0 0)) ((2 1) (1 1)) ((3 1) (1 1)))
  (non-orig (privk a) (privk b) (privk ks))
  (uniq-orig k)
  (operation encryption-test (added-strand keyserver 2)
    (enc a (pubk a) (privk ks)) (1 1))
  (traces
    ((recv
       (enc (enc a b k ta (privk a)) (enc b (pubk b) (privk ks))
         (enc a (pubk a) (privk ks)) (pubk b))))
    ((send (cat a b))
      (recv
        (cat (enc b (pubk b) (privk ks)) (enc a (pubk a) (privk ks))))
      (send
        (enc (enc a b k ta (privk a)) (enc b (pubk b) (privk ks))
          (enc a (pubk a) (privk ks)) (pubk b))))
    ((recv (cat b b-0))
      (send
        (cat (enc b-0 (pubk b-0) (privk ks))
          (enc b (pubk b) (privk ks)))))
    ((recv (cat a-0 a))
      (send
        (cat (enc a (pubk a) (privk ks))
          (enc a-0 (pubk a-0) (privk ks))))))
  (label 10)
  (parent 4)
  (unrealized)
  (shape)
  (maps ((0) ((a a) (b b) (ks ks) (k k) (ta ta))))
  (origs (k (1 2))))

(defskeleton denning-sacco
  (vars (ta text) (b ks b-0 name) (k skey))
  (defstrand resp 1 (ta ta) (a b) (b b) (ks ks) (k k))
  (defstrand init 3 (ta ta) (a b) (b b) (ks ks) (k k))
  (defstrand keyserver 2 (a b) (b b-0) (ks ks))
  (precedes ((1 2) (0 0)) ((2 1) (1 1)))
  (non-orig (privk b) (privk ks))
  (uniq-orig k)
  (operation encryption-test (displaced 3 2 keyserver 2)
    (enc a (pubk a) (privk ks)) (1 1))
  (traces
    ((recv
       (enc (enc b b k ta (privk b)) (enc b (pubk b) (privk ks))
         (enc b (pubk b) (privk ks)) (pubk b))))
    ((send (cat b b))
      (recv
        (cat (enc b (pubk b) (privk ks)) (enc b (pubk b) (privk ks))))
      (send
        (enc (enc b b k ta (privk b)) (enc b (pubk b) (privk ks))
          (enc b (pubk b) (privk ks)) (pubk b))))
    ((recv (cat b b-0))
      (send
        (cat (enc b-0 (pubk b-0) (privk ks))
          (enc b (pubk b) (privk ks))))))
  (label 11)
  (parent 4)
  (unrealized)
  (shape)
  (maps ((0) ((a b) (b b) (ks ks) (k k) (ta ta))))
  (origs (k (1 2))))

(defskeleton denning-sacco
  (vars (ta text) (a b ks b-0 b-1 name) (k skey))
  (defstrand resp 1 (ta ta) (a a) (b b) (ks ks) (k k))
  (defstrand init 3 (ta ta) (a a) (b b) (ks ks) (k k))
  (defstrand keyserver 2 (a b) (b b-0) (ks ks))
  (defstrand keyserver 2 (a a) (b b-1) (ks ks))
  (precedes ((1 2) (0 0)) ((2 1) (1 1)) ((3 1) (1 1)))
  (non-orig (privk a) (privk b) (privk ks))
  (uniq-orig k)
  (operation encryption-test (added-strand keyserver 2)
    (enc a (pubk a) (privk ks)) (1 1))
  (traces
    ((recv
       (enc (enc a b k ta (privk a)) (enc b (pubk b) (privk ks))
         (enc a (pubk a) (privk ks)) (pubk b))))
    ((send (cat a b))
      (recv
        (cat (enc b (pubk b) (privk ks)) (enc a (pubk a) (privk ks))))
      (send
        (enc (enc a b k ta (privk a)) (enc b (pubk b) (privk ks))
          (enc a (pubk a) (privk ks)) (pubk b))))
    ((recv (cat b b-0))
      (send
        (cat (enc b-0 (pubk b-0) (privk ks))
          (enc b (pubk b) (privk ks)))))
    ((recv (cat a b-1))
      (send
        (cat (enc b-1 (pubk b-1) (privk ks))
          (enc a (pubk a) (privk ks))))))
  (label 12)
  (parent 4)
  (unrealized)
  (shape)
  (maps ((0) ((a a) (b b) (ks ks) (k k) (ta ta))))
  (origs (k (1 2))))

(comment "Nothing left to do")
