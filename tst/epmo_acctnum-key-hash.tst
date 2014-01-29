(herald
  "Electronic Purchase with Money Order Protocol Variant with Key Hashing"
  (comment "This version includes account numbers in exchanges"))

(comment "CPSA 2.3.1")
(comment "All input read from epmo_acctnum-key-hash.scm")

(defprotocol epmo_acctnum basic
  (defrole bank
    (vars (b c m name) (acctnum nc nm nb price text))
    (trace (recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" (cat b m nb nm)) (privk m))))
    (annotations b
      (1
        (forall ((pm name))
          (implies
            (and (authtransfer c acctnum b price pm nm)
              (reqtransfer pm b price pm nm))
            (dotransfer acctnum b price pm nm))))
      (2
        (and (says c (authtransfer c acctnum b price m nm))
          (says m (reqtransfer m b price m nm))))))
  (defrole customer
    (vars (b c m name) (acctnum nb nc nm goods price text))
    (trace (send (enc c nc goods (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum price (pubk b)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb)))
    (non-orig (privk b))
    (uniq-orig nc)
    (annotations c
      (1
        (says m
          (implies
            (exists ((acctnum2 text))
              (dotransfer acctnum2 b price m nm)) (doship m goods c))))
      (3
        (says b
          (forall ((pm name))
            (implies
              (and (authtransfer c acctnum b price m nm)
                (reqtransfer pm b price pm nm))
              (dotransfer acctnum b price pm nm)))))
      (4 (authtransfer c acctnum b price m nm))))
  (defrole merchant
    (vars (b c m name) (nb nc nm goods price text))
    (trace (recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))
      (send (enc (enc "hash" (cat b m nb nm)) (privk m))))
    (uniq-orig nm)
    (annotations m
      (1
        (implies
          (exists ((acctnum2 text)) (dotransfer acctnum2 b price m nm))
          (doship m goods c)))
      (2
        (and
          (says b
            (forall ((pm name))
              (exists ((acctnum2 text))
                (implies
                  (and (authtransfer c acctnum2 b price m nm)
                    (reqtransfer pm b price pm nm))
                  (dotransfer acctnum2 b price pm nm)))))
          (says c
            (exists ((acctnum2 text))
              (authtransfer c acctnum2 b price m nm)))))
      (3 (and (reqtransfer m b price m nm) (doship m goods c))))))

(defskeleton epmo_acctnum
  (vars (nm nc nb goods price text) (b m c name))
  (defstrand merchant 4 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b) (c c) (m m))
  (non-orig (privk b) (privk m) (privk c))
  (uniq-orig nm nc nb)
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))
      (send (enc (enc "hash" (cat b m nb nm)) (privk m)))))
  (label 0)
  (unrealized (0 2))
  (origs (nm (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo_acctnum
  (vars (nm nc nb goods price acctnum text) (b m c name))
  (defstrand merchant 4 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b) (c c) (m m))
  (defstrand bank 2 (acctnum acctnum) (nc nc) (nm nm) (nb nb)
    (price price) (b b) (c c))
  (precedes ((0 1) (1 0)) ((1 1) (0 2)))
  (non-orig (privk b) (privk m) (privk c))
  (uniq-orig nm nc nb)
  (operation encryption-test (added-strand bank 2)
    (enc (enc "hash" (cat c nc nb nm price)) (privk b)) (0 2))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))
      (send (enc (enc "hash" (cat b m nb nm)) (privk m))))
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))))
  (label 1)
  (parent 0)
  (unrealized (0 2) (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo_acctnum
  (vars (nm nc nb goods price acctnum acctnum-0 goods-0 text)
    (b m c b-0 name))
  (defstrand merchant 4 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b) (c c) (m m))
  (defstrand bank 2 (acctnum acctnum) (nc nc) (nm nm) (nb nb)
    (price price) (b b) (c c))
  (defstrand customer 3 (acctnum acctnum-0) (nc nc) (nm nm)
    (goods goods-0) (price price) (b b-0) (c c) (m m))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (0 0)) ((2 2) (1 0)))
  (non-orig (privk b) (privk m) (privk c) (privk b-0))
  (uniq-orig nm nc nb)
  (operation nonce-test (added-strand customer 3) nm (1 0)
    (enc nc nm m price (pubk c)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))
      (send (enc (enc "hash" (cat b m nb nm)) (privk m))))
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum-0 price (pubk b-0)))))
  (label 2)
  (parent 1)
  (unrealized (0 0) (0 2) (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo_acctnum
  (vars (nm nc nb goods price acctnum goods-0 text) (m c b name))
  (defstrand merchant 4 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b) (c c) (m m))
  (defstrand bank 2 (acctnum acctnum) (nc nc) (nm nm) (nb nb)
    (price price) (b b) (c c))
  (defstrand customer 3 (acctnum acctnum) (nc nc) (nm nm)
    (goods goods-0) (price price) (b b) (c c) (m m))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (0 0)) ((2 2) (1 0)))
  (non-orig (privk m) (privk c) (privk b))
  (uniq-orig nm nc nb)
  (operation nonce-test (contracted (b-0 b) (acctnum-0 acctnum)) nm
    (1 0) (enc nc nm m price (pubk c))
    (enc c nc nm acctnum price (pubk b)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))
      (send (enc (enc "hash" (cat b m nb nm)) (privk m))))
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum price (pubk b)))))
  (label 3)
  (parent 2)
  (unrealized (0 0) (0 2))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton epmo_acctnum
  (vars (nm nc nb price acctnum goods text) (m c b name))
  (defstrand merchant 4 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b) (c c) (m m))
  (defstrand bank 2 (acctnum acctnum) (nc nc) (nm nm) (nb nb)
    (price price) (b b) (c c))
  (defstrand customer 3 (acctnum acctnum) (nc nc) (nm nm) (goods goods)
    (price price) (b b) (c c) (m m))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (0 0)) ((2 2) (1 0)))
  (non-orig (privk m) (privk c) (privk b))
  (uniq-orig nm nc nb)
  (operation nonce-test (contracted (goods-0 goods)) nc (0 0)
    (enc c nc goods (pubk m)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))
      (send (enc (enc "hash" (cat b m nb nm)) (privk m))))
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum price (pubk b)))))
  (label 4)
  (parent 3)
  (unrealized (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo_acctnum
  (vars (nm nc nb goods price acctnum goods-0 nm-0 price-0 text)
    (m c b name))
  (defstrand merchant 4 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b) (c c) (m m))
  (defstrand bank 2 (acctnum acctnum) (nc nc) (nm nm) (nb nb)
    (price price) (b b) (c c))
  (defstrand customer 3 (acctnum acctnum) (nc nc) (nm nm)
    (goods goods-0) (price price) (b b) (c c) (m m))
  (defstrand merchant 2 (nc nc) (nm nm-0) (goods goods-0)
    (price price-0) (c c) (m m))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (3 0)) ((2 2) (1 0))
    ((3 1) (0 0)))
  (non-orig (privk m) (privk c) (privk b))
  (uniq-orig nm nc nb nm-0)
  (operation nonce-test (added-strand merchant 2) nc (0 0)
    (enc c nc goods-0 (pubk m)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))
      (send (enc (enc "hash" (cat b m nb nm)) (privk m))))
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum price (pubk b))))
    ((recv (enc c nc goods-0 (pubk m)))
      (send (enc nc nm-0 m price-0 (pubk c)))))
  (label 5)
  (parent 3)
  (unrealized (0 0) (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo_acctnum
  (vars (nc nb acctnum nm goods price text) (c b m name))
  (defstrand merchant 4 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b) (c c) (m m))
  (defstrand bank 2 (acctnum acctnum) (nc nc) (nm nm) (nb nb)
    (price price) (b b) (c c))
  (defstrand customer 5 (acctnum acctnum) (nb nb) (nc nc) (nm nm)
    (goods goods) (price price) (b b) (c c) (m m))
  (precedes ((0 1) (2 1)) ((1 1) (2 3)) ((2 0) (0 0)) ((2 2) (1 0))
    ((2 4) (0 2)))
  (non-orig (privk c) (privk b) (privk m))
  (uniq-orig nc nb nm)
  (operation nonce-test (displaced 2 3 customer 5) nb (0 2)
    (enc nc nb (pubk c)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))
      (send (enc (enc "hash" (cat b m nb nm)) (privk m))))
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum price (pubk b)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))))
  (label 6)
  (parent 4)
  (unrealized)
  (shape)
  (maps
    ((0)
      ((b b) (m m) (c c) (nm nm) (nc nc) (nb nb) (goods goods)
        (price price))))
  (origs (nc (2 0)) (nm (0 1)) (nb (1 1))))

(defskeleton epmo_acctnum
  (vars (nm nc nb price acctnum goods nm-0 price-0 text) (m c b name))
  (defstrand merchant 4 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b) (c c) (m m))
  (defstrand bank 2 (acctnum acctnum) (nc nc) (nm nm) (nb nb)
    (price price) (b b) (c c))
  (defstrand customer 3 (acctnum acctnum) (nc nc) (nm nm) (goods goods)
    (price price) (b b) (c c) (m m))
  (defstrand merchant 2 (nc nc) (nm nm-0) (goods goods) (price price-0)
    (c c) (m m))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (3 0)) ((2 2) (1 0))
    ((3 1) (0 0)))
  (non-orig (privk m) (privk c) (privk b))
  (uniq-orig nm nc nb nm-0)
  (operation nonce-test (contracted (goods-0 goods)) nc (0 0)
    (enc nc nm-0 m price-0 (pubk c)) (enc c nc goods (pubk m)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))
      (send (enc (enc "hash" (cat b m nb nm)) (privk m))))
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum price (pubk b))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm-0 m price-0 (pubk c)))))
  (label 7)
  (parent 5)
  (unrealized (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo_acctnum
  (vars (nc nb nm price acctnum nm-0 goods price-0 text) (c b m name))
  (defstrand merchant 4 (nb nb) (nc nc) (nm nm-0) (goods goods)
    (price price-0) (b b) (c c) (m m))
  (defstrand bank 2 (acctnum acctnum) (nc nc) (nm nm-0) (nb nb)
    (price price-0) (b b) (c c))
  (defstrand merchant 2 (nc nc) (nm nm) (goods goods) (price price)
    (c c) (m m))
  (defstrand customer 5 (acctnum acctnum) (nb nb) (nc nc) (nm nm-0)
    (goods goods) (price price-0) (b b) (c c) (m m))
  (precedes ((0 1) (3 1)) ((1 1) (3 3)) ((2 1) (0 0)) ((3 0) (2 0))
    ((3 2) (1 0)) ((3 4) (0 2)))
  (non-orig (privk c) (privk b) (privk m))
  (uniq-orig nc nb nm nm-0)
  (operation nonce-test (displaced 2 4 customer 5) nb (0 2)
    (enc nc nb (pubk c)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm-0 m price-0 (pubk c)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm-0 price-0)) (privk b))
          nb)) (send (enc (enc "hash" (cat b m nb nm-0)) (privk m))))
    ((recv (enc c nc nm-0 acctnum price-0 (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm-0 price-0)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nm-0 m price-0 (pubk c)))
      (send (enc c nc nm-0 acctnum price-0 (pubk b)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm-0 price-0)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm-0 price-0)) (privk b))
          nb))))
  (label 8)
  (parent 7)
  (seen 6)
  (unrealized)
  (comment "1 in cohort - 0 not yet seen"))

(comment "Nothing left to do")

(defprotocol epmo_acctnum basic
  (defrole bank
    (vars (b c m name) (acctnum nc nm nb price text))
    (trace (recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" (cat b m nb nm)) (privk m))))
    (annotations b
      (1
        (forall ((pm name))
          (implies
            (and (authtransfer c acctnum b price pm nm)
              (reqtransfer pm b price pm nm))
            (dotransfer acctnum b price pm nm))))
      (2
        (and (says c (authtransfer c acctnum b price m nm))
          (says m (reqtransfer m b price m nm))))))
  (defrole customer
    (vars (b c m name) (acctnum nb nc nm goods price text))
    (trace (send (enc c nc goods (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum price (pubk b)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb)))
    (non-orig (privk b))
    (uniq-orig nc)
    (annotations c
      (1
        (says m
          (implies
            (exists ((acctnum2 text))
              (dotransfer acctnum2 b price m nm)) (doship m goods c))))
      (3
        (says b
          (forall ((pm name))
            (implies
              (and (authtransfer c acctnum b price m nm)
                (reqtransfer pm b price pm nm))
              (dotransfer acctnum b price pm nm)))))
      (4 (authtransfer c acctnum b price m nm))))
  (defrole merchant
    (vars (b c m name) (nb nc nm goods price text))
    (trace (recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))
      (send (enc (enc "hash" (cat b m nb nm)) (privk m))))
    (uniq-orig nm)
    (annotations m
      (1
        (implies
          (exists ((acctnum2 text)) (dotransfer acctnum2 b price m nm))
          (doship m goods c)))
      (2
        (and
          (says b
            (forall ((pm name))
              (exists ((acctnum2 text))
                (implies
                  (and (authtransfer c acctnum2 b price m nm)
                    (reqtransfer pm b price pm nm))
                  (dotransfer acctnum2 b price pm nm)))))
          (says c
            (exists ((acctnum2 text))
              (authtransfer c acctnum2 b price m nm)))))
      (3 (and (reqtransfer m b price m nm) (doship m goods c))))))

(defskeleton epmo_acctnum
  (vars (nm nb nc acctnum price text) (b m c name))
  (defstrand bank 3 (acctnum acctnum) (nc nc) (nm nm) (nb nb)
    (price price) (b b) (c c) (m m))
  (non-orig (privk b) (privk m) (privk c))
  (uniq-orig nm nb nc)
  (traces
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" (cat b m nb nm)) (privk m)))))
  (label 9)
  (unrealized (0 2))
  (origs (nb (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo_acctnum
  (vars (nm nb nc acctnum price nc-0 goods price-0 text)
    (b m c c-0 name))
  (defstrand bank 3 (acctnum acctnum) (nc nc) (nm nm) (nb nb)
    (price price) (b b) (c c) (m m))
  (defstrand merchant 4 (nb nb) (nc nc-0) (nm nm) (goods goods)
    (price price-0) (b b) (c c-0) (m m))
  (precedes ((0 1) (1 2)) ((1 1) (0 0)) ((1 3) (0 2)))
  (non-orig (privk b) (privk m) (privk c))
  (uniq-orig nm nb nc)
  (operation encryption-test (added-strand merchant 4)
    (enc (enc "hash" (cat b m nb nm)) (privk m)) (0 2))
  (traces
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" (cat b m nb nm)) (privk m))))
    ((recv (enc c-0 nc-0 goods (pubk m)))
      (send (enc nc-0 nm m price-0 (pubk c-0)))
      (recv
        (cat (enc (enc "hash" (cat c-0 nc-0 nb nm price-0)) (privk b))
          nb)) (send (enc (enc "hash" (cat b m nb nm)) (privk m)))))
  (label 10)
  (parent 9)
  (unrealized (1 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo_acctnum
  (vars (nm nb nc acctnum price goods text) (b m c name))
  (defstrand bank 3 (acctnum acctnum) (nc nc) (nm nm) (nb nb)
    (price price) (b b) (c c) (m m))
  (defstrand merchant 4 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b) (c c) (m m))
  (precedes ((0 1) (1 2)) ((1 1) (0 0)) ((1 3) (0 2)))
  (non-orig (privk b) (privk m) (privk c))
  (uniq-orig nm nb nc)
  (operation encryption-test (displaced 2 0 bank 2)
    (enc (enc "hash" (cat c-0 nc-0 nb nm price-0)) (privk b)) (1 2))
  (traces
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" (cat b m nb nm)) (privk m))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))
      (send (enc (enc "hash" (cat b m nb nm)) (privk m)))))
  (label 11)
  (parent 10)
  (unrealized (0 0) (1 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo_acctnum
  (vars
    (nm nb nc acctnum price goods acctnum-0 nm-0 goods-0 price-0 text)
    (b m c b-0 m-0 name))
  (defstrand bank 3 (acctnum acctnum) (nc nc) (nm nm) (nb nb)
    (price price) (b b) (c c) (m m))
  (defstrand merchant 4 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b) (c c) (m m))
  (defstrand customer 5 (acctnum acctnum-0) (nb nb) (nc nc) (nm nm-0)
    (goods goods-0) (price price-0) (b b-0) (c c) (m m-0))
  (precedes ((0 1) (2 3)) ((1 1) (0 0)) ((1 3) (0 2)) ((2 0) (1 0))
    ((2 4) (1 2)))
  (non-orig (privk b) (privk m) (privk c) (privk b-0))
  (uniq-orig nm nb nc)
  (operation nonce-test (added-strand customer 5) nb (1 2)
    (enc nc nb (pubk c)))
  (traces
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" (cat b m nb nm)) (privk m))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))
      (send (enc (enc "hash" (cat b m nb nm)) (privk m))))
    ((send (enc c nc goods-0 (pubk m-0)))
      (recv (enc nc nm-0 m-0 price-0 (pubk c)))
      (send (enc c nc nm-0 acctnum-0 price-0 (pubk b-0)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm-0 price-0)) (privk b-0))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm-0 price-0)) (privk b-0))
          nb))))
  (label 12)
  (parent 11)
  (unrealized (0 0) (2 3))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo_acctnum
  (vars (nm nb nc acctnum price goods acctnum-0 goods-0 text)
    (b m c m-0 name))
  (defstrand bank 3 (acctnum acctnum) (nc nc) (nm nm) (nb nb)
    (price price) (b b) (c c) (m m))
  (defstrand merchant 4 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b) (c c) (m m))
  (defstrand customer 5 (acctnum acctnum-0) (nb nb) (nc nc) (nm nm)
    (goods goods-0) (price price) (b b) (c c) (m m-0))
  (precedes ((0 1) (2 3)) ((1 1) (0 0)) ((1 1) (2 1)) ((1 3) (0 2))
    ((2 0) (1 0)) ((2 4) (1 2)))
  (non-orig (privk b) (privk m) (privk c))
  (uniq-orig nm nb nc)
  (operation encryption-test (displaced 3 0 bank 2)
    (enc (enc "hash" (cat c nc nb nm-0 price-0)) (privk b-0)) (2 3))
  (traces
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" (cat b m nb nm)) (privk m))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))
      (send (enc (enc "hash" (cat b m nb nm)) (privk m))))
    ((send (enc c nc goods-0 (pubk m-0)))
      (recv (enc nc nm m-0 price (pubk c)))
      (send (enc c nc nm acctnum-0 price (pubk b)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))))
  (label 13)
  (parent 12)
  (unrealized (0 0) (2 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo_acctnum
  (vars (nm nb nc acctnum price goods acctnum-0 goods-0 text)
    (b m c name))
  (defstrand bank 3 (acctnum acctnum) (nc nc) (nm nm) (nb nb)
    (price price) (b b) (c c) (m m))
  (defstrand merchant 4 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b) (c c) (m m))
  (defstrand customer 5 (acctnum acctnum-0) (nb nb) (nc nc) (nm nm)
    (goods goods-0) (price price) (b b) (c c) (m m))
  (precedes ((0 1) (2 3)) ((1 1) (0 0)) ((1 1) (2 1)) ((1 3) (0 2))
    ((2 0) (1 0)) ((2 4) (1 2)))
  (non-orig (privk b) (privk m) (privk c))
  (uniq-orig nm nb nc)
  (operation nonce-test (contracted (m-0 m)) nm (2 1)
    (enc nc nm m price (pubk c)))
  (traces
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" (cat b m nb nm)) (privk m))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))
      (send (enc (enc "hash" (cat b m nb nm)) (privk m))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum-0 price (pubk b)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))))
  (label 14)
  (parent 13)
  (unrealized (0 0) (1 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton epmo_acctnum
  (vars (nm nb nc acctnum price acctnum-0 goods text) (b m c name))
  (defstrand bank 3 (acctnum acctnum) (nc nc) (nm nm) (nb nb)
    (price price) (b b) (c c) (m m))
  (defstrand merchant 4 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b) (c c) (m m))
  (defstrand customer 5 (acctnum acctnum-0) (nb nb) (nc nc) (nm nm)
    (goods goods) (price price) (b b) (c c) (m m))
  (precedes ((0 1) (2 3)) ((1 1) (0 0)) ((1 1) (2 1)) ((1 3) (0 2))
    ((2 0) (1 0)) ((2 4) (1 2)))
  (non-orig (privk b) (privk m) (privk c))
  (uniq-orig nm nb nc)
  (operation nonce-test (contracted (goods-0 goods)) nc (1 0)
    (enc c nc goods (pubk m)))
  (traces
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" (cat b m nb nm)) (privk m))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))
      (send (enc (enc "hash" (cat b m nb nm)) (privk m))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum-0 price (pubk b)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))))
  (label 15)
  (parent 14)
  (unrealized (0 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo_acctnum
  (vars
    (nm nb nc acctnum price goods acctnum-0 goods-0 nm-0 price-0 text)
    (b m c name))
  (defstrand bank 3 (acctnum acctnum) (nc nc) (nm nm) (nb nb)
    (price price) (b b) (c c) (m m))
  (defstrand merchant 4 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b) (c c) (m m))
  (defstrand customer 5 (acctnum acctnum-0) (nb nb) (nc nc) (nm nm)
    (goods goods-0) (price price) (b b) (c c) (m m))
  (defstrand merchant 2 (nc nc) (nm nm-0) (goods goods-0)
    (price price-0) (c c) (m m))
  (precedes ((0 1) (2 3)) ((1 1) (0 0)) ((1 1) (2 1)) ((1 3) (0 2))
    ((2 0) (3 0)) ((2 4) (1 2)) ((3 1) (1 0)))
  (non-orig (privk b) (privk m) (privk c))
  (uniq-orig nm nb nc nm-0)
  (operation nonce-test (added-strand merchant 2) nc (1 0)
    (enc c nc goods-0 (pubk m)))
  (traces
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" (cat b m nb nm)) (privk m))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))
      (send (enc (enc "hash" (cat b m nb nm)) (privk m))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum-0 price (pubk b)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb)))
    ((recv (enc c nc goods-0 (pubk m)))
      (send (enc nc nm-0 m price-0 (pubk c)))))
  (label 16)
  (parent 14)
  (unrealized (0 0) (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo_acctnum
  (vars (nm nb nc acctnum price acctnum-0 goods text) (b m c name))
  (defstrand bank 3 (acctnum acctnum) (nc nc) (nm nm) (nb nb)
    (price price) (b b) (c c) (m m))
  (defstrand merchant 4 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b) (c c) (m m))
  (defstrand customer 5 (acctnum acctnum-0) (nb nb) (nc nc) (nm nm)
    (goods goods) (price price) (b b) (c c) (m m))
  (precedes ((0 1) (2 3)) ((1 1) (2 1)) ((1 3) (0 2)) ((2 0) (1 0))
    ((2 2) (0 0)) ((2 4) (1 2)))
  (non-orig (privk b) (privk m) (privk c))
  (uniq-orig nm nb nc)
  (operation nonce-test (displaced 3 2 customer 3) nm (0 0)
    (enc nc nm m price (pubk c)))
  (traces
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" (cat b m nb nm)) (privk m))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))
      (send (enc (enc "hash" (cat b m nb nm)) (privk m))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum-0 price (pubk b)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))))
  (label 17)
  (parent 15)
  (unrealized (0 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo_acctnum
  (vars (nm nb nc acctnum price acctnum-0 goods nm-0 price-0 text)
    (b m c name))
  (defstrand bank 3 (acctnum acctnum) (nc nc) (nm nm) (nb nb)
    (price price) (b b) (c c) (m m))
  (defstrand merchant 4 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b) (c c) (m m))
  (defstrand customer 5 (acctnum acctnum-0) (nb nb) (nc nc) (nm nm)
    (goods goods) (price price) (b b) (c c) (m m))
  (defstrand merchant 2 (nc nc) (nm nm-0) (goods goods) (price price-0)
    (c c) (m m))
  (precedes ((0 1) (2 3)) ((1 1) (0 0)) ((1 1) (2 1)) ((1 3) (0 2))
    ((2 0) (3 0)) ((2 4) (1 2)) ((3 1) (1 0)))
  (non-orig (privk b) (privk m) (privk c))
  (uniq-orig nm nb nc nm-0)
  (operation nonce-test (contracted (goods-0 goods)) nc (1 0)
    (enc nc nm-0 m price-0 (pubk c)) (enc c nc goods (pubk m)))
  (traces
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" (cat b m nb nm)) (privk m))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))
      (send (enc (enc "hash" (cat b m nb nm)) (privk m))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum-0 price (pubk b)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb)))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm-0 m price-0 (pubk c)))))
  (label 18)
  (parent 16)
  (unrealized (0 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo_acctnum
  (vars (nm nb nc price acctnum goods text) (b m c name))
  (defstrand bank 3 (acctnum acctnum) (nc nc) (nm nm) (nb nb)
    (price price) (b b) (c c) (m m))
  (defstrand merchant 4 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b) (c c) (m m))
  (defstrand customer 5 (acctnum acctnum) (nb nb) (nc nc) (nm nm)
    (goods goods) (price price) (b b) (c c) (m m))
  (precedes ((0 1) (2 3)) ((1 1) (2 1)) ((1 3) (0 2)) ((2 0) (1 0))
    ((2 2) (0 0)) ((2 4) (1 2)))
  (non-orig (privk b) (privk m) (privk c))
  (uniq-orig nm nb nc)
  (operation nonce-test (contracted (acctnum-0 acctnum)) nm (0 0)
    (enc nc nm m price (pubk c)) (enc c nc nm acctnum price (pubk b)))
  (traces
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" (cat b m nb nm)) (privk m))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))
      (send (enc (enc "hash" (cat b m nb nm)) (privk m))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum price (pubk b)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))))
  (label 19)
  (parent 17)
  (unrealized)
  (shape)
  (maps
    ((0)
      ((b b) (m m) (c c) (nm nm) (nb nb) (nc nc) (acctnum acctnum)
        (price price))))
  (origs (nc (2 0)) (nm (1 1)) (nb (0 1))))

(defskeleton epmo_acctnum
  (vars (nm nb nc acctnum price acctnum-0 goods nm-0 price-0 text)
    (b m c name))
  (defstrand bank 3 (acctnum acctnum) (nc nc) (nm nm) (nb nb)
    (price price) (b b) (c c) (m m))
  (defstrand merchant 4 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b) (c c) (m m))
  (defstrand customer 5 (acctnum acctnum-0) (nb nb) (nc nc) (nm nm)
    (goods goods) (price price) (b b) (c c) (m m))
  (defstrand merchant 2 (nc nc) (nm nm-0) (goods goods) (price price-0)
    (c c) (m m))
  (precedes ((0 1) (2 3)) ((1 1) (2 1)) ((1 3) (0 2)) ((2 0) (3 0))
    ((2 2) (0 0)) ((2 4) (1 2)) ((3 1) (1 0)))
  (non-orig (privk b) (privk m) (privk c))
  (uniq-orig nm nb nc nm-0)
  (operation nonce-test (displaced 4 2 customer 3) nm (0 0)
    (enc nc nm m price (pubk c)))
  (traces
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" (cat b m nb nm)) (privk m))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))
      (send (enc (enc "hash" (cat b m nb nm)) (privk m))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum-0 price (pubk b)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb)))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm-0 m price-0 (pubk c)))))
  (label 20)
  (parent 18)
  (unrealized (0 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo_acctnum
  (vars (nm nb nc price acctnum goods nm-0 price-0 text) (b m c name))
  (defstrand bank 3 (acctnum acctnum) (nc nc) (nm nm) (nb nb)
    (price price) (b b) (c c) (m m))
  (defstrand merchant 4 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b) (c c) (m m))
  (defstrand customer 5 (acctnum acctnum) (nb nb) (nc nc) (nm nm)
    (goods goods) (price price) (b b) (c c) (m m))
  (defstrand merchant 2 (nc nc) (nm nm-0) (goods goods) (price price-0)
    (c c) (m m))
  (precedes ((0 1) (2 3)) ((1 1) (2 1)) ((1 3) (0 2)) ((2 0) (3 0))
    ((2 2) (0 0)) ((2 4) (1 2)) ((3 1) (1 0)))
  (non-orig (privk b) (privk m) (privk c))
  (uniq-orig nm nb nc nm-0)
  (operation nonce-test (contracted (acctnum-0 acctnum)) nm (0 0)
    (enc nc nm m price (pubk c)) (enc c nc nm acctnum price (pubk b)))
  (traces
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" (cat b m nb nm)) (privk m))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))
      (send (enc (enc "hash" (cat b m nb nm)) (privk m))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum price (pubk b)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb)))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm-0 m price-0 (pubk c)))))
  (label 21)
  (parent 20)
  (seen 19)
  (unrealized)
  (comment "1 in cohort - 0 not yet seen"))

(comment "Nothing left to do")
