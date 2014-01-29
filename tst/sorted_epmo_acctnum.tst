(herald "Electronic Purchase with Money Order Protocol Variant"
  (bound 12)
  (comment "This version includes account numbers in exchanges"
    "This version uses sorts to avoid confusion"
    "between a nonce and other data"))

(comment "CPSA 2.3.1")
(comment "All input read from sorted_epmo_acctnum.scm")
(comment "Strand count bounded at 12")

(defprotocol sorted_epmo_acctnum basic
  (defrole bank
    (vars (b c m name) (acctnum price text) (hash name) (nc nm nb data))
    (trace (recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    (non-orig (privk hash))
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
    (vars (b c m hash name) (acctnum goods price text) (nc nm nb data))
    (trace (send (enc c nc goods (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum price (pubk b)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb)))
    (non-orig (privk b) (privk hash))
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
    (vars (b c m hash name) (goods price text) (nc nm nb data))
    (trace (recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    (non-orig (privk hash))
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

(defskeleton sorted_epmo_acctnum
  (vars (goods price text) (nm nc nb data) (b m c hash name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (non-orig (privk b) (privk m) (privk c) (privk hash))
  (uniq-orig nm nc nb)
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nm (pubk hash)) (privk m)))))
  (label 0)
  (unrealized (0 2))
  (origs (nm (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum text) (nm nc nb data) (b m c hash name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (hash hash))
  (precedes ((0 1) (1 0)) ((1 1) (0 2)))
  (non-orig (privk b) (privk m) (privk c) (privk hash))
  (uniq-orig nm nc nb)
  (operation encryption-test (added-strand bank 2)
    (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b)) (0 2))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))))
  (label 1)
  (parent 0)
  (unrealized (0 2) (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 text) (nm nc nb data)
    (b m c hash b-0 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 3 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nm) (b b-0) (c c) (m m))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (0 0)) ((2 2) (1 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0))
  (uniq-orig nm nc nb)
  (operation nonce-test (added-strand customer 3) nm (1 0)
    (enc nc nm m price (pubk c)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum-0 price (pubk b-0)))))
  (label 2)
  (parent 1)
  (unrealized (0 0) (0 2) (1 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum goods-0 text) (nm nc nb data)
    (m c hash b name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 3 (acctnum acctnum) (goods goods-0) (price price)
    (nc nc) (nm nm) (b b) (c c) (m m))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (0 0)) ((2 2) (1 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b))
  (uniq-orig nm nc nb)
  (operation nonce-test (contracted (b-0 b) (acctnum-0 acctnum)) nm
    (1 0) (enc nc nm m price (pubk c))
    (enc c nc nm acctnum price (pubk b)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum price (pubk b)))))
  (label 3)
  (parent 2)
  (unrealized (0 0) (0 2))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 text)
    (nm nc nb nb-0 data) (b m c hash b-0 hash-0 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 3 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nm) (b b-0) (c c) (m m))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nm)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (precedes ((0 1) (2 1)) ((0 1) (3 0)) ((1 1) (0 2)) ((2 0) (0 0))
    ((2 2) (1 0)) ((3 1) (1 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0)
    (privk hash-0))
  (uniq-orig nm nc nb)
  (operation nonce-test (added-strand bank 2) nm (1 0)
    (enc nc nm m price (pubk c))
    (enc c nc nm acctnum-0 price (pubk b-0)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum-0 price (pubk b-0))))
    ((recv (enc c nc nm acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nm price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))))
  (label 4)
  (parent 2)
  (unrealized (0 0) (0 2) (1 0) (3 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (price acctnum goods text) (nm nc nb data) (m c hash b name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 3 (acctnum acctnum) (goods goods) (price price)
    (nc nc) (nm nm) (b b) (c c) (m m))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (0 0)) ((2 2) (1 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b))
  (uniq-orig nm nc nb)
  (operation nonce-test (contracted (goods-0 goods)) nc (0 0)
    (enc c nc goods (pubk m)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum price (pubk b)))))
  (label 5)
  (parent 3)
  (unrealized (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum goods-0 price-0 text) (nm nc nb nm-0 data)
    (m c hash b name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 3 (acctnum acctnum) (goods goods-0) (price price)
    (nc nc) (nm nm) (b b) (c c) (m m))
  (defstrand merchant 2 (goods goods-0) (price price-0) (nc nc)
    (nm nm-0) (c c) (m m))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (3 0)) ((2 2) (1 0))
    ((3 1) (0 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b))
  (uniq-orig nm nc nb nm-0)
  (operation nonce-test (added-strand merchant 2) nc (0 0)
    (enc c nc goods-0 (pubk m)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum price (pubk b))))
    ((recv (enc c nc goods-0 (pubk m)))
      (send (enc nc nm-0 m price-0 (pubk c)))))
  (label 6)
  (parent 3)
  (unrealized (0 0) (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 text)
    (nm nc nb nb-0 data) (b m c hash b-0 hash-0 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 3 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nm) (b b-0) (c c) (m m))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nm)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (0 0)) ((2 2) (3 0))
    ((3 1) (1 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0)
    (privk hash-0))
  (uniq-orig nm nc nb)
  (operation nonce-test (displaced 4 2 customer 3) nm (3 0)
    (enc nc nm m price (pubk c)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum-0 price (pubk b-0))))
    ((recv (enc c nc nm acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nm price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))))
  (label 7)
  (parent 4)
  (unrealized (0 0) (0 2) (1 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (price acctnum goods text) (nm nc nb data) (c hash b m name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 5 (acctnum acctnum) (goods goods) (price price)
    (nc nc) (nm nm) (nb nb) (b b) (c c) (m m) (hash hash))
  (precedes ((0 1) (2 1)) ((1 1) (2 3)) ((2 0) (0 0)) ((2 2) (1 0))
    ((2 4) (0 2)))
  (non-orig (privk c) (privk hash) (privk b) (privk m))
  (uniq-orig nm nc nb)
  (operation nonce-test (displaced 2 3 customer 5) nb (0 2)
    (enc "hash" c nc nb nm price (pubk hash)) (enc nc nb (pubk c)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum price (pubk b)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))))
  (label 8)
  (parent 5)
  (unrealized)
  (shape)
  (maps
    ((0)
      ((b b) (m m) (c c) (nm nm) (nc nc) (nb nb) (hash hash)
        (goods goods) (price price))))
  (origs (nc (2 0)) (nm (0 1)) (nb (1 1))))

(defskeleton sorted_epmo_acctnum
  (vars (price acctnum goods price-0 text) (nm nc nb nm-0 data)
    (m c hash b name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 3 (acctnum acctnum) (goods goods) (price price)
    (nc nc) (nm nm) (b b) (c c) (m m))
  (defstrand merchant 2 (goods goods) (price price-0) (nc nc) (nm nm-0)
    (c c) (m m))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (3 0)) ((2 2) (1 0))
    ((3 1) (0 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b))
  (uniq-orig nm nc nb nm-0)
  (operation nonce-test (contracted (goods-0 goods)) nc (0 0)
    (enc nc nm-0 m price-0 (pubk c)) (enc c nc goods (pubk m)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum price (pubk b))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm-0 m price-0 (pubk c)))))
  (label 9)
  (parent 6)
  (unrealized (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum goods-0 text) (nm nc nb nb-0 data)
    (m c hash b hash-0 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 3 (acctnum acctnum) (goods goods-0) (price price)
    (nc nc) (nm nm) (b b) (c c) (m m))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (0 0)) ((2 2) (3 0))
    ((3 1) (1 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0))
  (uniq-orig nm nc nb)
  (operation nonce-test (contracted (b-0 b) (acctnum-0 acctnum)) nm
    (1 0) (enc "hash" c nc nb-0 nm price (pubk hash-0))
    (enc nc nm m price (pubk c)) (enc c nc nm acctnum price (pubk b)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum price (pubk b))))
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nm price (pubk hash-0)) (privk b))
          (enc nc nb-0 (pubk c))))))
  (label 10)
  (parent 7)
  (unrealized (0 0) (0 2))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 text) (nc nb nb-0 data)
    (b m c hash b-0 hash-0 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 3 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nb-0) (b b-0) (c c) (m m))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (0 0)) ((2 2) (3 0))
    ((3 1) (1 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0)
    (privk hash-0))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (displaced 4 3 bank 2) nm (1 0)
    (enc "hash" c nc nb-0 nm price (pubk hash-0))
    (enc nc nm m price (pubk c))
    (enc c nc nm acctnum-0 price (pubk b-0)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b-0))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))))
  (label 11)
  (parent 7)
  (unrealized (0 0) (0 2) (1 0))
  (comment "3 in cohort - 3 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (price price-0 acctnum goods text) (nm nc nb nm-0 data)
    (c hash b m name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand merchant 2 (goods goods) (price price-0) (nc nc) (nm nm-0)
    (c c) (m m))
  (defstrand customer 5 (acctnum acctnum) (goods goods) (price price)
    (nc nc) (nm nm) (nb nb) (b b) (c c) (m m) (hash hash))
  (precedes ((0 1) (3 1)) ((1 1) (3 3)) ((2 1) (0 0)) ((3 0) (2 0))
    ((3 2) (1 0)) ((3 4) (0 2)))
  (non-orig (privk c) (privk hash) (privk b) (privk m))
  (uniq-orig nm nc nb nm-0)
  (operation nonce-test (displaced 2 4 customer 5) nb (0 2)
    (enc "hash" c nc nb nm price (pubk hash)) (enc nc nb (pubk c)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm-0 m price-0 (pubk c))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum price (pubk b)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))))
  (label 12)
  (parent 9)
  (seen 8)
  (unrealized)
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (price acctnum goods text) (nm nc nb nb-0 data)
    (m c hash b hash-0 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 3 (acctnum acctnum) (goods goods) (price price)
    (nc nc) (nm nm) (b b) (c c) (m m))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (0 0)) ((2 2) (3 0))
    ((3 1) (1 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0))
  (uniq-orig nm nc nb)
  (operation nonce-test (contracted (goods-0 goods)) nc (0 0)
    (enc c nc goods (pubk m)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum price (pubk b))))
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nm price (pubk hash-0)) (privk b))
          (enc nc nb-0 (pubk c))))))
  (label 13)
  (parent 10)
  (unrealized (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum goods-0 price-0 text)
    (nm nc nb nb-0 nm-0 data) (m c hash b hash-0 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 3 (acctnum acctnum) (goods goods-0) (price price)
    (nc nc) (nm nm) (b b) (c c) (m m))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand merchant 2 (goods goods-0) (price price-0) (nc nc)
    (nm nm-0) (c c) (m m))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (4 0)) ((2 2) (3 0))
    ((3 1) (1 0)) ((4 1) (0 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0))
  (uniq-orig nm nc nb nm-0)
  (operation nonce-test (added-strand merchant 2) nc (0 0)
    (enc c nc goods-0 (pubk m)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum price (pubk b))))
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nm price (pubk hash-0)) (privk b))
          (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc goods-0 (pubk m)))
      (send (enc nc nm-0 m price-0 (pubk c)))))
  (label 14)
  (parent 10)
  (unrealized (0 0) (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum goods-0 text) (nc nb nb-0 data)
    (m c hash b hash-0 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 3 (acctnum acctnum) (goods goods-0) (price price)
    (nc nc) (nm nb-0) (b b) (c c) (m m))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (0 0)) ((2 2) (3 0))
    ((3 1) (1 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (contracted (b-0 b) (acctnum-0 acctnum)) nb-0
    (1 0) (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
    (enc nc nb-0 (pubk c)) (enc nc nb-0 m price (pubk c))
    (enc c nc nb-0 acctnum price (pubk b)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))))
  (label 15)
  (parent 11)
  (unrealized (0 0) (0 2))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 text)
    (nc nb nb-0 nb-1 data) (b m c hash b-0 hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 3 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nb-0) (b b-0) (c c) (m m))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b-0) (c c) (hash hash-1))
  (precedes ((0 1) (2 1)) ((0 1) (4 0)) ((1 1) (0 2)) ((2 0) (0 0))
    ((2 2) (3 0)) ((3 1) (1 0)) ((4 1) (1 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0)
    (privk hash-0) (privk hash-1))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (added-strand bank 2) nb-0 (1 0)
    (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
    (enc nc nb-0 (pubk c)) (enc nc nb-0 m price (pubk c))
    (enc c nc nb-0 acctnum-0 price (pubk b-0)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b-0))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b-0)) (enc nc nb-1 (pubk c))))))
  (label 16)
  (parent 11)
  (unrealized (0 0) (0 2) (1 0) (4 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 text) (nc nb nb-0 data)
    (b m c hash b-0 hash-0 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nb-0) (nb nb-0) (b b-0) (c c) (m m)
    (hash hash-0))
  (precedes ((0 1) (3 1)) ((1 1) (0 2)) ((2 1) (1 0)) ((3 0) (0 0))
    ((3 2) (2 0)) ((3 4) (1 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0)
    (privk hash-0))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (displaced 2 4 customer 5) nb-0 (1 0)
    (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
    (enc nc nb-0 (pubk c)) (enc nc nb-0 m price (pubk c))
    (enc c nc nb-0 acctnum-0 price (pubk b-0)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) nb-0))))
  (label 17)
  (parent 11)
  (unrealized (0 0) (0 2) (1 0) (3 3))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (price acctnum goods text) (nm nc nb nb-0 data)
    (c hash hash-0 b m name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand customer 5 (acctnum acctnum) (goods goods) (price price)
    (nc nc) (nm nm) (nb nb) (b b) (c c) (m m) (hash hash))
  (precedes ((0 1) (3 1)) ((1 1) (3 3)) ((2 1) (1 0)) ((3 0) (0 0))
    ((3 2) (2 0)) ((3 4) (0 2)))
  (non-orig (privk c) (privk hash) (privk hash-0) (privk b) (privk m))
  (uniq-orig nm nc nb)
  (operation nonce-test (displaced 2 4 customer 5) nb (0 2)
    (enc "hash" c nc nb nm price (pubk hash)) (enc nc nb (pubk c)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nm price (pubk hash-0)) (privk b))
          (enc nc nb-0 (pubk c)))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum price (pubk b)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))))
  (label 18)
  (parent 13)
  (seen 8)
  (unrealized)
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (price acctnum goods price-0 text) (nm nc nb nb-0 nm-0 data)
    (m c hash b hash-0 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 3 (acctnum acctnum) (goods goods) (price price)
    (nc nc) (nm nm) (b b) (c c) (m m))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand merchant 2 (goods goods) (price price-0) (nc nc) (nm nm-0)
    (c c) (m m))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (4 0)) ((2 2) (3 0))
    ((3 1) (1 0)) ((4 1) (0 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0))
  (uniq-orig nm nc nb nm-0)
  (operation nonce-test (contracted (goods-0 goods)) nc (0 0)
    (enc nc nm-0 m price-0 (pubk c)) (enc c nc goods (pubk m)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum price (pubk b))))
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nm price (pubk hash-0)) (privk b))
          (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm-0 m price-0 (pubk c)))))
  (label 19)
  (parent 14)
  (unrealized (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (price acctnum goods text) (nc nb nb-0 data)
    (m c hash b hash-0 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 3 (acctnum acctnum) (goods goods) (price price)
    (nc nc) (nm nb-0) (b b) (c c) (m m))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (0 0)) ((2 2) (3 0))
    ((3 1) (1 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (contracted (goods-0 goods)) nc (0 0)
    (enc c nc goods (pubk m)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))))
  (label 20)
  (parent 15)
  (unrealized (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum goods-0 price-0 text) (nc nb nb-0 nm data)
    (m c hash b hash-0 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 3 (acctnum acctnum) (goods goods-0) (price price)
    (nc nc) (nm nb-0) (b b) (c c) (m m))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand merchant 2 (goods goods-0) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (4 0)) ((2 2) (3 0))
    ((3 1) (1 0)) ((4 1) (0 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0))
  (uniq-orig nc nb nb-0 nm)
  (operation nonce-test (added-strand merchant 2) nc (0 0)
    (enc c nc goods-0 (pubk m)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc goods-0 (pubk m)))
      (send (enc nc nm m price-0 (pubk c)))))
  (label 21)
  (parent 15)
  (unrealized (0 0) (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 text)
    (nc nb nb-0 nb-1 data) (b m c hash b-0 hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 3 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nb-0) (b b-0) (c c) (m m))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b-0) (c c) (hash hash-1))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (0 0)) ((2 2) (3 0))
    ((2 2) (4 0)) ((3 1) (1 0)) ((4 1) (1 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0)
    (privk hash-0) (privk hash-1))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (displaced 5 2 customer 3) nb-0 (4 0)
    (enc nc nb-0 m price (pubk c)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b-0))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b-0)) (enc nc nb-1 (pubk c))))))
  (label 22)
  (parent 16)
  (unrealized (0 0) (0 2) (1 0))
  (comment "3 in cohort - 3 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 text) (nc nb nb-0 data)
    (b m c hash b-0 hash-0 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nb-0) (nb nb-0) (b b-0) (c c) (m m)
    (hash hash-0))
  (precedes ((0 1) (3 1)) ((1 1) (0 2)) ((2 1) (3 3)) ((3 0) (0 0))
    ((3 2) (2 0)) ((3 4) (1 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0)
    (privk hash-0))
  (uniq-orig nc nb nb-0)
  (operation encryption-test (displaced 4 2 bank 2)
    (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0)) (privk b-0))
    (3 3))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) nb-0))))
  (label 23)
  (parent 17)
  (unrealized (0 0) (0 2) (1 0))
  (comment "3 in cohort - 3 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 acctnum-1 text)
    (nc nb nb-0 data) (b m c hash b-0 hash-0 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nb-0) (nb nb-0) (b b-0) (c c) (m m)
    (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-1) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (precedes ((0 1) (3 1)) ((0 1) (4 0)) ((1 1) (0 2)) ((2 1) (1 0))
    ((3 0) (0 0)) ((3 2) (2 0)) ((3 4) (1 0)) ((4 1) (3 3)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0)
    (privk hash-0))
  (uniq-orig nc nb nb-0)
  (operation encryption-test (added-strand bank 2)
    (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0)) (privk b-0))
    (3 3))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) nb-0)))
    ((recv (enc c nc nb-0 acctnum-1 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))))
  (label 24)
  (parent 17)
  (unrealized (0 0) (0 2) (1 0) (4 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (price price-0 acctnum goods text) (nm nc nb nb-0 nm-0 data)
    (c hash hash-0 b m name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand merchant 2 (goods goods) (price price-0) (nc nc) (nm nm-0)
    (c c) (m m))
  (defstrand customer 5 (acctnum acctnum) (goods goods) (price price)
    (nc nc) (nm nm) (nb nb) (b b) (c c) (m m) (hash hash))
  (precedes ((0 1) (4 1)) ((1 1) (4 3)) ((2 1) (1 0)) ((3 1) (0 0))
    ((4 0) (3 0)) ((4 2) (2 0)) ((4 4) (0 2)))
  (non-orig (privk c) (privk hash) (privk hash-0) (privk b) (privk m))
  (uniq-orig nm nc nb nm-0)
  (operation nonce-test (displaced 2 5 customer 5) nb (0 2)
    (enc "hash" c nc nb nm price (pubk hash)) (enc nc nb (pubk c)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nm price (pubk hash-0)) (privk b))
          (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm-0 m price-0 (pubk c))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum price (pubk b)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))))
  (label 25)
  (parent 19)
  (seen 12)
  (unrealized)
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (price acctnum goods text) (nc nb nb-0 data)
    (c hash hash-0 b m name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand customer 5 (acctnum acctnum) (goods goods) (price price)
    (nc nc) (nm nb-0) (nb nb) (b b) (c c) (m m) (hash hash))
  (precedes ((0 1) (3 1)) ((1 1) (3 3)) ((2 1) (1 0)) ((3 0) (0 0))
    ((3 2) (2 0)) ((3 4) (0 2)))
  (non-orig (privk c) (privk hash) (privk hash-0) (privk b) (privk m))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (displaced 2 4 customer 5) nb (0 2)
    (enc "hash" c nc nb nb-0 price (pubk hash)) (enc nc nb (pubk c)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))))
  (label 26)
  (parent 20)
  (seen 8)
  (unrealized)
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (price acctnum goods price-0 text) (nc nb nb-0 nm data)
    (m c hash b hash-0 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 3 (acctnum acctnum) (goods goods) (price price)
    (nc nc) (nm nb-0) (b b) (c c) (m m))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand merchant 2 (goods goods) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (4 0)) ((2 2) (3 0))
    ((3 1) (1 0)) ((4 1) (0 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0))
  (uniq-orig nc nb nb-0 nm)
  (operation nonce-test (contracted (goods-0 goods)) nc (0 0)
    (enc nc nm m price-0 (pubk c)) (enc c nc goods (pubk m)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price-0 (pubk c)))))
  (label 27)
  (parent 21)
  (unrealized (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum goods-0 text) (nc nb nb-0 nb-1 data)
    (m c hash b hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 3 (acctnum acctnum) (goods goods-0) (price price)
    (nc nc) (nm nb-0) (b b) (c c) (m m))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b) (c c) (hash hash-1))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (0 0)) ((2 2) (3 0))
    ((2 2) (4 0)) ((3 1) (1 0)) ((4 1) (1 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0)
    (privk hash-1))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (contracted (b-0 b) (acctnum-0 acctnum)) nb-0
    (1 0) (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
    (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
    (enc nc nb-0 (pubk c)) (enc nc nb-0 m price (pubk c))
    (enc c nc nb-0 acctnum price (pubk b)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-1 (pubk c))))))
  (label 28)
  (parent 22)
  (unrealized (0 0) (0 2))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 text) (nc nb nb-0 data)
    (b m c hash b-0 hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-1))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nb-0) (nb nb-0) (b b-0) (c c) (m m)
    (hash hash-1))
  (precedes ((0 1) (4 1)) ((1 1) (0 2)) ((2 1) (1 0)) ((3 1) (1 0))
    ((4 0) (0 0)) ((4 2) (2 0)) ((4 2) (3 0)) ((4 4) (1 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0)
    (privk hash-0) (privk hash-1))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (displaced 2 5 customer 5) nb-0 (1 0)
    (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
    (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
    (enc nc nb-0 (pubk c)) (enc nc nb-0 m price (pubk c))
    (enc c nc nb-0 acctnum-0 price (pubk b-0)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
            (privk b-0)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
            (privk b-0)) nb-0))))
  (label 29)
  (parent 22)
  (seen 23 24)
  (unrealized (0 0) (0 2) (1 0) (4 3))
  (comment "2 in cohort - 0 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 text)
    (nc nb nb-0 nb-1 data) (b m c hash b-0 hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b-0) (c c) (hash hash-1))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nb-0) (nb nb-0) (b b-0) (c c) (m m)
    (hash hash-0))
  (precedes ((0 1) (4 1)) ((1 1) (0 2)) ((2 1) (1 0)) ((3 1) (1 0))
    ((4 0) (0 0)) ((4 2) (2 0)) ((4 2) (3 0)) ((4 4) (1 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0)
    (privk hash-0) (privk hash-1))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (displaced 2 5 customer 5) nb-0 (1 0)
    (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
    (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
    (enc nc nb-0 (pubk c)) (enc nc nb-0 m price (pubk c))
    (enc c nc nb-0 acctnum-0 price (pubk b-0)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b-0)) (enc nc nb-1 (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) nb-0))))
  (label 30)
  (parent 22)
  (unrealized (0 0) (0 2) (1 0) (4 3))
  (comment "3 in cohort - 3 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum goods-0 text) (nc nb nb-0 data)
    (m c hash b hash-0 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand customer 5 (acctnum acctnum) (goods goods-0) (price price)
    (nc nc) (nm nb-0) (nb nb-0) (b b) (c c) (m m) (hash hash-0))
  (precedes ((0 1) (3 1)) ((1 1) (0 2)) ((2 1) (3 3)) ((3 0) (0 0))
    ((3 2) (2 0)) ((3 4) (1 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (contracted (b-0 b) (acctnum-0 acctnum)) nc
    (1 0) (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
    (enc nc nb-0 (pubk c)) (enc nc nb-0 m price (pubk c))
    (enc c nc goods-0 (pubk m)) (enc c nc nb-0 acctnum price (pubk b)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) nb-0))))
  (label 31)
  (parent 23)
  (unrealized (0 0) (0 2))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 text)
    (nc nb nb-0 nb-1 data) (b m c hash b-0 hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nb-0) (nb nb-0) (b b-0) (c c) (m m)
    (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b-0) (c c) (hash hash-1))
  (precedes ((0 1) (3 1)) ((0 1) (4 0)) ((1 1) (0 2)) ((2 1) (3 3))
    ((3 0) (0 0)) ((3 2) (2 0)) ((3 4) (1 0)) ((4 1) (1 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0)
    (privk hash-0) (privk hash-1))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (added-strand bank 2) nc (1 0)
    (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
    (enc nc nb-0 (pubk c)) (enc nc nb-0 m price (pubk c))
    (enc c nc goods-0 (pubk m))
    (enc c nc nb-0 acctnum-0 price (pubk b-0)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) nb-0)))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b-0)) (enc nc nb-1 (pubk c))))))
  (label 32)
  (parent 23)
  (seen 38)
  (unrealized (0 0) (0 2) (1 0) (4 0))
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 price-0 text)
    (nc nb nb-0 nm data) (b m c hash b-0 hash-0 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nb-0) (nb nb-0) (b b-0) (c c) (m m)
    (hash hash-0))
  (defstrand merchant 2 (goods goods-0) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (precedes ((0 1) (3 1)) ((1 1) (0 2)) ((2 1) (3 3)) ((3 0) (0 0))
    ((3 0) (4 0)) ((3 2) (2 0)) ((3 4) (1 0)) ((4 1) (1 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0)
    (privk hash-0))
  (uniq-orig nc nb nb-0 nm)
  (operation nonce-test (added-strand merchant 2) nc (1 0)
    (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
    (enc nc nb-0 (pubk c)) (enc nc nb-0 m price (pubk c))
    (enc c nc goods-0 (pubk m))
    (enc c nc nb-0 acctnum-0 price (pubk b-0)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) nb-0)))
    ((recv (enc c nc goods-0 (pubk m)))
      (send (enc nc nm m price-0 (pubk c)))))
  (label 33)
  (parent 23)
  (unrealized (0 0) (0 2) (1 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 acctnum-1 text)
    (nc nb nb-0 data) (b m c hash b-0 hash-0 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nb-0) (nb nb-0) (b b-0) (c c) (m m)
    (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-1) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (precedes ((0 1) (3 1)) ((1 1) (0 2)) ((2 1) (1 0)) ((3 0) (0 0))
    ((3 2) (2 0)) ((3 2) (4 0)) ((3 4) (1 0)) ((4 1) (3 3)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0)
    (privk hash-0))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (displaced 5 3 customer 3) nb-0 (4 0)
    (enc nc nb-0 m price (pubk c)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) nb-0)))
    ((recv (enc c nc nb-0 acctnum-1 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))))
  (label 34)
  (parent 24)
  (seen 23)
  (unrealized (0 0) (0 2) (1 0) (4 0))
  (comment "2 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (price price-0 acctnum goods text) (nc nb nb-0 nm data)
    (c hash hash-0 b m name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand merchant 2 (goods goods) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (defstrand customer 5 (acctnum acctnum) (goods goods) (price price)
    (nc nc) (nm nb-0) (nb nb) (b b) (c c) (m m) (hash hash))
  (precedes ((0 1) (4 1)) ((1 1) (4 3)) ((2 1) (1 0)) ((3 1) (0 0))
    ((4 0) (3 0)) ((4 2) (2 0)) ((4 4) (0 2)))
  (non-orig (privk c) (privk hash) (privk hash-0) (privk b) (privk m))
  (uniq-orig nc nb nb-0 nm)
  (operation nonce-test (displaced 2 5 customer 5) nb (0 2)
    (enc "hash" c nc nb nb-0 price (pubk hash)) (enc nc nb (pubk c)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price-0 (pubk c))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))))
  (label 35)
  (parent 27)
  (seen 12)
  (unrealized)
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (price acctnum goods text) (nc nb nb-0 nb-1 data)
    (m c hash b hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 3 (acctnum acctnum) (goods goods) (price price)
    (nc nc) (nm nb-0) (b b) (c c) (m m))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b) (c c) (hash hash-1))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (0 0)) ((2 2) (3 0))
    ((2 2) (4 0)) ((3 1) (1 0)) ((4 1) (1 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0)
    (privk hash-1))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (contracted (goods-0 goods)) nc (0 0)
    (enc c nc goods (pubk m)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-1 (pubk c))))))
  (label 36)
  (parent 28)
  (unrealized (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum goods-0 price-0 text)
    (nc nb nb-0 nb-1 nm data) (m c hash b hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 3 (acctnum acctnum) (goods goods-0) (price price)
    (nc nc) (nm nb-0) (b b) (c c) (m m))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b) (c c) (hash hash-1))
  (defstrand merchant 2 (goods goods-0) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (5 0)) ((2 2) (3 0))
    ((2 2) (4 0)) ((3 1) (1 0)) ((4 1) (1 0)) ((5 1) (0 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0)
    (privk hash-1))
  (uniq-orig nc nb nb-0 nm)
  (operation nonce-test (added-strand merchant 2) nc (0 0)
    (enc c nc goods-0 (pubk m)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-1 (pubk c)))))
    ((recv (enc c nc goods-0 (pubk m)))
      (send (enc nc nm m price-0 (pubk c)))))
  (label 37)
  (parent 28)
  (unrealized (0 0) (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 text)
    (nc nb nb-0 nb-1 data) (b m c hash b-0 hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b-0) (c c) (hash hash-1))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nb-0) (nb nb-0) (b b-0) (c c) (m m)
    (hash hash-0))
  (precedes ((0 1) (4 1)) ((1 1) (0 2)) ((2 1) (4 3)) ((3 1) (1 0))
    ((4 0) (0 0)) ((4 2) (2 0)) ((4 2) (3 0)) ((4 4) (1 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0)
    (privk hash-0) (privk hash-1))
  (uniq-orig nc nb nb-0)
  (operation encryption-test (displaced 5 2 bank 2)
    (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0)) (privk b-0))
    (4 3))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b-0)) (enc nc nb-1 (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) nb-0))))
  (label 38)
  (parent 30)
  (unrealized (0 0) (0 2) (1 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 text) (nc nb nb-0 data)
    (b m c hash b-0 hash-0 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nb-0) (nb nb-0) (b b-0) (c c) (m m)
    (hash hash-0))
  (precedes ((0 1) (4 1)) ((1 1) (0 2)) ((2 1) (1 0)) ((3 1) (4 3))
    ((4 0) (0 0)) ((4 2) (2 0)) ((4 2) (3 0)) ((4 4) (1 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0)
    (privk hash-0))
  (uniq-orig nc nb nb-0)
  (operation encryption-test (displaced 5 3 bank 2)
    (enc (enc "hash" c nc nb-1 nb-1 price (pubk hash-1)) (privk b-0))
    (4 3))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) nb-0))))
  (label 39)
  (parent 30)
  (seen 31 32 33)
  (unrealized (0 0) (0 2) (1 0))
  (comment "3 in cohort - 0 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 acctnum-1 text)
    (nc nb nb-0 nb-1 data) (b m c hash b-0 hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b-0) (c c) (hash hash-1))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nb-0) (nb nb-0) (b b-0) (c c) (m m)
    (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-1) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (precedes ((0 1) (4 1)) ((0 1) (5 0)) ((1 1) (0 2)) ((2 1) (1 0))
    ((3 1) (1 0)) ((4 0) (0 0)) ((4 2) (2 0)) ((4 2) (3 0))
    ((4 4) (1 0)) ((5 1) (4 3)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0)
    (privk hash-0) (privk hash-1))
  (uniq-orig nc nb nb-0)
  (operation encryption-test (added-strand bank 2)
    (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0)) (privk b-0))
    (4 3))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b-0)) (enc nc nb-1 (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) nb-0)))
    ((recv (enc c nc nb-0 acctnum-1 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))))
  (label 40)
  (parent 30)
  (unrealized (0 0) (0 2) (1 0) (5 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (price acctnum goods text) (nc nb nb-0 data)
    (m c hash b hash-0 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand customer 5 (acctnum acctnum) (goods goods) (price price)
    (nc nc) (nm nb-0) (nb nb-0) (b b) (c c) (m m) (hash hash-0))
  (precedes ((0 1) (3 1)) ((1 1) (0 2)) ((2 1) (3 3)) ((3 0) (0 0))
    ((3 2) (2 0)) ((3 4) (1 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (contracted (goods-0 goods)) nc (0 0)
    (enc c nc goods (pubk m)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) nb-0))))
  (label 41)
  (parent 31)
  (unrealized (0 2))
  (comment "empty cohort"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum goods-0 price-0 text) (nc nb nb-0 nm data)
    (m c hash b hash-0 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand customer 5 (acctnum acctnum) (goods goods-0) (price price)
    (nc nc) (nm nb-0) (nb nb-0) (b b) (c c) (m m) (hash hash-0))
  (defstrand merchant 2 (goods goods-0) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (precedes ((0 1) (3 1)) ((1 1) (0 2)) ((2 1) (3 3)) ((3 0) (4 0))
    ((3 2) (2 0)) ((3 4) (1 0)) ((4 1) (0 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0))
  (uniq-orig nc nb nb-0 nm)
  (operation nonce-test (added-strand merchant 2) nc (0 0)
    (enc c nc goods-0 (pubk m)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) nb-0)))
    ((recv (enc c nc goods-0 (pubk m)))
      (send (enc nc nm m price-0 (pubk c)))))
  (label 42)
  (parent 31)
  (unrealized (0 0) (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum goods-0 price-0 text) (nc nb nb-0 nm data)
    (m c hash b hash-0 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand customer 5 (acctnum acctnum) (goods goods-0) (price price)
    (nc nc) (nm nb-0) (nb nb-0) (b b) (c c) (m m) (hash hash-0))
  (defstrand merchant 2 (goods goods-0) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (precedes ((0 1) (3 1)) ((1 1) (0 2)) ((2 1) (3 3)) ((3 0) (0 0))
    ((3 0) (4 0)) ((3 2) (2 0)) ((3 4) (1 0)) ((4 1) (1 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0))
  (uniq-orig nc nb nb-0 nm)
  (operation nonce-test (contracted (b-0 b) (acctnum-0 acctnum)) nc
    (1 0) (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
    (enc nc nb-0 (pubk c)) (enc nc nb-0 m price (pubk c))
    (enc nc nm m price-0 (pubk c)) (enc c nc goods-0 (pubk m))
    (enc c nc nb-0 acctnum price (pubk b)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) nb-0)))
    ((recv (enc c nc goods-0 (pubk m)))
      (send (enc nc nm m price-0 (pubk c)))))
  (label 43)
  (parent 33)
  (seen 41 42)
  (unrealized (0 0) (0 2))
  (comment "2 in cohort - 0 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 price-0 text)
    (nc nb nb-0 nm nb-1 data) (b m c hash b-0 hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nb-0) (nb nb-0) (b b-0) (c c) (m m)
    (hash hash-0))
  (defstrand merchant 2 (goods goods-0) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b-0) (c c) (hash hash-1))
  (precedes ((0 1) (3 1)) ((0 1) (5 0)) ((1 1) (0 2)) ((2 1) (3 3))
    ((3 0) (0 0)) ((3 0) (4 0)) ((3 2) (2 0)) ((3 4) (1 0))
    ((4 1) (1 0)) ((5 1) (1 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0)
    (privk hash-0) (privk hash-1))
  (uniq-orig nc nb nb-0 nm)
  (operation nonce-test (added-strand bank 2) nc (1 0)
    (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
    (enc nc nb-0 (pubk c)) (enc nc nb-0 m price (pubk c))
    (enc nc nm m price-0 (pubk c)) (enc c nc goods-0 (pubk m))
    (enc c nc nb-0 acctnum-0 price (pubk b-0)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) nb-0)))
    ((recv (enc c nc goods-0 (pubk m)))
      (send (enc nc nm m price-0 (pubk c))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b-0)) (enc nc nb-1 (pubk c))))))
  (label 44)
  (parent 33)
  (seen 49)
  (unrealized (0 0) (0 2) (1 0) (5 0))
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 acctnum-1 text)
    (nc nb nb-0 nb-1 data) (b m c hash b-0 hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nb-0) (nb nb-0) (b b-0) (c c) (m m)
    (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-1) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b-0) (c c) (hash hash-1))
  (precedes ((0 1) (3 1)) ((0 1) (5 0)) ((1 1) (0 2)) ((2 1) (1 0))
    ((3 0) (0 0)) ((3 2) (2 0)) ((3 2) (4 0)) ((3 4) (1 0))
    ((4 1) (3 3)) ((5 1) (4 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0)
    (privk hash-0) (privk hash-1))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (added-strand bank 2) nb-0 (4 0)
    (enc nc nb-0 m price (pubk c))
    (enc c nc nb-0 acctnum-0 price (pubk b-0)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) nb-0)))
    ((recv (enc c nc nb-0 acctnum-1 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b-0)) (enc nc nb-1 (pubk c))))))
  (label 45)
  (parent 34)
  (unrealized (0 0) (0 2) (1 0) (4 0) (5 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (price acctnum goods text) (nc nb nb-0 nb-1 data)
    (c hash hash-0 hash-1 b m name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b) (c c) (hash hash-1))
  (defstrand customer 5 (acctnum acctnum) (goods goods) (price price)
    (nc nc) (nm nb-0) (nb nb) (b b) (c c) (m m) (hash hash))
  (precedes ((0 1) (4 1)) ((1 1) (4 3)) ((2 1) (1 0)) ((3 1) (1 0))
    ((4 0) (0 0)) ((4 2) (2 0)) ((4 2) (3 0)) ((4 4) (0 2)))
  (non-orig (privk c) (privk hash) (privk hash-0) (privk hash-1)
    (privk b) (privk m))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (displaced 2 5 customer 5) nb (0 2)
    (enc "hash" c nc nb nb-0 price (pubk hash)) (enc nc nb (pubk c)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-1 (pubk c)))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))))
  (label 46)
  (parent 36)
  (seen 18)
  (unrealized)
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (price acctnum goods price-0 text) (nc nb nb-0 nb-1 nm data)
    (m c hash b hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 3 (acctnum acctnum) (goods goods) (price price)
    (nc nc) (nm nb-0) (b b) (c c) (m m))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b) (c c) (hash hash-1))
  (defstrand merchant 2 (goods goods) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (5 0)) ((2 2) (3 0))
    ((2 2) (4 0)) ((3 1) (1 0)) ((4 1) (1 0)) ((5 1) (0 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0)
    (privk hash-1))
  (uniq-orig nc nb nb-0 nm)
  (operation nonce-test (contracted (goods-0 goods)) nc (0 0)
    (enc nc nm m price-0 (pubk c)) (enc c nc goods (pubk m)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-1 (pubk c)))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price-0 (pubk c)))))
  (label 47)
  (parent 37)
  (unrealized (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum goods-0 text) (nc nb nb-0 nb-1 data)
    (m c hash b hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b) (c c) (hash hash-1))
  (defstrand customer 5 (acctnum acctnum) (goods goods-0) (price price)
    (nc nc) (nm nb-0) (nb nb-0) (b b) (c c) (m m) (hash hash-0))
  (precedes ((0 1) (4 1)) ((1 1) (0 2)) ((2 1) (4 3)) ((3 1) (1 0))
    ((4 0) (0 0)) ((4 2) (2 0)) ((4 2) (3 0)) ((4 4) (1 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0)
    (privk hash-1))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (contracted (b-0 b) (acctnum-0 acctnum)) nc
    (1 0) (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
    (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
    (enc nc nb-0 (pubk c)) (enc nc nb-1 (pubk c))
    (enc nc nb-0 m price (pubk c)) (enc c nc goods-0 (pubk m))
    (enc c nc nb-0 acctnum price (pubk b)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-1 (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) nb-0))))
  (label 48)
  (parent 38)
  (unrealized (0 0) (0 2))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 price-0 text)
    (nc nb nb-0 nb-1 nm data) (b m c hash b-0 hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b-0) (c c) (hash hash-1))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nb-0) (nb nb-0) (b b-0) (c c) (m m)
    (hash hash-0))
  (defstrand merchant 2 (goods goods-0) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (precedes ((0 1) (4 1)) ((1 1) (0 2)) ((2 1) (4 3)) ((3 1) (1 0))
    ((4 0) (0 0)) ((4 0) (5 0)) ((4 2) (2 0)) ((4 2) (3 0))
    ((4 4) (1 0)) ((5 1) (1 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0)
    (privk hash-0) (privk hash-1))
  (uniq-orig nc nb nb-0 nm)
  (operation nonce-test (added-strand merchant 2) nc (1 0)
    (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
    (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
    (enc nc nb-0 (pubk c)) (enc nc nb-1 (pubk c))
    (enc nc nb-0 m price (pubk c)) (enc c nc goods-0 (pubk m))
    (enc c nc nb-0 acctnum-0 price (pubk b-0)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b-0)) (enc nc nb-1 (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) nb-0)))
    ((recv (enc c nc goods-0 (pubk m)))
      (send (enc nc nm m price-0 (pubk c)))))
  (label 49)
  (parent 38)
  (unrealized (0 0) (0 2) (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 acctnum-1 text)
    (nc nb nb-0 nb-1 data) (b m c hash b-0 hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b-0) (c c) (hash hash-1))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nb-0) (nb nb-0) (b b-0) (c c) (m m)
    (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-1) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (precedes ((0 1) (4 1)) ((1 1) (0 2)) ((2 1) (1 0)) ((3 1) (1 0))
    ((4 0) (0 0)) ((4 2) (2 0)) ((4 2) (3 0)) ((4 2) (5 0))
    ((4 4) (1 0)) ((5 1) (4 3)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0)
    (privk hash-0) (privk hash-1))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (displaced 6 4 customer 3) nb-0 (5 0)
    (enc nc nb-0 m price (pubk c)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b-0)) (enc nc nb-1 (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) nb-0)))
    ((recv (enc c nc nb-0 acctnum-1 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))))
  (label 50)
  (parent 40)
  (seen 38 52)
  (unrealized (0 0) (0 2) (1 0) (5 0))
  (comment "3 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (price acctnum goods price-0 text) (nc nb nb-0 nm data)
    (m c hash b hash-0 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand customer 5 (acctnum acctnum) (goods goods) (price price)
    (nc nc) (nm nb-0) (nb nb-0) (b b) (c c) (m m) (hash hash-0))
  (defstrand merchant 2 (goods goods) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (precedes ((0 1) (3 1)) ((1 1) (0 2)) ((2 1) (3 3)) ((3 0) (4 0))
    ((3 2) (2 0)) ((3 4) (1 0)) ((4 1) (0 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0))
  (uniq-orig nc nb nb-0 nm)
  (operation nonce-test (contracted (goods-0 goods)) nc (0 0)
    (enc nc nm m price-0 (pubk c)) (enc c nc goods (pubk m)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) nb-0)))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price-0 (pubk c)))))
  (label 51)
  (parent 42)
  (unrealized (0 2))
  (comment "empty cohort"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 acctnum-1 text)
    (nc nb nb-0 nb-1 data) (b m c hash b-0 hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nb-0) (nb nb-0) (b b-0) (c c) (m m)
    (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-1) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b-0) (c c) (hash hash-1))
  (precedes ((0 1) (3 1)) ((1 1) (0 2)) ((2 1) (1 0)) ((3 0) (0 0))
    ((3 2) (2 0)) ((3 2) (5 0)) ((3 4) (1 0)) ((4 1) (3 3))
    ((5 1) (4 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0)
    (privk hash-0) (privk hash-1))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (displaced 6 3 customer 3) nb-0 (5 0)
    (enc nc nb-0 m price (pubk c)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) nb-0)))
    ((recv (enc c nc nb-0 acctnum-1 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b-0)) (enc nc nb-1 (pubk c))))))
  (label 52)
  (parent 45)
  (unrealized (0 0) (0 2) (1 0) (4 0))
  (comment "3 in cohort - 3 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (price price-0 acctnum goods text) (nc nb nb-0 nb-1 nm data)
    (c hash hash-0 hash-1 b m name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b) (c c) (hash hash-1))
  (defstrand merchant 2 (goods goods) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (defstrand customer 5 (acctnum acctnum) (goods goods) (price price)
    (nc nc) (nm nb-0) (nb nb) (b b) (c c) (m m) (hash hash))
  (precedes ((0 1) (5 1)) ((1 1) (5 3)) ((2 1) (1 0)) ((3 1) (1 0))
    ((4 1) (0 0)) ((5 0) (4 0)) ((5 2) (2 0)) ((5 2) (3 0))
    ((5 4) (0 2)))
  (non-orig (privk c) (privk hash) (privk hash-0) (privk hash-1)
    (privk b) (privk m))
  (uniq-orig nc nb nb-0 nm)
  (operation nonce-test (displaced 2 6 customer 5) nb (0 2)
    (enc "hash" c nc nb nb-0 price (pubk hash)) (enc nc nb (pubk c)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-1 (pubk c)))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price-0 (pubk c))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))))
  (label 53)
  (parent 47)
  (seen 25)
  (unrealized)
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (price acctnum goods text) (nc nb nb-0 nb-1 data)
    (m c hash b hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b) (c c) (hash hash-1))
  (defstrand customer 5 (acctnum acctnum) (goods goods) (price price)
    (nc nc) (nm nb-0) (nb nb-0) (b b) (c c) (m m) (hash hash-0))
  (precedes ((0 1) (4 1)) ((1 1) (0 2)) ((2 1) (4 3)) ((3 1) (1 0))
    ((4 0) (0 0)) ((4 2) (2 0)) ((4 2) (3 0)) ((4 4) (1 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0)
    (privk hash-1))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (contracted (goods-0 goods)) nc (0 0)
    (enc c nc goods (pubk m)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-1 (pubk c)))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) nb-0))))
  (label 54)
  (parent 48)
  (unrealized (0 2))
  (comment "empty cohort"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum goods-0 price-0 text)
    (nc nb nb-0 nb-1 nm data) (m c hash b hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b) (c c) (hash hash-1))
  (defstrand customer 5 (acctnum acctnum) (goods goods-0) (price price)
    (nc nc) (nm nb-0) (nb nb-0) (b b) (c c) (m m) (hash hash-0))
  (defstrand merchant 2 (goods goods-0) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (precedes ((0 1) (4 1)) ((1 1) (0 2)) ((2 1) (4 3)) ((3 1) (1 0))
    ((4 0) (5 0)) ((4 2) (2 0)) ((4 2) (3 0)) ((4 4) (1 0))
    ((5 1) (0 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0)
    (privk hash-1))
  (uniq-orig nc nb nb-0 nm)
  (operation nonce-test (added-strand merchant 2) nc (0 0)
    (enc c nc goods-0 (pubk m)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-1 (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) nb-0)))
    ((recv (enc c nc goods-0 (pubk m)))
      (send (enc nc nm m price-0 (pubk c)))))
  (label 55)
  (parent 48)
  (unrealized (0 0) (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum goods-0 price-0 text)
    (nc nb nb-0 nb-1 nm data) (m c hash b hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b) (c c) (hash hash-1))
  (defstrand customer 5 (acctnum acctnum) (goods goods-0) (price price)
    (nc nc) (nm nb-0) (nb nb-0) (b b) (c c) (m m) (hash hash-0))
  (defstrand merchant 2 (goods goods-0) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (precedes ((0 1) (4 1)) ((1 1) (0 2)) ((2 1) (4 3)) ((3 1) (1 0))
    ((4 0) (0 0)) ((4 0) (5 0)) ((4 2) (2 0)) ((4 2) (3 0))
    ((4 4) (1 0)) ((5 1) (1 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0)
    (privk hash-1))
  (uniq-orig nc nb nb-0 nm)
  (operation nonce-test (contracted (b-0 b) (acctnum-0 acctnum)) nc
    (1 0) (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
    (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
    (enc nc nb-0 (pubk c)) (enc nc nb-1 (pubk c))
    (enc nc nb-0 m price (pubk c)) (enc nc nm m price-0 (pubk c))
    (enc c nc goods-0 (pubk m)) (enc c nc nb-0 acctnum price (pubk b)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-1 (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) nb-0)))
    ((recv (enc c nc goods-0 (pubk m)))
      (send (enc nc nm m price-0 (pubk c)))))
  (label 56)
  (parent 49)
  (seen 54 55)
  (unrealized (0 0) (0 2))
  (comment "2 in cohort - 0 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 acctnum-1 text)
    (nc nb nb-0 nb-1 nb-2 data)
    (b m c hash b-0 hash-0 hash-1 hash-2 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b-0) (c c) (hash hash-1))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nb-0) (nb nb-0) (b b-0) (c c) (m m)
    (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-1) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-2) (b b-0) (c c) (hash hash-2))
  (precedes ((0 1) (4 1)) ((0 1) (6 0)) ((1 1) (0 2)) ((2 1) (1 0))
    ((3 1) (1 0)) ((4 0) (0 0)) ((4 2) (2 0)) ((4 2) (3 0))
    ((4 2) (5 0)) ((4 4) (1 0)) ((5 1) (4 3)) ((6 1) (5 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0)
    (privk hash-0) (privk hash-1) (privk hash-2))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (added-strand bank 2) nb-0 (5 0)
    (enc nc nb-0 m price (pubk c))
    (enc c nc nb-0 acctnum-0 price (pubk b-0)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b-0)) (enc nc nb-1 (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) nb-0)))
    ((recv (enc c nc nb-0 acctnum-1 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-2 nb-0 price (pubk hash-2))
            (privk b-0)) (enc nc nb-2 (pubk c))))))
  (label 57)
  (parent 50)
  (seen 52)
  (unrealized (0 0) (0 2) (1 0) (5 0) (6 0))
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 text)
    (nc nb nb-0 nb-1 data) (b m c hash b-0 hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nb-0) (nb nb-0) (b b-0) (c c) (m m)
    (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b-0) (c c) (hash hash-1))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (0 0)) ((2 2) (4 0))
    ((2 4) (1 0)) ((3 1) (2 3)) ((4 1) (3 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0)
    (privk hash-0) (privk hash-1))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (contracted (acctnum-1 acctnum-0)) nb-0 (4 0)
    (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
    (enc nc nb-0 m price (pubk c))
    (enc c nc nb-0 acctnum-0 price (pubk b-0)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) nb-0)))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b-0)) (enc nc nb-1 (pubk c))))))
  (label 58)
  (parent 52)
  (unrealized (0 0) (0 2) (1 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 acctnum-1 text)
    (nc nb nb-0 data) (b m c hash b-0 hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nb-0) (nb nb-0) (b b-0) (c c) (m m)
    (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-1) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-1))
  (precedes ((0 1) (3 1)) ((1 1) (0 2)) ((2 1) (1 0)) ((3 0) (0 0))
    ((3 2) (2 0)) ((3 2) (5 0)) ((3 4) (1 0)) ((4 1) (3 3))
    ((5 1) (4 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0)
    (privk hash-0) (privk hash-1))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (displaced 6 5 bank 2) nb-1 (4 0)
    (enc "hash" c nc nb-0 nb-1 price (pubk hash-1))
    (enc nc nb-1 m price (pubk c))
    (enc c nc nb-1 acctnum-0 price (pubk b-0)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) nb-0)))
    ((recv (enc c nc nb-0 acctnum-1 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
            (privk b-0)) (enc nc nb-0 (pubk c))))))
  (label 59)
  (parent 52)
  (unrealized (0 0) (0 2) (1 0) (4 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 acctnum-1 text)
    (nc nb nb-0 nb-1 data) (b m c hash b-0 hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nb-0) (nb nb-0) (b b-0) (c c) (m m)
    (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-1) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b-0) (c c) (hash hash-1))
  (precedes ((0 1) (3 1)) ((1 1) (0 2)) ((2 1) (4 0)) ((3 0) (0 0))
    ((3 2) (2 0)) ((3 2) (5 0)) ((3 4) (1 0)) ((4 1) (3 3))
    ((5 1) (4 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0)
    (privk hash-0) (privk hash-1))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (displaced 6 2 bank 2) nb-0 (4 0)
    (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
    (enc nc nb-0 m price (pubk c))
    (enc c nc nb-0 acctnum-0 price (pubk b-0)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) nb-0)))
    ((recv (enc c nc nb-0 acctnum-1 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b-0)) (enc nc nb-1 (pubk c))))))
  (label 60)
  (parent 52)
  (unrealized (0 0) (0 2) (1 0) (4 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (price acctnum goods price-0 text) (nc nb nb-0 nb-1 nm data)
    (m c hash b hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b) (c c) (hash hash-1))
  (defstrand customer 5 (acctnum acctnum) (goods goods) (price price)
    (nc nc) (nm nb-0) (nb nb-0) (b b) (c c) (m m) (hash hash-0))
  (defstrand merchant 2 (goods goods) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (precedes ((0 1) (4 1)) ((1 1) (0 2)) ((2 1) (4 3)) ((3 1) (1 0))
    ((4 0) (5 0)) ((4 2) (2 0)) ((4 2) (3 0)) ((4 4) (1 0))
    ((5 1) (0 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0)
    (privk hash-1))
  (uniq-orig nc nb nb-0 nm)
  (operation nonce-test (contracted (goods-0 goods)) nc (0 0)
    (enc nc nm m price-0 (pubk c)) (enc c nc goods (pubk m)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-1 (pubk c)))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) nb-0)))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price-0 (pubk c)))))
  (label 61)
  (parent 55)
  (unrealized (0 2))
  (comment "empty cohort"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum goods-0 text) (nc nb nb-0 nb-1 data)
    (m c hash b hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 5 (acctnum acctnum) (goods goods-0) (price price)
    (nc nc) (nm nb-0) (nb nb-0) (b b) (c c) (m m) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b) (c c) (hash hash-1))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (0 0)) ((2 2) (4 0))
    ((2 4) (1 0)) ((3 1) (2 3)) ((4 1) (3 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0)
    (privk hash-1))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (contracted (b-0 b) (acctnum-0 acctnum)) nc
    (1 0) (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
    (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
    (enc nc nb-0 (pubk c)) (enc nc nb-1 (pubk c))
    (enc nc nb-0 m price (pubk c)) (enc c nc goods-0 (pubk m))
    (enc c nc nb-0 acctnum price (pubk b)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) nb-0)))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-1 (pubk c))))))
  (label 62)
  (parent 58)
  (unrealized (0 0) (0 2))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 price-0 text)
    (nc nb nb-0 nb-1 nm data) (b m c hash b-0 hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nb-0) (nb nb-0) (b b-0) (c c) (m m)
    (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b-0) (c c) (hash hash-1))
  (defstrand merchant 2 (goods goods-0) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (0 0)) ((2 0) (5 0))
    ((2 2) (4 0)) ((2 4) (1 0)) ((3 1) (2 3)) ((4 1) (3 0))
    ((5 1) (1 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0)
    (privk hash-0) (privk hash-1))
  (uniq-orig nc nb nb-0 nm)
  (operation nonce-test (added-strand merchant 2) nc (1 0)
    (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
    (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
    (enc nc nb-0 (pubk c)) (enc nc nb-1 (pubk c))
    (enc nc nb-0 m price (pubk c)) (enc c nc goods-0 (pubk m))
    (enc c nc nb-0 acctnum-0 price (pubk b-0)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) nb-0)))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b-0)) (enc nc nb-1 (pubk c)))))
    ((recv (enc c nc goods-0 (pubk m)))
      (send (enc nc nm m price-0 (pubk c)))))
  (label 63)
  (parent 58)
  (unrealized (0 0) (0 2) (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 text) (nc nb nb-0 data)
    (b m c hash b-0 hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nb-0) (nb nb-0) (b b-0) (c c) (m m)
    (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-1))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (0 0)) ((2 2) (4 0))
    ((2 4) (1 0)) ((3 1) (2 3)) ((4 1) (3 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0)
    (privk hash-0) (privk hash-1))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (contracted (acctnum-1 acctnum-0)) nb-0 (4 0)
    (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
    (enc nc nb-0 (pubk c)) (enc nc nb-0 m price (pubk c))
    (enc c nc nb-0 acctnum-0 price (pubk b-0)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) nb-0)))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
            (privk b-0)) (enc nc nb-0 (pubk c))))))
  (label 64)
  (parent 59)
  (unrealized (0 0) (0 2) (1 0))
  (comment "3 in cohort - 3 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 acctnum-1 text)
    (nc nb nb-0 nb-1 data) (b m c hash b-0 hash-0 hash-1 hash-2 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nb-0) (nb nb-0) (b b-0) (c c) (m m)
    (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-1) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-1))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b-0) (c c) (hash hash-2))
  (precedes ((0 1) (3 1)) ((0 1) (6 0)) ((1 1) (0 2)) ((2 1) (1 0))
    ((3 0) (0 0)) ((3 2) (2 0)) ((3 2) (5 0)) ((3 4) (1 0))
    ((4 1) (3 3)) ((5 1) (4 0)) ((6 1) (4 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0)
    (privk hash-0) (privk hash-1) (privk hash-2))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (added-strand bank 2) nb-0 (4 0)
    (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
    (enc nc nb-0 (pubk c)) (enc nc nb-0 m price (pubk c))
    (enc c nc nb-0 acctnum-0 price (pubk b-0)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) nb-0)))
    ((recv (enc c nc nb-0 acctnum-1 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-2))
            (privk b-0)) (enc nc nb-1 (pubk c))))))
  (label 65)
  (parent 59)
  (unrealized (0 0) (0 2) (1 0) (4 0) (6 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 text)
    (nc nb nb-0 nb-1 data) (b m c hash b-0 hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nb-0) (nb nb-0) (b b-0) (c c) (m m)
    (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b-0) (c c) (hash hash-1))
  (precedes ((0 1) (3 1)) ((1 1) (0 2)) ((2 1) (4 0)) ((3 0) (0 0))
    ((3 2) (2 0)) ((3 2) (5 0)) ((3 4) (1 0)) ((4 1) (3 3))
    ((5 1) (4 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0)
    (privk hash-0) (privk hash-1))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (contracted (acctnum-1 acctnum-0)) nb-0 (4 0)
    (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
    (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
    (enc nc nb-0 (pubk c)) (enc nc nb-0 m price (pubk c))
    (enc c nc nb-0 acctnum-0 price (pubk b-0)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) nb-0)))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b-0)) (enc nc nb-1 (pubk c))))))
  (label 66)
  (parent 60)
  (unrealized (0 0) (0 2) (1 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (price acctnum goods text) (nc nb nb-0 nb-1 data)
    (m c hash b hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 5 (acctnum acctnum) (goods goods) (price price)
    (nc nc) (nm nb-0) (nb nb-0) (b b) (c c) (m m) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b) (c c) (hash hash-1))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (0 0)) ((2 2) (4 0))
    ((2 4) (1 0)) ((3 1) (2 3)) ((4 1) (3 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0)
    (privk hash-1))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (contracted (goods-0 goods)) nc (0 0)
    (enc c nc goods (pubk m)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) nb-0)))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-1 (pubk c))))))
  (label 67)
  (parent 62)
  (unrealized (0 2))
  (comment "empty cohort"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum goods-0 price-0 text)
    (nc nb nb-0 nb-1 nm data) (m c hash b hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 5 (acctnum acctnum) (goods goods-0) (price price)
    (nc nc) (nm nb-0) (nb nb-0) (b b) (c c) (m m) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b) (c c) (hash hash-1))
  (defstrand merchant 2 (goods goods-0) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (5 0)) ((2 2) (4 0))
    ((2 4) (1 0)) ((3 1) (2 3)) ((4 1) (3 0)) ((5 1) (0 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0)
    (privk hash-1))
  (uniq-orig nc nb nb-0 nm)
  (operation nonce-test (added-strand merchant 2) nc (0 0)
    (enc c nc goods-0 (pubk m)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) nb-0)))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-1 (pubk c)))))
    ((recv (enc c nc goods-0 (pubk m)))
      (send (enc nc nm m price-0 (pubk c)))))
  (label 68)
  (parent 62)
  (unrealized (0 0) (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum goods-0 price-0 text)
    (nc nb nb-0 nb-1 nm data) (m c hash b hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 5 (acctnum acctnum) (goods goods-0) (price price)
    (nc nc) (nm nb-0) (nb nb-0) (b b) (c c) (m m) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b) (c c) (hash hash-1))
  (defstrand merchant 2 (goods goods-0) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (0 0)) ((2 0) (5 0))
    ((2 2) (4 0)) ((2 4) (1 0)) ((3 1) (2 3)) ((4 1) (3 0))
    ((5 1) (1 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0)
    (privk hash-1))
  (uniq-orig nc nb nb-0 nm)
  (operation nonce-test (contracted (b-0 b) (acctnum-0 acctnum)) nc
    (1 0) (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
    (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
    (enc nc nb-0 (pubk c)) (enc nc nb-1 (pubk c))
    (enc nc nb-0 m price (pubk c)) (enc nc nm m price-0 (pubk c))
    (enc c nc goods-0 (pubk m)) (enc c nc nb-0 acctnum price (pubk b)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) nb-0)))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-1 (pubk c)))))
    ((recv (enc c nc goods-0 (pubk m)))
      (send (enc nc nm m price-0 (pubk c)))))
  (label 69)
  (parent 63)
  (seen 67 68)
  (unrealized (0 0) (0 2))
  (comment "2 in cohort - 0 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum goods-0 text) (nc nb nb-0 data)
    (m c hash b hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 5 (acctnum acctnum) (goods goods-0) (price price)
    (nc nc) (nm nb-0) (nb nb-0) (b b) (c c) (m m) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-1))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (0 0)) ((2 2) (4 0))
    ((2 4) (1 0)) ((3 1) (2 3)) ((4 1) (3 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0)
    (privk hash-1))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (contracted (b-0 b) (acctnum-0 acctnum)) nc
    (1 0) (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
    (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
    (enc nc nb-0 (pubk c)) (enc nc nb-0 m price (pubk c))
    (enc c nc goods-0 (pubk m)) (enc c nc nb-0 acctnum price (pubk b)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) nb-0)))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-0 (pubk c))))))
  (label 70)
  (parent 64)
  (unrealized (0 0) (0 2))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 text)
    (nc nb nb-0 nb-1 data) (b m c hash b-0 hash-0 hash-1 hash-2 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nb-0) (nb nb-0) (b b-0) (c c) (m m)
    (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-1))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b-0) (c c) (hash hash-2))
  (precedes ((0 1) (2 1)) ((0 1) (5 0)) ((1 1) (0 2)) ((2 0) (0 0))
    ((2 2) (4 0)) ((2 4) (1 0)) ((3 1) (2 3)) ((4 1) (3 0))
    ((5 1) (1 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0)
    (privk hash-0) (privk hash-1) (privk hash-2))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (added-strand bank 2) nc (1 0)
    (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
    (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
    (enc nc nb-0 (pubk c)) (enc nc nb-0 m price (pubk c))
    (enc c nc goods-0 (pubk m))
    (enc c nc nb-0 acctnum-0 price (pubk b-0)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) nb-0)))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-2))
            (privk b-0)) (enc nc nb-1 (pubk c))))))
  (label 71)
  (parent 64)
  (unrealized (0 0) (0 2) (1 0) (5 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 price-0 text)
    (nc nb nb-0 nm data) (b m c hash b-0 hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nb-0) (nb nb-0) (b b-0) (c c) (m m)
    (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-1))
  (defstrand merchant 2 (goods goods-0) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (0 0)) ((2 0) (5 0))
    ((2 2) (4 0)) ((2 4) (1 0)) ((3 1) (2 3)) ((4 1) (3 0))
    ((5 1) (1 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0)
    (privk hash-0) (privk hash-1))
  (uniq-orig nc nb nb-0 nm)
  (operation nonce-test (added-strand merchant 2) nc (1 0)
    (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
    (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
    (enc nc nb-0 (pubk c)) (enc nc nb-0 m price (pubk c))
    (enc c nc goods-0 (pubk m))
    (enc c nc nb-0 acctnum-0 price (pubk b-0)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) nb-0)))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc goods-0 (pubk m)))
      (send (enc nc nm m price-0 (pubk c)))))
  (label 72)
  (parent 64)
  (unrealized (0 0) (0 2) (1 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 acctnum-1 text)
    (nc nb nb-0 nb-1 data) (b m c hash b-0 hash-0 hash-1 hash-2 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nb-0) (nb nb-0) (b b-0) (c c) (m m)
    (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-1) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-1))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b-0) (c c) (hash hash-2))
  (precedes ((0 1) (3 1)) ((1 1) (0 2)) ((2 1) (1 0)) ((3 0) (0 0))
    ((3 2) (2 0)) ((3 2) (5 0)) ((3 2) (6 0)) ((3 4) (1 0))
    ((4 1) (3 3)) ((5 1) (4 0)) ((6 1) (4 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0)
    (privk hash-0) (privk hash-1) (privk hash-2))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (displaced 7 3 customer 3) nb-0 (6 0)
    (enc nc nb-0 m price (pubk c)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) nb-0)))
    ((recv (enc c nc nb-0 acctnum-1 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-2))
            (privk b-0)) (enc nc nb-1 (pubk c))))))
  (label 73)
  (parent 65)
  (unrealized (0 0) (0 2) (1 0) (4 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum goods-0 text) (nc nb nb-0 nb-1 data)
    (m c hash b hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand customer 5 (acctnum acctnum) (goods goods-0) (price price)
    (nc nc) (nm nb-0) (nb nb-0) (b b) (c c) (m m) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b) (c c) (hash hash-1))
  (precedes ((0 1) (3 1)) ((1 1) (0 2)) ((2 1) (4 0)) ((3 0) (0 0))
    ((3 2) (2 0)) ((3 2) (5 0)) ((3 4) (1 0)) ((4 1) (3 3))
    ((5 1) (4 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0)
    (privk hash-1))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (contracted (b-0 b) (acctnum-0 acctnum)) nc
    (1 0) (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
    (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
    (enc nc nb-0 (pubk c)) (enc nc nb-1 (pubk c))
    (enc nc nb-0 m price (pubk c)) (enc c nc goods-0 (pubk m))
    (enc c nc nb-0 acctnum price (pubk b)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) nb-0)))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-1 (pubk c))))))
  (label 74)
  (parent 66)
  (unrealized (0 0) (0 2))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 price-0 text)
    (nc nb nb-0 nb-1 nm data) (b m c hash b-0 hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nb-0) (nb nb-0) (b b-0) (c c) (m m)
    (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b-0) (c c) (hash hash-1))
  (defstrand merchant 2 (goods goods-0) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (precedes ((0 1) (3 1)) ((1 1) (0 2)) ((2 1) (4 0)) ((3 0) (0 0))
    ((3 0) (6 0)) ((3 2) (2 0)) ((3 2) (5 0)) ((3 4) (1 0))
    ((4 1) (3 3)) ((5 1) (4 0)) ((6 1) (1 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0)
    (privk hash-0) (privk hash-1))
  (uniq-orig nc nb nb-0 nm)
  (operation nonce-test (added-strand merchant 2) nc (1 0)
    (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
    (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
    (enc nc nb-0 (pubk c)) (enc nc nb-1 (pubk c))
    (enc nc nb-0 m price (pubk c)) (enc c nc goods-0 (pubk m))
    (enc c nc nb-0 acctnum-0 price (pubk b-0)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) nb-0)))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b-0)) (enc nc nb-1 (pubk c)))))
    ((recv (enc c nc goods-0 (pubk m)))
      (send (enc nc nm m price-0 (pubk c)))))
  (label 75)
  (parent 66)
  (unrealized (0 0) (0 2) (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (price acctnum goods price-0 text) (nc nb nb-0 nb-1 nm data)
    (m c hash b hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 5 (acctnum acctnum) (goods goods) (price price)
    (nc nc) (nm nb-0) (nb nb-0) (b b) (c c) (m m) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b) (c c) (hash hash-1))
  (defstrand merchant 2 (goods goods) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (5 0)) ((2 2) (4 0))
    ((2 4) (1 0)) ((3 1) (2 3)) ((4 1) (3 0)) ((5 1) (0 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0)
    (privk hash-1))
  (uniq-orig nc nb nb-0 nm)
  (operation nonce-test (contracted (goods-0 goods)) nc (0 0)
    (enc nc nm m price-0 (pubk c)) (enc c nc goods (pubk m)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) nb-0)))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-1 (pubk c)))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price-0 (pubk c)))))
  (label 76)
  (parent 68)
  (unrealized (0 2))
  (comment "empty cohort"))

(defskeleton sorted_epmo_acctnum
  (vars (price acctnum goods text) (nc nb nb-0 data)
    (m c hash b hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 5 (acctnum acctnum) (goods goods) (price price)
    (nc nc) (nm nb-0) (nb nb-0) (b b) (c c) (m m) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-1))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (0 0)) ((2 2) (4 0))
    ((2 4) (1 0)) ((3 1) (2 3)) ((4 1) (3 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0)
    (privk hash-1))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (contracted (goods-0 goods)) nc (0 0)
    (enc c nc goods (pubk m)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) nb-0)))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-0 (pubk c))))))
  (label 77)
  (parent 70)
  (unrealized (0 2))
  (comment "empty cohort"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum goods-0 price-0 text) (nc nb nb-0 nm data)
    (m c hash b hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 5 (acctnum acctnum) (goods goods-0) (price price)
    (nc nc) (nm nb-0) (nb nb-0) (b b) (c c) (m m) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-1))
  (defstrand merchant 2 (goods goods-0) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (5 0)) ((2 2) (4 0))
    ((2 4) (1 0)) ((3 1) (2 3)) ((4 1) (3 0)) ((5 1) (0 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0)
    (privk hash-1))
  (uniq-orig nc nb nb-0 nm)
  (operation nonce-test (added-strand merchant 2) nc (0 0)
    (enc c nc goods-0 (pubk m)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) nb-0)))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc goods-0 (pubk m)))
      (send (enc nc nm m price-0 (pubk c)))))
  (label 78)
  (parent 70)
  (unrealized (0 0) (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 text)
    (nc nb nb-0 nb-1 data) (b m c hash b-0 hash-0 hash-1 hash-2 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nb-0) (nb nb-0) (b b-0) (c c) (m m)
    (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-1))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b-0) (c c) (hash hash-2))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (0 0)) ((2 2) (4 0))
    ((2 2) (5 0)) ((2 4) (1 0)) ((3 1) (2 3)) ((4 1) (3 0))
    ((5 1) (1 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0)
    (privk hash-0) (privk hash-1) (privk hash-2))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (displaced 6 2 customer 3) nb-0 (5 0)
    (enc nc nb-0 m price (pubk c)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) nb-0)))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-2))
            (privk b-0)) (enc nc nb-1 (pubk c))))))
  (label 79)
  (parent 71)
  (unrealized (0 0) (0 2) (1 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum goods-0 price-0 text) (nc nb nb-0 nm data)
    (m c hash b hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 5 (acctnum acctnum) (goods goods-0) (price price)
    (nc nc) (nm nb-0) (nb nb-0) (b b) (c c) (m m) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-1))
  (defstrand merchant 2 (goods goods-0) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (0 0)) ((2 0) (5 0))
    ((2 2) (4 0)) ((2 4) (1 0)) ((3 1) (2 3)) ((4 1) (3 0))
    ((5 1) (1 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0)
    (privk hash-1))
  (uniq-orig nc nb nb-0 nm)
  (operation nonce-test (contracted (b-0 b) (acctnum-0 acctnum)) nc
    (1 0) (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
    (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
    (enc nc nb-0 (pubk c)) (enc nc nb-0 m price (pubk c))
    (enc nc nm m price-0 (pubk c)) (enc c nc goods-0 (pubk m))
    (enc c nc nb-0 acctnum price (pubk b)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) nb-0)))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc goods-0 (pubk m)))
      (send (enc nc nm m price-0 (pubk c)))))
  (label 80)
  (parent 72)
  (seen 77 78)
  (unrealized (0 0) (0 2))
  (comment "2 in cohort - 0 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 price-0 text)
    (nc nb nb-0 nm nb-1 data)
    (b m c hash b-0 hash-0 hash-1 hash-2 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nb-0) (nb nb-0) (b b-0) (c c) (m m)
    (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-1))
  (defstrand merchant 2 (goods goods-0) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b-0) (c c) (hash hash-2))
  (precedes ((0 1) (2 1)) ((0 1) (6 0)) ((1 1) (0 2)) ((2 0) (0 0))
    ((2 0) (5 0)) ((2 2) (4 0)) ((2 4) (1 0)) ((3 1) (2 3))
    ((4 1) (3 0)) ((5 1) (1 0)) ((6 1) (1 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0)
    (privk hash-0) (privk hash-1) (privk hash-2))
  (uniq-orig nc nb nb-0 nm)
  (operation nonce-test (added-strand bank 2) nc (1 0)
    (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
    (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
    (enc nc nb-0 (pubk c)) (enc nc nb-0 m price (pubk c))
    (enc nc nm m price-0 (pubk c)) (enc c nc goods-0 (pubk m))
    (enc c nc nb-0 acctnum-0 price (pubk b-0)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) nb-0)))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc goods-0 (pubk m)))
      (send (enc nc nm m price-0 (pubk c))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-2))
            (privk b-0)) (enc nc nb-1 (pubk c))))))
  (label 81)
  (parent 72)
  (seen 88)
  (unrealized (0 0) (0 2) (1 0) (6 0))
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 text)
    (nc nb nb-0 nb-1 data) (b m c hash b-0 hash-0 hash-1 hash-2 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nb-0) (nb nb-0) (b b-0) (c c) (m m)
    (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-1))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b-0) (c c) (hash hash-2))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (0 0)) ((2 2) (4 0))
    ((2 2) (5 0)) ((2 4) (1 0)) ((3 1) (2 3)) ((4 1) (3 0))
    ((5 1) (3 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0)
    (privk hash-0) (privk hash-1) (privk hash-2))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (contracted (acctnum-1 acctnum-0)) nb-0 (4 0)
    (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
    (enc "hash" c nc nb-1 nb-0 price (pubk hash-2))
    (enc nc nb-0 (pubk c)) (enc nc nb-0 m price (pubk c))
    (enc c nc nb-0 acctnum-0 price (pubk b-0)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) nb-0)))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-2))
            (privk b-0)) (enc nc nb-1 (pubk c))))))
  (label 82)
  (parent 73)
  (unrealized (0 0) (0 2) (1 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (price acctnum goods text) (nc nb nb-0 nb-1 data)
    (m c hash b hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand customer 5 (acctnum acctnum) (goods goods) (price price)
    (nc nc) (nm nb-0) (nb nb-0) (b b) (c c) (m m) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b) (c c) (hash hash-1))
  (precedes ((0 1) (3 1)) ((1 1) (0 2)) ((2 1) (4 0)) ((3 0) (0 0))
    ((3 2) (2 0)) ((3 2) (5 0)) ((3 4) (1 0)) ((4 1) (3 3))
    ((5 1) (4 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0)
    (privk hash-1))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (contracted (goods-0 goods)) nc (0 0)
    (enc c nc goods (pubk m)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) nb-0)))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-1 (pubk c))))))
  (label 83)
  (parent 74)
  (unrealized (0 2))
  (comment "empty cohort"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum goods-0 price-0 text)
    (nc nb nb-0 nb-1 nm data) (m c hash b hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand customer 5 (acctnum acctnum) (goods goods-0) (price price)
    (nc nc) (nm nb-0) (nb nb-0) (b b) (c c) (m m) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b) (c c) (hash hash-1))
  (defstrand merchant 2 (goods goods-0) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (precedes ((0 1) (3 1)) ((1 1) (0 2)) ((2 1) (4 0)) ((3 0) (6 0))
    ((3 2) (2 0)) ((3 2) (5 0)) ((3 4) (1 0)) ((4 1) (3 3))
    ((5 1) (4 0)) ((6 1) (0 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0)
    (privk hash-1))
  (uniq-orig nc nb nb-0 nm)
  (operation nonce-test (added-strand merchant 2) nc (0 0)
    (enc c nc goods-0 (pubk m)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) nb-0)))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-1 (pubk c)))))
    ((recv (enc c nc goods-0 (pubk m)))
      (send (enc nc nm m price-0 (pubk c)))))
  (label 84)
  (parent 74)
  (unrealized (0 0) (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum goods-0 price-0 text)
    (nc nb nb-0 nb-1 nm data) (m c hash b hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand customer 5 (acctnum acctnum) (goods goods-0) (price price)
    (nc nc) (nm nb-0) (nb nb-0) (b b) (c c) (m m) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b) (c c) (hash hash-1))
  (defstrand merchant 2 (goods goods-0) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (precedes ((0 1) (3 1)) ((1 1) (0 2)) ((2 1) (4 0)) ((3 0) (0 0))
    ((3 0) (6 0)) ((3 2) (2 0)) ((3 2) (5 0)) ((3 4) (1 0))
    ((4 1) (3 3)) ((5 1) (4 0)) ((6 1) (1 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0)
    (privk hash-1))
  (uniq-orig nc nb nb-0 nm)
  (operation nonce-test (contracted (b-0 b) (acctnum-0 acctnum)) nc
    (1 0) (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
    (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
    (enc nc nb-0 (pubk c)) (enc nc nb-1 (pubk c))
    (enc nc nb-0 m price (pubk c)) (enc nc nm m price-0 (pubk c))
    (enc c nc goods-0 (pubk m)) (enc c nc nb-0 acctnum price (pubk b)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) nb-0)))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-1 (pubk c)))))
    ((recv (enc c nc goods-0 (pubk m)))
      (send (enc nc nm m price-0 (pubk c)))))
  (label 85)
  (parent 75)
  (seen 83 84)
  (unrealized (0 0) (0 2))
  (comment "2 in cohort - 0 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (price acctnum goods price-0 text) (nc nb nb-0 nm data)
    (m c hash b hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 5 (acctnum acctnum) (goods goods) (price price)
    (nc nc) (nm nb-0) (nb nb-0) (b b) (c c) (m m) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-1))
  (defstrand merchant 2 (goods goods) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (5 0)) ((2 2) (4 0))
    ((2 4) (1 0)) ((3 1) (2 3)) ((4 1) (3 0)) ((5 1) (0 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0)
    (privk hash-1))
  (uniq-orig nc nb nb-0 nm)
  (operation nonce-test (contracted (goods-0 goods)) nc (0 0)
    (enc nc nm m price-0 (pubk c)) (enc c nc goods (pubk m)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) nb-0)))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price-0 (pubk c)))))
  (label 86)
  (parent 78)
  (unrealized (0 2))
  (comment "empty cohort"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum goods-0 text) (nc nb nb-0 nb-1 data)
    (m c hash b hash-0 hash-1 hash-2 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 5 (acctnum acctnum) (goods goods-0) (price price)
    (nc nc) (nm nb-0) (nb nb-0) (b b) (c c) (m m) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-1))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b) (c c) (hash hash-2))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (0 0)) ((2 2) (4 0))
    ((2 2) (5 0)) ((2 4) (1 0)) ((3 1) (2 3)) ((4 1) (3 0))
    ((5 1) (1 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0)
    (privk hash-1) (privk hash-2))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (contracted (b-0 b) (acctnum-0 acctnum)) nc
    (1 0) (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
    (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
    (enc "hash" c nc nb-1 nb-0 price (pubk hash-2))
    (enc nc nb-0 (pubk c)) (enc nc nb-1 (pubk c))
    (enc nc nb-0 m price (pubk c)) (enc c nc goods-0 (pubk m))
    (enc c nc nb-0 acctnum price (pubk b)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) nb-0)))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-2))
            (privk b)) (enc nc nb-1 (pubk c))))))
  (label 87)
  (parent 79)
  (unrealized (0 0) (0 2))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 price-0 text)
    (nc nb nb-0 nb-1 nm data)
    (b m c hash b-0 hash-0 hash-1 hash-2 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nb-0) (nb nb-0) (b b-0) (c c) (m m)
    (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-1))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b-0) (c c) (hash hash-2))
  (defstrand merchant 2 (goods goods-0) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (0 0)) ((2 0) (6 0))
    ((2 2) (4 0)) ((2 2) (5 0)) ((2 4) (1 0)) ((3 1) (2 3))
    ((4 1) (3 0)) ((5 1) (1 0)) ((6 1) (1 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0)
    (privk hash-0) (privk hash-1) (privk hash-2))
  (uniq-orig nc nb nb-0 nm)
  (operation nonce-test (added-strand merchant 2) nc (1 0)
    (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
    (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
    (enc "hash" c nc nb-1 nb-0 price (pubk hash-2))
    (enc nc nb-0 (pubk c)) (enc nc nb-1 (pubk c))
    (enc nc nb-0 m price (pubk c)) (enc c nc goods-0 (pubk m))
    (enc c nc nb-0 acctnum-0 price (pubk b-0)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) nb-0)))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-2))
            (privk b-0)) (enc nc nb-1 (pubk c)))))
    ((recv (enc c nc goods-0 (pubk m)))
      (send (enc nc nm m price-0 (pubk c)))))
  (label 88)
  (parent 79)
  (unrealized (0 0) (0 2) (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum goods-0 text) (nc nb nb-0 nb-1 data)
    (m c hash b hash-0 hash-1 hash-2 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 5 (acctnum acctnum) (goods goods-0) (price price)
    (nc nc) (nm nb-0) (nb nb-0) (b b) (c c) (m m) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-1))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b) (c c) (hash hash-2))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (0 0)) ((2 2) (4 0))
    ((2 2) (5 0)) ((2 4) (1 0)) ((3 1) (2 3)) ((4 1) (3 0))
    ((5 1) (3 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0)
    (privk hash-1) (privk hash-2))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (contracted (b-0 b) (acctnum-0 acctnum)) nc
    (1 0) (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
    (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
    (enc "hash" c nc nb-1 nb-0 price (pubk hash-2))
    (enc nc nb-0 (pubk c)) (enc nc nb-1 (pubk c))
    (enc nc nb-0 m price (pubk c)) (enc c nc goods-0 (pubk m))
    (enc c nc nb-0 acctnum price (pubk b)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) nb-0)))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-2))
            (privk b)) (enc nc nb-1 (pubk c))))))
  (label 89)
  (parent 82)
  (unrealized (0 0) (0 2))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum acctnum-0 goods-0 price-0 text)
    (nc nb nb-0 nb-1 nm data)
    (b m c hash b-0 hash-0 hash-1 hash-2 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nb-0) (nb nb-0) (b b-0) (c c) (m m)
    (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b-0) (c c) (hash hash-1))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b-0) (c c) (hash hash-2))
  (defstrand merchant 2 (goods goods-0) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (0 0)) ((2 0) (6 0))
    ((2 2) (4 0)) ((2 2) (5 0)) ((2 4) (1 0)) ((3 1) (2 3))
    ((4 1) (3 0)) ((5 1) (3 0)) ((6 1) (1 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0)
    (privk hash-0) (privk hash-1) (privk hash-2))
  (uniq-orig nc nb nb-0 nm)
  (operation nonce-test (added-strand merchant 2) nc (1 0)
    (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
    (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
    (enc "hash" c nc nb-1 nb-0 price (pubk hash-2))
    (enc nc nb-0 (pubk c)) (enc nc nb-1 (pubk c))
    (enc nc nb-0 m price (pubk c)) (enc c nc goods-0 (pubk m))
    (enc c nc nb-0 acctnum-0 price (pubk b-0)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) nb-0)))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
            (privk b-0)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b-0)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-2))
            (privk b-0)) (enc nc nb-1 (pubk c)))))
    ((recv (enc c nc goods-0 (pubk m)))
      (send (enc nc nm m price-0 (pubk c)))))
  (label 90)
  (parent 82)
  (unrealized (0 0) (0 2) (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (price acctnum goods price-0 text) (nc nb nb-0 nb-1 nm data)
    (m c hash b hash-0 hash-1 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand customer 5 (acctnum acctnum) (goods goods) (price price)
    (nc nc) (nm nb-0) (nb nb-0) (b b) (c c) (m m) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b) (c c) (hash hash-1))
  (defstrand merchant 2 (goods goods) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (precedes ((0 1) (3 1)) ((1 1) (0 2)) ((2 1) (4 0)) ((3 0) (6 0))
    ((3 2) (2 0)) ((3 2) (5 0)) ((3 4) (1 0)) ((4 1) (3 3))
    ((5 1) (4 0)) ((6 1) (0 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0)
    (privk hash-1))
  (uniq-orig nc nb nb-0 nm)
  (operation nonce-test (contracted (goods-0 goods)) nc (0 0)
    (enc nc nm m price-0 (pubk c)) (enc c nc goods (pubk m)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) nb-0)))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-1 (pubk c)))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price-0 (pubk c)))))
  (label 91)
  (parent 84)
  (unrealized (0 2))
  (comment "empty cohort"))

(defskeleton sorted_epmo_acctnum
  (vars (price acctnum goods text) (nc nb nb-0 nb-1 data)
    (m c hash b hash-0 hash-1 hash-2 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 5 (acctnum acctnum) (goods goods) (price price)
    (nc nc) (nm nb-0) (nb nb-0) (b b) (c c) (m m) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-1))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b) (c c) (hash hash-2))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (0 0)) ((2 2) (4 0))
    ((2 2) (5 0)) ((2 4) (1 0)) ((3 1) (2 3)) ((4 1) (3 0))
    ((5 1) (1 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0)
    (privk hash-1) (privk hash-2))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (contracted (goods-0 goods)) nc (0 0)
    (enc c nc goods (pubk m)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) nb-0)))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-2))
            (privk b)) (enc nc nb-1 (pubk c))))))
  (label 92)
  (parent 87)
  (unrealized (0 2))
  (comment "empty cohort"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum goods-0 price-0 text)
    (nc nb nb-0 nb-1 nm data) (m c hash b hash-0 hash-1 hash-2 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 5 (acctnum acctnum) (goods goods-0) (price price)
    (nc nc) (nm nb-0) (nb nb-0) (b b) (c c) (m m) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-1))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b) (c c) (hash hash-2))
  (defstrand merchant 2 (goods goods-0) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (6 0)) ((2 2) (4 0))
    ((2 2) (5 0)) ((2 4) (1 0)) ((3 1) (2 3)) ((4 1) (3 0))
    ((5 1) (1 0)) ((6 1) (0 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0)
    (privk hash-1) (privk hash-2))
  (uniq-orig nc nb nb-0 nm)
  (operation nonce-test (added-strand merchant 2) nc (0 0)
    (enc c nc goods-0 (pubk m)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) nb-0)))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-2))
            (privk b)) (enc nc nb-1 (pubk c)))))
    ((recv (enc c nc goods-0 (pubk m)))
      (send (enc nc nm m price-0 (pubk c)))))
  (label 93)
  (parent 87)
  (unrealized (0 0) (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum goods-0 price-0 text)
    (nc nb nb-0 nb-1 nm data) (m c hash b hash-0 hash-1 hash-2 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 5 (acctnum acctnum) (goods goods-0) (price price)
    (nc nc) (nm nb-0) (nb nb-0) (b b) (c c) (m m) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-1))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b) (c c) (hash hash-2))
  (defstrand merchant 2 (goods goods-0) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (0 0)) ((2 0) (6 0))
    ((2 2) (4 0)) ((2 2) (5 0)) ((2 4) (1 0)) ((3 1) (2 3))
    ((4 1) (3 0)) ((5 1) (1 0)) ((6 1) (1 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0)
    (privk hash-1) (privk hash-2))
  (uniq-orig nc nb nb-0 nm)
  (operation nonce-test (contracted (b-0 b) (acctnum-0 acctnum)) nc
    (1 0) (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
    (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
    (enc "hash" c nc nb-1 nb-0 price (pubk hash-2))
    (enc nc nb-0 (pubk c)) (enc nc nb-1 (pubk c))
    (enc nc nb-0 m price (pubk c)) (enc nc nm m price-0 (pubk c))
    (enc c nc goods-0 (pubk m)) (enc c nc nb-0 acctnum price (pubk b)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) nb-0)))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-2))
            (privk b)) (enc nc nb-1 (pubk c)))))
    ((recv (enc c nc goods-0 (pubk m)))
      (send (enc nc nm m price-0 (pubk c)))))
  (label 94)
  (parent 88)
  (seen 92 93)
  (unrealized (0 0) (0 2))
  (comment "2 in cohort - 0 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (price acctnum goods text) (nc nb nb-0 nb-1 data)
    (m c hash b hash-0 hash-1 hash-2 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 5 (acctnum acctnum) (goods goods) (price price)
    (nc nc) (nm nb-0) (nb nb-0) (b b) (c c) (m m) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-1))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b) (c c) (hash hash-2))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (0 0)) ((2 2) (4 0))
    ((2 2) (5 0)) ((2 4) (1 0)) ((3 1) (2 3)) ((4 1) (3 0))
    ((5 1) (3 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0)
    (privk hash-1) (privk hash-2))
  (uniq-orig nc nb nb-0)
  (operation nonce-test (contracted (goods-0 goods)) nc (0 0)
    (enc c nc goods (pubk m)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) nb-0)))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-2))
            (privk b)) (enc nc nb-1 (pubk c))))))
  (label 95)
  (parent 89)
  (unrealized (0 2))
  (comment "empty cohort"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum goods-0 price-0 text)
    (nc nb nb-0 nb-1 nm data) (m c hash b hash-0 hash-1 hash-2 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 5 (acctnum acctnum) (goods goods-0) (price price)
    (nc nc) (nm nb-0) (nb nb-0) (b b) (c c) (m m) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-1))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b) (c c) (hash hash-2))
  (defstrand merchant 2 (goods goods-0) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (6 0)) ((2 2) (4 0))
    ((2 2) (5 0)) ((2 4) (1 0)) ((3 1) (2 3)) ((4 1) (3 0))
    ((5 1) (3 0)) ((6 1) (0 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0)
    (privk hash-1) (privk hash-2))
  (uniq-orig nc nb nb-0 nm)
  (operation nonce-test (added-strand merchant 2) nc (0 0)
    (enc c nc goods-0 (pubk m)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) nb-0)))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-2))
            (privk b)) (enc nc nb-1 (pubk c)))))
    ((recv (enc c nc goods-0 (pubk m)))
      (send (enc nc nm m price-0 (pubk c)))))
  (label 96)
  (parent 89)
  (unrealized (0 0) (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (goods price acctnum goods-0 price-0 text)
    (nc nb nb-0 nb-1 nm data) (m c hash b hash-0 hash-1 hash-2 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 5 (acctnum acctnum) (goods goods-0) (price price)
    (nc nc) (nm nb-0) (nb nb-0) (b b) (c c) (m m) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-1))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b) (c c) (hash hash-2))
  (defstrand merchant 2 (goods goods-0) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (0 0)) ((2 0) (6 0))
    ((2 2) (4 0)) ((2 2) (5 0)) ((2 4) (1 0)) ((3 1) (2 3))
    ((4 1) (3 0)) ((5 1) (3 0)) ((6 1) (1 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0)
    (privk hash-1) (privk hash-2))
  (uniq-orig nc nb nb-0 nm)
  (operation nonce-test (contracted (b-0 b) (acctnum-0 acctnum)) nc
    (1 0) (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
    (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
    (enc "hash" c nc nb-1 nb-0 price (pubk hash-2))
    (enc nc nb-0 (pubk c)) (enc nc nb-1 (pubk c))
    (enc nc nb-0 m price (pubk c)) (enc nc nm m price-0 (pubk c))
    (enc c nc goods-0 (pubk m)) (enc c nc nb-0 acctnum price (pubk b)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) nb-0)))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-2))
            (privk b)) (enc nc nb-1 (pubk c)))))
    ((recv (enc c nc goods-0 (pubk m)))
      (send (enc nc nm m price-0 (pubk c)))))
  (label 97)
  (parent 90)
  (seen 95 96)
  (unrealized (0 0) (0 2))
  (comment "2 in cohort - 0 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (price acctnum goods price-0 text) (nc nb nb-0 nb-1 nm data)
    (m c hash b hash-0 hash-1 hash-2 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 5 (acctnum acctnum) (goods goods) (price price)
    (nc nc) (nm nb-0) (nb nb-0) (b b) (c c) (m m) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-1))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b) (c c) (hash hash-2))
  (defstrand merchant 2 (goods goods) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (6 0)) ((2 2) (4 0))
    ((2 2) (5 0)) ((2 4) (1 0)) ((3 1) (2 3)) ((4 1) (3 0))
    ((5 1) (1 0)) ((6 1) (0 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0)
    (privk hash-1) (privk hash-2))
  (uniq-orig nc nb nb-0 nm)
  (operation nonce-test (contracted (goods-0 goods)) nc (0 0)
    (enc nc nm m price-0 (pubk c)) (enc c nc goods (pubk m)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) nb-0)))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-2))
            (privk b)) (enc nc nb-1 (pubk c)))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price-0 (pubk c)))))
  (label 98)
  (parent 93)
  (unrealized (0 2))
  (comment "empty cohort"))

(defskeleton sorted_epmo_acctnum
  (vars (price acctnum goods price-0 text) (nc nb nb-0 nb-1 nm data)
    (m c hash b hash-0 hash-1 hash-2 name))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (hash hash))
  (defstrand customer 5 (acctnum acctnum) (goods goods) (price price)
    (nc nc) (nm nb-0) (nb nb-0) (b b) (c c) (m m) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-1))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b) (c c) (hash hash-2))
  (defstrand merchant 2 (goods goods) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (6 0)) ((2 2) (4 0))
    ((2 2) (5 0)) ((2 4) (1 0)) ((3 1) (2 3)) ((4 1) (3 0))
    ((5 1) (3 0)) ((6 1) (0 0)))
  (non-orig (privk m) (privk c) (privk hash) (privk b) (privk hash-0)
    (privk hash-1) (privk hash-2))
  (uniq-orig nc nb nb-0 nm)
  (operation nonce-test (contracted (goods-0 goods)) nc (0 0)
    (enc nc nm m price-0 (pubk c)) (enc c nc goods (pubk m)))
  (traces
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) nb-0)))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-2))
            (privk b)) (enc nc nb-1 (pubk c)))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price-0 (pubk c)))))
  (label 99)
  (parent 96)
  (unrealized (0 2))
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol sorted_epmo_acctnum basic
  (defrole bank
    (vars (b c m name) (acctnum price text) (hash name) (nc nm nb data))
    (trace (recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    (non-orig (privk hash))
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
    (vars (b c m hash name) (acctnum goods price text) (nc nm nb data))
    (trace (send (enc c nc goods (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum price (pubk b)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb)))
    (non-orig (privk b) (privk hash))
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
    (vars (b c m hash name) (goods price text) (nc nm nb data))
    (trace (recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    (non-orig (privk hash))
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

(defskeleton sorted_epmo_acctnum
  (vars (acctnum price text) (nm nb nc data) (b m c hash name))
  (defstrand bank 3 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (non-orig (privk b) (privk m) (privk c) (privk hash))
  (uniq-orig nm nb nc)
  (traces
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" b m nb nm (pubk hash)) (privk m)))))
  (label 100)
  (unrealized (0 2))
  (origs (nb (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (acctnum price goods price-0 text) (nm nb nc nc-0 data)
    (b m c hash c-0 name))
  (defstrand bank 3 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 4 (goods goods) (price price-0) (nc nc-0) (nm nm)
    (nb nb) (b b) (c c-0) (m m) (hash hash))
  (precedes ((0 1) (1 2)) ((1 1) (0 0)) ((1 3) (0 2)))
  (non-orig (privk b) (privk m) (privk c) (privk hash))
  (uniq-orig nm nb nc)
  (operation encryption-test (added-strand merchant 4)
    (enc (enc "hash" b m nb nm (pubk hash)) (privk m)) (0 2))
  (traces
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((recv (enc c-0 nc-0 goods (pubk m)))
      (send (enc nc-0 nm m price-0 (pubk c-0)))
      (recv
        (cat
          (enc (enc "hash" c-0 nc-0 nb nm price-0 (pubk hash))
            (privk b)) nb))
      (send (enc (enc "hash" b m nb nm (pubk hash)) (privk m)))))
  (label 101)
  (parent 100)
  (unrealized (1 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (acctnum price goods text) (nm nb nc data) (b m c hash name))
  (defstrand bank 3 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (precedes ((0 1) (1 2)) ((1 1) (0 0)) ((1 3) (0 2)))
  (non-orig (privk b) (privk m) (privk c) (privk hash))
  (uniq-orig nm nb nc)
  (operation encryption-test (displaced 2 0 bank 2)
    (enc (enc "hash" c-0 nc-0 nb nm price-0 (pubk hash)) (privk b))
    (1 2))
  (traces
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nm (pubk hash)) (privk m)))))
  (label 102)
  (parent 101)
  (unrealized (0 0) (1 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (acctnum price goods acctnum-0 goods-0 text) (nm nb nc data)
    (b m c hash b-0 m-0 name))
  (defstrand bank 3 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nm) (nb nb) (b b-0) (c c) (m m-0)
    (hash hash))
  (precedes ((0 1) (2 3)) ((1 1) (0 0)) ((1 1) (2 1)) ((1 3) (0 2))
    ((2 0) (1 0)) ((2 4) (1 2)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0))
  (uniq-orig nm nb nc)
  (operation nonce-test (added-strand customer 5) nb (1 2)
    (enc "hash" c nc nb nm price (pubk hash)) (enc nc nb (pubk c)))
  (traces
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((send (enc c nc goods-0 (pubk m-0)))
      (recv (enc nc nm m-0 price (pubk c)))
      (send (enc c nc nm acctnum-0 price (pubk b-0)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b-0))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b-0))
          nb))))
  (label 103)
  (parent 102)
  (unrealized (0 0) (2 1) (2 3))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (acctnum price goods acctnum-0 goods-0 text) (nm nb nc data)
    (b m c hash b-0 name))
  (defstrand bank 3 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nm) (nb nb) (b b-0) (c c) (m m)
    (hash hash))
  (precedes ((0 1) (2 3)) ((1 1) (0 0)) ((1 1) (2 1)) ((1 3) (0 2))
    ((2 0) (1 0)) ((2 4) (1 2)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk b-0))
  (uniq-orig nm nb nc)
  (operation nonce-test (contracted (m-0 m)) nm (2 1)
    (enc nc nm m price (pubk c)))
  (traces
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum-0 price (pubk b-0)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b-0))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b-0))
          nb))))
  (label 104)
  (parent 103)
  (unrealized (0 0) (1 0) (2 3))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (acctnum price goods acctnum-0 goods-0 text) (nm nb nc data)
    (b m c hash name))
  (defstrand bank 3 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nm) (nb nb) (b b) (c c) (m m) (hash hash))
  (precedes ((0 1) (2 3)) ((1 1) (0 0)) ((1 1) (2 1)) ((1 3) (0 2))
    ((2 0) (1 0)) ((2 4) (1 2)))
  (non-orig (privk b) (privk m) (privk c) (privk hash))
  (uniq-orig nm nb nc)
  (operation encryption-test (displaced 3 0 bank 2)
    (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b-0)) (2 3))
  (traces
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum-0 price (pubk b)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))))
  (label 105)
  (parent 104)
  (unrealized (0 0) (1 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (acctnum price acctnum-0 goods text) (nm nb nc data)
    (b m c hash name))
  (defstrand bank 3 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods) (price price)
    (nc nc) (nm nm) (nb nb) (b b) (c c) (m m) (hash hash))
  (precedes ((0 1) (2 3)) ((1 1) (0 0)) ((1 1) (2 1)) ((1 3) (0 2))
    ((2 0) (1 0)) ((2 4) (1 2)))
  (non-orig (privk b) (privk m) (privk c) (privk hash))
  (uniq-orig nm nb nc)
  (operation nonce-test (contracted (goods-0 goods)) nc (1 0)
    (enc c nc goods (pubk m)))
  (traces
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum-0 price (pubk b)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))))
  (label 106)
  (parent 105)
  (unrealized (0 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (acctnum price goods acctnum-0 goods-0 price-0 text)
    (nm nb nc nm-0 data) (b m c hash name))
  (defstrand bank 3 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods-0)
    (price price) (nc nc) (nm nm) (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 2 (goods goods-0) (price price-0) (nc nc)
    (nm nm-0) (c c) (m m))
  (precedes ((0 1) (2 3)) ((1 1) (0 0)) ((1 1) (2 1)) ((1 3) (0 2))
    ((2 0) (3 0)) ((2 4) (1 2)) ((3 1) (1 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash))
  (uniq-orig nm nb nc nm-0)
  (operation nonce-test (added-strand merchant 2) nc (1 0)
    (enc c nc goods-0 (pubk m)))
  (traces
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((send (enc c nc goods-0 (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum-0 price (pubk b)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb)))
    ((recv (enc c nc goods-0 (pubk m)))
      (send (enc nc nm-0 m price-0 (pubk c)))))
  (label 107)
  (parent 105)
  (unrealized (0 0) (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (acctnum price acctnum-0 goods text) (nm nb nc data)
    (b m c hash name))
  (defstrand bank 3 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods) (price price)
    (nc nc) (nm nm) (nb nb) (b b) (c c) (m m) (hash hash))
  (precedes ((0 1) (2 3)) ((1 1) (2 1)) ((1 3) (0 2)) ((2 0) (1 0))
    ((2 2) (0 0)) ((2 4) (1 2)))
  (non-orig (privk b) (privk m) (privk c) (privk hash))
  (uniq-orig nm nb nc)
  (operation nonce-test (displaced 3 2 customer 3) nm (0 0)
    (enc nc nm m price (pubk c)))
  (traces
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum-0 price (pubk b)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))))
  (label 108)
  (parent 106)
  (unrealized (0 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (acctnum price acctnum-0 goods price-0 text)
    (nm nb nc nm-0 data) (b m c hash name))
  (defstrand bank 3 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods) (price price)
    (nc nc) (nm nm) (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 2 (goods goods) (price price-0) (nc nc) (nm nm-0)
    (c c) (m m))
  (precedes ((0 1) (2 3)) ((1 1) (0 0)) ((1 1) (2 1)) ((1 3) (0 2))
    ((2 0) (3 0)) ((2 4) (1 2)) ((3 1) (1 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash))
  (uniq-orig nm nb nc nm-0)
  (operation nonce-test (contracted (goods-0 goods)) nc (1 0)
    (enc nc nm-0 m price-0 (pubk c)) (enc c nc goods (pubk m)))
  (traces
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum-0 price (pubk b)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb)))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm-0 m price-0 (pubk c)))))
  (label 109)
  (parent 107)
  (unrealized (0 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (price acctnum goods text) (nm nb nc data) (b m c hash name))
  (defstrand bank 3 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand customer 5 (acctnum acctnum) (goods goods) (price price)
    (nc nc) (nm nm) (nb nb) (b b) (c c) (m m) (hash hash))
  (precedes ((0 1) (2 3)) ((1 1) (2 1)) ((1 3) (0 2)) ((2 0) (1 0))
    ((2 2) (0 0)) ((2 4) (1 2)))
  (non-orig (privk b) (privk m) (privk c) (privk hash))
  (uniq-orig nm nb nc)
  (operation nonce-test (contracted (acctnum-0 acctnum)) nm (0 0)
    (enc nc nm m price (pubk c)) (enc c nc nm acctnum price (pubk b)))
  (traces
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum price (pubk b)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))))
  (label 110)
  (parent 108)
  (unrealized)
  (shape)
  (maps
    ((0)
      ((b b) (m m) (c c) (nm nm) (nb nb) (nc nc) (hash hash)
        (acctnum acctnum) (price price))))
  (origs (nc (2 0)) (nm (1 1)) (nb (0 1))))

(defskeleton sorted_epmo_acctnum
  (vars (acctnum price acctnum-0 goods text) (nm nb nc nb-0 data)
    (b m c hash hash-0 name))
  (defstrand bank 3 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods) (price price)
    (nc nc) (nm nm) (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nm)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (precedes ((0 1) (2 3)) ((1 1) (2 1)) ((1 1) (3 0)) ((1 3) (0 2))
    ((2 0) (1 0)) ((2 2) (0 0)) ((2 4) (1 2)) ((3 1) (0 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk hash-0))
  (uniq-orig nm nb nc)
  (operation nonce-test (added-strand bank 2) nm (0 0)
    (enc nc nm m price (pubk c)) (enc c nc nm acctnum-0 price (pubk b)))
  (traces
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum-0 price (pubk b)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb)))
    ((recv (enc c nc nm acctnum-0 price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nm price (pubk hash-0)) (privk b))
          (enc nc nb-0 (pubk c))))))
  (label 111)
  (parent 108)
  (unrealized (0 0) (3 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (acctnum price acctnum-0 goods price-0 text)
    (nm nb nc nm-0 data) (b m c hash name))
  (defstrand bank 3 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods) (price price)
    (nc nc) (nm nm) (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 2 (goods goods) (price price-0) (nc nc) (nm nm-0)
    (c c) (m m))
  (precedes ((0 1) (2 3)) ((1 1) (2 1)) ((1 3) (0 2)) ((2 0) (3 0))
    ((2 2) (0 0)) ((2 4) (1 2)) ((3 1) (1 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash))
  (uniq-orig nm nb nc nm-0)
  (operation nonce-test (displaced 4 2 customer 3) nm (0 0)
    (enc nc nm m price (pubk c)))
  (traces
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum-0 price (pubk b)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb)))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm-0 m price-0 (pubk c)))))
  (label 112)
  (parent 109)
  (unrealized (0 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (acctnum price acctnum-0 goods text) (nm nb nc nb-0 data)
    (b m c hash hash-0 name))
  (defstrand bank 3 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods) (price price)
    (nc nc) (nm nm) (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nm)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (precedes ((0 1) (2 3)) ((1 1) (2 1)) ((1 3) (0 2)) ((2 0) (1 0))
    ((2 2) (3 0)) ((2 4) (1 2)) ((3 1) (0 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk hash-0))
  (uniq-orig nm nb nc)
  (operation nonce-test (displaced 4 2 customer 3) nm (3 0)
    (enc nc nm m price (pubk c)))
  (traces
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum-0 price (pubk b)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb)))
    ((recv (enc c nc nm acctnum-0 price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nm price (pubk hash-0)) (privk b))
          (enc nc nb-0 (pubk c))))))
  (label 113)
  (parent 111)
  (unrealized (0 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (price acctnum goods price-0 text) (nm nb nc nm-0 data)
    (b m c hash name))
  (defstrand bank 3 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand customer 5 (acctnum acctnum) (goods goods) (price price)
    (nc nc) (nm nm) (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 2 (goods goods) (price price-0) (nc nc) (nm nm-0)
    (c c) (m m))
  (precedes ((0 1) (2 3)) ((1 1) (2 1)) ((1 3) (0 2)) ((2 0) (3 0))
    ((2 2) (0 0)) ((2 4) (1 2)) ((3 1) (1 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash))
  (uniq-orig nm nb nc nm-0)
  (operation nonce-test (contracted (acctnum-0 acctnum)) nm (0 0)
    (enc nc nm m price (pubk c)) (enc c nc nm acctnum price (pubk b)))
  (traces
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum price (pubk b)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb)))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm-0 m price-0 (pubk c)))))
  (label 114)
  (parent 112)
  (seen 110)
  (unrealized)
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (acctnum price acctnum-0 goods price-0 text)
    (nm nb nc nm-0 nb-0 data) (b m c hash hash-0 name))
  (defstrand bank 3 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods) (price price)
    (nc nc) (nm nm) (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 2 (goods goods) (price price-0) (nc nc) (nm nm-0)
    (c c) (m m))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nm)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (precedes ((0 1) (2 3)) ((1 1) (2 1)) ((1 1) (4 0)) ((1 3) (0 2))
    ((2 0) (3 0)) ((2 2) (0 0)) ((2 4) (1 2)) ((3 1) (1 0))
    ((4 1) (0 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk hash-0))
  (uniq-orig nm nb nc nm-0)
  (operation nonce-test (added-strand bank 2) nm (0 0)
    (enc nc nm m price (pubk c)) (enc c nc nm acctnum-0 price (pubk b)))
  (traces
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum-0 price (pubk b)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb)))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm-0 m price-0 (pubk c))))
    ((recv (enc c nc nm acctnum-0 price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nm price (pubk hash-0)) (privk b))
          (enc nc nb-0 (pubk c))))))
  (label 115)
  (parent 112)
  (unrealized (0 0) (4 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (price acctnum goods text) (nm nb nc nb-0 data)
    (b m c hash hash-0 name))
  (defstrand bank 3 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand customer 5 (acctnum acctnum) (goods goods) (price price)
    (nc nc) (nm nm) (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (precedes ((0 1) (2 3)) ((1 1) (2 1)) ((1 3) (0 2)) ((2 0) (1 0))
    ((2 2) (3 0)) ((2 4) (1 2)) ((3 1) (0 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk hash-0))
  (uniq-orig nm nb nc)
  (operation nonce-test (contracted (acctnum-0 acctnum)) nm (0 0)
    (enc "hash" c nc nb-0 nm price (pubk hash-0))
    (enc nc nm m price (pubk c)) (enc c nc nm acctnum price (pubk b)))
  (traces
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum price (pubk b)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb)))
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nm price (pubk hash-0)) (privk b))
          (enc nc nb-0 (pubk c))))))
  (label 116)
  (parent 113)
  (seen 110)
  (unrealized)
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (acctnum price acctnum-0 goods text) (nb nc nb-0 data)
    (b m c hash hash-0 name))
  (defstrand bank 3 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods) (price price)
    (nc nc) (nm nb-0) (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (precedes ((0 1) (2 3)) ((1 1) (2 1)) ((1 3) (0 2)) ((2 0) (1 0))
    ((2 2) (3 0)) ((2 4) (1 2)) ((3 1) (0 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk hash-0))
  (uniq-orig nb nc nb-0)
  (operation nonce-test (displaced 4 3 bank 2) nm (0 0)
    (enc "hash" c nc nb-0 nm price (pubk hash-0))
    (enc nc nm m price (pubk c)) (enc c nc nm acctnum-0 price (pubk b)))
  (traces
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb)))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))))
  (label 117)
  (parent 113)
  (unrealized (0 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (acctnum price acctnum-0 goods price-0 text)
    (nm nb nc nm-0 nb-0 data) (b m c hash hash-0 name))
  (defstrand bank 3 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods) (price price)
    (nc nc) (nm nm) (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 2 (goods goods) (price price-0) (nc nc) (nm nm-0)
    (c c) (m m))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nm)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (precedes ((0 1) (2 3)) ((1 1) (2 1)) ((1 3) (0 2)) ((2 0) (3 0))
    ((2 2) (4 0)) ((2 4) (1 2)) ((3 1) (1 0)) ((4 1) (0 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk hash-0))
  (uniq-orig nm nb nc nm-0)
  (operation nonce-test (displaced 5 2 customer 3) nm (4 0)
    (enc nc nm m price (pubk c)))
  (traces
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum-0 price (pubk b)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb)))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm-0 m price-0 (pubk c))))
    ((recv (enc c nc nm acctnum-0 price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nm price (pubk hash-0)) (privk b))
          (enc nc nb-0 (pubk c))))))
  (label 118)
  (parent 115)
  (unrealized (0 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (price acctnum goods text) (nb nc nb-0 data)
    (b m c hash hash-0 name))
  (defstrand bank 3 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand customer 5 (acctnum acctnum) (goods goods) (price price)
    (nc nc) (nm nb-0) (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (precedes ((0 1) (2 3)) ((1 1) (2 1)) ((1 3) (0 2)) ((2 0) (1 0))
    ((2 2) (3 0)) ((2 4) (1 2)) ((3 1) (0 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk hash-0))
  (uniq-orig nb nc nb-0)
  (operation nonce-test (contracted (acctnum-0 acctnum)) nb-0 (0 0)
    (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
    (enc nc nb-0 (pubk c)) (enc nc nb-0 m price (pubk c))
    (enc c nc nb-0 acctnum price (pubk b)))
  (traces
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb)))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))))
  (label 119)
  (parent 117)
  (seen 110)
  (unrealized)
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (acctnum price acctnum-0 goods text) (nb nc nb-0 nb-1 data)
    (b m c hash hash-0 hash-1 name))
  (defstrand bank 3 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods) (price price)
    (nc nc) (nm nb-0) (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b) (c c) (hash hash-1))
  (precedes ((0 1) (2 3)) ((1 1) (2 1)) ((1 1) (4 0)) ((1 3) (0 2))
    ((2 0) (1 0)) ((2 2) (3 0)) ((2 4) (1 2)) ((3 1) (0 0))
    ((4 1) (0 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk hash-0)
    (privk hash-1))
  (uniq-orig nb nc nb-0)
  (operation nonce-test (added-strand bank 2) nb-0 (0 0)
    (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
    (enc nc nb-0 (pubk c)) (enc nc nb-0 m price (pubk c))
    (enc c nc nb-0 acctnum-0 price (pubk b)))
  (traces
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb)))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-1 (pubk c))))))
  (label 120)
  (parent 117)
  (unrealized (0 0) (4 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (price acctnum goods price-0 text) (nm nb nc nm-0 nb-0 data)
    (b m c hash hash-0 name))
  (defstrand bank 3 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nm)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand customer 5 (acctnum acctnum) (goods goods) (price price)
    (nc nc) (nm nm) (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 2 (goods goods) (price price-0) (nc nc) (nm nm-0)
    (c c) (m m))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nm)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (precedes ((0 1) (2 3)) ((1 1) (2 1)) ((1 3) (0 2)) ((2 0) (3 0))
    ((2 2) (4 0)) ((2 4) (1 2)) ((3 1) (1 0)) ((4 1) (0 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk hash-0))
  (uniq-orig nm nb nc nm-0)
  (operation nonce-test (contracted (acctnum-0 acctnum)) nm (0 0)
    (enc "hash" c nc nb-0 nm price (pubk hash-0))
    (enc nc nm m price (pubk c)) (enc c nc nm acctnum price (pubk b)))
  (traces
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nm (pubk hash)) (privk m))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nm m price (pubk c)))
      (send (enc c nc nm acctnum price (pubk b)))
      (recv
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" c nc nb nm price (pubk hash)) (privk b))
          nb)))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm-0 m price-0 (pubk c))))
    ((recv (enc c nc nm acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nm price (pubk hash-0)) (privk b))
          (enc nc nb-0 (pubk c))))))
  (label 121)
  (parent 118)
  (seen 116)
  (unrealized)
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (acctnum price acctnum-0 goods price-0 text)
    (nb nc nm nb-0 data) (b m c hash hash-0 name))
  (defstrand bank 3 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods) (price price)
    (nc nc) (nm nb-0) (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 2 (goods goods) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (precedes ((0 1) (2 3)) ((1 1) (2 1)) ((1 3) (0 2)) ((2 0) (3 0))
    ((2 2) (4 0)) ((2 4) (1 2)) ((3 1) (1 0)) ((4 1) (0 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk hash-0))
  (uniq-orig nb nc nm nb-0)
  (operation nonce-test (displaced 5 4 bank 2) nm-0 (0 0)
    (enc "hash" c nc nb-0 nm-0 price (pubk hash-0))
    (enc nc nm-0 m price (pubk c))
    (enc c nc nm-0 acctnum-0 price (pubk b)))
  (traces
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb)))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price-0 (pubk c))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))))
  (label 122)
  (parent 118)
  (unrealized (0 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (acctnum price acctnum-0 goods text) (nb nc nb-0 nb-1 data)
    (b m c hash hash-0 hash-1 name))
  (defstrand bank 3 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods) (price price)
    (nc nc) (nm nb-0) (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b) (c c) (hash hash-1))
  (precedes ((0 1) (2 3)) ((1 1) (2 1)) ((1 3) (0 2)) ((2 0) (1 0))
    ((2 2) (3 0)) ((2 2) (4 0)) ((2 4) (1 2)) ((3 1) (0 0))
    ((4 1) (0 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk hash-0)
    (privk hash-1))
  (uniq-orig nb nc nb-0)
  (operation nonce-test (displaced 5 2 customer 3) nb-0 (4 0)
    (enc nc nb-0 m price (pubk c)))
  (traces
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb)))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-1 (pubk c))))))
  (label 123)
  (parent 120)
  (unrealized (0 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (price acctnum goods price-0 text) (nb nc nm nb-0 data)
    (b m c hash hash-0 name))
  (defstrand bank 3 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand customer 5 (acctnum acctnum) (goods goods) (price price)
    (nc nc) (nm nb-0) (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 2 (goods goods) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (precedes ((0 1) (2 3)) ((1 1) (2 1)) ((1 3) (0 2)) ((2 0) (3 0))
    ((2 2) (4 0)) ((2 4) (1 2)) ((3 1) (1 0)) ((4 1) (0 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk hash-0))
  (uniq-orig nb nc nm nb-0)
  (operation nonce-test (contracted (acctnum-0 acctnum)) nb-0 (0 0)
    (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
    (enc nc nb-0 (pubk c)) (enc nc nb-0 m price (pubk c))
    (enc c nc nb-0 acctnum price (pubk b)))
  (traces
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb)))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price-0 (pubk c))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c))))))
  (label 124)
  (parent 122)
  (seen 119)
  (unrealized)
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (acctnum price acctnum-0 goods price-0 text)
    (nb nc nm nb-0 nb-1 data) (b m c hash hash-0 hash-1 name))
  (defstrand bank 3 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods) (price price)
    (nc nc) (nm nb-0) (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 2 (goods goods) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b) (c c) (hash hash-1))
  (precedes ((0 1) (2 3)) ((1 1) (2 1)) ((1 1) (5 0)) ((1 3) (0 2))
    ((2 0) (3 0)) ((2 2) (4 0)) ((2 4) (1 2)) ((3 1) (1 0))
    ((4 1) (0 0)) ((5 1) (0 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk hash-0)
    (privk hash-1))
  (uniq-orig nb nc nm nb-0)
  (operation nonce-test (added-strand bank 2) nb-0 (0 0)
    (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
    (enc nc nb-0 (pubk c)) (enc nc nb-0 m price (pubk c))
    (enc c nc nb-0 acctnum-0 price (pubk b)))
  (traces
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb)))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price-0 (pubk c))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-1 (pubk c))))))
  (label 125)
  (parent 122)
  (unrealized (0 0) (5 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (price acctnum goods text) (nb nc nb-0 nb-1 data)
    (b m c hash hash-0 hash-1 name))
  (defstrand bank 3 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand customer 5 (acctnum acctnum) (goods goods) (price price)
    (nc nc) (nm nb-0) (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b) (c c) (hash hash-1))
  (precedes ((0 1) (2 3)) ((1 1) (2 1)) ((1 3) (0 2)) ((2 0) (1 0))
    ((2 2) (3 0)) ((2 2) (4 0)) ((2 4) (1 2)) ((3 1) (0 0))
    ((4 1) (0 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk hash-0)
    (privk hash-1))
  (uniq-orig nb nc nb-0)
  (operation nonce-test (contracted (acctnum-0 acctnum)) nb-0 (0 0)
    (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
    (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
    (enc nc nb-0 (pubk c)) (enc nc nb-0 m price (pubk c))
    (enc c nc nb-0 acctnum price (pubk b)))
  (traces
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb)))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-1 (pubk c))))))
  (label 126)
  (parent 123)
  (seen 116)
  (unrealized)
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (acctnum price acctnum-0 goods price-0 text)
    (nb nc nm nb-0 nb-1 data) (b m c hash hash-0 hash-1 name))
  (defstrand bank 3 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand customer 5 (acctnum acctnum-0) (goods goods) (price price)
    (nc nc) (nm nb-0) (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 2 (goods goods) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum-0) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b) (c c) (hash hash-1))
  (precedes ((0 1) (2 3)) ((1 1) (2 1)) ((1 3) (0 2)) ((2 0) (3 0))
    ((2 2) (4 0)) ((2 2) (5 0)) ((2 4) (1 2)) ((3 1) (1 0))
    ((4 1) (0 0)) ((5 1) (0 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk hash-0)
    (privk hash-1))
  (uniq-orig nb nc nm nb-0)
  (operation nonce-test (displaced 6 2 customer 3) nb-0 (5 0)
    (enc nc nb-0 m price (pubk c)))
  (traces
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum-0 price (pubk b)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb)))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price-0 (pubk c))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum-0 price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-1 (pubk c))))))
  (label 127)
  (parent 125)
  (unrealized (0 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton sorted_epmo_acctnum
  (vars (price acctnum goods price-0 text) (nb nc nm nb-0 nb-1 data)
    (b m c hash hash-0 hash-1 name))
  (defstrand bank 3 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 4 (goods goods) (price price) (nc nc) (nm nb-0)
    (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand customer 5 (acctnum acctnum) (goods goods) (price price)
    (nc nc) (nm nb-0) (nb nb) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 2 (goods goods) (price price-0) (nc nc) (nm nm)
    (c c) (m m))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-0) (b b) (c c) (hash hash-0))
  (defstrand bank 2 (acctnum acctnum) (price price) (nc nc) (nm nb-0)
    (nb nb-1) (b b) (c c) (hash hash-1))
  (precedes ((0 1) (2 3)) ((1 1) (2 1)) ((1 3) (0 2)) ((2 0) (3 0))
    ((2 2) (4 0)) ((2 2) (5 0)) ((2 4) (1 2)) ((3 1) (1 0))
    ((4 1) (0 0)) ((5 1) (0 0)))
  (non-orig (privk b) (privk m) (privk c) (privk hash) (privk hash-0)
    (privk hash-1))
  (uniq-orig nb nc nm nb-0)
  (operation nonce-test (contracted (acctnum-0 acctnum)) nb-0 (0 0)
    (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
    (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
    (enc nc nb-0 (pubk c)) (enc nc nb-0 m price (pubk c))
    (enc c nc nb-0 acctnum price (pubk b)))
  (traces
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nb-0 m price (pubk c)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb))
      (send (enc (enc "hash" b m nb nb-0 (pubk hash)) (privk m))))
    ((send (enc c nc goods (pubk m)))
      (recv (enc nc nb-0 m price (pubk c)))
      (send (enc c nc nb-0 acctnum price (pubk b)))
      (recv
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" c nc nb nb-0 price (pubk hash)) (privk b))
          nb)))
    ((recv (enc c nc goods (pubk m)))
      (send (enc nc nm m price-0 (pubk c))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-0 nb-0 price (pubk hash-0))
            (privk b)) (enc nc nb-0 (pubk c)))))
    ((recv (enc c nc nb-0 acctnum price (pubk b)))
      (send
        (cat
          (enc (enc "hash" c nc nb-1 nb-0 price (pubk hash-1))
            (privk b)) (enc nc nb-1 (pubk c))))))
  (label 128)
  (parent 127)
  (seen 126)
  (unrealized)
  (comment "1 in cohort - 0 not yet seen"))

(comment "Nothing left to do")
