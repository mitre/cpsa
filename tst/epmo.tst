(herald "Electronic Purchase with Money Order Protocol"
  (comment "Annotated with trust management formulas"))

(comment "CPSA 2.3.1")
(comment "All input read from epmo.scm")

(defprotocol epmo basic
  (defrole bank
    (vars (b c m name) (hash akey) (nc nm nb data) (price text))
    (trace (recv (enc c nc nm price (pubk b)))
      (send
        (cat (enc (enc c nc nb nm price hash) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc b nb nm hash) (privk m))))
    (non-orig (invk hash))
    (uniq-orig nb)
    (annotations b
      (1
        (implies
          (and (forall ((pm name)) (says c (transfer b price pm nm)))
            (forall ((pm name)) (says pm (transfer b price pm nm))))
          (forall ((pm name)) (transfer b price pm nm))))
      (2
        (and (says c (transfer b price m nm))
          (says m (transfer b price m nm))))))
  (defrole customer
    (vars (b c m name) (hash akey) (nb nc nm data) (goods price text))
    (trace (send (enc c nc goods price (pubk m)))
      (recv (enc nc nm m goods price (pubk c)))
      (send (enc c nc nm price (pubk b)))
      (recv
        (cat (enc (enc c nc nb nm price hash) (privk b))
          (enc nc nb (pubk c))))
      (send (cat (enc (enc c nc nb nm price hash) (privk b)) nb)))
    (non-orig (invk hash))
    (uniq-orig nc)
    (annotations c
      (1
        (says m
          (forall ((pb name))
            (implies (transfer pb price m nm) (ship m goods c)))))
      (3
        (says b
          (implies
            (and (forall ((pm name)) (says c (transfer b price pm nm)))
              (forall ((pm name)) (says m (transfer b price pm nm))))
            (transfer b price m nm)))) (4 (transfer b price m nm))))
  (defrole merchant
    (vars (b c m name) (hash akey) (nb nc nm data) (goods price text))
    (trace (recv (enc c nc goods price (pubk m)))
      (send (enc nc nm m goods price (pubk c)))
      (recv (cat (enc (enc c nc nb nm price hash) (privk b)) nb))
      (send (enc (enc b nb nm hash) (privk m))))
    (non-orig (invk hash))
    (uniq-orig nm)
    (annotations m
      (1
        (forall ((pb name))
          (implies (transfer pb price m nm) (ship m goods c))))
      (2
        (and
          (says b
            (implies
              (and
                (forall ((pm name)) (says c (transfer b price pm nm)))
                (forall ((pm name)) (says m (transfer b price pm nm))))
              (transfer b price m nm)))
          (says c (transfer b price m nm))))
      (3 (and (transfer b price m nm) (ship m goods c))))))

(defskeleton epmo
  (vars (goods price text) (nb nc nm data) (b c m name) (hash akey))
  (defstrand customer 5 (goods goods) (price price) (nb nb) (nc nc)
    (nm nm) (b b) (c c) (m m) (hash hash))
  (non-orig (invk hash) (privk b) (privk c) (privk m))
  (uniq-orig nc)
  (traces
    ((send (enc c nc goods price (pubk m)))
      (recv (enc nc nm m goods price (pubk c)))
      (send (enc c nc nm price (pubk b)))
      (recv
        (cat (enc (enc c nc nb nm price hash) (privk b))
          (enc nc nb (pubk c))))
      (send (cat (enc (enc c nc nb nm price hash) (privk b)) nb))))
  (label 0)
  (unrealized (0 1) (0 3))
  (origs (nc (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo
  (vars (goods price text) (nb nc nm nm-0 data) (b c m name)
    (hash akey))
  (defstrand customer 5 (goods goods) (price price) (nb nb) (nc nc)
    (nm nm) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 2 (goods goods) (price price) (nc nc) (nm nm-0)
    (c c) (m m))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (invk hash) (privk b) (privk c) (privk m))
  (uniq-orig nc nm-0)
  (operation nonce-test (added-strand merchant 2) nc (0 1)
    (enc c nc goods price (pubk m)))
  (traces
    ((send (enc c nc goods price (pubk m)))
      (recv (enc nc nm m goods price (pubk c)))
      (send (enc c nc nm price (pubk b)))
      (recv
        (cat (enc (enc c nc nb nm price hash) (privk b))
          (enc nc nb (pubk c))))
      (send (cat (enc (enc c nc nb nm price hash) (privk b)) nb)))
    ((recv (enc c nc goods price (pubk m)))
      (send (enc nc nm-0 m goods price (pubk c)))))
  (label 1)
  (parent 0)
  (unrealized (0 1) (0 3))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo
  (vars (goods price text) (nb nc nm data) (b c m name) (hash akey))
  (defstrand customer 5 (goods goods) (price price) (nb nb) (nc nc)
    (nm nm) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 2 (goods goods) (price price) (nc nc) (nm nm)
    (c c) (m m))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (invk hash) (privk b) (privk c) (privk m))
  (uniq-orig nc nm)
  (operation nonce-test (contracted (nm-0 nm)) nc (0 1)
    (enc nc nm m goods price (pubk c)) (enc c nc goods price (pubk m)))
  (traces
    ((send (enc c nc goods price (pubk m)))
      (recv (enc nc nm m goods price (pubk c)))
      (send (enc c nc nm price (pubk b)))
      (recv
        (cat (enc (enc c nc nb nm price hash) (privk b))
          (enc nc nb (pubk c))))
      (send (cat (enc (enc c nc nb nm price hash) (privk b)) nb)))
    ((recv (enc c nc goods price (pubk m)))
      (send (enc nc nm m goods price (pubk c)))))
  (label 2)
  (parent 1)
  (unrealized (0 3))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo
  (vars (goods price text) (nb nc nm data) (b c m name) (hash akey))
  (defstrand customer 5 (goods goods) (price price) (nb nb) (nc nc)
    (nm nm) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 2 (goods goods) (price price) (nc nc) (nm nm)
    (c c) (m m))
  (defstrand bank 2 (price price) (nc nc) (nm nm) (nb nb) (b b) (c c)
    (hash hash))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)) ((1 1) (2 0)) ((2 1) (0 3)))
  (non-orig (invk hash) (privk b) (privk c) (privk m))
  (uniq-orig nb nc nm)
  (operation encryption-test (added-strand bank 2)
    (enc (enc c nc nb nm price hash) (privk b)) (0 3))
  (traces
    ((send (enc c nc goods price (pubk m)))
      (recv (enc nc nm m goods price (pubk c)))
      (send (enc c nc nm price (pubk b)))
      (recv
        (cat (enc (enc c nc nb nm price hash) (privk b))
          (enc nc nb (pubk c))))
      (send (cat (enc (enc c nc nb nm price hash) (privk b)) nb)))
    ((recv (enc c nc goods price (pubk m)))
      (send (enc nc nm m goods price (pubk c))))
    ((recv (enc c nc nm price (pubk b)))
      (send
        (cat (enc (enc c nc nb nm price hash) (privk b))
          (enc nc nb (pubk c))))))
  (label 3)
  (parent 2)
  (unrealized (2 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo
  (vars (goods price text) (nb nc nm data) (b c m name) (hash akey))
  (defstrand customer 5 (goods goods) (price price) (nb nb) (nc nc)
    (nm nm) (b b) (c c) (m m) (hash hash))
  (defstrand merchant 2 (goods goods) (price price) (nc nc) (nm nm)
    (c c) (m m))
  (defstrand bank 2 (price price) (nc nc) (nm nm) (nb nb) (b b) (c c)
    (hash hash))
  (precedes ((0 0) (1 0)) ((0 2) (2 0)) ((1 1) (0 1)) ((2 1) (0 3)))
  (non-orig (invk hash) (privk b) (privk c) (privk m))
  (uniq-orig nb nc nm)
  (operation nonce-test (displaced 3 0 customer 3) nc (2 0)
    (enc nc nm m goods price (pubk c)) (enc c nc goods price (pubk m)))
  (traces
    ((send (enc c nc goods price (pubk m)))
      (recv (enc nc nm m goods price (pubk c)))
      (send (enc c nc nm price (pubk b)))
      (recv
        (cat (enc (enc c nc nb nm price hash) (privk b))
          (enc nc nb (pubk c))))
      (send (cat (enc (enc c nc nb nm price hash) (privk b)) nb)))
    ((recv (enc c nc goods price (pubk m)))
      (send (enc nc nm m goods price (pubk c))))
    ((recv (enc c nc nm price (pubk b)))
      (send
        (cat (enc (enc c nc nb nm price hash) (privk b))
          (enc nc nb (pubk c))))))
  (label 4)
  (parent 3)
  (unrealized)
  (shape)
  (maps
    ((0)
      ((b b) (c c) (m m) (hash hash) (nb nb) (nc nc) (nm nm)
        (goods goods) (price price))))
  (origs (nc (0 0)) (nb (2 1)) (nm (1 1))))

(comment "Nothing left to do")

(defprotocol epmo basic
  (defrole bank
    (vars (b c m name) (hash akey) (nc nm nb data) (price text))
    (trace (recv (enc c nc nm price (pubk b)))
      (send
        (cat (enc (enc c nc nb nm price hash) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc b nb nm hash) (privk m))))
    (non-orig (invk hash))
    (uniq-orig nb)
    (annotations b
      (1
        (implies
          (and (forall ((pm name)) (says c (transfer b price pm nm)))
            (forall ((pm name)) (says pm (transfer b price pm nm))))
          (forall ((pm name)) (transfer b price pm nm))))
      (2
        (and (says c (transfer b price m nm))
          (says m (transfer b price m nm))))))
  (defrole customer
    (vars (b c m name) (hash akey) (nb nc nm data) (goods price text))
    (trace (send (enc c nc goods price (pubk m)))
      (recv (enc nc nm m goods price (pubk c)))
      (send (enc c nc nm price (pubk b)))
      (recv
        (cat (enc (enc c nc nb nm price hash) (privk b))
          (enc nc nb (pubk c))))
      (send (cat (enc (enc c nc nb nm price hash) (privk b)) nb)))
    (non-orig (invk hash))
    (uniq-orig nc)
    (annotations c
      (1
        (says m
          (forall ((pb name))
            (implies (transfer pb price m nm) (ship m goods c)))))
      (3
        (says b
          (implies
            (and (forall ((pm name)) (says c (transfer b price pm nm)))
              (forall ((pm name)) (says m (transfer b price pm nm))))
            (transfer b price m nm)))) (4 (transfer b price m nm))))
  (defrole merchant
    (vars (b c m name) (hash akey) (nb nc nm data) (goods price text))
    (trace (recv (enc c nc goods price (pubk m)))
      (send (enc nc nm m goods price (pubk c)))
      (recv (cat (enc (enc c nc nb nm price hash) (privk b)) nb))
      (send (enc (enc b nb nm hash) (privk m))))
    (non-orig (invk hash))
    (uniq-orig nm)
    (annotations m
      (1
        (forall ((pb name))
          (implies (transfer pb price m nm) (ship m goods c))))
      (2
        (and
          (says b
            (implies
              (and
                (forall ((pm name)) (says c (transfer b price pm nm)))
                (forall ((pm name)) (says m (transfer b price pm nm))))
              (transfer b price m nm)))
          (says c (transfer b price m nm))))
      (3 (and (transfer b price m nm) (ship m goods c))))))

(defskeleton epmo
  (vars (price text) (nc nm nb data) (b c m name) (hash akey))
  (defstrand bank 3 (price price) (nc nc) (nm nm) (nb nb) (b b) (c c)
    (m m) (hash hash))
  (non-orig (invk hash) (privk b) (privk c) (privk m))
  (uniq-orig nb)
  (traces
    ((recv (enc c nc nm price (pubk b)))
      (send
        (cat (enc (enc c nc nb nm price hash) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc b nb nm hash) (privk m)))))
  (label 5)
  (unrealized (0 2))
  (origs (nb (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo
  (vars (price goods price-0 text) (nc nm nb nc-0 data) (b c m c-0 name)
    (hash akey))
  (defstrand bank 3 (price price) (nc nc) (nm nm) (nb nb) (b b) (c c)
    (m m) (hash hash))
  (defstrand merchant 4 (goods goods) (price price-0) (nb nb) (nc nc-0)
    (nm nm) (b b) (c c-0) (m m) (hash hash))
  (precedes ((0 1) (1 2)) ((1 1) (0 0)) ((1 3) (0 2)))
  (non-orig (invk hash) (privk b) (privk c) (privk m))
  (uniq-orig nm nb)
  (operation encryption-test (added-strand merchant 4)
    (enc (enc b nb nm hash) (privk m)) (0 2))
  (traces
    ((recv (enc c nc nm price (pubk b)))
      (send
        (cat (enc (enc c nc nb nm price hash) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc b nb nm hash) (privk m))))
    ((recv (enc c-0 nc-0 goods price-0 (pubk m)))
      (send (enc nc-0 nm m goods price-0 (pubk c-0)))
      (recv (cat (enc (enc c-0 nc-0 nb nm price-0 hash) (privk b)) nb))
      (send (enc (enc b nb nm hash) (privk m)))))
  (label 6)
  (parent 5)
  (unrealized (1 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo
  (vars (price goods text) (nc nm nb data) (b c m name) (hash akey))
  (defstrand bank 3 (price price) (nc nc) (nm nm) (nb nb) (b b) (c c)
    (m m) (hash hash))
  (defstrand merchant 4 (goods goods) (price price) (nb nb) (nc nc)
    (nm nm) (b b) (c c) (m m) (hash hash))
  (precedes ((0 1) (1 2)) ((1 1) (0 0)) ((1 3) (0 2)))
  (non-orig (invk hash) (privk b) (privk c) (privk m))
  (uniq-orig nm nb)
  (operation encryption-test (displaced 2 0 bank 2)
    (enc (enc c-0 nc-0 nb nm price-0 hash) (privk b)) (1 2))
  (traces
    ((recv (enc c nc nm price (pubk b)))
      (send
        (cat (enc (enc c nc nb nm price hash) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc b nb nm hash) (privk m))))
    ((recv (enc c nc goods price (pubk m)))
      (send (enc nc nm m goods price (pubk c)))
      (recv (cat (enc (enc c nc nb nm price hash) (privk b)) nb))
      (send (enc (enc b nb nm hash) (privk m)))))
  (label 7)
  (parent 6)
  (unrealized (0 0) (1 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo
  (vars (price goods goods-0 text) (nc nm nb data) (b c m b-0 m-0 name)
    (hash akey))
  (defstrand bank 3 (price price) (nc nc) (nm nm) (nb nb) (b b) (c c)
    (m m) (hash hash))
  (defstrand merchant 4 (goods goods) (price price) (nb nb) (nc nc)
    (nm nm) (b b) (c c) (m m) (hash hash))
  (defstrand customer 5 (goods goods-0) (price price) (nb nb) (nc nc)
    (nm nm) (b b-0) (c c) (m m-0) (hash hash))
  (precedes ((0 1) (2 3)) ((1 1) (0 0)) ((1 1) (2 1)) ((1 3) (0 2))
    ((2 0) (1 0)) ((2 4) (1 2)))
  (non-orig (invk hash) (privk b) (privk c) (privk m))
  (uniq-orig nc nm nb)
  (operation nonce-test (added-strand customer 5) nb (1 2)
    (enc nc nb (pubk c)) (enc c nc nb nm price hash))
  (traces
    ((recv (enc c nc nm price (pubk b)))
      (send
        (cat (enc (enc c nc nb nm price hash) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc b nb nm hash) (privk m))))
    ((recv (enc c nc goods price (pubk m)))
      (send (enc nc nm m goods price (pubk c)))
      (recv (cat (enc (enc c nc nb nm price hash) (privk b)) nb))
      (send (enc (enc b nb nm hash) (privk m))))
    ((send (enc c nc goods-0 price (pubk m-0)))
      (recv (enc nc nm m-0 goods-0 price (pubk c)))
      (send (enc c nc nm price (pubk b-0)))
      (recv
        (cat (enc (enc c nc nb nm price hash) (privk b-0))
          (enc nc nb (pubk c))))
      (send (cat (enc (enc c nc nb nm price hash) (privk b-0)) nb))))
  (label 8)
  (parent 7)
  (unrealized (0 0) (2 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo
  (vars (price goods text) (nc nm nb data) (b c m b-0 name) (hash akey))
  (defstrand bank 3 (price price) (nc nc) (nm nm) (nb nb) (b b) (c c)
    (m m) (hash hash))
  (defstrand merchant 4 (goods goods) (price price) (nb nb) (nc nc)
    (nm nm) (b b) (c c) (m m) (hash hash))
  (defstrand customer 5 (goods goods) (price price) (nb nb) (nc nc)
    (nm nm) (b b-0) (c c) (m m) (hash hash))
  (precedes ((0 1) (2 3)) ((1 1) (0 0)) ((1 1) (2 1)) ((1 3) (0 2))
    ((2 0) (1 0)) ((2 4) (1 2)))
  (non-orig (invk hash) (privk b) (privk c) (privk m))
  (uniq-orig nc nm nb)
  (operation nonce-test (contracted (m-0 m) (goods-0 goods)) nm (2 1)
    (enc nc nm m goods price (pubk c)))
  (traces
    ((recv (enc c nc nm price (pubk b)))
      (send
        (cat (enc (enc c nc nb nm price hash) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc b nb nm hash) (privk m))))
    ((recv (enc c nc goods price (pubk m)))
      (send (enc nc nm m goods price (pubk c)))
      (recv (cat (enc (enc c nc nb nm price hash) (privk b)) nb))
      (send (enc (enc b nb nm hash) (privk m))))
    ((send (enc c nc goods price (pubk m)))
      (recv (enc nc nm m goods price (pubk c)))
      (send (enc c nc nm price (pubk b-0)))
      (recv
        (cat (enc (enc c nc nb nm price hash) (privk b-0))
          (enc nc nb (pubk c))))
      (send (cat (enc (enc c nc nb nm price hash) (privk b-0)) nb))))
  (label 9)
  (parent 8)
  (unrealized (0 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo
  (vars (price goods text) (nc nm nb data) (b c m b-0 name) (hash akey))
  (defstrand bank 3 (price price) (nc nc) (nm nm) (nb nb) (b b) (c c)
    (m m) (hash hash))
  (defstrand merchant 4 (goods goods) (price price) (nb nb) (nc nc)
    (nm nm) (b b) (c c) (m m) (hash hash))
  (defstrand customer 5 (goods goods) (price price) (nb nb) (nc nc)
    (nm nm) (b b-0) (c c) (m m) (hash hash))
  (precedes ((0 1) (2 3)) ((1 1) (2 1)) ((1 3) (0 2)) ((2 0) (1 0))
    ((2 2) (0 0)) ((2 4) (1 2)))
  (non-orig (invk hash) (privk b) (privk c) (privk m))
  (uniq-orig nc nm nb)
  (operation nonce-test (displaced 3 2 customer 3) nm (0 0)
    (enc nc nm m goods price (pubk c)))
  (traces
    ((recv (enc c nc nm price (pubk b)))
      (send
        (cat (enc (enc c nc nb nm price hash) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc b nb nm hash) (privk m))))
    ((recv (enc c nc goods price (pubk m)))
      (send (enc nc nm m goods price (pubk c)))
      (recv (cat (enc (enc c nc nb nm price hash) (privk b)) nb))
      (send (enc (enc b nb nm hash) (privk m))))
    ((send (enc c nc goods price (pubk m)))
      (recv (enc nc nm m goods price (pubk c)))
      (send (enc c nc nm price (pubk b-0)))
      (recv
        (cat (enc (enc c nc nb nm price hash) (privk b-0))
          (enc nc nb (pubk c))))
      (send (cat (enc (enc c nc nb nm price hash) (privk b-0)) nb))))
  (label 10)
  (parent 9)
  (unrealized)
  (shape)
  (maps
    ((0)
      ((b b) (c c) (m m) (hash hash) (nc nc) (nm nm) (nb nb)
        (price price))))
  (origs (nc (2 0)) (nb (0 1)) (nm (1 1))))

(comment "Nothing left to do")

(defprotocol epmo basic
  (defrole bank
    (vars (b c m name) (hash akey) (nc nm nb data) (price text))
    (trace (recv (enc c nc nm price (pubk b)))
      (send
        (cat (enc (enc c nc nb nm price hash) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc b nb nm hash) (privk m))))
    (non-orig (invk hash))
    (uniq-orig nb)
    (annotations b
      (1
        (implies
          (and (forall ((pm name)) (says c (transfer b price pm nm)))
            (forall ((pm name)) (says pm (transfer b price pm nm))))
          (forall ((pm name)) (transfer b price pm nm))))
      (2
        (and (says c (transfer b price m nm))
          (says m (transfer b price m nm))))))
  (defrole customer
    (vars (b c m name) (hash akey) (nb nc nm data) (goods price text))
    (trace (send (enc c nc goods price (pubk m)))
      (recv (enc nc nm m goods price (pubk c)))
      (send (enc c nc nm price (pubk b)))
      (recv
        (cat (enc (enc c nc nb nm price hash) (privk b))
          (enc nc nb (pubk c))))
      (send (cat (enc (enc c nc nb nm price hash) (privk b)) nb)))
    (non-orig (invk hash))
    (uniq-orig nc)
    (annotations c
      (1
        (says m
          (forall ((pb name))
            (implies (transfer pb price m nm) (ship m goods c)))))
      (3
        (says b
          (implies
            (and (forall ((pm name)) (says c (transfer b price pm nm)))
              (forall ((pm name)) (says m (transfer b price pm nm))))
            (transfer b price m nm)))) (4 (transfer b price m nm))))
  (defrole merchant
    (vars (b c m name) (hash akey) (nb nc nm data) (goods price text))
    (trace (recv (enc c nc goods price (pubk m)))
      (send (enc nc nm m goods price (pubk c)))
      (recv (cat (enc (enc c nc nb nm price hash) (privk b)) nb))
      (send (enc (enc b nb nm hash) (privk m))))
    (non-orig (invk hash))
    (uniq-orig nm)
    (annotations m
      (1
        (forall ((pb name))
          (implies (transfer pb price m nm) (ship m goods c))))
      (2
        (and
          (says b
            (implies
              (and
                (forall ((pm name)) (says c (transfer b price pm nm)))
                (forall ((pm name)) (says m (transfer b price pm nm))))
              (transfer b price m nm)))
          (says c (transfer b price m nm))))
      (3 (and (transfer b price m nm) (ship m goods c))))))

(defskeleton epmo
  (vars (goods price text) (nb nc nm data) (b c m name) (hash akey))
  (defstrand merchant 4 (goods goods) (price price) (nb nb) (nc nc)
    (nm nm) (b b) (c c) (m m) (hash hash))
  (non-orig (invk hash) (privk b) (privk c) (privk m))
  (uniq-orig nm)
  (traces
    ((recv (enc c nc goods price (pubk m)))
      (send (enc nc nm m goods price (pubk c)))
      (recv (cat (enc (enc c nc nb nm price hash) (privk b)) nb))
      (send (enc (enc b nb nm hash) (privk m)))))
  (label 11)
  (unrealized (0 2))
  (origs (nm (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo
  (vars (goods price text) (nb nc nm data) (b c m name) (hash akey))
  (defstrand merchant 4 (goods goods) (price price) (nb nb) (nc nc)
    (nm nm) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (price price) (nc nc) (nm nm) (nb nb) (b b) (c c)
    (hash hash))
  (precedes ((0 1) (1 0)) ((1 1) (0 2)))
  (non-orig (invk hash) (privk b) (privk c) (privk m))
  (uniq-orig nb nm)
  (operation encryption-test (added-strand bank 2)
    (enc (enc c nc nb nm price hash) (privk b)) (0 2))
  (traces
    ((recv (enc c nc goods price (pubk m)))
      (send (enc nc nm m goods price (pubk c)))
      (recv (cat (enc (enc c nc nb nm price hash) (privk b)) nb))
      (send (enc (enc b nb nm hash) (privk m))))
    ((recv (enc c nc nm price (pubk b)))
      (send
        (cat (enc (enc c nc nb nm price hash) (privk b))
          (enc nc nb (pubk c))))))
  (label 12)
  (parent 11)
  (unrealized (0 2) (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo
  (vars (goods price text) (nb nc nm data) (b c m b-0 name) (hash akey))
  (defstrand merchant 4 (goods goods) (price price) (nb nb) (nc nc)
    (nm nm) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (price price) (nc nc) (nm nm) (nb nb) (b b) (c c)
    (hash hash))
  (defstrand customer 3 (goods goods) (price price) (nc nc) (nm nm)
    (b b-0) (c c) (m m))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (0 0)) ((2 2) (1 0)))
  (non-orig (invk hash) (privk b) (privk c) (privk m))
  (uniq-orig nb nc nm)
  (operation nonce-test (added-strand customer 3) nm (1 0)
    (enc nc nm m goods price (pubk c)))
  (traces
    ((recv (enc c nc goods price (pubk m)))
      (send (enc nc nm m goods price (pubk c)))
      (recv (cat (enc (enc c nc nb nm price hash) (privk b)) nb))
      (send (enc (enc b nb nm hash) (privk m))))
    ((recv (enc c nc nm price (pubk b)))
      (send
        (cat (enc (enc c nc nb nm price hash) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods price (pubk m)))
      (recv (enc nc nm m goods price (pubk c)))
      (send (enc c nc nm price (pubk b-0)))))
  (label 13)
  (parent 12)
  (unrealized (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo
  (vars (price goods text) (nb nc nm data) (b c b-0 m name) (hash akey))
  (defstrand merchant 4 (goods goods) (price price) (nb nb) (nc nc)
    (nm nm) (b b) (c c) (m m) (hash hash))
  (defstrand bank 2 (price price) (nc nc) (nm nm) (nb nb) (b b) (c c)
    (hash hash))
  (defstrand customer 5 (goods goods) (price price) (nb nb) (nc nc)
    (nm nm) (b b-0) (c c) (m m) (hash hash))
  (precedes ((0 1) (2 1)) ((1 1) (2 3)) ((2 0) (0 0)) ((2 2) (1 0))
    ((2 4) (0 2)))
  (non-orig (invk hash) (privk b) (privk c) (privk m))
  (uniq-orig nb nc nm)
  (operation nonce-test (displaced 2 3 customer 5) nb (0 2)
    (enc nc nb (pubk c)) (enc c nc nb nm price hash))
  (traces
    ((recv (enc c nc goods price (pubk m)))
      (send (enc nc nm m goods price (pubk c)))
      (recv (cat (enc (enc c nc nb nm price hash) (privk b)) nb))
      (send (enc (enc b nb nm hash) (privk m))))
    ((recv (enc c nc nm price (pubk b)))
      (send
        (cat (enc (enc c nc nb nm price hash) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods price (pubk m)))
      (recv (enc nc nm m goods price (pubk c)))
      (send (enc c nc nm price (pubk b-0)))
      (recv
        (cat (enc (enc c nc nb nm price hash) (privk b-0))
          (enc nc nb (pubk c))))
      (send (cat (enc (enc c nc nb nm price hash) (privk b-0)) nb))))
  (label 14)
  (parent 13)
  (unrealized)
  (shape)
  (maps
    ((0)
      ((b b) (c c) (m m) (hash hash) (nb nb) (nc nc) (nm nm)
        (goods goods) (price price))))
  (origs (nc (2 0)) (nb (1 1)) (nm (0 1))))

(comment "Nothing left to do")
