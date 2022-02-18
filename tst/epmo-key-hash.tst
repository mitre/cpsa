(herald "Electronic Purchase with Money Order Protocol with Key Hashing"
  (comment "Annotated with trust management formulas"))

(comment "CPSA 4.3.0")
(comment "All input read from tst/epmo-key-hash.scm")

(defprotocol epmo basic
  (defrole bank
    (vars (b c m name) (nc nm nb data) (price text))
    (trace (recv (enc c nc nm price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" (cat b nb nm)) (privk m))))
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
    (vars (b c m name) (nb nc nm data) (goods price text))
    (trace (send (enc c nc goods price (pubk m)))
      (recv (enc nc nm m goods price (pubk c)))
      (send (enc c nc nm price (pubk b)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb)))
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
    (vars (b c m name) (nb nc nm data) (goods price text))
    (trace (recv (enc c nc goods price (pubk m)))
      (send (enc nc nm m goods price (pubk c)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))
      (send (enc (enc "hash" (cat b nb nm)) (privk m))))
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
      (3 (and (transfer b price m nm) (ship m goods c)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defgenrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2)) (false))))
  (defgenrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defgenrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1)))))
  (defgenrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2))))))

(defskeleton epmo
  (vars (nb nc nm data) (goods price text) (b c m name))
  (defstrand customer 5 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b) (c c) (m m))
  (non-orig (privk b) (privk c) (privk m))
  (uniq-orig nc)
  (traces
    ((send (enc c nc goods price (pubk m)))
      (recv (enc nc nm m goods price (pubk c)))
      (send (enc c nc nm price (pubk b)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))))
  (label 0)
  (unrealized (0 1) (0 3))
  (origs (nc (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo
  (vars (nb nc nm nm-0 data) (goods price text) (b c m name))
  (defstrand customer 5 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b) (c c) (m m))
  (defstrand merchant 2 (nc nc) (nm nm-0) (goods goods) (price price)
    (c c) (m m))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk b) (privk c) (privk m))
  (uniq-orig nc nm-0)
  (operation nonce-test (added-strand merchant 2) nc (0 1)
    (enc c nc goods price (pubk m)))
  (traces
    ((send (enc c nc goods price (pubk m)))
      (recv (enc nc nm m goods price (pubk c)))
      (send (enc c nc nm price (pubk b)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb)))
    ((recv (enc c nc goods price (pubk m)))
      (send (enc nc nm-0 m goods price (pubk c)))))
  (label 1)
  (parent 0)
  (unrealized (0 1) (0 3))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo
  (vars (nb nc nm data) (goods price text) (b c m name))
  (defstrand customer 5 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b) (c c) (m m))
  (defstrand merchant 2 (nc nc) (nm nm) (goods goods) (price price)
    (c c) (m m))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk b) (privk c) (privk m))
  (uniq-orig nc nm)
  (operation nonce-test (contracted (nm-0 nm)) nc (0 1)
    (enc nc nm m goods price (pubk c)) (enc c nc goods price (pubk m)))
  (traces
    ((send (enc c nc goods price (pubk m)))
      (recv (enc nc nm m goods price (pubk c)))
      (send (enc c nc nm price (pubk b)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb)))
    ((recv (enc c nc goods price (pubk m)))
      (send (enc nc nm m goods price (pubk c)))))
  (label 2)
  (parent 1)
  (unrealized (0 3))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo
  (vars (nb nc nm data) (goods price text) (b c m name))
  (defstrand customer 5 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b) (c c) (m m))
  (defstrand merchant 2 (nc nc) (nm nm) (goods goods) (price price)
    (c c) (m m))
  (defstrand bank 2 (nc nc) (nm nm) (nb nb) (price price) (b b) (c c))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)) ((1 1) (2 0)) ((2 1) (0 3)))
  (non-orig (privk b) (privk c) (privk m))
  (uniq-orig nb nc nm)
  (operation encryption-test (added-strand bank 2)
    (enc (enc "hash" (cat c nc nb nm price)) (privk b)) (0 3))
  (traces
    ((send (enc c nc goods price (pubk m)))
      (recv (enc nc nm m goods price (pubk c)))
      (send (enc c nc nm price (pubk b)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb)))
    ((recv (enc c nc goods price (pubk m)))
      (send (enc nc nm m goods price (pubk c))))
    ((recv (enc c nc nm price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))))
  (label 3)
  (parent 2)
  (unrealized (2 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton epmo
  (vars (nb nc nm data) (goods price text) (b c m name))
  (defstrand customer 5 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b) (c c) (m m))
  (defstrand merchant 2 (nc nc) (nm nm) (goods goods) (price price)
    (c c) (m m))
  (defstrand bank 2 (nc nc) (nm nm) (nb nb) (price price) (b b) (c c))
  (precedes ((0 0) (1 0)) ((0 2) (2 0)) ((1 1) (0 1)) ((2 1) (0 3)))
  (non-orig (privk b) (privk c) (privk m))
  (uniq-orig nb nc nm)
  (operation nonce-test (displaced 3 0 customer 3) nc (2 0)
    (enc nc nm m goods price (pubk c)) (enc c nc goods price (pubk m)))
  (traces
    ((send (enc c nc goods price (pubk m)))
      (recv (enc nc nm m goods price (pubk c)))
      (send (enc c nc nm price (pubk b)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb)))
    ((recv (enc c nc goods price (pubk m)))
      (send (enc nc nm m goods price (pubk c))))
    ((recv (enc c nc nm price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))))
  (label 4)
  (parent 3)
  (realized)
  (shape)
  (maps
    ((0)
      ((b b) (c c) (m m) (nb nb) (nc nc) (nm nm) (goods goods)
        (price price))))
  (origs (nc (0 0)) (nb (2 1)) (nm (1 1))))

(defskeleton epmo
  (vars (nb nc nm nm-0 data) (goods price text) (b c m name))
  (defstrand customer 5 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b) (c c) (m m))
  (defstrand merchant 2 (nc nc) (nm nm) (goods goods) (price price)
    (c c) (m m))
  (defstrand bank 2 (nc nc) (nm nm) (nb nb) (price price) (b b) (c c))
  (defstrand merchant 2 (nc nc) (nm nm-0) (goods goods) (price price)
    (c c) (m m))
  (precedes ((0 0) (1 0)) ((0 0) (3 0)) ((1 1) (0 1)) ((1 1) (2 0))
    ((2 1) (0 3)) ((3 1) (2 0)))
  (non-orig (privk b) (privk c) (privk m))
  (uniq-orig nb nc nm nm-0)
  (operation nonce-test (added-strand merchant 2) nc (2 0)
    (enc nc nm m goods price (pubk c)) (enc c nc goods price (pubk m)))
  (traces
    ((send (enc c nc goods price (pubk m)))
      (recv (enc nc nm m goods price (pubk c)))
      (send (enc c nc nm price (pubk b)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb)))
    ((recv (enc c nc goods price (pubk m)))
      (send (enc nc nm m goods price (pubk c))))
    ((recv (enc c nc nm price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc goods price (pubk m)))
      (send (enc nc nm-0 m goods price (pubk c)))))
  (label 5)
  (parent 3)
  (unrealized (2 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo
  (vars (nb nc nm nm-0 data) (goods price text) (b c m name))
  (defstrand customer 5 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b) (c c) (m m))
  (defstrand merchant 2 (nc nc) (nm nm) (goods goods) (price price)
    (c c) (m m))
  (defstrand bank 2 (nc nc) (nm nm) (nb nb) (price price) (b b) (c c))
  (defstrand merchant 2 (nc nc) (nm nm-0) (goods goods) (price price)
    (c c) (m m))
  (precedes ((0 0) (1 0)) ((0 0) (3 0)) ((0 2) (2 0)) ((1 1) (0 1))
    ((2 1) (0 3)) ((3 1) (2 0)))
  (non-orig (privk b) (privk c) (privk m))
  (uniq-orig nb nc nm nm-0)
  (operation nonce-test (displaced 4 0 customer 3) nc (2 0)
    (enc nc nm m goods price (pubk c))
    (enc nc nm-0 m goods price (pubk c))
    (enc c nc goods price (pubk m)))
  (traces
    ((send (enc c nc goods price (pubk m)))
      (recv (enc nc nm m goods price (pubk c)))
      (send (enc c nc nm price (pubk b)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb)))
    ((recv (enc c nc goods price (pubk m)))
      (send (enc nc nm m goods price (pubk c))))
    ((recv (enc c nc nm price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c)))))
    ((recv (enc c nc goods price (pubk m)))
      (send (enc nc nm-0 m goods price (pubk c)))))
  (label 6)
  (parent 5)
  (seen 4)
  (realized)
  (comment "1 in cohort - 0 not yet seen"))

(comment "Nothing left to do")

(defprotocol epmo basic
  (defrole bank
    (vars (b c m name) (nc nm nb data) (price text))
    (trace (recv (enc c nc nm price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" (cat b nb nm)) (privk m))))
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
    (vars (b c m name) (nb nc nm data) (goods price text))
    (trace (send (enc c nc goods price (pubk m)))
      (recv (enc nc nm m goods price (pubk c)))
      (send (enc c nc nm price (pubk b)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb)))
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
    (vars (b c m name) (nb nc nm data) (goods price text))
    (trace (recv (enc c nc goods price (pubk m)))
      (send (enc nc nm m goods price (pubk c)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))
      (send (enc (enc "hash" (cat b nb nm)) (privk m))))
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
      (3 (and (transfer b price m nm) (ship m goods c)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defgenrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2)) (false))))
  (defgenrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defgenrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1)))))
  (defgenrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2))))))

(defskeleton epmo
  (vars (nc nm nb data) (price text) (b c m name))
  (defstrand bank 3 (nc nc) (nm nm) (nb nb) (price price) (b b) (c c)
    (m m))
  (non-orig (privk b) (privk c) (privk m))
  (uniq-orig nb)
  (traces
    ((recv (enc c nc nm price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" (cat b nb nm)) (privk m)))))
  (label 7)
  (unrealized (0 2))
  (origs (nb (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo
  (vars (nc nm nb nc-0 data) (price goods price-0 text)
    (b c m c-0 name))
  (defstrand bank 3 (nc nc) (nm nm) (nb nb) (price price) (b b) (c c)
    (m m))
  (defstrand merchant 4 (nb nb) (nc nc-0) (nm nm) (goods goods)
    (price price-0) (b b) (c c-0) (m m))
  (precedes ((0 1) (1 2)) ((1 1) (0 0)) ((1 3) (0 2)))
  (non-orig (privk b) (privk c) (privk m))
  (uniq-orig nm nb)
  (operation encryption-test (added-strand merchant 4)
    (enc (enc "hash" (cat b nb nm)) (privk m)) (0 2))
  (traces
    ((recv (enc c nc nm price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" (cat b nb nm)) (privk m))))
    ((recv (enc c-0 nc-0 goods price-0 (pubk m)))
      (send (enc nc-0 nm m goods price-0 (pubk c-0)))
      (recv
        (cat (enc (enc "hash" (cat c-0 nc-0 nb nm price-0)) (privk b))
          nb)) (send (enc (enc "hash" (cat b nb nm)) (privk m)))))
  (label 8)
  (parent 7)
  (unrealized (1 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo
  (vars (nc nm nb data) (price goods text) (b c m name))
  (defstrand bank 3 (nc nc) (nm nm) (nb nb) (price price) (b b) (c c)
    (m m))
  (defstrand merchant 4 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b) (c c) (m m))
  (precedes ((0 1) (1 2)) ((1 1) (0 0)) ((1 3) (0 2)))
  (non-orig (privk b) (privk c) (privk m))
  (uniq-orig nm nb)
  (operation encryption-test (displaced 2 0 bank 2)
    (enc (enc "hash" (cat c-0 nc-0 nb nm price-0)) (privk b)) (1 2))
  (traces
    ((recv (enc c nc nm price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" (cat b nb nm)) (privk m))))
    ((recv (enc c nc goods price (pubk m)))
      (send (enc nc nm m goods price (pubk c)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))
      (send (enc (enc "hash" (cat b nb nm)) (privk m)))))
  (label 9)
  (parent 8)
  (unrealized (0 0) (1 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo
  (vars (nc nm nb nm-0 data) (price goods goods-0 price-0 text)
    (b c m b-0 m-0 name))
  (defstrand bank 3 (nc nc) (nm nm) (nb nb) (price price) (b b) (c c)
    (m m))
  (defstrand merchant 4 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b) (c c) (m m))
  (defstrand customer 5 (nb nb) (nc nc) (nm nm-0) (goods goods-0)
    (price price-0) (b b-0) (c c) (m m-0))
  (precedes ((0 1) (2 3)) ((1 1) (0 0)) ((1 3) (0 2)) ((2 0) (1 0))
    ((2 4) (1 2)))
  (non-orig (privk b) (privk c) (privk m))
  (uniq-orig nc nm nb)
  (operation nonce-test (added-strand customer 5) nb (1 2)
    (enc nc nb (pubk c)))
  (traces
    ((recv (enc c nc nm price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" (cat b nb nm)) (privk m))))
    ((recv (enc c nc goods price (pubk m)))
      (send (enc nc nm m goods price (pubk c)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))
      (send (enc (enc "hash" (cat b nb nm)) (privk m))))
    ((send (enc c nc goods-0 price-0 (pubk m-0)))
      (recv (enc nc nm-0 m-0 goods-0 price-0 (pubk c)))
      (send (enc c nc nm-0 price-0 (pubk b-0)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm-0 price-0)) (privk b-0))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm-0 price-0)) (privk b-0))
          nb))))
  (label 10)
  (parent 9)
  (unrealized (0 0) (2 3))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton epmo
  (vars (nc nm nb data) (price goods goods-0 text) (b c m b-0 m-0 name))
  (defstrand bank 3 (nc nc) (nm nm) (nb nb) (price price) (b b) (c c)
    (m m))
  (defstrand merchant 4 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b) (c c) (m m))
  (defstrand customer 5 (nb nb) (nc nc) (nm nm) (goods goods-0)
    (price price) (b b-0) (c c) (m m-0))
  (precedes ((0 1) (2 3)) ((1 1) (0 0)) ((1 1) (2 1)) ((1 3) (0 2))
    ((2 0) (1 0)) ((2 4) (1 2)))
  (non-orig (privk b) (privk c) (privk m))
  (uniq-orig nc nm nb)
  (operation encryption-test (displaced 3 0 bank 2)
    (enc "hash" (cat c nc nb nm-0 price-0)) (2 3))
  (traces
    ((recv (enc c nc nm price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" (cat b nb nm)) (privk m))))
    ((recv (enc c nc goods price (pubk m)))
      (send (enc nc nm m goods price (pubk c)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))
      (send (enc (enc "hash" (cat b nb nm)) (privk m))))
    ((send (enc c nc goods-0 price (pubk m-0)))
      (recv (enc nc nm m-0 goods-0 price (pubk c)))
      (send (enc c nc nm price (pubk b-0)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b-0))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b-0))
          nb))))
  (label 11)
  (parent 10)
  (unrealized (0 0) (2 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo
  (vars (nc nm nb nm-0 data) (price goods goods-0 price-0 text)
    (b c m b-0 m-0 name))
  (defstrand bank 3 (nc nc) (nm nm) (nb nb) (price price) (b b) (c c)
    (m m))
  (defstrand merchant 4 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b) (c c) (m m))
  (defstrand customer 5 (nb nb) (nc nc) (nm nm-0) (goods goods-0)
    (price price-0) (b b-0) (c c) (m m-0))
  (deflistener (cat c nc nb nm-0 price-0))
  (precedes ((0 1) (3 0)) ((1 1) (0 0)) ((1 3) (0 2)) ((2 0) (1 0))
    ((2 4) (1 2)) ((3 1) (2 3)))
  (non-orig (privk b) (privk c) (privk m))
  (uniq-orig nc nm nb)
  (operation encryption-test (added-listener (cat c nc nb nm-0 price-0))
    (enc "hash" (cat c nc nb nm-0 price-0)) (2 3))
  (traces
    ((recv (enc c nc nm price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" (cat b nb nm)) (privk m))))
    ((recv (enc c nc goods price (pubk m)))
      (send (enc nc nm m goods price (pubk c)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))
      (send (enc (enc "hash" (cat b nb nm)) (privk m))))
    ((send (enc c nc goods-0 price-0 (pubk m-0)))
      (recv (enc nc nm-0 m-0 goods-0 price-0 (pubk c)))
      (send (enc c nc nm-0 price-0 (pubk b-0)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm-0 price-0)) (privk b-0))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm-0 price-0)) (privk b-0))
          nb)))
    ((recv (cat c nc nb nm-0 price-0))
      (send (cat c nc nb nm-0 price-0))))
  (label 12)
  (parent 10)
  (unrealized (0 0) (3 0))
  (dead)
  (comment "empty cohort"))

(defskeleton epmo
  (vars (nc nm nb data) (price goods text) (b c m b-0 name))
  (defstrand bank 3 (nc nc) (nm nm) (nb nb) (price price) (b b) (c c)
    (m m))
  (defstrand merchant 4 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b) (c c) (m m))
  (defstrand customer 5 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b-0) (c c) (m m))
  (precedes ((0 1) (2 3)) ((1 1) (0 0)) ((1 1) (2 1)) ((1 3) (0 2))
    ((2 0) (1 0)) ((2 4) (1 2)))
  (non-orig (privk b) (privk c) (privk m))
  (uniq-orig nc nm nb)
  (operation nonce-test (contracted (m-0 m) (goods-0 goods)) nm (2 1)
    (enc nc nm m goods price (pubk c)))
  (traces
    ((recv (enc c nc nm price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" (cat b nb nm)) (privk m))))
    ((recv (enc c nc goods price (pubk m)))
      (send (enc nc nm m goods price (pubk c)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))
      (send (enc (enc "hash" (cat b nb nm)) (privk m))))
    ((send (enc c nc goods price (pubk m)))
      (recv (enc nc nm m goods price (pubk c)))
      (send (enc c nc nm price (pubk b-0)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b-0))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b-0))
          nb))))
  (label 13)
  (parent 11)
  (unrealized (0 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo
  (vars (nc nm nb data) (price goods text) (b c m b-0 name))
  (defstrand bank 3 (nc nc) (nm nm) (nb nb) (price price) (b b) (c c)
    (m m))
  (defstrand merchant 4 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b) (c c) (m m))
  (defstrand customer 5 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b-0) (c c) (m m))
  (precedes ((0 1) (2 3)) ((1 1) (2 1)) ((1 3) (0 2)) ((2 0) (1 0))
    ((2 2) (0 0)) ((2 4) (1 2)))
  (non-orig (privk b) (privk c) (privk m))
  (uniq-orig nc nm nb)
  (operation nonce-test (displaced 3 2 customer 3) nm (0 0)
    (enc nc nm m goods price (pubk c)))
  (traces
    ((recv (enc c nc nm price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" (cat b nb nm)) (privk m))))
    ((recv (enc c nc goods price (pubk m)))
      (send (enc nc nm m goods price (pubk c)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))
      (send (enc (enc "hash" (cat b nb nm)) (privk m))))
    ((send (enc c nc goods price (pubk m)))
      (recv (enc nc nm m goods price (pubk c)))
      (send (enc c nc nm price (pubk b-0)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b-0))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b-0))
          nb))))
  (label 14)
  (parent 13)
  (realized)
  (shape)
  (maps ((0) ((b b) (c c) (m m) (nc nc) (nm nm) (nb nb) (price price))))
  (origs (nc (2 0)) (nb (0 1)) (nm (1 1))))

(comment "Nothing left to do")

(defprotocol epmo basic
  (defrole bank
    (vars (b c m name) (nc nm nb data) (price text))
    (trace (recv (enc c nc nm price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (recv (enc (enc "hash" (cat b nb nm)) (privk m))))
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
    (vars (b c m name) (nb nc nm data) (goods price text))
    (trace (send (enc c nc goods price (pubk m)))
      (recv (enc nc nm m goods price (pubk c)))
      (send (enc c nc nm price (pubk b)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb)))
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
    (vars (b c m name) (nb nc nm data) (goods price text))
    (trace (recv (enc c nc goods price (pubk m)))
      (send (enc nc nm m goods price (pubk c)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))
      (send (enc (enc "hash" (cat b nb nm)) (privk m))))
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
      (3 (and (transfer b price m nm) (ship m goods c)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defgenrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2)) (false))))
  (defgenrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defgenrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1)))))
  (defgenrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2))))))

(defskeleton epmo
  (vars (nb nc nm data) (goods price text) (b c m name))
  (defstrand merchant 4 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b) (c c) (m m))
  (non-orig (privk b) (privk c) (privk m))
  (uniq-orig nm)
  (traces
    ((recv (enc c nc goods price (pubk m)))
      (send (enc nc nm m goods price (pubk c)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))
      (send (enc (enc "hash" (cat b nb nm)) (privk m)))))
  (label 15)
  (unrealized (0 2))
  (origs (nm (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo
  (vars (nb nc nm data) (goods price text) (b c m name))
  (defstrand merchant 4 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b) (c c) (m m))
  (defstrand bank 2 (nc nc) (nm nm) (nb nb) (price price) (b b) (c c))
  (precedes ((0 1) (1 0)) ((1 1) (0 2)))
  (non-orig (privk b) (privk c) (privk m))
  (uniq-orig nb nm)
  (operation encryption-test (added-strand bank 2)
    (enc (enc "hash" (cat c nc nb nm price)) (privk b)) (0 2))
  (traces
    ((recv (enc c nc goods price (pubk m)))
      (send (enc nc nm m goods price (pubk c)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))
      (send (enc (enc "hash" (cat b nb nm)) (privk m))))
    ((recv (enc c nc nm price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c))))))
  (label 16)
  (parent 15)
  (unrealized (0 2) (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo
  (vars (nb nc nm data) (goods price text) (b c m b-0 name))
  (defstrand merchant 4 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b) (c c) (m m))
  (defstrand bank 2 (nc nc) (nm nm) (nb nb) (price price) (b b) (c c))
  (defstrand customer 3 (nc nc) (nm nm) (goods goods) (price price)
    (b b-0) (c c) (m m))
  (precedes ((0 1) (2 1)) ((1 1) (0 2)) ((2 0) (0 0)) ((2 2) (1 0)))
  (non-orig (privk b) (privk c) (privk m))
  (uniq-orig nb nc nm)
  (operation nonce-test (added-strand customer 3) nm (1 0)
    (enc nc nm m goods price (pubk c)))
  (traces
    ((recv (enc c nc goods price (pubk m)))
      (send (enc nc nm m goods price (pubk c)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))
      (send (enc (enc "hash" (cat b nb nm)) (privk m))))
    ((recv (enc c nc nm price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods price (pubk m)))
      (recv (enc nc nm m goods price (pubk c)))
      (send (enc c nc nm price (pubk b-0)))))
  (label 17)
  (parent 16)
  (unrealized (0 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton epmo
  (vars (nb nc nm data) (goods price text) (b c b-0 m name))
  (defstrand merchant 4 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b) (c c) (m m))
  (defstrand bank 2 (nc nc) (nm nm) (nb nb) (price price) (b b) (c c))
  (defstrand customer 5 (nb nb) (nc nc) (nm nm) (goods goods)
    (price price) (b b-0) (c c) (m m))
  (precedes ((0 1) (2 1)) ((1 1) (2 3)) ((2 0) (0 0)) ((2 2) (1 0))
    ((2 4) (0 2)))
  (non-orig (privk b) (privk c) (privk m))
  (uniq-orig nb nc nm)
  (operation nonce-test (displaced 2 3 customer 5) nb (0 2)
    (enc nc nb (pubk c)))
  (traces
    ((recv (enc c nc goods price (pubk m)))
      (send (enc nc nm m goods price (pubk c)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b)) nb))
      (send (enc (enc "hash" (cat b nb nm)) (privk m))))
    ((recv (enc c nc nm price (pubk b)))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b))
          (enc nc nb (pubk c)))))
    ((send (enc c nc goods price (pubk m)))
      (recv (enc nc nm m goods price (pubk c)))
      (send (enc c nc nm price (pubk b-0)))
      (recv
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b-0))
          (enc nc nb (pubk c))))
      (send
        (cat (enc (enc "hash" (cat c nc nb nm price)) (privk b-0))
          nb))))
  (label 18)
  (parent 17)
  (realized)
  (shape)
  (maps
    ((0)
      ((b b) (c c) (m m) (nb nb) (nc nc) (nm nm) (goods goods)
        (price price))))
  (origs (nc (2 0)) (nb (1 1)) (nm (0 1))))

(comment "Nothing left to do")
