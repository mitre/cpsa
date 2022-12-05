guttman@MM271004-PC examples % for i in *.tst; do echo $i; cpsa4diff $i `basename $i tst`txt; done 
for i in *.tst; do echo $i; cpsa4diff $i `basename $i tst`txt; done 
blanchet.tst
blanchet_shapes.tst
bltk_test.tst
bltk_test_shapes.tst
chan-yahalom-role-decl.tst
chan-yahalom-role-decl_shapes.tst
chan-yahalom.tst
chan-yahalom_shapes.tst
dhcr_um_expt_assume.tst
<<< dhcr_um_expt_assume.tst:258:1: 
(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (l l-0 lb x y rndx)
    (zeta expt))
  (defstrand init 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (la l) (x x) (beta l-0) (upsilon (mul (rec x) y zeta)))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l-0))
  (defstrand resp 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor-1)
    (lb lb) (y y) (alpha (mul l l-0 (rec lb))) (zeta zeta))
  (precedes ((0 2) (3 2)) ((1 1) (0 0)) ((2 2) (0 1)) ((3 3) (0 3)))
  (non-orig (privk "sig" b))
  (uniq-orig na nb l l-0)
  (uniq-gen x y)
  (absent (x l) (x l-0) (y (mul l l-0 (rec lb))) (y lb) (y zeta))
  (gen-st (pv a l) (pv b lb))
  (facts (neq (exp (gen) (mul (rec x) y zeta)) (gen))
    (neq (exp (gen) zeta) (gen)) (trans 2 1) (trans 1 1) (trans 2 0)
    (trans 1 0) (neq a b) (undisclosed l)
    (undisclosed l-0)) gen-st-ltx-disclose-0)
<<<
>>> dhcr_um_expt_assume.txt:258:1: 
(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (a b name)
    (pt pt-0 pt-1 pt-2 pt-3 pval)
    (priv-stor priv-stor-0 priv-stor-1 locn) (l l-0 lb x y rndx)
    (zeta expt))
  (defstrand init 5 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor)
    (la l) (x x) (beta l-0) (upsilon (mul (rec x) y zeta)))
  (defstrand ltx-gen 2 (ignore ignore) (self a) (priv-stor priv-stor)
    (l l))
  (defstrand ltx-gen 3 (ignore ignore-0) (self b)
    (priv-stor priv-stor-0) (l l-0))
  (defstrand resp 4 (na na) (nb nb) (a a) (b b) (priv-stor priv-stor-1)
    (lb lb) (y y) (alpha (mul l l-0 (rec lb))) (zeta zeta))
  (precedes ((0 2) (3 2)) ((1 1) (0 0)) ((2 2) (0 1)) ((3 3) (0 3)))
  (non-orig (privk "sig" b))
  (uniq-orig na nb l l-0)
  (uniq-gen x y)
  (absent (x l) (x l-0) (y (mul l l-0 (rec lb))) (y lb) (y zeta))
  (gen-st (pv a l) (pv b lb))
  (facts (neq (exp (gen) (mul (rec x) y zeta)) (gen))
    (neq (exp (gen) zeta) (gen)) (trans 2 1) (trans 1 1) (trans 2 0)
    (trans 1 0) (neq a b) (undisclosed l) (undisclosed l-0))
  (operation encryption-test (added-strand resp 4)
    (enc na nb a b
      (hash (exp (gen) (mul l l-0)) (exp (gen) (mul y zeta)))) (0 3))
  (traces
    ((load priv-stor (cat pt (pv a l)))
      (recv
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na a b (exp (gen) x)))
      (recv
        (cat (exp (gen) (mul (rec x) y zeta))
          (enc na nb a b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul y zeta))))))
      (send nb))
    ((load priv-stor (cat pt-0 ignore))
      (stor priv-stor (cat pt (pv a l))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv b l-0)))
      (send
        (sig (body b (exp (gen) l-0) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor-1 (cat pt-3 (pv b lb)))
      (recv
        (sig (body a (exp (gen) (mul l l-0 (rec lb))) (pubk "sig" a))
          (privk "sig" a))) (recv (cat na a b (exp (gen) zeta)))
      (send
        (cat (exp (gen) y)
          (enc na nb a b
            (hash (exp (gen) (mul l l-0)) (exp (gen) (mul y zeta))))))))
  (label 4)
  (parent 3)
  (unrealized (0 3) (3 0) (3 1))
  (comment "2 in cohort - 2 not yet seen"))
>>>
dhcr_um_expt_assume_shapes.tst
<<< dhcr_um_expt_assume_shapes.tst:161:1: 
(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (b self name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn)
    (lb l x y rndx))
  (defstrand init 5 (na na) (nb nb) (a self) (b b)
    (priv-stor priv-stor-0) (la l) (x x) (beta lb) (upsilon y))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l lb))
  (defstrand resp 4 (na na) (nb nb) (a self) (b b) (priv-stor priv-stor)
    (lb lb) (y y) (alpha l) (zeta x))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l))
  (precedes ((0 2) (2 2)) ((1 1) (2 0)) ((1 2) (0 1)) ((2 3) (0 3))
    ((3 1) (0 0)) ((3 2) (2 1)))
  (non-orig (privk "sig" b))
  (uniq-orig na nb lb l)
  (uniq-gen x y)
  (absent (x lb) (x l) (y lb) (y l) (y x))
  (gen-st (pv b lb) (pv self l))
  (facts (neq (exp (gen) y) (gen)) (neq (exp (gen) x) (gen)) (trans 3 1)
    (trans 1 1) (trans 3 0) (trans 1 0) (neq self b) (undisclosed l)
    (undisclosed lb))
  (rule assume-init-0 assume-resp-0 trRl_ltx-gen-at-1 trRl_ltx-gen-at-0)
  (operation nonce-test (displaced 4 2 resp 4) (exp (gen) y-0) (0 3))
  (traces
    ((load priv-stor-0 (cat pt-2 (pv self l)))
      (recv
        (sig (body b (exp (gen) lb) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na self b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb self b
            (hash (exp (gen) (mul lb l)) (exp (gen) (mul x y))))))
      (send nb))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv b lb)))
      (send
        (sig (body b (exp (gen) lb) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt-0 (pv b lb)))
      (recv
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self))) (recv (cat na self b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb self b
            (hash (exp (gen) (mul lb l)) (exp (gen) (mul x y)))))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv self l)))
      (send
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self)))))
  (label 16)
  (parent 0)
  (realized)
  (shape)
  (maps
    ((0)
      ((a self) (b b) (la l) (beta lb) (x x) (upsilon y) (na na) (nb nb)
        (priv-stor priv-stor-0) (pt pt-2))))
  (origs (nb (2 3)) (l (3 1)) (pt-2 (3 1)) (lb (1 1)) (pt-0 (1 1))
    (na (0 2))))
<<<
>>> dhcr_um_expt_assume_shapes.txt:161:1: 
(defskeleton dhcr-um
  (vars (ignore ignore-0 mesg) (na nb data) (b self name)
    (pt pt-0 pt-1 pt-2 pval) (priv-stor priv-stor-0 locn)
    (lb l x y rndx))
  (defstrand init 5 (na na) (nb nb) (a self) (b b)
    (priv-stor priv-stor-0) (la l) (x x) (beta lb) (upsilon y))
  (defstrand ltx-gen 3 (ignore ignore) (self b) (priv-stor priv-stor)
    (l lb))
  (defstrand resp 4 (na na) (nb nb) (a self) (b b) (priv-stor priv-stor)
    (lb lb) (y y) (alpha l) (zeta x))
  (defstrand ltx-gen 3 (ignore ignore-0) (self self)
    (priv-stor priv-stor-0) (l l))
  (precedes ((0 2) (2 2)) ((1 1) (2 0)) ((1 2) (0 1)) ((2 3) (0 3))
    ((3 1) (0 0)) ((3 2) (2 1)))
  (non-orig (privk "sig" b))
  (uniq-orig na nb lb l)
  (uniq-gen x y)
  (absent (x lb) (x l) (y lb) (y l) (y x))
  (gen-st (pv b lb) (pv self l))
  (facts (neq (exp (gen) y) (gen)) (neq (exp (gen) x) (gen)) (trans 3 1)
    (trans 1 1) (trans 3 0) (trans 1 0) (neq self b) (undisclosed l)
    (undisclosed lb))
  (operation nonce-test (displaced 4 2 resp 4) (exp (gen) y-0) (0 3))
  (traces
    ((load priv-stor-0 (cat pt-2 (pv self l)))
      (recv
        (sig (body b (exp (gen) lb) (pubk "sig" b)) (privk "sig" b)))
      (send (cat na self b (exp (gen) x)))
      (recv
        (cat (exp (gen) y)
          (enc na nb self b
            (hash (exp (gen) (mul lb l)) (exp (gen) (mul x y))))))
      (send nb))
    ((load priv-stor (cat pt ignore))
      (stor priv-stor (cat pt-0 (pv b lb)))
      (send
        (sig (body b (exp (gen) lb) (pubk "sig" b)) (privk "sig" b))))
    ((load priv-stor (cat pt-0 (pv b lb)))
      (recv
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self))) (recv (cat na self b (exp (gen) x)))
      (send
        (cat (exp (gen) y)
          (enc na nb self b
            (hash (exp (gen) (mul lb l)) (exp (gen) (mul x y)))))))
    ((load priv-stor-0 (cat pt-1 ignore-0))
      (stor priv-stor-0 (cat pt-2 (pv self l)))
      (send
        (sig (body self (exp (gen) l) (pubk "sig" self))
          (privk "sig" self)))))
  (label 16)
  (parent 0)
  (realized)
  (shape)
  (maps
    ((0)
      ((a self) (b b) (la l) (beta lb) (x x) (upsilon y) (na na) (nb nb)
        (priv-stor priv-stor-0) (pt pt-2))))
  (origs (nb (2 3)) (l (3 1)) (pt-2 (3 1)) (lb (1 1)) (pt-0 (1 1))
    (na (0 2))))
>>>
kerb.tst
kerb_shapes.tst
kerberos-variant-guar.tst
kerberos-variant-guar_shapes.tst
<<< kerberos-variant-guar_shapes.tst:236:1: 
(defskeleton kerberos-variant
  (vars (a-ks-lt b-ks-lt k skey) (t l text) (a b ks name))
  (defstrand keyserver 2 (a-ks-lt a-ks-lt) (b-ks-lt b-ks-lt) (k k) (t t)
    (l l) (a a) (b b) (ks ks))
  (non-orig a-ks-lt b-ks-lt)
  (uniq-orig k)
  (facts (long-term b ks b-ks-lt) (long-term a ks a-ks-lt))
  (rule long-term-key-non guar-keyserver-2)
  (traces
    ((recv (cat a b ks))
      (send
        (cat (enc t l k a b ks a-ks-lt)
          (enc "ticket" t l k a b ks b-ks-lt)))))
  (label 13)
  (parent 12)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (ks ks) (a-ks-lt a-ks-lt) (b-ks-lt b-ks-lt) (t t)
        (l l) (k k))))
  (origs (k (0 1))))
<<<
>>> kerberos-variant-guar_shapes.txt:236:1: 
(defskeleton kerberos-variant
  (vars (a-ks-lt b-ks-lt k skey) (t l text) (a b ks name))
  (defstrand keyserver 2 (a-ks-lt a-ks-lt) (b-ks-lt b-ks-lt) (k k) (t t)
    (l l) (a a) (b b) (ks ks))
  (non-orig a-ks-lt b-ks-lt)
  (uniq-orig k)
  (facts (long-term b ks b-ks-lt) (long-term a ks a-ks-lt))
  (traces
    ((recv (cat a b ks))
      (send
        (cat (enc t l k a b ks a-ks-lt)
          (enc "ticket" t l k a b ks b-ks-lt)))))
  (label 13)
  (parent 12)
  (realized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (ks ks) (a-ks-lt a-ks-lt) (b-ks-lt b-ks-lt) (t t)
        (l l) (k k))))
  (origs (k (0 1))))
>>>
minipay-rely-guar-2.tst
>>> minipay-rely-guar-2.txt:2163:1: 
(defskeleton minipay-rely-guar
  (vars (bank-conf-commit mesg) (cost amount) (account n account-0 data)
    (item item-0 merchandise)
    (merc-conf btr mtr merc-conf-0 bank-conf bank-conf-0 text)
    (c m b name))
  (defstrand merc 3
    (for-bank
      (enc n cost account-0 bank-conf-0 (hash n merc-conf)
        (pubk "enc" b))) (bank-conf-commit bank-conf-commit) (cost cost)
    (n n) (item item) (merc-conf merc-conf) (bank-conf bank-conf-0)
    (btr btr) (mtr mtr) (c c) (m m) (b b))
  (defstrand cust 1 (cost cost) (account account) (n n) (item item-0)
    (merc-conf merc-conf-0) (bank-conf bank-conf) (c c) (m m) (b b))
  (defstrand bank 2 (cost cost) (account account-0) (n n)
    (merc-conf merc-conf) (bank-conf bank-conf-0) (btr btr) (mtr mtr)
    (c c) (m m) (b b))
  (precedes ((0 1) (2 0)) ((2 1) (0 2)))
  (non-orig (privk "enc" m) (privk "enc" b) (privk "sig" m)
    (privk "sig" b))
  (uniq-orig btr mtr)
  (facts (buy-via c m b item-0 cost n)
    (will-transfer c m b cost n mtr btr))
  (operation encryption-test (contracted (bank-conf-1 bank-conf-0))
    (sign (bconf c m b (hash n cost) merc-conf btr mtr) (privk "sig" b))
    (0 2)
    (enc bank-conf-0
      (sign (bconf c m b (hash n cost) merc-conf btr mtr)
        (privk "sig" b)) (pubk "enc" m)))
  (traces
    ((recv
       (enc n cost item merc-conf bank-conf-commit
         (sign
           (order c m b cost
             (enc n cost account-0 bank-conf-0 (hash n merc-conf)
               (pubk "enc" b))) (privk "sig" c)) (pubk "enc" m)))
      (send
        (sign
          (payreq c m b (hash cost n) merc-conf mtr
            (enc n cost account-0 bank-conf-0 (hash n merc-conf)
              (pubk "enc" b))) (privk "sig" m)))
      (recv
        (enc bank-conf-0
          (sign (bconf c m b (hash n cost) merc-conf btr mtr)
            (privk "sig" b)) (pubk "enc" m))))
    ((send
       (enc n cost item-0 merc-conf-0 (hash n bank-conf)
         (sign
           (order c m b cost
             (enc n cost account bank-conf (hash n merc-conf-0)
               (pubk "enc" b))) (privk "sig" c)) (pubk "enc" m))))
    ((recv
       (sign
         (payreq c m b (hash cost n) merc-conf mtr
           (enc n cost account-0 bank-conf-0 (hash n merc-conf)
             (pubk "enc" b))) (privk "sig" m)))
      (send
        (enc bank-conf-0
          (sign (bconf c m b (hash n cost) merc-conf btr mtr)
            (privk "sig" b)) (pubk "enc" m)))))
  (label 26)
  (parent 25)
  (realized)
  (shape)
  (maps
    ((0)
      ((c c) (m m) (b b) (cost cost) (item item) (merc-conf merc-conf)
        (bank-conf bank-conf-0) (btr btr) (mtr mtr) (n n)
        (for-bank
          (enc n cost account-0 bank-conf-0 (hash n merc-conf)
            (pubk "enc" b))) (bank-conf-commit bank-conf-commit))))
  (origs (mtr (0 1)) (btr (2 1))))
>>>
minipay-rely-guar.tst
<<< minipay-rely-guar.tst:159:1: 
(defskeleton minipay-rely-guar
  (vars (cost amount) (n account data) (item merchandise)
    (merc-conf bank-conf btr mtr text) (c m b name))
  (defstrand cust 3 (cost cost) (account account) (n n) (item item)
    (merc-conf merc-conf) (bank-conf bank-conf) (btr btr) (mtr mtr)
    (c c) (m m) (b b))
  (non-orig (privk "enc" m) (privk "enc" b) (privk "sig" m)
    (privk "sig" b))
  (uniq-orig n)
  (facts (will-transfer c m b cost n mtr btr) (will-ship c m b item mtr)
    (buy-via c m b item cost n))
  (rule rely-cust-3 guar-cust-1)
  (traces
    ((send
       (enc n cost item merc-conf (hash n bank-conf)
         (sign
           (order c m b cost
             (enc n cost account bank-conf (hash n merc-conf)
               (pubk "enc" b))) (privk "sig" c)) (pubk "enc" m)))
      (recv
        (sign (bconf c m b (hash n cost) merc-conf btr mtr)
          (privk "sig" b)))
      (recv
        (sign (mconf c m b (hash n item cost) bank-conf btr mtr)
          (privk "sig" m)))))
  (label 1)
  (parent 0)
  (unrealized (0 1) (0 2))
  (origs (n (0 0)))
  (comment "1 in cohort - 1 not yet seen"))
<<<
>>> minipay-rely-guar.txt:159:1: 
(defskeleton minipay-rely-guar
  (vars (cost amount) (n account data) (item merchandise)
    (merc-conf bank-conf btr mtr text) (c m b name))
  (defstrand cust 3 (cost cost) (account account) (n n) (item item)
    (merc-conf merc-conf) (bank-conf bank-conf) (btr btr) (mtr mtr)
    (c c) (m m) (b b))
  (non-orig (privk "enc" m) (privk "enc" b) (privk "sig" m)
    (privk "sig" b))
  (uniq-orig n)
  (facts (will-transfer c m b cost n mtr btr) (will-ship c m b item mtr)
    (buy-via c m b item cost n))
  (traces
    ((send
       (enc n cost item merc-conf (hash n bank-conf)
         (sign
           (order c m b cost
             (enc n cost account bank-conf (hash n merc-conf)
               (pubk "enc" b))) (privk "sig" c)) (pubk "enc" m)))
      (recv
        (sign (bconf c m b (hash n cost) merc-conf btr mtr)
          (privk "sig" b)))
      (recv
        (sign (mconf c m b (hash n item cost) bank-conf btr mtr)
          (privk "sig" m)))))
  (label 1)
  (parent 0)
  (unrealized (0 1) (0 2))
  (origs (n (0 0)))
  (comment "1 in cohort - 1 not yet seen"))
>>>
minipay-rely-guar_shapes.tst
<<< minipay-rely-guar_shapes.tst:163:1: 
(defskeleton minipay-rely-guar
  (vars (cost amount) (n account data) (item merchandise)
    (merc-conf bank-conf btr mtr text) (c m b name))
  (defstrand cust 3 (cost cost) (account account) (n n) (item item)
    (merc-conf merc-conf) (bank-conf bank-conf) (btr btr) (mtr mtr)
    (c c) (m m) (b b))
  (defstrand bank 2 (cost cost) (account account) (n n)
    (merc-conf merc-conf) (bank-conf bank-conf) (btr btr) (mtr mtr)
    (c c) (m m) (b b))
  (defstrand merc 4
    (for-bank
      (enc n cost account bank-conf (hash n merc-conf) (pubk "enc" b)))
    (bank-conf-commit (hash n bank-conf)) (cost cost) (n n) (item item)
    (merc-conf merc-conf) (bank-conf bank-conf) (btr btr) (mtr mtr)
    (c c) (m m) (b b))
  (precedes ((0 0) (2 0)) ((1 1) (2 2)) ((2 1) (1 0)) ((2 3) (0 1)))
  (non-orig (privk "enc" m) (privk "enc" b) (privk "sig" m)
    (privk "sig" b))
  (uniq-orig n btr mtr)
  (facts (buy-via c m b item cost n) (will-ship c m b item mtr)
    (will-transfer c m b cost n mtr btr))
  (rule guar-cust-1 guar-merc-4 guar-bank-2)
  (operation encryption-test (displaced 2 3 merc 4)
    (sign (bconf c m b (hash n cost) merc-conf btr mtr) (privk "sig" b))
    (0 1)
    (enc bank-conf
      (sign (bconf c m b (hash n cost) merc-conf btr mtr)
        (privk "sig" b)) (pubk "enc" m)))
  (traces
    ((send
       (enc n cost item merc-conf (hash n bank-conf)
         (sign
           (order c m b cost
             (enc n cost account bank-conf (hash n merc-conf)
               (pubk "enc" b))) (privk "sig" c)) (pubk "enc" m)))
      (recv
        (sign (bconf c m b (hash n cost) merc-conf btr mtr)
          (privk "sig" b)))
      (recv
        (sign (mconf c m b (hash n item cost) bank-conf btr mtr)
          (privk "sig" m))))
    ((recv
       (sign
         (payreq c m b (hash cost n) merc-conf mtr
           (enc n cost account bank-conf (hash n merc-conf)
             (pubk "enc" b))) (privk "sig" m)))
      (send
        (enc bank-conf
          (sign (bconf c m b (hash n cost) merc-conf btr mtr)
            (privk "sig" b)) (pubk "enc" m))))
    ((recv
       (enc n cost item merc-conf (hash n bank-conf)
         (sign
           (order c m b cost
             (enc n cost account bank-conf (hash n merc-conf)
               (pubk "enc" b))) (privk "sig" c)) (pubk "enc" m)))
      (send
        (sign
          (payreq c m b (hash cost n) merc-conf mtr
            (enc n cost account bank-conf (hash n merc-conf)
              (pubk "enc" b))) (privk "sig" m)))
      (recv
        (enc bank-conf
          (sign (bconf c m b (hash n cost) merc-conf btr mtr)
            (privk "sig" b)) (pubk "enc" m)))
      (send
        (cat
          (sign (bconf c m b (hash n cost) merc-conf btr mtr)
            (privk "sig" b))
          (sign (mconf c m b (hash n item cost) bank-conf btr mtr)
            (privk "sig" m))))))
  (label 7)
  (parent 0)
  (realized)
  (shape)
  (maps
    ((0)
      ((c c) (m m) (b b) (n n) (cost cost) (item item)
        (merc-conf merc-conf) (bank-conf bank-conf) (btr btr) (mtr mtr)
        (account account))))
  (origs (mtr (2 1)) (btr (1 1)) (n (0 0))))
<<<
>>> minipay-rely-guar_shapes.txt:163:1: 
(defskeleton minipay-rely-guar
  (vars (cost amount) (n account data) (item merchandise)
    (merc-conf bank-conf btr mtr text) (c m b name))
  (defstrand cust 3 (cost cost) (account account) (n n) (item item)
    (merc-conf merc-conf) (bank-conf bank-conf) (btr btr) (mtr mtr)
    (c c) (m m) (b b))
  (defstrand bank 2 (cost cost) (account account) (n n)
    (merc-conf merc-conf) (bank-conf bank-conf) (btr btr) (mtr mtr)
    (c c) (m m) (b b))
  (defstrand merc 4
    (for-bank
      (enc n cost account bank-conf (hash n merc-conf) (pubk "enc" b)))
    (bank-conf-commit (hash n bank-conf)) (cost cost) (n n) (item item)
    (merc-conf merc-conf) (bank-conf bank-conf) (btr btr) (mtr mtr)
    (c c) (m m) (b b))
  (precedes ((0 0) (2 0)) ((1 1) (2 2)) ((2 1) (1 0)) ((2 3) (0 1)))
  (non-orig (privk "enc" m) (privk "enc" b) (privk "sig" m)
    (privk "sig" b))
  (uniq-orig n btr mtr)
  (facts (buy-via c m b item cost n) (will-ship c m b item mtr)
    (will-transfer c m b cost n mtr btr))
  (operation encryption-test (displaced 2 3 merc 4)
    (sign (bconf c m b (hash n cost) merc-conf btr mtr) (privk "sig" b))
    (0 1)
    (enc bank-conf
      (sign (bconf c m b (hash n cost) merc-conf btr mtr)
        (privk "sig" b)) (pubk "enc" m)))
  (traces
    ((send
       (enc n cost item merc-conf (hash n bank-conf)
         (sign
           (order c m b cost
             (enc n cost account bank-conf (hash n merc-conf)
               (pubk "enc" b))) (privk "sig" c)) (pubk "enc" m)))
      (recv
        (sign (bconf c m b (hash n cost) merc-conf btr mtr)
          (privk "sig" b)))
      (recv
        (sign (mconf c m b (hash n item cost) bank-conf btr mtr)
          (privk "sig" m))))
    ((recv
       (sign
         (payreq c m b (hash cost n) merc-conf mtr
           (enc n cost account bank-conf (hash n merc-conf)
             (pubk "enc" b))) (privk "sig" m)))
      (send
        (enc bank-conf
          (sign (bconf c m b (hash n cost) merc-conf btr mtr)
            (privk "sig" b)) (pubk "enc" m))))
    ((recv
       (enc n cost item merc-conf (hash n bank-conf)
         (sign
           (order c m b cost
             (enc n cost account bank-conf (hash n merc-conf)
               (pubk "enc" b))) (privk "sig" c)) (pubk "enc" m)))
      (send
        (sign
          (payreq c m b (hash cost n) merc-conf mtr
            (enc n cost account bank-conf (hash n merc-conf)
              (pubk "enc" b))) (privk "sig" m)))
      (recv
        (enc bank-conf
          (sign (bconf c m b (hash n cost) merc-conf btr mtr)
            (privk "sig" b)) (pubk "enc" m)))
      (send
        (cat
          (sign (bconf c m b (hash n cost) merc-conf btr mtr)
            (privk "sig" b))
          (sign (mconf c m b (hash n item cost) bank-conf btr mtr)
            (privk "sig" m))))))
  (label 7)
  (parent 0)
  (realized)
  (shape)
  (maps
    ((0)
      ((c c) (m m) (b b) (n n) (cost cost) (item item)
        (merc-conf merc-conf) (bank-conf bank-conf) (btr btr) (mtr mtr)
        (account account))))
  (origs (mtr (2 1)) (btr (1 1)) (n (0 0))))
>>>
minipay-test-relies.tst
<<< minipay-test-relies.tst:137:1: 
(defskeleton minipay-rely-guar
  (vars (cost amount) (n account data) (item merchandise)
    (mtr btr merc-conf bank-conf text) (c m b name))
  (defstrand cust 3 (cost cost) (account account) (n n) (item item)
    (merc-conf merc-conf) (bank-conf bank-conf) (btr btr) (mtr mtr)
    (c c) (m m) (b b))
  (non-orig (privk "enc" m) (privk "enc" b) (privk "sig" m)
    (privk "sig" b))
  (facts (buy-via c m b item cost n))
  (rule guar-cust-1)
  (traces
    ((send
       (enc n cost item merc-conf (hash n bank-conf)
         (sign
           (order c m b cost
             (enc n cost account bank-conf (hash n merc-conf)
               (pubk "enc" b))) (privk "sig" c)) (pubk "enc" m)))
      (recv
        (sign (bconf c m b (hash n cost) merc-conf btr mtr)
          (privk "sig" b)))
      (recv
        (sign (mconf c m b (hash n item cost) bank-conf btr mtr)
          (privk "sig" m)))))
  (label 1)
  (parent 0)
  (unrealized (0 1) (0 2))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))
<<<
>>> minipay-test-relies.txt:137:1: 
(defskeleton minipay-rely-guar
  (vars (cost amount) (n account data) (item merchandise)
    (mtr btr merc-conf bank-conf text) (c m b name))
  (defstrand cust 3 (cost cost) (account account) (n n) (item item)
    (merc-conf merc-conf) (bank-conf bank-conf) (btr btr) (mtr mtr)
    (c c) (m m) (b b))
  (non-orig (privk "enc" m) (privk "enc" b) (privk "sig" m)
    (privk "sig" b))
  (facts (buy-via c m b item cost n))
  (traces
    ((send
       (enc n cost item merc-conf (hash n bank-conf)
         (sign
           (order c m b cost
             (enc n cost account bank-conf (hash n merc-conf)
               (pubk "enc" b))) (privk "sig" c)) (pubk "enc" m)))
      (recv
        (sign (bconf c m b (hash n cost) merc-conf btr mtr)
          (privk "sig" b)))
      (recv
        (sign (mconf c m b (hash n item cost) bank-conf btr mtr)
          (privk "sig" m)))))
  (label 1)
  (parent 0)
  (unrealized (0 1) (0 2))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))
>>>
minipay.tst
minipay_shapes.tst
ns.tst
ns_shapes.tst
open-closed-late-destructure.tst
<<< open-closed-late-destructure.tst:264:1: 
(defskeleton subatomic-open-closed
  (vars (old old1 mesg) (k skey) (d o name) (pt pt-0 pt-1 pt-2 pval)
    (start-ch chan) (lk ls locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (deflistener k)
  (defstrand dev-up 5 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls))
  (precedes ((0 0) (2 0)) ((2 4) (1 0)))
  (uniq-orig k)
  (conf start-ch)
  (auth start-ch)
  (facts (trans 2 4) (trans 2 2) (same-dev ls lk) (trans 2 3)
    (trans 2
      1)) fact-dev-up-same-dev0 trRl_dev-up-at-3 trRl_dev-up-at-1)
<<<
>>> open-closed-late-destructure.txt:264:1: 
(defskeleton subatomic-open-closed
  (vars (old old1 mesg) (k skey) (d o name) (pt pt-0 pt-1 pt-2 pval)
    (start-ch chan) (lk ls locn))
  (defstrand owner-power-dev 2 (k k) (d d) (o o) (start-ch start-ch))
  (deflistener k)
  (defstrand dev-up 5 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls))
  (precedes ((0 0) (2 0)) ((2 4) (1 0)))
  (uniq-orig k)
  (conf start-ch)
  (auth start-ch)
  (facts (trans 2 4) (trans 2 2) (same-dev ls lk) (trans 2 3)
    (trans 2 1))
  (operation nonce-test (added-strand dev-up 4) k (1 0)
    (ch-msg start-ch (cat "power-up" d o k)))
  (traces ((send start-ch (cat "power-up" d o k)) (recv (enc "up" k)))
    ((recv k) (send k))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt old))
      (load ls (cat pt-0 old1))
      (stor lk (cat pt-1 (dev-key-state d o k)))
      (stor ls (cat pt-2 (door-state d (closed o))))))
  (label 2)
  (parent 1)
  (seen 2)
  (unrealized (0 1) (1 0))
  (comment "1 in cohort - 0 not yet seen"))
>>>
open-closed-late-destructure_shapes.tst
<<< open-closed-late-destructure_shapes.tst:498:1: 
(defskeleton subatomic-open-closed
  (vars (old old1 any mesg) (k skey) (n nb text) (b d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (start-ch chan) (ls lk locn))
  (defstrand dev-pass 4 (k k) (n n) (nb nb) (d d) (o o) (b b) (lk lk)
    (ls ls))
  (defstrand dev-up 5 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls))
  (defstrand owner-power-dev 1 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-open 4 (any any)
    (request (enc (open-req b d o nb n) (hash-dk b nb n k))) (k k) (n n)
    (nb nb) (d d) (o o) (b b) (lk lk) (ls ls))
  (precedes ((1 4) (3 1)) ((2 0) (1 0)) ((3 3) (0 0)))
  (gen-st (dev-key-state d o k) (door-state d (opened b nb n)))
  (conf start-ch)
  (auth start-ch)
  (facts (same-dev ls lk) (trans 3 3) (trans 3 1) (trans 1 4)
    (trans 1 2) (trans 1 3) (trans 1 1))
  (operation channel-test (displaced 4 1 dev-up 4)
    (ch-msg lk (cat pt-5 (dev-key-state d o-0 k-0))) (3 2))
  (traces
    ((load lk (cat pt-2 (dev-key-state d o k)))
      (load ls (cat pt (door-state d (opened b nb n))))
      (recv (cat b nb n (enc "may I pass" (hash-dk b nb n k))))
      (send (enc "you may pass" n (hash-dk b nb n k))))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (load ls (cat pt-1 old1))
      (stor lk (cat pt-2 (dev-key-state d o k)))
      (stor ls (cat pt-3 (door-state d (closed o)))))
    ((send start-ch (cat "power-up" d o k)))
    ((recv (cat b n nb (enc (open-req b d o nb n) (hash-dk b nb n k))))
      (load ls (cat pt-4 (door-state d any)))
      (load lk (cat pt-2 (dev-key-state d o k)))
      (stor ls (cat pt (door-state d (opened b nb n))))))
  (label 8)
  (parent 3)
  (realized)
  (shape)
  (maps
    ((0)
      ((k k) (n n) (nb nb) (d d) (o o) (b b) (lk lk) (ls ls) (pt pt-2)
        (pt-0 pt))))
  (origs (pt-2 (1 3)) (pt (3 3)) (pt-3 (1 4))))
<<<
>>> open-closed-late-destructure_shapes.txt:498:1: 
(defskeleton subatomic-open-closed
  (vars (old old1 any mesg) (k skey) (n nb text) (b d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (start-ch chan) (ls lk locn))
  (defstrand dev-pass 4 (k k) (n n) (nb nb) (d d) (o o) (b b) (lk lk)
    (ls ls))
  (defstrand dev-up 5 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls))
  (defstrand owner-power-dev 1 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-open 4 (any any)
    (request (enc (open-req b d o nb n) (hash-dk b nb n k))) (k k) (n n)
    (nb nb) (d d) (o o) (b b) (lk lk) (ls ls))
  (precedes ((1 4) (3 1)) ((2 0) (1 0)) ((3 3) (0 0)))
  (gen-st (dev-key-state d o k) (door-state d (opened b nb n)))
  (conf start-ch)
  (auth start-ch)
  (facts (same-dev ls lk) (trans 1 4) (trans 1 3) (trans 1 2)
    (trans 1 1) (trans 3 3) (trans 3 1))
  (operation channel-test (displaced 4 1 dev-up 4)
    (ch-msg lk (cat pt-5 (dev-key-state d o-0 k-0))) (3 2))
  (traces
    ((load lk (cat pt-2 (dev-key-state d o k)))
      (load ls (cat pt (door-state d (opened b nb n))))
      (recv (cat b nb n (enc "may I pass" (hash-dk b nb n k))))
      (send (enc "you may pass" n (hash-dk b nb n k))))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (load ls (cat pt-1 old1))
      (stor lk (cat pt-2 (dev-key-state d o k)))
      (stor ls (cat pt-3 (door-state d (closed o)))))
    ((send start-ch (cat "power-up" d o k)))
    ((recv (cat b n nb (enc (open-req b d o nb n) (hash-dk b nb n k))))
      (load ls (cat pt-4 (door-state d any)))
      (load lk (cat pt-2 (dev-key-state d o k)))
      (stor ls (cat pt (door-state d (opened b nb n))))))
  (label 8)
  (parent 3)
  (realized)
  (shape)
  (maps
    ((0)
      ((k k) (n n) (nb nb) (d d) (o o) (b b) (lk lk) (ls ls) (pt pt-2)
        (pt-0 pt))))
  (origs (pt-2 (1 3)) (pt (3 3)) (pt-3 (1 4))))
>>>
open-closed.tst
open-closed_shapes.tst
<<< open-closed_shapes.tst:466:1: 
(defskeleton open-closed
  (vars (old old1 any mesg) (k skey) (n nb text) (b d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (start-ch chan) (ls lk locn))
  (defstrand dev-pass 4 (k k) (n n) (nb nb) (d d) (o o) (b b) (lk lk)
    (ls ls))
  (defstrand dev-up 5 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls))
  (defstrand owner-power-dev 1 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-open 5 (any any) (k k) (n n) (nb nb) (d d) (o o) (b b)
    (lk lk) (ls ls))
  (precedes ((1 4) (3 0)) ((2 0) (1 0)) ((3 4) (0 0)))
  (gen-st (dev-key-state d o k) (door-state d (opened b nb n)))
  (conf start-ch)
  (auth start-ch)
  (facts (same-dev ls lk) (trans 1 4) (trans 1 3) (trans 1 2)
    (trans 1 1) (trans 3 4) (trans 3 2))
  (rule fact-dev-pass-same-dev0 trRl_dev-up-at-4 trRl_dev-up-at-3
    trRl_dev-up-at-2 trRl_dev-up-at-1 trRl_dev-open-at-4
    trRl_dev-open-at-2)
  (operation channel-test (displaced 4 1 dev-up 4)
    (ch-msg lk (cat pt-5 (dev-key-state d o k))) (3 3))
  (traces
    ((load lk (cat pt-2 (dev-key-state d o k)))
      (load ls (cat pt (door-state d (opened b nb n))))
      (recv (cat b nb n (enc "may I pass" (hash-dk b nb n k))))
      (send (enc "you may pass" n (hash-dk b nb n k))))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (load ls (cat pt-1 old1))
      (stor lk (cat pt-2 (dev-key-state d o k)))
      (stor ls (cat pt-3 (door-state d (closed o)))))
    ((send start-ch (cat "power-up" d o k)))
    ((load lk (cat pt-2 (dev-key-state d o k)))
      (recv (cat b n (enc (open-req b d o nb n) (hash-dk b nb n k))))
      (load ls (cat pt-4 (door-state d any)))
      (load lk (cat pt-2 (dev-key-state d o k)))
      (stor ls (cat pt (door-state d (opened b nb n))))))
  (label 10)
  (parent 3)
  (realized)
  (shape)
  (maps
    ((0)
      ((k k) (n n) (nb nb) (d d) (o o) (b b) (lk lk) (ls ls) (pt pt-2)
        (pt-0 pt))))
  (origs (pt-2 (1 3)) (pt-3 (1 4)) (pt (3 4))))
<<<
>>> open-closed_shapes.txt:466:1: 
(defskeleton open-closed
  (vars (old old1 any mesg) (k skey) (n nb text) (b d o name)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval) (start-ch chan) (ls lk locn))
  (defstrand dev-pass 4 (k k) (n n) (nb nb) (d d) (o o) (b b) (lk lk)
    (ls ls))
  (defstrand dev-up 5 (old old) (old1 old1) (k k) (d d) (o o)
    (start-ch start-ch) (lk lk) (ls ls))
  (defstrand owner-power-dev 1 (k k) (d d) (o o) (start-ch start-ch))
  (defstrand dev-open 5 (any any) (k k) (n n) (nb nb) (d d) (o o) (b b)
    (lk lk) (ls ls))
  (precedes ((1 4) (3 0)) ((2 0) (1 0)) ((3 4) (0 0)))
  (gen-st (dev-key-state d o k) (door-state d (opened b nb n)))
  (conf start-ch)
  (auth start-ch)
  (facts (same-dev ls lk) (trans 1 4) (trans 1 3) (trans 1 2)
    (trans 1 1) (trans 3 4) (trans 3 2))
  (operation channel-test (displaced 4 1 dev-up 4)
    (ch-msg lk (cat pt-5 (dev-key-state d o k))) (3 3))
  (traces
    ((load lk (cat pt-2 (dev-key-state d o k)))
      (load ls (cat pt (door-state d (opened b nb n))))
      (recv (cat b nb n (enc "may I pass" (hash-dk b nb n k))))
      (send (enc "you may pass" n (hash-dk b nb n k))))
    ((recv start-ch (cat "power-up" d o k)) (load lk (cat pt-0 old))
      (load ls (cat pt-1 old1))
      (stor lk (cat pt-2 (dev-key-state d o k)))
      (stor ls (cat pt-3 (door-state d (closed o)))))
    ((send start-ch (cat "power-up" d o k)))
    ((load lk (cat pt-2 (dev-key-state d o k)))
      (recv (cat b n (enc (open-req b d o nb n) (hash-dk b nb n k))))
      (load ls (cat pt-4 (door-state d any)))
      (load lk (cat pt-2 (dev-key-state d o k)))
      (stor ls (cat pt (door-state d (opened b nb n))))))
  (label 10)
  (parent 3)
  (realized)
  (shape)
  (maps
    ((0)
      ((k k) (n n) (nb nb) (d d) (o o) (b b) (lk lk) (ls ls) (pt pt-2)
        (pt-0 pt))))
  (origs (pt-2 (1 3)) (pt-3 (1 4)) (pt (3 4))))
>>>
or.tst
or_shapes.tst
pkinit.tst
pkinit_shapes.tst
plaindh.tst
plaindh_shapes.tst
