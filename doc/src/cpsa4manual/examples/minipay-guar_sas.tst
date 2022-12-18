(herald minipay-guar (try-old-strands) (bound 16))

(comment "CPSA 4.4.0")
(comment "All input read from minipay-guar_sas.scm")
(comment "Strand count bounded at 16")
(comment "Old strands tried first")

(defprotocol minipay-guar basic
  (defrole cust
    (vars (c m b name) (cost amount) (item merchandise)
      (merc-conf bank-conf btr mtr text) (account acct)
      (n ncb ncm data))
    (trace
      (send
        (enc n cost item merc-conf ncm (hash n (hash ncb bank-conf))
          (sign
            (order c m b cost
              (enc n cost account bank-conf ncb
                (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
            (privk "sig" c)) (pubk "enc" m)))
      (recv
        (sign
          (bconf (hash c m b n cost (hash n (hash ncm item merc-conf)))
            btr mtr) (privk "sig" b)))
      (recv
        (sign
          (mconf (hash c m b n item cost (hash n (hash ncb bank-conf)))
            btr mtr) (privk "sig" m))))
    (facts (neq n ncb) (neq n ncm) (neq ncm ncb)))
  (defrole merc
    (vars (c m b name) (cost amount) (item merchandise)
      (merc-conf btr mtr text) (n ncm data)
      (for-bank bank-conf-commit bank-conf-decommit mesg))
    (trace
      (recv
        (enc n cost item merc-conf ncm bank-conf-commit
          (sign (order c m b cost for-bank) (privk "sig" c))
          (pubk "enc" m)))
      (send
        (enc
          (payreq c m b (hash cost n) (hash ncm item merc-conf) mtr
            (cat (sign (order c m b cost for-bank) (privk "sig" c))
              for-bank)) (pubk "enc" b)))
      (recv
        (enc bank-conf-decommit
          (sign
            (bconf
              (hash c m b n cost (hash n (hash ncm item merc-conf))) btr
              mtr) (privk "sig" b)) (pubk "enc" m)))
      (send
        (sign
          (bconf (hash c m b n cost (hash n (hash ncm item merc-conf)))
            btr mtr) (privk "sig" b)))
      (send
        (sign
          (mconf (hash c m b n item cost (hash n bank-conf-decommit))
            btr mtr) (privk "sig" m))))
    (uniq-orig mtr))
  (defrole bank
    (vars (c m b name) (cost amount) (bank-conf btr mtr text)
      (merc-conf-decommit mesg) (account acct) (n ncb data))
    (trace
      (recv
        (enc
          (payreq c m b (hash cost n) merc-conf-decommit mtr
            (cat
              (sign
                (order c m b cost
                  (enc n cost account bank-conf ncb
                    (hash n merc-conf-decommit) (pubk "enc" b)))
                (privk "sig" c))
              (enc n cost account bank-conf ncb
                (hash n merc-conf-decommit) (pubk "enc" b))))
          (pubk "enc" b)))
      (send
        (enc (hash ncb bank-conf)
          (sign
            (bconf (hash c m b n cost (hash n merc-conf-decommit)) btr
              mtr) (privk "sig" b)) (pubk "enc" m))))
    (uniq-orig btr))
  (defrule guar-cust-1
    (forall
      ((z strd) (n data) (cost amount) (item merchandise) (b m c name))
      (implies
        (and (p "cust" z (idx 1)) (p "cust" "n" z n)
          (p "cust" "cost" z cost) (p "cust" "item" z item)
          (p "cust" "b" z b) (p "cust" "m" z m) (p "cust" "c" z c))
        (fact buy-via c m b item cost n))))
  (defrule guar-merc-4
    (forall ((z strd) (mtr text) (item merchandise) (b m c name))
      (implies
        (and (p "merc" z (idx 4)) (p "merc" "mtr" z mtr)
          (p "merc" "item" z item) (p "merc" "b" z b) (p "merc" "m" z m)
          (p "merc" "c" z c))
        (fact will-ship c m b item mtr))))
  (defrule guar-bank-2
    (forall
      ((z strd) (btr mtr text) (n data) (cost amount) (c b m name))
      (implies
        (and (p "bank" z (idx 2)) (p "bank" "btr" z btr)
          (p "bank" "mtr" z mtr) (p "bank" "n" z n)
          (p "bank" "cost" z cost) (p "bank" "c" z c) (p "bank" "b" z b)
          (p "bank" "m" z m))
        (and (non (privk "sig" c))
          (fact will-transfer c m b cost n mtr btr)))))
  (defrule cheq-merc-4
    (forall
      ((z strd) (n data) (bank-conf-decommit bank-conf-commit mesg))
      (implies
        (and (p "merc" z (idx 4)) (p "merc" "n" z n)
          (p "merc" "bank-conf-decommit" z bank-conf-decommit)
          (p "merc" "bank-conf-commit" z bank-conf-commit))
        (= bank-conf-commit (hash n bank-conf-decommit)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule fact-cust-neq2
    (forall ((z strd) (ncb n data))
      (implies
        (and (p "cust" z (idx 1)) (p "cust" "ncb" z ncb)
          (p "cust" "n" z n)) (fact neq n ncb))))
  (defgenrule fact-cust-neq1
    (forall ((z strd) (ncm n data))
      (implies
        (and (p "cust" z (idx 1)) (p "cust" "ncm" z ncm)
          (p "cust" "n" z n)) (fact neq n ncm))))
  (defgenrule fact-cust-neq0
    (forall ((z strd) (ncb ncm data))
      (implies
        (and (p "cust" z (idx 1)) (p "cust" "ncb" z ncb)
          (p "cust" "ncm" z ncm)) (fact neq ncm ncb))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule fact-cust-neq2
    (forall ((z strd) (ncb n data))
      (implies
        (and (p "cust" z (idx 1)) (p "cust" "ncb" z ncb)
          (p "cust" "n" z n)) (fact neq n ncb))))
  (defgenrule fact-cust-neq1
    (forall ((z strd) (ncm n data))
      (implies
        (and (p "cust" z (idx 1)) (p "cust" "ncm" z ncm)
          (p "cust" "n" z n)) (fact neq n ncm))))
  (defgenrule fact-cust-neq0
    (forall ((z strd) (ncb ncm data))
      (implies
        (and (p "cust" z (idx 1)) (p "cust" "ncb" z ncb)
          (p "cust" "ncm" z ncm)) (fact neq ncm ncb))))
  (lang (acct atom) (amount atom) (merchandise atom) (sign sign)
    (order (tuple 5)) (bconf (tuple 3)) (mconf (tuple 3))
    (payreq (tuple 7))))

(defskeleton minipay-guar
  (vars (account acct) (cost amount) (n ncb ncm data) (item merchandise)
    (mtr btr merc-conf bank-conf text) (c m b name))
  (defstrand cust 2 (account account) (cost cost) (n n) (ncb ncb)
    (ncm ncm) (item item) (merc-conf merc-conf) (bank-conf bank-conf)
    (btr btr) (mtr mtr) (c c) (m m) (b b))
  (non-orig (privk "sig" b))
  (goals
    (forall
      ((account acct) (cost amount) (n ncb ncm data) (item merchandise)
        (mtr btr merc-conf bank-conf text) (c m b name) (z strd))
      (implies
        (and (p "cust" z 2) (p "cust" "account" z account)
          (p "cust" "cost" z cost) (p "cust" "n" z n)
          (p "cust" "ncb" z ncb) (p "cust" "ncm" z ncm)
          (p "cust" "item" z item) (p "cust" "merc-conf" z merc-conf)
          (p "cust" "bank-conf" z bank-conf) (p "cust" "btr" z btr)
          (p "cust" "mtr" z mtr) (p "cust" "c" z c) (p "cust" "m" z m)
          (p "cust" "b" z b) (non (privk "sig" b)))
        (or
          (exists ((z-0 strd))
            (and (p "bank" z-0 2)
              (p "bank" "merc-conf-decommit" z-0
                (hash ncm item merc-conf))
              (p "bank" "account" z-0 account)
              (p "bank" "cost" z-0 cost) (p "bank" "n" z-0 n)
              (p "bank" "ncb" z-0 ncb)
              (p "bank" "bank-conf" z-0 bank-conf)
              (p "bank" "btr" z-0 btr) (p "bank" "mtr" z-0 mtr)
              (p "bank" "c" z-0 c) (p "bank" "m" z-0 m)
              (p "bank" "b" z-0 b) (prec z 0 z-0 0) (prec z-0 1 z 1)
              (non (privk "sig" c)) (uniq-at btr z-0 1) (fact neq n ncb)
              (fact neq n ncm) (fact neq ncm ncb)
              (fact buy-via c m b item cost n)
              (fact will-transfer c m b cost n mtr btr)))
          (exists
            ((account-0 acct) (ncb-0 data) (bank-conf-0 text)
              (z-0 z-1 strd))
            (and (p "bank" z-0 2) (p "cust" z-1 1)
              (p "bank" "merc-conf-decommit" z-0
                (hash ncm item merc-conf))
              (p "bank" "account" z-0 account-0)
              (p "bank" "cost" z-0 cost) (p "bank" "n" z-0 n)
              (p "bank" "ncb" z-0 ncb-0)
              (p "bank" "bank-conf" z-0 bank-conf-0)
              (p "bank" "btr" z-0 btr) (p "bank" "mtr" z-0 mtr)
              (p "bank" "c" z-0 c) (p "bank" "m" z-0 m)
              (p "bank" "b" z-0 b) (p "cust" "account" z-1 account-0)
              (p "cust" "cost" z-1 cost) (p "cust" "n" z-1 n)
              (p "cust" "ncb" z-1 ncb-0) (p "cust" "ncm" z-1 ncm)
              (p "cust" "item" z-1 item)
              (p "cust" "merc-conf" z-1 merc-conf)
              (p "cust" "bank-conf" z-1 bank-conf-0)
              (p "cust" "c" z-1 c) (p "cust" "m" z-1 m)
              (p "cust" "b" z-1 b) (prec z-0 1 z 1) (prec z-1 0 z-0 0)
              (non (privk "sig" c)) (uniq-at btr z-0 1)
              (fact neq n ncb-0) (fact neq n ncb) (fact neq n ncm)
              (fact neq ncm ncb-0) (fact neq ncm ncb)
              (fact buy-via c m b item cost n)
              (fact will-transfer c m b cost n mtr btr)))))))
  (traces
    ((send
       (enc n cost item merc-conf ncm (hash n (hash ncb bank-conf))
         (sign
           (order c m b cost
             (enc n cost account bank-conf ncb
               (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
           (privk "sig" c)) (pubk "enc" m)))
      (recv
        (sign
          (bconf (hash c m b n cost (hash n (hash ncm item merc-conf)))
            btr mtr) (privk "sig" b)))))
  (label 0)
  (unrealized (0 1))
  (origs)
  (comment "Not closed under rules"))

(defskeleton minipay-guar
  (vars (account acct) (cost amount) (n ncb ncm data) (item merchandise)
    (mtr btr merc-conf bank-conf text) (c m b name))
  (defstrand cust 2 (account account) (cost cost) (n n) (ncb ncb)
    (ncm ncm) (item item) (merc-conf merc-conf) (bank-conf bank-conf)
    (btr btr) (mtr mtr) (c c) (m m) (b b))
  (non-orig (privk "sig" b))
  (facts (buy-via c m b item cost n) (neq n ncb) (neq n ncm)
    (neq ncm ncb))
  (rule fact-cust-neq0 fact-cust-neq1 fact-cust-neq2 guar-cust-1)
  (traces
    ((send
       (enc n cost item merc-conf ncm (hash n (hash ncb bank-conf))
         (sign
           (order c m b cost
             (enc n cost account bank-conf ncb
               (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
           (privk "sig" c)) (pubk "enc" m)))
      (recv
        (sign
          (bconf (hash c m b n cost (hash n (hash ncm item merc-conf)))
            btr mtr) (privk "sig" b)))))
  (label 1)
  (parent 0)
  (unrealized (0 1))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton minipay-guar
  (vars (account account-0 acct) (cost amount) (n ncb ncm ncb-0 data)
    (item merchandise) (mtr btr merc-conf bank-conf bank-conf-0 text)
    (c m b name))
  (defstrand cust 2 (account account) (cost cost) (n n) (ncb ncb)
    (ncm ncm) (item item) (merc-conf merc-conf) (bank-conf bank-conf)
    (btr btr) (mtr mtr) (c c) (m m) (b b))
  (defstrand bank 2 (merc-conf-decommit (hash ncm item merc-conf))
    (account account-0) (cost cost) (n n) (ncb ncb-0)
    (bank-conf bank-conf-0) (btr btr) (mtr mtr) (c c) (m m) (b b))
  (precedes ((1 1) (0 1)))
  (non-orig (privk "sig" c) (privk "sig" b))
  (uniq-orig btr)
  (facts (buy-via c m b item cost n)
    (will-transfer c m b cost n mtr btr) (neq n ncb) (neq n ncm)
    (neq ncm ncb))
  (rule fact-cust-neq0 fact-cust-neq1 fact-cust-neq2 guar-bank-2
    guar-cust-1)
  (operation encryption-test (added-strand bank 2)
    (sign
      (bconf (hash c m b n cost (hash n (hash ncm item merc-conf))) btr
        mtr) (privk "sig" b)) (0 1))
  (traces
    ((send
       (enc n cost item merc-conf ncm (hash n (hash ncb bank-conf))
         (sign
           (order c m b cost
             (enc n cost account bank-conf ncb
               (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
           (privk "sig" c)) (pubk "enc" m)))
      (recv
        (sign
          (bconf (hash c m b n cost (hash n (hash ncm item merc-conf)))
            btr mtr) (privk "sig" b))))
    ((recv
       (enc
         (payreq c m b (hash cost n) (hash ncm item merc-conf) mtr
           (cat
             (sign
               (order c m b cost
                 (enc n cost account-0 bank-conf-0 ncb-0
                   (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
               (privk "sig" c))
             (enc n cost account-0 bank-conf-0 ncb-0
               (hash n (hash ncm item merc-conf)) (pubk "enc" b))))
         (pubk "enc" b)))
      (send
        (enc (hash ncb-0 bank-conf-0)
          (sign
            (bconf
              (hash c m b n cost (hash n (hash ncm item merc-conf))) btr
              mtr) (privk "sig" b)) (pubk "enc" m)))))
  (label 2)
  (parent 1)
  (unrealized (1 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton minipay-guar
  (vars (account acct) (cost amount) (n ncb ncm data) (item merchandise)
    (mtr btr merc-conf bank-conf text) (c m b name))
  (defstrand cust 2 (account account) (cost cost) (n n) (ncb ncb)
    (ncm ncm) (item item) (merc-conf merc-conf) (bank-conf bank-conf)
    (btr btr) (mtr mtr) (c c) (m m) (b b))
  (defstrand bank 2 (merc-conf-decommit (hash ncm item merc-conf))
    (account account) (cost cost) (n n) (ncb ncb) (bank-conf bank-conf)
    (btr btr) (mtr mtr) (c c) (m m) (b b))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk "sig" c) (privk "sig" b))
  (uniq-orig btr)
  (facts (buy-via c m b item cost n)
    (will-transfer c m b cost n mtr btr) (neq n ncb) (neq n ncm)
    (neq ncm ncb))
  (rule fact-cust-neq0 fact-cust-neq1 fact-cust-neq2 guar-bank-2
    guar-cust-1)
  (operation encryption-test (displaced 2 0 cust 1)
    (sign
      (order c m b cost
        (enc n cost account-0 bank-conf-0 ncb-0
          (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
      (privk "sig" c)) (1 0))
  (traces
    ((send
       (enc n cost item merc-conf ncm (hash n (hash ncb bank-conf))
         (sign
           (order c m b cost
             (enc n cost account bank-conf ncb
               (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
           (privk "sig" c)) (pubk "enc" m)))
      (recv
        (sign
          (bconf (hash c m b n cost (hash n (hash ncm item merc-conf)))
            btr mtr) (privk "sig" b))))
    ((recv
       (enc
         (payreq c m b (hash cost n) (hash ncm item merc-conf) mtr
           (cat
             (sign
               (order c m b cost
                 (enc n cost account bank-conf ncb
                   (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
               (privk "sig" c))
             (enc n cost account bank-conf ncb
               (hash n (hash ncm item merc-conf)) (pubk "enc" b))))
         (pubk "enc" b)))
      (send
        (enc (hash ncb bank-conf)
          (sign
            (bconf
              (hash c m b n cost (hash n (hash ncm item merc-conf))) btr
              mtr) (privk "sig" b)) (pubk "enc" m)))))
  (label 3)
  (parent 2)
  (realized)
  (shape)
  (satisfies yes)
  (maps
    ((0)
      ((account account) (cost cost) (n n) (ncb ncb) (ncm ncm)
        (item item) (mtr mtr) (btr btr) (merc-conf merc-conf)
        (bank-conf bank-conf) (c c) (m m) (b b))))
  (origs (btr (1 1))))

(defskeleton minipay-guar
  (vars (account account-0 acct) (cost amount) (n ncb ncm ncb-0 data)
    (item merchandise) (mtr btr merc-conf bank-conf bank-conf-0 text)
    (c m b name))
  (defstrand cust 2 (account account) (cost cost) (n n) (ncb ncb)
    (ncm ncm) (item item) (merc-conf merc-conf) (bank-conf bank-conf)
    (btr btr) (mtr mtr) (c c) (m m) (b b))
  (defstrand bank 2 (merc-conf-decommit (hash ncm item merc-conf))
    (account account-0) (cost cost) (n n) (ncb ncb-0)
    (bank-conf bank-conf-0) (btr btr) (mtr mtr) (c c) (m m) (b b))
  (defstrand cust 1 (account account-0) (cost cost) (n n) (ncb ncb-0)
    (ncm ncm) (item item) (merc-conf merc-conf) (bank-conf bank-conf-0)
    (c c) (m m) (b b))
  (precedes ((1 1) (0 1)) ((2 0) (1 0)))
  (non-orig (privk "sig" c) (privk "sig" b))
  (uniq-orig btr)
  (facts (buy-via c m b item cost n)
    (will-transfer c m b cost n mtr btr) (neq n ncb-0) (neq n ncb)
    (neq n ncm) (neq ncm ncb-0) (neq ncm ncb))
  (rule fact-cust-neq0 fact-cust-neq1 fact-cust-neq2 guar-bank-2
    guar-cust-1)
  (operation encryption-test (added-strand cust 1)
    (sign
      (order c m b cost
        (enc n cost account-0 bank-conf-0 ncb-0
          (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
      (privk "sig" c)) (1 0))
  (traces
    ((send
       (enc n cost item merc-conf ncm (hash n (hash ncb bank-conf))
         (sign
           (order c m b cost
             (enc n cost account bank-conf ncb
               (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
           (privk "sig" c)) (pubk "enc" m)))
      (recv
        (sign
          (bconf (hash c m b n cost (hash n (hash ncm item merc-conf)))
            btr mtr) (privk "sig" b))))
    ((recv
       (enc
         (payreq c m b (hash cost n) (hash ncm item merc-conf) mtr
           (cat
             (sign
               (order c m b cost
                 (enc n cost account-0 bank-conf-0 ncb-0
                   (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
               (privk "sig" c))
             (enc n cost account-0 bank-conf-0 ncb-0
               (hash n (hash ncm item merc-conf)) (pubk "enc" b))))
         (pubk "enc" b)))
      (send
        (enc (hash ncb-0 bank-conf-0)
          (sign
            (bconf
              (hash c m b n cost (hash n (hash ncm item merc-conf))) btr
              mtr) (privk "sig" b)) (pubk "enc" m))))
    ((send
       (enc n cost item merc-conf ncm (hash n (hash ncb-0 bank-conf-0))
         (sign
           (order c m b cost
             (enc n cost account-0 bank-conf-0 ncb-0
               (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
           (privk "sig" c)) (pubk "enc" m)))))
  (label 4)
  (parent 2)
  (realized)
  (shape)
  (satisfies yes)
  (maps
    ((0)
      ((account account) (cost cost) (n n) (ncb ncb) (ncm ncm)
        (item item) (mtr mtr) (btr btr) (merc-conf merc-conf)
        (bank-conf bank-conf) (c c) (m m) (b b))))
  (origs (btr (1 1))))

(comment "Nothing left to do")

(defprotocol minipay-guar basic
  (defrole cust
    (vars (c m b name) (cost amount) (item merchandise)
      (merc-conf bank-conf btr mtr text) (account acct)
      (n ncb ncm data))
    (trace
      (send
        (enc n cost item merc-conf ncm (hash n (hash ncb bank-conf))
          (sign
            (order c m b cost
              (enc n cost account bank-conf ncb
                (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
            (privk "sig" c)) (pubk "enc" m)))
      (recv
        (sign
          (bconf (hash c m b n cost (hash n (hash ncm item merc-conf)))
            btr mtr) (privk "sig" b)))
      (recv
        (sign
          (mconf (hash c m b n item cost (hash n (hash ncb bank-conf)))
            btr mtr) (privk "sig" m))))
    (facts (neq n ncb) (neq n ncm) (neq ncm ncb)))
  (defrole merc
    (vars (c m b name) (cost amount) (item merchandise)
      (merc-conf btr mtr text) (n ncm data)
      (for-bank bank-conf-commit bank-conf-decommit mesg))
    (trace
      (recv
        (enc n cost item merc-conf ncm bank-conf-commit
          (sign (order c m b cost for-bank) (privk "sig" c))
          (pubk "enc" m)))
      (send
        (enc
          (payreq c m b (hash cost n) (hash ncm item merc-conf) mtr
            (cat (sign (order c m b cost for-bank) (privk "sig" c))
              for-bank)) (pubk "enc" b)))
      (recv
        (enc bank-conf-decommit
          (sign
            (bconf
              (hash c m b n cost (hash n (hash ncm item merc-conf))) btr
              mtr) (privk "sig" b)) (pubk "enc" m)))
      (send
        (sign
          (bconf (hash c m b n cost (hash n (hash ncm item merc-conf)))
            btr mtr) (privk "sig" b)))
      (send
        (sign
          (mconf (hash c m b n item cost (hash n bank-conf-decommit))
            btr mtr) (privk "sig" m))))
    (uniq-orig mtr))
  (defrole bank
    (vars (c m b name) (cost amount) (bank-conf btr mtr text)
      (merc-conf-decommit mesg) (account acct) (n ncb data))
    (trace
      (recv
        (enc
          (payreq c m b (hash cost n) merc-conf-decommit mtr
            (cat
              (sign
                (order c m b cost
                  (enc n cost account bank-conf ncb
                    (hash n merc-conf-decommit) (pubk "enc" b)))
                (privk "sig" c))
              (enc n cost account bank-conf ncb
                (hash n merc-conf-decommit) (pubk "enc" b))))
          (pubk "enc" b)))
      (send
        (enc (hash ncb bank-conf)
          (sign
            (bconf (hash c m b n cost (hash n merc-conf-decommit)) btr
              mtr) (privk "sig" b)) (pubk "enc" m))))
    (uniq-orig btr))
  (defrule guar-cust-1
    (forall
      ((z strd) (n data) (cost amount) (item merchandise) (b m c name))
      (implies
        (and (p "cust" z (idx 1)) (p "cust" "n" z n)
          (p "cust" "cost" z cost) (p "cust" "item" z item)
          (p "cust" "b" z b) (p "cust" "m" z m) (p "cust" "c" z c))
        (fact buy-via c m b item cost n))))
  (defrule guar-merc-4
    (forall ((z strd) (mtr text) (item merchandise) (b m c name))
      (implies
        (and (p "merc" z (idx 4)) (p "merc" "mtr" z mtr)
          (p "merc" "item" z item) (p "merc" "b" z b) (p "merc" "m" z m)
          (p "merc" "c" z c))
        (fact will-ship c m b item mtr))))
  (defrule guar-bank-2
    (forall
      ((z strd) (btr mtr text) (n data) (cost amount) (c b m name))
      (implies
        (and (p "bank" z (idx 2)) (p "bank" "btr" z btr)
          (p "bank" "mtr" z mtr) (p "bank" "n" z n)
          (p "bank" "cost" z cost) (p "bank" "c" z c) (p "bank" "b" z b)
          (p "bank" "m" z m))
        (and (non (privk "sig" c))
          (fact will-transfer c m b cost n mtr btr)))))
  (defrule cheq-merc-4
    (forall
      ((z strd) (n data) (bank-conf-decommit bank-conf-commit mesg))
      (implies
        (and (p "merc" z (idx 4)) (p "merc" "n" z n)
          (p "merc" "bank-conf-decommit" z bank-conf-decommit)
          (p "merc" "bank-conf-commit" z bank-conf-commit))
        (= bank-conf-commit (hash n bank-conf-decommit)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule fact-cust-neq2
    (forall ((z strd) (ncb n data))
      (implies
        (and (p "cust" z (idx 1)) (p "cust" "ncb" z ncb)
          (p "cust" "n" z n)) (fact neq n ncb))))
  (defgenrule fact-cust-neq1
    (forall ((z strd) (ncm n data))
      (implies
        (and (p "cust" z (idx 1)) (p "cust" "ncm" z ncm)
          (p "cust" "n" z n)) (fact neq n ncm))))
  (defgenrule fact-cust-neq0
    (forall ((z strd) (ncb ncm data))
      (implies
        (and (p "cust" z (idx 1)) (p "cust" "ncb" z ncb)
          (p "cust" "ncm" z ncm)) (fact neq ncm ncb))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule fact-cust-neq2
    (forall ((z strd) (ncb n data))
      (implies
        (and (p "cust" z (idx 1)) (p "cust" "ncb" z ncb)
          (p "cust" "n" z n)) (fact neq n ncb))))
  (defgenrule fact-cust-neq1
    (forall ((z strd) (ncm n data))
      (implies
        (and (p "cust" z (idx 1)) (p "cust" "ncm" z ncm)
          (p "cust" "n" z n)) (fact neq n ncm))))
  (defgenrule fact-cust-neq0
    (forall ((z strd) (ncb ncm data))
      (implies
        (and (p "cust" z (idx 1)) (p "cust" "ncb" z ncb)
          (p "cust" "ncm" z ncm)) (fact neq ncm ncb))))
  (lang (acct atom) (amount atom) (merchandise atom) (sign sign)
    (order (tuple 5)) (bconf (tuple 3)) (mconf (tuple 3))
    (payreq (tuple 7))))

(defskeleton minipay-guar
  (vars (account acct) (cost amount) (n ncb ncm data) (item merchandise)
    (mtr btr merc-conf bank-conf text) (c m b name))
  (defstrand cust 3 (account account) (cost cost) (n n) (ncb ncb)
    (ncm ncm) (item item) (merc-conf merc-conf) (bank-conf bank-conf)
    (btr btr) (mtr mtr) (c c) (m m) (b b))
  (non-orig (privk "sig" m))
  (goals
    (forall
      ((account acct) (cost amount) (n ncb ncm data) (item merchandise)
        (mtr btr merc-conf bank-conf text) (c m b name) (z strd))
      (implies
        (and (p "cust" z 3) (p "cust" "account" z account)
          (p "cust" "cost" z cost) (p "cust" "n" z n)
          (p "cust" "ncb" z ncb) (p "cust" "ncm" z ncm)
          (p "cust" "item" z item) (p "cust" "merc-conf" z merc-conf)
          (p "cust" "bank-conf" z bank-conf) (p "cust" "btr" z btr)
          (p "cust" "mtr" z mtr) (p "cust" "c" z c) (p "cust" "m" z m)
          (p "cust" "b" z b) (non (privk "sig" m)))
        (exists
          ((for-bank mesg) (ncm-0 data) (merc-conf-0 text) (z-0 strd))
          (and (p "merc" z-0 5) (p "merc" "for-bank" z-0 for-bank)
            (p "merc" "bank-conf-commit" z-0
              (hash n (hash ncb bank-conf)))
            (p "merc" "bank-conf-decommit" z-0 (hash ncb bank-conf))
            (p "merc" "cost" z-0 cost) (p "merc" "n" z-0 n)
            (p "merc" "ncm" z-0 ncm-0) (p "merc" "item" z-0 item)
            (p "merc" "merc-conf" z-0 merc-conf-0)
            (p "merc" "btr" z-0 btr) (p "merc" "mtr" z-0 mtr)
            (p "merc" "c" z-0 c) (p "merc" "m" z-0 m)
            (p "merc" "b" z-0 b) (prec z-0 1 z 1) (prec z-0 4 z 2)
            (uniq-at mtr z-0 1) (fact neq n ncb) (fact neq n ncm)
            (fact neq ncm ncb) (fact buy-via c m b item cost n)
            (fact will-ship c m b item mtr))))))
  (traces
    ((send
       (enc n cost item merc-conf ncm (hash n (hash ncb bank-conf))
         (sign
           (order c m b cost
             (enc n cost account bank-conf ncb
               (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
           (privk "sig" c)) (pubk "enc" m)))
      (recv
        (sign
          (bconf (hash c m b n cost (hash n (hash ncm item merc-conf)))
            btr mtr) (privk "sig" b)))
      (recv
        (sign
          (mconf (hash c m b n item cost (hash n (hash ncb bank-conf)))
            btr mtr) (privk "sig" m)))))
  (label 5)
  (unrealized (0 2))
  (origs)
  (comment "Not closed under rules"))

(defskeleton minipay-guar
  (vars (account acct) (cost amount) (n ncb ncm data) (item merchandise)
    (mtr btr merc-conf bank-conf text) (c m b name))
  (defstrand cust 3 (account account) (cost cost) (n n) (ncb ncb)
    (ncm ncm) (item item) (merc-conf merc-conf) (bank-conf bank-conf)
    (btr btr) (mtr mtr) (c c) (m m) (b b))
  (non-orig (privk "sig" m))
  (facts (buy-via c m b item cost n) (neq n ncb) (neq n ncm)
    (neq ncm ncb))
  (rule fact-cust-neq0 fact-cust-neq1 fact-cust-neq2 guar-cust-1)
  (traces
    ((send
       (enc n cost item merc-conf ncm (hash n (hash ncb bank-conf))
         (sign
           (order c m b cost
             (enc n cost account bank-conf ncb
               (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
           (privk "sig" c)) (pubk "enc" m)))
      (recv
        (sign
          (bconf (hash c m b n cost (hash n (hash ncm item merc-conf)))
            btr mtr) (privk "sig" b)))
      (recv
        (sign
          (mconf (hash c m b n item cost (hash n (hash ncb bank-conf)))
            btr mtr) (privk "sig" m)))))
  (label 6)
  (parent 5)
  (unrealized (0 2))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton minipay-guar
  (vars (for-bank mesg) (account acct) (cost amount)
    (n ncb ncm ncm-0 data) (item merchandise)
    (mtr btr merc-conf bank-conf merc-conf-0 text) (c m b name))
  (defstrand cust 3 (account account) (cost cost) (n n) (ncb ncb)
    (ncm ncm) (item item) (merc-conf merc-conf) (bank-conf bank-conf)
    (btr btr) (mtr mtr) (c c) (m m) (b b))
  (defstrand merc 5 (for-bank for-bank)
    (bank-conf-commit (hash n (hash ncb bank-conf)))
    (bank-conf-decommit (hash ncb bank-conf)) (cost cost) (n n)
    (ncm ncm-0) (item item) (merc-conf merc-conf-0) (btr btr) (mtr mtr)
    (c c) (m m) (b b))
  (precedes ((1 1) (0 1)) ((1 4) (0 2)))
  (non-orig (privk "sig" m))
  (uniq-orig mtr)
  (facts (buy-via c m b item cost n) (will-ship c m b item mtr)
    (neq n ncb) (neq n ncm) (neq ncm ncb))
  (rule cheq-merc-4 fact-cust-neq0 fact-cust-neq1 fact-cust-neq2
    guar-cust-1 guar-merc-4)
  (operation encryption-test (added-strand merc 5)
    (sign
      (mconf (hash c m b n item cost (hash n (hash ncb bank-conf))) btr
        mtr) (privk "sig" m)) (0 2))
  (traces
    ((send
       (enc n cost item merc-conf ncm (hash n (hash ncb bank-conf))
         (sign
           (order c m b cost
             (enc n cost account bank-conf ncb
               (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
           (privk "sig" c)) (pubk "enc" m)))
      (recv
        (sign
          (bconf (hash c m b n cost (hash n (hash ncm item merc-conf)))
            btr mtr) (privk "sig" b)))
      (recv
        (sign
          (mconf (hash c m b n item cost (hash n (hash ncb bank-conf)))
            btr mtr) (privk "sig" m))))
    ((recv
       (enc n cost item merc-conf-0 ncm-0 (hash n (hash ncb bank-conf))
         (sign (order c m b cost for-bank) (privk "sig" c))
         (pubk "enc" m)))
      (send
        (enc
          (payreq c m b (hash cost n) (hash ncm-0 item merc-conf-0) mtr
            (cat (sign (order c m b cost for-bank) (privk "sig" c))
              for-bank)) (pubk "enc" b)))
      (recv
        (enc (hash ncb bank-conf)
          (sign
            (bconf
              (hash c m b n cost (hash n (hash ncm-0 item merc-conf-0)))
              btr mtr) (privk "sig" b)) (pubk "enc" m)))
      (send
        (sign
          (bconf
            (hash c m b n cost (hash n (hash ncm-0 item merc-conf-0)))
            btr mtr) (privk "sig" b)))
      (send
        (sign
          (mconf (hash c m b n item cost (hash n (hash ncb bank-conf)))
            btr mtr) (privk "sig" m)))))
  (label 7)
  (parent 6)
  (realized)
  (shape)
  (satisfies yes)
  (maps
    ((0)
      ((account account) (cost cost) (n n) (ncb ncb) (ncm ncm)
        (item item) (mtr mtr) (btr btr) (merc-conf merc-conf)
        (bank-conf bank-conf) (c c) (m m) (b b))))
  (origs (mtr (1 1))))

(comment "Nothing left to do")

(defprotocol minipay-guar basic
  (defrole cust
    (vars (c m b name) (cost amount) (item merchandise)
      (merc-conf bank-conf btr mtr text) (account acct)
      (n ncb ncm data))
    (trace
      (send
        (enc n cost item merc-conf ncm (hash n (hash ncb bank-conf))
          (sign
            (order c m b cost
              (enc n cost account bank-conf ncb
                (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
            (privk "sig" c)) (pubk "enc" m)))
      (recv
        (sign
          (bconf (hash c m b n cost (hash n (hash ncm item merc-conf)))
            btr mtr) (privk "sig" b)))
      (recv
        (sign
          (mconf (hash c m b n item cost (hash n (hash ncb bank-conf)))
            btr mtr) (privk "sig" m))))
    (facts (neq n ncb) (neq n ncm) (neq ncm ncb)))
  (defrole merc
    (vars (c m b name) (cost amount) (item merchandise)
      (merc-conf btr mtr text) (n ncm data)
      (for-bank bank-conf-commit bank-conf-decommit mesg))
    (trace
      (recv
        (enc n cost item merc-conf ncm bank-conf-commit
          (sign (order c m b cost for-bank) (privk "sig" c))
          (pubk "enc" m)))
      (send
        (enc
          (payreq c m b (hash cost n) (hash ncm item merc-conf) mtr
            (cat (sign (order c m b cost for-bank) (privk "sig" c))
              for-bank)) (pubk "enc" b)))
      (recv
        (enc bank-conf-decommit
          (sign
            (bconf
              (hash c m b n cost (hash n (hash ncm item merc-conf))) btr
              mtr) (privk "sig" b)) (pubk "enc" m)))
      (send
        (sign
          (bconf (hash c m b n cost (hash n (hash ncm item merc-conf)))
            btr mtr) (privk "sig" b)))
      (send
        (sign
          (mconf (hash c m b n item cost (hash n bank-conf-decommit))
            btr mtr) (privk "sig" m))))
    (uniq-orig mtr))
  (defrole bank
    (vars (c m b name) (cost amount) (bank-conf btr mtr text)
      (merc-conf-decommit mesg) (account acct) (n ncb data))
    (trace
      (recv
        (enc
          (payreq c m b (hash cost n) merc-conf-decommit mtr
            (cat
              (sign
                (order c m b cost
                  (enc n cost account bank-conf ncb
                    (hash n merc-conf-decommit) (pubk "enc" b)))
                (privk "sig" c))
              (enc n cost account bank-conf ncb
                (hash n merc-conf-decommit) (pubk "enc" b))))
          (pubk "enc" b)))
      (send
        (enc (hash ncb bank-conf)
          (sign
            (bconf (hash c m b n cost (hash n merc-conf-decommit)) btr
              mtr) (privk "sig" b)) (pubk "enc" m))))
    (uniq-orig btr))
  (defrule guar-cust-1
    (forall
      ((z strd) (n data) (cost amount) (item merchandise) (b m c name))
      (implies
        (and (p "cust" z (idx 1)) (p "cust" "n" z n)
          (p "cust" "cost" z cost) (p "cust" "item" z item)
          (p "cust" "b" z b) (p "cust" "m" z m) (p "cust" "c" z c))
        (fact buy-via c m b item cost n))))
  (defrule guar-merc-4
    (forall ((z strd) (mtr text) (item merchandise) (b m c name))
      (implies
        (and (p "merc" z (idx 4)) (p "merc" "mtr" z mtr)
          (p "merc" "item" z item) (p "merc" "b" z b) (p "merc" "m" z m)
          (p "merc" "c" z c))
        (fact will-ship c m b item mtr))))
  (defrule guar-bank-2
    (forall
      ((z strd) (btr mtr text) (n data) (cost amount) (c b m name))
      (implies
        (and (p "bank" z (idx 2)) (p "bank" "btr" z btr)
          (p "bank" "mtr" z mtr) (p "bank" "n" z n)
          (p "bank" "cost" z cost) (p "bank" "c" z c) (p "bank" "b" z b)
          (p "bank" "m" z m))
        (and (non (privk "sig" c))
          (fact will-transfer c m b cost n mtr btr)))))
  (defrule cheq-merc-4
    (forall
      ((z strd) (n data) (bank-conf-decommit bank-conf-commit mesg))
      (implies
        (and (p "merc" z (idx 4)) (p "merc" "n" z n)
          (p "merc" "bank-conf-decommit" z bank-conf-decommit)
          (p "merc" "bank-conf-commit" z bank-conf-commit))
        (= bank-conf-commit (hash n bank-conf-decommit)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule fact-cust-neq2
    (forall ((z strd) (ncb n data))
      (implies
        (and (p "cust" z (idx 1)) (p "cust" "ncb" z ncb)
          (p "cust" "n" z n)) (fact neq n ncb))))
  (defgenrule fact-cust-neq1
    (forall ((z strd) (ncm n data))
      (implies
        (and (p "cust" z (idx 1)) (p "cust" "ncm" z ncm)
          (p "cust" "n" z n)) (fact neq n ncm))))
  (defgenrule fact-cust-neq0
    (forall ((z strd) (ncb ncm data))
      (implies
        (and (p "cust" z (idx 1)) (p "cust" "ncb" z ncb)
          (p "cust" "ncm" z ncm)) (fact neq ncm ncb))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule fact-cust-neq2
    (forall ((z strd) (ncb n data))
      (implies
        (and (p "cust" z (idx 1)) (p "cust" "ncb" z ncb)
          (p "cust" "n" z n)) (fact neq n ncb))))
  (defgenrule fact-cust-neq1
    (forall ((z strd) (ncm n data))
      (implies
        (and (p "cust" z (idx 1)) (p "cust" "ncm" z ncm)
          (p "cust" "n" z n)) (fact neq n ncm))))
  (defgenrule fact-cust-neq0
    (forall ((z strd) (ncb ncm data))
      (implies
        (and (p "cust" z (idx 1)) (p "cust" "ncb" z ncb)
          (p "cust" "ncm" z ncm)) (fact neq ncm ncb))))
  (lang (acct atom) (amount atom) (merchandise atom) (sign sign)
    (order (tuple 5)) (bconf (tuple 3)) (mconf (tuple 3))
    (payreq (tuple 7))))

(defskeleton minipay-guar
  (vars (for-bank bank-conf-commit bank-conf-decommit mesg)
    (cost amount) (n ncm data) (item merchandise)
    (mtr btr merc-conf text) (c m b name))
  (defstrand merc 3 (for-bank for-bank)
    (bank-conf-commit bank-conf-commit)
    (bank-conf-decommit bank-conf-decommit) (cost cost) (n n) (ncm ncm)
    (item item) (merc-conf merc-conf) (btr btr) (mtr mtr) (c c) (m m)
    (b b))
  (non-orig (privk "sig" b))
  (uniq-orig mtr)
  (goals
    (forall
      ((for-bank bank-conf-commit bank-conf-decommit mesg) (cost amount)
        (n ncm data) (item merchandise) (mtr btr merc-conf text)
        (c m b name) (z strd))
      (implies
        (and (p "merc" z 3) (p "merc" "for-bank" z for-bank)
          (p "merc" "bank-conf-commit" z bank-conf-commit)
          (p "merc" "bank-conf-decommit" z bank-conf-decommit)
          (p "merc" "cost" z cost) (p "merc" "n" z n)
          (p "merc" "ncm" z ncm) (p "merc" "item" z item)
          (p "merc" "merc-conf" z merc-conf) (p "merc" "btr" z btr)
          (p "merc" "mtr" z mtr) (p "merc" "c" z c) (p "merc" "m" z m)
          (p "merc" "b" z b) (non (privk "sig" b)) (uniq-at mtr z 1))
        (or
          (exists
            ((account acct) (ncb data) (bank-conf text) (z-0 z-1 strd))
            (and
              (= for-bank
                (enc n cost account bank-conf ncb
                  (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
              (p "bank" z-0 2) (p "cust" z-1 1)
              (p "merc" "for-bank" z
                (enc n cost account bank-conf ncb
                  (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
              (p "bank" "merc-conf-decommit" z-0
                (hash ncm item merc-conf))
              (p "bank" "account" z-0 account)
              (p "bank" "cost" z-0 cost) (p "bank" "n" z-0 n)
              (p "bank" "ncb" z-0 ncb)
              (p "bank" "bank-conf" z-0 bank-conf)
              (p "bank" "btr" z-0 btr) (p "bank" "mtr" z-0 mtr)
              (p "bank" "c" z-0 c) (p "bank" "m" z-0 m)
              (p "bank" "b" z-0 b) (p "cust" "account" z-1 account)
              (p "cust" "cost" z-1 cost) (p "cust" "n" z-1 n)
              (p "cust" "ncb" z-1 ncb) (p "cust" "ncm" z-1 ncm)
              (p "cust" "item" z-1 item)
              (p "cust" "merc-conf" z-1 merc-conf)
              (p "cust" "bank-conf" z-1 bank-conf) (p "cust" "c" z-1 c)
              (p "cust" "m" z-1 m) (p "cust" "b" z-1 b) (prec z 1 z-0 0)
              (prec z-0 1 z 2) (prec z-1 0 z 0) (non (privk "sig" c))
              (uniq-at btr z-0 1) (fact neq n ncb) (fact neq n ncm)
              (fact neq ncm ncb) (fact buy-via c m b item cost n)
              (fact will-transfer c m b cost n mtr btr)))
          (exists
            ((account account-0 acct) (ncb n-0 ncb-0 ncm-0 data)
              (item-0 merchandise)
              (bank-conf merc-conf-0 bank-conf-0 text)
              (z-0 z-1 z-2 strd))
            (and
              (= for-bank
                (enc n-0 cost account-0 bank-conf-0 ncb-0
                  (hash n-0 (hash ncm-0 item-0 merc-conf-0))
                  (pubk "enc" b))) (p "bank" z-0 2) (p "cust" z-1 1)
              (p "cust" z-2 1)
              (p "merc" "for-bank" z
                (enc n-0 cost account-0 bank-conf-0 ncb-0
                  (hash n-0 (hash ncm-0 item-0 merc-conf-0))
                  (pubk "enc" b)))
              (p "bank" "merc-conf-decommit" z-0
                (hash ncm item merc-conf))
              (p "bank" "account" z-0 account)
              (p "bank" "cost" z-0 cost) (p "bank" "n" z-0 n)
              (p "bank" "ncb" z-0 ncb)
              (p "bank" "bank-conf" z-0 bank-conf)
              (p "bank" "btr" z-0 btr) (p "bank" "mtr" z-0 mtr)
              (p "bank" "c" z-0 c) (p "bank" "m" z-0 m)
              (p "bank" "b" z-0 b) (p "cust" "account" z-1 account-0)
              (p "cust" "cost" z-1 cost) (p "cust" "n" z-1 n-0)
              (p "cust" "ncb" z-1 ncb-0) (p "cust" "ncm" z-1 ncm-0)
              (p "cust" "item" z-1 item-0)
              (p "cust" "merc-conf" z-1 merc-conf-0)
              (p "cust" "bank-conf" z-1 bank-conf-0)
              (p "cust" "c" z-1 c) (p "cust" "m" z-1 m)
              (p "cust" "b" z-1 b) (p "cust" "account" z-2 account)
              (p "cust" "cost" z-2 cost) (p "cust" "n" z-2 n)
              (p "cust" "ncb" z-2 ncb) (p "cust" "ncm" z-2 ncm)
              (p "cust" "item" z-2 item)
              (p "cust" "merc-conf" z-2 merc-conf)
              (p "cust" "bank-conf" z-2 bank-conf) (p "cust" "c" z-2 c)
              (p "cust" "m" z-2 m) (p "cust" "b" z-2 b) (prec z 1 z-0 0)
              (prec z-0 1 z 2) (prec z-1 0 z 0) (prec z-2 0 z-0 0)
              (non (privk "sig" c)) (uniq-at btr z-0 1) (fact neq n ncb)
              (fact neq n-0 ncb-0) (fact neq n ncm) (fact neq n-0 ncm-0)
              (fact neq ncm ncb) (fact neq ncm-0 ncb-0)
              (fact buy-via c m b item cost n)
              (fact buy-via c m b item-0 cost n-0)
              (fact will-transfer c m b cost n mtr btr)))))))
  (traces
    ((recv
       (enc n cost item merc-conf ncm bank-conf-commit
         (sign (order c m b cost for-bank) (privk "sig" c))
         (pubk "enc" m)))
      (send
        (enc
          (payreq c m b (hash cost n) (hash ncm item merc-conf) mtr
            (cat (sign (order c m b cost for-bank) (privk "sig" c))
              for-bank)) (pubk "enc" b)))
      (recv
        (enc bank-conf-decommit
          (sign
            (bconf
              (hash c m b n cost (hash n (hash ncm item merc-conf))) btr
              mtr) (privk "sig" b)) (pubk "enc" m)))))
  (label 8)
  (unrealized (0 2))
  (origs (mtr (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton minipay-guar
  (vars (for-bank bank-conf-commit bank-conf-decommit mesg)
    (account acct) (cost amount) (n ncm ncb data) (item merchandise)
    (mtr btr merc-conf bank-conf text) (c m b name))
  (defstrand merc 3 (for-bank for-bank)
    (bank-conf-commit bank-conf-commit)
    (bank-conf-decommit bank-conf-decommit) (cost cost) (n n) (ncm ncm)
    (item item) (merc-conf merc-conf) (btr btr) (mtr mtr) (c c) (m m)
    (b b))
  (defstrand bank 2 (merc-conf-decommit (hash ncm item merc-conf))
    (account account) (cost cost) (n n) (ncb ncb) (bank-conf bank-conf)
    (btr btr) (mtr mtr) (c c) (m m) (b b))
  (precedes ((0 1) (1 0)) ((1 1) (0 2)))
  (non-orig (privk "sig" c) (privk "sig" b))
  (uniq-orig mtr btr)
  (facts (will-transfer c m b cost n mtr btr))
  (rule guar-bank-2)
  (operation encryption-test (added-strand bank 2)
    (sign
      (bconf (hash c m b n cost (hash n (hash ncm item merc-conf))) btr
        mtr) (privk "sig" b)) (0 2))
  (traces
    ((recv
       (enc n cost item merc-conf ncm bank-conf-commit
         (sign (order c m b cost for-bank) (privk "sig" c))
         (pubk "enc" m)))
      (send
        (enc
          (payreq c m b (hash cost n) (hash ncm item merc-conf) mtr
            (cat (sign (order c m b cost for-bank) (privk "sig" c))
              for-bank)) (pubk "enc" b)))
      (recv
        (enc bank-conf-decommit
          (sign
            (bconf
              (hash c m b n cost (hash n (hash ncm item merc-conf))) btr
              mtr) (privk "sig" b)) (pubk "enc" m))))
    ((recv
       (enc
         (payreq c m b (hash cost n) (hash ncm item merc-conf) mtr
           (cat
             (sign
               (order c m b cost
                 (enc n cost account bank-conf ncb
                   (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
               (privk "sig" c))
             (enc n cost account bank-conf ncb
               (hash n (hash ncm item merc-conf)) (pubk "enc" b))))
         (pubk "enc" b)))
      (send
        (enc (hash ncb bank-conf)
          (sign
            (bconf
              (hash c m b n cost (hash n (hash ncm item merc-conf))) btr
              mtr) (privk "sig" b)) (pubk "enc" m)))))
  (label 9)
  (parent 8)
  (unrealized (0 0) (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton minipay-guar
  (vars (bank-conf-commit bank-conf-decommit mesg)
    (account account-0 acct) (cost amount)
    (n ncm ncb n-0 ncb-0 ncm-0 data) (item item-0 merchandise)
    (mtr btr merc-conf bank-conf merc-conf-0 bank-conf-0 text)
    (c m b name))
  (defstrand merc 3
    (for-bank
      (enc n-0 cost account-0 bank-conf-0 ncb-0
        (hash n-0 (hash ncm-0 item-0 merc-conf-0)) (pubk "enc" b)))
    (bank-conf-commit bank-conf-commit)
    (bank-conf-decommit bank-conf-decommit) (cost cost) (n n) (ncm ncm)
    (item item) (merc-conf merc-conf) (btr btr) (mtr mtr) (c c) (m m)
    (b b))
  (defstrand bank 2 (merc-conf-decommit (hash ncm item merc-conf))
    (account account) (cost cost) (n n) (ncb ncb) (bank-conf bank-conf)
    (btr btr) (mtr mtr) (c c) (m m) (b b))
  (defstrand cust 1 (account account-0) (cost cost) (n n-0) (ncb ncb-0)
    (ncm ncm-0) (item item-0) (merc-conf merc-conf-0)
    (bank-conf bank-conf-0) (c c) (m m) (b b))
  (precedes ((0 1) (1 0)) ((1 1) (0 2)) ((2 0) (0 0)))
  (non-orig (privk "sig" c) (privk "sig" b))
  (uniq-orig mtr btr)
  (facts (buy-via c m b item-0 cost n-0)
    (will-transfer c m b cost n mtr btr) (neq n-0 ncb-0) (neq n-0 ncm-0)
    (neq ncm-0 ncb-0))
  (rule fact-cust-neq0 fact-cust-neq1 fact-cust-neq2 guar-bank-2
    guar-cust-1)
  (operation encryption-test (added-strand cust 1)
    (sign
      (order c m b cost
        (enc n-0 cost account-0 bank-conf-0 ncb-0
          (hash n-0 (hash ncm-0 item-0 merc-conf-0)) (pubk "enc" b)))
      (privk "sig" c)) (0 0))
  (traces
    ((recv
       (enc n cost item merc-conf ncm bank-conf-commit
         (sign
           (order c m b cost
             (enc n-0 cost account-0 bank-conf-0 ncb-0
               (hash n-0 (hash ncm-0 item-0 merc-conf-0))
               (pubk "enc" b))) (privk "sig" c)) (pubk "enc" m)))
      (send
        (enc
          (payreq c m b (hash cost n) (hash ncm item merc-conf) mtr
            (cat
              (sign
                (order c m b cost
                  (enc n-0 cost account-0 bank-conf-0 ncb-0
                    (hash n-0 (hash ncm-0 item-0 merc-conf-0))
                    (pubk "enc" b))) (privk "sig" c))
              (enc n-0 cost account-0 bank-conf-0 ncb-0
                (hash n-0 (hash ncm-0 item-0 merc-conf-0))
                (pubk "enc" b)))) (pubk "enc" b)))
      (recv
        (enc bank-conf-decommit
          (sign
            (bconf
              (hash c m b n cost (hash n (hash ncm item merc-conf))) btr
              mtr) (privk "sig" b)) (pubk "enc" m))))
    ((recv
       (enc
         (payreq c m b (hash cost n) (hash ncm item merc-conf) mtr
           (cat
             (sign
               (order c m b cost
                 (enc n cost account bank-conf ncb
                   (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
               (privk "sig" c))
             (enc n cost account bank-conf ncb
               (hash n (hash ncm item merc-conf)) (pubk "enc" b))))
         (pubk "enc" b)))
      (send
        (enc (hash ncb bank-conf)
          (sign
            (bconf
              (hash c m b n cost (hash n (hash ncm item merc-conf))) btr
              mtr) (privk "sig" b)) (pubk "enc" m))))
    ((send
       (enc n-0 cost item-0 merc-conf-0 ncm-0
         (hash n-0 (hash ncb-0 bank-conf-0))
         (sign
           (order c m b cost
             (enc n-0 cost account-0 bank-conf-0 ncb-0
               (hash n-0 (hash ncm-0 item-0 merc-conf-0))
               (pubk "enc" b))) (privk "sig" c)) (pubk "enc" m)))))
  (label 10)
  (parent 9)
  (unrealized (1 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton minipay-guar
  (vars (bank-conf-commit bank-conf-decommit mesg) (account acct)
    (cost amount) (n ncb ncm data) (item merchandise)
    (mtr btr merc-conf bank-conf text) (c m b name))
  (defstrand merc 3
    (for-bank
      (enc n cost account bank-conf ncb
        (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
    (bank-conf-commit bank-conf-commit)
    (bank-conf-decommit bank-conf-decommit) (cost cost) (n n) (ncm ncm)
    (item item) (merc-conf merc-conf) (btr btr) (mtr mtr) (c c) (m m)
    (b b))
  (defstrand bank 2 (merc-conf-decommit (hash ncm item merc-conf))
    (account account) (cost cost) (n n) (ncb ncb) (bank-conf bank-conf)
    (btr btr) (mtr mtr) (c c) (m m) (b b))
  (defstrand cust 1 (account account) (cost cost) (n n) (ncb ncb)
    (ncm ncm) (item item) (merc-conf merc-conf) (bank-conf bank-conf)
    (c c) (m m) (b b))
  (precedes ((0 1) (1 0)) ((1 1) (0 2)) ((2 0) (0 0)))
  (non-orig (privk "sig" c) (privk "sig" b))
  (uniq-orig mtr btr)
  (facts (buy-via c m b item cost n)
    (will-transfer c m b cost n mtr btr) (neq n ncb) (neq n ncm)
    (neq ncm ncb))
  (rule fact-cust-neq0 fact-cust-neq1 fact-cust-neq2 guar-bank-2
    guar-cust-1)
  (operation encryption-test (displaced 3 2 cust 1)
    (sign
      (order c m b cost
        (enc n-0 cost account-0 bank-conf-0 ncb-0
          (hash n-0 (hash ncm-0 item-0 merc-conf-0)) (pubk "enc" b)))
      (privk "sig" c)) (1 0))
  (traces
    ((recv
       (enc n cost item merc-conf ncm bank-conf-commit
         (sign
           (order c m b cost
             (enc n cost account bank-conf ncb
               (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
           (privk "sig" c)) (pubk "enc" m)))
      (send
        (enc
          (payreq c m b (hash cost n) (hash ncm item merc-conf) mtr
            (cat
              (sign
                (order c m b cost
                  (enc n cost account bank-conf ncb
                    (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
                (privk "sig" c))
              (enc n cost account bank-conf ncb
                (hash n (hash ncm item merc-conf)) (pubk "enc" b))))
          (pubk "enc" b)))
      (recv
        (enc bank-conf-decommit
          (sign
            (bconf
              (hash c m b n cost (hash n (hash ncm item merc-conf))) btr
              mtr) (privk "sig" b)) (pubk "enc" m))))
    ((recv
       (enc
         (payreq c m b (hash cost n) (hash ncm item merc-conf) mtr
           (cat
             (sign
               (order c m b cost
                 (enc n cost account bank-conf ncb
                   (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
               (privk "sig" c))
             (enc n cost account bank-conf ncb
               (hash n (hash ncm item merc-conf)) (pubk "enc" b))))
         (pubk "enc" b)))
      (send
        (enc (hash ncb bank-conf)
          (sign
            (bconf
              (hash c m b n cost (hash n (hash ncm item merc-conf))) btr
              mtr) (privk "sig" b)) (pubk "enc" m))))
    ((send
       (enc n cost item merc-conf ncm (hash n (hash ncb bank-conf))
         (sign
           (order c m b cost
             (enc n cost account bank-conf ncb
               (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
           (privk "sig" c)) (pubk "enc" m)))))
  (label 11)
  (parent 10)
  (realized)
  (shape)
  (satisfies yes)
  (maps
    ((0)
      ((for-bank
         (enc n cost account bank-conf ncb
           (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
        (bank-conf-commit bank-conf-commit)
        (bank-conf-decommit bank-conf-decommit) (cost cost) (n n)
        (ncm ncm) (item item) (mtr mtr) (btr btr) (merc-conf merc-conf)
        (c c) (m m) (b b))))
  (origs (btr (1 1)) (mtr (0 1))))

(defskeleton minipay-guar
  (vars (bank-conf-commit bank-conf-decommit mesg)
    (account account-0 acct) (cost amount)
    (n ncm ncb n-0 ncb-0 ncm-0 data) (item item-0 merchandise)
    (mtr btr merc-conf bank-conf merc-conf-0 bank-conf-0 text)
    (c m b name))
  (defstrand merc 3
    (for-bank
      (enc n-0 cost account-0 bank-conf-0 ncb-0
        (hash n-0 (hash ncm-0 item-0 merc-conf-0)) (pubk "enc" b)))
    (bank-conf-commit bank-conf-commit)
    (bank-conf-decommit bank-conf-decommit) (cost cost) (n n) (ncm ncm)
    (item item) (merc-conf merc-conf) (btr btr) (mtr mtr) (c c) (m m)
    (b b))
  (defstrand bank 2 (merc-conf-decommit (hash ncm item merc-conf))
    (account account) (cost cost) (n n) (ncb ncb) (bank-conf bank-conf)
    (btr btr) (mtr mtr) (c c) (m m) (b b))
  (defstrand cust 1 (account account-0) (cost cost) (n n-0) (ncb ncb-0)
    (ncm ncm-0) (item item-0) (merc-conf merc-conf-0)
    (bank-conf bank-conf-0) (c c) (m m) (b b))
  (defstrand cust 1 (account account) (cost cost) (n n) (ncb ncb)
    (ncm ncm) (item item) (merc-conf merc-conf) (bank-conf bank-conf)
    (c c) (m m) (b b))
  (precedes ((0 1) (1 0)) ((1 1) (0 2)) ((2 0) (0 0)) ((3 0) (1 0)))
  (non-orig (privk "sig" c) (privk "sig" b))
  (uniq-orig mtr btr)
  (facts (buy-via c m b item cost n) (buy-via c m b item-0 cost n-0)
    (will-transfer c m b cost n mtr btr) (neq n ncb) (neq n-0 ncb-0)
    (neq n ncm) (neq n-0 ncm-0) (neq ncm ncb) (neq ncm-0 ncb-0))
  (rule fact-cust-neq0 fact-cust-neq1 fact-cust-neq2 guar-bank-2
    guar-cust-1)
  (operation encryption-test (added-strand cust 1)
    (sign
      (order c m b cost
        (enc n cost account bank-conf ncb
          (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
      (privk "sig" c)) (1 0))
  (traces
    ((recv
       (enc n cost item merc-conf ncm bank-conf-commit
         (sign
           (order c m b cost
             (enc n-0 cost account-0 bank-conf-0 ncb-0
               (hash n-0 (hash ncm-0 item-0 merc-conf-0))
               (pubk "enc" b))) (privk "sig" c)) (pubk "enc" m)))
      (send
        (enc
          (payreq c m b (hash cost n) (hash ncm item merc-conf) mtr
            (cat
              (sign
                (order c m b cost
                  (enc n-0 cost account-0 bank-conf-0 ncb-0
                    (hash n-0 (hash ncm-0 item-0 merc-conf-0))
                    (pubk "enc" b))) (privk "sig" c))
              (enc n-0 cost account-0 bank-conf-0 ncb-0
                (hash n-0 (hash ncm-0 item-0 merc-conf-0))
                (pubk "enc" b)))) (pubk "enc" b)))
      (recv
        (enc bank-conf-decommit
          (sign
            (bconf
              (hash c m b n cost (hash n (hash ncm item merc-conf))) btr
              mtr) (privk "sig" b)) (pubk "enc" m))))
    ((recv
       (enc
         (payreq c m b (hash cost n) (hash ncm item merc-conf) mtr
           (cat
             (sign
               (order c m b cost
                 (enc n cost account bank-conf ncb
                   (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
               (privk "sig" c))
             (enc n cost account bank-conf ncb
               (hash n (hash ncm item merc-conf)) (pubk "enc" b))))
         (pubk "enc" b)))
      (send
        (enc (hash ncb bank-conf)
          (sign
            (bconf
              (hash c m b n cost (hash n (hash ncm item merc-conf))) btr
              mtr) (privk "sig" b)) (pubk "enc" m))))
    ((send
       (enc n-0 cost item-0 merc-conf-0 ncm-0
         (hash n-0 (hash ncb-0 bank-conf-0))
         (sign
           (order c m b cost
             (enc n-0 cost account-0 bank-conf-0 ncb-0
               (hash n-0 (hash ncm-0 item-0 merc-conf-0))
               (pubk "enc" b))) (privk "sig" c)) (pubk "enc" m))))
    ((send
       (enc n cost item merc-conf ncm (hash n (hash ncb bank-conf))
         (sign
           (order c m b cost
             (enc n cost account bank-conf ncb
               (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
           (privk "sig" c)) (pubk "enc" m)))))
  (label 12)
  (parent 10)
  (realized)
  (shape)
  (satisfies yes)
  (maps
    ((0)
      ((for-bank
         (enc n-0 cost account-0 bank-conf-0 ncb-0
           (hash n-0 (hash ncm-0 item-0 merc-conf-0)) (pubk "enc" b)))
        (bank-conf-commit bank-conf-commit)
        (bank-conf-decommit bank-conf-decommit) (cost cost) (n n)
        (ncm ncm) (item item) (mtr mtr) (btr btr) (merc-conf merc-conf)
        (c c) (m m) (b b))))
  (origs (btr (1 1)) (mtr (0 1))))

(comment "Nothing left to do")

(defprotocol minipay-guar basic
  (defrole cust
    (vars (c m b name) (cost amount) (item merchandise)
      (merc-conf bank-conf btr mtr text) (account acct)
      (n ncb ncm data))
    (trace
      (send
        (enc n cost item merc-conf ncm (hash n (hash ncb bank-conf))
          (sign
            (order c m b cost
              (enc n cost account bank-conf ncb
                (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
            (privk "sig" c)) (pubk "enc" m)))
      (recv
        (sign
          (bconf (hash c m b n cost (hash n (hash ncm item merc-conf)))
            btr mtr) (privk "sig" b)))
      (recv
        (sign
          (mconf (hash c m b n item cost (hash n (hash ncb bank-conf)))
            btr mtr) (privk "sig" m))))
    (facts (neq n ncb) (neq n ncm) (neq ncm ncb)))
  (defrole merc
    (vars (c m b name) (cost amount) (item merchandise)
      (merc-conf btr mtr text) (n ncm data)
      (for-bank bank-conf-commit bank-conf-decommit mesg))
    (trace
      (recv
        (enc n cost item merc-conf ncm bank-conf-commit
          (sign (order c m b cost for-bank) (privk "sig" c))
          (pubk "enc" m)))
      (send
        (enc
          (payreq c m b (hash cost n) (hash ncm item merc-conf) mtr
            (cat (sign (order c m b cost for-bank) (privk "sig" c))
              for-bank)) (pubk "enc" b)))
      (recv
        (enc bank-conf-decommit
          (sign
            (bconf
              (hash c m b n cost (hash n (hash ncm item merc-conf))) btr
              mtr) (privk "sig" b)) (pubk "enc" m)))
      (send
        (sign
          (bconf (hash c m b n cost (hash n (hash ncm item merc-conf)))
            btr mtr) (privk "sig" b)))
      (send
        (sign
          (mconf (hash c m b n item cost (hash n bank-conf-decommit))
            btr mtr) (privk "sig" m))))
    (uniq-orig mtr))
  (defrole bank
    (vars (c m b name) (cost amount) (bank-conf btr mtr text)
      (merc-conf-decommit mesg) (account acct) (n ncb data))
    (trace
      (recv
        (enc
          (payreq c m b (hash cost n) merc-conf-decommit mtr
            (cat
              (sign
                (order c m b cost
                  (enc n cost account bank-conf ncb
                    (hash n merc-conf-decommit) (pubk "enc" b)))
                (privk "sig" c))
              (enc n cost account bank-conf ncb
                (hash n merc-conf-decommit) (pubk "enc" b))))
          (pubk "enc" b)))
      (send
        (enc (hash ncb bank-conf)
          (sign
            (bconf (hash c m b n cost (hash n merc-conf-decommit)) btr
              mtr) (privk "sig" b)) (pubk "enc" m))))
    (uniq-orig btr))
  (defrule guar-cust-1
    (forall
      ((z strd) (n data) (cost amount) (item merchandise) (b m c name))
      (implies
        (and (p "cust" z (idx 1)) (p "cust" "n" z n)
          (p "cust" "cost" z cost) (p "cust" "item" z item)
          (p "cust" "b" z b) (p "cust" "m" z m) (p "cust" "c" z c))
        (fact buy-via c m b item cost n))))
  (defrule guar-merc-4
    (forall ((z strd) (mtr text) (item merchandise) (b m c name))
      (implies
        (and (p "merc" z (idx 4)) (p "merc" "mtr" z mtr)
          (p "merc" "item" z item) (p "merc" "b" z b) (p "merc" "m" z m)
          (p "merc" "c" z c))
        (fact will-ship c m b item mtr))))
  (defrule guar-bank-2
    (forall
      ((z strd) (btr mtr text) (n data) (cost amount) (c b m name))
      (implies
        (and (p "bank" z (idx 2)) (p "bank" "btr" z btr)
          (p "bank" "mtr" z mtr) (p "bank" "n" z n)
          (p "bank" "cost" z cost) (p "bank" "c" z c) (p "bank" "b" z b)
          (p "bank" "m" z m))
        (and (non (privk "sig" c))
          (fact will-transfer c m b cost n mtr btr)))))
  (defrule cheq-merc-4
    (forall
      ((z strd) (n data) (bank-conf-decommit bank-conf-commit mesg))
      (implies
        (and (p "merc" z (idx 4)) (p "merc" "n" z n)
          (p "merc" "bank-conf-decommit" z bank-conf-decommit)
          (p "merc" "bank-conf-commit" z bank-conf-commit))
        (= bank-conf-commit (hash n bank-conf-decommit)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule fact-cust-neq2
    (forall ((z strd) (ncb n data))
      (implies
        (and (p "cust" z (idx 1)) (p "cust" "ncb" z ncb)
          (p "cust" "n" z n)) (fact neq n ncb))))
  (defgenrule fact-cust-neq1
    (forall ((z strd) (ncm n data))
      (implies
        (and (p "cust" z (idx 1)) (p "cust" "ncm" z ncm)
          (p "cust" "n" z n)) (fact neq n ncm))))
  (defgenrule fact-cust-neq0
    (forall ((z strd) (ncb ncm data))
      (implies
        (and (p "cust" z (idx 1)) (p "cust" "ncb" z ncb)
          (p "cust" "ncm" z ncm)) (fact neq ncm ncb))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule fact-cust-neq2
    (forall ((z strd) (ncb n data))
      (implies
        (and (p "cust" z (idx 1)) (p "cust" "ncb" z ncb)
          (p "cust" "n" z n)) (fact neq n ncb))))
  (defgenrule fact-cust-neq1
    (forall ((z strd) (ncm n data))
      (implies
        (and (p "cust" z (idx 1)) (p "cust" "ncm" z ncm)
          (p "cust" "n" z n)) (fact neq n ncm))))
  (defgenrule fact-cust-neq0
    (forall ((z strd) (ncb ncm data))
      (implies
        (and (p "cust" z (idx 1)) (p "cust" "ncb" z ncb)
          (p "cust" "ncm" z ncm)) (fact neq ncm ncb))))
  (lang (acct atom) (amount atom) (merchandise atom) (sign sign)
    (order (tuple 5)) (bconf (tuple 3)) (mconf (tuple 3))
    (payreq (tuple 7))))

(defskeleton minipay-guar
  (vars (merc-conf-decommit mesg) (account acct) (cost amount)
    (n ncb data) (bank-conf mtr text) (c m b name))
  (defstrand bank 1 (merc-conf-decommit merc-conf-decommit)
    (account account) (cost cost) (n n) (ncb ncb) (bank-conf bank-conf)
    (mtr mtr) (c c) (m m) (b b))
  (non-orig (privk "sig" c))
  (goals
    (forall
      ((merc-conf-decommit mesg) (account acct) (cost amount)
        (n ncb data) (bank-conf mtr text) (c m b name) (z strd))
      (implies
        (and (p "bank" z 1)
          (p "bank" "merc-conf-decommit" z merc-conf-decommit)
          (p "bank" "account" z account) (p "bank" "cost" z cost)
          (p "bank" "n" z n) (p "bank" "ncb" z ncb)
          (p "bank" "bank-conf" z bank-conf) (p "bank" "mtr" z mtr)
          (p "bank" "c" z c) (p "bank" "m" z m) (p "bank" "b" z b)
          (non (privk "sig" c)))
        (exists
          ((ncm data) (item merchandise) (merc-conf text) (z-0 strd))
          (and (= merc-conf-decommit (hash ncm item merc-conf))
            (p "cust" z-0 1)
            (p "bank" "merc-conf-decommit" z (hash ncm item merc-conf))
            (p "cust" "account" z-0 account) (p "cust" "cost" z-0 cost)
            (p "cust" "n" z-0 n) (p "cust" "ncb" z-0 ncb)
            (p "cust" "ncm" z-0 ncm) (p "cust" "item" z-0 item)
            (p "cust" "merc-conf" z-0 merc-conf)
            (p "cust" "bank-conf" z-0 bank-conf) (p "cust" "c" z-0 c)
            (p "cust" "m" z-0 m) (p "cust" "b" z-0 b) (prec z-0 0 z 0)
            (fact neq n ncb) (fact neq n ncm) (fact neq ncm ncb)
            (fact buy-via c m b item cost n))))))
  (traces
    ((recv
       (enc
         (payreq c m b (hash cost n) merc-conf-decommit mtr
           (cat
             (sign
               (order c m b cost
                 (enc n cost account bank-conf ncb
                   (hash n merc-conf-decommit) (pubk "enc" b)))
               (privk "sig" c))
             (enc n cost account bank-conf ncb
               (hash n merc-conf-decommit) (pubk "enc" b))))
         (pubk "enc" b)))))
  (label 13)
  (unrealized (0 0))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton minipay-guar
  (vars (account acct) (cost amount) (n ncb ncm data) (item merchandise)
    (bank-conf mtr merc-conf text) (c m b name))
  (defstrand bank 1 (merc-conf-decommit (hash ncm item merc-conf))
    (account account) (cost cost) (n n) (ncb ncb) (bank-conf bank-conf)
    (mtr mtr) (c c) (m m) (b b))
  (defstrand cust 1 (account account) (cost cost) (n n) (ncb ncb)
    (ncm ncm) (item item) (merc-conf merc-conf) (bank-conf bank-conf)
    (c c) (m m) (b b))
  (precedes ((1 0) (0 0)))
  (non-orig (privk "sig" c))
  (facts (buy-via c m b item cost n) (neq n ncb) (neq n ncm)
    (neq ncm ncb))
  (rule fact-cust-neq0 fact-cust-neq1 fact-cust-neq2 guar-cust-1)
  (operation encryption-test (added-strand cust 1)
    (sign
      (order c m b cost
        (enc n cost account bank-conf ncb
          (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
      (privk "sig" c)) (0 0))
  (traces
    ((recv
       (enc
         (payreq c m b (hash cost n) (hash ncm item merc-conf) mtr
           (cat
             (sign
               (order c m b cost
                 (enc n cost account bank-conf ncb
                   (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
               (privk "sig" c))
             (enc n cost account bank-conf ncb
               (hash n (hash ncm item merc-conf)) (pubk "enc" b))))
         (pubk "enc" b))))
    ((send
       (enc n cost item merc-conf ncm (hash n (hash ncb bank-conf))
         (sign
           (order c m b cost
             (enc n cost account bank-conf ncb
               (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
           (privk "sig" c)) (pubk "enc" m)))))
  (label 14)
  (parent 13)
  (realized)
  (shape)
  (satisfies yes)
  (maps
    ((0)
      ((merc-conf-decommit (hash ncm item merc-conf)) (account account)
        (cost cost) (n n) (ncb ncb) (bank-conf bank-conf) (mtr mtr)
        (c c) (m m) (b b))))
  (origs))

(comment "Nothing left to do")
