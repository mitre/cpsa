(herald minipay-rely-guar (try-old-strands) (bound 16))

(comment "CPSA 4.4.0")
(comment "Coherent logic")

(comment "CPSA 4.4.0")

(comment "All input read from minipay-rely-guar.scm")

(comment "Strand count bounded at 16")

(comment "Old strands tried first")

(defprotocol minipay-rely-guar basic
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
  (defrule rely-cust-3
    (forall ((z strd) (mtr text) (item merchandise) (b m c name))
      (implies
        (and (p "cust" z (idx 3)) (p "cust" "mtr" z mtr)
          (p "cust" "item" z item) (p "cust" "b" z b) (p "cust" "m" z m)
          (p "cust" "c" z c))
        (fact will-ship c m b item mtr))))
  (defrule rely-cust-2
    (forall
      ((z strd) (btr mtr text) (n data) (cost amount) (b m c name))
      (implies
        (and (p "cust" z (idx 2)) (p "cust" "btr" z btr)
          (p "cust" "mtr" z mtr) (p "cust" "n" z n)
          (p "cust" "cost" z cost) (p "cust" "b" z b) (p "cust" "m" z m)
          (p "cust" "c" z c))
        (fact will-transfer c m b cost n mtr btr))))
  (defrule rely-merc-3
    (forall
      ((z strd) (n data) (cost amount) (item merchandise) (b m c name)
        (btr mtr text))
      (implies
        (and (p "merc" z (idx 3)) (p "merc" "n" z n)
          (p "merc" "cost" z cost) (p "merc" "item" z item)
          (p "merc" "b" z b) (p "merc" "m" z m) (p "merc" "c" z c)
          (p "merc" "btr" z btr) (p "merc" "mtr" z mtr))
        (and (fact buy-via c m b item cost n)
          (fact will-transfer c m b cost n mtr btr)))))
  (defrule rely-bank-1
    (forall ((z strd) (n data) (cost amount) (b m c name))
      (implies
        (and (p "bank" z (idx 1)) (p "bank" "n" z n)
          (p "bank" "cost" z cost) (p "bank" "b" z b) (p "bank" "m" z m)
          (p "bank" "c" z c))
        (exists ((item merchandise))
          (fact buy-via c m b item cost n)))))
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
  (lang (acct atom) (amount atom) (merchandise atom) (sign sign)
    (order (tuple 5)) (bconf (tuple 3)) (mconf (tuple 3))
    (payreq (tuple 7))))

(defgoal minipay-rely-guar
  (forall
    ((account acct) (cost amount) (n ncb ncm data) (item merchandise)
      (merc-conf bank-conf btr mtr text) (c m b name) (z strd))
    (implies
      (and (p "cust" z 3) (p "cust" "account" z account)
        (p "cust" "cost" z cost) (p "cust" "n" z n)
        (p "cust" "ncb" z ncb) (p "cust" "ncm" z ncm)
        (p "cust" "item" z item) (p "cust" "merc-conf" z merc-conf)
        (p "cust" "bank-conf" z bank-conf) (p "cust" "btr" z btr)
        (p "cust" "mtr" z mtr) (p "cust" "c" z c) (p "cust" "m" z m)
        (p "cust" "b" z b) (non (privk "enc" m)) (non (privk "enc" b))
        (non (privk "sig" m)) (non (privk "sig" b)) (uniq-at n z 0))
      (exists ((z-0 z-1 strd))
        (and (p "bank" z-0 2) (p "merc" z-1 5)
          (p "bank" "merc-conf-decommit" z-0 (hash ncm item merc-conf))
          (p "bank" "account" z-0 account) (p "bank" "cost" z-0 cost)
          (p "bank" "n" z-0 n) (p "bank" "ncb" z-0 ncb)
          (p "bank" "bank-conf" z-0 bank-conf) (p "bank" "btr" z-0 btr)
          (p "bank" "mtr" z-0 mtr) (p "bank" "c" z-0 c)
          (p "bank" "m" z-0 m) (p "bank" "b" z-0 b)
          (p "merc" "for-bank" z-1
            (enc n cost account bank-conf ncb
              (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
          (p "merc" "bank-conf-commit" z-1
            (hash n (hash ncb bank-conf)))
          (p "merc" "bank-conf-decommit" z-1 (hash ncb bank-conf))
          (p "merc" "cost" z-1 cost) (p "merc" "n" z-1 n)
          (p "merc" "ncm" z-1 ncm) (p "merc" "item" z-1 item)
          (p "merc" "merc-conf" z-1 merc-conf) (p "merc" "btr" z-1 btr)
          (p "merc" "mtr" z-1 mtr) (p "merc" "c" z-1 c)
          (p "merc" "m" z-1 m) (p "merc" "b" z-1 b) (prec z 0 z-1 0)
          (prec z-0 1 z-1 2) (prec z-1 1 z-0 0) (prec z-1 3 z 1)
          (prec z-1 4 z 2) (non (privk "sig" c)) (uniq-at mtr z-1 1)
          (uniq-at btr z-0 1) (fact neq n ncb) (fact neq n ncm)
          (fact neq ncm ncb) (fact buy-via c m b item cost n)
          (fact will-ship c m b item mtr)
          (fact will-transfer c m b cost n mtr btr))))))

(defprotocol minipay-rely-guar basic
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
  (defrule rely-cust-3
    (forall ((z strd) (mtr text) (item merchandise) (b m c name))
      (implies
        (and (p "cust" z (idx 3)) (p "cust" "mtr" z mtr)
          (p "cust" "item" z item) (p "cust" "b" z b) (p "cust" "m" z m)
          (p "cust" "c" z c))
        (fact will-ship c m b item mtr))))
  (defrule rely-cust-2
    (forall
      ((z strd) (btr mtr text) (n data) (cost amount) (b m c name))
      (implies
        (and (p "cust" z (idx 2)) (p "cust" "btr" z btr)
          (p "cust" "mtr" z mtr) (p "cust" "n" z n)
          (p "cust" "cost" z cost) (p "cust" "b" z b) (p "cust" "m" z m)
          (p "cust" "c" z c))
        (fact will-transfer c m b cost n mtr btr))))
  (defrule rely-merc-3
    (forall
      ((z strd) (n data) (cost amount) (item merchandise) (b m c name)
        (btr mtr text))
      (implies
        (and (p "merc" z (idx 3)) (p "merc" "n" z n)
          (p "merc" "cost" z cost) (p "merc" "item" z item)
          (p "merc" "b" z b) (p "merc" "m" z m) (p "merc" "c" z c)
          (p "merc" "btr" z btr) (p "merc" "mtr" z mtr))
        (and (fact buy-via c m b item cost n)
          (fact will-transfer c m b cost n mtr btr)))))
  (defrule rely-bank-1
    (forall ((z strd) (n data) (cost amount) (b m c name))
      (implies
        (and (p "bank" z (idx 1)) (p "bank" "n" z n)
          (p "bank" "cost" z cost) (p "bank" "b" z b) (p "bank" "m" z m)
          (p "bank" "c" z c))
        (exists ((item merchandise))
          (fact buy-via c m b item cost n)))))
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
  (lang (acct atom) (amount atom) (merchandise atom) (sign sign)
    (order (tuple 5)) (bconf (tuple 3)) (mconf (tuple 3))
    (payreq (tuple 7))))

(defgoal minipay-rely-guar
  (forall
    ((for-bank bank-conf-commit bank-conf-decommit mesg) (cost amount)
      (n ncm data) (item merchandise) (merc-conf btr mtr text)
      (c m b name) (z strd))
    (implies
      (and (p "merc" z 3) (p "merc" "for-bank" z for-bank)
        (p "merc" "bank-conf-commit" z bank-conf-commit)
        (p "merc" "bank-conf-decommit" z bank-conf-decommit)
        (p "merc" "cost" z cost) (p "merc" "n" z n)
        (p "merc" "ncm" z ncm) (p "merc" "item" z item)
        (p "merc" "merc-conf" z merc-conf) (p "merc" "btr" z btr)
        (p "merc" "mtr" z mtr) (p "merc" "c" z c) (p "merc" "m" z m)
        (p "merc" "b" z b) (non (privk "enc" m)) (non (privk "enc" b))
        (non (privk "sig" m)) (non (privk "sig" b)) (uniq-at mtr z 1))
      (exists
        ((account acct) (ncb data) (bank-conf text) (z-0 z-1 strd))
        (and
          (= for-bank
            (enc n cost account bank-conf ncb
              (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
          (= bank-conf-commit (hash n (hash ncb bank-conf)))
          (= bank-conf-decommit (hash ncb bank-conf)) (p "bank" z-0 2)
          (p "cust" z-1 1)
          (p "merc" "for-bank" z
            (enc n cost account bank-conf ncb
              (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
          (p "merc" "bank-conf-commit" z (hash n (hash ncb bank-conf)))
          (p "merc" "bank-conf-decommit" z (hash ncb bank-conf))
          (p "bank" "merc-conf-decommit" z-0 (hash ncm item merc-conf))
          (p "bank" "account" z-0 account) (p "bank" "cost" z-0 cost)
          (p "bank" "n" z-0 n) (p "bank" "ncb" z-0 ncb)
          (p "bank" "bank-conf" z-0 bank-conf) (p "bank" "btr" z-0 btr)
          (p "bank" "mtr" z-0 mtr) (p "bank" "c" z-0 c)
          (p "bank" "m" z-0 m) (p "bank" "b" z-0 b)
          (p "cust" "account" z-1 account) (p "cust" "cost" z-1 cost)
          (p "cust" "n" z-1 n) (p "cust" "ncb" z-1 ncb)
          (p "cust" "ncm" z-1 ncm) (p "cust" "item" z-1 item)
          (p "cust" "merc-conf" z-1 merc-conf)
          (p "cust" "bank-conf" z-1 bank-conf) (p "cust" "c" z-1 c)
          (p "cust" "m" z-1 m) (p "cust" "b" z-1 b) (prec z 1 z-0 0)
          (prec z-0 1 z 2) (prec z-1 0 z 0) (non (privk "sig" c))
          (uniq-at btr z-0 1) (fact neq n ncb) (fact neq n ncm)
          (fact neq ncm ncb) (fact buy-via c m b item cost n)
          (fact will-transfer c m b cost n mtr btr))))))

(defprotocol minipay-rely-guar basic
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
  (defrule rely-cust-3
    (forall ((z strd) (mtr text) (item merchandise) (b m c name))
      (implies
        (and (p "cust" z (idx 3)) (p "cust" "mtr" z mtr)
          (p "cust" "item" z item) (p "cust" "b" z b) (p "cust" "m" z m)
          (p "cust" "c" z c))
        (fact will-ship c m b item mtr))))
  (defrule rely-cust-2
    (forall
      ((z strd) (btr mtr text) (n data) (cost amount) (b m c name))
      (implies
        (and (p "cust" z (idx 2)) (p "cust" "btr" z btr)
          (p "cust" "mtr" z mtr) (p "cust" "n" z n)
          (p "cust" "cost" z cost) (p "cust" "b" z b) (p "cust" "m" z m)
          (p "cust" "c" z c))
        (fact will-transfer c m b cost n mtr btr))))
  (defrule rely-merc-3
    (forall
      ((z strd) (n data) (cost amount) (item merchandise) (b m c name)
        (btr mtr text))
      (implies
        (and (p "merc" z (idx 3)) (p "merc" "n" z n)
          (p "merc" "cost" z cost) (p "merc" "item" z item)
          (p "merc" "b" z b) (p "merc" "m" z m) (p "merc" "c" z c)
          (p "merc" "btr" z btr) (p "merc" "mtr" z mtr))
        (and (fact buy-via c m b item cost n)
          (fact will-transfer c m b cost n mtr btr)))))
  (defrule rely-bank-1
    (forall ((z strd) (n data) (cost amount) (b m c name))
      (implies
        (and (p "bank" z (idx 1)) (p "bank" "n" z n)
          (p "bank" "cost" z cost) (p "bank" "b" z b) (p "bank" "m" z m)
          (p "bank" "c" z c))
        (exists ((item merchandise))
          (fact buy-via c m b item cost n)))))
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
  (lang (acct atom) (amount atom) (merchandise atom) (sign sign)
    (order (tuple 5)) (bconf (tuple 3)) (mconf (tuple 3))
    (payreq (tuple 7))))

(defgoal minipay-rely-guar
  (forall
    ((merc-conf-decommit mesg) (account acct) (cost amount) (n ncb data)
      (bank-conf btr mtr text) (c m b name) (z strd))
    (implies
      (and (p "bank" z 2)
        (p "bank" "merc-conf-decommit" z merc-conf-decommit)
        (p "bank" "account" z account) (p "bank" "cost" z cost)
        (p "bank" "n" z n) (p "bank" "ncb" z ncb)
        (p "bank" "bank-conf" z bank-conf) (p "bank" "btr" z btr)
        (p "bank" "mtr" z mtr) (p "bank" "c" z c) (p "bank" "m" z m)
        (p "bank" "b" z b) (non (privk "enc" m)) (non (privk "enc" b))
        (non (privk "sig" c)) (non (privk "sig" m)) (uniq-at btr z 1))
      (exists
        ((ncm data) (item merchandise) (merc-conf text) (z-0 z-1 strd))
        (and (= merc-conf-decommit (hash ncm item merc-conf))
          (p "cust" z-0 1) (p "merc" z-1 2)
          (p "bank" "merc-conf-decommit" z (hash ncm item merc-conf))
          (p "cust" "account" z-0 account) (p "cust" "cost" z-0 cost)
          (p "cust" "n" z-0 n) (p "cust" "ncb" z-0 ncb)
          (p "cust" "ncm" z-0 ncm) (p "cust" "item" z-0 item)
          (p "cust" "merc-conf" z-0 merc-conf)
          (p "cust" "bank-conf" z-0 bank-conf) (p "cust" "c" z-0 c)
          (p "cust" "m" z-0 m) (p "cust" "b" z-0 b)
          (p "merc" "for-bank" z-1
            (enc n cost account bank-conf ncb
              (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
          (p "merc" "bank-conf-commit" z-1
            (hash n (hash ncb bank-conf))) (p "merc" "cost" z-1 cost)
          (p "merc" "n" z-1 n) (p "merc" "ncm" z-1 ncm)
          (p "merc" "item" z-1 item)
          (p "merc" "merc-conf" z-1 merc-conf) (p "merc" "mtr" z-1 mtr)
          (p "merc" "c" z-1 c) (p "merc" "m" z-1 m) (p "merc" "b" z-1 b)
          (prec z-0 0 z-1 0) (prec z-1 1 z 0) (uniq-at mtr z-1 1)
          (fact neq n ncb) (fact neq n ncm) (fact neq ncm ncb)
          (fact buy-via c m b item cost n)
          (fact will-transfer c m b cost n mtr btr))))))

(defprotocol minipay-rely-guar basic
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
  (defrule rely-cust-3
    (forall ((z strd) (mtr text) (item merchandise) (b m c name))
      (implies
        (and (p "cust" z (idx 3)) (p "cust" "mtr" z mtr)
          (p "cust" "item" z item) (p "cust" "b" z b) (p "cust" "m" z m)
          (p "cust" "c" z c))
        (fact will-ship c m b item mtr))))
  (defrule rely-cust-2
    (forall
      ((z strd) (btr mtr text) (n data) (cost amount) (b m c name))
      (implies
        (and (p "cust" z (idx 2)) (p "cust" "btr" z btr)
          (p "cust" "mtr" z mtr) (p "cust" "n" z n)
          (p "cust" "cost" z cost) (p "cust" "b" z b) (p "cust" "m" z m)
          (p "cust" "c" z c))
        (fact will-transfer c m b cost n mtr btr))))
  (defrule rely-merc-3
    (forall
      ((z strd) (n data) (cost amount) (item merchandise) (b m c name)
        (btr mtr text))
      (implies
        (and (p "merc" z (idx 3)) (p "merc" "n" z n)
          (p "merc" "cost" z cost) (p "merc" "item" z item)
          (p "merc" "b" z b) (p "merc" "m" z m) (p "merc" "c" z c)
          (p "merc" "btr" z btr) (p "merc" "mtr" z mtr))
        (and (fact buy-via c m b item cost n)
          (fact will-transfer c m b cost n mtr btr)))))
  (defrule rely-bank-1
    (forall ((z strd) (n data) (cost amount) (b m c name))
      (implies
        (and (p "bank" z (idx 1)) (p "bank" "n" z n)
          (p "bank" "cost" z cost) (p "bank" "b" z b) (p "bank" "m" z m)
          (p "bank" "c" z c))
        (exists ((item merchandise))
          (fact buy-via c m b item cost n)))))
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
  (lang (acct atom) (amount atom) (merchandise atom) (sign sign)
    (order (tuple 5)) (bconf (tuple 3)) (mconf (tuple 3))
    (payreq (tuple 7))))

(defgoal minipay-rely-guar
  (forall
    ((merc-conf-decommit mesg) (account acct) (cost amount) (n ncb data)
      (bank-conf btr mtr text) (c m b name) (z strd))
    (implies
      (and (p "bank" z 2)
        (p "bank" "merc-conf-decommit" z merc-conf-decommit)
        (p "bank" "account" z account) (p "bank" "cost" z cost)
        (p "bank" "n" z n) (p "bank" "ncb" z ncb)
        (p "bank" "bank-conf" z bank-conf) (p "bank" "btr" z btr)
        (p "bank" "mtr" z mtr) (p "bank" "c" z c) (p "bank" "m" z m)
        (p "bank" "b" z b) (non (privk "enc" m)) (non (privk "sig" c))
        (uniq-at btr z 1))
      (exists
        ((ncm data) (item merchandise) (merc-conf mtr-0 text)
          (z-0 z-1 strd))
        (and (= merc-conf-decommit (hash ncm item merc-conf))
          (p "cust" z-0 1) (p "merc" z-1 2)
          (p "bank" "merc-conf-decommit" z (hash ncm item merc-conf))
          (p "cust" "account" z-0 account) (p "cust" "cost" z-0 cost)
          (p "cust" "n" z-0 n) (p "cust" "ncb" z-0 ncb)
          (p "cust" "ncm" z-0 ncm) (p "cust" "item" z-0 item)
          (p "cust" "merc-conf" z-0 merc-conf)
          (p "cust" "bank-conf" z-0 bank-conf) (p "cust" "c" z-0 c)
          (p "cust" "m" z-0 m) (p "cust" "b" z-0 b)
          (p "merc" "for-bank" z-1
            (enc n cost account bank-conf ncb
              (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
          (p "merc" "bank-conf-commit" z-1
            (hash n (hash ncb bank-conf))) (p "merc" "cost" z-1 cost)
          (p "merc" "n" z-1 n) (p "merc" "ncm" z-1 ncm)
          (p "merc" "item" z-1 item)
          (p "merc" "merc-conf" z-1 merc-conf)
          (p "merc" "mtr" z-1 mtr-0) (p "merc" "c" z-1 c)
          (p "merc" "m" z-1 m) (p "merc" "b" z-1 b) (prec z-0 0 z-1 0)
          (prec z-1 1 z 0) (uniq-at mtr-0 z-1 1) (fact neq n ncb)
          (fact neq n ncm) (fact neq ncm ncb)
          (fact buy-via c m b item cost n)
          (fact will-transfer c m b cost n mtr btr))))))

(defprotocol minipay-rely-guar basic
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
  (defrule rely-cust-3
    (forall ((z strd) (mtr text) (item merchandise) (b m c name))
      (implies
        (and (p "cust" z (idx 3)) (p "cust" "mtr" z mtr)
          (p "cust" "item" z item) (p "cust" "b" z b) (p "cust" "m" z m)
          (p "cust" "c" z c))
        (fact will-ship c m b item mtr))))
  (defrule rely-cust-2
    (forall
      ((z strd) (btr mtr text) (n data) (cost amount) (b m c name))
      (implies
        (and (p "cust" z (idx 2)) (p "cust" "btr" z btr)
          (p "cust" "mtr" z mtr) (p "cust" "n" z n)
          (p "cust" "cost" z cost) (p "cust" "b" z b) (p "cust" "m" z m)
          (p "cust" "c" z c))
        (fact will-transfer c m b cost n mtr btr))))
  (defrule rely-merc-3
    (forall
      ((z strd) (n data) (cost amount) (item merchandise) (b m c name)
        (btr mtr text))
      (implies
        (and (p "merc" z (idx 3)) (p "merc" "n" z n)
          (p "merc" "cost" z cost) (p "merc" "item" z item)
          (p "merc" "b" z b) (p "merc" "m" z m) (p "merc" "c" z c)
          (p "merc" "btr" z btr) (p "merc" "mtr" z mtr))
        (and (fact buy-via c m b item cost n)
          (fact will-transfer c m b cost n mtr btr)))))
  (defrule rely-bank-1
    (forall ((z strd) (n data) (cost amount) (b m c name))
      (implies
        (and (p "bank" z (idx 1)) (p "bank" "n" z n)
          (p "bank" "cost" z cost) (p "bank" "b" z b) (p "bank" "m" z m)
          (p "bank" "c" z c))
        (exists ((item merchandise))
          (fact buy-via c m b item cost n)))))
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
  (lang (acct atom) (amount atom) (merchandise atom) (sign sign)
    (order (tuple 5)) (bconf (tuple 3)) (mconf (tuple 3))
    (payreq (tuple 7))))

(defgoal minipay-rely-guar
  (forall
    ((for-bank bank-conf-commit bank-conf-decommit for-bank-0
       bank-conf-commit-0 bank-conf-decommit-0 mesg) (account acct)
      (cost cost-0 cost-1 amount) (n ncb ncm ncm-0 ncm-1 data)
      (item item-0 item-1 merchandise)
      (merc-conf bank-conf btr mtr merc-conf-0 btr-0 mtr-0 merc-conf-1
        btr-1 mtr-1 text) (c m b name) (z z-0 z-1 strd))
    (implies
      (and (p "cust" z 3) (p "merc" z-0 3) (p "merc" z-1 3)
        (p "cust" "account" z account) (p "cust" "cost" z cost)
        (p "cust" "n" z n) (p "cust" "ncb" z ncb) (p "cust" "ncm" z ncm)
        (p "cust" "item" z item) (p "cust" "merc-conf" z merc-conf)
        (p "cust" "bank-conf" z bank-conf) (p "cust" "btr" z btr)
        (p "cust" "mtr" z mtr) (p "cust" "c" z c) (p "cust" "m" z m)
        (p "cust" "b" z b) (p "merc" "for-bank" z-0 for-bank)
        (p "merc" "bank-conf-commit" z-0 bank-conf-commit)
        (p "merc" "bank-conf-decommit" z-0 bank-conf-decommit)
        (p "merc" "cost" z-0 cost-0) (p "merc" "n" z-0 n)
        (p "merc" "ncm" z-0 ncm-0) (p "merc" "item" z-0 item-0)
        (p "merc" "merc-conf" z-0 merc-conf-0)
        (p "merc" "btr" z-0 btr-0) (p "merc" "mtr" z-0 mtr-0)
        (p "merc" "c" z-0 c) (p "merc" "m" z-0 m) (p "merc" "b" z-0 b)
        (p "merc" "for-bank" z-1 for-bank-0)
        (p "merc" "bank-conf-commit" z-1 bank-conf-commit-0)
        (p "merc" "bank-conf-decommit" z-1 bank-conf-decommit-0)
        (p "merc" "cost" z-1 cost-1) (p "merc" "n" z-1 n)
        (p "merc" "ncm" z-1 ncm-1) (p "merc" "item" z-1 item-1)
        (p "merc" "merc-conf" z-1 merc-conf-1)
        (p "merc" "btr" z-1 btr-1) (p "merc" "mtr" z-1 mtr-1)
        (p "merc" "c" z-1 c) (p "merc" "m" z-1 m) (p "merc" "b" z-1 b)
        (non (privk "enc" b)) (non (privk "sig" b))
        (uniq-at mtr-1 z-1 1) (uniq-at mtr-0 z-0 1) (uniq-at n z 0))
      (or
        (exists ((z-2 strd))
          (and (= z-1 z-0) (= cost-0 cost) (= item-0 item)
            (= merc-conf-0 merc-conf) (= btr-0 btr) (= mtr-0 mtr)
            (= ncm-0 ncm)
            (= for-bank
              (enc n cost account bank-conf ncb
                (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
            (= cost-1 cost) (= item-1 item) (= merc-conf-1 merc-conf)
            (= btr-1 btr) (= mtr-1 mtr) (= ncm-1 ncm)
            (= for-bank-0
              (enc n cost account bank-conf ncb
                (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
            (= bank-conf-commit-0 bank-conf-commit)
            (= bank-conf-decommit-0 bank-conf-decommit) (p "bank" z-2 2)
            (p "merc" "for-bank" z-0
              (enc n cost account bank-conf ncb
                (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
            (p "merc" "cost" z-0 cost) (p "merc" "ncm" z-0 ncm)
            (p "merc" "item" z-0 item)
            (p "merc" "merc-conf" z-0 merc-conf)
            (p "merc" "btr" z-0 btr) (p "merc" "mtr" z-0 mtr)
            (p "bank" "merc-conf-decommit" z-2
              (hash ncm item merc-conf))
            (p "bank" "account" z-2 account) (p "bank" "cost" z-2 cost)
            (p "bank" "n" z-2 n) (p "bank" "ncb" z-2 ncb)
            (p "bank" "bank-conf" z-2 bank-conf)
            (p "bank" "btr" z-2 btr) (p "bank" "mtr" z-2 mtr)
            (p "bank" "c" z-2 c) (p "bank" "m" z-2 m)
            (p "bank" "b" z-2 b) (prec z 0 z-0 0) (prec z-0 1 z-2 0)
            (prec z-2 1 z 1) (prec z-2 1 z-0 2) (non (privk "sig" c))
            (uniq-at btr z-2 1) (uniq-at mtr z-0 1) (fact neq n ncb)
            (fact neq n ncm) (fact neq ncm ncb)
            (fact will-ship c m b item mtr)
            (fact buy-via c m b item cost n)
            (fact will-transfer c m b cost n mtr btr)))
        (exists ((z-2 z-3 strd))
          (and (= z-1 z-0) (= cost-0 cost) (= item-0 item)
            (= merc-conf-0 merc-conf) (= ncm-0 ncm)
            (= for-bank
              (enc n cost account bank-conf ncb
                (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
            (= cost-1 cost) (= item-1 item) (= merc-conf-1 merc-conf)
            (= btr-1 btr-0) (= mtr-1 mtr-0) (= ncm-1 ncm)
            (= for-bank-0
              (enc n cost account bank-conf ncb
                (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
            (= bank-conf-commit-0 bank-conf-commit)
            (= bank-conf-decommit-0 bank-conf-decommit) (p "bank" z-2 2)
            (p "bank" z-3 2)
            (p "merc" "for-bank" z-0
              (enc n cost account bank-conf ncb
                (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
            (p "merc" "cost" z-0 cost) (p "merc" "ncm" z-0 ncm)
            (p "merc" "item" z-0 item)
            (p "merc" "merc-conf" z-0 merc-conf)
            (p "bank" "merc-conf-decommit" z-2
              (hash ncm item merc-conf))
            (p "bank" "account" z-2 account) (p "bank" "cost" z-2 cost)
            (p "bank" "n" z-2 n) (p "bank" "ncb" z-2 ncb)
            (p "bank" "bank-conf" z-2 bank-conf)
            (p "bank" "btr" z-2 btr) (p "bank" "mtr" z-2 mtr)
            (p "bank" "c" z-2 c) (p "bank" "m" z-2 m)
            (p "bank" "b" z-2 b)
            (p "bank" "merc-conf-decommit" z-3
              (hash ncm item merc-conf))
            (p "bank" "account" z-3 account) (p "bank" "cost" z-3 cost)
            (p "bank" "n" z-3 n) (p "bank" "ncb" z-3 ncb)
            (p "bank" "bank-conf" z-3 bank-conf)
            (p "bank" "btr" z-3 btr-0) (p "bank" "mtr" z-3 mtr-0)
            (p "bank" "c" z-3 c) (p "bank" "m" z-3 m)
            (p "bank" "b" z-3 b) (prec z 0 z-0 0) (prec z 0 z-2 0)
            (prec z-0 1 z-3 0) (prec z-2 1 z 1) (prec z-3 1 z-0 2)
            (non (privk "sig" c)) (uniq-at btr-0 z-3 1)
            (uniq-at btr z-2 1) (fact neq n ncb) (fact neq n ncm)
            (fact neq ncm ncb) (fact will-ship c m b item mtr)
            (fact buy-via c m b item cost n)
            (fact will-transfer c m b cost n mtr-0 btr-0)
            (fact will-transfer c m b cost n mtr btr)))
        (exists ((z-2 z-3 strd))
          (and (= cost-0 cost) (= item-0 item) (= merc-conf-0 merc-conf)
            (= btr-0 btr) (= mtr-0 mtr) (= ncm-0 ncm)
            (= for-bank
              (enc n cost account bank-conf ncb
                (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
            (= cost-1 cost) (= item-1 item) (= merc-conf-1 merc-conf)
            (= ncm-1 ncm)
            (= for-bank-0
              (enc n cost account bank-conf ncb
                (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
            (p "bank" z-2 2) (p "bank" z-3 2)
            (p "merc" "for-bank" z-0
              (enc n cost account bank-conf ncb
                (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
            (p "merc" "cost" z-0 cost) (p "merc" "ncm" z-0 ncm)
            (p "merc" "item" z-0 item)
            (p "merc" "merc-conf" z-0 merc-conf)
            (p "merc" "btr" z-0 btr) (p "merc" "mtr" z-0 mtr)
            (p "merc" "for-bank" z-1
              (enc n cost account bank-conf ncb
                (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
            (p "merc" "cost" z-1 cost) (p "merc" "ncm" z-1 ncm)
            (p "merc" "item" z-1 item)
            (p "merc" "merc-conf" z-1 merc-conf)
            (p "bank" "merc-conf-decommit" z-2
              (hash ncm item merc-conf))
            (p "bank" "account" z-2 account) (p "bank" "cost" z-2 cost)
            (p "bank" "n" z-2 n) (p "bank" "ncb" z-2 ncb)
            (p "bank" "bank-conf" z-2 bank-conf)
            (p "bank" "btr" z-2 btr) (p "bank" "mtr" z-2 mtr)
            (p "bank" "c" z-2 c) (p "bank" "m" z-2 m)
            (p "bank" "b" z-2 b)
            (p "bank" "merc-conf-decommit" z-3
              (hash ncm item merc-conf))
            (p "bank" "account" z-3 account) (p "bank" "cost" z-3 cost)
            (p "bank" "n" z-3 n) (p "bank" "ncb" z-3 ncb)
            (p "bank" "bank-conf" z-3 bank-conf)
            (p "bank" "btr" z-3 btr-1) (p "bank" "mtr" z-3 mtr-1)
            (p "bank" "c" z-3 c) (p "bank" "m" z-3 m)
            (p "bank" "b" z-3 b) (prec z 0 z-0 0) (prec z 0 z-1 0)
            (prec z-0 1 z-2 0) (prec z-1 1 z-3 0) (prec z-2 1 z 1)
            (prec z-2 1 z-0 2) (prec z-3 1 z-1 2) (non (privk "sig" c))
            (uniq-at btr-1 z-3 1) (uniq-at btr z-2 1)
            (uniq-at mtr z-0 1) (fact neq n ncb) (fact neq n ncm)
            (fact neq ncm ncb) (fact will-ship c m b item mtr)
            (fact buy-via c m b item cost n)
            (fact will-transfer c m b cost n mtr-1 btr-1)
            (fact will-transfer c m b cost n mtr btr)))
        (exists ((z-2 z-3 z-4 strd))
          (and (= cost-0 cost) (= item-0 item) (= merc-conf-0 merc-conf)
            (= ncm-0 ncm)
            (= for-bank
              (enc n cost account bank-conf ncb
                (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
            (= cost-1 cost) (= item-1 item) (= merc-conf-1 merc-conf)
            (= ncm-1 ncm)
            (= for-bank-0
              (enc n cost account bank-conf ncb
                (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
            (p "bank" z-2 2) (p "bank" z-3 2) (p "bank" z-4 2)
            (p "merc" "for-bank" z-0
              (enc n cost account bank-conf ncb
                (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
            (p "merc" "cost" z-0 cost) (p "merc" "ncm" z-0 ncm)
            (p "merc" "item" z-0 item)
            (p "merc" "merc-conf" z-0 merc-conf)
            (p "merc" "for-bank" z-1
              (enc n cost account bank-conf ncb
                (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
            (p "merc" "cost" z-1 cost) (p "merc" "ncm" z-1 ncm)
            (p "merc" "item" z-1 item)
            (p "merc" "merc-conf" z-1 merc-conf)
            (p "bank" "merc-conf-decommit" z-2
              (hash ncm item merc-conf))
            (p "bank" "account" z-2 account) (p "bank" "cost" z-2 cost)
            (p "bank" "n" z-2 n) (p "bank" "ncb" z-2 ncb)
            (p "bank" "bank-conf" z-2 bank-conf)
            (p "bank" "btr" z-2 btr) (p "bank" "mtr" z-2 mtr)
            (p "bank" "c" z-2 c) (p "bank" "m" z-2 m)
            (p "bank" "b" z-2 b)
            (p "bank" "merc-conf-decommit" z-3
              (hash ncm item merc-conf))
            (p "bank" "account" z-3 account) (p "bank" "cost" z-3 cost)
            (p "bank" "n" z-3 n) (p "bank" "ncb" z-3 ncb)
            (p "bank" "bank-conf" z-3 bank-conf)
            (p "bank" "btr" z-3 btr-0) (p "bank" "mtr" z-3 mtr-0)
            (p "bank" "c" z-3 c) (p "bank" "m" z-3 m)
            (p "bank" "b" z-3 b)
            (p "bank" "merc-conf-decommit" z-4
              (hash ncm item merc-conf))
            (p "bank" "account" z-4 account) (p "bank" "cost" z-4 cost)
            (p "bank" "n" z-4 n) (p "bank" "ncb" z-4 ncb)
            (p "bank" "bank-conf" z-4 bank-conf)
            (p "bank" "btr" z-4 btr-1) (p "bank" "mtr" z-4 mtr-1)
            (p "bank" "c" z-4 c) (p "bank" "m" z-4 m)
            (p "bank" "b" z-4 b) (prec z 0 z-0 0) (prec z 0 z-1 0)
            (prec z 0 z-2 0) (prec z-0 1 z-3 0) (prec z-1 1 z-4 0)
            (prec z-2 1 z 1) (prec z-3 1 z-0 2) (prec z-4 1 z-1 2)
            (non (privk "sig" c)) (uniq-at btr-1 z-4 1)
            (uniq-at btr-0 z-3 1) (uniq-at btr z-2 1) (fact neq n ncb)
            (fact neq n ncm) (fact neq ncm ncb)
            (fact will-ship c m b item mtr)
            (fact buy-via c m b item cost n)
            (fact will-transfer c m b cost n mtr-1 btr-1)
            (fact will-transfer c m b cost n mtr-0 btr-0)
            (fact will-transfer c m b cost n mtr btr)))))))

(defprotocol minipay-rely-guar basic
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
  (defrule rely-cust-3
    (forall ((z strd) (mtr text) (item merchandise) (b m c name))
      (implies
        (and (p "cust" z (idx 3)) (p "cust" "mtr" z mtr)
          (p "cust" "item" z item) (p "cust" "b" z b) (p "cust" "m" z m)
          (p "cust" "c" z c))
        (fact will-ship c m b item mtr))))
  (defrule rely-cust-2
    (forall
      ((z strd) (btr mtr text) (n data) (cost amount) (b m c name))
      (implies
        (and (p "cust" z (idx 2)) (p "cust" "btr" z btr)
          (p "cust" "mtr" z mtr) (p "cust" "n" z n)
          (p "cust" "cost" z cost) (p "cust" "b" z b) (p "cust" "m" z m)
          (p "cust" "c" z c))
        (fact will-transfer c m b cost n mtr btr))))
  (defrule rely-merc-3
    (forall
      ((z strd) (n data) (cost amount) (item merchandise) (b m c name)
        (btr mtr text))
      (implies
        (and (p "merc" z (idx 3)) (p "merc" "n" z n)
          (p "merc" "cost" z cost) (p "merc" "item" z item)
          (p "merc" "b" z b) (p "merc" "m" z m) (p "merc" "c" z c)
          (p "merc" "btr" z btr) (p "merc" "mtr" z mtr))
        (and (fact buy-via c m b item cost n)
          (fact will-transfer c m b cost n mtr btr)))))
  (defrule rely-bank-1
    (forall ((z strd) (n data) (cost amount) (b m c name))
      (implies
        (and (p "bank" z (idx 1)) (p "bank" "n" z n)
          (p "bank" "cost" z cost) (p "bank" "b" z b) (p "bank" "m" z m)
          (p "bank" "c" z c))
        (exists ((item merchandise))
          (fact buy-via c m b item cost n)))))
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
  (lang (acct atom) (amount atom) (merchandise atom) (sign sign)
    (order (tuple 5)) (bconf (tuple 3)) (mconf (tuple 3))
    (payreq (tuple 7))))

(defgoal minipay-rely-guar
  (forall
    ((for-bank bank-conf-commit bank-conf-decommit mesg) (cost amount)
      (n ncm data) (item merchandise) (merc-conf btr mtr text)
      (c m b name) (z strd))
    (implies
      (and (p "merc" z 4) (p "merc" "for-bank" z for-bank)
        (p "merc" "bank-conf-commit" z bank-conf-commit)
        (p "merc" "bank-conf-decommit" z bank-conf-decommit)
        (p "merc" "cost" z cost) (p "merc" "n" z n)
        (p "merc" "ncm" z ncm) (p "merc" "item" z item)
        (p "merc" "merc-conf" z merc-conf) (p "merc" "btr" z btr)
        (p "merc" "mtr" z mtr) (p "merc" "c" z c) (p "merc" "m" z m)
        (p "merc" "b" z b) (non (privk "enc" m)) (non (privk "enc" b))
        (non (privk "sig" m)) (non (privk "sig" b)) (uniq-at mtr z 1))
      (exists
        ((account acct) (ncb data) (bank-conf text) (z-0 z-1 strd))
        (and
          (= for-bank
            (enc n cost account bank-conf ncb
              (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
          (= bank-conf-commit (hash n (hash ncb bank-conf)))
          (= bank-conf-decommit (hash ncb bank-conf)) (p "bank" z-0 2)
          (p "cust" z-1 1)
          (p "merc" "for-bank" z
            (enc n cost account bank-conf ncb
              (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
          (p "merc" "bank-conf-commit" z (hash n (hash ncb bank-conf)))
          (p "merc" "bank-conf-decommit" z (hash ncb bank-conf))
          (p "bank" "merc-conf-decommit" z-0 (hash ncm item merc-conf))
          (p "bank" "account" z-0 account) (p "bank" "cost" z-0 cost)
          (p "bank" "n" z-0 n) (p "bank" "ncb" z-0 ncb)
          (p "bank" "bank-conf" z-0 bank-conf) (p "bank" "btr" z-0 btr)
          (p "bank" "mtr" z-0 mtr) (p "bank" "c" z-0 c)
          (p "bank" "m" z-0 m) (p "bank" "b" z-0 b)
          (p "cust" "account" z-1 account) (p "cust" "cost" z-1 cost)
          (p "cust" "n" z-1 n) (p "cust" "ncb" z-1 ncb)
          (p "cust" "ncm" z-1 ncm) (p "cust" "item" z-1 item)
          (p "cust" "merc-conf" z-1 merc-conf)
          (p "cust" "bank-conf" z-1 bank-conf) (p "cust" "c" z-1 c)
          (p "cust" "m" z-1 m) (p "cust" "b" z-1 b) (prec z 1 z-0 0)
          (prec z-0 1 z 2) (prec z-1 0 z 0) (non (privk "sig" c))
          (uniq-at btr z-0 1) (fact neq n ncb) (fact neq n ncm)
          (fact neq ncm ncb) (fact buy-via c m b item cost n)
          (fact will-ship c m b item mtr)
          (fact will-transfer c m b cost n mtr btr))))))

(defprotocol minipay-rely-guar basic
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
  (defrule rely-cust-3
    (forall ((z strd) (mtr text) (item merchandise) (b m c name))
      (implies
        (and (p "cust" z (idx 3)) (p "cust" "mtr" z mtr)
          (p "cust" "item" z item) (p "cust" "b" z b) (p "cust" "m" z m)
          (p "cust" "c" z c))
        (fact will-ship c m b item mtr))))
  (defrule rely-cust-2
    (forall
      ((z strd) (btr mtr text) (n data) (cost amount) (b m c name))
      (implies
        (and (p "cust" z (idx 2)) (p "cust" "btr" z btr)
          (p "cust" "mtr" z mtr) (p "cust" "n" z n)
          (p "cust" "cost" z cost) (p "cust" "b" z b) (p "cust" "m" z m)
          (p "cust" "c" z c))
        (fact will-transfer c m b cost n mtr btr))))
  (defrule rely-merc-3
    (forall
      ((z strd) (n data) (cost amount) (item merchandise) (b m c name)
        (btr mtr text))
      (implies
        (and (p "merc" z (idx 3)) (p "merc" "n" z n)
          (p "merc" "cost" z cost) (p "merc" "item" z item)
          (p "merc" "b" z b) (p "merc" "m" z m) (p "merc" "c" z c)
          (p "merc" "btr" z btr) (p "merc" "mtr" z mtr))
        (and (fact buy-via c m b item cost n)
          (fact will-transfer c m b cost n mtr btr)))))
  (defrule rely-bank-1
    (forall ((z strd) (n data) (cost amount) (b m c name))
      (implies
        (and (p "bank" z (idx 1)) (p "bank" "n" z n)
          (p "bank" "cost" z cost) (p "bank" "b" z b) (p "bank" "m" z m)
          (p "bank" "c" z c))
        (exists ((item merchandise))
          (fact buy-via c m b item cost n)))))
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
  (lang (acct atom) (amount atom) (merchandise atom) (sign sign)
    (order (tuple 5)) (bconf (tuple 3)) (mconf (tuple 3))
    (payreq (tuple 7))))

(defgoal minipay-rely-guar
  (forall
    ((for-bank bank-conf-commit bank-conf-decommit mesg) (cost amount)
      (n ncm data) (item merchandise) (merc-conf btr mtr text)
      (c m b name) (z strd))
    (implies
      (and (p "merc" z 4) (p "merc" "for-bank" z for-bank)
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
            (= bank-conf-commit (hash n bank-conf-decommit))
            (p "bank" z-0 2) (p "cust" z-1 1)
            (p "merc" "for-bank" z
              (enc n cost account bank-conf ncb
                (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
            (p "merc" "bank-conf-commit" z (hash n bank-conf-decommit))
            (p "bank" "merc-conf-decommit" z-0
              (hash ncm item merc-conf))
            (p "bank" "account" z-0 account) (p "bank" "cost" z-0 cost)
            (p "bank" "n" z-0 n) (p "bank" "ncb" z-0 ncb)
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
            (fact will-ship c m b item mtr)
            (fact will-transfer c m b cost n mtr btr)))
        (exists
          ((account account-0 acct) (ncb n-0 ncb-0 ncm-0 data)
            (item-0 merchandise)
            (bank-conf merc-conf-0 bank-conf-0 text) (z-0 z-1 z-2 strd))
          (and
            (= for-bank
              (enc n-0 cost account-0 bank-conf-0 ncb-0
                (hash n-0 (hash ncm-0 item-0 merc-conf-0))
                (pubk "enc" b)))
            (= bank-conf-commit (hash n bank-conf-decommit))
            (p "bank" z-0 2) (p "cust" z-1 1) (p "cust" z-2 1)
            (p "merc" "for-bank" z
              (enc n-0 cost account-0 bank-conf-0 ncb-0
                (hash n-0 (hash ncm-0 item-0 merc-conf-0))
                (pubk "enc" b)))
            (p "merc" "bank-conf-commit" z (hash n bank-conf-decommit))
            (p "bank" "merc-conf-decommit" z-0
              (hash ncm item merc-conf))
            (p "bank" "account" z-0 account) (p "bank" "cost" z-0 cost)
            (p "bank" "n" z-0 n) (p "bank" "ncb" z-0 ncb)
            (p "bank" "bank-conf" z-0 bank-conf)
            (p "bank" "btr" z-0 btr) (p "bank" "mtr" z-0 mtr)
            (p "bank" "c" z-0 c) (p "bank" "m" z-0 m)
            (p "bank" "b" z-0 b) (p "cust" "account" z-1 account-0)
            (p "cust" "cost" z-1 cost) (p "cust" "n" z-1 n-0)
            (p "cust" "ncb" z-1 ncb-0) (p "cust" "ncm" z-1 ncm-0)
            (p "cust" "item" z-1 item-0)
            (p "cust" "merc-conf" z-1 merc-conf-0)
            (p "cust" "bank-conf" z-1 bank-conf-0) (p "cust" "c" z-1 c)
            (p "cust" "m" z-1 m) (p "cust" "b" z-1 b)
            (p "cust" "account" z-2 account) (p "cust" "cost" z-2 cost)
            (p "cust" "n" z-2 n) (p "cust" "ncb" z-2 ncb)
            (p "cust" "ncm" z-2 ncm) (p "cust" "item" z-2 item)
            (p "cust" "merc-conf" z-2 merc-conf)
            (p "cust" "bank-conf" z-2 bank-conf) (p "cust" "c" z-2 c)
            (p "cust" "m" z-2 m) (p "cust" "b" z-2 b) (prec z 1 z-0 0)
            (prec z-0 1 z 2) (prec z-1 0 z 0) (prec z-2 0 z-0 0)
            (non (privk "sig" c)) (uniq-at btr z-0 1) (fact neq n ncb)
            (fact neq n-0 ncb-0) (fact neq n ncm) (fact neq n-0 ncm-0)
            (fact neq ncm ncb) (fact neq ncm-0 ncb-0)
            (fact buy-via c m b item cost n)
            (fact buy-via c m b item-0 cost n-0)
            (fact will-ship c m b item mtr)
            (fact will-transfer c m b cost n mtr btr)))))))

(defprotocol minipay-rely-guar basic
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
  (defrule rely-cust-3
    (forall ((z strd) (mtr text) (item merchandise) (b m c name))
      (implies
        (and (p "cust" z (idx 3)) (p "cust" "mtr" z mtr)
          (p "cust" "item" z item) (p "cust" "b" z b) (p "cust" "m" z m)
          (p "cust" "c" z c))
        (fact will-ship c m b item mtr))))
  (defrule rely-cust-2
    (forall
      ((z strd) (btr mtr text) (n data) (cost amount) (b m c name))
      (implies
        (and (p "cust" z (idx 2)) (p "cust" "btr" z btr)
          (p "cust" "mtr" z mtr) (p "cust" "n" z n)
          (p "cust" "cost" z cost) (p "cust" "b" z b) (p "cust" "m" z m)
          (p "cust" "c" z c))
        (fact will-transfer c m b cost n mtr btr))))
  (defrule rely-merc-3
    (forall
      ((z strd) (n data) (cost amount) (item merchandise) (b m c name)
        (btr mtr text))
      (implies
        (and (p "merc" z (idx 3)) (p "merc" "n" z n)
          (p "merc" "cost" z cost) (p "merc" "item" z item)
          (p "merc" "b" z b) (p "merc" "m" z m) (p "merc" "c" z c)
          (p "merc" "btr" z btr) (p "merc" "mtr" z mtr))
        (and (fact buy-via c m b item cost n)
          (fact will-transfer c m b cost n mtr btr)))))
  (defrule rely-bank-1
    (forall ((z strd) (n data) (cost amount) (b m c name))
      (implies
        (and (p "bank" z (idx 1)) (p "bank" "n" z n)
          (p "bank" "cost" z cost) (p "bank" "b" z b) (p "bank" "m" z m)
          (p "bank" "c" z c))
        (exists ((item merchandise))
          (fact buy-via c m b item cost n)))))
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
  (lang (acct atom) (amount atom) (merchandise atom) (sign sign)
    (order (tuple 5)) (bconf (tuple 3)) (mconf (tuple 3))
    (payreq (tuple 7))))

(defgoal minipay-rely-guar
  (forall
    ((for-bank bank-conf-commit mesg) (cost amount) (n ncm data)
      (item merchandise) (merc-conf text) (c m b name) (z strd))
    (implies
      (and (p "merc" z 1) (p "merc" "for-bank" z for-bank)
        (p "merc" "bank-conf-commit" z bank-conf-commit)
        (p "merc" "cost" z cost) (p "merc" "n" z n)
        (p "merc" "ncm" z ncm) (p "merc" "item" z item)
        (p "merc" "merc-conf" z merc-conf) (p "merc" "c" z c)
        (p "merc" "m" z m) (p "merc" "b" z b) (non (privk "enc" m))
        (non (privk "sig" c)))
      (or
        (exists ((account acct) (ncb data) (bank-conf text) (z-0 strd))
          (and
            (= for-bank
              (enc n cost account bank-conf ncb
                (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
            (= bank-conf-commit (hash n (hash ncb bank-conf)))
            (p "cust" z-0 1)
            (p "merc" "for-bank" z
              (enc n cost account bank-conf ncb
                (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
            (p "merc" "bank-conf-commit" z
              (hash n (hash ncb bank-conf)))
            (p "cust" "account" z-0 account) (p "cust" "cost" z-0 cost)
            (p "cust" "n" z-0 n) (p "cust" "ncb" z-0 ncb)
            (p "cust" "ncm" z-0 ncm) (p "cust" "item" z-0 item)
            (p "cust" "merc-conf" z-0 merc-conf)
            (p "cust" "bank-conf" z-0 bank-conf) (p "cust" "c" z-0 c)
            (p "cust" "m" z-0 m) (p "cust" "b" z-0 b) (prec z-0 0 z 0)
            (fact neq n ncb) (fact neq n ncm) (fact neq ncm ncb)
            (fact buy-via c m b item cost n)))
        (exists
          ((account acct) (n-0 ncb ncm-0 data) (item-0 merchandise)
            (merc-conf-0 bank-conf mtr text) (z-0 z-1 strd))
          (and
            (= for-bank
              (enc n-0 cost account bank-conf ncb
                (hash n-0 (hash ncm-0 item-0 merc-conf-0))
                (pubk "enc" b))) (p "cust" z-0 1) (p "merc" z-1 2)
            (p "merc" "for-bank" z
              (enc n-0 cost account bank-conf ncb
                (hash n-0 (hash ncm-0 item-0 merc-conf-0))
                (pubk "enc" b))) (p "cust" "account" z-0 account)
            (p "cust" "cost" z-0 cost) (p "cust" "n" z-0 n-0)
            (p "cust" "ncb" z-0 ncb) (p "cust" "ncm" z-0 ncm-0)
            (p "cust" "item" z-0 item-0)
            (p "cust" "merc-conf" z-0 merc-conf-0)
            (p "cust" "bank-conf" z-0 bank-conf) (p "cust" "c" z-0 c)
            (p "cust" "m" z-0 m) (p "cust" "b" z-0 b)
            (p "merc" "for-bank" z-1
              (enc n-0 cost account bank-conf ncb
                (hash n-0 (hash ncm-0 item-0 merc-conf-0))
                (pubk "enc" b)))
            (p "merc" "bank-conf-commit" z-1
              (hash n-0 (hash ncb bank-conf)))
            (p "merc" "cost" z-1 cost) (p "merc" "n" z-1 n-0)
            (p "merc" "ncm" z-1 ncm-0) (p "merc" "item" z-1 item-0)
            (p "merc" "merc-conf" z-1 merc-conf-0)
            (p "merc" "mtr" z-1 mtr) (p "merc" "c" z-1 c)
            (p "merc" "m" z-1 m) (p "merc" "b" z-1 b) (prec z-0 0 z-1 0)
            (prec z-1 1 z 0) (uniq-at mtr z-1 1) (fact neq n-0 ncb)
            (fact neq n-0 ncm-0) (fact neq ncm-0 ncb)
            (fact buy-via c m b item-0 cost n-0)))))))

(defprotocol minipay-rely-guar basic
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
  (defrule rely-cust-3
    (forall ((z strd) (mtr text) (item merchandise) (b m c name))
      (implies
        (and (p "cust" z (idx 3)) (p "cust" "mtr" z mtr)
          (p "cust" "item" z item) (p "cust" "b" z b) (p "cust" "m" z m)
          (p "cust" "c" z c))
        (fact will-ship c m b item mtr))))
  (defrule rely-cust-2
    (forall
      ((z strd) (btr mtr text) (n data) (cost amount) (b m c name))
      (implies
        (and (p "cust" z (idx 2)) (p "cust" "btr" z btr)
          (p "cust" "mtr" z mtr) (p "cust" "n" z n)
          (p "cust" "cost" z cost) (p "cust" "b" z b) (p "cust" "m" z m)
          (p "cust" "c" z c))
        (fact will-transfer c m b cost n mtr btr))))
  (defrule rely-merc-3
    (forall
      ((z strd) (n data) (cost amount) (item merchandise) (b m c name)
        (btr mtr text))
      (implies
        (and (p "merc" z (idx 3)) (p "merc" "n" z n)
          (p "merc" "cost" z cost) (p "merc" "item" z item)
          (p "merc" "b" z b) (p "merc" "m" z m) (p "merc" "c" z c)
          (p "merc" "btr" z btr) (p "merc" "mtr" z mtr))
        (and (fact buy-via c m b item cost n)
          (fact will-transfer c m b cost n mtr btr)))))
  (defrule rely-bank-1
    (forall ((z strd) (n data) (cost amount) (b m c name))
      (implies
        (and (p "bank" z (idx 1)) (p "bank" "n" z n)
          (p "bank" "cost" z cost) (p "bank" "b" z b) (p "bank" "m" z m)
          (p "bank" "c" z c))
        (exists ((item merchandise))
          (fact buy-via c m b item cost n)))))
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
  (lang (acct atom) (amount atom) (merchandise atom) (sign sign)
    (order (tuple 5)) (bconf (tuple 3)) (mconf (tuple 3))
    (payreq (tuple 7))))

(defgoal minipay-rely-guar
  (forall
    ((for-bank bank-conf-commit mesg) (cost amount) (n ncm data)
      (item merchandise) (merc-conf text) (c m b name) (z strd))
    (implies
      (and (p "merc" z 1) (p "merc" "for-bank" z for-bank)
        (p "merc" "bank-conf-commit" z bank-conf-commit)
        (p "merc" "cost" z cost) (p "merc" "n" z n)
        (p "merc" "ncm" z ncm) (p "merc" "item" z item)
        (p "merc" "merc-conf" z merc-conf) (p "merc" "c" z c)
        (p "merc" "m" z m) (p "merc" "b" z b) (non (privk "enc" m))
        (non (privk "enc" b)) (non (privk "sig" c)))
      (exists ((account acct) (ncb data) (bank-conf text) (z-0 strd))
        (and
          (= for-bank
            (enc n cost account bank-conf ncb
              (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
          (= bank-conf-commit (hash n (hash ncb bank-conf)))
          (p "cust" z-0 1)
          (p "merc" "for-bank" z
            (enc n cost account bank-conf ncb
              (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
          (p "merc" "bank-conf-commit" z (hash n (hash ncb bank-conf)))
          (p "cust" "account" z-0 account) (p "cust" "cost" z-0 cost)
          (p "cust" "n" z-0 n) (p "cust" "ncb" z-0 ncb)
          (p "cust" "ncm" z-0 ncm) (p "cust" "item" z-0 item)
          (p "cust" "merc-conf" z-0 merc-conf)
          (p "cust" "bank-conf" z-0 bank-conf) (p "cust" "c" z-0 c)
          (p "cust" "m" z-0 m) (p "cust" "b" z-0 b) (prec z-0 0 z 0)
          (fact neq n ncb) (fact neq n ncm) (fact neq ncm ncb)
          (fact buy-via c m b item cost n))))))
