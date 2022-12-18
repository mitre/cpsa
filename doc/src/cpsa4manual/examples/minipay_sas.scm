(herald minipay (try-old-strands) (bound 16) (limit 5000))

(comment "CPSA 4.4.0")
(comment "Coherent logic")

(comment "CPSA 4.4.0")

(comment "All input read from minipay.scm")

(comment "Step count limited to 5000")

(comment "Strand count bounded at 16")

(comment "Old strands tried first")

(defprotocol minipay basic
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

(defgoal minipay
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
          (prec z-1 4 z 2) (uniq-at mtr z-1 1) (uniq-at btr z-0 1)
          (fact neq n ncb) (fact neq n ncm) (fact neq ncm ncb))))))

(defprotocol minipay basic
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

(defgoal minipay
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
      (exists ((account acct) (ncb data) (bank-conf text) (z-0 strd))
        (and
          (= for-bank
            (enc n cost account bank-conf ncb
              (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
          (= bank-conf-decommit (hash ncb bank-conf)) (p "bank" z-0 2)
          (p "merc" "for-bank" z
            (enc n cost account bank-conf ncb
              (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
          (p "merc" "bank-conf-decommit" z (hash ncb bank-conf))
          (p "bank" "merc-conf-decommit" z-0 (hash ncm item merc-conf))
          (p "bank" "account" z-0 account) (p "bank" "cost" z-0 cost)
          (p "bank" "n" z-0 n) (p "bank" "ncb" z-0 ncb)
          (p "bank" "bank-conf" z-0 bank-conf) (p "bank" "btr" z-0 btr)
          (p "bank" "mtr" z-0 mtr) (p "bank" "c" z-0 c)
          (p "bank" "m" z-0 m) (p "bank" "b" z-0 b) (prec z 1 z-0 0)
          (prec z-0 1 z 2) (uniq-at btr z-0 1))))))

(defprotocol minipay basic
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

(defgoal minipay
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
          (fact neq n ncb) (fact neq n ncm) (fact neq ncm ncb))))))

(defprotocol minipay basic
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

(defgoal minipay
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
          (fact neq n ncm) (fact neq ncm ncb))))))

(defprotocol minipay basic
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

(defgoal minipay
  (forall
    ((account acct) (cost amount) (n ncb ncm data) (item merchandise)
      (bank-conf btr mtr merc-conf mtr-0 btr-0 mtr-1 text) (c m b name)
      (z z-0 z-1 strd))
    (implies
      (and (p "bank" z 2) (p "cust" z-0 3) (p "merc" z-1 2)
        (p "bank" "merc-conf-decommit" z (hash ncm item merc-conf))
        (p "bank" "account" z account) (p "bank" "cost" z cost)
        (p "bank" "n" z n) (p "bank" "ncb" z ncb)
        (p "bank" "bank-conf" z bank-conf) (p "bank" "btr" z btr)
        (p "bank" "mtr" z mtr) (p "bank" "c" z c) (p "bank" "m" z m)
        (p "bank" "b" z b) (p "cust" "account" z-0 account)
        (p "cust" "cost" z-0 cost) (p "cust" "n" z-0 n)
        (p "cust" "ncb" z-0 ncb) (p "cust" "ncm" z-0 ncm)
        (p "cust" "item" z-0 item) (p "cust" "merc-conf" z-0 merc-conf)
        (p "cust" "bank-conf" z-0 bank-conf) (p "cust" "btr" z-0 btr-0)
        (p "cust" "mtr" z-0 mtr-1) (p "cust" "c" z-0 c)
        (p "cust" "m" z-0 m) (p "cust" "b" z-0 b)
        (p "merc" "for-bank" z-1
          (enc n cost account bank-conf ncb
            (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
        (p "merc" "bank-conf-commit" z-1 (hash n (hash ncb bank-conf)))
        (p "merc" "cost" z-1 cost) (p "merc" "n" z-1 n)
        (p "merc" "ncm" z-1 ncm) (p "merc" "item" z-1 item)
        (p "merc" "merc-conf" z-1 merc-conf) (p "merc" "mtr" z-1 mtr-0)
        (p "merc" "c" z-1 c) (p "merc" "m" z-1 m) (p "merc" "b" z-1 b)
        (prec z-0 0 z-1 0) (prec z-1 1 z 0) (non (privk "enc" m))
        (non (privk "sig" c)) (non (privk "sig" m))
        (non (privk "sig" b)) (uniq-at btr z 1) (uniq-at mtr-0 z-1 1)
        (uniq-at ncm z-0 0) (uniq-at n z-0 0) (uniq-at ncb z-0 0)
        (fact neq n ncb) (fact neq n ncm) (fact neq ncm ncb))
      (or
        (and (= mtr-0 mtr) (= btr-0 btr) (= mtr-1 mtr) (p "merc" z-1 5)
          (p "cust" "btr" z-0 btr) (p "cust" "mtr" z-0 mtr)
          (p "merc" "bank-conf-decommit" z-1 (hash ncb bank-conf))
          (p "merc" "btr" z-1 btr) (p "merc" "mtr" z-1 mtr)
          (prec z 1 z-1 2) (prec z-1 3 z-0 1) (prec z-1 4 z-0 2)
          (uniq-at mtr z-1 1))
        (exists ((z-2 strd))
          (and (= btr-0 btr) (= mtr-1 mtr) (p "merc" z-2 5)
            (p "cust" "btr" z-0 btr) (p "cust" "mtr" z-0 mtr)
            (p "merc" "for-bank" z-2
              (enc n cost account bank-conf ncb
                (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
            (p "merc" "bank-conf-commit" z-2
              (hash n (hash ncb bank-conf)))
            (p "merc" "bank-conf-decommit" z-2 (hash ncb bank-conf))
            (p "merc" "cost" z-2 cost) (p "merc" "n" z-2 n)
            (p "merc" "ncm" z-2 ncm) (p "merc" "item" z-2 item)
            (p "merc" "merc-conf" z-2 merc-conf)
            (p "merc" "btr" z-2 btr) (p "merc" "mtr" z-2 mtr)
            (p "merc" "c" z-2 c) (p "merc" "m" z-2 m)
            (p "merc" "b" z-2 b) (prec z 1 z-2 2) (prec z-0 0 z-2 0)
            (prec z-2 1 z 0) (prec z-2 3 z-0 1) (prec z-2 4 z-0 2)
            (uniq-at mtr z-2 1)))
        (exists ((z-2 strd))
          (and (= mtr-1 mtr-0) (p "bank" z-2 2) (p "merc" z-1 5)
            (p "cust" "mtr" z-0 mtr-0)
            (p "bank" "merc-conf-decommit" z-2
              (hash ncm item merc-conf))
            (p "bank" "account" z-2 account) (p "bank" "cost" z-2 cost)
            (p "bank" "n" z-2 n) (p "bank" "ncb" z-2 ncb)
            (p "bank" "bank-conf" z-2 bank-conf)
            (p "bank" "btr" z-2 btr-0) (p "bank" "mtr" z-2 mtr-0)
            (p "bank" "c" z-2 c) (p "bank" "m" z-2 m)
            (p "bank" "b" z-2 b)
            (p "merc" "bank-conf-decommit" z-1 (hash ncb bank-conf))
            (p "merc" "btr" z-1 btr-0) (prec z-2 1 z-1 2)
            (prec z-1 1 z-2 0) (prec z-1 3 z-0 1) (prec z-1 4 z-0 2)
            (uniq-at btr-0 z-2 1)))
        (exists ((z-2 z-3 strd))
          (and (p "bank" z-2 2) (p "merc" z-3 5)
            (p "bank" "merc-conf-decommit" z-2
              (hash ncm item merc-conf))
            (p "bank" "account" z-2 account) (p "bank" "cost" z-2 cost)
            (p "bank" "n" z-2 n) (p "bank" "ncb" z-2 ncb)
            (p "bank" "bank-conf" z-2 bank-conf)
            (p "bank" "btr" z-2 btr-0) (p "bank" "mtr" z-2 mtr-1)
            (p "bank" "c" z-2 c) (p "bank" "m" z-2 m)
            (p "bank" "b" z-2 b)
            (p "merc" "for-bank" z-3
              (enc n cost account bank-conf ncb
                (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
            (p "merc" "bank-conf-commit" z-3
              (hash n (hash ncb bank-conf)))
            (p "merc" "bank-conf-decommit" z-3 (hash ncb bank-conf))
            (p "merc" "cost" z-3 cost) (p "merc" "n" z-3 n)
            (p "merc" "ncm" z-3 ncm) (p "merc" "item" z-3 item)
            (p "merc" "merc-conf" z-3 merc-conf)
            (p "merc" "btr" z-3 btr-0) (p "merc" "mtr" z-3 mtr-1)
            (p "merc" "c" z-3 c) (p "merc" "m" z-3 m)
            (p "merc" "b" z-3 b) (prec z-0 0 z-3 0) (prec z-2 1 z-3 2)
            (prec z-3 1 z-2 0) (prec z-3 3 z-0 1) (prec z-3 4 z-0 2)
            (uniq-at mtr-1 z-3 1) (uniq-at btr-0 z-2 1)))))))

(defprotocol minipay basic
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

(defgoal minipay
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
      (exists ((account acct) (ncb data) (bank-conf text) (z-0 strd))
        (and
          (= for-bank
            (enc n cost account bank-conf ncb
              (hash n (hash ncm item merc-conf)) (pubk "enc" b)))
          (= bank-conf-commit (hash n (hash ncb bank-conf)))
          (= bank-conf-decommit (hash ncb bank-conf)) (p "bank" z-0 2)
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
          (p "bank" "m" z-0 m) (p "bank" "b" z-0 b) (prec z 1 z-0 0)
          (prec z-0 1 z 2) (uniq-at btr z-0 1))))))

(defprotocol minipay basic
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

(defgoal minipay
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
      (exists ((account acct) (ncb data) (bank-conf text) (z-0 strd))
        (and (= bank-conf-commit (hash n bank-conf-decommit))
          (p "bank" z-0 2)
          (p "merc" "bank-conf-commit" z (hash n bank-conf-decommit))
          (p "bank" "merc-conf-decommit" z-0 (hash ncm item merc-conf))
          (p "bank" "account" z-0 account) (p "bank" "cost" z-0 cost)
          (p "bank" "n" z-0 n) (p "bank" "ncb" z-0 ncb)
          (p "bank" "bank-conf" z-0 bank-conf) (p "bank" "btr" z-0 btr)
          (p "bank" "mtr" z-0 mtr) (p "bank" "c" z-0 c)
          (p "bank" "m" z-0 m) (p "bank" "b" z-0 b) (prec z 1 z-0 0)
          (prec z-0 1 z 2) (uniq-at btr z-0 1))))))

(defprotocol minipay basic
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

(defgoal minipay
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
            (fact neq n ncb) (fact neq n ncm) (fact neq ncm ncb)))
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
            (fact neq n-0 ncm-0) (fact neq ncm-0 ncb)))))))

(defprotocol minipay basic
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

(defgoal minipay
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
          (fact neq n ncb) (fact neq n ncm) (fact neq ncm ncb))))))
