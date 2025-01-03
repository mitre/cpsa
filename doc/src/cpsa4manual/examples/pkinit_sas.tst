(herald "Kerberos PKINIT")

(comment "CPSA 4.4.0")
(comment "All input read from pkinit_sas.scm")

(defprotocol pkinit-flawed basic
  (defrole client
    (vars (c t as name) (n2 n1 text) (tc tk tgt data) (k ak skey))
    (trace (send (cat (enc tc n2 (privk c)) c t n1))
      (recv
        (cat (enc (enc k n2 (privk as)) (pubk c)) c tgt
          (enc ak n1 tk t k))))
    (uniq-orig n2 n1))
  (defrole auth
    (vars (c t as name) (n2 n1 text) (tc tk tgt data) (k ak skey))
    (trace (recv (cat (enc tc n2 (privk c)) c t n1))
      (send
        (cat (enc (enc k n2 (privk as)) (pubk c)) c tgt
          (enc ak n1 tk t k))))
    (uniq-orig k ak))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton pkinit-flawed
  (vars (tc tk tgt data) (k ak skey) (n2 n1 text) (c as t name))
  (defstrand client 2 (tc tc) (tk tk) (tgt tgt) (k k) (ak ak) (n2 n2)
    (n1 n1) (c c) (t t) (as as))
  (non-orig (privk c) (privk as))
  (uniq-orig n2 n1)
  (goals
    (forall
      ((tc tk tgt data) (k ak skey) (n2 n1 text) (c as t name) (z strd))
      (implies
        (and (p "client" z 2) (p "client" "tc" z tc)
          (p "client" "tk" z tk) (p "client" "tgt" z tgt)
          (p "client" "k" z k) (p "client" "ak" z ak)
          (p "client" "n2" z n2) (p "client" "n1" z n1)
          (p "client" "c" z c) (p "client" "t" z t)
          (p "client" "as" z as) (non (privk c)) (non (privk as))
          (uniq-at n2 z 0) (uniq-at n1 z 0))
        (exists
          ((tc-0 tk-0 tgt-0 data) (ak-0 skey) (n1-0 text) (c-0 t-0 name)
            (z-0 strd))
          (and (p "auth" z-0 2) (p "auth" "tc" z-0 tc-0)
            (p "auth" "tk" z-0 tk-0) (p "auth" "tgt" z-0 tgt-0)
            (p "auth" "k" z-0 k) (p "auth" "ak" z-0 ak-0)
            (p "auth" "n2" z-0 n2) (p "auth" "n1" z-0 n1-0)
            (p "auth" "c" z-0 c-0) (p "auth" "t" z-0 t-0)
            (p "auth" "as" z-0 as) (prec z 0 z-0 0) (prec z-0 1 z 1)
            (uniq-at k z-0 1) (uniq-at ak-0 z-0 1))))))
  (traces
    ((send (cat (enc tc n2 (privk c)) c t n1))
      (recv
        (cat (enc (enc k n2 (privk as)) (pubk c)) c tgt
          (enc ak n1 tk t k)))))
  (label 0)
  (unrealized (0 1))
  (origs (n2 (0 0)) (n1 (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton pkinit-flawed
  (vars (tc tk tgt tc-0 tk-0 tgt-0 data) (k ak ak-0 skey)
    (n2 n1 n1-0 text) (c as t c-0 t-0 name))
  (defstrand client 2 (tc tc) (tk tk) (tgt tgt) (k k) (ak ak) (n2 n2)
    (n1 n1) (c c) (t t) (as as))
  (defstrand auth 2 (tc tc-0) (tk tk-0) (tgt tgt-0) (k k) (ak ak-0)
    (n2 n2) (n1 n1-0) (c c-0) (t t-0) (as as))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk c) (privk as))
  (uniq-orig k ak-0 n2 n1)
  (operation encryption-test (added-strand auth 2) (enc k n2 (privk as))
    (0 1))
  (traces
    ((send (cat (enc tc n2 (privk c)) c t n1))
      (recv
        (cat (enc (enc k n2 (privk as)) (pubk c)) c tgt
          (enc ak n1 tk t k))))
    ((recv (cat (enc tc-0 n2 (privk c-0)) c-0 t-0 n1-0))
      (send
        (cat (enc (enc k n2 (privk as)) (pubk c-0)) c-0 tgt-0
          (enc ak-0 n1-0 tk-0 t-0 k)))))
  (label 1)
  (parent 0)
  (realized)
  (shape)
  (satisfies yes)
  (maps
    ((0)
      ((tc tc) (tk tk) (tgt tgt) (k k) (ak ak) (n2 n2) (n1 n1) (c c)
        (as as) (t t))))
  (origs (k (1 1)) (ak-0 (1 1)) (n2 (0 0)) (n1 (0 0))))

(comment "Nothing left to do")

(defprotocol pkinit-fix1 basic
  (defrole client
    (vars (c t as name) (n2 n1 text) (tc tk tgt data) (k ak skey))
    (trace (send (cat (enc tc n2 (privk c)) c t n1))
      (recv
        (cat (enc (enc k n2 c (privk as)) (pubk c)) c tgt
          (enc ak n1 tk t k))))
    (uniq-orig n2 n1))
  (defrole auth
    (vars (c t as name) (n2 n1 text) (tc tk tgt data) (k ak skey))
    (trace (recv (cat (enc tc n2 (privk c)) c t n1))
      (send
        (cat (enc (enc k n2 c (privk as)) (pubk c)) c tgt
          (enc ak n1 tk t k))))
    (uniq-orig k ak))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton pkinit-fix1
  (vars (tc tk tgt data) (k ak skey) (n2 n1 text) (c as t name))
  (defstrand client 2 (tc tc) (tk tk) (tgt tgt) (k k) (ak ak) (n2 n2)
    (n1 n1) (c c) (t t) (as as))
  (non-orig (privk c) (privk as))
  (uniq-orig n2 n1)
  (goals
    (forall
      ((tc tk tgt data) (k ak skey) (n2 n1 text) (c as t name) (z strd))
      (implies
        (and (p "client" z 2) (p "client" "tc" z tc)
          (p "client" "tk" z tk) (p "client" "tgt" z tgt)
          (p "client" "k" z k) (p "client" "ak" z ak)
          (p "client" "n2" z n2) (p "client" "n1" z n1)
          (p "client" "c" z c) (p "client" "t" z t)
          (p "client" "as" z as) (non (privk c)) (non (privk as))
          (uniq-at n2 z 0) (uniq-at n1 z 0))
        (exists ((tgt-0 data) (z-0 strd))
          (and (p "auth" z-0 2) (p "auth" "tc" z-0 tc)
            (p "auth" "tk" z-0 tk) (p "auth" "tgt" z-0 tgt-0)
            (p "auth" "k" z-0 k) (p "auth" "ak" z-0 ak)
            (p "auth" "n2" z-0 n2) (p "auth" "n1" z-0 n1)
            (p "auth" "c" z-0 c) (p "auth" "t" z-0 t)
            (p "auth" "as" z-0 as) (prec z 0 z-0 0) (prec z-0 1 z 1)
            (uniq-at k z-0 1) (uniq-at ak z-0 1))))))
  (traces
    ((send (cat (enc tc n2 (privk c)) c t n1))
      (recv
        (cat (enc (enc k n2 c (privk as)) (pubk c)) c tgt
          (enc ak n1 tk t k)))))
  (label 2)
  (unrealized (0 1))
  (origs (n2 (0 0)) (n1 (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton pkinit-fix1
  (vars (tc tk tgt tc-0 tk-0 tgt-0 data) (k ak ak-0 skey)
    (n2 n1 n1-0 text) (c as t t-0 name))
  (defstrand client 2 (tc tc) (tk tk) (tgt tgt) (k k) (ak ak) (n2 n2)
    (n1 n1) (c c) (t t) (as as))
  (defstrand auth 2 (tc tc-0) (tk tk-0) (tgt tgt-0) (k k) (ak ak-0)
    (n2 n2) (n1 n1-0) (c c) (t t-0) (as as))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk c) (privk as))
  (uniq-orig k ak-0 n2 n1)
  (operation encryption-test (added-strand auth 2)
    (enc k n2 c (privk as)) (0 1))
  (traces
    ((send (cat (enc tc n2 (privk c)) c t n1))
      (recv
        (cat (enc (enc k n2 c (privk as)) (pubk c)) c tgt
          (enc ak n1 tk t k))))
    ((recv (cat (enc tc-0 n2 (privk c)) c t-0 n1-0))
      (send
        (cat (enc (enc k n2 c (privk as)) (pubk c)) c tgt-0
          (enc ak-0 n1-0 tk-0 t-0 k)))))
  (label 3)
  (parent 2)
  (unrealized (0 1) (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton pkinit-fix1
  (vars (tc tk tgt tk-0 tgt-0 data) (k ak ak-0 skey) (n2 n1 n1-0 text)
    (c as t t-0 name))
  (defstrand client 2 (tc tc) (tk tk) (tgt tgt) (k k) (ak ak) (n2 n2)
    (n1 n1) (c c) (t t) (as as))
  (defstrand auth 2 (tc tc) (tk tk-0) (tgt tgt-0) (k k) (ak ak-0)
    (n2 n2) (n1 n1-0) (c c) (t t-0) (as as))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk c) (privk as))
  (uniq-orig k ak-0 n2 n1)
  (operation encryption-test (displaced 2 0 client 1)
    (enc tc-0 n2 (privk c)) (1 0))
  (traces
    ((send (cat (enc tc n2 (privk c)) c t n1))
      (recv
        (cat (enc (enc k n2 c (privk as)) (pubk c)) c tgt
          (enc ak n1 tk t k))))
    ((recv (cat (enc tc n2 (privk c)) c t-0 n1-0))
      (send
        (cat (enc (enc k n2 c (privk as)) (pubk c)) c tgt-0
          (enc ak-0 n1-0 tk-0 t-0 k)))))
  (label 4)
  (parent 3)
  (unrealized (0 1))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton pkinit-fix1
  (vars (tc tgt tk tgt-0 data) (k ak skey) (n2 n1 text) (c as t name))
  (defstrand client 2 (tc tc) (tk tk) (tgt tgt) (k k) (ak ak) (n2 n2)
    (n1 n1) (c c) (t t) (as as))
  (defstrand auth 2 (tc tc) (tk tk) (tgt tgt-0) (k k) (ak ak) (n2 n2)
    (n1 n1) (c c) (t t) (as as))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk c) (privk as))
  (uniq-orig k ak n2 n1)
  (operation encryption-test (displaced 2 1 auth 2)
    (enc ak-0 n1-0 tk-0 t-0 k) (0 1))
  (traces
    ((send (cat (enc tc n2 (privk c)) c t n1))
      (recv
        (cat (enc (enc k n2 c (privk as)) (pubk c)) c tgt
          (enc ak n1 tk t k))))
    ((recv (cat (enc tc n2 (privk c)) c t n1))
      (send
        (cat (enc (enc k n2 c (privk as)) (pubk c)) c tgt-0
          (enc ak n1 tk t k)))))
  (label 5)
  (parent 4)
  (realized)
  (shape)
  (satisfies yes)
  (maps
    ((0)
      ((tc tc) (tk tk) (tgt tgt) (k k) (ak ak) (n2 n2) (n1 n1) (c c)
        (as as) (t t))))
  (origs (k (1 1)) (ak (1 1)) (n2 (0 0)) (n1 (0 0))))

(defskeleton pkinit-fix1
  (vars (tc tk tgt tk-0 tgt-0 data) (k ak ak-0 skey) (n2 n1 n1-0 text)
    (c as t t-0 name))
  (defstrand client 2 (tc tc) (tk tk) (tgt tgt) (k k) (ak ak) (n2 n2)
    (n1 n1) (c c) (t t) (as as))
  (defstrand auth 2 (tc tc) (tk tk-0) (tgt tgt-0) (k k) (ak ak-0)
    (n2 n2) (n1 n1-0) (c c) (t t-0) (as as))
  (deflistener k)
  (precedes ((0 0) (1 0)) ((1 1) (2 0)) ((2 1) (0 1)))
  (non-orig (privk c) (privk as))
  (uniq-orig k ak-0 n2 n1)
  (operation encryption-test (added-listener k) (enc ak n1 tk t k)
    (0 1))
  (traces
    ((send (cat (enc tc n2 (privk c)) c t n1))
      (recv
        (cat (enc (enc k n2 c (privk as)) (pubk c)) c tgt
          (enc ak n1 tk t k))))
    ((recv (cat (enc tc n2 (privk c)) c t-0 n1-0))
      (send
        (cat (enc (enc k n2 c (privk as)) (pubk c)) c tgt-0
          (enc ak-0 n1-0 tk-0 t-0 k)))) ((recv k) (send k)))
  (label 6)
  (parent 4)
  (unrealized (2 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton pkinit-fix1
  (vars (tc tk tgt tk-0 tgt-0 data) (ak ak-0 skey) (n2 n1 n1-0 text)
    (c as t t-0 name))
  (defstrand client 2 (tc tc) (tk tk) (tgt tgt) (k ak-0) (ak ak) (n2 n2)
    (n1 n1) (c c) (t t) (as as))
  (defstrand auth 2 (tc tc) (tk tk-0) (tgt tgt-0) (k ak-0) (ak ak-0)
    (n2 n2) (n1 n1-0) (c c) (t t-0) (as as))
  (deflistener ak-0)
  (precedes ((0 0) (1 0)) ((1 1) (2 0)) ((2 1) (0 1)))
  (non-orig (privk c) (privk as))
  (uniq-orig ak-0 n2 n1)
  (operation nonce-test (displaced 3 1 auth 2) k (2 0)
    (enc (enc k n2 c (privk as)) (pubk c)))
  (traces
    ((send (cat (enc tc n2 (privk c)) c t n1))
      (recv
        (cat (enc (enc ak-0 n2 c (privk as)) (pubk c)) c tgt
          (enc ak n1 tk t ak-0))))
    ((recv (cat (enc tc n2 (privk c)) c t-0 n1-0))
      (send
        (cat (enc (enc ak-0 n2 c (privk as)) (pubk c)) c tgt-0
          (enc ak-0 n1-0 tk-0 t-0 ak-0)))) ((recv ak-0) (send ak-0)))
  (label 7)
  (parent 6)
  (unrealized (2 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol pkinit-fix2 basic
  (defrole client
    (vars (c t as name) (n2 n1 text) (tc tk tgt data) (k ak skey))
    (trace (send (cat (enc tc n2 (privk c)) c t n1))
      (recv
        (cat
          (enc (enc k (hash (enc tc n2 (privk c)) c t n1) (privk as))
            (pubk c)) c tgt (enc ak n1 tk t k))))
    (uniq-orig n2 n1))
  (defrole auth
    (vars (c t as name) (n2 n1 text) (tc tk tgt data) (k ak skey))
    (trace (recv (cat (enc tc n2 (privk c)) c t n1))
      (send
        (cat
          (enc (enc k (hash (enc tc n2 (privk c)) c t n1) (privk as))
            (pubk c)) c tgt (enc ak n1 tk t k))))
    (uniq-orig k ak))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton pkinit-fix2
  (vars (tc tk tgt data) (k ak skey) (n2 n1 text) (c as t name))
  (defstrand client 2 (tc tc) (tk tk) (tgt tgt) (k k) (ak ak) (n2 n2)
    (n1 n1) (c c) (t t) (as as))
  (non-orig (privk c) (privk as))
  (uniq-orig n2 n1)
  (goals
    (forall
      ((tc tk tgt data) (k ak skey) (n2 n1 text) (c as t name) (z strd))
      (implies
        (and (p "client" z 2) (p "client" "tc" z tc)
          (p "client" "tk" z tk) (p "client" "tgt" z tgt)
          (p "client" "k" z k) (p "client" "ak" z ak)
          (p "client" "n2" z n2) (p "client" "n1" z n1)
          (p "client" "c" z c) (p "client" "t" z t)
          (p "client" "as" z as) (non (privk c)) (non (privk as))
          (uniq-at n2 z 0) (uniq-at n1 z 0))
        (exists ((tgt-0 data) (z-0 strd))
          (and (p "auth" z-0 2) (p "auth" "tc" z-0 tc)
            (p "auth" "tk" z-0 tk) (p "auth" "tgt" z-0 tgt-0)
            (p "auth" "k" z-0 k) (p "auth" "ak" z-0 ak)
            (p "auth" "n2" z-0 n2) (p "auth" "n1" z-0 n1)
            (p "auth" "c" z-0 c) (p "auth" "t" z-0 t)
            (p "auth" "as" z-0 as) (prec z 0 z-0 0) (prec z-0 1 z 1)
            (uniq-at k z-0 1) (uniq-at ak z-0 1))))))
  (traces
    ((send (cat (enc tc n2 (privk c)) c t n1))
      (recv
        (cat
          (enc (enc k (hash (enc tc n2 (privk c)) c t n1) (privk as))
            (pubk c)) c tgt (enc ak n1 tk t k)))))
  (label 8)
  (unrealized (0 1))
  (origs (n2 (0 0)) (n1 (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton pkinit-fix2
  (vars (tc tk tgt tk-0 tgt-0 data) (k ak ak-0 skey) (n2 n1 text)
    (c as t name))
  (defstrand client 2 (tc tc) (tk tk) (tgt tgt) (k k) (ak ak) (n2 n2)
    (n1 n1) (c c) (t t) (as as))
  (defstrand auth 2 (tc tc) (tk tk-0) (tgt tgt-0) (k k) (ak ak-0)
    (n2 n2) (n1 n1) (c c) (t t) (as as))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk c) (privk as))
  (uniq-orig k ak-0 n2 n1)
  (operation encryption-test (added-strand auth 2)
    (enc k (hash (enc tc n2 (privk c)) c t n1) (privk as)) (0 1))
  (traces
    ((send (cat (enc tc n2 (privk c)) c t n1))
      (recv
        (cat
          (enc (enc k (hash (enc tc n2 (privk c)) c t n1) (privk as))
            (pubk c)) c tgt (enc ak n1 tk t k))))
    ((recv (cat (enc tc n2 (privk c)) c t n1))
      (send
        (cat
          (enc (enc k (hash (enc tc n2 (privk c)) c t n1) (privk as))
            (pubk c)) c tgt-0 (enc ak-0 n1 tk-0 t k)))))
  (label 9)
  (parent 8)
  (unrealized (0 1))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton pkinit-fix2
  (vars (tc tgt tk tgt-0 data) (k ak skey) (n2 n1 text) (c as t name))
  (defstrand client 2 (tc tc) (tk tk) (tgt tgt) (k k) (ak ak) (n2 n2)
    (n1 n1) (c c) (t t) (as as))
  (defstrand auth 2 (tc tc) (tk tk) (tgt tgt-0) (k k) (ak ak) (n2 n2)
    (n1 n1) (c c) (t t) (as as))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk c) (privk as))
  (uniq-orig k ak n2 n1)
  (operation encryption-test (displaced 2 1 auth 2)
    (enc ak-0 n1 tk-0 t k) (0 1))
  (traces
    ((send (cat (enc tc n2 (privk c)) c t n1))
      (recv
        (cat
          (enc (enc k (hash (enc tc n2 (privk c)) c t n1) (privk as))
            (pubk c)) c tgt (enc ak n1 tk t k))))
    ((recv (cat (enc tc n2 (privk c)) c t n1))
      (send
        (cat
          (enc (enc k (hash (enc tc n2 (privk c)) c t n1) (privk as))
            (pubk c)) c tgt-0 (enc ak n1 tk t k)))))
  (label 10)
  (parent 9)
  (realized)
  (shape)
  (satisfies yes)
  (maps
    ((0)
      ((tc tc) (tk tk) (tgt tgt) (k k) (ak ak) (n2 n2) (n1 n1) (c c)
        (as as) (t t))))
  (origs (k (1 1)) (ak (1 1)) (n2 (0 0)) (n1 (0 0))))

(defskeleton pkinit-fix2
  (vars (tc tk tgt tk-0 tgt-0 data) (k ak ak-0 skey) (n2 n1 text)
    (c as t name))
  (defstrand client 2 (tc tc) (tk tk) (tgt tgt) (k k) (ak ak) (n2 n2)
    (n1 n1) (c c) (t t) (as as))
  (defstrand auth 2 (tc tc) (tk tk-0) (tgt tgt-0) (k k) (ak ak-0)
    (n2 n2) (n1 n1) (c c) (t t) (as as))
  (deflistener k)
  (precedes ((0 0) (1 0)) ((1 1) (2 0)) ((2 1) (0 1)))
  (non-orig (privk c) (privk as))
  (uniq-orig k ak-0 n2 n1)
  (operation encryption-test (added-listener k) (enc ak n1 tk t k)
    (0 1))
  (traces
    ((send (cat (enc tc n2 (privk c)) c t n1))
      (recv
        (cat
          (enc (enc k (hash (enc tc n2 (privk c)) c t n1) (privk as))
            (pubk c)) c tgt (enc ak n1 tk t k))))
    ((recv (cat (enc tc n2 (privk c)) c t n1))
      (send
        (cat
          (enc (enc k (hash (enc tc n2 (privk c)) c t n1) (privk as))
            (pubk c)) c tgt-0 (enc ak-0 n1 tk-0 t k))))
    ((recv k) (send k)))
  (label 11)
  (parent 9)
  (unrealized (2 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton pkinit-fix2
  (vars (tc tk tgt tk-0 tgt-0 data) (ak ak-0 skey) (n2 n1 text)
    (c as t name))
  (defstrand client 2 (tc tc) (tk tk) (tgt tgt) (k ak-0) (ak ak) (n2 n2)
    (n1 n1) (c c) (t t) (as as))
  (defstrand auth 2 (tc tc) (tk tk-0) (tgt tgt-0) (k ak-0) (ak ak-0)
    (n2 n2) (n1 n1) (c c) (t t) (as as))
  (deflistener ak-0)
  (precedes ((0 0) (1 0)) ((1 1) (2 0)) ((2 1) (0 1)))
  (non-orig (privk c) (privk as))
  (uniq-orig ak-0 n2 n1)
  (operation nonce-test (displaced 3 1 auth 2) k (2 0)
    (enc (enc k (hash (enc tc n2 (privk c)) c t n1) (privk as))
      (pubk c)))
  (traces
    ((send (cat (enc tc n2 (privk c)) c t n1))
      (recv
        (cat
          (enc (enc ak-0 (hash (enc tc n2 (privk c)) c t n1) (privk as))
            (pubk c)) c tgt (enc ak n1 tk t ak-0))))
    ((recv (cat (enc tc n2 (privk c)) c t n1))
      (send
        (cat
          (enc (enc ak-0 (hash (enc tc n2 (privk c)) c t n1) (privk as))
            (pubk c)) c tgt-0 (enc ak-0 n1 tk-0 t ak-0))))
    ((recv ak-0) (send ak-0)))
  (label 12)
  (parent 11)
  (unrealized (2 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol pkinit-flawed basic
  (defrole client
    (vars (c t as name) (n2 n1 text) (tc tk tgt data) (k ak skey))
    (trace (send (cat (enc tc n2 (privk c)) c t n1))
      (recv
        (cat (enc (enc k n2 (privk as)) (pubk c)) c tgt
          (enc ak n1 tk t k))))
    (uniq-orig n2 n1))
  (defrole auth
    (vars (c t as name) (n2 n1 text) (tc tk tgt data) (k ak skey))
    (trace (recv (cat (enc tc n2 (privk c)) c t n1))
      (send
        (cat (enc (enc k n2 (privk as)) (pubk c)) c tgt
          (enc ak n1 tk t k))))
    (uniq-orig k ak))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton pkinit-flawed
  (vars (tc tc-0 tk tgt data) (k ak skey) (n2 n1 n2-0 n1-0 text)
    (c c-0 as t t-0 name))
  (defstrand client 2 (tc tc-0) (tk tk) (tgt tgt) (k k) (ak ak)
    (n2 n2-0) (n1 n1-0) (c c) (t t-0) (as as))
  (defstrand auth 1 (tc tc) (n2 n2) (n1 n1) (c c-0) (t t))
  (non-orig (privk c) (privk as))
  (uniq-orig n2-0 n1-0)
  (goals
    (forall
      ((tc tc-0 tk tgt data) (k ak skey) (n2 n1 n2-0 n1-0 text)
        (c c-0 as t t-0 name) (z z-0 strd))
      (implies
        (and (p "auth" z 1) (p "client" z-0 2) (p "auth" "tc" z tc)
          (p "auth" "n2" z n2) (p "auth" "n1" z n1) (p "auth" "c" z c-0)
          (p "auth" "t" z t) (p "client" "tc" z-0 tc-0)
          (p "client" "tk" z-0 tk) (p "client" "tgt" z-0 tgt)
          (p "client" "k" z-0 k) (p "client" "ak" z-0 ak)
          (p "client" "n2" z-0 n2-0) (p "client" "n1" z-0 n1-0)
          (p "client" "c" z-0 c) (p "client" "t" z-0 t-0)
          (p "client" "as" z-0 as) (non (privk c)) (non (privk as))
          (uniq-at n2-0 z-0 0) (uniq-at n1-0 z-0 0))
        (or
          (exists ((tk-0 tgt-0 data) (ak-0 skey))
            (and (= n2-0 n2) (p "auth" z 2) (p "client" "n2" z-0 n2)
              (p "auth" "tk" z tk-0) (p "auth" "tgt" z tgt-0)
              (p "auth" "k" z k) (p "auth" "ak" z ak-0)
              (p "auth" "as" z as) (prec z-0 0 z 0) (prec z 1 z-0 1)
              (uniq-at k z 1) (uniq-at ak-0 z 1) (uniq-at n2 z-0 0)))
          (exists
            ((tc-1 tk-0 tgt-0 data) (ak-0 skey) (n1-1 text)
              (c-1 t-1 name) (z-1 strd))
            (and (p "auth" z-1 2) (p "auth" "tc" z-1 tc-1)
              (p "auth" "tk" z-1 tk-0) (p "auth" "tgt" z-1 tgt-0)
              (p "auth" "k" z-1 k) (p "auth" "ak" z-1 ak-0)
              (p "auth" "n2" z-1 n2-0) (p "auth" "n1" z-1 n1-1)
              (p "auth" "c" z-1 c-1) (p "auth" "t" z-1 t-1)
              (p "auth" "as" z-1 as) (prec z-0 0 z-1 0)
              (prec z-1 1 z-0 1) (uniq-at k z-1 1)
              (uniq-at ak-0 z-1 1)))))))
  (traces
    ((send (cat (enc tc-0 n2-0 (privk c)) c t-0 n1-0))
      (recv
        (cat (enc (enc k n2-0 (privk as)) (pubk c)) c tgt
          (enc ak n1-0 tk t-0 k))))
    ((recv (cat (enc tc n2 (privk c-0)) c-0 t n1))))
  (label 13)
  (unrealized (0 1))
  (origs (n2-0 (0 0)) (n1-0 (0 0)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton pkinit-flawed
  (vars (tc tk tgt tc-0 tk-0 tgt-0 data) (k ak ak-0 skey)
    (n2 n1 n1-0 text) (c as t c-0 t-0 name))
  (defstrand client 2 (tc tc) (tk tk) (tgt tgt) (k k) (ak ak) (n2 n2)
    (n1 n1) (c c) (t t) (as as))
  (defstrand auth 2 (tc tc-0) (tk tk-0) (tgt tgt-0) (k k) (ak ak-0)
    (n2 n2) (n1 n1-0) (c c-0) (t t-0) (as as))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk c) (privk as))
  (uniq-orig k ak-0 n2 n1)
  (operation encryption-test (displaced 1 2 auth 2)
    (enc k n2 (privk as)) (0 1))
  (traces
    ((send (cat (enc tc n2 (privk c)) c t n1))
      (recv
        (cat (enc (enc k n2 (privk as)) (pubk c)) c tgt
          (enc ak n1 tk t k))))
    ((recv (cat (enc tc-0 n2 (privk c-0)) c-0 t-0 n1-0))
      (send
        (cat (enc (enc k n2 (privk as)) (pubk c-0)) c-0 tgt-0
          (enc ak-0 n1-0 tk-0 t-0 k)))))
  (label 14)
  (parent 13)
  (realized)
  (shape)
  (satisfies yes)
  (maps
    ((0 1)
      ((tc tc-0) (tc-0 tc) (tk tk) (tgt tgt) (k k) (ak ak) (n2 n2)
        (n1 n1-0) (n2-0 n2) (n1-0 n1) (c c) (c-0 c-0) (as as) (t t-0)
        (t-0 t))))
  (origs (k (1 1)) (ak-0 (1 1)) (n2 (0 0)) (n1 (0 0))))

(defskeleton pkinit-flawed
  (vars (tc tc-0 tk tgt tc-1 tk-0 tgt-0 data) (k ak ak-0 skey)
    (n2 n1 n2-0 n1-0 n1-1 text) (c c-0 as t t-0 c-1 t-1 name))
  (defstrand client 2 (tc tc-0) (tk tk) (tgt tgt) (k k) (ak ak)
    (n2 n2-0) (n1 n1-0) (c c) (t t-0) (as as))
  (defstrand auth 1 (tc tc) (n2 n2) (n1 n1) (c c-0) (t t))
  (defstrand auth 2 (tc tc-1) (tk tk-0) (tgt tgt-0) (k k) (ak ak-0)
    (n2 n2-0) (n1 n1-1) (c c-1) (t t-1) (as as))
  (precedes ((0 0) (2 0)) ((2 1) (0 1)))
  (non-orig (privk c) (privk as))
  (uniq-orig k ak-0 n2-0 n1-0)
  (operation encryption-test (added-strand auth 2)
    (enc k n2-0 (privk as)) (0 1))
  (traces
    ((send (cat (enc tc-0 n2-0 (privk c)) c t-0 n1-0))
      (recv
        (cat (enc (enc k n2-0 (privk as)) (pubk c)) c tgt
          (enc ak n1-0 tk t-0 k))))
    ((recv (cat (enc tc n2 (privk c-0)) c-0 t n1)))
    ((recv (cat (enc tc-1 n2-0 (privk c-1)) c-1 t-1 n1-1))
      (send
        (cat (enc (enc k n2-0 (privk as)) (pubk c-1)) c-1 tgt-0
          (enc ak-0 n1-1 tk-0 t-1 k)))))
  (label 15)
  (parent 13)
  (realized)
  (shape)
  (satisfies yes)
  (maps
    ((0 1)
      ((tc tc) (tc-0 tc-0) (tk tk) (tgt tgt) (k k) (ak ak) (n2 n2)
        (n1 n1) (n2-0 n2-0) (n1-0 n1-0) (c c) (c-0 c-0) (as as) (t t)
        (t-0 t-0))))
  (origs (k (2 1)) (ak-0 (2 1)) (n2-0 (0 0)) (n1-0 (0 0))))

(comment "Nothing left to do")

(defprotocol pkinit-fix1 basic
  (defrole client
    (vars (c t as name) (n2 n1 text) (tc tk tgt data) (k ak skey))
    (trace (send (cat (enc tc n2 (privk c)) c t n1))
      (recv
        (cat (enc (enc k n2 c (privk as)) (pubk c)) c tgt
          (enc ak n1 tk t k))))
    (uniq-orig n2 n1))
  (defrole auth
    (vars (c t as name) (n2 n1 text) (tc tk tgt data) (k ak skey))
    (trace (recv (cat (enc tc n2 (privk c)) c t n1))
      (send
        (cat (enc (enc k n2 c (privk as)) (pubk c)) c tgt
          (enc ak n1 tk t k))))
    (uniq-orig k ak))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton pkinit-fix1
  (vars (tc tc-0 tk tgt data) (k ak skey) (n2 n1 n2-0 n1-0 text)
    (c c-0 as t t-0 name))
  (defstrand client 2 (tc tc-0) (tk tk) (tgt tgt) (k k) (ak ak)
    (n2 n2-0) (n1 n1-0) (c c) (t t-0) (as as))
  (defstrand auth 1 (tc tc) (n2 n2) (n1 n1) (c c-0) (t t))
  (non-orig (privk c) (privk as))
  (uniq-orig n2-0 n1-0)
  (goals
    (forall
      ((tc tc-0 tk tgt data) (k ak skey) (n2 n1 n2-0 n1-0 text)
        (c c-0 as t t-0 name) (z z-0 strd))
      (implies
        (and (p "auth" z 1) (p "client" z-0 2) (p "auth" "tc" z tc)
          (p "auth" "n2" z n2) (p "auth" "n1" z n1) (p "auth" "c" z c-0)
          (p "auth" "t" z t) (p "client" "tc" z-0 tc-0)
          (p "client" "tk" z-0 tk) (p "client" "tgt" z-0 tgt)
          (p "client" "k" z-0 k) (p "client" "ak" z-0 ak)
          (p "client" "n2" z-0 n2-0) (p "client" "n1" z-0 n1-0)
          (p "client" "c" z-0 c) (p "client" "t" z-0 t-0)
          (p "client" "as" z-0 as) (non (privk c)) (non (privk as))
          (uniq-at n2-0 z-0 0) (uniq-at n1-0 z-0 0))
        (or
          (exists ((tgt-0 data))
            (and (= c-0 c) (= t-0 t) (= n2-0 n2) (= n1-0 n1) (= tc-0 tc)
              (p "auth" z 2) (p "client" "tc" z-0 tc)
              (p "client" "n2" z-0 n2) (p "client" "n1" z-0 n1)
              (p "client" "t" z-0 t) (p "auth" "tk" z tk)
              (p "auth" "tgt" z tgt-0) (p "auth" "k" z k)
              (p "auth" "ak" z ak) (p "auth" "c" z c)
              (p "auth" "as" z as) (prec z-0 0 z 0) (prec z 1 z-0 1)
              (uniq-at k z 1) (uniq-at ak z 1) (uniq-at n1 z-0 0)
              (uniq-at n2 z-0 0)))
          (exists ((tgt-0 data) (z-1 strd))
            (and (p "auth" z-1 2) (p "auth" "tc" z-1 tc-0)
              (p "auth" "tk" z-1 tk) (p "auth" "tgt" z-1 tgt-0)
              (p "auth" "k" z-1 k) (p "auth" "ak" z-1 ak)
              (p "auth" "n2" z-1 n2-0) (p "auth" "n1" z-1 n1-0)
              (p "auth" "c" z-1 c) (p "auth" "t" z-1 t-0)
              (p "auth" "as" z-1 as) (prec z-0 0 z-1 0)
              (prec z-1 1 z-0 1) (uniq-at k z-1 1)
              (uniq-at ak z-1 1)))))))
  (traces
    ((send (cat (enc tc-0 n2-0 (privk c)) c t-0 n1-0))
      (recv
        (cat (enc (enc k n2-0 c (privk as)) (pubk c)) c tgt
          (enc ak n1-0 tk t-0 k))))
    ((recv (cat (enc tc n2 (privk c-0)) c-0 t n1))))
  (label 16)
  (unrealized (0 1))
  (origs (n2-0 (0 0)) (n1-0 (0 0)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton pkinit-fix1
  (vars (tc tk tgt tc-0 tk-0 tgt-0 data) (k ak ak-0 skey)
    (n2 n1 n1-0 text) (c as t t-0 name))
  (defstrand client 2 (tc tc) (tk tk) (tgt tgt) (k k) (ak ak) (n2 n2)
    (n1 n1) (c c) (t t) (as as))
  (defstrand auth 2 (tc tc-0) (tk tk-0) (tgt tgt-0) (k k) (ak ak-0)
    (n2 n2) (n1 n1-0) (c c) (t t-0) (as as))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk c) (privk as))
  (uniq-orig k ak-0 n2 n1)
  (operation encryption-test (displaced 1 2 auth 2)
    (enc k n2 c (privk as)) (0 1))
  (traces
    ((send (cat (enc tc n2 (privk c)) c t n1))
      (recv
        (cat (enc (enc k n2 c (privk as)) (pubk c)) c tgt
          (enc ak n1 tk t k))))
    ((recv (cat (enc tc-0 n2 (privk c)) c t-0 n1-0))
      (send
        (cat (enc (enc k n2 c (privk as)) (pubk c)) c tgt-0
          (enc ak-0 n1-0 tk-0 t-0 k)))))
  (label 17)
  (parent 16)
  (unrealized (0 1) (1 0))
  (origs (k (1 1)) (ak-0 (1 1)) (n2 (0 0)) (n1 (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton pkinit-fix1
  (vars (tc tc-0 tk tgt tc-1 tk-0 tgt-0 data) (k ak ak-0 skey)
    (n2 n1 n2-0 n1-0 n1-1 text) (c c-0 as t t-0 t-1 name))
  (defstrand client 2 (tc tc-0) (tk tk) (tgt tgt) (k k) (ak ak)
    (n2 n2-0) (n1 n1-0) (c c) (t t-0) (as as))
  (defstrand auth 1 (tc tc) (n2 n2) (n1 n1) (c c-0) (t t))
  (defstrand auth 2 (tc tc-1) (tk tk-0) (tgt tgt-0) (k k) (ak ak-0)
    (n2 n2-0) (n1 n1-1) (c c) (t t-1) (as as))
  (precedes ((0 0) (2 0)) ((2 1) (0 1)))
  (non-orig (privk c) (privk as))
  (uniq-orig k ak-0 n2-0 n1-0)
  (operation encryption-test (added-strand auth 2)
    (enc k n2-0 c (privk as)) (0 1))
  (traces
    ((send (cat (enc tc-0 n2-0 (privk c)) c t-0 n1-0))
      (recv
        (cat (enc (enc k n2-0 c (privk as)) (pubk c)) c tgt
          (enc ak n1-0 tk t-0 k))))
    ((recv (cat (enc tc n2 (privk c-0)) c-0 t n1)))
    ((recv (cat (enc tc-1 n2-0 (privk c)) c t-1 n1-1))
      (send
        (cat (enc (enc k n2-0 c (privk as)) (pubk c)) c tgt-0
          (enc ak-0 n1-1 tk-0 t-1 k)))))
  (label 18)
  (parent 16)
  (unrealized (0 1) (2 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton pkinit-fix1
  (vars (tc tk tgt tk-0 tgt-0 data) (k ak ak-0 skey) (n2 n1 n1-0 text)
    (c as t t-0 name))
  (defstrand client 2 (tc tc) (tk tk) (tgt tgt) (k k) (ak ak) (n2 n2)
    (n1 n1) (c c) (t t) (as as))
  (defstrand auth 2 (tc tc) (tk tk-0) (tgt tgt-0) (k k) (ak ak-0)
    (n2 n2) (n1 n1-0) (c c) (t t-0) (as as))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk c) (privk as))
  (uniq-orig k ak-0 n2 n1)
  (operation encryption-test (displaced 2 0 client 1)
    (enc tc-0 n2 (privk c)) (1 0))
  (traces
    ((send (cat (enc tc n2 (privk c)) c t n1))
      (recv
        (cat (enc (enc k n2 c (privk as)) (pubk c)) c tgt
          (enc ak n1 tk t k))))
    ((recv (cat (enc tc n2 (privk c)) c t-0 n1-0))
      (send
        (cat (enc (enc k n2 c (privk as)) (pubk c)) c tgt-0
          (enc ak-0 n1-0 tk-0 t-0 k)))))
  (label 19)
  (parent 17)
  (unrealized (0 1))
  (origs (n2 (0 0)) (n1 (0 0)) (k (1 1)) (ak-0 (1 1)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton pkinit-fix1
  (vars (tc tc-0 tk tgt tk-0 tgt-0 data) (k ak ak-0 skey)
    (n2 n1 n2-0 n1-0 n1-1 text) (c c-0 as t t-0 t-1 name))
  (defstrand client 2 (tc tc-0) (tk tk) (tgt tgt) (k k) (ak ak)
    (n2 n2-0) (n1 n1-0) (c c) (t t-0) (as as))
  (defstrand auth 1 (tc tc) (n2 n2) (n1 n1) (c c-0) (t t))
  (defstrand auth 2 (tc tc-0) (tk tk-0) (tgt tgt-0) (k k) (ak ak-0)
    (n2 n2-0) (n1 n1-1) (c c) (t t-1) (as as))
  (precedes ((0 0) (2 0)) ((2 1) (0 1)))
  (non-orig (privk c) (privk as))
  (uniq-orig k ak-0 n2-0 n1-0)
  (operation encryption-test (displaced 3 0 client 1)
    (enc tc-1 n2-0 (privk c)) (2 0))
  (traces
    ((send (cat (enc tc-0 n2-0 (privk c)) c t-0 n1-0))
      (recv
        (cat (enc (enc k n2-0 c (privk as)) (pubk c)) c tgt
          (enc ak n1-0 tk t-0 k))))
    ((recv (cat (enc tc n2 (privk c-0)) c-0 t n1)))
    ((recv (cat (enc tc-0 n2-0 (privk c)) c t-1 n1-1))
      (send
        (cat (enc (enc k n2-0 c (privk as)) (pubk c)) c tgt-0
          (enc ak-0 n1-1 tk-0 t-1 k)))))
  (label 20)
  (parent 18)
  (unrealized (0 1))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton pkinit-fix1
  (vars (tc tgt tk tgt-0 data) (k ak skey) (n2 n1 text) (c as t name))
  (defstrand client 2 (tc tc) (tk tk) (tgt tgt) (k k) (ak ak) (n2 n2)
    (n1 n1) (c c) (t t) (as as))
  (defstrand auth 2 (tc tc) (tk tk) (tgt tgt-0) (k k) (ak ak) (n2 n2)
    (n1 n1) (c c) (t t) (as as))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk c) (privk as))
  (uniq-orig k ak n2 n1)
  (operation encryption-test (displaced 2 1 auth 2)
    (enc ak-0 n1-0 tk-0 t-0 k) (0 1))
  (traces
    ((send (cat (enc tc n2 (privk c)) c t n1))
      (recv
        (cat (enc (enc k n2 c (privk as)) (pubk c)) c tgt
          (enc ak n1 tk t k))))
    ((recv (cat (enc tc n2 (privk c)) c t n1))
      (send
        (cat (enc (enc k n2 c (privk as)) (pubk c)) c tgt-0
          (enc ak n1 tk t k)))))
  (label 21)
  (parent 19)
  (realized)
  (shape)
  (satisfies yes)
  (maps
    ((0 1)
      ((tc tc) (tc-0 tc) (tk tk) (tgt tgt) (k k) (ak ak) (n2 n2) (n1 n1)
        (n2-0 n2) (n1-0 n1) (c c) (c-0 c) (as as) (t t) (t-0 t))))
  (origs (k (1 1)) (ak (1 1)) (n2 (0 0)) (n1 (0 0))))

(defskeleton pkinit-fix1
  (vars (tc tk tgt tk-0 tgt-0 data) (k ak ak-0 skey) (n2 n1 n1-0 text)
    (c as t t-0 name))
  (defstrand client 2 (tc tc) (tk tk) (tgt tgt) (k k) (ak ak) (n2 n2)
    (n1 n1) (c c) (t t) (as as))
  (defstrand auth 2 (tc tc) (tk tk-0) (tgt tgt-0) (k k) (ak ak-0)
    (n2 n2) (n1 n1-0) (c c) (t t-0) (as as))
  (deflistener k)
  (precedes ((0 0) (1 0)) ((1 1) (2 0)) ((2 1) (0 1)))
  (non-orig (privk c) (privk as))
  (uniq-orig k ak-0 n2 n1)
  (operation encryption-test (added-listener k) (enc ak n1 tk t k)
    (0 1))
  (traces
    ((send (cat (enc tc n2 (privk c)) c t n1))
      (recv
        (cat (enc (enc k n2 c (privk as)) (pubk c)) c tgt
          (enc ak n1 tk t k))))
    ((recv (cat (enc tc n2 (privk c)) c t-0 n1-0))
      (send
        (cat (enc (enc k n2 c (privk as)) (pubk c)) c tgt-0
          (enc ak-0 n1-0 tk-0 t-0 k)))) ((recv k) (send k)))
  (label 22)
  (parent 19)
  (unrealized (2 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton pkinit-fix1
  (vars (tc tc-0 tgt tk tgt-0 data) (k ak skey) (n2 n1 n2-0 n1-0 text)
    (c c-0 as t t-0 name))
  (defstrand client 2 (tc tc-0) (tk tk) (tgt tgt) (k k) (ak ak)
    (n2 n2-0) (n1 n1-0) (c c) (t t-0) (as as))
  (defstrand auth 1 (tc tc) (n2 n2) (n1 n1) (c c-0) (t t))
  (defstrand auth 2 (tc tc-0) (tk tk) (tgt tgt-0) (k k) (ak ak)
    (n2 n2-0) (n1 n1-0) (c c) (t t-0) (as as))
  (precedes ((0 0) (2 0)) ((2 1) (0 1)))
  (non-orig (privk c) (privk as))
  (uniq-orig k ak n2-0 n1-0)
  (operation encryption-test (displaced 3 2 auth 2)
    (enc ak-0 n1-1 tk-0 t-1 k) (0 1))
  (traces
    ((send (cat (enc tc-0 n2-0 (privk c)) c t-0 n1-0))
      (recv
        (cat (enc (enc k n2-0 c (privk as)) (pubk c)) c tgt
          (enc ak n1-0 tk t-0 k))))
    ((recv (cat (enc tc n2 (privk c-0)) c-0 t n1)))
    ((recv (cat (enc tc-0 n2-0 (privk c)) c t-0 n1-0))
      (send
        (cat (enc (enc k n2-0 c (privk as)) (pubk c)) c tgt-0
          (enc ak n1-0 tk t-0 k)))))
  (label 23)
  (parent 20)
  (realized)
  (shape)
  (satisfies yes)
  (maps
    ((0 1)
      ((tc tc) (tc-0 tc-0) (tk tk) (tgt tgt) (k k) (ak ak) (n2 n2)
        (n1 n1) (n2-0 n2-0) (n1-0 n1-0) (c c) (c-0 c-0) (as as) (t t)
        (t-0 t-0))))
  (origs (k (2 1)) (ak (2 1)) (n2-0 (0 0)) (n1-0 (0 0))))

(defskeleton pkinit-fix1
  (vars (tc tc-0 tk tgt tk-0 tgt-0 data) (k ak ak-0 skey)
    (n2 n1 n2-0 n1-0 n1-1 text) (c c-0 as t t-0 t-1 name))
  (defstrand client 2 (tc tc-0) (tk tk) (tgt tgt) (k k) (ak ak)
    (n2 n2-0) (n1 n1-0) (c c) (t t-0) (as as))
  (defstrand auth 1 (tc tc) (n2 n2) (n1 n1) (c c-0) (t t))
  (defstrand auth 2 (tc tc-0) (tk tk-0) (tgt tgt-0) (k k) (ak ak-0)
    (n2 n2-0) (n1 n1-1) (c c) (t t-1) (as as))
  (deflistener k)
  (precedes ((0 0) (2 0)) ((2 1) (3 0)) ((3 1) (0 1)))
  (non-orig (privk c) (privk as))
  (uniq-orig k ak-0 n2-0 n1-0)
  (operation encryption-test (added-listener k) (enc ak n1-0 tk t-0 k)
    (0 1))
  (traces
    ((send (cat (enc tc-0 n2-0 (privk c)) c t-0 n1-0))
      (recv
        (cat (enc (enc k n2-0 c (privk as)) (pubk c)) c tgt
          (enc ak n1-0 tk t-0 k))))
    ((recv (cat (enc tc n2 (privk c-0)) c-0 t n1)))
    ((recv (cat (enc tc-0 n2-0 (privk c)) c t-1 n1-1))
      (send
        (cat (enc (enc k n2-0 c (privk as)) (pubk c)) c tgt-0
          (enc ak-0 n1-1 tk-0 t-1 k)))) ((recv k) (send k)))
  (label 24)
  (parent 20)
  (unrealized (3 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton pkinit-fix1
  (vars (tc tk tgt tk-0 tgt-0 data) (ak ak-0 skey) (n2 n1 n1-0 text)
    (c as t t-0 name))
  (defstrand client 2 (tc tc) (tk tk) (tgt tgt) (k ak-0) (ak ak) (n2 n2)
    (n1 n1) (c c) (t t) (as as))
  (defstrand auth 2 (tc tc) (tk tk-0) (tgt tgt-0) (k ak-0) (ak ak-0)
    (n2 n2) (n1 n1-0) (c c) (t t-0) (as as))
  (deflistener ak-0)
  (precedes ((0 0) (1 0)) ((1 1) (2 0)) ((2 1) (0 1)))
  (non-orig (privk c) (privk as))
  (uniq-orig ak-0 n2 n1)
  (operation nonce-test (displaced 3 1 auth 2) k (2 0)
    (enc (enc k n2 c (privk as)) (pubk c)))
  (traces
    ((send (cat (enc tc n2 (privk c)) c t n1))
      (recv
        (cat (enc (enc ak-0 n2 c (privk as)) (pubk c)) c tgt
          (enc ak n1 tk t ak-0))))
    ((recv (cat (enc tc n2 (privk c)) c t-0 n1-0))
      (send
        (cat (enc (enc ak-0 n2 c (privk as)) (pubk c)) c tgt-0
          (enc ak-0 n1-0 tk-0 t-0 ak-0)))) ((recv ak-0) (send ak-0)))
  (label 25)
  (parent 22)
  (unrealized (2 0))
  (dead)
  (comment "empty cohort"))

(defskeleton pkinit-fix1
  (vars (tc tc-0 tk tgt tk-0 tgt-0 data) (ak ak-0 skey)
    (n2 n1 n2-0 n1-0 n1-1 text) (c c-0 as t t-0 t-1 name))
  (defstrand client 2 (tc tc-0) (tk tk) (tgt tgt) (k ak-0) (ak ak)
    (n2 n2-0) (n1 n1-0) (c c) (t t-0) (as as))
  (defstrand auth 1 (tc tc) (n2 n2) (n1 n1) (c c-0) (t t))
  (defstrand auth 2 (tc tc-0) (tk tk-0) (tgt tgt-0) (k ak-0) (ak ak-0)
    (n2 n2-0) (n1 n1-1) (c c) (t t-1) (as as))
  (deflistener ak-0)
  (precedes ((0 0) (2 0)) ((2 1) (3 0)) ((3 1) (0 1)))
  (non-orig (privk c) (privk as))
  (uniq-orig ak-0 n2-0 n1-0)
  (operation nonce-test (displaced 4 2 auth 2) k (3 0)
    (enc (enc k n2-0 c (privk as)) (pubk c)))
  (traces
    ((send (cat (enc tc-0 n2-0 (privk c)) c t-0 n1-0))
      (recv
        (cat (enc (enc ak-0 n2-0 c (privk as)) (pubk c)) c tgt
          (enc ak n1-0 tk t-0 ak-0))))
    ((recv (cat (enc tc n2 (privk c-0)) c-0 t n1)))
    ((recv (cat (enc tc-0 n2-0 (privk c)) c t-1 n1-1))
      (send
        (cat (enc (enc ak-0 n2-0 c (privk as)) (pubk c)) c tgt-0
          (enc ak-0 n1-1 tk-0 t-1 ak-0)))) ((recv ak-0) (send ak-0)))
  (label 26)
  (parent 24)
  (unrealized (3 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")

(defprotocol pkinit-fix2 basic
  (defrole client
    (vars (c t as name) (n2 n1 text) (tc tk tgt data) (k ak skey))
    (trace (send (cat (enc tc n2 (privk c)) c t n1))
      (recv
        (cat
          (enc (enc k (hash (enc tc n2 (privk c)) c t n1) (privk as))
            (pubk c)) c tgt (enc ak n1 tk t k))))
    (uniq-orig n2 n1))
  (defrole auth
    (vars (c t as name) (n2 n1 text) (tc tk tgt data) (k ak skey))
    (trace (recv (cat (enc tc n2 (privk c)) c t n1))
      (send
        (cat
          (enc (enc k (hash (enc tc n2 (privk c)) c t n1) (privk as))
            (pubk c)) c tgt (enc ak n1 tk t k))))
    (uniq-orig k ak))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton pkinit-fix2
  (vars (tc tc-0 tk tgt data) (k ak skey) (n2 n1 n2-0 n1-0 text)
    (c c-0 as t t-0 name))
  (defstrand client 2 (tc tc-0) (tk tk) (tgt tgt) (k k) (ak ak)
    (n2 n2-0) (n1 n1-0) (c c) (t t-0) (as as))
  (defstrand auth 1 (tc tc) (n2 n2) (n1 n1) (c c-0) (t t))
  (non-orig (privk c) (privk as))
  (uniq-orig n2-0 n1-0)
  (goals
    (forall
      ((tc tc-0 tk tgt data) (k ak skey) (n2 n1 n2-0 n1-0 text)
        (c c-0 as t t-0 name) (z z-0 strd))
      (implies
        (and (p "auth" z 1) (p "client" z-0 2) (p "auth" "tc" z tc)
          (p "auth" "n2" z n2) (p "auth" "n1" z n1) (p "auth" "c" z c-0)
          (p "auth" "t" z t) (p "client" "tc" z-0 tc-0)
          (p "client" "tk" z-0 tk) (p "client" "tgt" z-0 tgt)
          (p "client" "k" z-0 k) (p "client" "ak" z-0 ak)
          (p "client" "n2" z-0 n2-0) (p "client" "n1" z-0 n1-0)
          (p "client" "c" z-0 c) (p "client" "t" z-0 t-0)
          (p "client" "as" z-0 as) (non (privk c)) (non (privk as))
          (uniq-at n2-0 z-0 0) (uniq-at n1-0 z-0 0))
        (or
          (exists ((tgt-0 data))
            (and (= c-0 c) (= t-0 t) (= n2-0 n2) (= n1-0 n1) (= tc-0 tc)
              (p "auth" z 2) (p "client" "tc" z-0 tc)
              (p "client" "n2" z-0 n2) (p "client" "n1" z-0 n1)
              (p "client" "t" z-0 t) (p "auth" "tk" z tk)
              (p "auth" "tgt" z tgt-0) (p "auth" "k" z k)
              (p "auth" "ak" z ak) (p "auth" "c" z c)
              (p "auth" "as" z as) (prec z-0 0 z 0) (prec z 1 z-0 1)
              (uniq-at k z 1) (uniq-at ak z 1) (uniq-at n2 z-0 0)
              (uniq-at n1 z-0 0)))
          (exists ((tgt-0 data) (z-1 strd))
            (and (p "auth" z-1 2) (p "auth" "tc" z-1 tc-0)
              (p "auth" "tk" z-1 tk) (p "auth" "tgt" z-1 tgt-0)
              (p "auth" "k" z-1 k) (p "auth" "ak" z-1 ak)
              (p "auth" "n2" z-1 n2-0) (p "auth" "n1" z-1 n1-0)
              (p "auth" "c" z-1 c) (p "auth" "t" z-1 t-0)
              (p "auth" "as" z-1 as) (prec z-0 0 z-1 0)
              (prec z-1 1 z-0 1) (uniq-at k z-1 1)
              (uniq-at ak z-1 1)))))))
  (traces
    ((send (cat (enc tc-0 n2-0 (privk c)) c t-0 n1-0))
      (recv
        (cat
          (enc
            (enc k (hash (enc tc-0 n2-0 (privk c)) c t-0 n1-0)
              (privk as)) (pubk c)) c tgt (enc ak n1-0 tk t-0 k))))
    ((recv (cat (enc tc n2 (privk c-0)) c-0 t n1))))
  (label 27)
  (unrealized (0 1))
  (origs (n2-0 (0 0)) (n1-0 (0 0)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton pkinit-fix2
  (vars (tc tk tgt tk-0 tgt-0 data) (k ak ak-0 skey) (n2 n1 text)
    (c as t name))
  (defstrand client 2 (tc tc) (tk tk) (tgt tgt) (k k) (ak ak) (n2 n2)
    (n1 n1) (c c) (t t) (as as))
  (defstrand auth 2 (tc tc) (tk tk-0) (tgt tgt-0) (k k) (ak ak-0)
    (n2 n2) (n1 n1) (c c) (t t) (as as))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk c) (privk as))
  (uniq-orig k ak-0 n2 n1)
  (operation encryption-test (displaced 1 2 auth 2)
    (enc k (hash (enc tc n2 (privk c)) c t n1) (privk as)) (0 1))
  (traces
    ((send (cat (enc tc n2 (privk c)) c t n1))
      (recv
        (cat
          (enc (enc k (hash (enc tc n2 (privk c)) c t n1) (privk as))
            (pubk c)) c tgt (enc ak n1 tk t k))))
    ((recv (cat (enc tc n2 (privk c)) c t n1))
      (send
        (cat
          (enc (enc k (hash (enc tc n2 (privk c)) c t n1) (privk as))
            (pubk c)) c tgt-0 (enc ak-0 n1 tk-0 t k)))))
  (label 28)
  (parent 27)
  (unrealized (0 1))
  (origs (k (1 1)) (ak-0 (1 1)) (n2 (0 0)) (n1 (0 0)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton pkinit-fix2
  (vars (tc tc-0 tk tgt tk-0 tgt-0 data) (k ak ak-0 skey)
    (n2 n1 n2-0 n1-0 text) (c c-0 as t t-0 name))
  (defstrand client 2 (tc tc-0) (tk tk) (tgt tgt) (k k) (ak ak)
    (n2 n2-0) (n1 n1-0) (c c) (t t-0) (as as))
  (defstrand auth 1 (tc tc) (n2 n2) (n1 n1) (c c-0) (t t))
  (defstrand auth 2 (tc tc-0) (tk tk-0) (tgt tgt-0) (k k) (ak ak-0)
    (n2 n2-0) (n1 n1-0) (c c) (t t-0) (as as))
  (precedes ((0 0) (2 0)) ((2 1) (0 1)))
  (non-orig (privk c) (privk as))
  (uniq-orig k ak-0 n2-0 n1-0)
  (operation encryption-test (added-strand auth 2)
    (enc k (hash (enc tc-0 n2-0 (privk c)) c t-0 n1-0) (privk as))
    (0 1))
  (traces
    ((send (cat (enc tc-0 n2-0 (privk c)) c t-0 n1-0))
      (recv
        (cat
          (enc
            (enc k (hash (enc tc-0 n2-0 (privk c)) c t-0 n1-0)
              (privk as)) (pubk c)) c tgt (enc ak n1-0 tk t-0 k))))
    ((recv (cat (enc tc n2 (privk c-0)) c-0 t n1)))
    ((recv (cat (enc tc-0 n2-0 (privk c)) c t-0 n1-0))
      (send
        (cat
          (enc
            (enc k (hash (enc tc-0 n2-0 (privk c)) c t-0 n1-0)
              (privk as)) (pubk c)) c tgt-0
          (enc ak-0 n1-0 tk-0 t-0 k)))))
  (label 29)
  (parent 27)
  (unrealized (0 1))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton pkinit-fix2
  (vars (tc tgt tk tgt-0 data) (k ak skey) (n2 n1 text) (c as t name))
  (defstrand client 2 (tc tc) (tk tk) (tgt tgt) (k k) (ak ak) (n2 n2)
    (n1 n1) (c c) (t t) (as as))
  (defstrand auth 2 (tc tc) (tk tk) (tgt tgt-0) (k k) (ak ak) (n2 n2)
    (n1 n1) (c c) (t t) (as as))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk c) (privk as))
  (uniq-orig k ak n2 n1)
  (operation encryption-test (displaced 2 1 auth 2)
    (enc ak-0 n1 tk-0 t k) (0 1))
  (traces
    ((send (cat (enc tc n2 (privk c)) c t n1))
      (recv
        (cat
          (enc (enc k (hash (enc tc n2 (privk c)) c t n1) (privk as))
            (pubk c)) c tgt (enc ak n1 tk t k))))
    ((recv (cat (enc tc n2 (privk c)) c t n1))
      (send
        (cat
          (enc (enc k (hash (enc tc n2 (privk c)) c t n1) (privk as))
            (pubk c)) c tgt-0 (enc ak n1 tk t k)))))
  (label 30)
  (parent 28)
  (realized)
  (shape)
  (satisfies yes)
  (maps
    ((0 1)
      ((tc tc) (tc-0 tc) (tk tk) (tgt tgt) (k k) (ak ak) (n2 n2) (n1 n1)
        (n2-0 n2) (n1-0 n1) (c c) (c-0 c) (as as) (t t) (t-0 t))))
  (origs (k (1 1)) (ak (1 1)) (n2 (0 0)) (n1 (0 0))))

(defskeleton pkinit-fix2
  (vars (tc tk tgt tk-0 tgt-0 data) (k ak ak-0 skey) (n2 n1 text)
    (c as t name))
  (defstrand client 2 (tc tc) (tk tk) (tgt tgt) (k k) (ak ak) (n2 n2)
    (n1 n1) (c c) (t t) (as as))
  (defstrand auth 2 (tc tc) (tk tk-0) (tgt tgt-0) (k k) (ak ak-0)
    (n2 n2) (n1 n1) (c c) (t t) (as as))
  (deflistener k)
  (precedes ((0 0) (1 0)) ((1 1) (2 0)) ((2 1) (0 1)))
  (non-orig (privk c) (privk as))
  (uniq-orig k ak-0 n2 n1)
  (operation encryption-test (added-listener k) (enc ak n1 tk t k)
    (0 1))
  (traces
    ((send (cat (enc tc n2 (privk c)) c t n1))
      (recv
        (cat
          (enc (enc k (hash (enc tc n2 (privk c)) c t n1) (privk as))
            (pubk c)) c tgt (enc ak n1 tk t k))))
    ((recv (cat (enc tc n2 (privk c)) c t n1))
      (send
        (cat
          (enc (enc k (hash (enc tc n2 (privk c)) c t n1) (privk as))
            (pubk c)) c tgt-0 (enc ak-0 n1 tk-0 t k))))
    ((recv k) (send k)))
  (label 31)
  (parent 28)
  (unrealized (2 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton pkinit-fix2
  (vars (tc tc-0 tgt tk tgt-0 data) (k ak skey) (n2 n1 n2-0 n1-0 text)
    (c c-0 as t t-0 name))
  (defstrand client 2 (tc tc-0) (tk tk) (tgt tgt) (k k) (ak ak)
    (n2 n2-0) (n1 n1-0) (c c) (t t-0) (as as))
  (defstrand auth 1 (tc tc) (n2 n2) (n1 n1) (c c-0) (t t))
  (defstrand auth 2 (tc tc-0) (tk tk) (tgt tgt-0) (k k) (ak ak)
    (n2 n2-0) (n1 n1-0) (c c) (t t-0) (as as))
  (precedes ((0 0) (2 0)) ((2 1) (0 1)))
  (non-orig (privk c) (privk as))
  (uniq-orig k ak n2-0 n1-0)
  (operation encryption-test (displaced 3 2 auth 2)
    (enc ak-0 n1-0 tk-0 t-0 k) (0 1))
  (traces
    ((send (cat (enc tc-0 n2-0 (privk c)) c t-0 n1-0))
      (recv
        (cat
          (enc
            (enc k (hash (enc tc-0 n2-0 (privk c)) c t-0 n1-0)
              (privk as)) (pubk c)) c tgt (enc ak n1-0 tk t-0 k))))
    ((recv (cat (enc tc n2 (privk c-0)) c-0 t n1)))
    ((recv (cat (enc tc-0 n2-0 (privk c)) c t-0 n1-0))
      (send
        (cat
          (enc
            (enc k (hash (enc tc-0 n2-0 (privk c)) c t-0 n1-0)
              (privk as)) (pubk c)) c tgt-0 (enc ak n1-0 tk t-0 k)))))
  (label 32)
  (parent 29)
  (realized)
  (shape)
  (satisfies yes)
  (maps
    ((0 1)
      ((tc tc) (tc-0 tc-0) (tk tk) (tgt tgt) (k k) (ak ak) (n2 n2)
        (n1 n1) (n2-0 n2-0) (n1-0 n1-0) (c c) (c-0 c-0) (as as) (t t)
        (t-0 t-0))))
  (origs (k (2 1)) (ak (2 1)) (n2-0 (0 0)) (n1-0 (0 0))))

(defskeleton pkinit-fix2
  (vars (tc tc-0 tk tgt tk-0 tgt-0 data) (k ak ak-0 skey)
    (n2 n1 n2-0 n1-0 text) (c c-0 as t t-0 name))
  (defstrand client 2 (tc tc-0) (tk tk) (tgt tgt) (k k) (ak ak)
    (n2 n2-0) (n1 n1-0) (c c) (t t-0) (as as))
  (defstrand auth 1 (tc tc) (n2 n2) (n1 n1) (c c-0) (t t))
  (defstrand auth 2 (tc tc-0) (tk tk-0) (tgt tgt-0) (k k) (ak ak-0)
    (n2 n2-0) (n1 n1-0) (c c) (t t-0) (as as))
  (deflistener k)
  (precedes ((0 0) (2 0)) ((2 1) (3 0)) ((3 1) (0 1)))
  (non-orig (privk c) (privk as))
  (uniq-orig k ak-0 n2-0 n1-0)
  (operation encryption-test (added-listener k) (enc ak n1-0 tk t-0 k)
    (0 1))
  (traces
    ((send (cat (enc tc-0 n2-0 (privk c)) c t-0 n1-0))
      (recv
        (cat
          (enc
            (enc k (hash (enc tc-0 n2-0 (privk c)) c t-0 n1-0)
              (privk as)) (pubk c)) c tgt (enc ak n1-0 tk t-0 k))))
    ((recv (cat (enc tc n2 (privk c-0)) c-0 t n1)))
    ((recv (cat (enc tc-0 n2-0 (privk c)) c t-0 n1-0))
      (send
        (cat
          (enc
            (enc k (hash (enc tc-0 n2-0 (privk c)) c t-0 n1-0)
              (privk as)) (pubk c)) c tgt-0
          (enc ak-0 n1-0 tk-0 t-0 k)))) ((recv k) (send k)))
  (label 33)
  (parent 29)
  (unrealized (3 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton pkinit-fix2
  (vars (tc tk tgt tk-0 tgt-0 data) (ak ak-0 skey) (n2 n1 text)
    (c as t name))
  (defstrand client 2 (tc tc) (tk tk) (tgt tgt) (k ak-0) (ak ak) (n2 n2)
    (n1 n1) (c c) (t t) (as as))
  (defstrand auth 2 (tc tc) (tk tk-0) (tgt tgt-0) (k ak-0) (ak ak-0)
    (n2 n2) (n1 n1) (c c) (t t) (as as))
  (deflistener ak-0)
  (precedes ((0 0) (1 0)) ((1 1) (2 0)) ((2 1) (0 1)))
  (non-orig (privk c) (privk as))
  (uniq-orig ak-0 n2 n1)
  (operation nonce-test (displaced 3 1 auth 2) k (2 0)
    (enc (enc k (hash (enc tc n2 (privk c)) c t n1) (privk as))
      (pubk c)))
  (traces
    ((send (cat (enc tc n2 (privk c)) c t n1))
      (recv
        (cat
          (enc (enc ak-0 (hash (enc tc n2 (privk c)) c t n1) (privk as))
            (pubk c)) c tgt (enc ak n1 tk t ak-0))))
    ((recv (cat (enc tc n2 (privk c)) c t n1))
      (send
        (cat
          (enc (enc ak-0 (hash (enc tc n2 (privk c)) c t n1) (privk as))
            (pubk c)) c tgt-0 (enc ak-0 n1 tk-0 t ak-0))))
    ((recv ak-0) (send ak-0)))
  (label 34)
  (parent 31)
  (unrealized (2 0))
  (dead)
  (comment "empty cohort"))

(defskeleton pkinit-fix2
  (vars (tc tc-0 tk tgt tk-0 tgt-0 data) (ak ak-0 skey)
    (n2 n1 n2-0 n1-0 text) (c c-0 as t t-0 name))
  (defstrand client 2 (tc tc-0) (tk tk) (tgt tgt) (k ak-0) (ak ak)
    (n2 n2-0) (n1 n1-0) (c c) (t t-0) (as as))
  (defstrand auth 1 (tc tc) (n2 n2) (n1 n1) (c c-0) (t t))
  (defstrand auth 2 (tc tc-0) (tk tk-0) (tgt tgt-0) (k ak-0) (ak ak-0)
    (n2 n2-0) (n1 n1-0) (c c) (t t-0) (as as))
  (deflistener ak-0)
  (precedes ((0 0) (2 0)) ((2 1) (3 0)) ((3 1) (0 1)))
  (non-orig (privk c) (privk as))
  (uniq-orig ak-0 n2-0 n1-0)
  (operation nonce-test (displaced 4 2 auth 2) k (3 0)
    (enc (enc k (hash (enc tc-0 n2-0 (privk c)) c t-0 n1-0) (privk as))
      (pubk c)))
  (traces
    ((send (cat (enc tc-0 n2-0 (privk c)) c t-0 n1-0))
      (recv
        (cat
          (enc
            (enc ak-0 (hash (enc tc-0 n2-0 (privk c)) c t-0 n1-0)
              (privk as)) (pubk c)) c tgt (enc ak n1-0 tk t-0 ak-0))))
    ((recv (cat (enc tc n2 (privk c-0)) c-0 t n1)))
    ((recv (cat (enc tc-0 n2-0 (privk c)) c t-0 n1-0))
      (send
        (cat
          (enc
            (enc ak-0 (hash (enc tc-0 n2-0 (privk c)) c t-0 n1-0)
              (privk as)) (pubk c)) c tgt-0
          (enc ak-0 n1-0 tk-0 t-0 ak-0)))) ((recv ak-0) (send ak-0)))
  (label 35)
  (parent 33)
  (unrealized (3 0))
  (dead)
  (comment "empty cohort"))

(comment "Nothing left to do")
