(herald "Kerberos PKINIT")

(comment "CPSA 4.4.0")
(comment "Coherent logic")

(comment "CPSA 4.4.0")

(comment "All input read from pkinit.scm")

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
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defgoal pkinit-flawed
  (forall
    ((tc tk tgt data) (k ak skey) (n2 n1 text) (c as t name) (z strd))
    (implies
      (and (p "client" z 2) (p "client" "tc" z tc)
        (p "client" "tk" z tk) (p "client" "tgt" z tgt)
        (p "client" "k" z k) (p "client" "ak" z ak)
        (p "client" "n2" z n2) (p "client" "n1" z n1)
        (p "client" "c" z c) (p "client" "t" z t) (p "client" "as" z as)
        (non (privk c)) (non (privk as)) (uniq-at n2 z 0)
        (uniq-at n1 z 0))
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
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defgoal pkinit-fix1
  (forall
    ((tc tk tgt data) (k ak skey) (n2 n1 text) (c as t name) (z strd))
    (implies
      (and (p "client" z 2) (p "client" "tc" z tc)
        (p "client" "tk" z tk) (p "client" "tgt" z tgt)
        (p "client" "k" z k) (p "client" "ak" z ak)
        (p "client" "n2" z n2) (p "client" "n1" z n1)
        (p "client" "c" z c) (p "client" "t" z t) (p "client" "as" z as)
        (non (privk c)) (non (privk as)) (uniq-at n2 z 0)
        (uniq-at n1 z 0))
      (exists ((tgt-0 data) (z-0 strd))
        (and (p "auth" z-0 2) (p "auth" "tc" z-0 tc)
          (p "auth" "tk" z-0 tk) (p "auth" "tgt" z-0 tgt-0)
          (p "auth" "k" z-0 k) (p "auth" "ak" z-0 ak)
          (p "auth" "n2" z-0 n2) (p "auth" "n1" z-0 n1)
          (p "auth" "c" z-0 c) (p "auth" "t" z-0 t)
          (p "auth" "as" z-0 as) (prec z 0 z-0 0) (prec z-0 1 z 1)
          (uniq-at k z-0 1) (uniq-at ak z-0 1))))))

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
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defgoal pkinit-fix2
  (forall
    ((tc tk tgt data) (k ak skey) (n2 n1 text) (c as t name) (z strd))
    (implies
      (and (p "client" z 2) (p "client" "tc" z tc)
        (p "client" "tk" z tk) (p "client" "tgt" z tgt)
        (p "client" "k" z k) (p "client" "ak" z ak)
        (p "client" "n2" z n2) (p "client" "n1" z n1)
        (p "client" "c" z c) (p "client" "t" z t) (p "client" "as" z as)
        (non (privk c)) (non (privk as)) (uniq-at n2 z 0)
        (uniq-at n1 z 0))
      (exists ((tgt-0 data) (z-0 strd))
        (and (p "auth" z-0 2) (p "auth" "tc" z-0 tc)
          (p "auth" "tk" z-0 tk) (p "auth" "tgt" z-0 tgt-0)
          (p "auth" "k" z-0 k) (p "auth" "ak" z-0 ak)
          (p "auth" "n2" z-0 n2) (p "auth" "n1" z-0 n1)
          (p "auth" "c" z-0 c) (p "auth" "t" z-0 t)
          (p "auth" "as" z-0 as) (prec z 0 z-0 0) (prec z-0 1 z 1)
          (uniq-at k z-0 1) (uniq-at ak z-0 1))))))

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
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defgoal pkinit-flawed
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
          ((tc-1 tk-0 tgt-0 data) (ak-0 skey) (n1-1 text) (c-1 t-1 name)
            (z-1 strd))
          (and (p "auth" z-1 2) (p "auth" "tc" z-1 tc-1)
            (p "auth" "tk" z-1 tk-0) (p "auth" "tgt" z-1 tgt-0)
            (p "auth" "k" z-1 k) (p "auth" "ak" z-1 ak-0)
            (p "auth" "n2" z-1 n2-0) (p "auth" "n1" z-1 n1-1)
            (p "auth" "c" z-1 c-1) (p "auth" "t" z-1 t-1)
            (p "auth" "as" z-1 as) (prec z-0 0 z-1 0) (prec z-1 1 z-0 1)
            (uniq-at k z-1 1) (uniq-at ak-0 z-1 1)))))))

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
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defgoal pkinit-fix1
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
            (p "auth" "ak" z ak) (p "auth" "c" z c) (p "auth" "as" z as)
            (prec z-0 0 z 0) (prec z 1 z-0 1) (uniq-at k z 1)
            (uniq-at ak z 1) (uniq-at n1 z-0 0) (uniq-at n2 z-0 0)))
        (exists ((tgt-0 data) (z-1 strd))
          (and (p "auth" z-1 2) (p "auth" "tc" z-1 tc-0)
            (p "auth" "tk" z-1 tk) (p "auth" "tgt" z-1 tgt-0)
            (p "auth" "k" z-1 k) (p "auth" "ak" z-1 ak)
            (p "auth" "n2" z-1 n2-0) (p "auth" "n1" z-1 n1-0)
            (p "auth" "c" z-1 c) (p "auth" "t" z-1 t-0)
            (p "auth" "as" z-1 as) (prec z-0 0 z-1 0) (prec z-1 1 z-0 1)
            (uniq-at k z-1 1) (uniq-at ak z-1 1)))))))

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
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defgoal pkinit-fix2
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
            (p "auth" "ak" z ak) (p "auth" "c" z c) (p "auth" "as" z as)
            (prec z-0 0 z 0) (prec z 1 z-0 1) (uniq-at k z 1)
            (uniq-at ak z 1) (uniq-at n2 z-0 0) (uniq-at n1 z-0 0)))
        (exists ((tgt-0 data) (z-1 strd))
          (and (p "auth" z-1 2) (p "auth" "tc" z-1 tc-0)
            (p "auth" "tk" z-1 tk) (p "auth" "tgt" z-1 tgt-0)
            (p "auth" "k" z-1 k) (p "auth" "ak" z-1 ak)
            (p "auth" "n2" z-1 n2-0) (p "auth" "n1" z-1 n1-0)
            (p "auth" "c" z-1 c) (p "auth" "t" z-1 t-0)
            (p "auth" "as" z-1 as) (prec z-0 0 z-1 0) (prec z-1 1 z-0 1)
            (uniq-at k z-1 1) (uniq-at ak z-1 1)))))))
