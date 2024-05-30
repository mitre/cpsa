(herald "Kerberos PK init")

(comment "CPSA 4.4.3")
(comment "All input read from tst/pkinit.scm")

(defprotocol pkinit basic
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

(defskeleton pkinit
  (vars (tc tk tgt data) (k ak skey) (n2 n1 text) (c as t name))
  (defstrand client 2 (tc tc) (tk tk) (tgt tgt) (k k) (ak ak) (n2 n2)
    (n1 n1) (c c) (t t) (as as))
  (non-orig (privk c) (privk as))
  (uniq-orig n2 n1)
  (traces
    ((send (cat (enc tc n2 (privk c)) c t n1))
      (recv
        (cat (enc (enc k n2 (privk as)) (pubk c)) c tgt
          (enc ak n1 tk t k)))))
  (label 0)
  (unrealized (0 1))
  (origs (n2 (0 0)) (n1 (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton pkinit
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
  (strand-map 0)
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
  (maps
    ((0)
      ((c c) (as as) (t t) (n2 n2) (n1 n1) (tc tc) (tk tk) (tgt tgt)
        (k k) (ak ak))))
  (origs (k (1 1)) (ak-0 (1 1)) (n2 (0 0)) (n1 (0 0))))

(comment "Nothing left to do")
