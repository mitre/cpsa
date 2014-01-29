(herald "Kerberos PK init")

(comment "CPSA 2.3.1")
(comment "All input read from pkinit.scm")

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
    (uniq-orig k ak)))

(defskeleton pkinit
  (vars (n2 n1 text) (tc tk tgt data) (c as t name) (k ak skey))
  (defstrand client 2 (n2 n2) (n1 n1) (tc tc) (tk tk) (tgt tgt) (c c)
    (t t) (as as) (k k) (ak ak))
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
  (vars (n2 n1 n1-0 text) (tc tk tgt tc-0 tk-0 tgt-0 data)
    (c as t c-0 t-0 name) (k ak ak-0 skey))
  (defstrand client 2 (n2 n2) (n1 n1) (tc tc) (tk tk) (tgt tgt) (c c)
    (t t) (as as) (k k) (ak ak))
  (defstrand auth 2 (n2 n2) (n1 n1-0) (tc tc-0) (tk tk-0) (tgt tgt-0)
    (c c-0) (t t-0) (as as) (k k) (ak ak-0))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (privk c) (privk as))
  (uniq-orig n2 n1 k ak-0)
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
  (unrealized)
  (shape)
  (maps
    ((0)
      ((c c) (as as) (t t) (n2 n2) (n1 n1) (tc tc) (tk tk) (tgt tgt)
        (k k) (ak ak))))
  (origs (k (1 1)) (ak-0 (1 1)) (n2 (0 0)) (n1 (0 0))))

(comment "Nothing left to do")
