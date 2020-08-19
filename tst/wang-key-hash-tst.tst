(herald "Wang's Fair Exchange Protocol" (bound 10))

(comment "CPSA 4.3.0")
(comment "All input read from tst/wang-key-hash-tst.scm")
(comment "Strand count bounded at 10")

(defprotocol wang basic
  (defrole init1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (send (cat k r))))
  (defrole init2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init3
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole init4
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init5
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole resp1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (recv (cat k r))))
  (defrole resp2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b)))) (recv (cat k r))))
  (defrole resp3
    (vars (a b t name) (e1 e2 x mesg))
    (trace
      (recv
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e1 e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))
          (enc "rcrq" (cat a b t (enc "h" (cat "h" e1)) x) e2
            (privk "sign" b))))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" e1)) x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab1
    (vars (a b t name) (y x mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (send (cat "sync-abrq" (enc "abrq" a b t y x (privk "sign" a))))
      (send
        (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab2
    (vars (a b t name) (y x e mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (recv
        (cat "sync-abrq"
          (enc "eortag" (enc "h" (cat "h" a b t y x)) e
            (privk "sign" b))))
      (send
        (enc "eortag" (enc "h" (cat "h" a b t y x)) e
          (privk "sign" b)))))
  (defrole ttp-rc1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-rc-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)))) (send (cat k r))))
  (defrole ttp-rc2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-rc-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-cf1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-cf-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (enc (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)) (privk "sign" t)))))
  (defrole ttp-cf2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-cf-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2))
        (false))))
  (defrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1))))))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (defstrand init1 1 (r r) (m m) (a a) (b b) (t t) (k k))
  (deflistener m)
  (non-orig (privk "encr" t))
  (uniq-orig m k)
  (comment "Experiment 1 to prove Lemma 4.1.")
  (traces
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))) ((recv m) (send m)))
  (label 0)
  (unrealized (1 0))
  (preskeleton)
  (origs (m (0 0)) (k (0 0)))
  (comment "Not a skeleton"))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (defstrand init1 1 (r r) (m m) (a a) (b b) (t t) (k k))
  (deflistener m)
  (precedes ((0 0) (1 0)))
  (non-orig (privk "encr" t))
  (uniq-orig m k)
  (traces
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))) ((recv m) (send m)))
  (label 1)
  (parent 0)
  (unrealized (1 0))
  (origs (m (0 0)) (k (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (defstrand init1 1 (r r) (m m) (a a) (b b) (t t) (k k))
  (deflistener m)
  (deflistener k)
  (precedes ((0 0) (2 0)) ((2 1) (1 0)))
  (non-orig (privk "encr" t))
  (uniq-orig m k)
  (operation nonce-test (added-listener k) m (1 0) (enc m k))
  (traces
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))) ((recv m) (send m)) ((recv k) (send k)))
  (label 2)
  (parent 1)
  (unrealized (2 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (deflistener m)
  (deflistener k)
  (defstrand init1 3 (r r) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 1) (0 0)) ((2 2) (1 0)))
  (non-orig (privk "encr" t))
  (uniq-orig m k)
  (operation nonce-test (displaced 0 3 init1 3) k (2 0)
    (enc "keytag"
      (enc "h"
        (cat "h" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
  (traces ((recv m) (send m)) ((recv k) (send k))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (send (cat k r))))
  (label 3)
  (parent 2)
  (unrealized)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (defstrand init1 1 (r r) (m m) (a a) (b b) (t t) (k k))
  (deflistener m)
  (deflistener k)
  (defstrand ttp-rc1 3 (y (enc "h" (cat "h" (enc m k)))) (r r) (a a)
    (b b) (t t) (k k))
  (precedes ((0 0) (3 0)) ((2 1) (1 0)) ((3 2) (2 0)))
  (non-orig (privk "encr" t))
  (uniq-orig m k)
  (operation nonce-test (added-strand ttp-rc1 3) k (2 0)
    (enc "keytag"
      (enc "h"
        (cat "h" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
  (traces
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))) ((recv m) (send m)) ((recv k) (send k))
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))
         (enc "eortag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))
         (enc "rcrq"
           (cat a b t (enc "h" (cat "h" (enc m k)))
             (enc "h" (cat "h" k)))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))))
      (send
        (cat "sync-rc-req"
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b)))) (send (cat k r))))
  (label 4)
  (parent 2)
  (unrealized)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (deflistener m)
  (defstrand init1 3 (r r) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 2) (0 0)))
  (non-orig (privk "encr" t))
  (uniq-orig m k)
  (operation generalization deleted (1 0))
  (traces ((recv m) (send m))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (send (cat k r))))
  (label 5)
  (parent 3)
  (unrealized)
  (shape)
  (maps ((1 0) ((b b) (t t) (m m) (r r) (k k) (a a))))
  (origs (m (1 0)) (k (1 0))))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (defstrand init1 1 (r r) (m m) (a a) (b b) (t t) (k k))
  (deflistener m)
  (defstrand ttp-rc1 3 (y (enc "h" (cat "h" (enc m k)))) (r r) (a a)
    (b b) (t t) (k k))
  (precedes ((0 0) (2 0)) ((2 2) (1 0)))
  (non-orig (privk "encr" t))
  (uniq-orig m k)
  (operation generalization deleted (2 0))
  (traces
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))) ((recv m) (send m))
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))
         (enc "eortag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))
         (enc "rcrq"
           (cat a b t (enc "h" (cat "h" (enc m k)))
             (enc "h" (cat "h" k)))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))))
      (send
        (cat "sync-rc-req"
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b)))) (send (cat k r))))
  (label 6)
  (parent 4)
  (unrealized)
  (shape)
  (maps ((0 1) ((b b) (t t) (m m) (r r) (k k) (a a))))
  (origs (m (0 0)) (k (0 0))))

(comment "Nothing left to do")

(defprotocol wang basic
  (defrole init1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (send (cat k r))))
  (defrole init2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init3
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole init4
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init5
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole resp1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (recv (cat k r))))
  (defrole resp2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b)))) (recv (cat k r))))
  (defrole resp3
    (vars (a b t name) (e1 e2 x mesg))
    (trace
      (recv
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e1 e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))
          (enc "rcrq" (cat a b t (enc "h" (cat "h" e1)) x) e2
            (privk "sign" b))))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" e1)) x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab1
    (vars (a b t name) (y x mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (send (cat "sync-abrq" (enc "abrq" a b t y x (privk "sign" a))))
      (send
        (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab2
    (vars (a b t name) (y x e mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (recv
        (cat "sync-abrq"
          (enc "eortag" (enc "h" (cat "h" a b t y x)) e
            (privk "sign" b))))
      (send
        (enc "eortag" (enc "h" (cat "h" a b t y x)) e
          (privk "sign" b)))))
  (defrole ttp-rc1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-rc-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)))) (send (cat k r))))
  (defrole ttp-rc2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-rc-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-cf1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-cf-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (enc (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)) (privk "sign" t)))))
  (defrole ttp-cf2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-cf-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2))
        (false))))
  (defrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1))))))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (defstrand init1 1 (r r) (m m) (a a) (b b) (t t) (k k))
  (deflistener k)
  (non-orig (privk "encr" t))
  (uniq-orig m k)
  (comment "Experiment 2 to prove Lemma 4.1.")
  (traces
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))) ((recv k) (send k)))
  (label 7)
  (unrealized (1 0))
  (preskeleton)
  (origs (m (0 0)) (k (0 0)))
  (comment "Not a skeleton"))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (defstrand init1 1 (r r) (m m) (a a) (b b) (t t) (k k))
  (deflistener k)
  (precedes ((0 0) (1 0)))
  (non-orig (privk "encr" t))
  (uniq-orig m k)
  (traces
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))) ((recv k) (send k)))
  (label 8)
  (parent 7)
  (unrealized (1 0))
  (origs (m (0 0)) (k (0 0)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (deflistener k)
  (defstrand init1 3 (r r) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 2) (0 0)))
  (non-orig (privk "encr" t))
  (uniq-orig m k)
  (operation nonce-test (displaced 0 2 init1 3) k (1 0)
    (enc "keytag"
      (enc "h"
        (cat "h" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
  (traces ((recv k) (send k))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (send (cat k r))))
  (label 9)
  (parent 8)
  (unrealized)
  (shape)
  (maps ((1 0) ((b b) (t t) (m m) (r r) (k k) (a a))))
  (origs (m (1 0)) (k (1 0))))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (defstrand init1 1 (r r) (m m) (a a) (b b) (t t) (k k))
  (deflistener k)
  (defstrand ttp-rc1 3 (y (enc "h" (cat "h" (enc m k)))) (r r) (a a)
    (b b) (t t) (k k))
  (precedes ((0 0) (2 0)) ((2 2) (1 0)))
  (non-orig (privk "encr" t))
  (uniq-orig m k)
  (operation nonce-test (added-strand ttp-rc1 3) k (1 0)
    (enc "keytag"
      (enc "h"
        (cat "h" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
  (traces
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))) ((recv k) (send k))
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))
         (enc "eortag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))
         (enc "rcrq"
           (cat a b t (enc "h" (cat "h" (enc m k)))
             (enc "h" (cat "h" k)))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))))
      (send
        (cat "sync-rc-req"
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b)))) (send (cat k r))))
  (label 10)
  (parent 8)
  (unrealized)
  (shape)
  (maps ((0 1) ((b b) (t t) (m m) (r r) (k k) (a a))))
  (origs (m (0 0)) (k (0 0))))

(comment "Nothing left to do")

(defprotocol wang basic
  (defrole init1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (send (cat k r))))
  (defrole init2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init3
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole init4
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init5
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole resp1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (recv (cat k r))))
  (defrole resp2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b)))) (recv (cat k r))))
  (defrole resp3
    (vars (a b t name) (e1 e2 x mesg))
    (trace
      (recv
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e1 e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))
          (enc "rcrq" (cat a b t (enc "h" (cat "h" e1)) x) e2
            (privk "sign" b))))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" e1)) x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab1
    (vars (a b t name) (y x mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (send (cat "sync-abrq" (enc "abrq" a b t y x (privk "sign" a))))
      (send
        (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab2
    (vars (a b t name) (y x e mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (recv
        (cat "sync-abrq"
          (enc "eortag" (enc "h" (cat "h" a b t y x)) e
            (privk "sign" b))))
      (send
        (enc "eortag" (enc "h" (cat "h" a b t y x)) e
          (privk "sign" b)))))
  (defrole ttp-rc1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-rc-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)))) (send (cat k r))))
  (defrole ttp-rc2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-rc-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-cf1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-cf-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (enc (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)) (privk "sign" t)))))
  (defrole ttp-cf2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-cf-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2))
        (false))))
  (defrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1))))))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (defstrand init1 3 (r r) (m m) (a a) (b b) (t t) (k k))
  (non-orig (privk "sign" b))
  (comment "First of three experiments to prove Lemma 4.2, clause 1.")
  (traces
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (send (cat k r))))
  (label 11)
  (unrealized (0 1))
  (origs)
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (defstrand init1 3 (r r) (m m) (a a) (b b) (t t) (k k))
  (defstrand resp1 2 (r r) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 1) (0 1)))
  (non-orig (privk "sign" b))
  (operation encryption-test (added-strand resp1 2)
    (enc "eortag"
      (enc "h"
        (cat "h" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k))))
      (enc "keytag"
        (enc "h"
          (cat "h" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))) k r (pubk "encr" t))
      (privk "sign" b)) (0 1))
  (traces
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (send (cat k r)))
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (label 12)
  (parent 11)
  (unrealized)
  (shape)
  (maps ((0) ((b b) (t t) (m m) (r r) (k k) (a a))))
  (origs))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (defstrand init1 3 (r r) (m m) (a a) (b b) (t t) (k k))
  (defstrand resp3 2 (e1 (enc m k))
    (e2
      (enc "keytag"
        (enc "h"
          (cat "h" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
    (x (enc "h" (cat "h" k))) (a a) (b b) (t t))
  (precedes ((1 1) (0 1)))
  (non-orig (privk "sign" b))
  (operation encryption-test (added-strand resp3 2)
    (enc "eortag"
      (enc "h"
        (cat "h" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k))))
      (enc "keytag"
        (enc "h"
          (cat "h" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))) k r (pubk "encr" t))
      (privk "sign" b)) (0 1))
  (traces
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (send (cat k r)))
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))))
  (label 13)
  (parent 11)
  (unrealized)
  (shape)
  (maps ((0) ((b b) (t t) (m m) (r r) (k k) (a a))))
  (origs))

(comment "Nothing left to do")

(defprotocol wang basic
  (defrole init1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (send (cat k r))))
  (defrole init2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init3
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole init4
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init5
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole resp1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (recv (cat k r))))
  (defrole resp2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b)))) (recv (cat k r))))
  (defrole resp3
    (vars (a b t name) (e1 e2 x mesg))
    (trace
      (recv
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e1 e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))
          (enc "rcrq" (cat a b t (enc "h" (cat "h" e1)) x) e2
            (privk "sign" b))))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" e1)) x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab1
    (vars (a b t name) (y x mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (send (cat "sync-abrq" (enc "abrq" a b t y x (privk "sign" a))))
      (send
        (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab2
    (vars (a b t name) (y x e mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (recv
        (cat "sync-abrq"
          (enc "eortag" (enc "h" (cat "h" a b t y x)) e
            (privk "sign" b))))
      (send
        (enc "eortag" (enc "h" (cat "h" a b t y x)) e
          (privk "sign" b)))))
  (defrole ttp-rc1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-rc-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)))) (send (cat k r))))
  (defrole ttp-rc2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-rc-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-cf1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-cf-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (enc (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)) (privk "sign" t)))))
  (defrole ttp-cf2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-cf-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2))
        (false))))
  (defrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1))))))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (defstrand init3 3 (r r) (m m) (a a) (b b) (t t) (k k))
  (non-orig (privk "sign" b))
  (comment "Second of three experiments to prove Lemma 4.2, clause 1.")
  (traces
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (label 14)
  (unrealized (0 2))
  (origs)
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (defstrand init3 3 (r r) (m m) (a a) (b b) (t t) (k k))
  (defstrand resp1 2 (r r) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 1) (0 2)))
  (non-orig (privk "sign" b))
  (operation encryption-test (added-strand resp1 2)
    (enc "eortag"
      (enc "h"
        (cat "h" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k))))
      (enc "keytag"
        (enc "h"
          (cat "h" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))) k r (pubk "encr" t))
      (privk "sign" b)) (0 2))
  (traces
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))))
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (label 15)
  (parent 14)
  (unrealized)
  (shape)
  (maps ((0) ((b b) (t t) (m m) (r r) (k k) (a a))))
  (origs))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (defstrand init3 3 (r r) (m m) (a a) (b b) (t t) (k k))
  (defstrand resp3 2 (e1 (enc m k))
    (e2
      (enc "keytag"
        (enc "h"
          (cat "h" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
    (x (enc "h" (cat "h" k))) (a a) (b b) (t t))
  (precedes ((1 1) (0 2)))
  (non-orig (privk "sign" b))
  (operation encryption-test (added-strand resp3 2)
    (enc "eortag"
      (enc "h"
        (cat "h" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k))))
      (enc "keytag"
        (enc "h"
          (cat "h" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))) k r (pubk "encr" t))
      (privk "sign" b)) (0 2))
  (traces
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))))
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))))
  (label 16)
  (parent 14)
  (unrealized)
  (shape)
  (maps ((0) ((b b) (t t) (m m) (r r) (k k) (a a))))
  (origs))

(comment "Nothing left to do")

(defprotocol wang basic
  (defrole init1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (send (cat k r))))
  (defrole init2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init3
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole init4
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init5
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole resp1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (recv (cat k r))))
  (defrole resp2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b)))) (recv (cat k r))))
  (defrole resp3
    (vars (a b t name) (e1 e2 x mesg))
    (trace
      (recv
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e1 e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))
          (enc "rcrq" (cat a b t (enc "h" (cat "h" e1)) x) e2
            (privk "sign" b))))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" e1)) x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab1
    (vars (a b t name) (y x mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (send (cat "sync-abrq" (enc "abrq" a b t y x (privk "sign" a))))
      (send
        (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab2
    (vars (a b t name) (y x e mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (recv
        (cat "sync-abrq"
          (enc "eortag" (enc "h" (cat "h" a b t y x)) e
            (privk "sign" b))))
      (send
        (enc "eortag" (enc "h" (cat "h" a b t y x)) e
          (privk "sign" b)))))
  (defrole ttp-rc1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-rc-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)))) (send (cat k r))))
  (defrole ttp-rc2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-rc-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-cf1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-cf-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (enc (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)) (privk "sign" t)))))
  (defrole ttp-cf2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-cf-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2))
        (false))))
  (defrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1))))))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (defstrand init5 4 (r r) (m m) (a a) (b b) (t t) (k k))
  (non-orig (privk "sign" b))
  (comment "Third of three experiments to prove Lemma 4.2, clause 1.")
  (traces
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (label 17)
  (unrealized (0 1) (0 3))
  (origs)
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (defstrand init5 4 (r r) (m m) (a a) (b b) (t t) (k k))
  (defstrand resp1 2 (r r) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 1) (0 1)))
  (non-orig (privk "sign" b))
  (operation encryption-test (added-strand resp1 2)
    (enc "eortag"
      (enc "h"
        (cat "h" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k))))
      (enc "keytag"
        (enc "h"
          (cat "h" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))) k r (pubk "encr" t))
      (privk "sign" b)) (0 1))
  (traces
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))))
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (label 18)
  (parent 17)
  (unrealized)
  (shape)
  (maps ((0) ((b b) (t t) (m m) (r r) (k k) (a a))))
  (origs))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (defstrand init5 4 (r r) (m m) (a a) (b b) (t t) (k k))
  (defstrand resp3 2 (e1 (enc m k))
    (e2
      (enc "keytag"
        (enc "h"
          (cat "h" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
    (x (enc "h" (cat "h" k))) (a a) (b b) (t t))
  (precedes ((1 1) (0 1)))
  (non-orig (privk "sign" b))
  (operation encryption-test (added-strand resp3 2)
    (enc "eortag"
      (enc "h"
        (cat "h" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k))))
      (enc "keytag"
        (enc "h"
          (cat "h" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))) k r (pubk "encr" t))
      (privk "sign" b)) (0 1))
  (traces
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))))
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))))
  (label 19)
  (parent 17)
  (unrealized)
  (shape)
  (maps ((0) ((b b) (t t) (m m) (r r) (k k) (a a))))
  (origs))

(comment "Nothing left to do")

(defprotocol wang basic
  (defrole init1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (send (cat k r))))
  (defrole init2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init3
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole init4
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init5
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole resp1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (recv (cat k r))))
  (defrole resp2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b)))) (recv (cat k r))))
  (defrole resp3
    (vars (a b t name) (e1 e2 x mesg))
    (trace
      (recv
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e1 e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))
          (enc "rcrq" (cat a b t (enc "h" (cat "h" e1)) x) e2
            (privk "sign" b))))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" e1)) x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab1
    (vars (a b t name) (y x mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (send (cat "sync-abrq" (enc "abrq" a b t y x (privk "sign" a))))
      (send
        (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab2
    (vars (a b t name) (y x e mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (recv
        (cat "sync-abrq"
          (enc "eortag" (enc "h" (cat "h" a b t y x)) e
            (privk "sign" b))))
      (send
        (enc "eortag" (enc "h" (cat "h" a b t y x)) e
          (privk "sign" b)))))
  (defrole ttp-rc1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-rc-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)))) (send (cat k r))))
  (defrole ttp-rc2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-rc-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-cf1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-cf-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (enc (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)) (privk "sign" t)))))
  (defrole ttp-cf2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-cf-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2))
        (false))))
  (defrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1))))))

(defskeleton wang
  (vars (r text) (m data) (a t b name) (k skey))
  (defstrand resp1 3 (r r) (m m) (a a) (b b) (t t) (k k))
  (non-orig (privk "sign" a))
  (comment "First of two experiments to prove Lemma 4.2, clause 2.")
  (traces
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (recv (cat k r))))
  (label 20)
  (unrealized (0 0))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton wang
  (vars (r text) (m data) (a t b name) (k skey))
  (defstrand resp1 3 (r r) (m m) (a a) (b b) (t t) (k k))
  (defstrand init5 1 (r r) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 0) (0 0)))
  (non-orig (privk "sign" a))
  (operation encryption-test (added-strand init5 1)
    (enc "eootag"
      (enc "h"
        (cat "h" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k))))
      (enc "keytag"
        (enc "h"
          (cat "h" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))) k r (pubk "encr" t))
      (privk "sign" a)) (0 0))
  (traces
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (recv (cat k r)))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))))
  (label 21)
  (parent 20)
  (unrealized)
  (shape)
  (maps ((0) ((a a) (t t) (m m) (r r) (k k) (b b))))
  (origs))

(comment "Nothing left to do")

(defprotocol wang basic
  (defrole init1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (send (cat k r))))
  (defrole init2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init3
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole init4
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init5
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole resp1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (recv (cat k r))))
  (defrole resp2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b)))) (recv (cat k r))))
  (defrole resp3
    (vars (a b t name) (e1 e2 x mesg))
    (trace
      (recv
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e1 e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))
          (enc "rcrq" (cat a b t (enc "h" (cat "h" e1)) x) e2
            (privk "sign" b))))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" e1)) x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab1
    (vars (a b t name) (y x mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (send (cat "sync-abrq" (enc "abrq" a b t y x (privk "sign" a))))
      (send
        (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab2
    (vars (a b t name) (y x e mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (recv
        (cat "sync-abrq"
          (enc "eortag" (enc "h" (cat "h" a b t y x)) e
            (privk "sign" b))))
      (send
        (enc "eortag" (enc "h" (cat "h" a b t y x)) e
          (privk "sign" b)))))
  (defrole ttp-rc1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-rc-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)))) (send (cat k r))))
  (defrole ttp-rc2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-rc-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-cf1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-cf-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (enc (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)) (privk "sign" t)))))
  (defrole ttp-cf2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-cf-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2))
        (false))))
  (defrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1))))))

(defskeleton wang
  (vars (r text) (m data) (a t b name) (k skey))
  (defstrand resp2 4 (r r) (m m) (a a) (b b) (t t) (k k))
  (non-orig (privk "sign" a))
  (comment "Second of two experiments to prove Lemma 4.2, clause 2.")
  (traces
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b)))) (recv (cat k r))))
  (label 22)
  (unrealized (0 0))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton wang
  (vars (r text) (m data) (a t b name) (k skey))
  (defstrand resp2 4 (r r) (m m) (a a) (b b) (t t) (k k))
  (defstrand init5 1 (r r) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 0) (0 0)))
  (non-orig (privk "sign" a))
  (operation encryption-test (added-strand init5 1)
    (enc "eootag"
      (enc "h"
        (cat "h" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k))))
      (enc "keytag"
        (enc "h"
          (cat "h" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))) k r (pubk "encr" t))
      (privk "sign" a)) (0 0))
  (traces
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b)))) (recv (cat k r)))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))))
  (label 23)
  (parent 22)
  (unrealized)
  (shape)
  (maps ((0) ((a a) (t t) (m m) (r r) (k k) (b b))))
  (origs))

(comment "Nothing left to do")

(defprotocol wang basic
  (defrole init1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (send (cat k r))))
  (defrole init2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init3
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole init4
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init5
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole resp1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (recv (cat k r))))
  (defrole resp2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b)))) (recv (cat k r))))
  (defrole resp3
    (vars (a b t name) (e1 e2 x mesg))
    (trace
      (recv
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e1 e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))
          (enc "rcrq" (cat a b t (enc "h" (cat "h" e1)) x) e2
            (privk "sign" b))))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" e1)) x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab1
    (vars (a b t name) (y x mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (send (cat "sync-abrq" (enc "abrq" a b t y x (privk "sign" a))))
      (send
        (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab2
    (vars (a b t name) (y x e mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (recv
        (cat "sync-abrq"
          (enc "eortag" (enc "h" (cat "h" a b t y x)) e
            (privk "sign" b))))
      (send
        (enc "eortag" (enc "h" (cat "h" a b t y x)) e
          (privk "sign" b)))))
  (defrole ttp-rc1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-rc-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)))) (send (cat k r))))
  (defrole ttp-rc2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-rc-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-cf1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-cf-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (enc (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)) (privk "sign" t)))))
  (defrole ttp-cf2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-cf-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2))
        (false))))
  (defrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1))))))

(defskeleton wang
  (vars (e1 e2 x mesg) (a t b name))
  (defstrand resp3 4 (e1 e1) (e2 e2) (x x) (a a) (b b) (t t))
  (non-orig (privk "sign" a))
  (comment "Experiments to prove Lemma 4.2, clause 3.")
  (traces
    ((recv
       (cat (cat a b t (enc "h" (cat "h" e1)) x) e1 e2
         (enc "eootag"
           (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
           (privk "sign" a))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))
          (enc "rcrq" (cat a b t (enc "h" (cat "h" e1)) x) e2
            (privk "sign" b))))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" e1)) x (privk "sign" a))
          (privk "sign" t)))))
  (label 24)
  (unrealized (0 0) (0 3))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton wang
  (vars (r text) (m data) (a t b name) (k skey))
  (defstrand resp3 4 (e1 (enc m k))
    (e2
      (enc "keytag"
        (enc "h"
          (cat "h" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
    (x (enc "h" (cat "h" k))) (a a) (b b) (t t))
  (defstrand init5 1 (r r) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 0) (0 0)))
  (non-orig (privk "sign" a))
  (operation encryption-test (added-strand init5 1)
    (enc "eootag"
      (enc "h"
        (cat "h" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k))))
      (enc "keytag"
        (enc "h"
          (cat "h" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))) k r (pubk "encr" t))
      (privk "sign" a)) (0 0))
  (traces
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))))
  (label 25)
  (parent 24)
  (unrealized (0 3))
  (comment "4 in cohort - 4 not yet seen"))

(defskeleton wang
  (vars (r r-0 text) (m data) (a t b name) (k skey))
  (defstrand resp3 4 (e1 (enc m k))
    (e2
      (enc "keytag"
        (enc "h"
          (cat "h" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
    (x (enc "h" (cat "h" k))) (a a) (b b) (t t))
  (defstrand init5 1 (r r) (m m) (a a) (b b) (t t) (k k))
  (defstrand init3 2 (r r-0) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 0) (0 0)) ((2 1) (0 3)))
  (non-orig (privk "sign" a))
  (operation encryption-test (added-strand init3 2)
    (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
      (enc "h" (cat "h" k)) (privk "sign" a)) (0 3))
  (traces
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a)))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r-0 (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r-0 (pubk "encr" t))
           (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))))
  (label 26)
  (parent 25)
  (unrealized)
  (shape)
  (maps
    ((0)
      ((a a) (t t) (b b) (e1 (enc m k))
        (e2
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
        (x (enc "h" (cat "h" k))))))
  (origs))

(defskeleton wang
  (vars (r text) (m data) (a t b name) (k skey))
  (defstrand resp3 4 (e1 (enc m k))
    (e2
      (enc "keytag"
        (enc "h"
          (cat "h" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
    (x (enc "h" (cat "h" k))) (a a) (b b) (t t))
  (defstrand init3 2 (r r) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 0) (0 0)) ((1 1) (0 3)))
  (non-orig (privk "sign" a))
  (operation encryption-test (displaced 1 2 init3 2)
    (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
      (enc "h" (cat "h" k)) (privk "sign" a)) (0 3))
  (traces
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))))
  (label 27)
  (parent 25)
  (unrealized)
  (shape)
  (maps
    ((0)
      ((a a) (t t) (b b) (e1 (enc m k))
        (e2
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
        (x (enc "h" (cat "h" k))))))
  (origs))

(defskeleton wang
  (vars (r text) (m data) (a t b name) (k skey))
  (defstrand resp3 4 (e1 (enc m k))
    (e2
      (enc "keytag"
        (enc "h"
          (cat "h" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
    (x (enc "h" (cat "h" k))) (a a) (b b) (t t))
  (defstrand init5 3 (r r) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 0) (0 0)) ((1 2) (0 3)))
  (non-orig (privk "sign" a))
  (operation encryption-test (displaced 1 2 init5 3)
    (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
      (enc "h" (cat "h" k)) (privk "sign" a)) (0 3))
  (traces
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))))
  (label 28)
  (parent 25)
  (unrealized)
  (shape)
  (maps
    ((0)
      ((a a) (t t) (b b) (e1 (enc m k))
        (e2
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
        (x (enc "h" (cat "h" k))))))
  (origs))

(defskeleton wang
  (vars (r r-0 text) (m data) (a t b name) (k skey))
  (defstrand resp3 4 (e1 (enc m k))
    (e2
      (enc "keytag"
        (enc "h"
          (cat "h" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
    (x (enc "h" (cat "h" k))) (a a) (b b) (t t))
  (defstrand init5 1 (r r) (m m) (a a) (b b) (t t) (k k))
  (defstrand init5 3 (r r-0) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 0) (0 0)) ((2 2) (0 3)))
  (non-orig (privk "sign" a))
  (operation encryption-test (added-strand init5 3)
    (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
      (enc "h" (cat "h" k)) (privk "sign" a)) (0 3))
  (traces
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a)))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r-0 (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r-0 (pubk "encr" t))
           (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r-0 (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))))
  (label 29)
  (parent 25)
  (unrealized)
  (shape)
  (maps
    ((0)
      ((a a) (t t) (b b) (e1 (enc m k))
        (e2
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
        (x (enc "h" (cat "h" k))))))
  (origs))

(comment "Nothing left to do")

(defprotocol wang basic
  (defrole init1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (send (cat k r))))
  (defrole init2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init3
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole init4
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init5
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole resp1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (recv (cat k r))))
  (defrole resp2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b)))) (recv (cat k r))))
  (defrole resp3
    (vars (a b t name) (e1 e2 x mesg))
    (trace
      (recv
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e1 e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))
          (enc "rcrq" (cat a b t (enc "h" (cat "h" e1)) x) e2
            (privk "sign" b))))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" e1)) x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab1
    (vars (a b t name) (y x mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (send (cat "sync-abrq" (enc "abrq" a b t y x (privk "sign" a))))
      (send
        (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab2
    (vars (a b t name) (y x e mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (recv
        (cat "sync-abrq"
          (enc "eortag" (enc "h" (cat "h" a b t y x)) e
            (privk "sign" b))))
      (send
        (enc "eortag" (enc "h" (cat "h" a b t y x)) e
          (privk "sign" b)))))
  (defrole ttp-rc1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-rc-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)))) (send (cat k r))))
  (defrole ttp-rc2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-rc-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-cf1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-cf-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (enc (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)) (privk "sign" t)))))
  (defrole ttp-cf2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-cf-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2))
        (false))))
  (defrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1))))))

(defskeleton wang
  (vars (y x mesg) (a b t name))
  (deflistener
    (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
      (privk "sign" t)))
  (non-orig (privk "sign" t))
  (comment "Experiments to prove Lemma 4.3, clause 1.")
  (traces
    ((recv
       (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
         (privk "sign" t)))
      (send
        (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
          (privk "sign" t)))))
  (label 30)
  (unrealized (0 0))
  (origs)
  (comment "3 in cohort - 3 not yet seen"))

(defskeleton wang
  (vars (y x mesg) (a b t name))
  (deflistener
    (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
      (privk "sign" t)))
  (defstrand ttp-ab1 3 (y y) (x x) (a a) (b b) (t t))
  (precedes ((1 2) (0 0)))
  (non-orig (privk "sign" t))
  (operation encryption-test (added-strand ttp-ab1 3)
    (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
      (privk "sign" t)) (0 0))
  (traces
    ((recv
       (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
         (privk "sign" t)))
      (send
        (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
          (privk "sign" t))))
    ((recv (enc "abrq" a b t y x (privk "sign" a)))
      (send (cat "sync-abrq" (enc "abrq" a b t y x (privk "sign" a))))
      (send
        (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
          (privk "sign" t)))))
  (label 31)
  (parent 30)
  (unrealized)
  (shape)
  (maps ((0) ((a a) (b b) (t t) (y y) (x x))))
  (origs))

(defskeleton wang
  (vars (y mesg) (r text) (a b t name) (k skey))
  (deflistener
    (enc "abcf"
      (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
      (privk "sign" t)))
  (defstrand ttp-rc2 3 (y y) (r r) (a a) (b b) (t t) (k k))
  (precedes ((1 2) (0 0)))
  (non-orig (privk "sign" t))
  (operation encryption-test (added-strand ttp-rc2 3)
    (enc "abcf"
      (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
      (privk "sign" t)) (0 0))
  (traces
    ((recv
       (enc "abcf"
         (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
         (privk "sign" t)))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t))))
    ((recv
       (cat (cat a b t y (enc "h" (cat "h" k)))
         (enc "keytag" (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
           k r (pubk "encr" t))
         (enc "eootag" (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
             (pubk "encr" t)) (privk "sign" a))
         (enc "eortag" (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
             (pubk "encr" t)) (privk "sign" b))
         (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
           (enc "keytag"
             (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
             (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-rc-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (label 32)
  (parent 30)
  (unrealized)
  (shape)
  (maps ((0) ((a a) (b b) (t t) (y y) (x (enc "h" (cat "h" k))))))
  (origs))

(defskeleton wang
  (vars (y mesg) (r text) (a b t name) (k skey))
  (deflistener
    (enc "abcf"
      (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
      (privk "sign" t)))
  (defstrand ttp-cf2 3 (y y) (r r) (a a) (b b) (t t) (k k))
  (precedes ((1 2) (0 0)))
  (non-orig (privk "sign" t))
  (operation encryption-test (added-strand ttp-cf2 3)
    (enc "abcf"
      (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
      (privk "sign" t)) (0 0))
  (traces
    ((recv
       (enc "abcf"
         (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
         (privk "sign" t)))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t))))
    ((recv
       (cat (cat a b t y (enc "h" (cat "h" k)))
         (enc "keytag" (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
           k r (pubk "encr" t))
         (enc "eootag" (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
             (pubk "encr" t)) (privk "sign" a))
         (enc "eortag" (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
             (pubk "encr" t)) (privk "sign" b))
         (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
           (enc "keytag"
             (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
             (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-cf-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (label 33)
  (parent 30)
  (unrealized)
  (shape)
  (maps ((0) ((a a) (b b) (t t) (y y) (x (enc "h" (cat "h" k))))))
  (origs))

(comment "Nothing left to do")

(defprotocol wang basic
  (defrole init1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (send (cat k r))))
  (defrole init2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init3
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole init4
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init5
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole resp1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (recv (cat k r))))
  (defrole resp2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b)))) (recv (cat k r))))
  (defrole resp3
    (vars (a b t name) (e1 e2 x mesg))
    (trace
      (recv
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e1 e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))
          (enc "rcrq" (cat a b t (enc "h" (cat "h" e1)) x) e2
            (privk "sign" b))))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" e1)) x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab1
    (vars (a b t name) (y x mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (send (cat "sync-abrq" (enc "abrq" a b t y x (privk "sign" a))))
      (send
        (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab2
    (vars (a b t name) (y x e mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (recv
        (cat "sync-abrq"
          (enc "eortag" (enc "h" (cat "h" a b t y x)) e
            (privk "sign" b))))
      (send
        (enc "eortag" (enc "h" (cat "h" a b t y x)) e
          (privk "sign" b)))))
  (defrole ttp-rc1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-rc-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)))) (send (cat k r))))
  (defrole ttp-rc2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-rc-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-cf1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-cf-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (enc (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)) (privk "sign" t)))))
  (defrole ttp-cf2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-cf-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2))
        (false))))
  (defrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1))))))

(defskeleton wang
  (vars (y x mesg) (a b t name))
  (defstrand ttp-ab1 3 (y y) (x x) (a a) (b b) (t t))
  (non-orig (privk "encr" t) (privk "sign" a))
  (comment "Experiment 1 to prove Lemma 4.3, clause 2.")
  (traces
    ((recv (enc "abrq" a b t y x (privk "sign" a)))
      (send (cat "sync-abrq" (enc "abrq" a b t y x (privk "sign" a))))
      (send
        (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
          (privk "sign" t)))))
  (label 34)
  (unrealized (0 0))
  (origs)
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton wang
  (vars (r text) (m data) (a b t name) (k skey))
  (defstrand ttp-ab1 3 (y (enc "h" (cat "h" (enc m k))))
    (x (enc "h" (cat "h" k))) (a a) (b b) (t t))
  (defstrand init3 2 (r r) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 1) (0 0)))
  (non-orig (privk "encr" t) (privk "sign" a))
  (operation encryption-test (added-strand init3 2)
    (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
      (enc "h" (cat "h" k)) (privk "sign" a)) (0 0))
  (traces
    ((recv
       (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
         (enc "h" (cat "h" k)) (privk "sign" a)))
      (send
        (cat "sync-abrq"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))))
  (label 35)
  (parent 34)
  (unrealized)
  (shape)
  (maps
    ((0)
      ((y (enc "h" (cat "h" (enc m k)))) (x (enc "h" (cat "h" k))) (a a)
        (b b) (t t))))
  (origs))

(defskeleton wang
  (vars (r text) (m data) (a b t name) (k skey))
  (defstrand ttp-ab1 3 (y (enc "h" (cat "h" (enc m k))))
    (x (enc "h" (cat "h" k))) (a a) (b b) (t t))
  (defstrand init5 3 (r r) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 2) (0 0)))
  (non-orig (privk "encr" t) (privk "sign" a))
  (operation encryption-test (added-strand init5 3)
    (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
      (enc "h" (cat "h" k)) (privk "sign" a)) (0 0))
  (traces
    ((recv
       (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
         (enc "h" (cat "h" k)) (privk "sign" a)))
      (send
        (cat "sync-abrq"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))))
  (label 36)
  (parent 34)
  (unrealized)
  (shape)
  (maps
    ((0)
      ((y (enc "h" (cat "h" (enc m k)))) (x (enc "h" (cat "h" k))) (a a)
        (b b) (t t))))
  (origs))

(comment "Nothing left to do")

(defprotocol wang basic
  (defrole init1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (send (cat k r))))
  (defrole init2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init3
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole init4
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init5
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole resp1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (recv (cat k r))))
  (defrole resp2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b)))) (recv (cat k r))))
  (defrole resp3
    (vars (a b t name) (e1 e2 x mesg))
    (trace
      (recv
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e1 e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))
          (enc "rcrq" (cat a b t (enc "h" (cat "h" e1)) x) e2
            (privk "sign" b))))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" e1)) x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab1
    (vars (a b t name) (y x mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (send (cat "sync-abrq" (enc "abrq" a b t y x (privk "sign" a))))
      (send
        (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab2
    (vars (a b t name) (y x e mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (recv
        (cat "sync-abrq"
          (enc "eortag" (enc "h" (cat "h" a b t y x)) e
            (privk "sign" b))))
      (send
        (enc "eortag" (enc "h" (cat "h" a b t y x)) e
          (privk "sign" b)))))
  (defrole ttp-rc1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-rc-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)))) (send (cat k r))))
  (defrole ttp-rc2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-rc-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-cf1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-cf-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (enc (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)) (privk "sign" t)))))
  (defrole ttp-cf2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-cf-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2))
        (false))))
  (defrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1))))))

(defskeleton wang
  (vars (y mesg) (r text) (a b t name) (k skey))
  (defstrand ttp-rc2 3 (y y) (r r) (a a) (b b) (t t) (k k))
  (non-orig (privk "encr" t) (privk "sign" a))
  (comment "Experiment 2 to prove Lemma 4.3, clause 2.")
  (traces
    ((recv
       (cat (cat a b t y (enc "h" (cat "h" k)))
         (enc "keytag" (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
           k r (pubk "encr" t))
         (enc "eootag" (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
             (pubk "encr" t)) (privk "sign" a))
         (enc "eortag" (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
             (pubk "encr" t)) (privk "sign" b))
         (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
           (enc "keytag"
             (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
             (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-rc-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (label 37)
  (unrealized (0 0) (0 1))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton wang
  (vars (r text) (m data) (a b t name) (k skey))
  (defstrand ttp-rc2 3 (y (enc "h" (cat "h" (enc m k)))) (r r) (a a)
    (b b) (t t) (k k))
  (defstrand init5 1 (r r) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 0) (0 0)))
  (non-orig (privk "encr" t) (privk "sign" a))
  (operation encryption-test (added-strand init5 1)
    (enc "eootag"
      (enc "h"
        (cat "h" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k))))
      (enc "keytag"
        (enc "h"
          (cat "h" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))) k r (pubk "encr" t))
      (privk "sign" a)) (0 0))
  (traces
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))
         (enc "eortag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))
         (enc "rcrq"
           (cat a b t (enc "h" (cat "h" (enc m k)))
             (enc "h" (cat "h" k)))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))))
      (recv
        (cat "sync-rc-req"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))))
  (label 38)
  (parent 37)
  (unrealized (0 1))
  (comment "4 in cohort - 4 not yet seen"))

(defskeleton wang
  (vars (r r-0 text) (m data) (a b t name) (k skey))
  (defstrand ttp-rc2 3 (y (enc "h" (cat "h" (enc m k)))) (r r) (a a)
    (b b) (t t) (k k))
  (defstrand init5 1 (r r) (m m) (a a) (b b) (t t) (k k))
  (defstrand init3 2 (r r-0) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 0) (0 0)) ((2 1) (0 1)))
  (non-orig (privk "encr" t) (privk "sign" a))
  (operation encryption-test (added-strand init3 2)
    (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
      (enc "h" (cat "h" k)) (privk "sign" a)) (0 1))
  (traces
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))
         (enc "eortag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))
         (enc "rcrq"
           (cat a b t (enc "h" (cat "h" (enc m k)))
             (enc "h" (cat "h" k)))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))))
      (recv
        (cat "sync-rc-req"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a)))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r-0 (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r-0 (pubk "encr" t))
           (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))))
  (label 39)
  (parent 38)
  (unrealized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (t t) (r r) (k k)
        (y (enc "h" (cat "h" (enc m k)))))))
  (origs))

(defskeleton wang
  (vars (r text) (m data) (a b t name) (k skey))
  (defstrand ttp-rc2 3 (y (enc "h" (cat "h" (enc m k)))) (r r) (a a)
    (b b) (t t) (k k))
  (defstrand init3 2 (r r) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 0) (0 0)) ((1 1) (0 1)))
  (non-orig (privk "encr" t) (privk "sign" a))
  (operation encryption-test (displaced 1 2 init3 2)
    (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
      (enc "h" (cat "h" k)) (privk "sign" a)) (0 1))
  (traces
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))
         (enc "eortag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))
         (enc "rcrq"
           (cat a b t (enc "h" (cat "h" (enc m k)))
             (enc "h" (cat "h" k)))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))))
      (recv
        (cat "sync-rc-req"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))))
  (label 40)
  (parent 38)
  (unrealized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (t t) (r r) (k k)
        (y (enc "h" (cat "h" (enc m k)))))))
  (origs))

(defskeleton wang
  (vars (r text) (m data) (a b t name) (k skey))
  (defstrand ttp-rc2 3 (y (enc "h" (cat "h" (enc m k)))) (r r) (a a)
    (b b) (t t) (k k))
  (defstrand init5 3 (r r) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 0) (0 0)) ((1 2) (0 1)))
  (non-orig (privk "encr" t) (privk "sign" a))
  (operation encryption-test (displaced 1 2 init5 3)
    (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
      (enc "h" (cat "h" k)) (privk "sign" a)) (0 1))
  (traces
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))
         (enc "eortag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))
         (enc "rcrq"
           (cat a b t (enc "h" (cat "h" (enc m k)))
             (enc "h" (cat "h" k)))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))))
      (recv
        (cat "sync-rc-req"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))))
  (label 41)
  (parent 38)
  (unrealized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (t t) (r r) (k k)
        (y (enc "h" (cat "h" (enc m k)))))))
  (origs))

(defskeleton wang
  (vars (r r-0 text) (m data) (a b t name) (k skey))
  (defstrand ttp-rc2 3 (y (enc "h" (cat "h" (enc m k)))) (r r) (a a)
    (b b) (t t) (k k))
  (defstrand init5 1 (r r) (m m) (a a) (b b) (t t) (k k))
  (defstrand init5 3 (r r-0) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 0) (0 0)) ((2 2) (0 1)))
  (non-orig (privk "encr" t) (privk "sign" a))
  (operation encryption-test (added-strand init5 3)
    (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
      (enc "h" (cat "h" k)) (privk "sign" a)) (0 1))
  (traces
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))
         (enc "eortag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))
         (enc "rcrq"
           (cat a b t (enc "h" (cat "h" (enc m k)))
             (enc "h" (cat "h" k)))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))))
      (recv
        (cat "sync-rc-req"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a)))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r-0 (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r-0 (pubk "encr" t))
           (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r-0 (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))))
  (label 42)
  (parent 38)
  (unrealized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (t t) (r r) (k k)
        (y (enc "h" (cat "h" (enc m k)))))))
  (origs))

(comment "Nothing left to do")

(defprotocol wang basic
  (defrole init1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (send (cat k r))))
  (defrole init2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init3
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole init4
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init5
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole resp1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (recv (cat k r))))
  (defrole resp2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b)))) (recv (cat k r))))
  (defrole resp3
    (vars (a b t name) (e1 e2 x mesg))
    (trace
      (recv
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e1 e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))
          (enc "rcrq" (cat a b t (enc "h" (cat "h" e1)) x) e2
            (privk "sign" b))))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" e1)) x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab1
    (vars (a b t name) (y x mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (send (cat "sync-abrq" (enc "abrq" a b t y x (privk "sign" a))))
      (send
        (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab2
    (vars (a b t name) (y x e mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (recv
        (cat "sync-abrq"
          (enc "eortag" (enc "h" (cat "h" a b t y x)) e
            (privk "sign" b))))
      (send
        (enc "eortag" (enc "h" (cat "h" a b t y x)) e
          (privk "sign" b)))))
  (defrole ttp-rc1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-rc-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)))) (send (cat k r))))
  (defrole ttp-rc2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-rc-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-cf1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-cf-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (enc (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)) (privk "sign" t)))))
  (defrole ttp-cf2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-cf-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2))
        (false))))
  (defrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1))))))

(defskeleton wang
  (vars (y mesg) (r text) (a b t name) (k skey))
  (defstrand ttp-cf2 3 (y y) (r r) (a a) (b b) (t t) (k k))
  (non-orig (privk "encr" t) (privk "sign" a))
  (comment "Experiment 3 to prove Lemma 4.3, clause 2.")
  (traces
    ((recv
       (cat (cat a b t y (enc "h" (cat "h" k)))
         (enc "keytag" (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
           k r (pubk "encr" t))
         (enc "eootag" (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
             (pubk "encr" t)) (privk "sign" a))
         (enc "eortag" (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
             (pubk "encr" t)) (privk "sign" b))
         (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
           (enc "keytag"
             (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
             (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-cf-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (label 43)
  (unrealized (0 0) (0 1))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton wang
  (vars (r text) (m data) (a b t name) (k skey))
  (defstrand ttp-cf2 3 (y (enc "h" (cat "h" (enc m k)))) (r r) (a a)
    (b b) (t t) (k k))
  (defstrand init5 1 (r r) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 0) (0 0)))
  (non-orig (privk "encr" t) (privk "sign" a))
  (operation encryption-test (added-strand init5 1)
    (enc "eootag"
      (enc "h"
        (cat "h" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k))))
      (enc "keytag"
        (enc "h"
          (cat "h" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))) k r (pubk "encr" t))
      (privk "sign" a)) (0 0))
  (traces
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))
         (enc "eortag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))
         (enc "cfrq"
           (cat a b t (enc "h" (cat "h" (enc m k)))
             (enc "h" (cat "h" k)))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))))
      (recv
        (cat "sync-cf-req"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))))
  (label 44)
  (parent 43)
  (unrealized (0 1))
  (comment "4 in cohort - 4 not yet seen"))

(defskeleton wang
  (vars (r r-0 text) (m data) (a b t name) (k skey))
  (defstrand ttp-cf2 3 (y (enc "h" (cat "h" (enc m k)))) (r r) (a a)
    (b b) (t t) (k k))
  (defstrand init5 1 (r r) (m m) (a a) (b b) (t t) (k k))
  (defstrand init3 2 (r r-0) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 0) (0 0)) ((2 1) (0 1)))
  (non-orig (privk "encr" t) (privk "sign" a))
  (operation encryption-test (added-strand init3 2)
    (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
      (enc "h" (cat "h" k)) (privk "sign" a)) (0 1))
  (traces
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))
         (enc "eortag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))
         (enc "cfrq"
           (cat a b t (enc "h" (cat "h" (enc m k)))
             (enc "h" (cat "h" k)))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))))
      (recv
        (cat "sync-cf-req"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a)))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r-0 (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r-0 (pubk "encr" t))
           (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))))
  (label 45)
  (parent 44)
  (unrealized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (t t) (r r) (k k)
        (y (enc "h" (cat "h" (enc m k)))))))
  (origs))

(defskeleton wang
  (vars (r text) (m data) (a b t name) (k skey))
  (defstrand ttp-cf2 3 (y (enc "h" (cat "h" (enc m k)))) (r r) (a a)
    (b b) (t t) (k k))
  (defstrand init3 2 (r r) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 0) (0 0)) ((1 1) (0 1)))
  (non-orig (privk "encr" t) (privk "sign" a))
  (operation encryption-test (displaced 1 2 init3 2)
    (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
      (enc "h" (cat "h" k)) (privk "sign" a)) (0 1))
  (traces
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))
         (enc "eortag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))
         (enc "cfrq"
           (cat a b t (enc "h" (cat "h" (enc m k)))
             (enc "h" (cat "h" k)))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))))
      (recv
        (cat "sync-cf-req"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))))
  (label 46)
  (parent 44)
  (unrealized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (t t) (r r) (k k)
        (y (enc "h" (cat "h" (enc m k)))))))
  (origs))

(defskeleton wang
  (vars (r text) (m data) (a b t name) (k skey))
  (defstrand ttp-cf2 3 (y (enc "h" (cat "h" (enc m k)))) (r r) (a a)
    (b b) (t t) (k k))
  (defstrand init5 3 (r r) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 0) (0 0)) ((1 2) (0 1)))
  (non-orig (privk "encr" t) (privk "sign" a))
  (operation encryption-test (displaced 1 2 init5 3)
    (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
      (enc "h" (cat "h" k)) (privk "sign" a)) (0 1))
  (traces
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))
         (enc "eortag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))
         (enc "cfrq"
           (cat a b t (enc "h" (cat "h" (enc m k)))
             (enc "h" (cat "h" k)))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))))
      (recv
        (cat "sync-cf-req"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))))
  (label 47)
  (parent 44)
  (unrealized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (t t) (r r) (k k)
        (y (enc "h" (cat "h" (enc m k)))))))
  (origs))

(defskeleton wang
  (vars (r r-0 text) (m data) (a b t name) (k skey))
  (defstrand ttp-cf2 3 (y (enc "h" (cat "h" (enc m k)))) (r r) (a a)
    (b b) (t t) (k k))
  (defstrand init5 1 (r r) (m m) (a a) (b b) (t t) (k k))
  (defstrand init5 3 (r r-0) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 0) (0 0)) ((2 2) (0 1)))
  (non-orig (privk "encr" t) (privk "sign" a))
  (operation encryption-test (added-strand init5 3)
    (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
      (enc "h" (cat "h" k)) (privk "sign" a)) (0 1))
  (traces
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))
         (enc "eortag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))
         (enc "cfrq"
           (cat a b t (enc "h" (cat "h" (enc m k)))
             (enc "h" (cat "h" k)))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))))
      (recv
        (cat "sync-cf-req"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a)))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r-0 (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r-0 (pubk "encr" t))
           (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r-0 (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))))
  (label 48)
  (parent 44)
  (unrealized)
  (shape)
  (maps
    ((0)
      ((a a) (b b) (t t) (r r) (k k)
        (y (enc "h" (cat "h" (enc m k)))))))
  (origs))

(comment "Nothing left to do")

(defprotocol wang basic
  (defrole init1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (send (cat k r))))
  (defrole init2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init3
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole init4
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init5
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole resp1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (recv (cat k r))))
  (defrole resp2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b)))) (recv (cat k r))))
  (defrole resp3
    (vars (a b t name) (e1 e2 x mesg))
    (trace
      (recv
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e1 e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))
          (enc "rcrq" (cat a b t (enc "h" (cat "h" e1)) x) e2
            (privk "sign" b))))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" e1)) x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab1
    (vars (a b t name) (y x mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (send (cat "sync-abrq" (enc "abrq" a b t y x (privk "sign" a))))
      (send
        (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab2
    (vars (a b t name) (y x e mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (recv
        (cat "sync-abrq"
          (enc "eortag" (enc "h" (cat "h" a b t y x)) e
            (privk "sign" b))))
      (send
        (enc "eortag" (enc "h" (cat "h" a b t y x)) e
          (privk "sign" b)))))
  (defrole ttp-rc1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-rc-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)))) (send (cat k r))))
  (defrole ttp-rc2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-rc-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-cf1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-cf-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (enc (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)) (privk "sign" t)))))
  (defrole ttp-cf2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-cf-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2))
        (false))))
  (defrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1))))))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (deflistener m)
  (defstrand init1 1 (r r) (m m) (a a) (b b) (t t) (k k))
  (non-orig (privk "encr" t))
  (uniq-orig m k)
  (goals
    (forall ((r text) (m data) (b t a name) (k skey) (z z-0 strd))
      (implies
        (and (p "init1" z 1) (p "" z-0 2) (p "init1" "r" z r)
          (p "init1" "m" z m) (p "init1" "a" z a) (p "init1" "b" z b)
          (p "init1" "t" z t) (p "init1" "k" z k) (p "" "x" z-0 m)
          (non (privk "encr" t)) (uniq-at m z 0) (uniq-at k z 0))
        (or (and (p "init1" z 3) (prec z 2 z-0 0))
          (exists ((z-1 strd))
            (and (p "ttp-rc1" z-1 3)
              (p "ttp-rc1" "y" z-1 (enc "h" (cat "h" (enc m k))))
              (p "ttp-rc1" "r" z-1 r) (p "ttp-rc1" "a" z-1 a)
              (p "ttp-rc1" "b" z-1 b) (p "ttp-rc1" "t" z-1 t)
              (p "ttp-rc1" "k" z-1 k) (prec z 0 z-1 0)
              (prec z-1 2 z-0 0)))))))
  (traces ((recv m) (send m))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))))
  (label 49)
  (unrealized (0 0))
  (preskeleton)
  (origs (m (1 0)) (k (1 0)))
  (comment "Not a skeleton"))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (deflistener m)
  (defstrand init1 1 (r r) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 0) (0 0)))
  (non-orig (privk "encr" t))
  (uniq-orig m k)
  (traces ((recv m) (send m))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))))
  (label 50)
  (parent 49)
  (unrealized (0 0))
  (origs (m (1 0)) (k (1 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (deflistener m)
  (defstrand init1 1 (r r) (m m) (a a) (b b) (t t) (k k))
  (deflistener k)
  (precedes ((1 0) (2 0)) ((2 1) (0 0)))
  (non-orig (privk "encr" t))
  (uniq-orig m k)
  (operation nonce-test (added-listener k) m (0 0) (enc m k))
  (traces ((recv m) (send m))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))) ((recv k) (send k)))
  (label 51)
  (parent 50)
  (unrealized (2 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (deflistener m)
  (deflistener k)
  (defstrand init1 3 (r r) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 1) (0 0)) ((2 2) (1 0)))
  (non-orig (privk "encr" t))
  (uniq-orig m k)
  (operation nonce-test (displaced 1 3 init1 3) k (2 0)
    (enc "keytag"
      (enc "h"
        (cat "h" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
  (traces ((recv m) (send m)) ((recv k) (send k))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (send (cat k r))))
  (label 52)
  (parent 51)
  (unrealized)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (deflistener m)
  (defstrand init1 1 (r r) (m m) (a a) (b b) (t t) (k k))
  (deflistener k)
  (defstrand ttp-rc1 3 (y (enc "h" (cat "h" (enc m k)))) (r r) (a a)
    (b b) (t t) (k k))
  (precedes ((1 0) (3 0)) ((2 1) (0 0)) ((3 2) (2 0)))
  (non-orig (privk "encr" t))
  (uniq-orig m k)
  (operation nonce-test (added-strand ttp-rc1 3) k (2 0)
    (enc "keytag"
      (enc "h"
        (cat "h" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
  (traces ((recv m) (send m))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))) ((recv k) (send k))
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))
         (enc "eortag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))
         (enc "rcrq"
           (cat a b t (enc "h" (cat "h" (enc m k)))
             (enc "h" (cat "h" k)))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))))
      (send
        (cat "sync-rc-req"
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b)))) (send (cat k r))))
  (label 53)
  (parent 51)
  (unrealized)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (deflistener m)
  (defstrand init1 3 (r r) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 2) (0 0)))
  (non-orig (privk "encr" t))
  (uniq-orig m k)
  (operation generalization deleted (1 0))
  (traces ((recv m) (send m))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (send (cat k r))))
  (label 54)
  (parent 52)
  (unrealized)
  (shape)
  (satisfies yes)
  (maps ((0 1) ((r r) (m m) (b b) (t t) (a a) (k k))))
  (origs (m (1 0)) (k (1 0))))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (deflistener m)
  (defstrand init1 1 (r r) (m m) (a a) (b b) (t t) (k k))
  (defstrand ttp-rc1 3 (y (enc "h" (cat "h" (enc m k)))) (r r) (a a)
    (b b) (t t) (k k))
  (precedes ((1 0) (2 0)) ((2 2) (0 0)))
  (non-orig (privk "encr" t))
  (uniq-orig m k)
  (operation generalization deleted (2 0))
  (traces ((recv m) (send m))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a)))))
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))
         (enc "eortag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))
         (enc "rcrq"
           (cat a b t (enc "h" (cat "h" (enc m k)))
             (enc "h" (cat "h" k)))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))))
      (send
        (cat "sync-rc-req"
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b)))) (send (cat k r))))
  (label 55)
  (parent 53)
  (unrealized)
  (shape)
  (satisfies yes)
  (maps ((0 1) ((r r) (m m) (b b) (t t) (a a) (k k))))
  (origs (m (1 0)) (k (1 0))))

(comment "Nothing left to do")

(defprotocol wang basic
  (defrole init1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (send (cat k r))))
  (defrole init2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init3
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole init4
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init5
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole resp1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (recv (cat k r))))
  (defrole resp2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b)))) (recv (cat k r))))
  (defrole resp3
    (vars (a b t name) (e1 e2 x mesg))
    (trace
      (recv
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e1 e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))
          (enc "rcrq" (cat a b t (enc "h" (cat "h" e1)) x) e2
            (privk "sign" b))))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" e1)) x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab1
    (vars (a b t name) (y x mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (send (cat "sync-abrq" (enc "abrq" a b t y x (privk "sign" a))))
      (send
        (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab2
    (vars (a b t name) (y x e mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (recv
        (cat "sync-abrq"
          (enc "eortag" (enc "h" (cat "h" a b t y x)) e
            (privk "sign" b))))
      (send
        (enc "eortag" (enc "h" (cat "h" a b t y x)) e
          (privk "sign" b)))))
  (defrole ttp-rc1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-rc-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)))) (send (cat k r))))
  (defrole ttp-rc2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-rc-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-cf1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-cf-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (enc (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)) (privk "sign" t)))))
  (defrole ttp-cf2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-cf-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2))
        (false))))
  (defrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1))))))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (deflistener k)
  (defstrand init1 1 (r r) (m m) (a a) (b b) (t t) (k k))
  (non-orig (privk "encr" t))
  (uniq-orig m k)
  (goals
    (forall ((r text) (m data) (b t a name) (k skey) (z z-0 strd))
      (implies
        (and (p "init1" z 1) (p "" z-0 2) (p "init1" "r" z r)
          (p "init1" "m" z m) (p "init1" "a" z a) (p "init1" "b" z b)
          (p "init1" "t" z t) (p "init1" "k" z k) (p "" "x" z-0 k)
          (non (privk "encr" t)) (uniq-at m z 0) (uniq-at k z 0))
        (or (and (p "init1" z 3) (prec z 2 z-0 0))
          (exists ((z-1 strd))
            (and (p "ttp-rc1" z-1 3)
              (p "ttp-rc1" "y" z-1 (enc "h" (cat "h" (enc m k))))
              (p "ttp-rc1" "r" z-1 r) (p "ttp-rc1" "a" z-1 a)
              (p "ttp-rc1" "b" z-1 b) (p "ttp-rc1" "t" z-1 t)
              (p "ttp-rc1" "k" z-1 k) (prec z 0 z-1 0)
              (prec z-1 2 z-0 0)))))))
  (traces ((recv k) (send k))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))))
  (label 56)
  (unrealized (0 0))
  (preskeleton)
  (origs (m (1 0)) (k (1 0)))
  (comment "Not a skeleton"))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (deflistener k)
  (defstrand init1 1 (r r) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 0) (0 0)))
  (non-orig (privk "encr" t))
  (uniq-orig m k)
  (traces ((recv k) (send k))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))))
  (label 57)
  (parent 56)
  (unrealized (0 0))
  (origs (m (1 0)) (k (1 0)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (deflistener k)
  (defstrand init1 3 (r r) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 2) (0 0)))
  (non-orig (privk "encr" t))
  (uniq-orig m k)
  (operation nonce-test (displaced 1 2 init1 3) k (0 0)
    (enc "keytag"
      (enc "h"
        (cat "h" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
  (traces ((recv k) (send k))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (send (cat k r))))
  (label 58)
  (parent 57)
  (unrealized)
  (shape)
  (satisfies yes)
  (maps ((0 1) ((r r) (m m) (b b) (t t) (a a) (k k))))
  (origs (m (1 0)) (k (1 0))))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (deflistener k)
  (defstrand init1 1 (r r) (m m) (a a) (b b) (t t) (k k))
  (defstrand ttp-rc1 3 (y (enc "h" (cat "h" (enc m k)))) (r r) (a a)
    (b b) (t t) (k k))
  (precedes ((1 0) (2 0)) ((2 2) (0 0)))
  (non-orig (privk "encr" t))
  (uniq-orig m k)
  (operation nonce-test (added-strand ttp-rc1 3) k (0 0)
    (enc "keytag"
      (enc "h"
        (cat "h" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
  (traces ((recv k) (send k))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a)))))
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))
         (enc "eortag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))
         (enc "rcrq"
           (cat a b t (enc "h" (cat "h" (enc m k)))
             (enc "h" (cat "h" k)))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))))
      (send
        (cat "sync-rc-req"
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b)))) (send (cat k r))))
  (label 59)
  (parent 57)
  (unrealized)
  (shape)
  (satisfies yes)
  (maps ((0 1) ((r r) (m m) (b b) (t t) (a a) (k k))))
  (origs (m (1 0)) (k (1 0))))

(comment "Nothing left to do")

(defprotocol wang basic
  (defrole init1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (send (cat k r))))
  (defrole init2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init3
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole init4
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init5
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole resp1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (recv (cat k r))))
  (defrole resp2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b)))) (recv (cat k r))))
  (defrole resp3
    (vars (a b t name) (e1 e2 x mesg))
    (trace
      (recv
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e1 e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))
          (enc "rcrq" (cat a b t (enc "h" (cat "h" e1)) x) e2
            (privk "sign" b))))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" e1)) x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab1
    (vars (a b t name) (y x mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (send (cat "sync-abrq" (enc "abrq" a b t y x (privk "sign" a))))
      (send
        (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab2
    (vars (a b t name) (y x e mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (recv
        (cat "sync-abrq"
          (enc "eortag" (enc "h" (cat "h" a b t y x)) e
            (privk "sign" b))))
      (send
        (enc "eortag" (enc "h" (cat "h" a b t y x)) e
          (privk "sign" b)))))
  (defrole ttp-rc1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-rc-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)))) (send (cat k r))))
  (defrole ttp-rc2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-rc-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-cf1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-cf-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (enc (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)) (privk "sign" t)))))
  (defrole ttp-cf2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-cf-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2))
        (false))))
  (defrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1))))))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (defstrand init1 3 (r r) (m m) (a a) (b b) (t t) (k k))
  (non-orig (privk "sign" b))
  (goals
    (forall ((r text) (m data) (b t a name) (k skey) (z strd))
      (implies
        (and (p "init1" z 3) (p "init1" "r" z r) (p "init1" "m" z m)
          (p "init1" "a" z a) (p "init1" "b" z b) (p "init1" "t" z t)
          (p "init1" "k" z k) (non (privk "sign" b)))
        (or
          (exists ((z-0 strd))
            (and (p "resp1" z-0 2) (p "resp1" "r" z-0 r)
              (p "resp1" "m" z-0 m) (p "resp1" "a" z-0 a)
              (p "resp1" "b" z-0 b) (p "resp1" "t" z-0 t)
              (p "resp1" "k" z-0 k) (prec z-0 1 z 1)))
          (exists ((z-0 strd))
            (and (p "resp3" z-0 2) (p "resp3" "e1" z-0 (enc m k))
              (p "resp3" "e2" z-0
                (enc "keytag"
                  (enc "h"
                    (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                      (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
              (p "resp3" "x" z-0 (enc "h" (cat "h" k)))
              (p "resp3" "a" z-0 a) (p "resp3" "b" z-0 b)
              (p "resp3" "t" z-0 t) (prec z-0 1 z 1)))))))
  (traces
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (send (cat k r))))
  (label 60)
  (unrealized (0 1))
  (origs)
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (defstrand init1 3 (r r) (m m) (a a) (b b) (t t) (k k))
  (defstrand resp1 2 (r r) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 1) (0 1)))
  (non-orig (privk "sign" b))
  (operation encryption-test (added-strand resp1 2)
    (enc "eortag"
      (enc "h"
        (cat "h" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k))))
      (enc "keytag"
        (enc "h"
          (cat "h" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))) k r (pubk "encr" t))
      (privk "sign" b)) (0 1))
  (traces
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (send (cat k r)))
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (label 61)
  (parent 60)
  (unrealized)
  (shape)
  (satisfies yes)
  (maps ((0) ((r r) (m m) (b b) (t t) (a a) (k k))))
  (origs))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (defstrand init1 3 (r r) (m m) (a a) (b b) (t t) (k k))
  (defstrand resp3 2 (e1 (enc m k))
    (e2
      (enc "keytag"
        (enc "h"
          (cat "h" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
    (x (enc "h" (cat "h" k))) (a a) (b b) (t t))
  (precedes ((1 1) (0 1)))
  (non-orig (privk "sign" b))
  (operation encryption-test (added-strand resp3 2)
    (enc "eortag"
      (enc "h"
        (cat "h" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k))))
      (enc "keytag"
        (enc "h"
          (cat "h" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))) k r (pubk "encr" t))
      (privk "sign" b)) (0 1))
  (traces
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (send (cat k r)))
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))))
  (label 62)
  (parent 60)
  (unrealized)
  (shape)
  (satisfies yes)
  (maps ((0) ((r r) (m m) (b b) (t t) (a a) (k k))))
  (origs))

(comment "Nothing left to do")

(defprotocol wang basic
  (defrole init1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (send (cat k r))))
  (defrole init2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init3
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole init4
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init5
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole resp1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (recv (cat k r))))
  (defrole resp2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b)))) (recv (cat k r))))
  (defrole resp3
    (vars (a b t name) (e1 e2 x mesg))
    (trace
      (recv
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e1 e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))
          (enc "rcrq" (cat a b t (enc "h" (cat "h" e1)) x) e2
            (privk "sign" b))))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" e1)) x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab1
    (vars (a b t name) (y x mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (send (cat "sync-abrq" (enc "abrq" a b t y x (privk "sign" a))))
      (send
        (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab2
    (vars (a b t name) (y x e mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (recv
        (cat "sync-abrq"
          (enc "eortag" (enc "h" (cat "h" a b t y x)) e
            (privk "sign" b))))
      (send
        (enc "eortag" (enc "h" (cat "h" a b t y x)) e
          (privk "sign" b)))))
  (defrole ttp-rc1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-rc-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)))) (send (cat k r))))
  (defrole ttp-rc2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-rc-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-cf1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-cf-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (enc (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)) (privk "sign" t)))))
  (defrole ttp-cf2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-cf-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2))
        (false))))
  (defrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1))))))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (defstrand init3 3 (r r) (m m) (a a) (b b) (t t) (k k))
  (non-orig (privk "sign" b))
  (goals
    (forall ((r text) (m data) (b t a name) (k skey) (z strd))
      (implies
        (and (p "init3" z 3) (p "init3" "r" z r) (p "init3" "m" z m)
          (p "init3" "a" z a) (p "init3" "b" z b) (p "init3" "t" z t)
          (p "init3" "k" z k) (non (privk "sign" b)))
        (or
          (exists ((z-0 strd))
            (and (p "resp1" z-0 2) (p "resp1" "r" z-0 r)
              (p "resp1" "m" z-0 m) (p "resp1" "a" z-0 a)
              (p "resp1" "b" z-0 b) (p "resp1" "t" z-0 t)
              (p "resp1" "k" z-0 k) (prec z-0 1 z 2)))
          (exists ((z-0 strd))
            (and (p "resp3" z-0 2) (p "resp3" "e1" z-0 (enc m k))
              (p "resp3" "e2" z-0
                (enc "keytag"
                  (enc "h"
                    (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                      (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
              (p "resp3" "x" z-0 (enc "h" (cat "h" k)))
              (p "resp3" "a" z-0 a) (p "resp3" "b" z-0 b)
              (p "resp3" "t" z-0 t) (prec z-0 1 z 2)))))))
  (traces
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (label 63)
  (unrealized (0 2))
  (origs)
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (defstrand init3 3 (r r) (m m) (a a) (b b) (t t) (k k))
  (defstrand resp1 2 (r r) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 1) (0 2)))
  (non-orig (privk "sign" b))
  (operation encryption-test (added-strand resp1 2)
    (enc "eortag"
      (enc "h"
        (cat "h" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k))))
      (enc "keytag"
        (enc "h"
          (cat "h" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))) k r (pubk "encr" t))
      (privk "sign" b)) (0 2))
  (traces
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))))
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (label 64)
  (parent 63)
  (unrealized)
  (shape)
  (satisfies yes)
  (maps ((0) ((r r) (m m) (b b) (t t) (a a) (k k))))
  (origs))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (defstrand init3 3 (r r) (m m) (a a) (b b) (t t) (k k))
  (defstrand resp3 2 (e1 (enc m k))
    (e2
      (enc "keytag"
        (enc "h"
          (cat "h" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
    (x (enc "h" (cat "h" k))) (a a) (b b) (t t))
  (precedes ((1 1) (0 2)))
  (non-orig (privk "sign" b))
  (operation encryption-test (added-strand resp3 2)
    (enc "eortag"
      (enc "h"
        (cat "h" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k))))
      (enc "keytag"
        (enc "h"
          (cat "h" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))) k r (pubk "encr" t))
      (privk "sign" b)) (0 2))
  (traces
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))))
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))))
  (label 65)
  (parent 63)
  (unrealized)
  (shape)
  (satisfies yes)
  (maps ((0) ((r r) (m m) (b b) (t t) (a a) (k k))))
  (origs))

(comment "Nothing left to do")

(defprotocol wang basic
  (defrole init1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (send (cat k r))))
  (defrole init2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init3
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole init4
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init5
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole resp1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (recv (cat k r))))
  (defrole resp2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b)))) (recv (cat k r))))
  (defrole resp3
    (vars (a b t name) (e1 e2 x mesg))
    (trace
      (recv
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e1 e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))
          (enc "rcrq" (cat a b t (enc "h" (cat "h" e1)) x) e2
            (privk "sign" b))))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" e1)) x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab1
    (vars (a b t name) (y x mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (send (cat "sync-abrq" (enc "abrq" a b t y x (privk "sign" a))))
      (send
        (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab2
    (vars (a b t name) (y x e mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (recv
        (cat "sync-abrq"
          (enc "eortag" (enc "h" (cat "h" a b t y x)) e
            (privk "sign" b))))
      (send
        (enc "eortag" (enc "h" (cat "h" a b t y x)) e
          (privk "sign" b)))))
  (defrole ttp-rc1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-rc-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)))) (send (cat k r))))
  (defrole ttp-rc2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-rc-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-cf1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-cf-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (enc (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)) (privk "sign" t)))))
  (defrole ttp-cf2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-cf-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2))
        (false))))
  (defrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1))))))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (defstrand init5 4 (r r) (m m) (a a) (b b) (t t) (k k))
  (non-orig (privk "sign" b))
  (goals
    (forall ((r text) (m data) (b t a name) (k skey) (z strd))
      (implies
        (and (p "init5" z 4) (p "init5" "r" z r) (p "init5" "m" z m)
          (p "init5" "a" z a) (p "init5" "b" z b) (p "init5" "t" z t)
          (p "init5" "k" z k) (non (privk "sign" b)))
        (or
          (exists ((z-0 strd))
            (and (p "resp1" z-0 2) (p "resp1" "r" z-0 r)
              (p "resp1" "m" z-0 m) (p "resp1" "a" z-0 a)
              (p "resp1" "b" z-0 b) (p "resp1" "t" z-0 t)
              (p "resp1" "k" z-0 k) (prec z-0 1 z 1)))
          (exists ((z-0 strd))
            (and (p "resp3" z-0 2) (p "resp3" "e1" z-0 (enc m k))
              (p "resp3" "e2" z-0
                (enc "keytag"
                  (enc "h"
                    (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                      (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
              (p "resp3" "x" z-0 (enc "h" (cat "h" k)))
              (p "resp3" "a" z-0 a) (p "resp3" "b" z-0 b)
              (p "resp3" "t" z-0 t) (prec z-0 1 z 1)))))))
  (traces
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (label 66)
  (unrealized (0 1) (0 3))
  (origs)
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (defstrand init5 4 (r r) (m m) (a a) (b b) (t t) (k k))
  (defstrand resp1 2 (r r) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 1) (0 1)))
  (non-orig (privk "sign" b))
  (operation encryption-test (added-strand resp1 2)
    (enc "eortag"
      (enc "h"
        (cat "h" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k))))
      (enc "keytag"
        (enc "h"
          (cat "h" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))) k r (pubk "encr" t))
      (privk "sign" b)) (0 1))
  (traces
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))))
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (label 67)
  (parent 66)
  (unrealized)
  (shape)
  (satisfies yes)
  (maps ((0) ((r r) (m m) (b b) (t t) (a a) (k k))))
  (origs))

(defskeleton wang
  (vars (r text) (m data) (b t a name) (k skey))
  (defstrand init5 4 (r r) (m m) (a a) (b b) (t t) (k k))
  (defstrand resp3 2 (e1 (enc m k))
    (e2
      (enc "keytag"
        (enc "h"
          (cat "h" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
    (x (enc "h" (cat "h" k))) (a a) (b b) (t t))
  (precedes ((1 1) (0 1)))
  (non-orig (privk "sign" b))
  (operation encryption-test (added-strand resp3 2)
    (enc "eortag"
      (enc "h"
        (cat "h" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k))))
      (enc "keytag"
        (enc "h"
          (cat "h" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))) k r (pubk "encr" t))
      (privk "sign" b)) (0 1))
  (traces
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))))
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))))
  (label 68)
  (parent 66)
  (unrealized)
  (shape)
  (satisfies yes)
  (maps ((0) ((r r) (m m) (b b) (t t) (a a) (k k))))
  (origs))

(comment "Nothing left to do")

(defprotocol wang basic
  (defrole init1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (send (cat k r))))
  (defrole init2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init3
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole init4
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init5
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole resp1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (recv (cat k r))))
  (defrole resp2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b)))) (recv (cat k r))))
  (defrole resp3
    (vars (a b t name) (e1 e2 x mesg))
    (trace
      (recv
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e1 e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))
          (enc "rcrq" (cat a b t (enc "h" (cat "h" e1)) x) e2
            (privk "sign" b))))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" e1)) x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab1
    (vars (a b t name) (y x mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (send (cat "sync-abrq" (enc "abrq" a b t y x (privk "sign" a))))
      (send
        (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab2
    (vars (a b t name) (y x e mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (recv
        (cat "sync-abrq"
          (enc "eortag" (enc "h" (cat "h" a b t y x)) e
            (privk "sign" b))))
      (send
        (enc "eortag" (enc "h" (cat "h" a b t y x)) e
          (privk "sign" b)))))
  (defrole ttp-rc1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-rc-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)))) (send (cat k r))))
  (defrole ttp-rc2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-rc-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-cf1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-cf-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (enc (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)) (privk "sign" t)))))
  (defrole ttp-cf2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-cf-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2))
        (false))))
  (defrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1))))))

(defskeleton wang
  (vars (r text) (m data) (a t b name) (k skey))
  (defstrand resp1 3 (r r) (m m) (a a) (b b) (t t) (k k))
  (non-orig (privk "sign" a))
  (goals
    (forall ((r text) (m data) (a t b name) (k skey) (z strd))
      (implies
        (and (p "resp1" z 3) (p "resp1" "r" z r) (p "resp1" "m" z m)
          (p "resp1" "a" z a) (p "resp1" "b" z b) (p "resp1" "t" z t)
          (p "resp1" "k" z k) (non (privk "sign" a)))
        (exists ((z-0 strd))
          (and (p "init5" z-0 1) (p "init5" "r" z-0 r)
            (p "init5" "m" z-0 m) (p "init5" "a" z-0 a)
            (p "init5" "b" z-0 b) (p "init5" "t" z-0 t)
            (p "init5" "k" z-0 k) (prec z-0 0 z 0))))))
  (traces
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (recv (cat k r))))
  (label 69)
  (unrealized (0 0))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton wang
  (vars (r text) (m data) (a t b name) (k skey))
  (defstrand resp1 3 (r r) (m m) (a a) (b b) (t t) (k k))
  (defstrand init5 1 (r r) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 0) (0 0)))
  (non-orig (privk "sign" a))
  (operation encryption-test (added-strand init5 1)
    (enc "eootag"
      (enc "h"
        (cat "h" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k))))
      (enc "keytag"
        (enc "h"
          (cat "h" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))) k r (pubk "encr" t))
      (privk "sign" a)) (0 0))
  (traces
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (recv (cat k r)))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))))
  (label 70)
  (parent 69)
  (unrealized)
  (shape)
  (satisfies yes)
  (maps ((0) ((r r) (m m) (a a) (t t) (b b) (k k))))
  (origs))

(comment "Nothing left to do")

(defprotocol wang basic
  (defrole init1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (send (cat k r))))
  (defrole init2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init3
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole init4
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init5
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole resp1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (recv (cat k r))))
  (defrole resp2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b)))) (recv (cat k r))))
  (defrole resp3
    (vars (a b t name) (e1 e2 x mesg))
    (trace
      (recv
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e1 e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))
          (enc "rcrq" (cat a b t (enc "h" (cat "h" e1)) x) e2
            (privk "sign" b))))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" e1)) x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab1
    (vars (a b t name) (y x mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (send (cat "sync-abrq" (enc "abrq" a b t y x (privk "sign" a))))
      (send
        (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab2
    (vars (a b t name) (y x e mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (recv
        (cat "sync-abrq"
          (enc "eortag" (enc "h" (cat "h" a b t y x)) e
            (privk "sign" b))))
      (send
        (enc "eortag" (enc "h" (cat "h" a b t y x)) e
          (privk "sign" b)))))
  (defrole ttp-rc1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-rc-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)))) (send (cat k r))))
  (defrole ttp-rc2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-rc-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-cf1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-cf-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (enc (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)) (privk "sign" t)))))
  (defrole ttp-cf2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-cf-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2))
        (false))))
  (defrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1))))))

(defskeleton wang
  (vars (r text) (m data) (a t b name) (k skey))
  (defstrand resp2 4 (r r) (m m) (a a) (b b) (t t) (k k))
  (non-orig (privk "sign" a))
  (goals
    (forall ((r text) (m data) (a t b name) (k skey) (z strd))
      (implies
        (and (p "resp2" z 4) (p "resp2" "r" z r) (p "resp2" "m" z m)
          (p "resp2" "a" z a) (p "resp2" "b" z b) (p "resp2" "t" z t)
          (p "resp2" "k" z k) (non (privk "sign" a)))
        (exists ((z-0 strd))
          (and (p "init5" z-0 1) (p "init5" "r" z-0 r)
            (p "init5" "m" z-0 m) (p "init5" "a" z-0 a)
            (p "init5" "b" z-0 b) (p "init5" "t" z-0 t)
            (p "init5" "k" z-0 k) (prec z-0 0 z 0))))))
  (traces
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b)))) (recv (cat k r))))
  (label 71)
  (unrealized (0 0))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton wang
  (vars (r text) (m data) (a t b name) (k skey))
  (defstrand resp2 4 (r r) (m m) (a a) (b b) (t t) (k k))
  (defstrand init5 1 (r r) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 0) (0 0)))
  (non-orig (privk "sign" a))
  (operation encryption-test (added-strand init5 1)
    (enc "eootag"
      (enc "h"
        (cat "h" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k))))
      (enc "keytag"
        (enc "h"
          (cat "h" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))) k r (pubk "encr" t))
      (privk "sign" a)) (0 0))
  (traces
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b)))) (recv (cat k r)))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))))
  (label 72)
  (parent 71)
  (unrealized)
  (shape)
  (satisfies yes)
  (maps ((0) ((r r) (m m) (a a) (t t) (b b) (k k))))
  (origs))

(comment "Nothing left to do")

(defprotocol wang basic
  (defrole init1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (send (cat k r))))
  (defrole init2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init3
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole init4
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init5
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole resp1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (recv (cat k r))))
  (defrole resp2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b)))) (recv (cat k r))))
  (defrole resp3
    (vars (a b t name) (e1 e2 x mesg))
    (trace
      (recv
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e1 e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))
          (enc "rcrq" (cat a b t (enc "h" (cat "h" e1)) x) e2
            (privk "sign" b))))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" e1)) x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab1
    (vars (a b t name) (y x mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (send (cat "sync-abrq" (enc "abrq" a b t y x (privk "sign" a))))
      (send
        (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab2
    (vars (a b t name) (y x e mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (recv
        (cat "sync-abrq"
          (enc "eortag" (enc "h" (cat "h" a b t y x)) e
            (privk "sign" b))))
      (send
        (enc "eortag" (enc "h" (cat "h" a b t y x)) e
          (privk "sign" b)))))
  (defrole ttp-rc1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-rc-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)))) (send (cat k r))))
  (defrole ttp-rc2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-rc-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-cf1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-cf-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (enc (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)) (privk "sign" t)))))
  (defrole ttp-cf2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-cf-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2))
        (false))))
  (defrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1))))))

(defskeleton wang
  (vars (e1 e2 x mesg) (a t b name))
  (defstrand resp3 4 (e1 e1) (e2 e2) (x x) (a a) (b b) (t t))
  (non-orig (privk "sign" a))
  (goals
    (forall ((e1 e2 x mesg) (a t b name) (z strd))
      (implies
        (and (p "resp3" z 4) (p "resp3" "e1" z e1) (p "resp3" "e2" z e2)
          (p "resp3" "x" z x) (p "resp3" "a" z a) (p "resp3" "b" z b)
          (p "resp3" "t" z t) (non (privk "sign" a)))
        (or
          (exists ((r text) (m data) (k skey) (z-0 strd))
            (and (= e1 (enc m k))
              (= e2
                (enc "keytag"
                  (enc "h"
                    (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                      (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
              (= x (enc "h" (cat "h" k))) (p "init3" z-0 2)
              (p "resp3" "e1" z (enc m k))
              (p "resp3" "e2" z
                (enc "keytag"
                  (enc "h"
                    (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                      (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
              (p "resp3" "x" z (enc "h" (cat "h" k)))
              (p "init3" "r" z-0 r) (p "init3" "m" z-0 m)
              (p "init3" "a" z-0 a) (p "init3" "b" z-0 b)
              (p "init3" "t" z-0 t) (p "init3" "k" z-0 k)
              (prec z-0 0 z 0) (prec z-0 1 z 3)))
          (exists ((r r-0 text) (m data) (k skey) (z-0 z-1 strd))
            (and (= e1 (enc m k))
              (= e2
                (enc "keytag"
                  (enc "h"
                    (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                      (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
              (= x (enc "h" (cat "h" k))) (p "init5" z-0 1)
              (p "init3" z-1 2) (p "resp3" "e1" z (enc m k))
              (p "resp3" "e2" z
                (enc "keytag"
                  (enc "h"
                    (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                      (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
              (p "resp3" "x" z (enc "h" (cat "h" k)))
              (p "init5" "r" z-0 r) (p "init5" "m" z-0 m)
              (p "init5" "a" z-0 a) (p "init5" "b" z-0 b)
              (p "init5" "t" z-0 t) (p "init5" "k" z-0 k)
              (p "init3" "r" z-1 r-0) (p "init3" "m" z-1 m)
              (p "init3" "a" z-1 a) (p "init3" "b" z-1 b)
              (p "init3" "t" z-1 t) (p "init3" "k" z-1 k)
              (prec z-0 0 z 0) (prec z-1 1 z 3)))
          (exists ((r text) (m data) (k skey) (z-0 strd))
            (and (= e1 (enc m k))
              (= e2
                (enc "keytag"
                  (enc "h"
                    (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                      (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
              (= x (enc "h" (cat "h" k))) (p "init5" z-0 3)
              (p "resp3" "e1" z (enc m k))
              (p "resp3" "e2" z
                (enc "keytag"
                  (enc "h"
                    (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                      (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
              (p "resp3" "x" z (enc "h" (cat "h" k)))
              (p "init5" "r" z-0 r) (p "init5" "m" z-0 m)
              (p "init5" "a" z-0 a) (p "init5" "b" z-0 b)
              (p "init5" "t" z-0 t) (p "init5" "k" z-0 k)
              (prec z-0 0 z 0) (prec z-0 2 z 3)))
          (exists ((r r-0 text) (m data) (k skey) (z-0 z-1 strd))
            (and (= e1 (enc m k))
              (= e2
                (enc "keytag"
                  (enc "h"
                    (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                      (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
              (= x (enc "h" (cat "h" k))) (p "init5" z-0 1)
              (p "init5" z-1 3) (p "resp3" "e1" z (enc m k))
              (p "resp3" "e2" z
                (enc "keytag"
                  (enc "h"
                    (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                      (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
              (p "resp3" "x" z (enc "h" (cat "h" k)))
              (p "init5" "r" z-0 r) (p "init5" "m" z-0 m)
              (p "init5" "a" z-0 a) (p "init5" "b" z-0 b)
              (p "init5" "t" z-0 t) (p "init5" "k" z-0 k)
              (p "init5" "r" z-1 r-0) (p "init5" "m" z-1 m)
              (p "init5" "a" z-1 a) (p "init5" "b" z-1 b)
              (p "init5" "t" z-1 t) (p "init5" "k" z-1 k)
              (prec z-0 0 z 0) (prec z-1 2 z 3)))))))
  (traces
    ((recv
       (cat (cat a b t (enc "h" (cat "h" e1)) x) e1 e2
         (enc "eootag"
           (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
           (privk "sign" a))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))
          (enc "rcrq" (cat a b t (enc "h" (cat "h" e1)) x) e2
            (privk "sign" b))))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" e1)) x (privk "sign" a))
          (privk "sign" t)))))
  (label 73)
  (unrealized (0 0) (0 3))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton wang
  (vars (r text) (m data) (a t b name) (k skey))
  (defstrand resp3 4 (e1 (enc m k))
    (e2
      (enc "keytag"
        (enc "h"
          (cat "h" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
    (x (enc "h" (cat "h" k))) (a a) (b b) (t t))
  (defstrand init5 1 (r r) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 0) (0 0)))
  (non-orig (privk "sign" a))
  (operation encryption-test (added-strand init5 1)
    (enc "eootag"
      (enc "h"
        (cat "h" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k))))
      (enc "keytag"
        (enc "h"
          (cat "h" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))) k r (pubk "encr" t))
      (privk "sign" a)) (0 0))
  (traces
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))))
  (label 74)
  (parent 73)
  (unrealized (0 3))
  (comment "4 in cohort - 4 not yet seen"))

(defskeleton wang
  (vars (r r-0 text) (m data) (a t b name) (k skey))
  (defstrand resp3 4 (e1 (enc m k))
    (e2
      (enc "keytag"
        (enc "h"
          (cat "h" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
    (x (enc "h" (cat "h" k))) (a a) (b b) (t t))
  (defstrand init5 1 (r r) (m m) (a a) (b b) (t t) (k k))
  (defstrand init3 2 (r r-0) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 0) (0 0)) ((2 1) (0 3)))
  (non-orig (privk "sign" a))
  (operation encryption-test (added-strand init3 2)
    (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
      (enc "h" (cat "h" k)) (privk "sign" a)) (0 3))
  (traces
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a)))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r-0 (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r-0 (pubk "encr" t))
           (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))))
  (label 75)
  (parent 74)
  (unrealized)
  (shape)
  (satisfies yes)
  (maps
    ((0)
      ((e1 (enc m k))
        (e2
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
        (x (enc "h" (cat "h" k))) (a a) (t t) (b b))))
  (origs))

(defskeleton wang
  (vars (r text) (m data) (a t b name) (k skey))
  (defstrand resp3 4 (e1 (enc m k))
    (e2
      (enc "keytag"
        (enc "h"
          (cat "h" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
    (x (enc "h" (cat "h" k))) (a a) (b b) (t t))
  (defstrand init3 2 (r r) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 0) (0 0)) ((1 1) (0 3)))
  (non-orig (privk "sign" a))
  (operation encryption-test (displaced 1 2 init3 2)
    (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
      (enc "h" (cat "h" k)) (privk "sign" a)) (0 3))
  (traces
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))))
  (label 76)
  (parent 74)
  (unrealized)
  (shape)
  (satisfies yes)
  (maps
    ((0)
      ((e1 (enc m k))
        (e2
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
        (x (enc "h" (cat "h" k))) (a a) (t t) (b b))))
  (origs))

(defskeleton wang
  (vars (r text) (m data) (a t b name) (k skey))
  (defstrand resp3 4 (e1 (enc m k))
    (e2
      (enc "keytag"
        (enc "h"
          (cat "h" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
    (x (enc "h" (cat "h" k))) (a a) (b b) (t t))
  (defstrand init5 3 (r r) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 0) (0 0)) ((1 2) (0 3)))
  (non-orig (privk "sign" a))
  (operation encryption-test (displaced 1 2 init5 3)
    (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
      (enc "h" (cat "h" k)) (privk "sign" a)) (0 3))
  (traces
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))))
  (label 77)
  (parent 74)
  (unrealized)
  (shape)
  (satisfies yes)
  (maps
    ((0)
      ((e1 (enc m k))
        (e2
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
        (x (enc "h" (cat "h" k))) (a a) (t t) (b b))))
  (origs))

(defskeleton wang
  (vars (r r-0 text) (m data) (a t b name) (k skey))
  (defstrand resp3 4 (e1 (enc m k))
    (e2
      (enc "keytag"
        (enc "h"
          (cat "h" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
    (x (enc "h" (cat "h" k))) (a a) (b b) (t t))
  (defstrand init5 1 (r r) (m m) (a a) (b b) (t t) (k k))
  (defstrand init5 3 (r r-0) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 0) (0 0)) ((2 2) (0 3)))
  (non-orig (privk "sign" a))
  (operation encryption-test (added-strand init5 3)
    (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
      (enc "h" (cat "h" k)) (privk "sign" a)) (0 3))
  (traces
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a)))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r-0 (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r-0 (pubk "encr" t))
           (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r-0 (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))))
  (label 78)
  (parent 74)
  (unrealized)
  (shape)
  (satisfies yes)
  (maps
    ((0)
      ((e1 (enc m k))
        (e2
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t)))
        (x (enc "h" (cat "h" k))) (a a) (t t) (b b))))
  (origs))

(comment "Nothing left to do")

(defprotocol wang basic
  (defrole init1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (send (cat k r))))
  (defrole init2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init3
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole init4
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init5
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole resp1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (recv (cat k r))))
  (defrole resp2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b)))) (recv (cat k r))))
  (defrole resp3
    (vars (a b t name) (e1 e2 x mesg))
    (trace
      (recv
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e1 e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))
          (enc "rcrq" (cat a b t (enc "h" (cat "h" e1)) x) e2
            (privk "sign" b))))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" e1)) x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab1
    (vars (a b t name) (y x mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (send (cat "sync-abrq" (enc "abrq" a b t y x (privk "sign" a))))
      (send
        (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab2
    (vars (a b t name) (y x e mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (recv
        (cat "sync-abrq"
          (enc "eortag" (enc "h" (cat "h" a b t y x)) e
            (privk "sign" b))))
      (send
        (enc "eortag" (enc "h" (cat "h" a b t y x)) e
          (privk "sign" b)))))
  (defrole ttp-rc1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-rc-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)))) (send (cat k r))))
  (defrole ttp-rc2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-rc-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-cf1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-cf-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (enc (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)) (privk "sign" t)))))
  (defrole ttp-cf2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-cf-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2))
        (false))))
  (defrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1))))))

(defskeleton wang
  (vars (y x mesg) (a b t name))
  (deflistener
    (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
      (privk "sign" t)))
  (non-orig (privk "sign" t))
  (goals
    (forall ((y x mesg) (a b t name) (z strd))
      (implies
        (and (p "" z 2)
          (p "" "x" z
            (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
              (privk "sign" t))) (non (privk "sign" t)))
        (or
          (exists ((z-0 strd))
            (and (p "ttp-ab1" z-0 3) (p "ttp-ab1" "y" z-0 y)
              (p "ttp-ab1" "x" z-0 x) (p "ttp-ab1" "a" z-0 a)
              (p "ttp-ab1" "b" z-0 b) (p "ttp-ab1" "t" z-0 t)
              (prec z-0 2 z 0)))
          (exists ((r text) (k skey) (z-0 strd))
            (and (= x (enc "h" (cat "h" k))) (p "ttp-rc2" z-0 3)
              (p "" "x" z
                (enc "abcf"
                  (enc "abrq" a b t y (enc "h" (cat "h" k))
                    (privk "sign" a)) (privk "sign" t)))
              (p "ttp-rc2" "y" z-0 y) (p "ttp-rc2" "r" z-0 r)
              (p "ttp-rc2" "a" z-0 a) (p "ttp-rc2" "b" z-0 b)
              (p "ttp-rc2" "t" z-0 t) (p "ttp-rc2" "k" z-0 k)
              (prec z-0 2 z 0)))
          (exists ((r text) (k skey) (z-0 strd))
            (and (= x (enc "h" (cat "h" k))) (p "ttp-cf2" z-0 3)
              (p "" "x" z
                (enc "abcf"
                  (enc "abrq" a b t y (enc "h" (cat "h" k))
                    (privk "sign" a)) (privk "sign" t)))
              (p "ttp-cf2" "y" z-0 y) (p "ttp-cf2" "r" z-0 r)
              (p "ttp-cf2" "a" z-0 a) (p "ttp-cf2" "b" z-0 b)
              (p "ttp-cf2" "t" z-0 t) (p "ttp-cf2" "k" z-0 k)
              (prec z-0 2 z 0)))))))
  (traces
    ((recv
       (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
         (privk "sign" t)))
      (send
        (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
          (privk "sign" t)))))
  (label 79)
  (unrealized (0 0))
  (origs)
  (comment "3 in cohort - 3 not yet seen"))

(defskeleton wang
  (vars (y x mesg) (a b t name))
  (deflistener
    (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
      (privk "sign" t)))
  (defstrand ttp-ab1 3 (y y) (x x) (a a) (b b) (t t))
  (precedes ((1 2) (0 0)))
  (non-orig (privk "sign" t))
  (operation encryption-test (added-strand ttp-ab1 3)
    (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
      (privk "sign" t)) (0 0))
  (traces
    ((recv
       (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
         (privk "sign" t)))
      (send
        (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
          (privk "sign" t))))
    ((recv (enc "abrq" a b t y x (privk "sign" a)))
      (send (cat "sync-abrq" (enc "abrq" a b t y x (privk "sign" a))))
      (send
        (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
          (privk "sign" t)))))
  (label 80)
  (parent 79)
  (unrealized)
  (shape)
  (satisfies yes)
  (maps ((0) ((y y) (x x) (a a) (b b) (t t))))
  (origs))

(defskeleton wang
  (vars (y mesg) (r text) (a b t name) (k skey))
  (deflistener
    (enc "abcf"
      (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
      (privk "sign" t)))
  (defstrand ttp-rc2 3 (y y) (r r) (a a) (b b) (t t) (k k))
  (precedes ((1 2) (0 0)))
  (non-orig (privk "sign" t))
  (operation encryption-test (added-strand ttp-rc2 3)
    (enc "abcf"
      (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
      (privk "sign" t)) (0 0))
  (traces
    ((recv
       (enc "abcf"
         (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
         (privk "sign" t)))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t))))
    ((recv
       (cat (cat a b t y (enc "h" (cat "h" k)))
         (enc "keytag" (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
           k r (pubk "encr" t))
         (enc "eootag" (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
             (pubk "encr" t)) (privk "sign" a))
         (enc "eortag" (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
             (pubk "encr" t)) (privk "sign" b))
         (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
           (enc "keytag"
             (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
             (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-rc-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (label 81)
  (parent 79)
  (unrealized)
  (shape)
  (satisfies yes)
  (maps ((0) ((y y) (x (enc "h" (cat "h" k))) (a a) (b b) (t t))))
  (origs))

(defskeleton wang
  (vars (y mesg) (r text) (a b t name) (k skey))
  (deflistener
    (enc "abcf"
      (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
      (privk "sign" t)))
  (defstrand ttp-cf2 3 (y y) (r r) (a a) (b b) (t t) (k k))
  (precedes ((1 2) (0 0)))
  (non-orig (privk "sign" t))
  (operation encryption-test (added-strand ttp-cf2 3)
    (enc "abcf"
      (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
      (privk "sign" t)) (0 0))
  (traces
    ((recv
       (enc "abcf"
         (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
         (privk "sign" t)))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t))))
    ((recv
       (cat (cat a b t y (enc "h" (cat "h" k)))
         (enc "keytag" (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
           k r (pubk "encr" t))
         (enc "eootag" (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
             (pubk "encr" t)) (privk "sign" a))
         (enc "eortag" (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
             (pubk "encr" t)) (privk "sign" b))
         (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
           (enc "keytag"
             (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
             (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-cf-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (label 82)
  (parent 79)
  (unrealized)
  (shape)
  (satisfies yes)
  (maps ((0) ((y y) (x (enc "h" (cat "h" k))) (a a) (b b) (t t))))
  (origs))

(comment "Nothing left to do")

(defprotocol wang basic
  (defrole init1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (send (cat k r))))
  (defrole init2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init3
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole init4
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init5
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole resp1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (recv (cat k r))))
  (defrole resp2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b)))) (recv (cat k r))))
  (defrole resp3
    (vars (a b t name) (e1 e2 x mesg))
    (trace
      (recv
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e1 e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))
          (enc "rcrq" (cat a b t (enc "h" (cat "h" e1)) x) e2
            (privk "sign" b))))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" e1)) x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab1
    (vars (a b t name) (y x mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (send (cat "sync-abrq" (enc "abrq" a b t y x (privk "sign" a))))
      (send
        (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab2
    (vars (a b t name) (y x e mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (recv
        (cat "sync-abrq"
          (enc "eortag" (enc "h" (cat "h" a b t y x)) e
            (privk "sign" b))))
      (send
        (enc "eortag" (enc "h" (cat "h" a b t y x)) e
          (privk "sign" b)))))
  (defrole ttp-rc1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-rc-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)))) (send (cat k r))))
  (defrole ttp-rc2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-rc-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-cf1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-cf-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (enc (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)) (privk "sign" t)))))
  (defrole ttp-cf2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-cf-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2))
        (false))))
  (defrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1))))))

(defskeleton wang
  (vars (y x mesg) (a b t name))
  (defstrand ttp-ab1 3 (y y) (x x) (a a) (b b) (t t))
  (non-orig (privk "encr" t) (privk "sign" a))
  (goals
    (forall ((y x mesg) (a b t name) (z strd))
      (implies
        (and (p "ttp-ab1" z 3) (p "ttp-ab1" "y" z y)
          (p "ttp-ab1" "x" z x) (p "ttp-ab1" "a" z a)
          (p "ttp-ab1" "b" z b) (p "ttp-ab1" "t" z t)
          (non (privk "encr" t)) (non (privk "sign" a)))
        (or
          (exists ((r text) (m data) (k skey) (z-0 strd))
            (and (= y (enc "h" (cat "h" (enc m k))))
              (= x (enc "h" (cat "h" k))) (p "init3" z-0 2)
              (p "ttp-ab1" "y" z (enc "h" (cat "h" (enc m k))))
              (p "ttp-ab1" "x" z (enc "h" (cat "h" k)))
              (p "init3" "r" z-0 r) (p "init3" "m" z-0 m)
              (p "init3" "a" z-0 a) (p "init3" "b" z-0 b)
              (p "init3" "t" z-0 t) (p "init3" "k" z-0 k)
              (prec z-0 1 z 0)))
          (exists ((r text) (m data) (k skey) (z-0 strd))
            (and (= y (enc "h" (cat "h" (enc m k))))
              (= x (enc "h" (cat "h" k))) (p "init5" z-0 3)
              (p "ttp-ab1" "y" z (enc "h" (cat "h" (enc m k))))
              (p "ttp-ab1" "x" z (enc "h" (cat "h" k)))
              (p "init5" "r" z-0 r) (p "init5" "m" z-0 m)
              (p "init5" "a" z-0 a) (p "init5" "b" z-0 b)
              (p "init5" "t" z-0 t) (p "init5" "k" z-0 k)
              (prec z-0 2 z 0)))))))
  (traces
    ((recv (enc "abrq" a b t y x (privk "sign" a)))
      (send (cat "sync-abrq" (enc "abrq" a b t y x (privk "sign" a))))
      (send
        (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
          (privk "sign" t)))))
  (label 83)
  (unrealized (0 0))
  (origs)
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton wang
  (vars (r text) (m data) (a b t name) (k skey))
  (defstrand ttp-ab1 3 (y (enc "h" (cat "h" (enc m k))))
    (x (enc "h" (cat "h" k))) (a a) (b b) (t t))
  (defstrand init3 2 (r r) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 1) (0 0)))
  (non-orig (privk "encr" t) (privk "sign" a))
  (operation encryption-test (added-strand init3 2)
    (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
      (enc "h" (cat "h" k)) (privk "sign" a)) (0 0))
  (traces
    ((recv
       (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
         (enc "h" (cat "h" k)) (privk "sign" a)))
      (send
        (cat "sync-abrq"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))))
  (label 84)
  (parent 83)
  (unrealized)
  (shape)
  (satisfies yes)
  (maps
    ((0)
      ((y (enc "h" (cat "h" (enc m k)))) (x (enc "h" (cat "h" k))) (a a)
        (b b) (t t))))
  (origs))

(defskeleton wang
  (vars (r text) (m data) (a b t name) (k skey))
  (defstrand ttp-ab1 3 (y (enc "h" (cat "h" (enc m k))))
    (x (enc "h" (cat "h" k))) (a a) (b b) (t t))
  (defstrand init5 3 (r r) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 2) (0 0)))
  (non-orig (privk "encr" t) (privk "sign" a))
  (operation encryption-test (added-strand init5 3)
    (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
      (enc "h" (cat "h" k)) (privk "sign" a)) (0 0))
  (traces
    ((recv
       (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
         (enc "h" (cat "h" k)) (privk "sign" a)))
      (send
        (cat "sync-abrq"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))))
  (label 85)
  (parent 83)
  (unrealized)
  (shape)
  (satisfies yes)
  (maps
    ((0)
      ((y (enc "h" (cat "h" (enc m k)))) (x (enc "h" (cat "h" k))) (a a)
        (b b) (t t))))
  (origs))

(comment "Nothing left to do")

(defprotocol wang basic
  (defrole init1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (send (cat k r))))
  (defrole init2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init3
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole init4
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t)))))
  (defrole init5
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))))
  (defrole resp1
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b))) (recv (cat k r))))
  (defrole resp2
    (vars (a b t name) (m data) (r text) (k skey))
    (trace
      (recv
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k))) (enc m k)
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))))
      (send
        (cat
          (cat a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (enc "eootag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" a))
          (enc "eortag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b))
          (enc "rcrq"
            (cat a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h"
                (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                  (enc "h" (cat "h" k)))) k r (pubk "encr" t))
            (privk "sign" b)))) (recv (cat k r))))
  (defrole resp3
    (vars (a b t name) (e1 e2 x mesg))
    (trace
      (recv
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e1 e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))))
      (send
        (cat (cat a b t (enc "h" (cat "h" e1)) x) e2
          (enc "eootag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t (enc "h" (cat "h" e1)) x)) e2
            (privk "sign" b))
          (enc "rcrq" (cat a b t (enc "h" (cat "h" e1)) x) e2
            (privk "sign" b))))
      (recv
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" e1)) x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab1
    (vars (a b t name) (y x mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (send (cat "sync-abrq" (enc "abrq" a b t y x (privk "sign" a))))
      (send
        (enc "abcf" (enc "abrq" a b t y x (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-ab2
    (vars (a b t name) (y x e mesg))
    (trace (recv (enc "abrq" a b t y x (privk "sign" a)))
      (recv
        (cat "sync-abrq"
          (enc "eortag" (enc "h" (cat "h" a b t y x)) e
            (privk "sign" b))))
      (send
        (enc "eortag" (enc "h" (cat "h" a b t y x)) e
          (privk "sign" b)))))
  (defrole ttp-rc1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-rc-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)))) (send (cat k r))))
  (defrole ttp-rc2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-rc-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrole ttp-cf1
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (cat "sync-cf-req" (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (send
        (enc (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b)) (privk "sign" t)))))
  (defrole ttp-cf2
    (vars (a b t name) (r text) (k skey) (y mesg))
    (trace
      (recv
        (cat (cat a b t y (enc "h" (cat "h" k)))
          (enc "keytag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
            (pubk "encr" t))
          (enc "eootag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" a))
          (enc "eortag"
            (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))
          (enc "cfrq" (cat a b t y (enc "h" (cat "h" k)))
            (enc "keytag"
              (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
              (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-cf-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (defrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2))
        (false))))
  (defrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1))))))

(defskeleton wang
  (vars (y mesg) (r text) (a b t name) (k skey))
  (defstrand ttp-rc2 3 (y y) (r r) (a a) (b b) (t t) (k k))
  (non-orig (privk "encr" t) (privk "sign" a))
  (goals
    (forall ((y mesg) (r text) (a b t name) (k skey) (z strd))
      (implies
        (and (p "ttp-rc2" z 3) (p "ttp-rc2" "y" z y)
          (p "ttp-rc2" "r" z r) (p "ttp-rc2" "a" z a)
          (p "ttp-rc2" "b" z b) (p "ttp-rc2" "t" z t)
          (p "ttp-rc2" "k" z k) (non (privk "encr" t))
          (non (privk "sign" a)))
        (or
          (exists ((m data) (z-0 strd))
            (and (= y (enc "h" (cat "h" (enc m k)))) (p "init3" z-0 2)
              (p "ttp-rc2" "y" z (enc "h" (cat "h" (enc m k))))
              (p "init3" "r" z-0 r) (p "init3" "m" z-0 m)
              (p "init3" "a" z-0 a) (p "init3" "b" z-0 b)
              (p "init3" "t" z-0 t) (p "init3" "k" z-0 k)
              (prec z-0 0 z 0) (prec z-0 1 z 1)))
          (exists ((r-0 text) (m data) (z-0 z-1 strd))
            (and (= y (enc "h" (cat "h" (enc m k)))) (p "init5" z-0 1)
              (p "init3" z-1 2)
              (p "ttp-rc2" "y" z (enc "h" (cat "h" (enc m k))))
              (p "init5" "r" z-0 r) (p "init5" "m" z-0 m)
              (p "init5" "a" z-0 a) (p "init5" "b" z-0 b)
              (p "init5" "t" z-0 t) (p "init5" "k" z-0 k)
              (p "init3" "r" z-1 r-0) (p "init3" "m" z-1 m)
              (p "init3" "a" z-1 a) (p "init3" "b" z-1 b)
              (p "init3" "t" z-1 t) (p "init3" "k" z-1 k)
              (prec z-0 0 z 0) (prec z-1 1 z 1)))
          (exists ((m data) (z-0 strd))
            (and (= y (enc "h" (cat "h" (enc m k)))) (p "init5" z-0 3)
              (p "ttp-rc2" "y" z (enc "h" (cat "h" (enc m k))))
              (p "init5" "r" z-0 r) (p "init5" "m" z-0 m)
              (p "init5" "a" z-0 a) (p "init5" "b" z-0 b)
              (p "init5" "t" z-0 t) (p "init5" "k" z-0 k)
              (prec z-0 0 z 0) (prec z-0 2 z 1)))
          (exists ((r-0 text) (m data) (z-0 z-1 strd))
            (and (= y (enc "h" (cat "h" (enc m k)))) (p "init5" z-0 1)
              (p "init5" z-1 3)
              (p "ttp-rc2" "y" z (enc "h" (cat "h" (enc m k))))
              (p "init5" "r" z-0 r) (p "init5" "m" z-0 m)
              (p "init5" "a" z-0 a) (p "init5" "b" z-0 b)
              (p "init5" "t" z-0 t) (p "init5" "k" z-0 k)
              (p "init5" "r" z-1 r-0) (p "init5" "m" z-1 m)
              (p "init5" "a" z-1 a) (p "init5" "b" z-1 b)
              (p "init5" "t" z-1 t) (p "init5" "k" z-1 k)
              (prec z-0 0 z 0) (prec z-1 2 z 1)))))))
  (traces
    ((recv
       (cat (cat a b t y (enc "h" (cat "h" k)))
         (enc "keytag" (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
           k r (pubk "encr" t))
         (enc "eootag" (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
             (pubk "encr" t)) (privk "sign" a))
         (enc "eortag" (enc "h" (cat "h" a b t y (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
             (pubk "encr" t)) (privk "sign" b))
         (enc "rcrq" (cat a b t y (enc "h" (cat "h" k)))
           (enc "keytag"
             (enc "h" (cat "h" a b t y (enc "h" (cat "h" k)))) k r
             (pubk "encr" t)) (privk "sign" b))))
      (recv
        (cat "sync-rc-req"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t y (enc "h" (cat "h" k)) (privk "sign" a))
          (privk "sign" t)))))
  (label 86)
  (unrealized (0 0) (0 1))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton wang
  (vars (r text) (m data) (a b t name) (k skey))
  (defstrand ttp-rc2 3 (y (enc "h" (cat "h" (enc m k)))) (r r) (a a)
    (b b) (t t) (k k))
  (defstrand init5 1 (r r) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 0) (0 0)))
  (non-orig (privk "encr" t) (privk "sign" a))
  (operation encryption-test (added-strand init5 1)
    (enc "eootag"
      (enc "h"
        (cat "h" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k))))
      (enc "keytag"
        (enc "h"
          (cat "h" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)))) k r (pubk "encr" t))
      (privk "sign" a)) (0 0))
  (traces
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))
         (enc "eortag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))
         (enc "rcrq"
           (cat a b t (enc "h" (cat "h" (enc m k)))
             (enc "h" (cat "h" k)))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))))
      (recv
        (cat "sync-rc-req"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))))
  (label 87)
  (parent 86)
  (unrealized (0 1))
  (comment "4 in cohort - 4 not yet seen"))

(defskeleton wang
  (vars (r r-0 text) (m data) (a b t name) (k skey))
  (defstrand ttp-rc2 3 (y (enc "h" (cat "h" (enc m k)))) (r r) (a a)
    (b b) (t t) (k k))
  (defstrand init5 1 (r r) (m m) (a a) (b b) (t t) (k k))
  (defstrand init3 2 (r r-0) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 0) (0 0)) ((2 1) (0 1)))
  (non-orig (privk "encr" t) (privk "sign" a))
  (operation encryption-test (added-strand init3 2)
    (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
      (enc "h" (cat "h" k)) (privk "sign" a)) (0 1))
  (traces
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))
         (enc "eortag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))
         (enc "rcrq"
           (cat a b t (enc "h" (cat "h" (enc m k)))
             (enc "h" (cat "h" k)))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))))
      (recv
        (cat "sync-rc-req"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a)))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r-0 (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r-0 (pubk "encr" t))
           (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))))
  (label 88)
  (parent 87)
  (unrealized)
  (shape)
  (satisfies yes)
  (maps
    ((0)
      ((y (enc "h" (cat "h" (enc m k)))) (r r) (a a) (b b) (t t)
        (k k))))
  (origs))

(defskeleton wang
  (vars (r text) (m data) (a b t name) (k skey))
  (defstrand ttp-rc2 3 (y (enc "h" (cat "h" (enc m k)))) (r r) (a a)
    (b b) (t t) (k k))
  (defstrand init3 2 (r r) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 0) (0 0)) ((1 1) (0 1)))
  (non-orig (privk "encr" t) (privk "sign" a))
  (operation encryption-test (displaced 1 2 init3 2)
    (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
      (enc "h" (cat "h" k)) (privk "sign" a)) (0 1))
  (traces
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))
         (enc "eortag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))
         (enc "rcrq"
           (cat a b t (enc "h" (cat "h" (enc m k)))
             (enc "h" (cat "h" k)))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))))
      (recv
        (cat "sync-rc-req"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))))
  (label 89)
  (parent 87)
  (unrealized)
  (shape)
  (satisfies yes)
  (maps
    ((0)
      ((y (enc "h" (cat "h" (enc m k)))) (r r) (a a) (b b) (t t)
        (k k))))
  (origs))

(defskeleton wang
  (vars (r text) (m data) (a b t name) (k skey))
  (defstrand ttp-rc2 3 (y (enc "h" (cat "h" (enc m k)))) (r r) (a a)
    (b b) (t t) (k k))
  (defstrand init5 3 (r r) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 0) (0 0)) ((1 2) (0 1)))
  (non-orig (privk "encr" t) (privk "sign" a))
  (operation encryption-test (displaced 1 2 init5 3)
    (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
      (enc "h" (cat "h" k)) (privk "sign" a)) (0 1))
  (traces
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))
         (enc "eortag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))
         (enc "rcrq"
           (cat a b t (enc "h" (cat "h" (enc m k)))
             (enc "h" (cat "h" k)))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))))
      (recv
        (cat "sync-rc-req"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))))
  (label 90)
  (parent 87)
  (unrealized)
  (shape)
  (satisfies yes)
  (maps
    ((0)
      ((y (enc "h" (cat "h" (enc m k)))) (r r) (a a) (b b) (t t)
        (k k))))
  (origs))

(defskeleton wang
  (vars (r r-0 text) (m data) (a b t name) (k skey))
  (defstrand ttp-rc2 3 (y (enc "h" (cat "h" (enc m k)))) (r r) (a a)
    (b b) (t t) (k k))
  (defstrand init5 1 (r r) (m m) (a a) (b b) (t t) (k k))
  (defstrand init5 3 (r r-0) (m m) (a a) (b b) (t t) (k k))
  (precedes ((1 0) (0 0)) ((2 2) (0 1)))
  (non-orig (privk "encr" t) (privk "sign" a))
  (operation encryption-test (added-strand init5 3)
    (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
      (enc "h" (cat "h" k)) (privk "sign" a)) (0 1))
  (traces
    ((recv
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a))
         (enc "eortag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))
         (enc "rcrq"
           (cat a b t (enc "h" (cat "h" (enc m k)))
             (enc "h" (cat "h" k)))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" b))))
      (recv
        (cat "sync-rc-req"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a))))
      (send
        (enc "abcf"
          (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
            (enc "h" (cat "h" k)) (privk "sign" a)) (privk "sign" t))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r (pubk "encr" t))
           (privk "sign" a)))))
    ((send
       (cat
         (cat a b t (enc "h" (cat "h" (enc m k))) (enc "h" (cat "h" k)))
         (enc m k)
         (enc "keytag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k)))) k r-0 (pubk "encr" t))
         (enc "eootag"
           (enc "h"
             (cat "h" a b t (enc "h" (cat "h" (enc m k)))
               (enc "h" (cat "h" k))))
           (enc "keytag"
             (enc "h"
               (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                 (enc "h" (cat "h" k)))) k r-0 (pubk "encr" t))
           (privk "sign" a))))
      (recv
        (enc "eortag"
          (enc "h"
            (cat "h" a b t (enc "h" (cat "h" (enc m k)))
              (enc "h" (cat "h" k))))
          (enc "keytag"
            (enc "h"
              (cat "h" a b t (enc "h" (cat "h" (enc m k)))
                (enc "h" (cat "h" k)))) k r-0 (pubk "encr" t))
          (privk "sign" b)))
      (send
        (enc "abrq" a b t (enc "h" (cat "h" (enc m k)))
          (enc "h" (cat "h" k)) (privk "sign" a)))))
  (label 91)
  (parent 87)
  (unrealized)
  (shape)
  (satisfies yes)
  (maps
    ((0)
      ((y (enc "h" (cat "h" (enc m k)))) (r r) (a a) (b b) (t t)
        (k k))))
  (origs))

(comment "Nothing left to do")
