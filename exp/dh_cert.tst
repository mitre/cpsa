(herald "Diffie-Hellman with Certificate" (algebra diffie-hellman))

(comment "CPSA 2.3.0")
(comment "All input read from dh_cert.scm")

(defprotocol dh-cert diffie-hellman
  (defrole ca
    (vars (p ca name) (ps-ltv expn))
    (trace
      (send (enc "cert" p (exp (gen) ps-ltv) (privk "certify" ca))))
    (uniq-orig ps-ltv))
  (defrole init
    (vars (a b ca name) (as-ltv bs-ltv x expn) (gB gy base))
    (trace
      (send
        (cat (exp (gen) as-ltv)
          (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
          (exp (gen) x)))
      (recv
        (cat gB (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          gy))
      (send
        (enc "tag1"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) gB
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) gy
          (enc "hash" (cat (exp gB x) (exp gy as-ltv)))))
      (recv
        (enc "tag2"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) gB
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) gy
          (enc "hash" (cat (exp gB x) (exp gy as-ltv))))))
    (uniq-orig as-ltv x))
  (defrole resp
    (vars (a b ca name) (bs-ltv as-ltv y expn) (gA gx base))
    (trace
      (recv
        (cat gA (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
          gx))
      (send
        (cat (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)))
      (recv
        (enc "tag1"
          (cat gA (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            gx) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y) (enc "hash" (cat (exp gx bs-ltv) (exp gA y)))))
      (send
        (enc "tag2"
          (cat gA (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            gx) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y) (enc "hash" (cat (exp gx bs-ltv) (exp gA y))))))
    (uniq-orig bs-ltv y)))

(defskeleton dh-cert
  (vars (ca a b name) (gB gy base) (as-ltv bs-ltv x expn))
  (defstrand init 4 (a a) (b b) (ca ca) (gB gB) (gy gy) (as-ltv as-ltv)
    (bs-ltv bs-ltv) (x x))
  (non-orig (privk ca))
  (uniq-orig as-ltv x)
  (traces
    ((send
       (cat (exp (gen) as-ltv)
         (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (exp (gen) x)))
      (recv
        (cat gB (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          gy))
      (send
        (enc "tag1"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) gB
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) gy
          (enc "hash" (cat (exp gB x) (exp gy as-ltv)))))
      (recv
        (enc "tag2"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) gB
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) gy
          (enc "hash" (cat (exp gB x) (exp gy as-ltv)))))))
  (label 0)
  (unrealized (0 3))
  (origs (x (0 0)) (as-ltv (0 0)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton dh-cert
  (vars (ca a b name) (as-ltv bs-ltv x y expn))
  (defstrand init 4 (a a) (b b) (ca ca) (gB (exp (gen) bs-ltv))
    (gy (exp (gen) y)) (as-ltv as-ltv) (bs-ltv bs-ltv) (x x))
  (defstrand resp 4 (a a) (b b) (ca ca) (gA (exp (gen) as-ltv))
    (gx (exp (gen) x)) (bs-ltv bs-ltv) (as-ltv as-ltv) (y y))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)) ((1 3) (0 3)))
  (non-orig (privk ca))
  (uniq-orig as-ltv bs-ltv x y)
  (operation encryption-test (added-strand resp 4)
    (enc "tag2"
      (cat (exp (gen) as-ltv)
        (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
        (exp (gen) x)) (exp (gen) bs-ltv)
      (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
      (exp (gen) y)
      (enc "hash"
        (cat (exp (exp (gen) bs-ltv) x) (exp (exp (gen) as-ltv) y))))
    (0 3))
  (traces
    ((send
       (cat (exp (gen) as-ltv)
         (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (exp (gen) x)))
      (recv
        (cat (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)))
      (send
        (enc "tag1"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y)))))
      (recv
        (enc "tag2"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y))))))
    ((recv
       (cat (exp (gen) as-ltv)
         (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (exp (gen) x)))
      (send
        (cat (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)))
      (recv
        (enc "tag1"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y)))))
      (send
        (enc "tag2"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y)))))))
  (label 1)
  (parent 0)
  (unrealized (1 2))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton dh-cert
  (vars (ca a b name) (gB gy base) (as-ltv bs-ltv x expn))
  (defstrand init 4 (a a) (b b) (ca ca) (gB gB) (gy gy) (as-ltv as-ltv)
    (bs-ltv bs-ltv) (x x))
  (deflistener (enc "hash" (cat (exp gB x) (exp gy as-ltv))))
  (precedes ((1 1) (0 3)))
  (non-orig (privk ca))
  (uniq-orig as-ltv x)
  (operation encryption-test
    (added-listener (enc "hash" (cat (exp gB x) (exp gy as-ltv))))
    (enc "tag2"
      (cat (exp (gen) as-ltv)
        (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
        (exp (gen) x)) gB
      (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) gy
      (enc "hash" (cat (exp gB x) (exp gy as-ltv)))) (0 3))
  (traces
    ((send
       (cat (exp (gen) as-ltv)
         (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (exp (gen) x)))
      (recv
        (cat gB (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          gy))
      (send
        (enc "tag1"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) gB
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) gy
          (enc "hash" (cat (exp gB x) (exp gy as-ltv)))))
      (recv
        (enc "tag2"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) gB
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) gy
          (enc "hash" (cat (exp gB x) (exp gy as-ltv))))))
    ((recv (enc "hash" (cat (exp gB x) (exp gy as-ltv))))
      (send (enc "hash" (cat (exp gB x) (exp gy as-ltv))))))
  (label 2)
  (parent 0)
  (unrealized (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dh-cert
  (vars (ca a b name) (as-ltv bs-ltv x y expn))
  (defstrand init 4 (a a) (b b) (ca ca) (gB (exp (gen) bs-ltv))
    (gy (exp (gen) y)) (as-ltv as-ltv) (bs-ltv bs-ltv) (x x))
  (defstrand resp 4 (a a) (b b) (ca ca) (gA (exp (gen) as-ltv))
    (gx (exp (gen) x)) (bs-ltv bs-ltv) (as-ltv as-ltv) (y y))
  (precedes ((0 0) (1 0)) ((0 2) (1 2)) ((1 1) (0 1)) ((1 3) (0 3)))
  (non-orig (privk ca))
  (uniq-orig as-ltv bs-ltv x y)
  (operation encryption-test (displaced 2 0 init 3)
    (enc "tag1"
      (cat (exp (gen) as-ltv)
        (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
        (exp (gen) x)) (exp (gen) bs-ltv)
      (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
      (exp (gen) y)
      (enc "hash"
        (cat (exp (exp (gen) bs-ltv) x) (exp (exp (gen) as-ltv) y))))
    (1 2))
  (traces
    ((send
       (cat (exp (gen) as-ltv)
         (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (exp (gen) x)))
      (recv
        (cat (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)))
      (send
        (enc "tag1"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y)))))
      (recv
        (enc "tag2"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y))))))
    ((recv
       (cat (exp (gen) as-ltv)
         (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (exp (gen) x)))
      (send
        (cat (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)))
      (recv
        (enc "tag1"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y)))))
      (send
        (enc "tag2"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y)))))))
  (label 3)
  (parent 1)
  (unrealized)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dh-cert
  (vars (ca a b name) (as-ltv bs-ltv x y expn))
  (defstrand init 4 (a a) (b b) (ca ca) (gB (exp (gen) bs-ltv))
    (gy (exp (gen) y)) (as-ltv as-ltv) (bs-ltv bs-ltv) (x x))
  (defstrand resp 4 (a a) (b b) (ca ca) (gA (exp (gen) as-ltv))
    (gx (exp (gen) x)) (bs-ltv bs-ltv) (as-ltv as-ltv) (y y))
  (deflistener
    (enc "hash"
      (cat (exp (exp (gen) bs-ltv) x) (exp (exp (gen) as-ltv) y))))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)) ((1 3) (0 3)) ((2 1) (1 2)))
  (non-orig (privk ca))
  (uniq-orig as-ltv bs-ltv x y)
  (operation encryption-test
    (added-listener
      (enc "hash"
        (cat (exp (exp (gen) bs-ltv) x) (exp (exp (gen) as-ltv) y))))
    (enc "tag1"
      (cat (exp (gen) as-ltv)
        (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
        (exp (gen) x)) (exp (gen) bs-ltv)
      (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
      (exp (gen) y)
      (enc "hash"
        (cat (exp (exp (gen) bs-ltv) x) (exp (exp (gen) as-ltv) y))))
    (1 2))
  (traces
    ((send
       (cat (exp (gen) as-ltv)
         (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (exp (gen) x)))
      (recv
        (cat (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)))
      (send
        (enc "tag1"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y)))))
      (recv
        (enc "tag2"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y))))))
    ((recv
       (cat (exp (gen) as-ltv)
         (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (exp (gen) x)))
      (send
        (cat (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)))
      (recv
        (enc "tag1"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y)))))
      (send
        (enc "tag2"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y))))))
    ((recv
       (enc "hash"
         (cat (exp (exp (gen) bs-ltv) x) (exp (exp (gen) as-ltv) y))))
      (send
        (enc "hash"
          (cat (exp (exp (gen) bs-ltv) x)
            (exp (exp (gen) as-ltv) y))))))
  (label 4)
  (parent 1)
  (unrealized (2 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dh-cert
  (vars (ca a b name) (gB gy base) (as-ltv bs-ltv x expn))
  (defstrand init 4 (a a) (b b) (ca ca) (gB gB) (gy gy) (as-ltv as-ltv)
    (bs-ltv bs-ltv) (x x))
  (deflistener (enc "hash" (cat (exp gB x) (exp gy as-ltv))))
  (deflistener (cat (exp gB x) (exp gy as-ltv)))
  (precedes ((0 0) (2 0)) ((1 1) (0 3)) ((2 1) (1 0)))
  (non-orig (privk ca))
  (uniq-orig as-ltv x)
  (operation encryption-test
    (added-listener (cat (exp gB x) (exp gy as-ltv)))
    (enc "hash" (cat (exp gB x) (exp gy as-ltv))) (1 0))
  (traces
    ((send
       (cat (exp (gen) as-ltv)
         (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (exp (gen) x)))
      (recv
        (cat gB (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          gy))
      (send
        (enc "tag1"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) gB
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) gy
          (enc "hash" (cat (exp gB x) (exp gy as-ltv)))))
      (recv
        (enc "tag2"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) gB
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) gy
          (enc "hash" (cat (exp gB x) (exp gy as-ltv))))))
    ((recv (enc "hash" (cat (exp gB x) (exp gy as-ltv))))
      (send (enc "hash" (cat (exp gB x) (exp gy as-ltv)))))
    ((recv (cat (exp gB x) (exp gy as-ltv)))
      (send (cat (exp gB x) (exp gy as-ltv)))))
  (label 5)
  (parent 2)
  (unrealized (2 0))
  (comment "3 in cohort - 3 not yet seen"))

(defskeleton dh-cert
  (vars (ca a b name) (as-ltv bs-ltv x y expn))
  (defstrand init 4 (a a) (b b) (ca ca) (gB (exp (gen) bs-ltv))
    (gy (exp (gen) y)) (as-ltv as-ltv) (bs-ltv bs-ltv) (x x))
  (non-orig (privk ca))
  (uniq-orig as-ltv bs-ltv x y)
  (operation generalization deleted (1 0))
  (traces
    ((send
       (cat (exp (gen) as-ltv)
         (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (exp (gen) x)))
      (recv
        (cat (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)))
      (send
        (enc "tag1"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y)))))
      (recv
        (enc "tag2"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y)))))))
  (label 6)
  (parent 3)
  (unrealized)
  (origs (as-ltv (0 0)) (x (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dh-cert
  (vars (ca a b name) (as-ltv bs-ltv x y expn))
  (defstrand init 4 (a a) (b b) (ca ca) (gB (exp (gen) bs-ltv))
    (gy (exp (gen) y)) (as-ltv as-ltv) (bs-ltv bs-ltv) (x x))
  (defstrand resp 4 (a a) (b b) (ca ca) (gA (exp (gen) as-ltv))
    (gx (exp (gen) x)) (bs-ltv bs-ltv) (as-ltv as-ltv) (y y))
  (deflistener
    (enc "hash"
      (cat (exp (exp (gen) bs-ltv) x) (exp (exp (gen) as-ltv) y))))
  (deflistener
    (cat (exp (exp (gen) bs-ltv) x) (exp (exp (gen) as-ltv) y)))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)) ((1 1) (3 0)) ((1 3) (0 3))
    ((2 1) (1 2)) ((3 1) (2 0)))
  (non-orig (privk ca))
  (uniq-orig as-ltv bs-ltv x y)
  (operation encryption-test
    (added-listener
      (cat (exp (exp (gen) bs-ltv) x) (exp (exp (gen) as-ltv) y)))
    (enc "hash"
      (cat (exp (exp (gen) bs-ltv) x) (exp (exp (gen) as-ltv) y)))
    (2 0))
  (traces
    ((send
       (cat (exp (gen) as-ltv)
         (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (exp (gen) x)))
      (recv
        (cat (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)))
      (send
        (enc "tag1"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y)))))
      (recv
        (enc "tag2"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y))))))
    ((recv
       (cat (exp (gen) as-ltv)
         (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (exp (gen) x)))
      (send
        (cat (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)))
      (recv
        (enc "tag1"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y)))))
      (send
        (enc "tag2"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y))))))
    ((recv
       (enc "hash"
         (cat (exp (exp (gen) bs-ltv) x) (exp (exp (gen) as-ltv) y))))
      (send
        (enc "hash"
          (cat (exp (exp (gen) bs-ltv) x) (exp (exp (gen) as-ltv) y)))))
    ((recv (cat (exp (exp (gen) bs-ltv) x) (exp (exp (gen) as-ltv) y)))
      (send
        (cat (exp (exp (gen) bs-ltv) x) (exp (exp (gen) as-ltv) y)))))
  (label 7)
  (parent 4)
  (unrealized (3 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton dh-cert
  (vars (ca a b name) (gy base) (as-ltv bs-ltv expn))
  (defstrand init 4 (a a) (b b) (ca ca) (gB (gen)) (gy gy)
    (as-ltv as-ltv) (bs-ltv bs-ltv) (x as-ltv))
  (deflistener (enc "hash" (cat (exp (gen) as-ltv) (exp gy as-ltv))))
  (deflistener (cat (exp (gen) as-ltv) (exp gy as-ltv)))
  (precedes ((0 0) (2 0)) ((1 1) (0 3)) ((2 1) (1 0)))
  (non-orig (privk ca))
  (uniq-orig as-ltv)
  (operation encryption-test (displaced 3 0 init 1) (exp (gen) x) (2 0))
  (traces
    ((send
       (cat (exp (gen) as-ltv)
         (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (exp (gen) as-ltv)))
      (recv
        (cat (gen)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) gy))
      (send
        (enc "tag1"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) as-ltv)) (gen)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) gy
          (enc "hash" (cat (exp (gen) as-ltv) (exp gy as-ltv)))))
      (recv
        (enc "tag2"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) as-ltv)) (gen)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) gy
          (enc "hash" (cat (exp (gen) as-ltv) (exp gy as-ltv))))))
    ((recv (enc "hash" (cat (exp (gen) as-ltv) (exp gy as-ltv))))
      (send (enc "hash" (cat (exp (gen) as-ltv) (exp gy as-ltv)))))
    ((recv (cat (exp (gen) as-ltv) (exp gy as-ltv)))
      (send (cat (exp (gen) as-ltv) (exp gy as-ltv)))))
  (label 8)
  (parent 5)
  (seen 14)
  (unrealized (2 0))
  (comment "3 in cohort - 2 not yet seen"))

(defskeleton dh-cert
  (vars (ca a b name) (gy base) (as-ltv bs-ltv x expn))
  (defstrand init 4 (a a) (b b) (ca ca) (gB (gen)) (gy gy)
    (as-ltv as-ltv) (bs-ltv bs-ltv) (x x))
  (deflistener (enc "hash" (cat (exp (gen) x) (exp gy as-ltv))))
  (deflistener (cat (exp (gen) x) (exp gy as-ltv)))
  (precedes ((0 0) (2 0)) ((1 1) (0 3)) ((2 1) (1 0)))
  (non-orig (privk ca))
  (uniq-orig as-ltv x)
  (operation encryption-test (displaced 3 0 init 1) (exp (gen) x) (2 0))
  (traces
    ((send
       (cat (exp (gen) as-ltv)
         (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (exp (gen) x)))
      (recv
        (cat (gen)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) gy))
      (send
        (enc "tag1"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (gen)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) gy
          (enc "hash" (cat (exp (gen) x) (exp gy as-ltv)))))
      (recv
        (enc "tag2"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (gen)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) gy
          (enc "hash" (cat (exp (gen) x) (exp gy as-ltv))))))
    ((recv (enc "hash" (cat (exp (gen) x) (exp gy as-ltv))))
      (send (enc "hash" (cat (exp (gen) x) (exp gy as-ltv)))))
    ((recv (cat (exp (gen) x) (exp gy as-ltv)))
      (send (cat (exp (gen) x) (exp gy as-ltv)))))
  (label 9)
  (parent 5)
  (seen 14)
  (unrealized (2 0))
  (comment "3 in cohort - 2 not yet seen"))

(defskeleton dh-cert
  (vars (ca a b name) (gB gy base) (as-ltv bs-ltv x expn))
  (defstrand init 4 (a a) (b b) (ca ca) (gB gB) (gy gy) (as-ltv as-ltv)
    (bs-ltv bs-ltv) (x x))
  (deflistener (enc "hash" (cat (exp gB x) (exp gy as-ltv))))
  (deflistener (cat (exp gB x) (exp gy as-ltv)))
  (deflistener x)
  (precedes ((0 0) (3 0)) ((1 1) (0 3)) ((2 1) (1 0)) ((3 1) (2 0)))
  (non-orig (privk ca))
  (uniq-orig as-ltv x)
  (operation encryption-test (added-listener x) (exp gB x) (2 0))
  (traces
    ((send
       (cat (exp (gen) as-ltv)
         (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (exp (gen) x)))
      (recv
        (cat gB (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          gy))
      (send
        (enc "tag1"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) gB
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) gy
          (enc "hash" (cat (exp gB x) (exp gy as-ltv)))))
      (recv
        (enc "tag2"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) gB
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) gy
          (enc "hash" (cat (exp gB x) (exp gy as-ltv))))))
    ((recv (enc "hash" (cat (exp gB x) (exp gy as-ltv))))
      (send (enc "hash" (cat (exp gB x) (exp gy as-ltv)))))
    ((recv (cat (exp gB x) (exp gy as-ltv)))
      (send (cat (exp gB x) (exp gy as-ltv)))) ((recv x) (send x)))
  (label 10)
  (parent 5)
  (unrealized (2 0) (3 0))
  (comment "empty cohort"))

(defskeleton dh-cert
  (vars (ca a b name) (as-ltv bs-ltv x y expn))
  (defstrand init 4 (a a) (b b) (ca ca) (gB (exp (gen) bs-ltv))
    (gy (exp (gen) y)) (as-ltv as-ltv) (bs-ltv bs-ltv) (x x))
  (non-orig (privk ca))
  (uniq-orig as-ltv x y)
  (operation generalization forgot bs-ltv)
  (traces
    ((send
       (cat (exp (gen) as-ltv)
         (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (exp (gen) x)))
      (recv
        (cat (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)))
      (send
        (enc "tag1"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y)))))
      (recv
        (enc "tag2"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y)))))))
  (label 11)
  (parent 6)
  (unrealized)
  (origs (as-ltv (0 0)) (x (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dh-cert
  (vars (ca a b name) (as-ltv bs-ltv x y expn))
  (defstrand init 4 (a a) (b b) (ca ca) (gB (exp (gen) bs-ltv))
    (gy (exp (gen) y)) (as-ltv as-ltv) (bs-ltv bs-ltv) (x x))
  (defstrand resp 4 (a a) (b b) (ca ca) (gA (exp (gen) as-ltv))
    (gx (exp (gen) x)) (bs-ltv bs-ltv) (as-ltv as-ltv) (y y))
  (deflistener
    (enc "hash"
      (cat (exp (exp (gen) bs-ltv) x) (exp (exp (gen) as-ltv) y))))
  (deflistener
    (cat (exp (exp (gen) bs-ltv) x) (exp (exp (gen) as-ltv) y)))
  (deflistener bs-ltv)
  (precedes ((0 0) (1 0)) ((1 1) (0 1)) ((1 1) (4 0)) ((1 3) (0 3))
    ((2 1) (1 2)) ((3 1) (2 0)) ((4 1) (3 0)))
  (non-orig (privk ca))
  (uniq-orig as-ltv bs-ltv x y)
  (operation encryption-test (added-listener bs-ltv)
    (exp (exp (gen) bs-ltv) x) (3 0))
  (traces
    ((send
       (cat (exp (gen) as-ltv)
         (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (exp (gen) x)))
      (recv
        (cat (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)))
      (send
        (enc "tag1"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y)))))
      (recv
        (enc "tag2"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y))))))
    ((recv
       (cat (exp (gen) as-ltv)
         (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (exp (gen) x)))
      (send
        (cat (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)))
      (recv
        (enc "tag1"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y)))))
      (send
        (enc "tag2"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y))))))
    ((recv
       (enc "hash"
         (cat (exp (exp (gen) bs-ltv) x) (exp (exp (gen) as-ltv) y))))
      (send
        (enc "hash"
          (cat (exp (exp (gen) bs-ltv) x) (exp (exp (gen) as-ltv) y)))))
    ((recv (cat (exp (exp (gen) bs-ltv) x) (exp (exp (gen) as-ltv) y)))
      (send
        (cat (exp (exp (gen) bs-ltv) x) (exp (exp (gen) as-ltv) y))))
    ((recv bs-ltv) (send bs-ltv)))
  (label 12)
  (parent 7)
  (unrealized (3 0) (4 0))
  (comment "empty cohort"))

(defskeleton dh-cert
  (vars (ca a b name) (as-ltv bs-ltv x y expn))
  (defstrand init 4 (a a) (b b) (ca ca) (gB (exp (gen) bs-ltv))
    (gy (exp (gen) y)) (as-ltv as-ltv) (bs-ltv bs-ltv) (x x))
  (defstrand resp 4 (a a) (b b) (ca ca) (gA (exp (gen) as-ltv))
    (gx (exp (gen) x)) (bs-ltv bs-ltv) (as-ltv as-ltv) (y y))
  (deflistener
    (enc "hash"
      (cat (exp (exp (gen) bs-ltv) x) (exp (exp (gen) as-ltv) y))))
  (deflistener
    (cat (exp (exp (gen) bs-ltv) x) (exp (exp (gen) as-ltv) y)))
  (deflistener x)
  (precedes ((0 0) (1 0)) ((0 0) (4 0)) ((1 1) (0 1)) ((1 1) (3 0))
    ((1 3) (0 3)) ((2 1) (1 2)) ((3 1) (2 0)) ((4 1) (3 0)))
  (non-orig (privk ca))
  (uniq-orig as-ltv bs-ltv x y)
  (operation encryption-test (added-listener x)
    (exp (exp (gen) bs-ltv) x) (3 0))
  (traces
    ((send
       (cat (exp (gen) as-ltv)
         (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (exp (gen) x)))
      (recv
        (cat (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)))
      (send
        (enc "tag1"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y)))))
      (recv
        (enc "tag2"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y))))))
    ((recv
       (cat (exp (gen) as-ltv)
         (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (exp (gen) x)))
      (send
        (cat (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)))
      (recv
        (enc "tag1"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y)))))
      (send
        (enc "tag2"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y))))))
    ((recv
       (enc "hash"
         (cat (exp (exp (gen) bs-ltv) x) (exp (exp (gen) as-ltv) y))))
      (send
        (enc "hash"
          (cat (exp (exp (gen) bs-ltv) x) (exp (exp (gen) as-ltv) y)))))
    ((recv (cat (exp (exp (gen) bs-ltv) x) (exp (exp (gen) as-ltv) y)))
      (send
        (cat (exp (exp (gen) bs-ltv) x) (exp (exp (gen) as-ltv) y))))
    ((recv x) (send x)))
  (label 13)
  (parent 7)
  (unrealized (3 0) (4 0))
  (comment "empty cohort"))

(defskeleton dh-cert
  (vars (ca a b name) (as-ltv bs-ltv expn))
  (defstrand init 4 (a a) (b b) (ca ca) (gB (gen)) (gy (gen))
    (as-ltv as-ltv) (bs-ltv bs-ltv) (x as-ltv))
  (deflistener (enc "hash" (cat (exp (gen) as-ltv) (exp (gen) as-ltv))))
  (deflistener (cat (exp (gen) as-ltv) (exp (gen) as-ltv)))
  (precedes ((0 0) (2 0)) ((1 1) (0 3)) ((2 1) (1 0)))
  (non-orig (privk ca))
  (uniq-orig as-ltv)
  (operation encryption-test (displaced 3 0 init 1) (exp (gen) as-ltv)
    (2 0))
  (traces
    ((send
       (cat (exp (gen) as-ltv)
         (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (exp (gen) as-ltv)))
      (recv
        (cat (gen)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) (gen)))
      (send
        (enc "tag1"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) as-ltv)) (gen)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) (gen)
          (enc "hash" (cat (exp (gen) as-ltv) (exp (gen) as-ltv)))))
      (recv
        (enc "tag2"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) as-ltv)) (gen)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) (gen)
          (enc "hash" (cat (exp (gen) as-ltv) (exp (gen) as-ltv))))))
    ((recv (enc "hash" (cat (exp (gen) as-ltv) (exp (gen) as-ltv))))
      (send (enc "hash" (cat (exp (gen) as-ltv) (exp (gen) as-ltv)))))
    ((recv (cat (exp (gen) as-ltv) (exp (gen) as-ltv)))
      (send (cat (exp (gen) as-ltv) (exp (gen) as-ltv)))))
  (label 14)
  (parent 8)
  (unrealized)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dh-cert
  (vars (ca a b name) (gy base) (as-ltv bs-ltv expn))
  (defstrand init 4 (a a) (b b) (ca ca) (gB (gen)) (gy gy)
    (as-ltv as-ltv) (bs-ltv bs-ltv) (x as-ltv))
  (deflistener (enc "hash" (cat (exp (gen) as-ltv) (exp gy as-ltv))))
  (deflistener (cat (exp (gen) as-ltv) (exp gy as-ltv)))
  (deflistener as-ltv)
  (precedes ((0 0) (3 0)) ((1 1) (0 3)) ((2 1) (1 0)) ((3 1) (2 0)))
  (non-orig (privk ca))
  (uniq-orig as-ltv)
  (operation encryption-test (added-listener as-ltv) (exp gy as-ltv)
    (2 0))
  (traces
    ((send
       (cat (exp (gen) as-ltv)
         (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (exp (gen) as-ltv)))
      (recv
        (cat (gen)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) gy))
      (send
        (enc "tag1"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) as-ltv)) (gen)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) gy
          (enc "hash" (cat (exp (gen) as-ltv) (exp gy as-ltv)))))
      (recv
        (enc "tag2"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) as-ltv)) (gen)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) gy
          (enc "hash" (cat (exp (gen) as-ltv) (exp gy as-ltv))))))
    ((recv (enc "hash" (cat (exp (gen) as-ltv) (exp gy as-ltv))))
      (send (enc "hash" (cat (exp (gen) as-ltv) (exp gy as-ltv)))))
    ((recv (cat (exp (gen) as-ltv) (exp gy as-ltv)))
      (send (cat (exp (gen) as-ltv) (exp gy as-ltv))))
    ((recv as-ltv) (send as-ltv)))
  (label 15)
  (parent 8)
  (unrealized (3 0))
  (comment "empty cohort"))

(defskeleton dh-cert
  (vars (ca a b name) (as-ltv bs-ltv x expn))
  (defstrand init 4 (a a) (b b) (ca ca) (gB (gen)) (gy (gen))
    (as-ltv as-ltv) (bs-ltv bs-ltv) (x x))
  (deflistener (enc "hash" (cat (exp (gen) x) (exp (gen) as-ltv))))
  (deflistener (cat (exp (gen) x) (exp (gen) as-ltv)))
  (precedes ((0 0) (2 0)) ((1 1) (0 3)) ((2 1) (1 0)))
  (non-orig (privk ca))
  (uniq-orig as-ltv x)
  (operation encryption-test (displaced 3 0 init 1) (exp (gen) as-ltv)
    (2 0))
  (traces
    ((send
       (cat (exp (gen) as-ltv)
         (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (exp (gen) x)))
      (recv
        (cat (gen)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) (gen)))
      (send
        (enc "tag1"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (gen)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) (gen)
          (enc "hash" (cat (exp (gen) x) (exp (gen) as-ltv)))))
      (recv
        (enc "tag2"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (gen)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) (gen)
          (enc "hash" (cat (exp (gen) x) (exp (gen) as-ltv))))))
    ((recv (enc "hash" (cat (exp (gen) x) (exp (gen) as-ltv))))
      (send (enc "hash" (cat (exp (gen) x) (exp (gen) as-ltv)))))
    ((recv (cat (exp (gen) x) (exp (gen) as-ltv)))
      (send (cat (exp (gen) x) (exp (gen) as-ltv)))))
  (label 16)
  (parent 9)
  (unrealized)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dh-cert
  (vars (ca a b name) (gy base) (as-ltv bs-ltv x expn))
  (defstrand init 4 (a a) (b b) (ca ca) (gB (gen)) (gy gy)
    (as-ltv as-ltv) (bs-ltv bs-ltv) (x x))
  (deflistener (enc "hash" (cat (exp (gen) x) (exp gy as-ltv))))
  (deflistener (cat (exp (gen) x) (exp gy as-ltv)))
  (deflistener as-ltv)
  (precedes ((0 0) (3 0)) ((1 1) (0 3)) ((2 1) (1 0)) ((3 1) (2 0)))
  (non-orig (privk ca))
  (uniq-orig as-ltv x)
  (operation encryption-test (added-listener as-ltv) (exp gy as-ltv)
    (2 0))
  (traces
    ((send
       (cat (exp (gen) as-ltv)
         (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (exp (gen) x)))
      (recv
        (cat (gen)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) gy))
      (send
        (enc "tag1"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (gen)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) gy
          (enc "hash" (cat (exp (gen) x) (exp gy as-ltv)))))
      (recv
        (enc "tag2"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (gen)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) gy
          (enc "hash" (cat (exp (gen) x) (exp gy as-ltv))))))
    ((recv (enc "hash" (cat (exp (gen) x) (exp gy as-ltv))))
      (send (enc "hash" (cat (exp (gen) x) (exp gy as-ltv)))))
    ((recv (cat (exp (gen) x) (exp gy as-ltv)))
      (send (cat (exp (gen) x) (exp gy as-ltv))))
    ((recv as-ltv) (send as-ltv)))
  (label 17)
  (parent 9)
  (unrealized (3 0))
  (comment "empty cohort"))

(defskeleton dh-cert
  (vars (ca a b name) (as-ltv bs-ltv x y expn))
  (defstrand init 4 (a a) (b b) (ca ca) (gB (exp (gen) bs-ltv))
    (gy (exp (gen) y)) (as-ltv as-ltv) (bs-ltv bs-ltv) (x x))
  (non-orig (privk ca))
  (uniq-orig as-ltv x)
  (operation generalization forgot y)
  (traces
    ((send
       (cat (exp (gen) as-ltv)
         (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (exp (gen) x)))
      (recv
        (cat (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)))
      (send
        (enc "tag1"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y)))))
      (recv
        (enc "tag2"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y)))))))
  (label 18)
  (parent 11)
  (unrealized)
  (origs (as-ltv (0 0)) (x (0 0)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dh-cert
  (vars (ca a b name) (as-ltv bs-ltv expn))
  (defstrand init 4 (a a) (b b) (ca ca) (gB (gen)) (gy (gen))
    (as-ltv as-ltv) (bs-ltv bs-ltv) (x as-ltv))
  (deflistener (cat (exp (gen) as-ltv) (exp (gen) as-ltv)))
  (precedes ((0 0) (1 0)) ((1 1) (0 3)))
  (non-orig (privk ca))
  (uniq-orig as-ltv)
  (operation generalization deleted (1 0))
  (traces
    ((send
       (cat (exp (gen) as-ltv)
         (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (exp (gen) as-ltv)))
      (recv
        (cat (gen)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) (gen)))
      (send
        (enc "tag1"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) as-ltv)) (gen)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) (gen)
          (enc "hash" (cat (exp (gen) as-ltv) (exp (gen) as-ltv)))))
      (recv
        (enc "tag2"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) as-ltv)) (gen)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) (gen)
          (enc "hash" (cat (exp (gen) as-ltv) (exp (gen) as-ltv))))))
    ((recv (cat (exp (gen) as-ltv) (exp (gen) as-ltv)))
      (send (cat (exp (gen) as-ltv) (exp (gen) as-ltv)))))
  (label 19)
  (parent 14)
  (unrealized)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dh-cert
  (vars (ca a b name) (as-ltv bs-ltv x expn))
  (defstrand init 4 (a a) (b b) (ca ca) (gB (gen)) (gy (gen))
    (as-ltv as-ltv) (bs-ltv bs-ltv) (x x))
  (deflistener (cat (exp (gen) x) (exp (gen) as-ltv)))
  (precedes ((0 0) (1 0)) ((1 1) (0 3)))
  (non-orig (privk ca))
  (uniq-orig as-ltv x)
  (operation generalization deleted (1 0))
  (traces
    ((send
       (cat (exp (gen) as-ltv)
         (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (exp (gen) x)))
      (recv
        (cat (gen)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) (gen)))
      (send
        (enc "tag1"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (gen)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) (gen)
          (enc "hash" (cat (exp (gen) x) (exp (gen) as-ltv)))))
      (recv
        (enc "tag2"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (gen)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) (gen)
          (enc "hash" (cat (exp (gen) x) (exp (gen) as-ltv))))))
    ((recv (cat (exp (gen) x) (exp (gen) as-ltv)))
      (send (cat (exp (gen) x) (exp (gen) as-ltv)))))
  (label 20)
  (parent 16)
  (unrealized)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dh-cert
  (vars (ca a b name) (as-ltv bs-ltv x y bs-ltv-0 expn))
  (defstrand init 4 (a a) (b b) (ca ca) (gB (exp (gen) bs-ltv))
    (gy (exp (gen) y)) (as-ltv as-ltv) (bs-ltv bs-ltv-0) (x x))
  (non-orig (privk ca))
  (uniq-orig as-ltv x)
  (operation generalization separated bs-ltv-0)
  (traces
    ((send
       (cat (exp (gen) as-ltv)
         (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (exp (gen) x)))
      (recv
        (cat (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv-0) (privk "certify" ca))
          (exp (gen) y)))
      (send
        (enc "tag1"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv-0) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y)))))
      (recv
        (enc "tag2"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv-0) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y)))))))
  (label 21)
  (parent 18)
  (unrealized)
  (shape)
  (maps
    ((0)
      ((ca ca) (a a) (b b) (as-ltv as-ltv) (bs-ltv bs-ltv-0) (x x)
        (gB (exp (gen) bs-ltv)) (gy (exp (gen) y)))))
  (origs (as-ltv (0 0)) (x (0 0))))

(defskeleton dh-cert
  (vars (ca a b name) (as-ltv bs-ltv expn))
  (defstrand init 4 (a a) (b b) (ca ca) (gB (gen)) (gy (gen))
    (as-ltv as-ltv) (bs-ltv bs-ltv) (x as-ltv))
  (non-orig (privk ca))
  (uniq-orig as-ltv)
  (operation generalization deleted (1 0))
  (traces
    ((send
       (cat (exp (gen) as-ltv)
         (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (exp (gen) as-ltv)))
      (recv
        (cat (gen)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) (gen)))
      (send
        (enc "tag1"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) as-ltv)) (gen)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) (gen)
          (enc "hash" (cat (exp (gen) as-ltv) (exp (gen) as-ltv)))))
      (recv
        (enc "tag2"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) as-ltv)) (gen)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) (gen)
          (enc "hash" (cat (exp (gen) as-ltv) (exp (gen) as-ltv)))))))
  (label 22)
  (parent 19)
  (seen 23)
  (unrealized)
  (origs (as-ltv (0 0)))
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton dh-cert
  (vars (ca a b name) (as-ltv bs-ltv x expn))
  (defstrand init 4 (a a) (b b) (ca ca) (gB (gen)) (gy (gen))
    (as-ltv as-ltv) (bs-ltv bs-ltv) (x x))
  (non-orig (privk ca))
  (uniq-orig as-ltv x)
  (operation generalization deleted (1 0))
  (traces
    ((send
       (cat (exp (gen) as-ltv)
         (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (exp (gen) x)))
      (recv
        (cat (gen)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) (gen)))
      (send
        (enc "tag1"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (gen)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) (gen)
          (enc "hash" (cat (exp (gen) x) (exp (gen) as-ltv)))))
      (recv
        (enc "tag2"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (gen)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) (gen)
          (enc "hash" (cat (exp (gen) x) (exp (gen) as-ltv)))))))
  (label 23)
  (parent 20)
  (unrealized)
  (shape)
  (maps
    ((0)
      ((ca ca) (a a) (b b) (as-ltv as-ltv) (bs-ltv bs-ltv) (x x)
        (gB (gen)) (gy (gen)))))
  (origs (as-ltv (0 0)) (x (0 0))))

(comment "Nothing left to do")

(defprotocol dh-cert diffie-hellman
  (defrole ca
    (vars (p ca name) (ps-ltv expn))
    (trace
      (send (enc "cert" p (exp (gen) ps-ltv) (privk "certify" ca))))
    (uniq-orig ps-ltv))
  (defrole init
    (vars (a b ca name) (as-ltv bs-ltv x expn) (gB gy base))
    (trace
      (send
        (cat (exp (gen) as-ltv)
          (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
          (exp (gen) x)))
      (recv
        (cat gB (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          gy))
      (send
        (enc "tag1"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) gB
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) gy
          (enc "hash" (cat (exp gB x) (exp gy as-ltv)))))
      (recv
        (enc "tag2"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) gB
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca)) gy
          (enc "hash" (cat (exp gB x) (exp gy as-ltv))))))
    (uniq-orig as-ltv x))
  (defrole resp
    (vars (a b ca name) (bs-ltv as-ltv y expn) (gA gx base))
    (trace
      (recv
        (cat gA (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
          gx))
      (send
        (cat (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)))
      (recv
        (enc "tag1"
          (cat gA (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            gx) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y) (enc "hash" (cat (exp gx bs-ltv) (exp gA y)))))
      (send
        (enc "tag2"
          (cat gA (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            gx) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y) (enc "hash" (cat (exp gx bs-ltv) (exp gA y))))))
    (uniq-orig bs-ltv y)))

(defskeleton dh-cert
  (vars (ca a b name) (gA gx base) (bs-ltv as-ltv y expn))
  (defstrand resp 4 (a a) (b b) (ca ca) (gA gA) (gx gx) (bs-ltv bs-ltv)
    (as-ltv as-ltv) (y y))
  (non-orig (privk ca))
  (uniq-orig bs-ltv y)
  (traces
    ((recv
       (cat gA (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         gx))
      (send
        (cat (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)))
      (recv
        (enc "tag1"
          (cat gA (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            gx) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y) (enc "hash" (cat (exp gx bs-ltv) (exp gA y)))))
      (send
        (enc "tag2"
          (cat gA (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            gx) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash" (cat (exp gx bs-ltv) (exp gA y)))))))
  (label 24)
  (unrealized (0 2))
  (origs (y (0 1)) (bs-ltv (0 1)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton dh-cert
  (vars (ca a b name) (bs-ltv as-ltv y x expn))
  (defstrand resp 4 (a a) (b b) (ca ca) (gA (exp (gen) as-ltv))
    (gx (exp (gen) x)) (bs-ltv bs-ltv) (as-ltv as-ltv) (y y))
  (defstrand init 3 (a a) (b b) (ca ca) (gB (exp (gen) bs-ltv))
    (gy (exp (gen) y)) (as-ltv as-ltv) (bs-ltv bs-ltv) (x x))
  (precedes ((0 1) (1 1)) ((1 0) (0 0)) ((1 2) (0 2)))
  (non-orig (privk ca))
  (uniq-orig bs-ltv as-ltv y x)
  (operation encryption-test (added-strand init 3)
    (enc "tag1"
      (cat (exp (gen) as-ltv)
        (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
        (exp (gen) x)) (exp (gen) bs-ltv)
      (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
      (exp (gen) y)
      (enc "hash"
        (cat (exp (exp (gen) bs-ltv) x) (exp (exp (gen) as-ltv) y))))
    (0 2))
  (traces
    ((recv
       (cat (exp (gen) as-ltv)
         (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (exp (gen) x)))
      (send
        (cat (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)))
      (recv
        (enc "tag1"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y)))))
      (send
        (enc "tag2"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y))))))
    ((send
       (cat (exp (gen) as-ltv)
         (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (exp (gen) x)))
      (recv
        (cat (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)))
      (send
        (enc "tag1"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y)))))))
  (label 25)
  (parent 24)
  (unrealized)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dh-cert
  (vars (ca a b name) (gA gx base) (bs-ltv as-ltv y expn))
  (defstrand resp 4 (a a) (b b) (ca ca) (gA gA) (gx gx) (bs-ltv bs-ltv)
    (as-ltv as-ltv) (y y))
  (deflistener (enc "hash" (cat (exp gx bs-ltv) (exp gA y))))
  (precedes ((1 1) (0 2)))
  (non-orig (privk ca))
  (uniq-orig bs-ltv y)
  (operation encryption-test
    (added-listener (enc "hash" (cat (exp gx bs-ltv) (exp gA y))))
    (enc "tag1"
      (cat gA (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca)) gx)
      (exp (gen) bs-ltv)
      (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
      (exp (gen) y) (enc "hash" (cat (exp gx bs-ltv) (exp gA y))))
    (0 2))
  (traces
    ((recv
       (cat gA (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         gx))
      (send
        (cat (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)))
      (recv
        (enc "tag1"
          (cat gA (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            gx) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y) (enc "hash" (cat (exp gx bs-ltv) (exp gA y)))))
      (send
        (enc "tag2"
          (cat gA (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            gx) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y) (enc "hash" (cat (exp gx bs-ltv) (exp gA y))))))
    ((recv (enc "hash" (cat (exp gx bs-ltv) (exp gA y))))
      (send (enc "hash" (cat (exp gx bs-ltv) (exp gA y))))))
  (label 26)
  (parent 24)
  (unrealized (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dh-cert
  (vars (ca a b name) (bs-ltv as-ltv y x expn))
  (defstrand resp 4 (a a) (b b) (ca ca) (gA (exp (gen) as-ltv))
    (gx (exp (gen) x)) (bs-ltv bs-ltv) (as-ltv as-ltv) (y y))
  (non-orig (privk ca))
  (uniq-orig bs-ltv as-ltv y x)
  (operation generalization deleted (1 0))
  (traces
    ((recv
       (cat (exp (gen) as-ltv)
         (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (exp (gen) x)))
      (send
        (cat (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)))
      (recv
        (enc "tag1"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y)))))
      (send
        (enc "tag2"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y)))))))
  (label 27)
  (parent 25)
  (unrealized)
  (origs (y (0 1)) (bs-ltv (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dh-cert
  (vars (ca a b name) (gA gx base) (bs-ltv as-ltv y expn))
  (defstrand resp 4 (a a) (b b) (ca ca) (gA gA) (gx gx) (bs-ltv bs-ltv)
    (as-ltv as-ltv) (y y))
  (deflistener (enc "hash" (cat (exp gx bs-ltv) (exp gA y))))
  (deflistener (cat (exp gx bs-ltv) (exp gA y)))
  (precedes ((0 1) (2 0)) ((1 1) (0 2)) ((2 1) (1 0)))
  (non-orig (privk ca))
  (uniq-orig bs-ltv y)
  (operation encryption-test
    (added-listener (cat (exp gx bs-ltv) (exp gA y)))
    (enc "hash" (cat (exp gx bs-ltv) (exp gA y))) (1 0))
  (traces
    ((recv
       (cat gA (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         gx))
      (send
        (cat (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)))
      (recv
        (enc "tag1"
          (cat gA (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            gx) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y) (enc "hash" (cat (exp gx bs-ltv) (exp gA y)))))
      (send
        (enc "tag2"
          (cat gA (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            gx) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y) (enc "hash" (cat (exp gx bs-ltv) (exp gA y))))))
    ((recv (enc "hash" (cat (exp gx bs-ltv) (exp gA y))))
      (send (enc "hash" (cat (exp gx bs-ltv) (exp gA y)))))
    ((recv (cat (exp gx bs-ltv) (exp gA y)))
      (send (cat (exp gx bs-ltv) (exp gA y)))))
  (label 28)
  (parent 26)
  (unrealized (2 0))
  (comment "3 in cohort - 3 not yet seen"))

(defskeleton dh-cert
  (vars (ca a b name) (bs-ltv as-ltv y x expn))
  (defstrand resp 4 (a a) (b b) (ca ca) (gA (exp (gen) as-ltv))
    (gx (exp (gen) x)) (bs-ltv bs-ltv) (as-ltv as-ltv) (y y))
  (non-orig (privk ca))
  (uniq-orig bs-ltv y x)
  (operation generalization forgot as-ltv)
  (traces
    ((recv
       (cat (exp (gen) as-ltv)
         (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (exp (gen) x)))
      (send
        (cat (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)))
      (recv
        (enc "tag1"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y)))))
      (send
        (enc "tag2"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y)))))))
  (label 29)
  (parent 27)
  (unrealized)
  (origs (y (0 1)) (bs-ltv (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dh-cert
  (vars (ca a b name) (gA base) (bs-ltv as-ltv y expn))
  (defstrand resp 4 (a a) (b b) (ca ca) (gA gA) (gx (gen))
    (bs-ltv bs-ltv) (as-ltv as-ltv) (y y))
  (deflistener (enc "hash" (cat (exp (gen) bs-ltv) (exp gA y))))
  (deflistener (cat (exp (gen) bs-ltv) (exp gA y)))
  (precedes ((0 1) (2 0)) ((1 1) (0 2)) ((2 1) (1 0)))
  (non-orig (privk ca))
  (uniq-orig bs-ltv y)
  (operation encryption-test (displaced 3 0 resp 2) (exp (gen) bs-ltv)
    (2 0))
  (traces
    ((recv
       (cat gA (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (gen)))
      (send
        (cat (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)))
      (recv
        (enc "tag1"
          (cat gA (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (gen)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash" (cat (exp (gen) bs-ltv) (exp gA y)))))
      (send
        (enc "tag2"
          (cat gA (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (gen)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash" (cat (exp (gen) bs-ltv) (exp gA y))))))
    ((recv (enc "hash" (cat (exp (gen) bs-ltv) (exp gA y))))
      (send (enc "hash" (cat (exp (gen) bs-ltv) (exp gA y)))))
    ((recv (cat (exp (gen) bs-ltv) (exp gA y)))
      (send (cat (exp (gen) bs-ltv) (exp gA y)))))
  (label 30)
  (parent 28)
  (unrealized (2 0))
  (comment "3 in cohort - 3 not yet seen"))

(defskeleton dh-cert
  (vars (ca a b name) (gA base) (bs-ltv as-ltv expn))
  (defstrand resp 4 (a a) (b b) (ca ca) (gA gA) (gx (gen))
    (bs-ltv bs-ltv) (as-ltv as-ltv) (y bs-ltv))
  (deflistener (enc "hash" (cat (exp (gen) bs-ltv) (exp gA bs-ltv))))
  (deflistener (cat (exp (gen) bs-ltv) (exp gA bs-ltv)))
  (precedes ((0 1) (2 0)) ((1 1) (0 2)) ((2 1) (1 0)))
  (non-orig (privk ca))
  (uniq-orig bs-ltv)
  (operation encryption-test (displaced 3 0 resp 2) (exp (gen) bs-ltv)
    (2 0))
  (traces
    ((recv
       (cat gA (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (gen)))
      (send
        (cat (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) bs-ltv)))
      (recv
        (enc "tag1"
          (cat gA (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (gen)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) bs-ltv)
          (enc "hash" (cat (exp (gen) bs-ltv) (exp gA bs-ltv)))))
      (send
        (enc "tag2"
          (cat gA (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (gen)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) bs-ltv)
          (enc "hash" (cat (exp (gen) bs-ltv) (exp gA bs-ltv))))))
    ((recv (enc "hash" (cat (exp (gen) bs-ltv) (exp gA bs-ltv))))
      (send (enc "hash" (cat (exp (gen) bs-ltv) (exp gA bs-ltv)))))
    ((recv (cat (exp (gen) bs-ltv) (exp gA bs-ltv)))
      (send (cat (exp (gen) bs-ltv) (exp gA bs-ltv)))))
  (label 31)
  (parent 28)
  (seen 34)
  (unrealized (2 0))
  (comment "3 in cohort - 1 not yet seen"))

(defskeleton dh-cert
  (vars (ca a b name) (gA gx base) (bs-ltv as-ltv y expn))
  (defstrand resp 4 (a a) (b b) (ca ca) (gA gA) (gx gx) (bs-ltv bs-ltv)
    (as-ltv as-ltv) (y y))
  (deflistener (enc "hash" (cat (exp gx bs-ltv) (exp gA y))))
  (deflistener (cat (exp gx bs-ltv) (exp gA y)))
  (deflistener bs-ltv)
  (precedes ((0 1) (3 0)) ((1 1) (0 2)) ((2 1) (1 0)) ((3 1) (2 0)))
  (non-orig (privk ca))
  (uniq-orig bs-ltv y)
  (operation encryption-test (added-listener bs-ltv) (exp gx bs-ltv)
    (2 0))
  (traces
    ((recv
       (cat gA (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         gx))
      (send
        (cat (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)))
      (recv
        (enc "tag1"
          (cat gA (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            gx) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y) (enc "hash" (cat (exp gx bs-ltv) (exp gA y)))))
      (send
        (enc "tag2"
          (cat gA (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            gx) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y) (enc "hash" (cat (exp gx bs-ltv) (exp gA y))))))
    ((recv (enc "hash" (cat (exp gx bs-ltv) (exp gA y))))
      (send (enc "hash" (cat (exp gx bs-ltv) (exp gA y)))))
    ((recv (cat (exp gx bs-ltv) (exp gA y)))
      (send (cat (exp gx bs-ltv) (exp gA y))))
    ((recv bs-ltv) (send bs-ltv)))
  (label 32)
  (parent 28)
  (unrealized (2 0) (3 0))
  (comment "empty cohort"))

(defskeleton dh-cert
  (vars (ca a b name) (bs-ltv as-ltv y x expn))
  (defstrand resp 4 (a a) (b b) (ca ca) (gA (exp (gen) as-ltv))
    (gx (exp (gen) x)) (bs-ltv bs-ltv) (as-ltv as-ltv) (y y))
  (non-orig (privk ca))
  (uniq-orig bs-ltv y)
  (operation generalization forgot x)
  (traces
    ((recv
       (cat (exp (gen) as-ltv)
         (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (exp (gen) x)))
      (send
        (cat (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)))
      (recv
        (enc "tag1"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y)))))
      (send
        (enc "tag2"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y)))))))
  (label 33)
  (parent 29)
  (unrealized)
  (origs (y (0 1)) (bs-ltv (0 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dh-cert
  (vars (ca a b name) (bs-ltv as-ltv expn))
  (defstrand resp 4 (a a) (b b) (ca ca) (gA (gen)) (gx (gen))
    (bs-ltv bs-ltv) (as-ltv as-ltv) (y bs-ltv))
  (deflistener (enc "hash" (cat (exp (gen) bs-ltv) (exp (gen) bs-ltv))))
  (deflistener (cat (exp (gen) bs-ltv) (exp (gen) bs-ltv)))
  (precedes ((0 1) (2 0)) ((1 1) (0 2)) ((2 1) (1 0)))
  (non-orig (privk ca))
  (uniq-orig bs-ltv)
  (operation encryption-test (displaced 3 0 resp 2) (exp (gen) y) (2 0))
  (traces
    ((recv
       (cat (gen) (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (gen)))
      (send
        (cat (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) bs-ltv)))
      (recv
        (enc "tag1"
          (cat (gen)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (gen)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) bs-ltv)
          (enc "hash" (cat (exp (gen) bs-ltv) (exp (gen) bs-ltv)))))
      (send
        (enc "tag2"
          (cat (gen)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (gen)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) bs-ltv)
          (enc "hash" (cat (exp (gen) bs-ltv) (exp (gen) bs-ltv))))))
    ((recv (enc "hash" (cat (exp (gen) bs-ltv) (exp (gen) bs-ltv))))
      (send (enc "hash" (cat (exp (gen) bs-ltv) (exp (gen) bs-ltv)))))
    ((recv (cat (exp (gen) bs-ltv) (exp (gen) bs-ltv)))
      (send (cat (exp (gen) bs-ltv) (exp (gen) bs-ltv)))))
  (label 34)
  (parent 30)
  (unrealized)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dh-cert
  (vars (ca a b name) (bs-ltv as-ltv y expn))
  (defstrand resp 4 (a a) (b b) (ca ca) (gA (gen)) (gx (gen))
    (bs-ltv bs-ltv) (as-ltv as-ltv) (y y))
  (deflistener (enc "hash" (cat (exp (gen) bs-ltv) (exp (gen) y))))
  (deflistener (cat (exp (gen) bs-ltv) (exp (gen) y)))
  (precedes ((0 1) (2 0)) ((1 1) (0 2)) ((2 1) (1 0)))
  (non-orig (privk ca))
  (uniq-orig bs-ltv y)
  (operation encryption-test (displaced 3 0 resp 2) (exp (gen) y) (2 0))
  (traces
    ((recv
       (cat (gen) (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (gen)))
      (send
        (cat (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)))
      (recv
        (enc "tag1"
          (cat (gen)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (gen)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash" (cat (exp (gen) bs-ltv) (exp (gen) y)))))
      (send
        (enc "tag2"
          (cat (gen)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (gen)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash" (cat (exp (gen) bs-ltv) (exp (gen) y))))))
    ((recv (enc "hash" (cat (exp (gen) bs-ltv) (exp (gen) y))))
      (send (enc "hash" (cat (exp (gen) bs-ltv) (exp (gen) y)))))
    ((recv (cat (exp (gen) bs-ltv) (exp (gen) y)))
      (send (cat (exp (gen) bs-ltv) (exp (gen) y)))))
  (label 35)
  (parent 30)
  (unrealized)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dh-cert
  (vars (ca a b name) (gA base) (bs-ltv as-ltv y expn))
  (defstrand resp 4 (a a) (b b) (ca ca) (gA gA) (gx (gen))
    (bs-ltv bs-ltv) (as-ltv as-ltv) (y y))
  (deflistener (enc "hash" (cat (exp (gen) bs-ltv) (exp gA y))))
  (deflistener (cat (exp (gen) bs-ltv) (exp gA y)))
  (deflistener y)
  (precedes ((0 1) (3 0)) ((1 1) (0 2)) ((2 1) (1 0)) ((3 1) (2 0)))
  (non-orig (privk ca))
  (uniq-orig bs-ltv y)
  (operation encryption-test (added-listener y) (exp gA y) (2 0))
  (traces
    ((recv
       (cat gA (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (gen)))
      (send
        (cat (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)))
      (recv
        (enc "tag1"
          (cat gA (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (gen)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash" (cat (exp (gen) bs-ltv) (exp gA y)))))
      (send
        (enc "tag2"
          (cat gA (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (gen)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash" (cat (exp (gen) bs-ltv) (exp gA y))))))
    ((recv (enc "hash" (cat (exp (gen) bs-ltv) (exp gA y))))
      (send (enc "hash" (cat (exp (gen) bs-ltv) (exp gA y)))))
    ((recv (cat (exp (gen) bs-ltv) (exp gA y)))
      (send (cat (exp (gen) bs-ltv) (exp gA y)))) ((recv y) (send y)))
  (label 36)
  (parent 30)
  (unrealized (3 0))
  (comment "empty cohort"))

(defskeleton dh-cert
  (vars (ca a b name) (gA base) (bs-ltv as-ltv expn))
  (defstrand resp 4 (a a) (b b) (ca ca) (gA gA) (gx (gen))
    (bs-ltv bs-ltv) (as-ltv as-ltv) (y bs-ltv))
  (deflistener (enc "hash" (cat (exp (gen) bs-ltv) (exp gA bs-ltv))))
  (deflistener (cat (exp (gen) bs-ltv) (exp gA bs-ltv)))
  (deflistener bs-ltv)
  (precedes ((0 1) (3 0)) ((1 1) (0 2)) ((2 1) (1 0)) ((3 1) (2 0)))
  (non-orig (privk ca))
  (uniq-orig bs-ltv)
  (operation encryption-test (added-listener bs-ltv) (exp gA bs-ltv)
    (2 0))
  (traces
    ((recv
       (cat gA (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (gen)))
      (send
        (cat (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) bs-ltv)))
      (recv
        (enc "tag1"
          (cat gA (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (gen)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) bs-ltv)
          (enc "hash" (cat (exp (gen) bs-ltv) (exp gA bs-ltv)))))
      (send
        (enc "tag2"
          (cat gA (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (gen)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) bs-ltv)
          (enc "hash" (cat (exp (gen) bs-ltv) (exp gA bs-ltv))))))
    ((recv (enc "hash" (cat (exp (gen) bs-ltv) (exp gA bs-ltv))))
      (send (enc "hash" (cat (exp (gen) bs-ltv) (exp gA bs-ltv)))))
    ((recv (cat (exp (gen) bs-ltv) (exp gA bs-ltv)))
      (send (cat (exp (gen) bs-ltv) (exp gA bs-ltv))))
    ((recv bs-ltv) (send bs-ltv)))
  (label 37)
  (parent 31)
  (unrealized (3 0))
  (comment "empty cohort"))

(defskeleton dh-cert
  (vars (ca a b name) (bs-ltv as-ltv y x as-ltv-0 expn))
  (defstrand resp 4 (a a) (b b) (ca ca) (gA (exp (gen) as-ltv))
    (gx (exp (gen) x)) (bs-ltv bs-ltv) (as-ltv as-ltv-0) (y y))
  (non-orig (privk ca))
  (uniq-orig bs-ltv y)
  (operation generalization separated as-ltv-0)
  (traces
    ((recv
       (cat (exp (gen) as-ltv)
         (enc "cert" a (exp (gen) as-ltv-0) (privk "certify" ca))
         (exp (gen) x)))
      (send
        (cat (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)))
      (recv
        (enc "tag1"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv-0) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y)))))
      (send
        (enc "tag2"
          (cat (exp (gen) as-ltv)
            (enc "cert" a (exp (gen) as-ltv-0) (privk "certify" ca))
            (exp (gen) x)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash"
            (cat (exp (exp (gen) bs-ltv) x)
              (exp (exp (gen) as-ltv) y)))))))
  (label 38)
  (parent 33)
  (unrealized)
  (shape)
  (maps
    ((0)
      ((ca ca) (a a) (b b) (bs-ltv bs-ltv) (as-ltv as-ltv-0) (y y)
        (gA (exp (gen) as-ltv)) (gx (exp (gen) x)))))
  (origs (y (0 1)) (bs-ltv (0 1))))

(defskeleton dh-cert
  (vars (ca a b name) (bs-ltv as-ltv expn))
  (defstrand resp 4 (a a) (b b) (ca ca) (gA (gen)) (gx (gen))
    (bs-ltv bs-ltv) (as-ltv as-ltv) (y bs-ltv))
  (deflistener (cat (exp (gen) bs-ltv) (exp (gen) bs-ltv)))
  (precedes ((0 1) (1 0)) ((1 1) (0 2)))
  (non-orig (privk ca))
  (uniq-orig bs-ltv)
  (operation generalization deleted (1 0))
  (traces
    ((recv
       (cat (gen) (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (gen)))
      (send
        (cat (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) bs-ltv)))
      (recv
        (enc "tag1"
          (cat (gen)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (gen)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) bs-ltv)
          (enc "hash" (cat (exp (gen) bs-ltv) (exp (gen) bs-ltv)))))
      (send
        (enc "tag2"
          (cat (gen)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (gen)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) bs-ltv)
          (enc "hash" (cat (exp (gen) bs-ltv) (exp (gen) bs-ltv))))))
    ((recv (cat (exp (gen) bs-ltv) (exp (gen) bs-ltv)))
      (send (cat (exp (gen) bs-ltv) (exp (gen) bs-ltv)))))
  (label 39)
  (parent 34)
  (unrealized)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dh-cert
  (vars (ca a b name) (bs-ltv as-ltv y expn))
  (defstrand resp 4 (a a) (b b) (ca ca) (gA (gen)) (gx (gen))
    (bs-ltv bs-ltv) (as-ltv as-ltv) (y y))
  (deflistener (cat (exp (gen) bs-ltv) (exp (gen) y)))
  (precedes ((0 1) (1 0)) ((1 1) (0 2)))
  (non-orig (privk ca))
  (uniq-orig bs-ltv y)
  (operation generalization deleted (1 0))
  (traces
    ((recv
       (cat (gen) (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (gen)))
      (send
        (cat (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)))
      (recv
        (enc "tag1"
          (cat (gen)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (gen)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash" (cat (exp (gen) bs-ltv) (exp (gen) y)))))
      (send
        (enc "tag2"
          (cat (gen)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (gen)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash" (cat (exp (gen) bs-ltv) (exp (gen) y))))))
    ((recv (cat (exp (gen) bs-ltv) (exp (gen) y)))
      (send (cat (exp (gen) bs-ltv) (exp (gen) y)))))
  (label 40)
  (parent 35)
  (unrealized)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton dh-cert
  (vars (ca a b name) (bs-ltv as-ltv expn))
  (defstrand resp 4 (a a) (b b) (ca ca) (gA (gen)) (gx (gen))
    (bs-ltv bs-ltv) (as-ltv as-ltv) (y bs-ltv))
  (non-orig (privk ca))
  (uniq-orig bs-ltv)
  (operation generalization deleted (1 0))
  (traces
    ((recv
       (cat (gen) (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (gen)))
      (send
        (cat (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) bs-ltv)))
      (recv
        (enc "tag1"
          (cat (gen)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (gen)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) bs-ltv)
          (enc "hash" (cat (exp (gen) bs-ltv) (exp (gen) bs-ltv)))))
      (send
        (enc "tag2"
          (cat (gen)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (gen)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) bs-ltv)
          (enc "hash" (cat (exp (gen) bs-ltv) (exp (gen) bs-ltv)))))))
  (label 41)
  (parent 39)
  (seen 42)
  (unrealized)
  (origs (bs-ltv (0 1)))
  (comment "1 in cohort - 0 not yet seen"))

(defskeleton dh-cert
  (vars (ca a b name) (bs-ltv as-ltv y expn))
  (defstrand resp 4 (a a) (b b) (ca ca) (gA (gen)) (gx (gen))
    (bs-ltv bs-ltv) (as-ltv as-ltv) (y y))
  (non-orig (privk ca))
  (uniq-orig bs-ltv y)
  (operation generalization deleted (1 0))
  (traces
    ((recv
       (cat (gen) (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
         (gen)))
      (send
        (cat (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)))
      (recv
        (enc "tag1"
          (cat (gen)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (gen)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash" (cat (exp (gen) bs-ltv) (exp (gen) y)))))
      (send
        (enc "tag2"
          (cat (gen)
            (enc "cert" a (exp (gen) as-ltv) (privk "certify" ca))
            (gen)) (exp (gen) bs-ltv)
          (enc "cert" b (exp (gen) bs-ltv) (privk "certify" ca))
          (exp (gen) y)
          (enc "hash" (cat (exp (gen) bs-ltv) (exp (gen) y)))))))
  (label 42)
  (parent 40)
  (unrealized)
  (shape)
  (maps
    ((0)
      ((ca ca) (a a) (b b) (bs-ltv bs-ltv) (as-ltv as-ltv) (y y)
        (gA (gen)) (gx (gen)))))
  (origs (bs-ltv (0 1)) (y (0 1))))

(comment "Nothing left to do")
