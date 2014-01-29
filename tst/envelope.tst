(herald "Envelope Protocol" (bound 20) (check-nonces))

(comment "CPSA 2.4.0")
(comment "All input read from envelope.scm")
(comment "Strand count bounded at 20")
(comment "Nonces checked first")

(defprotocol envelope basic
  (defrole tpm-power-on (vars) (trace (sync "boot")))
  (defrole tpm-quote
    (vars (nonce pcr mesg) (aik akey))
    (trace (recv (cat "quote" nonce)) (recv pcr)
      (sync (cat "observe" pcr)) (send (enc "quote" pcr nonce aik)))
    (non-orig aik)
    (priority (1 0)))
  (defrole tpm-extend-enc
    (vars (value mesg) (esk skey) (tne tno data) (tpmkey akey))
    (trace (recv (cat "establish transport" tpmkey (enc esk tpmkey)))
      (send (cat "establish transport" tne))
      (recv
        (cat "execute transport" (cat "extend" (enc value esk)) tno
          "false"
          (hash esk
            (hash "execute transport" (hash "extend" (enc value esk)))
            tne tno "false"))) (sync (cat "extend" value)))
    (non-orig (invk tpmkey))
    (uniq-orig tne))
  (defrole tpm-create-key
    (vars (k aik akey) (pcr mesg) (esk skey))
    (trace (recv (enc "create key" pcr esk))
      (send (enc "created" k pcr aik)))
    (non-orig esk aik (invk k))
    (uniq-orig k))
  (defrole tpm-decrypt
    (vars (m pcr mesg) (k aik akey))
    (trace (recv (cat "decrypt" (enc m k)))
      (recv (enc "created" k pcr aik)) (sync (cat "observe" pcr))
      (send m))
    (non-orig aik))
  (defrole alice
    (vars (v tne tno data) (esk1 esk skey) (k aik tpmkey akey) (n text)
      (pcr mesg))
    (trace (send (cat "establish transport" tpmkey (enc esk tpmkey)))
      (recv (cat "establish transport" tne))
      (send
        (cat "execute transport" (cat "extend" (enc n esk)) tno "false"
          (hash esk
            (hash "execute transport" (hash "extend" (enc n esk))) tne
            tno "false"))) (recv pcr)
      (send (enc "create key" (hash "obtain" (hash n pcr)) esk1))
      (recv (enc "created" k (hash "obtain" (hash n pcr)) aik))
      (send (enc v k)))
    (non-orig esk1 aik (invk tpmkey))
    (uniq-orig n v tno esk)))

(defskeleton envelope
  (vars (pcr mesg) (n text) (v tne tno data) (esk1 esk skey)
    (k aik tpmkey akey))
  (deflistener (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik))
  (deflistener v)
  (defstrand alice 7 (pcr pcr) (n n) (v v) (tne tne) (tno tno)
    (esk1 esk1) (esk esk) (k k) (aik aik) (tpmkey tpmkey))
  (non-orig esk1 aik (invk tpmkey))
  (uniq-orig n v tno esk)
  (traces
    ((recv (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik))
      (send (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik)))
    ((recv v) (send v))
    ((send (cat "establish transport" tpmkey (enc esk tpmkey)))
      (recv (cat "establish transport" tne))
      (send
        (cat "execute transport" (cat "extend" (enc n esk)) tno "false"
          (hash esk
            (hash "execute transport" (hash "extend" (enc n esk))) tne
            tno "false"))) (recv pcr)
      (send (enc "create key" (hash "obtain" (hash n pcr)) esk1))
      (recv (enc "created" k (hash "obtain" (hash n pcr)) aik))
      (send (enc v k))))
  (label 0)
  (unrealized (0 0) (1 0) (2 5))
  (preskeleton)
  (comment "Not a skeleton"))

(defskeleton envelope
  (vars (pcr mesg) (n text) (v tne tno data) (esk1 esk skey)
    (k aik tpmkey akey))
  (deflistener (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik))
  (deflistener v)
  (defstrand alice 7 (pcr pcr) (n n) (v v) (tne tne) (tno tno)
    (esk1 esk1) (esk esk) (k k) (aik aik) (tpmkey tpmkey))
  (precedes ((2 6) (0 0)) ((2 6) (1 0)))
  (non-orig esk1 aik (invk tpmkey))
  (uniq-orig n v tno esk)
  (traces
    ((recv (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik))
      (send (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik)))
    ((recv v) (send v))
    ((send (cat "establish transport" tpmkey (enc esk tpmkey)))
      (recv (cat "establish transport" tne))
      (send
        (cat "execute transport" (cat "extend" (enc n esk)) tno "false"
          (hash esk
            (hash "execute transport" (hash "extend" (enc n esk))) tne
            tno "false"))) (recv pcr)
      (send (enc "create key" (hash "obtain" (hash n pcr)) esk1))
      (recv (enc "created" k (hash "obtain" (hash n pcr)) aik))
      (send (enc v k))))
  (label 1)
  (parent 0)
  (unrealized (0 0) (2 5))
  (origs (esk (2 0)) (tno (2 2)) (v (2 6)) (n (2 2)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton envelope
  (vars (pcr mesg) (n text) (v tne tno data) (esk1 esk esk-0 skey)
    (k aik tpmkey akey))
  (deflistener (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik))
  (deflistener v)
  (defstrand alice 7 (pcr pcr) (n n) (v v) (tne tne) (tno tno)
    (esk1 esk1) (esk esk) (k k) (aik aik) (tpmkey tpmkey))
  (defstrand tpm-create-key 2 (pcr (hash "obtain" (hash n pcr)))
    (esk esk-0) (k k) (aik aik))
  (precedes ((2 6) (0 0)) ((2 6) (1 0)) ((3 1) (2 5)))
  (non-orig esk1 esk-0 aik (invk k) (invk tpmkey))
  (uniq-orig n v tno esk k)
  (operation encryption-test (added-strand tpm-create-key 2)
    (enc "created" k (hash "obtain" (hash n pcr)) aik) (2 5))
  (traces
    ((recv (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik))
      (send (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik)))
    ((recv v) (send v))
    ((send (cat "establish transport" tpmkey (enc esk tpmkey)))
      (recv (cat "establish transport" tne))
      (send
        (cat "execute transport" (cat "extend" (enc n esk)) tno "false"
          (hash esk
            (hash "execute transport" (hash "extend" (enc n esk))) tne
            tno "false"))) (recv pcr)
      (send (enc "create key" (hash "obtain" (hash n pcr)) esk1))
      (recv (enc "created" k (hash "obtain" (hash n pcr)) aik))
      (send (enc v k)))
    ((recv (enc "create key" (hash "obtain" (hash n pcr)) esk-0))
      (send (enc "created" k (hash "obtain" (hash n pcr)) aik))))
  (label 2)
  (parent 1)
  (unrealized (0 0) (1 0) (3 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton envelope
  (vars (pcr mesg) (n text) (v tne tno data) (esk1 esk skey)
    (k aik tpmkey akey))
  (deflistener (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik))
  (deflistener v)
  (defstrand alice 7 (pcr pcr) (n n) (v v) (tne tne) (tno tno)
    (esk1 esk1) (esk esk) (k k) (aik aik) (tpmkey tpmkey))
  (defstrand tpm-create-key 2 (pcr (hash "obtain" (hash n pcr)))
    (esk esk1) (k k) (aik aik))
  (precedes ((2 4) (3 0)) ((2 6) (0 0)) ((2 6) (1 0)) ((3 1) (2 5)))
  (non-orig esk1 aik (invk k) (invk tpmkey))
  (uniq-orig n v tno esk k)
  (operation encryption-test (displaced 4 2 alice 5)
    (enc "create key" (hash "obtain" (hash n pcr)) esk-0) (3 0))
  (traces
    ((recv (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik))
      (send (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik)))
    ((recv v) (send v))
    ((send (cat "establish transport" tpmkey (enc esk tpmkey)))
      (recv (cat "establish transport" tne))
      (send
        (cat "execute transport" (cat "extend" (enc n esk)) tno "false"
          (hash esk
            (hash "execute transport" (hash "extend" (enc n esk))) tne
            tno "false"))) (recv pcr)
      (send (enc "create key" (hash "obtain" (hash n pcr)) esk1))
      (recv (enc "created" k (hash "obtain" (hash n pcr)) aik))
      (send (enc v k)))
    ((recv (enc "create key" (hash "obtain" (hash n pcr)) esk1))
      (send (enc "created" k (hash "obtain" (hash n pcr)) aik))))
  (label 3)
  (parent 2)
  (unrealized (0 0) (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton envelope
  (vars (pcr pcr-0 mesg) (n text) (v tne tno data) (esk1 esk skey)
    (k aik tpmkey aik-0 akey))
  (deflistener (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik))
  (deflistener v)
  (defstrand alice 7 (pcr pcr) (n n) (v v) (tne tne) (tno tno)
    (esk1 esk1) (esk esk) (k k) (aik aik) (tpmkey tpmkey))
  (defstrand tpm-create-key 2 (pcr (hash "obtain" (hash n pcr)))
    (esk esk1) (k k) (aik aik))
  (defstrand tpm-decrypt 4 (m v) (pcr pcr-0) (k k) (aik aik-0))
  (precedes ((2 4) (3 0)) ((2 6) (0 0)) ((2 6) (4 0)) ((3 1) (2 5))
    ((4 3) (1 0)))
  (non-orig esk1 aik aik-0 (invk k) (invk tpmkey))
  (uniq-orig n v tno esk k)
  (operation nonce-test (added-strand tpm-decrypt 4) v (1 0) (enc v k))
  (traces
    ((recv (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik))
      (send (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik)))
    ((recv v) (send v))
    ((send (cat "establish transport" tpmkey (enc esk tpmkey)))
      (recv (cat "establish transport" tne))
      (send
        (cat "execute transport" (cat "extend" (enc n esk)) tno "false"
          (hash esk
            (hash "execute transport" (hash "extend" (enc n esk))) tne
            tno "false"))) (recv pcr)
      (send (enc "create key" (hash "obtain" (hash n pcr)) esk1))
      (recv (enc "created" k (hash "obtain" (hash n pcr)) aik))
      (send (enc v k)))
    ((recv (enc "create key" (hash "obtain" (hash n pcr)) esk1))
      (send (enc "created" k (hash "obtain" (hash n pcr)) aik)))
    ((recv (cat "decrypt" (enc v k)))
      (recv (enc "created" k pcr-0 aik-0)) (sync (cat "observe" pcr-0))
      (send v)))
  (label 4)
  (parent 3)
  (unrealized (0 0) (4 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton envelope
  (vars (pcr mesg) (n text) (v tne tno data) (esk1 esk skey)
    (k aik tpmkey akey))
  (deflistener (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik))
  (deflistener v)
  (defstrand alice 7 (pcr pcr) (n n) (v v) (tne tne) (tno tno)
    (esk1 esk1) (esk esk) (k k) (aik aik) (tpmkey tpmkey))
  (defstrand tpm-create-key 2 (pcr (hash "obtain" (hash n pcr)))
    (esk esk1) (k k) (aik aik))
  (defstrand tpm-decrypt 4 (m v) (pcr (hash "obtain" (hash n pcr)))
    (k k) (aik aik))
  (precedes ((2 4) (3 0)) ((2 6) (0 0)) ((2 6) (4 0)) ((3 1) (2 5))
    ((4 3) (1 0)))
  (non-orig esk1 aik (invk k) (invk tpmkey))
  (uniq-orig n v tno esk k)
  (operation encryption-test (displaced 5 3 tpm-create-key 2)
    (enc "created" k pcr-0 aik-0) (4 1))
  (traces
    ((recv (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik))
      (send (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik)))
    ((recv v) (send v))
    ((send (cat "establish transport" tpmkey (enc esk tpmkey)))
      (recv (cat "establish transport" tne))
      (send
        (cat "execute transport" (cat "extend" (enc n esk)) tno "false"
          (hash esk
            (hash "execute transport" (hash "extend" (enc n esk))) tne
            tno "false"))) (recv pcr)
      (send (enc "create key" (hash "obtain" (hash n pcr)) esk1))
      (recv (enc "created" k (hash "obtain" (hash n pcr)) aik))
      (send (enc v k)))
    ((recv (enc "create key" (hash "obtain" (hash n pcr)) esk1))
      (send (enc "created" k (hash "obtain" (hash n pcr)) aik)))
    ((recv (cat "decrypt" (enc v k)))
      (recv (enc "created" k (hash "obtain" (hash n pcr)) aik))
      (sync (cat "observe" (hash "obtain" (hash n pcr)))) (send v)))
  (label 5)
  (parent 4)
  (unrealized (0 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton envelope
  (vars (pcr mesg) (n text) (v tne tno data) (esk1 esk skey)
    (k aik tpmkey akey))
  (deflistener (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik))
  (deflistener v)
  (defstrand alice 7 (pcr pcr) (n n) (v v) (tne tne) (tno tno)
    (esk1 esk1) (esk esk) (k k) (aik aik) (tpmkey tpmkey))
  (defstrand tpm-create-key 2 (pcr (hash "obtain" (hash n pcr)))
    (esk esk1) (k k) (aik aik))
  (defstrand tpm-decrypt 4 (m v) (pcr (hash "obtain" (hash n pcr)))
    (k k) (aik aik))
  (defstrand tpm-quote 4 (nonce (enc v k))
    (pcr (hash "refuse" (hash n pcr))) (aik aik))
  (precedes ((2 4) (3 0)) ((2 6) (4 0)) ((2 6) (5 0)) ((3 1) (2 5))
    ((4 3) (1 0)) ((5 3) (0 0)))
  (non-orig esk1 aik (invk k) (invk tpmkey))
  (uniq-orig n v tno esk k)
  (operation encryption-test (added-strand tpm-quote 4)
    (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik) (0 0))
  (traces
    ((recv (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik))
      (send (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik)))
    ((recv v) (send v))
    ((send (cat "establish transport" tpmkey (enc esk tpmkey)))
      (recv (cat "establish transport" tne))
      (send
        (cat "execute transport" (cat "extend" (enc n esk)) tno "false"
          (hash esk
            (hash "execute transport" (hash "extend" (enc n esk))) tne
            tno "false"))) (recv pcr)
      (send (enc "create key" (hash "obtain" (hash n pcr)) esk1))
      (recv (enc "created" k (hash "obtain" (hash n pcr)) aik))
      (send (enc v k)))
    ((recv (enc "create key" (hash "obtain" (hash n pcr)) esk1))
      (send (enc "created" k (hash "obtain" (hash n pcr)) aik)))
    ((recv (cat "decrypt" (enc v k)))
      (recv (enc "created" k (hash "obtain" (hash n pcr)) aik))
      (sync (cat "observe" (hash "obtain" (hash n pcr)))) (send v))
    ((recv (cat "quote" (enc v k))) (recv (hash "refuse" (hash n pcr)))
      (sync (cat "observe" (hash "refuse" (hash n pcr))))
      (send (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik))))
  (label 6)
  (parent 5)
  (unrealized (5 1))
  (comment "empty cohort"))

(comment "Nothing left to do")
