(herald "Envelope Protocol" (bound 20))

(comment "CPSA 2.4.0")
(comment "All input read from envelope.scm")
(comment "Strand count bounded at 20")

(defprotocol envelope basic
  (defrole tpm-power-on (vars) (trace (sync "boot")))
  (defrole tpm-quote
    (vars (nonce pcr mesg) (aik akey))
    (trace (recv (cat "quote" nonce)) (sync (cat "observe" pcr))
      (send (enc "quote" pcr nonce aik)))
    (non-orig aik))
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
  (defstrand tpm-quote 3 (nonce (enc v k))
    (pcr (hash "refuse" (hash n pcr))) (aik aik))
  (precedes ((2 4) (3 0)) ((2 6) (4 0)) ((2 6) (5 0)) ((3 1) (2 5))
    ((4 3) (1 0)) ((5 2) (0 0)))
  (non-orig esk1 aik (invk k) (invk tpmkey))
  (uniq-orig n v tno esk k)
  (operation encryption-test (added-strand tpm-quote 3)
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
    ((recv (cat "quote" (enc v k)))
      (sync (cat "observe" (hash "refuse" (hash n pcr))))
      (send (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik))))
  (label 6)
  (parent 5)
  (unrealized)
  (shape)
  (maps
    ((0 1 2)
      ((v v) (k k) (aik aik) (n n) (pcr pcr) (tne tne) (tno tno)
        (esk1 esk1) (esk esk) (tpmkey tpmkey))))
  (origs (k (3 1)) (n (2 2)) (tno (2 2)) (esk (2 0)) (v (2 6))))

(comment "Nothing left to do")

(defprotocol envelope basic
  (defrole tpm-power-on (vars) (trace (sync "boot")))
  (defrole tpm-quote
    (vars (nonce pcr mesg) (aik akey))
    (trace (recv (cat "quote" nonce)) (sync (cat "observe" pcr))
      (send (enc "quote" pcr nonce aik)))
    (non-orig aik))
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
  (vars (pcr mesg) (n text) (v tne tno tne-0 tno-0 tne-1 tno-1 data)
    (esk1 esk esk-0 esk-1 skey) (k aik tpmkey tpmkey-0 tpmkey-1 akey))
  (deflistener (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik))
  (deflistener v)
  (defstrand alice 7 (pcr pcr) (n n) (v v) (tne tne) (tno tno)
    (esk1 esk1) (esk esk) (k k) (aik aik) (tpmkey tpmkey))
  (defstrand tpm-create-key 2 (pcr (hash "obtain" (hash n pcr)))
    (esk esk1) (k k) (aik aik))
  (defstrand tpm-decrypt 4 (m v) (pcr (hash "obtain" (hash n pcr)))
    (k k) (aik aik))
  (defstrand tpm-quote 3 (nonce (enc v k))
    (pcr (hash "refuse" (hash n pcr))) (aik aik))
  (defstrand tpm-extend-enc 4 (value n) (tne tne-0) (tno tno-0)
    (esk esk-0) (tpmkey tpmkey-0))
  (defstrand tpm-extend-enc 4 (value n) (tne tne-1) (tno tno-1)
    (esk esk-1) (tpmkey tpmkey-1))
  (precedes ((2 4) (3 0)) ((2 6) (4 0)) ((2 6) (5 0)) ((3 1) (2 5))
    ((4 3) (1 0)) ((5 2) (0 0)) ((6 3) (7 3)))
  (non-orig esk1 aik (invk k) (invk tpmkey) (invk tpmkey-0)
    (invk tpmkey-1))
  (uniq-orig n v tno tne-0 tne-1 esk k)
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
    ((recv (cat "quote" (enc v k)))
      (sync (cat "observe" (hash "refuse" (hash n pcr))))
      (send (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik)))
    ((recv (cat "establish transport" tpmkey-0 (enc esk-0 tpmkey-0)))
      (send (cat "establish transport" tne-0))
      (recv
        (cat "execute transport" (cat "extend" (enc n esk-0)) tno-0
          "false"
          (hash esk-0
            (hash "execute transport" (hash "extend" (enc n esk-0)))
            tne-0 tno-0 "false"))) (sync (cat "extend" n)))
    ((recv (cat "establish transport" tpmkey-1 (enc esk-1 tpmkey-1)))
      (send (cat "establish transport" tne-1))
      (recv
        (cat "execute transport" (cat "extend" (enc n esk-1)) tno-1
          "false"
          (hash esk-1
            (hash "execute transport" (hash "extend" (enc n esk-1)))
            tne-1 tno-1 "false"))) (sync (cat "extend" n))))
  (label 7)
  (unrealized (6 2) (7 2))
  (preskeleton)
  (comment "Not a skeleton"))

(defskeleton envelope
  (vars (pcr mesg) (n text) (v tne tno tne-0 tno-0 tne-1 tno-1 data)
    (esk1 esk esk-0 esk-1 skey) (k aik tpmkey tpmkey-0 tpmkey-1 akey))
  (deflistener (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik))
  (deflistener v)
  (defstrand alice 7 (pcr pcr) (n n) (v v) (tne tne) (tno tno)
    (esk1 esk1) (esk esk) (k k) (aik aik) (tpmkey tpmkey))
  (defstrand tpm-create-key 2 (pcr (hash "obtain" (hash n pcr)))
    (esk esk1) (k k) (aik aik))
  (defstrand tpm-decrypt 4 (m v) (pcr (hash "obtain" (hash n pcr)))
    (k k) (aik aik))
  (defstrand tpm-quote 3 (nonce (enc v k))
    (pcr (hash "refuse" (hash n pcr))) (aik aik))
  (defstrand tpm-extend-enc 4 (value n) (tne tne-0) (tno tno-0)
    (esk esk-0) (tpmkey tpmkey-0))
  (defstrand tpm-extend-enc 4 (value n) (tne tne-1) (tno tno-1)
    (esk esk-1) (tpmkey tpmkey-1))
  (precedes ((2 2) (6 2)) ((2 2) (7 2)) ((2 4) (3 0)) ((2 6) (4 0))
    ((2 6) (5 0)) ((3 1) (2 5)) ((4 3) (1 0)) ((5 2) (0 0))
    ((6 3) (7 3)))
  (non-orig esk1 aik (invk k) (invk tpmkey) (invk tpmkey-0)
    (invk tpmkey-1))
  (uniq-orig n v tno tne-0 tne-1 esk k)
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
    ((recv (cat "quote" (enc v k)))
      (sync (cat "observe" (hash "refuse" (hash n pcr))))
      (send (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik)))
    ((recv (cat "establish transport" tpmkey-0 (enc esk-0 tpmkey-0)))
      (send (cat "establish transport" tne-0))
      (recv
        (cat "execute transport" (cat "extend" (enc n esk-0)) tno-0
          "false"
          (hash esk-0
            (hash "execute transport" (hash "extend" (enc n esk-0)))
            tne-0 tno-0 "false"))) (sync (cat "extend" n)))
    ((recv (cat "establish transport" tpmkey-1 (enc esk-1 tpmkey-1)))
      (send (cat "establish transport" tne-1))
      (recv
        (cat "execute transport" (cat "extend" (enc n esk-1)) tno-1
          "false"
          (hash esk-1
            (hash "execute transport" (hash "extend" (enc n esk-1)))
            tne-1 tno-1 "false"))) (sync (cat "extend" n))))
  (label 8)
  (parent 7)
  (unrealized (6 2) (7 2))
  (origs (tne-1 (7 1)) (tne-0 (6 1)) (n (2 2)) (v (2 6)) (tno (2 2))
    (esk (2 0)) (k (3 1)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton envelope
  (vars (pcr mesg) (n text) (v tne tno tne-0 tno-0 data)
    (esk1 esk esk-0 skey) (k aik tpmkey tpmkey-0 tpmkey-1 akey))
  (deflistener (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik))
  (deflistener v)
  (defstrand alice 7 (pcr pcr) (n n) (v v) (tne tne) (tno tno)
    (esk1 esk1) (esk esk) (k k) (aik aik) (tpmkey tpmkey))
  (defstrand tpm-create-key 2 (pcr (hash "obtain" (hash n pcr)))
    (esk esk1) (k k) (aik aik))
  (defstrand tpm-decrypt 4 (m v) (pcr (hash "obtain" (hash n pcr)))
    (k k) (aik aik))
  (defstrand tpm-quote 3 (nonce (enc v k))
    (pcr (hash "refuse" (hash n pcr))) (aik aik))
  (defstrand tpm-extend-enc 4 (value n) (tne tne-0) (tno tno-0)
    (esk esk-0) (tpmkey tpmkey-0))
  (defstrand tpm-extend-enc 4 (value n) (tne tne) (tno tno) (esk esk)
    (tpmkey tpmkey-1))
  (precedes ((2 0) (7 0)) ((2 2) (6 2)) ((2 2) (7 2)) ((2 4) (3 0))
    ((2 6) (4 0)) ((2 6) (5 0)) ((3 1) (2 5)) ((4 3) (1 0))
    ((5 2) (0 0)) ((6 3) (7 3)) ((7 1) (2 1)))
  (non-orig esk1 aik (invk k) (invk tpmkey) (invk tpmkey-0)
    (invk tpmkey-1))
  (uniq-orig n v tne tno tne-0 esk k)
  (operation encryption-test (displaced 8 2 alice 3)
    (hash esk-1 (hash "execute transport" (hash "extend" (enc n esk-1)))
      tne-1 tno-1 "false") (7 2))
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
    ((recv (cat "quote" (enc v k)))
      (sync (cat "observe" (hash "refuse" (hash n pcr))))
      (send (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik)))
    ((recv (cat "establish transport" tpmkey-0 (enc esk-0 tpmkey-0)))
      (send (cat "establish transport" tne-0))
      (recv
        (cat "execute transport" (cat "extend" (enc n esk-0)) tno-0
          "false"
          (hash esk-0
            (hash "execute transport" (hash "extend" (enc n esk-0)))
            tne-0 tno-0 "false"))) (sync (cat "extend" n)))
    ((recv (cat "establish transport" tpmkey-1 (enc esk tpmkey-1)))
      (send (cat "establish transport" tne))
      (recv
        (cat "execute transport" (cat "extend" (enc n esk)) tno "false"
          (hash esk
            (hash "execute transport" (hash "extend" (enc n esk))) tne
            tno "false"))) (sync (cat "extend" n))))
  (label 9)
  (parent 8)
  (unrealized (6 2) (7 0))
  (origs (n (2 2)) (tno (2 2)) (esk (2 0)) (tne (7 1)) (tne-0 (6 1))
    (v (2 6)) (k (3 1)))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton envelope
  (vars (pcr mesg) (n text) (v tne tno tne-0 tno-0 tne-1 tno-1 data)
    (esk1 esk esk-0 esk-1 skey) (k aik tpmkey tpmkey-0 tpmkey-1 akey))
  (deflistener (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik))
  (deflistener v)
  (defstrand alice 7 (pcr pcr) (n n) (v v) (tne tne) (tno tno)
    (esk1 esk1) (esk esk) (k k) (aik aik) (tpmkey tpmkey))
  (defstrand tpm-create-key 2 (pcr (hash "obtain" (hash n pcr)))
    (esk esk1) (k k) (aik aik))
  (defstrand tpm-decrypt 4 (m v) (pcr (hash "obtain" (hash n pcr)))
    (k k) (aik aik))
  (defstrand tpm-quote 3 (nonce (enc v k))
    (pcr (hash "refuse" (hash n pcr))) (aik aik))
  (defstrand tpm-extend-enc 4 (value n) (tne tne-0) (tno tno-0)
    (esk esk-0) (tpmkey tpmkey-0))
  (defstrand tpm-extend-enc 4 (value n) (tne tne-1) (tno tno-1)
    (esk esk-1) (tpmkey tpmkey-1))
  (deflistener
    (cat esk-1 (hash "execute transport" (hash "extend" (enc n esk-1)))
      tne-1 tno-1 "false"))
  (precedes ((2 2) (6 2)) ((2 2) (7 2)) ((2 4) (3 0)) ((2 6) (4 0))
    ((2 6) (5 0)) ((3 1) (2 5)) ((4 3) (1 0)) ((5 2) (0 0))
    ((6 3) (7 3)) ((7 1) (8 0)) ((8 1) (7 2)))
  (non-orig esk1 aik (invk k) (invk tpmkey) (invk tpmkey-0)
    (invk tpmkey-1))
  (uniq-orig n v tno tne-0 tne-1 esk k)
  (operation encryption-test
    (added-listener
      (cat esk-1
        (hash "execute transport" (hash "extend" (enc n esk-1))) tne-1
        tno-1 "false"))
    (hash esk-1 (hash "execute transport" (hash "extend" (enc n esk-1)))
      tne-1 tno-1 "false") (7 2))
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
    ((recv (cat "quote" (enc v k)))
      (sync (cat "observe" (hash "refuse" (hash n pcr))))
      (send (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik)))
    ((recv (cat "establish transport" tpmkey-0 (enc esk-0 tpmkey-0)))
      (send (cat "establish transport" tne-0))
      (recv
        (cat "execute transport" (cat "extend" (enc n esk-0)) tno-0
          "false"
          (hash esk-0
            (hash "execute transport" (hash "extend" (enc n esk-0)))
            tne-0 tno-0 "false"))) (sync (cat "extend" n)))
    ((recv (cat "establish transport" tpmkey-1 (enc esk-1 tpmkey-1)))
      (send (cat "establish transport" tne-1))
      (recv
        (cat "execute transport" (cat "extend" (enc n esk-1)) tno-1
          "false"
          (hash esk-1
            (hash "execute transport" (hash "extend" (enc n esk-1)))
            tne-1 tno-1 "false"))) (sync (cat "extend" n)))
    ((recv
       (cat esk-1
         (hash "execute transport" (hash "extend" (enc n esk-1))) tne-1
         tno-1 "false"))
      (send
        (cat esk-1
          (hash "execute transport" (hash "extend" (enc n esk-1))) tne-1
          tno-1 "false"))))
  (label 10)
  (parent 8)
  (unrealized (6 2) (7 2) (8 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton envelope
  (vars (pcr mesg) (n text) (v tne tno tne-0 tno-0 data)
    (esk1 esk esk-0 skey) (k aik tpmkey tpmkey-0 akey))
  (deflistener (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik))
  (deflistener v)
  (defstrand alice 7 (pcr pcr) (n n) (v v) (tne tne) (tno tno)
    (esk1 esk1) (esk esk) (k k) (aik aik) (tpmkey tpmkey))
  (defstrand tpm-create-key 2 (pcr (hash "obtain" (hash n pcr)))
    (esk esk1) (k k) (aik aik))
  (defstrand tpm-decrypt 4 (m v) (pcr (hash "obtain" (hash n pcr)))
    (k k) (aik aik))
  (defstrand tpm-quote 3 (nonce (enc v k))
    (pcr (hash "refuse" (hash n pcr))) (aik aik))
  (defstrand tpm-extend-enc 4 (value n) (tne tne-0) (tno tno-0)
    (esk esk-0) (tpmkey tpmkey-0))
  (defstrand tpm-extend-enc 4 (value n) (tne tne) (tno tno) (esk esk)
    (tpmkey tpmkey))
  (precedes ((2 0) (7 0)) ((2 2) (6 2)) ((2 2) (7 2)) ((2 4) (3 0))
    ((2 6) (4 0)) ((2 6) (5 0)) ((3 1) (2 5)) ((4 3) (1 0))
    ((5 2) (0 0)) ((6 3) (7 3)) ((7 1) (2 1)))
  (non-orig esk1 aik (invk k) (invk tpmkey) (invk tpmkey-0))
  (uniq-orig n v tne tno tne-0 esk k)
  (operation nonce-test (contracted (tpmkey-1 tpmkey)) esk (7 0)
    (enc esk tpmkey))
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
    ((recv (cat "quote" (enc v k)))
      (sync (cat "observe" (hash "refuse" (hash n pcr))))
      (send (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik)))
    ((recv (cat "establish transport" tpmkey-0 (enc esk-0 tpmkey-0)))
      (send (cat "establish transport" tne-0))
      (recv
        (cat "execute transport" (cat "extend" (enc n esk-0)) tno-0
          "false"
          (hash esk-0
            (hash "execute transport" (hash "extend" (enc n esk-0)))
            tne-0 tno-0 "false"))) (sync (cat "extend" n)))
    ((recv (cat "establish transport" tpmkey (enc esk tpmkey)))
      (send (cat "establish transport" tne))
      (recv
        (cat "execute transport" (cat "extend" (enc n esk)) tno "false"
          (hash esk
            (hash "execute transport" (hash "extend" (enc n esk))) tne
            tno "false"))) (sync (cat "extend" n))))
  (label 11)
  (parent 9)
  (unrealized (6 2))
  (origs (n (2 2)) (tno (2 2)) (esk (2 0)) (tne (7 1)) (tne-0 (6 1))
    (v (2 6)) (k (3 1)))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton envelope
  (vars (pcr pcr-0 mesg) (n text) (v tne tno tne-0 tno-0 data)
    (esk1 esk esk-0 skey) (k aik tpmkey tpmkey-0 tpmkey-1 aik-0 akey))
  (deflistener (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik))
  (deflistener v)
  (defstrand alice 7 (pcr pcr) (n n) (v v) (tne tne) (tno tno)
    (esk1 esk1) (esk esk) (k k) (aik aik) (tpmkey tpmkey))
  (defstrand tpm-create-key 2 (pcr (hash "obtain" (hash n pcr)))
    (esk esk1) (k k) (aik aik))
  (defstrand tpm-decrypt 4 (m v) (pcr (hash "obtain" (hash n pcr)))
    (k k) (aik aik))
  (defstrand tpm-quote 3 (nonce (enc v k))
    (pcr (hash "refuse" (hash n pcr))) (aik aik))
  (defstrand tpm-extend-enc 4 (value n) (tne tne-0) (tno tno-0)
    (esk esk-0) (tpmkey tpmkey-0))
  (defstrand tpm-extend-enc 4 (value n) (tne tne) (tno tno) (esk esk)
    (tpmkey tpmkey-1))
  (defstrand tpm-decrypt 4 (m esk) (pcr pcr-0) (k tpmkey) (aik aik-0))
  (precedes ((2 0) (8 0)) ((2 2) (6 2)) ((2 2) (7 2)) ((2 4) (3 0))
    ((2 6) (4 0)) ((2 6) (5 0)) ((3 1) (2 5)) ((4 3) (1 0))
    ((5 2) (0 0)) ((6 3) (7 3)) ((7 1) (2 1)) ((8 3) (7 0)))
  (non-orig esk1 aik aik-0 (invk k) (invk tpmkey) (invk tpmkey-0)
    (invk tpmkey-1))
  (uniq-orig n v tne tno tne-0 esk k)
  (operation nonce-test (added-strand tpm-decrypt 4) esk (7 0)
    (enc esk tpmkey))
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
    ((recv (cat "quote" (enc v k)))
      (sync (cat "observe" (hash "refuse" (hash n pcr))))
      (send (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik)))
    ((recv (cat "establish transport" tpmkey-0 (enc esk-0 tpmkey-0)))
      (send (cat "establish transport" tne-0))
      (recv
        (cat "execute transport" (cat "extend" (enc n esk-0)) tno-0
          "false"
          (hash esk-0
            (hash "execute transport" (hash "extend" (enc n esk-0)))
            tne-0 tno-0 "false"))) (sync (cat "extend" n)))
    ((recv (cat "establish transport" tpmkey-1 (enc esk tpmkey-1)))
      (send (cat "establish transport" tne))
      (recv
        (cat "execute transport" (cat "extend" (enc n esk)) tno "false"
          (hash esk
            (hash "execute transport" (hash "extend" (enc n esk))) tne
            tno "false"))) (sync (cat "extend" n)))
    ((recv (cat "decrypt" (enc esk tpmkey)))
      (recv (enc "created" tpmkey pcr-0 aik-0))
      (sync (cat "observe" pcr-0)) (send esk)))
  (label 12)
  (parent 9)
  (unrealized (8 1))
  (comment "empty cohort"))

(defskeleton envelope
  (vars (pcr mesg) (n text) (v tne tno tne-0 tno-0 tne-1 tno-1 data)
    (esk1 esk esk-0 esk-1 skey) (k aik tpmkey tpmkey-0 tpmkey-1 akey))
  (deflistener (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik))
  (deflistener v)
  (defstrand alice 7 (pcr pcr) (n n) (v v) (tne tne) (tno tno)
    (esk1 esk1) (esk esk) (k k) (aik aik) (tpmkey tpmkey))
  (defstrand tpm-create-key 2 (pcr (hash "obtain" (hash n pcr)))
    (esk esk1) (k k) (aik aik))
  (defstrand tpm-decrypt 4 (m v) (pcr (hash "obtain" (hash n pcr)))
    (k k) (aik aik))
  (defstrand tpm-quote 3 (nonce (enc v k))
    (pcr (hash "refuse" (hash n pcr))) (aik aik))
  (defstrand tpm-extend-enc 4 (value n) (tne tne-0) (tno tno-0)
    (esk esk-0) (tpmkey tpmkey-0))
  (defstrand tpm-extend-enc 4 (value n) (tne tne-1) (tno tno-1)
    (esk esk-1) (tpmkey tpmkey-1))
  (deflistener
    (cat esk-1 (hash "execute transport" (hash "extend" (enc n esk-1)))
      tne-1 tno-1 "false"))
  (deflistener (cat "execute transport" (hash "extend" (enc n esk-1))))
  (precedes ((2 2) (6 2)) ((2 2) (7 2)) ((2 4) (3 0)) ((2 6) (4 0))
    ((2 6) (5 0)) ((3 1) (2 5)) ((4 3) (1 0)) ((5 2) (0 0))
    ((6 3) (7 3)) ((7 1) (8 0)) ((8 1) (7 2)) ((9 1) (8 0)))
  (non-orig esk1 aik (invk k) (invk tpmkey) (invk tpmkey-0)
    (invk tpmkey-1))
  (uniq-orig n v tno tne-0 tne-1 esk k)
  (operation encryption-test
    (added-listener
      (cat "execute transport" (hash "extend" (enc n esk-1))))
    (hash "execute transport" (hash "extend" (enc n esk-1))) (8 0))
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
    ((recv (cat "quote" (enc v k)))
      (sync (cat "observe" (hash "refuse" (hash n pcr))))
      (send (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik)))
    ((recv (cat "establish transport" tpmkey-0 (enc esk-0 tpmkey-0)))
      (send (cat "establish transport" tne-0))
      (recv
        (cat "execute transport" (cat "extend" (enc n esk-0)) tno-0
          "false"
          (hash esk-0
            (hash "execute transport" (hash "extend" (enc n esk-0)))
            tne-0 tno-0 "false"))) (sync (cat "extend" n)))
    ((recv (cat "establish transport" tpmkey-1 (enc esk-1 tpmkey-1)))
      (send (cat "establish transport" tne-1))
      (recv
        (cat "execute transport" (cat "extend" (enc n esk-1)) tno-1
          "false"
          (hash esk-1
            (hash "execute transport" (hash "extend" (enc n esk-1)))
            tne-1 tno-1 "false"))) (sync (cat "extend" n)))
    ((recv
       (cat esk-1
         (hash "execute transport" (hash "extend" (enc n esk-1))) tne-1
         tno-1 "false"))
      (send
        (cat esk-1
          (hash "execute transport" (hash "extend" (enc n esk-1))) tne-1
          tno-1 "false")))
    ((recv (cat "execute transport" (hash "extend" (enc n esk-1))))
      (send (cat "execute transport" (hash "extend" (enc n esk-1))))))
  (label 13)
  (parent 10)
  (unrealized (6 2) (7 2) (9 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton envelope
  (vars (pcr mesg) (n text) (v tne tno tne-0 tno-0 data)
    (esk1 esk esk-0 skey) (k aik tpmkey tpmkey-0 akey))
  (deflistener (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik))
  (deflistener v)
  (defstrand alice 7 (pcr pcr) (n n) (v v) (tne tne) (tno tno)
    (esk1 esk1) (esk esk) (k k) (aik aik) (tpmkey tpmkey))
  (defstrand tpm-create-key 2 (pcr (hash "obtain" (hash n pcr)))
    (esk esk1) (k k) (aik aik))
  (defstrand tpm-decrypt 4 (m v) (pcr (hash "obtain" (hash n pcr)))
    (k k) (aik aik))
  (defstrand tpm-quote 3 (nonce (enc v k))
    (pcr (hash "refuse" (hash n pcr))) (aik aik))
  (defstrand tpm-extend-enc 4 (value n) (tne tne-0) (tno tno-0)
    (esk esk-0) (tpmkey tpmkey-0))
  (defstrand tpm-extend-enc 4 (value n) (tne tne) (tno tno) (esk esk)
    (tpmkey tpmkey))
  (deflistener
    (cat esk-0 (hash "execute transport" (hash "extend" (enc n esk-0)))
      tne-0 tno-0 "false"))
  (precedes ((2 0) (7 0)) ((2 2) (6 2)) ((2 2) (7 2)) ((2 4) (3 0))
    ((2 6) (4 0)) ((2 6) (5 0)) ((3 1) (2 5)) ((4 3) (1 0))
    ((5 2) (0 0)) ((6 1) (8 0)) ((6 3) (7 3)) ((7 1) (2 1))
    ((8 1) (6 2)))
  (non-orig esk1 aik (invk k) (invk tpmkey) (invk tpmkey-0))
  (uniq-orig n v tne tno tne-0 esk k)
  (operation encryption-test
    (added-listener
      (cat esk-0
        (hash "execute transport" (hash "extend" (enc n esk-0))) tne-0
        tno-0 "false"))
    (hash esk-0 (hash "execute transport" (hash "extend" (enc n esk-0)))
      tne-0 tno-0 "false") (6 2))
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
    ((recv (cat "quote" (enc v k)))
      (sync (cat "observe" (hash "refuse" (hash n pcr))))
      (send (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik)))
    ((recv (cat "establish transport" tpmkey-0 (enc esk-0 tpmkey-0)))
      (send (cat "establish transport" tne-0))
      (recv
        (cat "execute transport" (cat "extend" (enc n esk-0)) tno-0
          "false"
          (hash esk-0
            (hash "execute transport" (hash "extend" (enc n esk-0)))
            tne-0 tno-0 "false"))) (sync (cat "extend" n)))
    ((recv (cat "establish transport" tpmkey (enc esk tpmkey)))
      (send (cat "establish transport" tne))
      (recv
        (cat "execute transport" (cat "extend" (enc n esk)) tno "false"
          (hash esk
            (hash "execute transport" (hash "extend" (enc n esk))) tne
            tno "false"))) (sync (cat "extend" n)))
    ((recv
       (cat esk-0
         (hash "execute transport" (hash "extend" (enc n esk-0))) tne-0
         tno-0 "false"))
      (send
        (cat esk-0
          (hash "execute transport" (hash "extend" (enc n esk-0))) tne-0
          tno-0 "false"))))
  (label 14)
  (parent 11)
  (unrealized (6 2) (8 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton envelope
  (vars (pcr mesg) (n text) (v tne tno tne-0 tno-0 tne-1 tno-1 data)
    (esk1 esk esk-0 esk-1 skey) (k aik tpmkey tpmkey-0 tpmkey-1 akey))
  (deflistener (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik))
  (deflistener v)
  (defstrand alice 7 (pcr pcr) (n n) (v v) (tne tne) (tno tno)
    (esk1 esk1) (esk esk) (k k) (aik aik) (tpmkey tpmkey))
  (defstrand tpm-create-key 2 (pcr (hash "obtain" (hash n pcr)))
    (esk esk1) (k k) (aik aik))
  (defstrand tpm-decrypt 4 (m v) (pcr (hash "obtain" (hash n pcr)))
    (k k) (aik aik))
  (defstrand tpm-quote 3 (nonce (enc v k))
    (pcr (hash "refuse" (hash n pcr))) (aik aik))
  (defstrand tpm-extend-enc 4 (value n) (tne tne-0) (tno tno-0)
    (esk esk-0) (tpmkey tpmkey-0))
  (defstrand tpm-extend-enc 4 (value n) (tne tne-1) (tno tno-1)
    (esk esk-1) (tpmkey tpmkey-1))
  (deflistener
    (cat esk-1 (hash "execute transport" (hash "extend" (enc n esk-1)))
      tne-1 tno-1 "false"))
  (deflistener (cat "execute transport" (hash "extend" (enc n esk-1))))
  (deflistener (cat "extend" (enc n esk-1)))
  (precedes ((2 2) (6 2)) ((2 2) (10 0)) ((2 4) (3 0)) ((2 6) (4 0))
    ((2 6) (5 0)) ((3 1) (2 5)) ((4 3) (1 0)) ((5 2) (0 0))
    ((6 3) (7 3)) ((7 1) (8 0)) ((8 1) (7 2)) ((9 1) (8 0))
    ((10 1) (9 0)))
  (non-orig esk1 aik (invk k) (invk tpmkey) (invk tpmkey-0)
    (invk tpmkey-1))
  (uniq-orig n v tno tne-0 tne-1 esk k)
  (operation encryption-test
    (added-listener (cat "extend" (enc n esk-1)))
    (hash "extend" (enc n esk-1)) (9 0))
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
    ((recv (cat "quote" (enc v k)))
      (sync (cat "observe" (hash "refuse" (hash n pcr))))
      (send (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik)))
    ((recv (cat "establish transport" tpmkey-0 (enc esk-0 tpmkey-0)))
      (send (cat "establish transport" tne-0))
      (recv
        (cat "execute transport" (cat "extend" (enc n esk-0)) tno-0
          "false"
          (hash esk-0
            (hash "execute transport" (hash "extend" (enc n esk-0)))
            tne-0 tno-0 "false"))) (sync (cat "extend" n)))
    ((recv (cat "establish transport" tpmkey-1 (enc esk-1 tpmkey-1)))
      (send (cat "establish transport" tne-1))
      (recv
        (cat "execute transport" (cat "extend" (enc n esk-1)) tno-1
          "false"
          (hash esk-1
            (hash "execute transport" (hash "extend" (enc n esk-1)))
            tne-1 tno-1 "false"))) (sync (cat "extend" n)))
    ((recv
       (cat esk-1
         (hash "execute transport" (hash "extend" (enc n esk-1))) tne-1
         tno-1 "false"))
      (send
        (cat esk-1
          (hash "execute transport" (hash "extend" (enc n esk-1))) tne-1
          tno-1 "false")))
    ((recv (cat "execute transport" (hash "extend" (enc n esk-1))))
      (send (cat "execute transport" (hash "extend" (enc n esk-1)))))
    ((recv (cat "extend" (enc n esk-1)))
      (send (cat "extend" (enc n esk-1)))))
  (label 15)
  (parent 13)
  (unrealized (6 2) (10 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton envelope
  (vars (pcr mesg) (n text) (v tne tno tne-0 tno-0 data)
    (esk1 esk esk-0 skey) (k aik tpmkey tpmkey-0 akey))
  (deflistener (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik))
  (deflistener v)
  (defstrand alice 7 (pcr pcr) (n n) (v v) (tne tne) (tno tno)
    (esk1 esk1) (esk esk) (k k) (aik aik) (tpmkey tpmkey))
  (defstrand tpm-create-key 2 (pcr (hash "obtain" (hash n pcr)))
    (esk esk1) (k k) (aik aik))
  (defstrand tpm-decrypt 4 (m v) (pcr (hash "obtain" (hash n pcr)))
    (k k) (aik aik))
  (defstrand tpm-quote 3 (nonce (enc v k))
    (pcr (hash "refuse" (hash n pcr))) (aik aik))
  (defstrand tpm-extend-enc 4 (value n) (tne tne-0) (tno tno-0)
    (esk esk-0) (tpmkey tpmkey-0))
  (defstrand tpm-extend-enc 4 (value n) (tne tne) (tno tno) (esk esk)
    (tpmkey tpmkey))
  (deflistener
    (cat esk-0 (hash "execute transport" (hash "extend" (enc n esk-0)))
      tne-0 tno-0 "false"))
  (deflistener (cat "execute transport" (hash "extend" (enc n esk-0))))
  (precedes ((2 0) (7 0)) ((2 2) (6 2)) ((2 2) (7 2)) ((2 4) (3 0))
    ((2 6) (4 0)) ((2 6) (5 0)) ((3 1) (2 5)) ((4 3) (1 0))
    ((5 2) (0 0)) ((6 1) (8 0)) ((6 3) (7 3)) ((7 1) (2 1))
    ((8 1) (6 2)) ((9 1) (8 0)))
  (non-orig esk1 aik (invk k) (invk tpmkey) (invk tpmkey-0))
  (uniq-orig n v tne tno tne-0 esk k)
  (operation encryption-test
    (added-listener
      (cat "execute transport" (hash "extend" (enc n esk-0))))
    (hash "execute transport" (hash "extend" (enc n esk-0))) (8 0))
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
    ((recv (cat "quote" (enc v k)))
      (sync (cat "observe" (hash "refuse" (hash n pcr))))
      (send (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik)))
    ((recv (cat "establish transport" tpmkey-0 (enc esk-0 tpmkey-0)))
      (send (cat "establish transport" tne-0))
      (recv
        (cat "execute transport" (cat "extend" (enc n esk-0)) tno-0
          "false"
          (hash esk-0
            (hash "execute transport" (hash "extend" (enc n esk-0)))
            tne-0 tno-0 "false"))) (sync (cat "extend" n)))
    ((recv (cat "establish transport" tpmkey (enc esk tpmkey)))
      (send (cat "establish transport" tne))
      (recv
        (cat "execute transport" (cat "extend" (enc n esk)) tno "false"
          (hash esk
            (hash "execute transport" (hash "extend" (enc n esk))) tne
            tno "false"))) (sync (cat "extend" n)))
    ((recv
       (cat esk-0
         (hash "execute transport" (hash "extend" (enc n esk-0))) tne-0
         tno-0 "false"))
      (send
        (cat esk-0
          (hash "execute transport" (hash "extend" (enc n esk-0))) tne-0
          tno-0 "false")))
    ((recv (cat "execute transport" (hash "extend" (enc n esk-0))))
      (send (cat "execute transport" (hash "extend" (enc n esk-0))))))
  (label 16)
  (parent 14)
  (unrealized (6 2) (9 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton envelope
  (vars (pcr mesg) (n text) (v tne tno tne-0 tno-0 tne-1 tno-1 data)
    (esk1 esk esk-0 skey) (k aik tpmkey tpmkey-0 tpmkey-1 akey))
  (deflistener (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik))
  (deflistener v)
  (defstrand alice 7 (pcr pcr) (n n) (v v) (tne tne) (tno tno)
    (esk1 esk1) (esk esk) (k k) (aik aik) (tpmkey tpmkey))
  (defstrand tpm-create-key 2 (pcr (hash "obtain" (hash n pcr)))
    (esk esk1) (k k) (aik aik))
  (defstrand tpm-decrypt 4 (m v) (pcr (hash "obtain" (hash n pcr)))
    (k k) (aik aik))
  (defstrand tpm-quote 3 (nonce (enc v k))
    (pcr (hash "refuse" (hash n pcr))) (aik aik))
  (defstrand tpm-extend-enc 4 (value n) (tne tne-0) (tno tno-0)
    (esk esk-0) (tpmkey tpmkey-0))
  (defstrand tpm-extend-enc 4 (value n) (tne tne-1) (tno tno-1)
    (esk esk) (tpmkey tpmkey-1))
  (deflistener
    (cat esk (hash "execute transport" (hash "extend" (enc n esk)))
      tne-1 tno-1 "false"))
  (deflistener (cat "execute transport" (hash "extend" (enc n esk))))
  (deflistener (cat "extend" (enc n esk)))
  (precedes ((2 0) (7 0)) ((2 2) (6 2)) ((2 2) (10 0)) ((2 4) (3 0))
    ((2 6) (4 0)) ((2 6) (5 0)) ((3 1) (2 5)) ((4 3) (1 0))
    ((5 2) (0 0)) ((6 3) (7 3)) ((7 1) (8 0)) ((8 1) (7 2))
    ((9 1) (8 0)) ((10 1) (9 0)))
  (non-orig esk1 aik (invk k) (invk tpmkey) (invk tpmkey-0)
    (invk tpmkey-1))
  (uniq-orig n v tno tne-0 tne-1 esk k)
  (operation nonce-test (contracted (esk-1 esk)) n (10 0) (enc n esk))
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
    ((recv (cat "quote" (enc v k)))
      (sync (cat "observe" (hash "refuse" (hash n pcr))))
      (send (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik)))
    ((recv (cat "establish transport" tpmkey-0 (enc esk-0 tpmkey-0)))
      (send (cat "establish transport" tne-0))
      (recv
        (cat "execute transport" (cat "extend" (enc n esk-0)) tno-0
          "false"
          (hash esk-0
            (hash "execute transport" (hash "extend" (enc n esk-0)))
            tne-0 tno-0 "false"))) (sync (cat "extend" n)))
    ((recv (cat "establish transport" tpmkey-1 (enc esk tpmkey-1)))
      (send (cat "establish transport" tne-1))
      (recv
        (cat "execute transport" (cat "extend" (enc n esk)) tno-1
          "false"
          (hash esk
            (hash "execute transport" (hash "extend" (enc n esk))) tne-1
            tno-1 "false"))) (sync (cat "extend" n)))
    ((recv
       (cat esk (hash "execute transport" (hash "extend" (enc n esk)))
         tne-1 tno-1 "false"))
      (send
        (cat esk (hash "execute transport" (hash "extend" (enc n esk)))
          tne-1 tno-1 "false")))
    ((recv (cat "execute transport" (hash "extend" (enc n esk))))
      (send (cat "execute transport" (hash "extend" (enc n esk)))))
    ((recv (cat "extend" (enc n esk)))
      (send (cat "extend" (enc n esk)))))
  (label 17)
  (parent 15)
  (unrealized (6 2) (7 0) (8 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton envelope
  (vars (pcr mesg) (n text) (v tne tno tne-0 tno-0 tne-1 tno-1 data)
    (esk1 esk esk-0 esk-1 skey) (k aik tpmkey tpmkey-0 tpmkey-1 akey))
  (deflistener (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik))
  (deflistener v)
  (defstrand alice 7 (pcr pcr) (n n) (v v) (tne tne) (tno tno)
    (esk1 esk1) (esk esk) (k k) (aik aik) (tpmkey tpmkey))
  (defstrand tpm-create-key 2 (pcr (hash "obtain" (hash n pcr)))
    (esk esk1) (k k) (aik aik))
  (defstrand tpm-decrypt 4 (m v) (pcr (hash "obtain" (hash n pcr)))
    (k k) (aik aik))
  (defstrand tpm-quote 3 (nonce (enc v k))
    (pcr (hash "refuse" (hash n pcr))) (aik aik))
  (defstrand tpm-extend-enc 4 (value n) (tne tne-0) (tno tno-0)
    (esk esk-0) (tpmkey tpmkey-0))
  (defstrand tpm-extend-enc 4 (value n) (tne tne-1) (tno tno-1)
    (esk esk-1) (tpmkey tpmkey-1))
  (deflistener
    (cat esk-1 (hash "execute transport" (hash "extend" (enc n esk-1)))
      tne-1 tno-1 "false"))
  (deflistener (cat "execute transport" (hash "extend" (enc n esk-1))))
  (deflistener (cat "extend" (enc n esk-1)))
  (deflistener esk)
  (precedes ((2 0) (11 0)) ((2 2) (6 2)) ((2 2) (10 0)) ((2 4) (3 0))
    ((2 6) (4 0)) ((2 6) (5 0)) ((3 1) (2 5)) ((4 3) (1 0))
    ((5 2) (0 0)) ((6 3) (7 3)) ((7 1) (8 0)) ((8 1) (7 2))
    ((9 1) (8 0)) ((10 1) (9 0)) ((11 1) (10 0)))
  (non-orig esk1 aik (invk k) (invk tpmkey) (invk tpmkey-0)
    (invk tpmkey-1))
  (uniq-orig n v tno tne-0 tne-1 esk k)
  (operation nonce-test (added-listener esk) n (10 0) (enc n esk))
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
    ((recv (cat "quote" (enc v k)))
      (sync (cat "observe" (hash "refuse" (hash n pcr))))
      (send (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik)))
    ((recv (cat "establish transport" tpmkey-0 (enc esk-0 tpmkey-0)))
      (send (cat "establish transport" tne-0))
      (recv
        (cat "execute transport" (cat "extend" (enc n esk-0)) tno-0
          "false"
          (hash esk-0
            (hash "execute transport" (hash "extend" (enc n esk-0)))
            tne-0 tno-0 "false"))) (sync (cat "extend" n)))
    ((recv (cat "establish transport" tpmkey-1 (enc esk-1 tpmkey-1)))
      (send (cat "establish transport" tne-1))
      (recv
        (cat "execute transport" (cat "extend" (enc n esk-1)) tno-1
          "false"
          (hash esk-1
            (hash "execute transport" (hash "extend" (enc n esk-1)))
            tne-1 tno-1 "false"))) (sync (cat "extend" n)))
    ((recv
       (cat esk-1
         (hash "execute transport" (hash "extend" (enc n esk-1))) tne-1
         tno-1 "false"))
      (send
        (cat esk-1
          (hash "execute transport" (hash "extend" (enc n esk-1))) tne-1
          tno-1 "false")))
    ((recv (cat "execute transport" (hash "extend" (enc n esk-1))))
      (send (cat "execute transport" (hash "extend" (enc n esk-1)))))
    ((recv (cat "extend" (enc n esk-1)))
      (send (cat "extend" (enc n esk-1)))) ((recv esk) (send esk)))
  (label 18)
  (parent 15)
  (unrealized (6 2) (11 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton envelope
  (vars (pcr mesg) (n text) (v tne tno tne-0 tno-0 data)
    (esk1 esk esk-0 skey) (k aik tpmkey tpmkey-0 akey))
  (deflistener (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik))
  (deflistener v)
  (defstrand alice 7 (pcr pcr) (n n) (v v) (tne tne) (tno tno)
    (esk1 esk1) (esk esk) (k k) (aik aik) (tpmkey tpmkey))
  (defstrand tpm-create-key 2 (pcr (hash "obtain" (hash n pcr)))
    (esk esk1) (k k) (aik aik))
  (defstrand tpm-decrypt 4 (m v) (pcr (hash "obtain" (hash n pcr)))
    (k k) (aik aik))
  (defstrand tpm-quote 3 (nonce (enc v k))
    (pcr (hash "refuse" (hash n pcr))) (aik aik))
  (defstrand tpm-extend-enc 4 (value n) (tne tne-0) (tno tno-0)
    (esk esk-0) (tpmkey tpmkey-0))
  (defstrand tpm-extend-enc 4 (value n) (tne tne) (tno tno) (esk esk)
    (tpmkey tpmkey))
  (deflistener
    (cat esk-0 (hash "execute transport" (hash "extend" (enc n esk-0)))
      tne-0 tno-0 "false"))
  (deflistener (cat "execute transport" (hash "extend" (enc n esk-0))))
  (deflistener (cat "extend" (enc n esk-0)))
  (precedes ((2 0) (7 0)) ((2 2) (7 2)) ((2 2) (10 0)) ((2 4) (3 0))
    ((2 6) (4 0)) ((2 6) (5 0)) ((3 1) (2 5)) ((4 3) (1 0))
    ((5 2) (0 0)) ((6 1) (8 0)) ((6 3) (7 3)) ((7 1) (2 1))
    ((8 1) (6 2)) ((9 1) (8 0)) ((10 1) (9 0)))
  (non-orig esk1 aik (invk k) (invk tpmkey) (invk tpmkey-0))
  (uniq-orig n v tne tno tne-0 esk k)
  (operation encryption-test
    (added-listener (cat "extend" (enc n esk-0)))
    (hash "extend" (enc n esk-0)) (9 0))
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
    ((recv (cat "quote" (enc v k)))
      (sync (cat "observe" (hash "refuse" (hash n pcr))))
      (send (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik)))
    ((recv (cat "establish transport" tpmkey-0 (enc esk-0 tpmkey-0)))
      (send (cat "establish transport" tne-0))
      (recv
        (cat "execute transport" (cat "extend" (enc n esk-0)) tno-0
          "false"
          (hash esk-0
            (hash "execute transport" (hash "extend" (enc n esk-0)))
            tne-0 tno-0 "false"))) (sync (cat "extend" n)))
    ((recv (cat "establish transport" tpmkey (enc esk tpmkey)))
      (send (cat "establish transport" tne))
      (recv
        (cat "execute transport" (cat "extend" (enc n esk)) tno "false"
          (hash esk
            (hash "execute transport" (hash "extend" (enc n esk))) tne
            tno "false"))) (sync (cat "extend" n)))
    ((recv
       (cat esk-0
         (hash "execute transport" (hash "extend" (enc n esk-0))) tne-0
         tno-0 "false"))
      (send
        (cat esk-0
          (hash "execute transport" (hash "extend" (enc n esk-0))) tne-0
          tno-0 "false")))
    ((recv (cat "execute transport" (hash "extend" (enc n esk-0))))
      (send (cat "execute transport" (hash "extend" (enc n esk-0)))))
    ((recv (cat "extend" (enc n esk-0)))
      (send (cat "extend" (enc n esk-0)))))
  (label 19)
  (parent 16)
  (unrealized (10 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton envelope
  (vars (pcr pcr-0 mesg) (n text)
    (v tne tno tne-0 tno-0 tne-1 tno-1 data) (esk1 esk esk-0 skey)
    (k aik tpmkey tpmkey-0 tpmkey-1 aik-0 akey))
  (deflistener (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik))
  (deflistener v)
  (defstrand alice 7 (pcr pcr) (n n) (v v) (tne tne) (tno tno)
    (esk1 esk1) (esk esk) (k k) (aik aik) (tpmkey tpmkey))
  (defstrand tpm-create-key 2 (pcr (hash "obtain" (hash n pcr)))
    (esk esk1) (k k) (aik aik))
  (defstrand tpm-decrypt 4 (m v) (pcr (hash "obtain" (hash n pcr)))
    (k k) (aik aik))
  (defstrand tpm-quote 3 (nonce (enc v k))
    (pcr (hash "refuse" (hash n pcr))) (aik aik))
  (defstrand tpm-extend-enc 4 (value n) (tne tne-0) (tno tno-0)
    (esk esk-0) (tpmkey tpmkey-0))
  (defstrand tpm-extend-enc 4 (value n) (tne tne-1) (tno tno-1)
    (esk esk) (tpmkey tpmkey-1))
  (deflistener
    (cat esk (hash "execute transport" (hash "extend" (enc n esk)))
      tne-1 tno-1 "false"))
  (deflistener (cat "execute transport" (hash "extend" (enc n esk))))
  (deflistener (cat "extend" (enc n esk)))
  (defstrand tpm-decrypt 4 (m esk) (pcr pcr-0) (k tpmkey) (aik aik-0))
  (precedes ((2 0) (7 0)) ((2 0) (11 0)) ((2 2) (6 2)) ((2 2) (10 0))
    ((2 4) (3 0)) ((2 6) (4 0)) ((2 6) (5 0)) ((3 1) (2 5))
    ((4 3) (1 0)) ((5 2) (0 0)) ((6 3) (7 3)) ((7 1) (8 0))
    ((8 1) (7 2)) ((9 1) (8 0)) ((10 1) (9 0)) ((11 3) (8 0)))
  (non-orig esk1 aik aik-0 (invk k) (invk tpmkey) (invk tpmkey-0)
    (invk tpmkey-1))
  (uniq-orig n v tno tne-0 tne-1 esk k)
  (operation nonce-test (added-strand tpm-decrypt 4) esk (8 0)
    (enc esk tpmkey))
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
    ((recv (cat "quote" (enc v k)))
      (sync (cat "observe" (hash "refuse" (hash n pcr))))
      (send (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik)))
    ((recv (cat "establish transport" tpmkey-0 (enc esk-0 tpmkey-0)))
      (send (cat "establish transport" tne-0))
      (recv
        (cat "execute transport" (cat "extend" (enc n esk-0)) tno-0
          "false"
          (hash esk-0
            (hash "execute transport" (hash "extend" (enc n esk-0)))
            tne-0 tno-0 "false"))) (sync (cat "extend" n)))
    ((recv (cat "establish transport" tpmkey-1 (enc esk tpmkey-1)))
      (send (cat "establish transport" tne-1))
      (recv
        (cat "execute transport" (cat "extend" (enc n esk)) tno-1
          "false"
          (hash esk
            (hash "execute transport" (hash "extend" (enc n esk))) tne-1
            tno-1 "false"))) (sync (cat "extend" n)))
    ((recv
       (cat esk (hash "execute transport" (hash "extend" (enc n esk)))
         tne-1 tno-1 "false"))
      (send
        (cat esk (hash "execute transport" (hash "extend" (enc n esk)))
          tne-1 tno-1 "false")))
    ((recv (cat "execute transport" (hash "extend" (enc n esk))))
      (send (cat "execute transport" (hash "extend" (enc n esk)))))
    ((recv (cat "extend" (enc n esk)))
      (send (cat "extend" (enc n esk))))
    ((recv (cat "decrypt" (enc esk tpmkey)))
      (recv (enc "created" tpmkey pcr-0 aik-0))
      (sync (cat "observe" pcr-0)) (send esk)))
  (label 20)
  (parent 17)
  (unrealized (6 2) (7 0) (11 1))
  (comment "empty cohort"))

(defskeleton envelope
  (vars (pcr pcr-0 mesg) (n text)
    (v tne tno tne-0 tno-0 tne-1 tno-1 data) (esk1 esk esk-0 esk-1 skey)
    (k aik tpmkey tpmkey-0 tpmkey-1 aik-0 akey))
  (deflistener (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik))
  (deflistener v)
  (defstrand alice 7 (pcr pcr) (n n) (v v) (tne tne) (tno tno)
    (esk1 esk1) (esk esk) (k k) (aik aik) (tpmkey tpmkey))
  (defstrand tpm-create-key 2 (pcr (hash "obtain" (hash n pcr)))
    (esk esk1) (k k) (aik aik))
  (defstrand tpm-decrypt 4 (m v) (pcr (hash "obtain" (hash n pcr)))
    (k k) (aik aik))
  (defstrand tpm-quote 3 (nonce (enc v k))
    (pcr (hash "refuse" (hash n pcr))) (aik aik))
  (defstrand tpm-extend-enc 4 (value n) (tne tne-0) (tno tno-0)
    (esk esk-0) (tpmkey tpmkey-0))
  (defstrand tpm-extend-enc 4 (value n) (tne tne-1) (tno tno-1)
    (esk esk-1) (tpmkey tpmkey-1))
  (deflistener
    (cat esk-1 (hash "execute transport" (hash "extend" (enc n esk-1)))
      tne-1 tno-1 "false"))
  (deflistener (cat "execute transport" (hash "extend" (enc n esk-1))))
  (deflistener (cat "extend" (enc n esk-1)))
  (deflistener esk)
  (defstrand tpm-decrypt 4 (m esk) (pcr pcr-0) (k tpmkey) (aik aik-0))
  (precedes ((2 0) (12 0)) ((2 2) (6 2)) ((2 2) (10 0)) ((2 4) (3 0))
    ((2 6) (4 0)) ((2 6) (5 0)) ((3 1) (2 5)) ((4 3) (1 0))
    ((5 2) (0 0)) ((6 3) (7 3)) ((7 1) (8 0)) ((8 1) (7 2))
    ((9 1) (8 0)) ((10 1) (9 0)) ((11 1) (10 0)) ((12 3) (11 0)))
  (non-orig esk1 aik aik-0 (invk k) (invk tpmkey) (invk tpmkey-0)
    (invk tpmkey-1))
  (uniq-orig n v tno tne-0 tne-1 esk k)
  (operation nonce-test (added-strand tpm-decrypt 4) esk (11 0)
    (enc esk tpmkey))
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
    ((recv (cat "quote" (enc v k)))
      (sync (cat "observe" (hash "refuse" (hash n pcr))))
      (send (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik)))
    ((recv (cat "establish transport" tpmkey-0 (enc esk-0 tpmkey-0)))
      (send (cat "establish transport" tne-0))
      (recv
        (cat "execute transport" (cat "extend" (enc n esk-0)) tno-0
          "false"
          (hash esk-0
            (hash "execute transport" (hash "extend" (enc n esk-0)))
            tne-0 tno-0 "false"))) (sync (cat "extend" n)))
    ((recv (cat "establish transport" tpmkey-1 (enc esk-1 tpmkey-1)))
      (send (cat "establish transport" tne-1))
      (recv
        (cat "execute transport" (cat "extend" (enc n esk-1)) tno-1
          "false"
          (hash esk-1
            (hash "execute transport" (hash "extend" (enc n esk-1)))
            tne-1 tno-1 "false"))) (sync (cat "extend" n)))
    ((recv
       (cat esk-1
         (hash "execute transport" (hash "extend" (enc n esk-1))) tne-1
         tno-1 "false"))
      (send
        (cat esk-1
          (hash "execute transport" (hash "extend" (enc n esk-1))) tne-1
          tno-1 "false")))
    ((recv (cat "execute transport" (hash "extend" (enc n esk-1))))
      (send (cat "execute transport" (hash "extend" (enc n esk-1)))))
    ((recv (cat "extend" (enc n esk-1)))
      (send (cat "extend" (enc n esk-1)))) ((recv esk) (send esk))
    ((recv (cat "decrypt" (enc esk tpmkey)))
      (recv (enc "created" tpmkey pcr-0 aik-0))
      (sync (cat "observe" pcr-0)) (send esk)))
  (label 21)
  (parent 18)
  (unrealized (6 2) (12 1))
  (comment "empty cohort"))

(defskeleton envelope
  (vars (pcr mesg) (n text) (v tne tno tne-0 tno-0 data) (esk1 esk skey)
    (k aik tpmkey tpmkey-0 akey))
  (deflistener (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik))
  (deflistener v)
  (defstrand alice 7 (pcr pcr) (n n) (v v) (tne tne) (tno tno)
    (esk1 esk1) (esk esk) (k k) (aik aik) (tpmkey tpmkey))
  (defstrand tpm-create-key 2 (pcr (hash "obtain" (hash n pcr)))
    (esk esk1) (k k) (aik aik))
  (defstrand tpm-decrypt 4 (m v) (pcr (hash "obtain" (hash n pcr)))
    (k k) (aik aik))
  (defstrand tpm-quote 3 (nonce (enc v k))
    (pcr (hash "refuse" (hash n pcr))) (aik aik))
  (defstrand tpm-extend-enc 4 (value n) (tne tne-0) (tno tno-0)
    (esk esk) (tpmkey tpmkey-0))
  (defstrand tpm-extend-enc 4 (value n) (tne tne) (tno tno) (esk esk)
    (tpmkey tpmkey))
  (deflistener
    (cat esk (hash "execute transport" (hash "extend" (enc n esk)))
      tne-0 tno-0 "false"))
  (deflistener (cat "execute transport" (hash "extend" (enc n esk))))
  (deflistener (cat "extend" (enc n esk)))
  (precedes ((2 0) (6 0)) ((2 0) (7 0)) ((2 2) (7 2)) ((2 2) (10 0))
    ((2 4) (3 0)) ((2 6) (4 0)) ((2 6) (5 0)) ((3 1) (2 5))
    ((4 3) (1 0)) ((5 2) (0 0)) ((6 1) (8 0)) ((6 3) (7 3))
    ((7 1) (2 1)) ((8 1) (6 2)) ((9 1) (8 0)) ((10 1) (9 0)))
  (non-orig esk1 aik (invk k) (invk tpmkey) (invk tpmkey-0))
  (uniq-orig n v tne tno tne-0 esk k)
  (operation nonce-test (contracted (esk-0 esk)) n (10 0) (enc n esk))
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
    ((recv (cat "quote" (enc v k)))
      (sync (cat "observe" (hash "refuse" (hash n pcr))))
      (send (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik)))
    ((recv (cat "establish transport" tpmkey-0 (enc esk tpmkey-0)))
      (send (cat "establish transport" tne-0))
      (recv
        (cat "execute transport" (cat "extend" (enc n esk)) tno-0
          "false"
          (hash esk
            (hash "execute transport" (hash "extend" (enc n esk))) tne-0
            tno-0 "false"))) (sync (cat "extend" n)))
    ((recv (cat "establish transport" tpmkey (enc esk tpmkey)))
      (send (cat "establish transport" tne))
      (recv
        (cat "execute transport" (cat "extend" (enc n esk)) tno "false"
          (hash esk
            (hash "execute transport" (hash "extend" (enc n esk))) tne
            tno "false"))) (sync (cat "extend" n)))
    ((recv
       (cat esk (hash "execute transport" (hash "extend" (enc n esk)))
         tne-0 tno-0 "false"))
      (send
        (cat esk (hash "execute transport" (hash "extend" (enc n esk)))
          tne-0 tno-0 "false")))
    ((recv (cat "execute transport" (hash "extend" (enc n esk))))
      (send (cat "execute transport" (hash "extend" (enc n esk)))))
    ((recv (cat "extend" (enc n esk)))
      (send (cat "extend" (enc n esk)))))
  (label 22)
  (parent 19)
  (unrealized (6 0) (8 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton envelope
  (vars (pcr mesg) (n text) (v tne tno tne-0 tno-0 data)
    (esk1 esk esk-0 skey) (k aik tpmkey tpmkey-0 akey))
  (deflistener (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik))
  (deflistener v)
  (defstrand alice 7 (pcr pcr) (n n) (v v) (tne tne) (tno tno)
    (esk1 esk1) (esk esk) (k k) (aik aik) (tpmkey tpmkey))
  (defstrand tpm-create-key 2 (pcr (hash "obtain" (hash n pcr)))
    (esk esk1) (k k) (aik aik))
  (defstrand tpm-decrypt 4 (m v) (pcr (hash "obtain" (hash n pcr)))
    (k k) (aik aik))
  (defstrand tpm-quote 3 (nonce (enc v k))
    (pcr (hash "refuse" (hash n pcr))) (aik aik))
  (defstrand tpm-extend-enc 4 (value n) (tne tne-0) (tno tno-0)
    (esk esk-0) (tpmkey tpmkey-0))
  (defstrand tpm-extend-enc 4 (value n) (tne tne) (tno tno) (esk esk)
    (tpmkey tpmkey))
  (deflistener
    (cat esk-0 (hash "execute transport" (hash "extend" (enc n esk-0)))
      tne-0 tno-0 "false"))
  (deflistener (cat "execute transport" (hash "extend" (enc n esk-0))))
  (deflistener (cat "extend" (enc n esk-0)))
  (deflistener esk)
  (precedes ((2 0) (7 0)) ((2 0) (11 0)) ((2 2) (7 2)) ((2 2) (10 0))
    ((2 4) (3 0)) ((2 6) (4 0)) ((2 6) (5 0)) ((3 1) (2 5))
    ((4 3) (1 0)) ((5 2) (0 0)) ((6 1) (8 0)) ((6 3) (7 3))
    ((7 1) (2 1)) ((8 1) (6 2)) ((9 1) (8 0)) ((10 1) (9 0))
    ((11 1) (10 0)))
  (non-orig esk1 aik (invk k) (invk tpmkey) (invk tpmkey-0))
  (uniq-orig n v tne tno tne-0 esk k)
  (operation nonce-test (added-listener esk) n (10 0) (enc n esk))
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
    ((recv (cat "quote" (enc v k)))
      (sync (cat "observe" (hash "refuse" (hash n pcr))))
      (send (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik)))
    ((recv (cat "establish transport" tpmkey-0 (enc esk-0 tpmkey-0)))
      (send (cat "establish transport" tne-0))
      (recv
        (cat "execute transport" (cat "extend" (enc n esk-0)) tno-0
          "false"
          (hash esk-0
            (hash "execute transport" (hash "extend" (enc n esk-0)))
            tne-0 tno-0 "false"))) (sync (cat "extend" n)))
    ((recv (cat "establish transport" tpmkey (enc esk tpmkey)))
      (send (cat "establish transport" tne))
      (recv
        (cat "execute transport" (cat "extend" (enc n esk)) tno "false"
          (hash esk
            (hash "execute transport" (hash "extend" (enc n esk))) tne
            tno "false"))) (sync (cat "extend" n)))
    ((recv
       (cat esk-0
         (hash "execute transport" (hash "extend" (enc n esk-0))) tne-0
         tno-0 "false"))
      (send
        (cat esk-0
          (hash "execute transport" (hash "extend" (enc n esk-0))) tne-0
          tno-0 "false")))
    ((recv (cat "execute transport" (hash "extend" (enc n esk-0))))
      (send (cat "execute transport" (hash "extend" (enc n esk-0)))))
    ((recv (cat "extend" (enc n esk-0)))
      (send (cat "extend" (enc n esk-0)))) ((recv esk) (send esk)))
  (label 23)
  (parent 19)
  (unrealized (11 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton envelope
  (vars (pcr pcr-0 mesg) (n text) (v tne tno tne-0 tno-0 data)
    (esk1 esk skey) (k aik tpmkey tpmkey-0 aik-0 akey))
  (deflistener (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik))
  (deflistener v)
  (defstrand alice 7 (pcr pcr) (n n) (v v) (tne tne) (tno tno)
    (esk1 esk1) (esk esk) (k k) (aik aik) (tpmkey tpmkey))
  (defstrand tpm-create-key 2 (pcr (hash "obtain" (hash n pcr)))
    (esk esk1) (k k) (aik aik))
  (defstrand tpm-decrypt 4 (m v) (pcr (hash "obtain" (hash n pcr)))
    (k k) (aik aik))
  (defstrand tpm-quote 3 (nonce (enc v k))
    (pcr (hash "refuse" (hash n pcr))) (aik aik))
  (defstrand tpm-extend-enc 4 (value n) (tne tne-0) (tno tno-0)
    (esk esk) (tpmkey tpmkey-0))
  (defstrand tpm-extend-enc 4 (value n) (tne tne) (tno tno) (esk esk)
    (tpmkey tpmkey))
  (deflistener
    (cat esk (hash "execute transport" (hash "extend" (enc n esk)))
      tne-0 tno-0 "false"))
  (deflistener (cat "execute transport" (hash "extend" (enc n esk))))
  (deflistener (cat "extend" (enc n esk)))
  (defstrand tpm-decrypt 4 (m esk) (pcr pcr-0) (k tpmkey) (aik aik-0))
  (precedes ((2 0) (6 0)) ((2 0) (7 0)) ((2 0) (11 0)) ((2 2) (7 2))
    ((2 2) (10 0)) ((2 4) (3 0)) ((2 6) (4 0)) ((2 6) (5 0))
    ((3 1) (2 5)) ((4 3) (1 0)) ((5 2) (0 0)) ((6 1) (8 0))
    ((6 3) (7 3)) ((7 1) (2 1)) ((8 1) (6 2)) ((9 1) (8 0))
    ((10 1) (9 0)) ((11 3) (8 0)))
  (non-orig esk1 aik aik-0 (invk k) (invk tpmkey) (invk tpmkey-0))
  (uniq-orig n v tne tno tne-0 esk k)
  (operation nonce-test (added-strand tpm-decrypt 4) esk (8 0)
    (enc esk tpmkey))
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
    ((recv (cat "quote" (enc v k)))
      (sync (cat "observe" (hash "refuse" (hash n pcr))))
      (send (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik)))
    ((recv (cat "establish transport" tpmkey-0 (enc esk tpmkey-0)))
      (send (cat "establish transport" tne-0))
      (recv
        (cat "execute transport" (cat "extend" (enc n esk)) tno-0
          "false"
          (hash esk
            (hash "execute transport" (hash "extend" (enc n esk))) tne-0
            tno-0 "false"))) (sync (cat "extend" n)))
    ((recv (cat "establish transport" tpmkey (enc esk tpmkey)))
      (send (cat "establish transport" tne))
      (recv
        (cat "execute transport" (cat "extend" (enc n esk)) tno "false"
          (hash esk
            (hash "execute transport" (hash "extend" (enc n esk))) tne
            tno "false"))) (sync (cat "extend" n)))
    ((recv
       (cat esk (hash "execute transport" (hash "extend" (enc n esk)))
         tne-0 tno-0 "false"))
      (send
        (cat esk (hash "execute transport" (hash "extend" (enc n esk)))
          tne-0 tno-0 "false")))
    ((recv (cat "execute transport" (hash "extend" (enc n esk))))
      (send (cat "execute transport" (hash "extend" (enc n esk)))))
    ((recv (cat "extend" (enc n esk)))
      (send (cat "extend" (enc n esk))))
    ((recv (cat "decrypt" (enc esk tpmkey)))
      (recv (enc "created" tpmkey pcr-0 aik-0))
      (sync (cat "observe" pcr-0)) (send esk)))
  (label 24)
  (parent 22)
  (unrealized (6 0) (11 1))
  (comment "empty cohort"))

(defskeleton envelope
  (vars (pcr pcr-0 mesg) (n text) (v tne tno tne-0 tno-0 data)
    (esk1 esk esk-0 skey) (k aik tpmkey tpmkey-0 aik-0 akey))
  (deflistener (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik))
  (deflistener v)
  (defstrand alice 7 (pcr pcr) (n n) (v v) (tne tne) (tno tno)
    (esk1 esk1) (esk esk) (k k) (aik aik) (tpmkey tpmkey))
  (defstrand tpm-create-key 2 (pcr (hash "obtain" (hash n pcr)))
    (esk esk1) (k k) (aik aik))
  (defstrand tpm-decrypt 4 (m v) (pcr (hash "obtain" (hash n pcr)))
    (k k) (aik aik))
  (defstrand tpm-quote 3 (nonce (enc v k))
    (pcr (hash "refuse" (hash n pcr))) (aik aik))
  (defstrand tpm-extend-enc 4 (value n) (tne tne-0) (tno tno-0)
    (esk esk-0) (tpmkey tpmkey-0))
  (defstrand tpm-extend-enc 4 (value n) (tne tne) (tno tno) (esk esk)
    (tpmkey tpmkey))
  (deflistener
    (cat esk-0 (hash "execute transport" (hash "extend" (enc n esk-0)))
      tne-0 tno-0 "false"))
  (deflistener (cat "execute transport" (hash "extend" (enc n esk-0))))
  (deflistener (cat "extend" (enc n esk-0)))
  (deflistener esk)
  (defstrand tpm-decrypt 4 (m esk) (pcr pcr-0) (k tpmkey) (aik aik-0))
  (precedes ((2 0) (7 0)) ((2 0) (12 0)) ((2 2) (7 2)) ((2 2) (10 0))
    ((2 4) (3 0)) ((2 6) (4 0)) ((2 6) (5 0)) ((3 1) (2 5))
    ((4 3) (1 0)) ((5 2) (0 0)) ((6 1) (8 0)) ((6 3) (7 3))
    ((7 1) (2 1)) ((8 1) (6 2)) ((9 1) (8 0)) ((10 1) (9 0))
    ((11 1) (10 0)) ((12 3) (11 0)))
  (non-orig esk1 aik aik-0 (invk k) (invk tpmkey) (invk tpmkey-0))
  (uniq-orig n v tne tno tne-0 esk k)
  (operation nonce-test (added-strand tpm-decrypt 4) esk (11 0)
    (enc esk tpmkey))
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
    ((recv (cat "quote" (enc v k)))
      (sync (cat "observe" (hash "refuse" (hash n pcr))))
      (send (enc "quote" (hash "refuse" (hash n pcr)) (enc v k) aik)))
    ((recv (cat "establish transport" tpmkey-0 (enc esk-0 tpmkey-0)))
      (send (cat "establish transport" tne-0))
      (recv
        (cat "execute transport" (cat "extend" (enc n esk-0)) tno-0
          "false"
          (hash esk-0
            (hash "execute transport" (hash "extend" (enc n esk-0)))
            tne-0 tno-0 "false"))) (sync (cat "extend" n)))
    ((recv (cat "establish transport" tpmkey (enc esk tpmkey)))
      (send (cat "establish transport" tne))
      (recv
        (cat "execute transport" (cat "extend" (enc n esk)) tno "false"
          (hash esk
            (hash "execute transport" (hash "extend" (enc n esk))) tne
            tno "false"))) (sync (cat "extend" n)))
    ((recv
       (cat esk-0
         (hash "execute transport" (hash "extend" (enc n esk-0))) tne-0
         tno-0 "false"))
      (send
        (cat esk-0
          (hash "execute transport" (hash "extend" (enc n esk-0))) tne-0
          tno-0 "false")))
    ((recv (cat "execute transport" (hash "extend" (enc n esk-0))))
      (send (cat "execute transport" (hash "extend" (enc n esk-0)))))
    ((recv (cat "extend" (enc n esk-0)))
      (send (cat "extend" (enc n esk-0)))) ((recv esk) (send esk))
    ((recv (cat "decrypt" (enc esk tpmkey)))
      (recv (enc "created" tpmkey pcr-0 aik-0))
      (sync (cat "observe" pcr-0)) (send esk)))
  (label 25)
  (parent 23)
  (unrealized (12 1))
  (comment "empty cohort"))

(comment "Nothing left to do")
