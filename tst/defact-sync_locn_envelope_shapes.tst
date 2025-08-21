(comment "CPSA 4.4.5")
(comment "Extracted shapes")

(herald "Envelope Protocol, location-based version" (check-nonces)
  (bound 30) (limit 6000))

(comment "CPSA 4.4.5")

(comment "All input read from tst/sync_locn_envelope.scm")

(comment "Step count limited to 6000")

(comment "Strand count bounded at 30")

(comment "Nonces checked first")

(defprotocol envelope basic
  (defrole tpm-power-on
    (vars (current-value mesg) (pcr locn) (tpm chan))
    (trace (recv tpm "power on") (load pcr current-value)
      (stor pcr "0")))
  (defrole tpm-extend-enc
    (vars (value current-value mesg) (pcr-id nonce text) (pcr locn)
      (tpm chan))
    (trace (send tpm (cat "token" nonce))
      (recv tpm (cat "extend" pcr-id value (hash pcr-id value nonce)))
      (load pcr current-value) (stor pcr (hash current-value value))
      (send "ext ok"))
    (uniq-orig nonce))
  (defrole tpm-quote
    (vars (nonce current-value mesg) (pcr-id text) (aik akey) (pcr locn)
      (tpm chan))
    (trace (recv tpm (cat "quote" pcr-id nonce))
      (load pcr current-value)
      (send (enc "quote" pcr-id current-value nonce aik))))
  (defrole tpm-create-key
    (vars (k aik akey) (pcr-id text) (pcrval mesg) (tpm chan))
    (trace (recv tpm (cat "create-req" pcr-id pcrval))
      (send (enc "created" k pcr-id pcrval aik)))
    (non-orig (invk k))
    (uniq-orig k)
    (auth tpm))
  (defrole tpm-decrypt
    (vars (m current-value mesg) (pcr-id text) (k aik akey) (pcr locn)
      (tpm chan))
    (trace (recv tpm (cat "decrypt" (enc m k)))
      (recv (enc "created" k pcr-id current-value aik))
      (load pcr current-value) (send m))
    (non-orig aik))
  (defrole alice
    (vars (n v data) (pcr-id nonce text) (k aik akey)
      (tpm tpmconf chan))
    (trace (recv tpm (cat "token" nonce))
      (send tpmconf (cat "extend" pcr-id n (hash pcr-id n nonce)))
      (send tpm (cat "create-req" pcr-id (hash (hash "0" n) "obtain")))
      (recv (enc "created" k pcr-id (hash (hash "0" n) "obtain") aik))
      (send (enc v k)))
    (non-orig aik)
    (uniq-orig n v)
    (conf tpmconf)
    (neq (k aik)))
  (defrule genStV-if-hashed-tpm-power-on
    (forall ((z strd) (v1 v2 mesg))
      (implies
        (and (p "tpm-power-on" z (idx 2))
          (p "tpm-power-on" "current-value" z (hash v1 v2)))
        (gen-st (hash v1 v2)))))
  (defrule genStV-if-hashed-tpm-extend-enc
    (forall ((z strd) (v1 v2 mesg))
      (implies
        (and (p "tpm-extend-enc" z (idx 3))
          (p "tpm-extend-enc" "current-value" z (hash v1 v2)))
        (gen-st (hash v1 v2)))))
  (defrule genStV-if-hashed-tpm-decrypt
    (forall ((z strd) (v1 v2 mesg))
      (implies
        (and (p "tpm-decrypt" z (idx 3))
          (p "tpm-decrypt" "current-value" z (hash v1 v2)))
        (gen-st (hash v1 v2)))))
  (defrule genStV-if-hashed-tpm-quote
    (forall ((z strd) (v1 v2 mesg))
      (implies
        (and (p "tpm-quote" z (idx 2))
          (p "tpm-quote" "current-value" z (hash v1 v2)))
        (gen-st (hash v1 v2)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defgenrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2)) (false))))
  (defgenrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defgenrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defgenrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1)))))
  (defgenrule trRl_tpm-power-on-at-2
    (forall ((z strd))
      (implies (p "tpm-power-on" z (idx 3)) (trans z (idx 2)))))
  (defgenrule trRl_tpm-power-on-at-1
    (forall ((z strd))
      (implies (p "tpm-power-on" z (idx 3)) (trans z (idx 1)))))
  (defgenrule trRl_tpm-extend-enc-at-3
    (forall ((z strd))
      (implies (p "tpm-extend-enc" z (idx 4)) (trans z (idx 3)))))
  (defgenrule trRl_tpm-extend-enc-at-2
    (forall ((z strd))
      (implies (p "tpm-extend-enc" z (idx 4)) (trans z (idx 2))))))

(defskeleton envelope
  (vars (v n data) (pcr-id nonce text) (k aik akey) (tpm tpmconf chan))
  (deflistener v)
  (defstrand alice 5 (n n) (v v) (pcr-id pcr-id) (nonce nonce) (k k)
    (aik aik) (tpm tpm) (tpmconf tpmconf))
  (non-orig aik)
  (uniq-orig v n)
  (conf tpmconf)
  (traces ((recv v) (send v))
    ((recv tpm (cat "token" nonce))
      (send tpmconf (cat "extend" pcr-id n (hash pcr-id n nonce)))
      (send tpm (cat "create-req" pcr-id (hash (hash "0" n) "obtain")))
      (recv (enc "created" k pcr-id (hash (hash "0" n) "obtain") aik))
      (send (enc v k))))
  (label 0)
  (unrealized (0 0) (1 3))
  (preskeleton)
  (origs (v (1 4)) (n (1 1)))
  (comment "Not a skeleton"))

(defskeleton envelope
  (vars (v n data) (pcr-id pcr-id-0 nonce nonce-0 text) (k aik akey)
    (pt pt-0 pt-1 pval) (tpmconf tpm tpm-0 chan) (pcr locn))
  (deflistener v)
  (defstrand alice 5 (n n) (v v) (pcr-id pcr-id) (nonce nonce-0) (k k)
    (aik aik) (tpm tpmconf) (tpmconf tpmconf))
  (defstrand tpm-create-key 2 (pcrval (hash (hash "0" n) "obtain"))
    (pcr-id pcr-id) (k k) (aik aik) (tpm tpmconf))
  (defstrand tpm-decrypt 4 (m v)
    (current-value (hash (hash "0" n) "obtain")) (pcr-id pcr-id) (k k)
    (aik aik) (tpm tpm) (pcr pcr))
  (defstrand tpm-extend-enc 4 (value "obtain")
    (current-value (hash "0" n)) (pcr-id pcr-id-0) (nonce nonce)
    (tpm tpm-0) (pcr pcr))
  (defstrand tpm-extend-enc 4 (value n) (current-value "0")
    (pcr-id pcr-id) (nonce nonce-0) (tpm tpmconf) (pcr pcr))
  (precedes ((1 1) (5 1)) ((1 2) (2 0)) ((1 4) (3 0)) ((2 1) (1 3))
    ((3 3) (0 0)) ((4 3) (3 2)) ((5 0) (1 0)) ((5 3) (4 2)))
  (non-orig aik (invk k))
  (uniq-orig v n nonce nonce-0 k)
  (gen-st (hash "0" n) (hash (hash "0" n) "obtain"))
  (conf tpmconf)
  (auth tpmconf)
  (leads-to ((4 3) (3 2)) ((5 3) (4 2)))
  (operation channel-test (displaced 6 1 alice 2)
    (ch-msg tpm-1 (cat "extend" pcr-id-1 n (hash pcr-id-1 n nonce-0)))
    (5 1))
  (strand-map 0 1 2 3 4 5)
  (traces ((recv v) (send v))
    ((recv tpmconf (cat "token" nonce-0))
      (send tpmconf (cat "extend" pcr-id n (hash pcr-id n nonce-0)))
      (send tpmconf
        (cat "create-req" pcr-id (hash (hash "0" n) "obtain")))
      (recv (enc "created" k pcr-id (hash (hash "0" n) "obtain") aik))
      (send (enc v k)))
    ((recv tpmconf
       (cat "create-req" pcr-id (hash (hash "0" n) "obtain")))
      (send (enc "created" k pcr-id (hash (hash "0" n) "obtain") aik)))
    ((recv tpm (cat "decrypt" (enc v k)))
      (recv (enc "created" k pcr-id (hash (hash "0" n) "obtain") aik))
      (load pcr (cat pt (hash (hash "0" n) "obtain"))) (send v))
    ((send tpm-0 (cat "token" nonce))
      (recv tpm-0
        (cat "extend" pcr-id-0 "obtain" (hash pcr-id-0 "obtain" nonce)))
      (load pcr (cat pt-0 (hash "0" n)))
      (stor pcr (cat pt (hash (hash "0" n) "obtain"))))
    ((send tpmconf (cat "token" nonce-0))
      (recv tpmconf (cat "extend" pcr-id n (hash pcr-id n nonce-0)))
      (load pcr (cat pt-1 "0")) (stor pcr (cat pt-0 (hash "0" n)))))
  (label 11)
  (parent 0)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((v v) (n n) (pcr-id pcr-id) (nonce nonce-0) (k k) (aik aik)
        (tpm tpmconf) (tpmconf tpmconf))))
  (origs (n (1 1)) (nonce-0 (5 0)) (pt-0 (5 3)) (nonce (4 0)) (pt (4 3))
    (k (2 1)) (v (1 4))))

(comment "Nothing left to do")

(defprotocol envelope basic
  (defrole tpm-power-on
    (vars (current-value mesg) (pcr locn) (tpm chan))
    (trace (recv tpm "power on") (load pcr current-value)
      (stor pcr "0")))
  (defrole tpm-extend-enc
    (vars (value current-value mesg) (pcr-id nonce text) (pcr locn)
      (tpm chan))
    (trace (send tpm (cat "token" nonce))
      (recv tpm (cat "extend" pcr-id value (hash pcr-id value nonce)))
      (load pcr current-value) (stor pcr (hash current-value value))
      (send "ext ok"))
    (uniq-orig nonce))
  (defrole tpm-quote
    (vars (nonce current-value mesg) (pcr-id text) (aik akey) (pcr locn)
      (tpm chan))
    (trace (recv tpm (cat "quote" pcr-id nonce))
      (load pcr current-value)
      (send (enc "quote" pcr-id current-value nonce aik))))
  (defrole tpm-create-key
    (vars (k aik akey) (pcr-id text) (pcrval mesg) (tpm chan))
    (trace (recv tpm (cat "create-req" pcr-id pcrval))
      (send (enc "created" k pcr-id pcrval aik)))
    (non-orig (invk k))
    (uniq-orig k)
    (auth tpm))
  (defrole tpm-decrypt
    (vars (m current-value mesg) (pcr-id text) (k aik akey) (pcr locn)
      (tpm chan))
    (trace (recv tpm (cat "decrypt" (enc m k)))
      (recv (enc "created" k pcr-id current-value aik))
      (load pcr current-value) (send m))
    (non-orig aik))
  (defrole alice
    (vars (n v data) (pcr-id nonce text) (k aik akey)
      (tpm tpmconf chan))
    (trace (recv tpm (cat "token" nonce))
      (send tpmconf (cat "extend" pcr-id n (hash pcr-id n nonce)))
      (send tpm (cat "create-req" pcr-id (hash (hash "0" n) "obtain")))
      (recv (enc "created" k pcr-id (hash (hash "0" n) "obtain") aik))
      (send (enc v k)))
    (non-orig aik)
    (uniq-orig n v)
    (conf tpmconf)
    (neq (k aik)))
  (defrule genStV-if-hashed-tpm-power-on
    (forall ((z strd) (v1 v2 mesg))
      (implies
        (and (p "tpm-power-on" z (idx 2))
          (p "tpm-power-on" "current-value" z (hash v1 v2)))
        (gen-st (hash v1 v2)))))
  (defrule genStV-if-hashed-tpm-extend-enc
    (forall ((z strd) (v1 v2 mesg))
      (implies
        (and (p "tpm-extend-enc" z (idx 3))
          (p "tpm-extend-enc" "current-value" z (hash v1 v2)))
        (gen-st (hash v1 v2)))))
  (defrule genStV-if-hashed-tpm-decrypt
    (forall ((z strd) (v1 v2 mesg))
      (implies
        (and (p "tpm-decrypt" z (idx 3))
          (p "tpm-decrypt" "current-value" z (hash v1 v2)))
        (gen-st (hash v1 v2)))))
  (defrule genStV-if-hashed-tpm-quote
    (forall ((z strd) (v1 v2 mesg))
      (implies
        (and (p "tpm-quote" z (idx 2))
          (p "tpm-quote" "current-value" z (hash v1 v2)))
        (gen-st (hash v1 v2)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defgenrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2)) (false))))
  (defgenrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defgenrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defgenrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1)))))
  (defgenrule trRl_tpm-power-on-at-2
    (forall ((z strd))
      (implies (p "tpm-power-on" z (idx 3)) (trans z (idx 2)))))
  (defgenrule trRl_tpm-power-on-at-1
    (forall ((z strd))
      (implies (p "tpm-power-on" z (idx 3)) (trans z (idx 1)))))
  (defgenrule trRl_tpm-extend-enc-at-3
    (forall ((z strd))
      (implies (p "tpm-extend-enc" z (idx 4)) (trans z (idx 3)))))
  (defgenrule trRl_tpm-extend-enc-at-2
    (forall ((z strd))
      (implies (p "tpm-extend-enc" z (idx 4)) (trans z (idx 2))))))

(defskeleton envelope
  (vars (n v data) (pcr-id pcr-id-0 nonce text) (k aik akey)
    (tpm tpmconf chan))
  (deflistener
    (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k) aik))
  (defstrand alice 5 (n n) (v v) (pcr-id pcr-id-0) (nonce nonce) (k k)
    (aik aik) (tpm tpm) (tpmconf tpmconf))
  (non-orig aik)
  (uniq-orig n v)
  (conf tpmconf)
  (traces
    ((recv
       (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k) aik))
      (send
        (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k)
          aik)))
    ((recv tpm (cat "token" nonce))
      (send tpmconf (cat "extend" pcr-id-0 n (hash pcr-id-0 n nonce)))
      (send tpm
        (cat "create-req" pcr-id-0 (hash (hash "0" n) "obtain")))
      (recv (enc "created" k pcr-id-0 (hash (hash "0" n) "obtain") aik))
      (send (enc v k))))
  (label 12)
  (unrealized (0 0) (1 3))
  (preskeleton)
  (origs (v (1 4)) (n (1 1)))
  (comment "Not a skeleton"))

(defskeleton envelope
  (vars (n v data) (pcr-id pcr-id-0 pcr-id-1 nonce nonce-0 text)
    (k aik akey) (pt pt-0 pt-1 pval) (tpmconf tpm tpm-0 chan)
    (pcr locn))
  (deflistener
    (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k) aik))
  (defstrand alice 5 (n n) (v v) (pcr-id pcr-id-0) (nonce nonce-0) (k k)
    (aik aik) (tpm tpmconf) (tpmconf tpmconf))
  (defstrand tpm-create-key 2 (pcrval (hash (hash "0" n) "obtain"))
    (pcr-id pcr-id-0) (k k) (aik aik) (tpm tpmconf))
  (defstrand tpm-quote 3 (nonce (enc v k))
    (current-value (hash (hash "0" n) "refuse")) (pcr-id pcr-id)
    (aik aik) (tpm tpm) (pcr pcr))
  (defstrand tpm-extend-enc 4 (value "refuse")
    (current-value (hash "0" n)) (pcr-id pcr-id-1) (nonce nonce)
    (tpm tpm-0) (pcr pcr))
  (defstrand tpm-extend-enc 4 (value n) (current-value "0")
    (pcr-id pcr-id-0) (nonce nonce-0) (tpm tpmconf) (pcr pcr))
  (precedes ((1 1) (5 1)) ((1 2) (2 0)) ((1 4) (3 0)) ((2 1) (1 3))
    ((3 2) (0 0)) ((4 3) (3 1)) ((5 0) (1 0)) ((5 3) (4 2)))
  (non-orig aik (invk k))
  (uniq-orig n v nonce nonce-0 k)
  (gen-st (hash "0" n) (hash (hash "0" n) "refuse"))
  (conf tpmconf)
  (auth tpmconf)
  (leads-to ((4 3) (3 1)) ((5 3) (4 2)))
  (operation channel-test (displaced 6 1 alice 2)
    (ch-msg tpm-1 (cat "extend" pcr-id-2 n (hash pcr-id-2 n nonce-0)))
    (5 1))
  (strand-map 0 1 2 3 4 5)
  (traces
    ((recv
       (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k) aik))
      (send
        (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k)
          aik)))
    ((recv tpmconf (cat "token" nonce-0))
      (send tpmconf (cat "extend" pcr-id-0 n (hash pcr-id-0 n nonce-0)))
      (send tpmconf
        (cat "create-req" pcr-id-0 (hash (hash "0" n) "obtain")))
      (recv (enc "created" k pcr-id-0 (hash (hash "0" n) "obtain") aik))
      (send (enc v k)))
    ((recv tpmconf
       (cat "create-req" pcr-id-0 (hash (hash "0" n) "obtain")))
      (send
        (enc "created" k pcr-id-0 (hash (hash "0" n) "obtain") aik)))
    ((recv tpm (cat "quote" pcr-id (enc v k)))
      (load pcr (cat pt (hash (hash "0" n) "refuse")))
      (send
        (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k)
          aik)))
    ((send tpm-0 (cat "token" nonce))
      (recv tpm-0
        (cat "extend" pcr-id-1 "refuse" (hash pcr-id-1 "refuse" nonce)))
      (load pcr (cat pt-0 (hash "0" n)))
      (stor pcr (cat pt (hash (hash "0" n) "refuse"))))
    ((send tpmconf (cat "token" nonce-0))
      (recv tpmconf (cat "extend" pcr-id-0 n (hash pcr-id-0 n nonce-0)))
      (load pcr (cat pt-1 "0")) (stor pcr (cat pt-0 (hash "0" n)))))
  (label 22)
  (parent 12)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((n n) (v v) (k k) (aik aik) (pcr-id pcr-id) (pcr-id-0 pcr-id-0)
        (nonce nonce-0) (tpm tpmconf) (tpmconf tpmconf))))
  (origs (n (1 1)) (nonce-0 (5 0)) (pt-0 (5 3)) (nonce (4 0)) (pt (4 3))
    (k (2 1)) (v (1 4))))

(comment "Nothing left to do")

(defprotocol envelope basic
  (defrole tpm-power-on
    (vars (current-value mesg) (pcr locn) (tpm chan))
    (trace (recv tpm "power on") (load pcr current-value)
      (stor pcr "0")))
  (defrole tpm-extend-enc
    (vars (value current-value mesg) (pcr-id nonce text) (pcr locn)
      (tpm chan))
    (trace (send tpm (cat "token" nonce))
      (recv tpm (cat "extend" pcr-id value (hash pcr-id value nonce)))
      (load pcr current-value) (stor pcr (hash current-value value))
      (send "ext ok"))
    (uniq-orig nonce))
  (defrole tpm-quote
    (vars (nonce current-value mesg) (pcr-id text) (aik akey) (pcr locn)
      (tpm chan))
    (trace (recv tpm (cat "quote" pcr-id nonce))
      (load pcr current-value)
      (send (enc "quote" pcr-id current-value nonce aik))))
  (defrole tpm-create-key
    (vars (k aik akey) (pcr-id text) (pcrval mesg) (tpm chan))
    (trace (recv tpm (cat "create-req" pcr-id pcrval))
      (send (enc "created" k pcr-id pcrval aik)))
    (non-orig (invk k))
    (uniq-orig k)
    (auth tpm))
  (defrole tpm-decrypt
    (vars (m current-value mesg) (pcr-id text) (k aik akey) (pcr locn)
      (tpm chan))
    (trace (recv tpm (cat "decrypt" (enc m k)))
      (recv (enc "created" k pcr-id current-value aik))
      (load pcr current-value) (send m))
    (non-orig aik))
  (defrole alice
    (vars (n v data) (pcr-id nonce text) (k aik akey)
      (tpm tpmconf chan))
    (trace (recv tpm (cat "token" nonce))
      (send tpmconf (cat "extend" pcr-id n (hash pcr-id n nonce)))
      (send tpm (cat "create-req" pcr-id (hash (hash "0" n) "obtain")))
      (recv (enc "created" k pcr-id (hash (hash "0" n) "obtain") aik))
      (send (enc v k)))
    (non-orig aik)
    (uniq-orig n v)
    (conf tpmconf)
    (neq (k aik)))
  (defrule genStV-if-hashed-tpm-power-on
    (forall ((z strd) (v1 v2 mesg))
      (implies
        (and (p "tpm-power-on" z (idx 2))
          (p "tpm-power-on" "current-value" z (hash v1 v2)))
        (gen-st (hash v1 v2)))))
  (defrule genStV-if-hashed-tpm-extend-enc
    (forall ((z strd) (v1 v2 mesg))
      (implies
        (and (p "tpm-extend-enc" z (idx 3))
          (p "tpm-extend-enc" "current-value" z (hash v1 v2)))
        (gen-st (hash v1 v2)))))
  (defrule genStV-if-hashed-tpm-decrypt
    (forall ((z strd) (v1 v2 mesg))
      (implies
        (and (p "tpm-decrypt" z (idx 3))
          (p "tpm-decrypt" "current-value" z (hash v1 v2)))
        (gen-st (hash v1 v2)))))
  (defrule genStV-if-hashed-tpm-quote
    (forall ((z strd) (v1 v2 mesg))
      (implies
        (and (p "tpm-quote" z (idx 2))
          (p "tpm-quote" "current-value" z (hash v1 v2)))
        (gen-st (hash v1 v2)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defgenrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2)) (false))))
  (defgenrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defgenrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defgenrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1)))))
  (defgenrule trRl_tpm-power-on-at-2
    (forall ((z strd))
      (implies (p "tpm-power-on" z (idx 3)) (trans z (idx 2)))))
  (defgenrule trRl_tpm-power-on-at-1
    (forall ((z strd))
      (implies (p "tpm-power-on" z (idx 3)) (trans z (idx 1)))))
  (defgenrule trRl_tpm-extend-enc-at-3
    (forall ((z strd))
      (implies (p "tpm-extend-enc" z (idx 4)) (trans z (idx 3)))))
  (defgenrule trRl_tpm-extend-enc-at-2
    (forall ((z strd))
      (implies (p "tpm-extend-enc" z (idx 4)) (trans z (idx 2))))))

(defskeleton envelope
  (vars (n v data) (pcr-id pcr-id-0 nonce text) (k aik akey)
    (tpm tpmconf chan))
  (deflistener
    (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k) aik))
  (deflistener v)
  (defstrand alice 5 (n n) (v v) (pcr-id pcr-id-0) (nonce nonce) (k k)
    (aik aik) (tpm tpm) (tpmconf tpmconf))
  (non-orig aik)
  (uniq-orig n v)
  (conf tpmconf)
  (traces
    ((recv
       (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k) aik))
      (send
        (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k)
          aik))) ((recv v) (send v))
    ((recv tpm (cat "token" nonce))
      (send tpmconf (cat "extend" pcr-id-0 n (hash pcr-id-0 n nonce)))
      (send tpm
        (cat "create-req" pcr-id-0 (hash (hash "0" n) "obtain")))
      (recv (enc "created" k pcr-id-0 (hash (hash "0" n) "obtain") aik))
      (send (enc v k))))
  (label 23)
  (unrealized (0 0) (1 0) (2 3))
  (preskeleton)
  (origs (v (2 4)) (n (2 1)))
  (comment "Not a skeleton"))

(comment "Nothing left to do")

(defprotocol envelope basic
  (defrole tpm-power-on
    (vars (current-value mesg) (pcr locn) (tpm chan))
    (trace (recv tpm "power on") (load pcr current-value)
      (stor pcr "0")))
  (defrole tpm-extend-enc
    (vars (value current-value mesg) (pcr-id nonce text) (pcr locn)
      (tpm chan))
    (trace (send tpm (cat "token" nonce))
      (recv tpm (cat "extend" pcr-id value (hash pcr-id value nonce)))
      (load pcr current-value) (stor pcr (hash current-value value))
      (send "ext ok"))
    (uniq-orig nonce))
  (defrole tpm-quote
    (vars (nonce current-value mesg) (pcr-id text) (aik akey) (pcr locn)
      (tpm chan))
    (trace (recv tpm (cat "quote" pcr-id nonce))
      (load pcr current-value)
      (send (enc "quote" pcr-id current-value nonce aik))))
  (defrole tpm-create-key
    (vars (k aik akey) (pcr-id text) (pcrval mesg) (tpm chan))
    (trace (recv tpm (cat "create-req" pcr-id pcrval))
      (send (enc "created" k pcr-id pcrval aik)))
    (non-orig (invk k))
    (uniq-orig k)
    (auth tpm))
  (defrole tpm-decrypt
    (vars (m current-value mesg) (pcr-id text) (k aik akey) (pcr locn)
      (tpm chan))
    (trace (recv tpm (cat "decrypt" (enc m k)))
      (recv (enc "created" k pcr-id current-value aik))
      (load pcr current-value) (send m))
    (non-orig aik))
  (defrole alice
    (vars (n v data) (pcr-id nonce text) (k aik akey)
      (tpm tpmconf chan))
    (trace (recv tpm (cat "token" nonce))
      (send tpmconf (cat "extend" pcr-id n (hash pcr-id n nonce)))
      (send tpm (cat "create-req" pcr-id (hash (hash "0" n) "obtain")))
      (recv (enc "created" k pcr-id (hash (hash "0" n) "obtain") aik))
      (send (enc v k)))
    (non-orig aik)
    (uniq-orig n v)
    (conf tpmconf)
    (neq (k aik)))
  (defrule genStV-if-hashed-tpm-power-on
    (forall ((z strd) (v1 v2 mesg))
      (implies
        (and (p "tpm-power-on" z (idx 2))
          (p "tpm-power-on" "current-value" z (hash v1 v2)))
        (gen-st (hash v1 v2)))))
  (defrule genStV-if-hashed-tpm-extend-enc
    (forall ((z strd) (v1 v2 mesg))
      (implies
        (and (p "tpm-extend-enc" z (idx 3))
          (p "tpm-extend-enc" "current-value" z (hash v1 v2)))
        (gen-st (hash v1 v2)))))
  (defrule genStV-if-hashed-tpm-decrypt
    (forall ((z strd) (v1 v2 mesg))
      (implies
        (and (p "tpm-decrypt" z (idx 3))
          (p "tpm-decrypt" "current-value" z (hash v1 v2)))
        (gen-st (hash v1 v2)))))
  (defrule genStV-if-hashed-tpm-quote
    (forall ((z strd) (v1 v2 mesg))
      (implies
        (and (p "tpm-quote" z (idx 2))
          (p "tpm-quote" "current-value" z (hash v1 v2)))
        (gen-st (hash v1 v2)))))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false))))
  (defgenrule scissorsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (leads-to z0 i0 z2 i2))
        (and (= z1 z2) (= i1 i2)))))
  (defgenrule cakeRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (leads-to z0 i0 z1 i1)
          (leads-to z0 i0 z2 i2) (prec z1 i1 z2 i2)) (false))))
  (defgenrule no-interruption
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (leads-to z0 i0 z2 i2) (trans z1 i1)
          (same-locn z0 i0 z1 i1) (prec z0 i0 z1 i1) (prec z1 i1 z2 i2))
        (false))))
  (defgenrule shearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (trans z2 i2)
          (leads-to z0 i0 z1 i1) (same-locn z0 i0 z2 i2)
          (prec z0 i0 z2 i2))
        (or (and (= z1 z2) (= i1 i2)) (prec z1 i1 z2 i2)))))
  (defgenrule invShearsRule
    (forall ((z0 z1 z2 strd) (i0 i1 i2 indx))
      (implies
        (and (trans z0 i0) (trans z1 i1) (same-locn z0 i0 z1 i1)
          (leads-to z1 i1 z2 i2) (prec z0 i0 z2 i2))
        (or (and (= z0 z1) (= i0 i1)) (prec z0 i0 z1 i1)))))
  (defgenrule trRl_tpm-power-on-at-2
    (forall ((z strd))
      (implies (p "tpm-power-on" z (idx 3)) (trans z (idx 2)))))
  (defgenrule trRl_tpm-power-on-at-1
    (forall ((z strd))
      (implies (p "tpm-power-on" z (idx 3)) (trans z (idx 1)))))
  (defgenrule trRl_tpm-extend-enc-at-3
    (forall ((z strd))
      (implies (p "tpm-extend-enc" z (idx 4)) (trans z (idx 3)))))
  (defgenrule trRl_tpm-extend-enc-at-2
    (forall ((z strd))
      (implies (p "tpm-extend-enc" z (idx 4)) (trans z (idx 2))))))

(defskeleton envelope
  (vars (n v data) (pcr-id pcr-id-0 nonce text) (k aik akey)
    (tpm tpmconf chan))
  (deflistener
    (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k) aik))
  (deflistener v)
  (defstrand alice 5 (n n) (v v) (pcr-id pcr-id-0) (nonce nonce) (k k)
    (aik aik) (tpm tpm) (tpmconf tpmconf))
  (non-orig aik)
  (uniq-orig n v)
  (conf tpmconf)
  (traces
    ((recv
       (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k) aik))
      (send
        (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k)
          aik))) ((recv v) (send v))
    ((recv tpm (cat "token" nonce))
      (send tpmconf (cat "extend" pcr-id-0 n (hash pcr-id-0 n nonce)))
      (send tpm
        (cat "create-req" pcr-id-0 (hash (hash "0" n) "obtain")))
      (recv (enc "created" k pcr-id-0 (hash (hash "0" n) "obtain") aik))
      (send (enc v k))))
  (label 38)
  (unrealized (0 0) (1 0) (2 3))
  (preskeleton)
  (origs (v (2 4)) (n (2 1)))
  (comment "Not a skeleton"))

(comment "Nothing left to do")
