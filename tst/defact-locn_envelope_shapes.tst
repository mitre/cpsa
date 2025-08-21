(comment "CPSA 4.4.5")
(comment "Extracted shapes")

(herald "Envelope Protocol, location-based version" (bound 30)
  (limit 1200))

(comment "CPSA 4.4.5")

(comment "All input read from tst/locn_envelope.scm")

(comment "Step count limited to 1200")

(comment "Strand count bounded at 30")

(defprotocol envelope basic
  (defrole tpm-power-on
    (vars (current-value mesg) (pcr locn) (tpm chan))
    (trace (recv tpm "power on") (load pcr current-value)
      (stor pcr "0")))
  (defrole tpm-extend-enc
    (vars (value current-value mesg) (pcr-id text) (pcr locn)
      (tpm chan))
    (trace (recv tpm (cat "extend" pcr-id value))
      (load pcr current-value) (stor pcr (hash current-value value))
      (send "ext ok")))
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
    (vars (n v data) (pcr-id text) (k aik akey) (tpm chan))
    (trace (send tpm (cat "extend" pcr-id n))
      (send tpm (cat "create-req" pcr-id (hash (hash "0" n) "obtain")))
      (recv (enc "created" k pcr-id (hash (hash "0" n) "obtain") aik))
      (send (enc v k)))
    (non-orig aik)
    (uniq-orig n v)
    (conf tpm)
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
        (and (p "tpm-extend-enc" z (idx 2))
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
  (defgenrule trRl_tpm-extend-enc-at-2
    (forall ((z strd))
      (implies (p "tpm-extend-enc" z (idx 3)) (trans z (idx 2)))))
  (defgenrule trRl_tpm-extend-enc-at-1
    (forall ((z strd))
      (implies (p "tpm-extend-enc" z (idx 3)) (trans z (idx 1))))))

(defskeleton envelope
  (vars (v n data) (pcr-id text) (k aik akey) (tpm chan))
  (deflistener v)
  (defstrand alice 4 (n n) (v v) (pcr-id pcr-id) (k k) (aik aik)
    (tpm tpm))
  (non-orig aik)
  (uniq-orig v n)
  (conf tpm)
  (traces ((recv v) (send v))
    ((send tpm (cat "extend" pcr-id n))
      (send tpm (cat "create-req" pcr-id (hash (hash "0" n) "obtain")))
      (recv (enc "created" k pcr-id (hash (hash "0" n) "obtain") aik))
      (send (enc v k))))
  (label 0)
  (unrealized (0 0) (1 2))
  (preskeleton)
  (origs (v (1 3)) (n (1 0)))
  (comment "Not a skeleton"))

(defskeleton envelope
  (vars (v n data) (pcr-id pcr-id-0 text) (k aik akey)
    (pt pt-0 pt-1 pval) (tpm tpm-0 tpm-1 chan) (pcr locn))
  (deflistener v)
  (defstrand alice 4 (n n) (v v) (pcr-id pcr-id) (k k) (aik aik)
    (tpm tpm))
  (defstrand tpm-create-key 2 (pcrval (hash (hash "0" n) "obtain"))
    (pcr-id pcr-id) (k k) (aik aik) (tpm tpm))
  (defstrand tpm-decrypt 4 (m v)
    (current-value (hash (hash "0" n) "obtain")) (pcr-id pcr-id) (k k)
    (aik aik) (tpm tpm-0) (pcr pcr))
  (defstrand tpm-extend-enc 3 (value "obtain")
    (current-value (hash "0" n)) (pcr-id pcr-id-0) (tpm tpm-1)
    (pcr pcr))
  (defstrand tpm-extend-enc 3 (value n) (current-value "0")
    (pcr-id pcr-id) (tpm tpm) (pcr pcr))
  (precedes ((1 0) (5 0)) ((1 1) (2 0)) ((1 3) (3 0)) ((2 1) (1 2))
    ((3 3) (0 0)) ((4 2) (3 2)) ((5 2) (4 1)))
  (non-orig aik (invk k))
  (uniq-orig v n k)
  (gen-st (hash "0" n) (hash (hash "0" n) "obtain"))
  (conf tpm)
  (auth tpm)
  (leads-to ((4 2) (3 2)) ((5 2) (4 1)))
  (operation nonce-test (contracted (pcr-id-1 pcr-id) (tpm-2 tpm)) n
    (5 0) (ch-msg tpm (cat "extend" pcr-id n)))
  (strand-map 0 1 2 3 4 5)
  (traces ((recv v) (send v))
    ((send tpm (cat "extend" pcr-id n))
      (send tpm (cat "create-req" pcr-id (hash (hash "0" n) "obtain")))
      (recv (enc "created" k pcr-id (hash (hash "0" n) "obtain") aik))
      (send (enc v k)))
    ((recv tpm (cat "create-req" pcr-id (hash (hash "0" n) "obtain")))
      (send (enc "created" k pcr-id (hash (hash "0" n) "obtain") aik)))
    ((recv tpm-0 (cat "decrypt" (enc v k)))
      (recv (enc "created" k pcr-id (hash (hash "0" n) "obtain") aik))
      (load pcr (cat pt (hash (hash "0" n) "obtain"))) (send v))
    ((recv tpm-1 (cat "extend" pcr-id-0 "obtain"))
      (load pcr (cat pt-0 (hash "0" n)))
      (stor pcr (cat pt (hash (hash "0" n) "obtain"))))
    ((recv tpm (cat "extend" pcr-id n)) (load pcr (cat pt-1 "0"))
      (stor pcr (cat pt-0 (hash "0" n)))))
  (label 8)
  (parent 0)
  (realized)
  (shape)
  (maps ((0 1) ((v v) (n n) (pcr-id pcr-id) (k k) (aik aik) (tpm tpm))))
  (origs (pt-0 (5 2)) (pt (4 2)) (k (2 1)) (n (1 0)) (v (1 3))))

(comment "Nothing left to do")

(defprotocol envelope basic
  (defrole tpm-power-on
    (vars (current-value mesg) (pcr locn) (tpm chan))
    (trace (recv tpm "power on") (load pcr current-value)
      (stor pcr "0")))
  (defrole tpm-extend-enc
    (vars (value current-value mesg) (pcr-id text) (pcr locn)
      (tpm chan))
    (trace (recv tpm (cat "extend" pcr-id value))
      (load pcr current-value) (stor pcr (hash current-value value))
      (send "ext ok")))
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
    (vars (n v data) (pcr-id text) (k aik akey) (tpm chan))
    (trace (send tpm (cat "extend" pcr-id n))
      (send tpm (cat "create-req" pcr-id (hash (hash "0" n) "obtain")))
      (recv (enc "created" k pcr-id (hash (hash "0" n) "obtain") aik))
      (send (enc v k)))
    (non-orig aik)
    (uniq-orig n v)
    (conf tpm)
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
        (and (p "tpm-extend-enc" z (idx 2))
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
  (defgenrule trRl_tpm-extend-enc-at-2
    (forall ((z strd))
      (implies (p "tpm-extend-enc" z (idx 3)) (trans z (idx 2)))))
  (defgenrule trRl_tpm-extend-enc-at-1
    (forall ((z strd))
      (implies (p "tpm-extend-enc" z (idx 3)) (trans z (idx 1))))))

(defskeleton envelope
  (vars (n v data) (pcr-id pcr-id-0 text) (k aik akey) (tpm chan))
  (deflistener
    (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k) aik))
  (defstrand alice 4 (n n) (v v) (pcr-id pcr-id-0) (k k) (aik aik)
    (tpm tpm))
  (non-orig aik)
  (uniq-orig n v)
  (conf tpm)
  (traces
    ((recv
       (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k) aik))
      (send
        (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k)
          aik)))
    ((send tpm (cat "extend" pcr-id-0 n))
      (send tpm
        (cat "create-req" pcr-id-0 (hash (hash "0" n) "obtain")))
      (recv (enc "created" k pcr-id-0 (hash (hash "0" n) "obtain") aik))
      (send (enc v k))))
  (label 9)
  (unrealized (0 0) (1 2))
  (preskeleton)
  (origs (v (1 3)) (n (1 0)))
  (comment "Not a skeleton"))

(defskeleton envelope
  (vars (n v data) (pcr-id pcr-id-0 pcr-id-1 text) (k aik akey)
    (pt pt-0 pt-1 pval) (tpm tpm-0 tpm-1 chan) (pcr locn))
  (deflistener
    (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k) aik))
  (defstrand alice 4 (n n) (v v) (pcr-id pcr-id-0) (k k) (aik aik)
    (tpm tpm))
  (defstrand tpm-create-key 2 (pcrval (hash (hash "0" n) "obtain"))
    (pcr-id pcr-id-0) (k k) (aik aik) (tpm tpm))
  (defstrand tpm-quote 3 (nonce (enc v k))
    (current-value (hash (hash "0" n) "refuse")) (pcr-id pcr-id)
    (aik aik) (tpm tpm-0) (pcr pcr))
  (defstrand tpm-extend-enc 3 (value "refuse")
    (current-value (hash "0" n)) (pcr-id pcr-id-1) (tpm tpm-1)
    (pcr pcr))
  (defstrand tpm-extend-enc 3 (value n) (current-value "0")
    (pcr-id pcr-id-0) (tpm tpm) (pcr pcr))
  (precedes ((1 0) (5 0)) ((1 1) (2 0)) ((1 3) (3 0)) ((2 1) (1 2))
    ((3 2) (0 0)) ((4 2) (3 1)) ((5 2) (4 1)))
  (non-orig aik (invk k))
  (uniq-orig n v k)
  (gen-st (hash "0" n) (hash (hash "0" n) "refuse"))
  (conf tpm)
  (auth tpm)
  (leads-to ((4 2) (3 1)) ((5 2) (4 1)))
  (operation nonce-test (contracted (pcr-id-2 pcr-id-0) (tpm-2 tpm)) n
    (5 0) (ch-msg tpm (cat "extend" pcr-id-0 n)))
  (strand-map 0 1 2 3 4 5)
  (traces
    ((recv
       (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k) aik))
      (send
        (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k)
          aik)))
    ((send tpm (cat "extend" pcr-id-0 n))
      (send tpm
        (cat "create-req" pcr-id-0 (hash (hash "0" n) "obtain")))
      (recv (enc "created" k pcr-id-0 (hash (hash "0" n) "obtain") aik))
      (send (enc v k)))
    ((recv tpm (cat "create-req" pcr-id-0 (hash (hash "0" n) "obtain")))
      (send
        (enc "created" k pcr-id-0 (hash (hash "0" n) "obtain") aik)))
    ((recv tpm-0 (cat "quote" pcr-id (enc v k)))
      (load pcr (cat pt (hash (hash "0" n) "refuse")))
      (send
        (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k)
          aik)))
    ((recv tpm-1 (cat "extend" pcr-id-1 "refuse"))
      (load pcr (cat pt-0 (hash "0" n)))
      (stor pcr (cat pt (hash (hash "0" n) "refuse"))))
    ((recv tpm (cat "extend" pcr-id-0 n)) (load pcr (cat pt-1 "0"))
      (stor pcr (cat pt-0 (hash "0" n)))))
  (label 16)
  (parent 9)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((n n) (v v) (k k) (aik aik) (pcr-id pcr-id) (pcr-id-0 pcr-id-0)
        (tpm tpm))))
  (origs (pt-0 (5 2)) (pt (4 2)) (n (1 0)) (k (2 1)) (v (1 3))))

(comment "Nothing left to do")

(defprotocol envelope basic
  (defrole tpm-power-on
    (vars (current-value mesg) (pcr locn) (tpm chan))
    (trace (recv tpm "power on") (load pcr current-value)
      (stor pcr "0")))
  (defrole tpm-extend-enc
    (vars (value current-value mesg) (pcr-id text) (pcr locn)
      (tpm chan))
    (trace (recv tpm (cat "extend" pcr-id value))
      (load pcr current-value) (stor pcr (hash current-value value))
      (send "ext ok")))
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
    (vars (n v data) (pcr-id text) (k aik akey) (tpm chan))
    (trace (send tpm (cat "extend" pcr-id n))
      (send tpm (cat "create-req" pcr-id (hash (hash "0" n) "obtain")))
      (recv (enc "created" k pcr-id (hash (hash "0" n) "obtain") aik))
      (send (enc v k)))
    (non-orig aik)
    (uniq-orig n v)
    (conf tpm)
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
        (and (p "tpm-extend-enc" z (idx 2))
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
  (defgenrule trRl_tpm-extend-enc-at-2
    (forall ((z strd))
      (implies (p "tpm-extend-enc" z (idx 3)) (trans z (idx 2)))))
  (defgenrule trRl_tpm-extend-enc-at-1
    (forall ((z strd))
      (implies (p "tpm-extend-enc" z (idx 3)) (trans z (idx 1))))))

(defskeleton envelope
  (vars (n v data) (pcr-id pcr-id-0 text) (k aik akey) (tpm chan))
  (deflistener
    (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k) aik))
  (deflistener v)
  (defstrand alice 4 (n n) (v v) (pcr-id pcr-id-0) (k k) (aik aik)
    (tpm tpm))
  (non-orig aik)
  (uniq-orig n v)
  (conf tpm)
  (traces
    ((recv
       (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k) aik))
      (send
        (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k)
          aik))) ((recv v) (send v))
    ((send tpm (cat "extend" pcr-id-0 n))
      (send tpm
        (cat "create-req" pcr-id-0 (hash (hash "0" n) "obtain")))
      (recv (enc "created" k pcr-id-0 (hash (hash "0" n) "obtain") aik))
      (send (enc v k))))
  (label 17)
  (unrealized (0 0) (1 0) (2 2))
  (preskeleton)
  (origs (v (2 3)) (n (2 0)))
  (comment "Not a skeleton"))

(defskeleton envelope
  (vars (n v data) (pcr-id pcr-id-0 pcr-id-1 pcr-id-2 text) (k aik akey)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval)
    (tpm tpm-0 tpm-1 tpm-2 tpm-3 chan) (pcr pcr-0 locn))
  (deflistener
    (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k) aik))
  (deflistener v)
  (defstrand alice 4 (n n) (v v) (pcr-id pcr-id-0) (k k) (aik aik)
    (tpm tpm))
  (defstrand tpm-create-key 2 (pcrval (hash (hash "0" n) "obtain"))
    (pcr-id pcr-id-0) (k k) (aik aik) (tpm tpm))
  (defstrand tpm-decrypt 4 (m v)
    (current-value (hash (hash "0" n) "obtain")) (pcr-id pcr-id-0) (k k)
    (aik aik) (tpm tpm-0) (pcr pcr))
  (defstrand tpm-extend-enc 3 (value "obtain")
    (current-value (hash "0" n)) (pcr-id pcr-id-1) (tpm tpm-1)
    (pcr pcr))
  (defstrand tpm-extend-enc 3 (value n) (current-value "0")
    (pcr-id pcr-id-0) (tpm tpm) (pcr pcr))
  (defstrand tpm-quote 3 (nonce (enc v k))
    (current-value (hash (hash "0" n) "refuse")) (pcr-id pcr-id)
    (aik aik) (tpm tpm-2) (pcr pcr-0))
  (defstrand tpm-extend-enc 3 (value "refuse")
    (current-value (hash "0" n)) (pcr-id pcr-id-2) (tpm tpm-3)
    (pcr pcr-0))
  (defstrand tpm-extend-enc 3 (value n) (current-value "0")
    (pcr-id pcr-id-0) (tpm tpm) (pcr pcr-0))
  (precedes ((2 0) (6 0)) ((2 0) (9 0)) ((2 1) (3 0)) ((2 3) (4 0))
    ((2 3) (7 0)) ((3 1) (2 2)) ((4 3) (1 0)) ((5 2) (4 2))
    ((6 2) (5 1)) ((7 2) (0 0)) ((8 2) (7 1)) ((9 2) (8 1)))
  (non-orig aik (invk k))
  (uniq-orig n v k)
  (gen-st (hash "0" n) (hash (hash "0" n) "obtain")
    (hash (hash "0" n) "refuse"))
  (conf tpm)
  (auth tpm)
  (leads-to ((5 2) (4 2)) ((6 2) (5 1)) ((8 2) (7 1)) ((9 2) (8 1)))
  (operation nonce-test (contracted (pcr-id-3 pcr-id-0) (tpm-4 tpm)) n
    (9 0) (ch-msg tpm (cat "extend" pcr-id-0 n)))
  (strand-map 0 1 2 3 4 5 6 7 8 9)
  (traces
    ((recv
       (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k) aik))
      (send
        (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k)
          aik))) ((recv v) (send v))
    ((send tpm (cat "extend" pcr-id-0 n))
      (send tpm
        (cat "create-req" pcr-id-0 (hash (hash "0" n) "obtain")))
      (recv (enc "created" k pcr-id-0 (hash (hash "0" n) "obtain") aik))
      (send (enc v k)))
    ((recv tpm (cat "create-req" pcr-id-0 (hash (hash "0" n) "obtain")))
      (send
        (enc "created" k pcr-id-0 (hash (hash "0" n) "obtain") aik)))
    ((recv tpm-0 (cat "decrypt" (enc v k)))
      (recv (enc "created" k pcr-id-0 (hash (hash "0" n) "obtain") aik))
      (load pcr (cat pt (hash (hash "0" n) "obtain"))) (send v))
    ((recv tpm-1 (cat "extend" pcr-id-1 "obtain"))
      (load pcr (cat pt-0 (hash "0" n)))
      (stor pcr (cat pt (hash (hash "0" n) "obtain"))))
    ((recv tpm (cat "extend" pcr-id-0 n)) (load pcr (cat pt-1 "0"))
      (stor pcr (cat pt-0 (hash "0" n))))
    ((recv tpm-2 (cat "quote" pcr-id (enc v k)))
      (load pcr-0 (cat pt-2 (hash (hash "0" n) "refuse")))
      (send
        (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k)
          aik)))
    ((recv tpm-3 (cat "extend" pcr-id-2 "refuse"))
      (load pcr-0 (cat pt-3 (hash "0" n)))
      (stor pcr-0 (cat pt-2 (hash (hash "0" n) "refuse"))))
    ((recv tpm (cat "extend" pcr-id-0 n)) (load pcr-0 (cat pt-4 "0"))
      (stor pcr-0 (cat pt-3 (hash "0" n)))))
  (label 29)
  (parent 17)
  (realized)
  (shape)
  (maps
    ((0 1 2)
      ((n n) (v v) (k k) (aik aik) (pcr-id pcr-id) (pcr-id-0 pcr-id-0)
        (tpm tpm))))
  (origs (pt-3 (9 2)) (pt-2 (8 2)) (pt-0 (6 2)) (pt (5 2)) (k (3 1))
    (n (2 0)) (v (2 3))))

(comment "Nothing left to do")

(defprotocol envelope-plus basic
  (defrole tpm-power-on
    (vars (current-value mesg) (pcr locn) (tpm chan))
    (trace (recv tpm "power on") (load pcr current-value)
      (stor pcr "0")))
  (defrole tpm-extend-enc
    (vars (value current-value mesg) (pcr-id text) (pcr locn)
      (tpm chan))
    (trace (recv tpm (cat "extend" pcr-id value))
      (load pcr current-value) (stor pcr (hash current-value value))
      (send "ext ok")))
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
    (vars (n v data) (pcr-id text) (k aik akey) (tpm chan))
    (trace (send tpm (cat "extend" pcr-id n))
      (send tpm (cat "create-req" pcr-id (hash (hash "0" n) "obtain")))
      (recv (enc "created" k pcr-id (hash (hash "0" n) "obtain") aik))
      (send (enc v k)))
    (non-orig aik)
    (uniq-orig n v)
    (conf tpm)
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
        (and (p "tpm-extend-enc" z (idx 2))
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
  (defrule ordered-extends
    (forall ((y z strd) (pcr locn))
      (implies
        (and (p "tpm-extend-enc" y (idx 3))
          (p "tpm-extend-enc" z (idx 3))
          (p "tpm-extend-enc" "pcr" y pcr)
          (p "tpm-extend-enc" "pcr" z pcr))
        (or
          (= y z)
          (prec y (idx 2) z (idx 1))
          (prec z (idx 2) y (idx 1))))))
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
  (defgenrule trRl_tpm-extend-enc-at-2
    (forall ((z strd))
      (implies (p "tpm-extend-enc" z (idx 3)) (trans z (idx 2)))))
  (defgenrule trRl_tpm-extend-enc-at-1
    (forall ((z strd))
      (implies (p "tpm-extend-enc" z (idx 3)) (trans z (idx 1))))))

(defskeleton envelope-plus
  (vars (v n data) (pcr-id text) (k aik akey) (tpm chan))
  (deflistener v)
  (defstrand alice 4 (n n) (v v) (pcr-id pcr-id) (k k) (aik aik)
    (tpm tpm))
  (non-orig aik)
  (uniq-orig v n)
  (conf tpm)
  (traces ((recv v) (send v))
    ((send tpm (cat "extend" pcr-id n))
      (send tpm (cat "create-req" pcr-id (hash (hash "0" n) "obtain")))
      (recv (enc "created" k pcr-id (hash (hash "0" n) "obtain") aik))
      (send (enc v k))))
  (label 30)
  (unrealized (0 0) (1 2))
  (preskeleton)
  (origs (v (1 3)) (n (1 0)))
  (comment "Not a skeleton"))

(defskeleton envelope-plus
  (vars (v n data) (pcr-id pcr-id-0 text) (k aik akey)
    (pt pt-0 pt-1 pval) (tpm tpm-0 tpm-1 chan) (pcr locn))
  (deflistener v)
  (defstrand alice 4 (n n) (v v) (pcr-id pcr-id) (k k) (aik aik)
    (tpm tpm))
  (defstrand tpm-create-key 2 (pcrval (hash (hash "0" n) "obtain"))
    (pcr-id pcr-id) (k k) (aik aik) (tpm tpm))
  (defstrand tpm-decrypt 4 (m v)
    (current-value (hash (hash "0" n) "obtain")) (pcr-id pcr-id) (k k)
    (aik aik) (tpm tpm-0) (pcr pcr))
  (defstrand tpm-extend-enc 3 (value "obtain")
    (current-value (hash "0" n)) (pcr-id pcr-id-0) (tpm tpm-1)
    (pcr pcr))
  (defstrand tpm-extend-enc 3 (value n) (current-value "0")
    (pcr-id pcr-id) (tpm tpm) (pcr pcr))
  (precedes ((1 0) (5 0)) ((1 1) (2 0)) ((1 3) (3 0)) ((2 1) (1 2))
    ((3 3) (0 0)) ((4 2) (3 2)) ((5 2) (4 1)))
  (non-orig aik (invk k))
  (uniq-orig v n k)
  (gen-st (hash "0" n) (hash (hash "0" n) "obtain"))
  (conf tpm)
  (auth tpm)
  (leads-to ((4 2) (3 2)) ((5 2) (4 1)))
  (operation nonce-test (contracted (pcr-id-1 pcr-id) (tpm-2 tpm)) n
    (5 0) (ch-msg tpm (cat "extend" pcr-id n)))
  (strand-map 0 1 2 3 4 5)
  (traces ((recv v) (send v))
    ((send tpm (cat "extend" pcr-id n))
      (send tpm (cat "create-req" pcr-id (hash (hash "0" n) "obtain")))
      (recv (enc "created" k pcr-id (hash (hash "0" n) "obtain") aik))
      (send (enc v k)))
    ((recv tpm (cat "create-req" pcr-id (hash (hash "0" n) "obtain")))
      (send (enc "created" k pcr-id (hash (hash "0" n) "obtain") aik)))
    ((recv tpm-0 (cat "decrypt" (enc v k)))
      (recv (enc "created" k pcr-id (hash (hash "0" n) "obtain") aik))
      (load pcr (cat pt (hash (hash "0" n) "obtain"))) (send v))
    ((recv tpm-1 (cat "extend" pcr-id-0 "obtain"))
      (load pcr (cat pt-0 (hash "0" n)))
      (stor pcr (cat pt (hash (hash "0" n) "obtain"))))
    ((recv tpm (cat "extend" pcr-id n)) (load pcr (cat pt-1 "0"))
      (stor pcr (cat pt-0 (hash "0" n)))))
  (label 38)
  (parent 30)
  (realized)
  (shape)
  (maps ((0 1) ((v v) (n n) (pcr-id pcr-id) (k k) (aik aik) (tpm tpm))))
  (origs (pt-0 (5 2)) (pt (4 2)) (k (2 1)) (n (1 0)) (v (1 3))))

(comment "Nothing left to do")

(defprotocol envelope-plus basic
  (defrole tpm-power-on
    (vars (current-value mesg) (pcr locn) (tpm chan))
    (trace (recv tpm "power on") (load pcr current-value)
      (stor pcr "0")))
  (defrole tpm-extend-enc
    (vars (value current-value mesg) (pcr-id text) (pcr locn)
      (tpm chan))
    (trace (recv tpm (cat "extend" pcr-id value))
      (load pcr current-value) (stor pcr (hash current-value value))
      (send "ext ok")))
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
    (vars (n v data) (pcr-id text) (k aik akey) (tpm chan))
    (trace (send tpm (cat "extend" pcr-id n))
      (send tpm (cat "create-req" pcr-id (hash (hash "0" n) "obtain")))
      (recv (enc "created" k pcr-id (hash (hash "0" n) "obtain") aik))
      (send (enc v k)))
    (non-orig aik)
    (uniq-orig n v)
    (conf tpm)
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
        (and (p "tpm-extend-enc" z (idx 2))
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
  (defrule ordered-extends
    (forall ((y z strd) (pcr locn))
      (implies
        (and (p "tpm-extend-enc" y (idx 3))
          (p "tpm-extend-enc" z (idx 3))
          (p "tpm-extend-enc" "pcr" y pcr)
          (p "tpm-extend-enc" "pcr" z pcr))
        (or
          (= y z)
          (prec y (idx 2) z (idx 1))
          (prec z (idx 2) y (idx 1))))))
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
  (defgenrule trRl_tpm-extend-enc-at-2
    (forall ((z strd))
      (implies (p "tpm-extend-enc" z (idx 3)) (trans z (idx 2)))))
  (defgenrule trRl_tpm-extend-enc-at-1
    (forall ((z strd))
      (implies (p "tpm-extend-enc" z (idx 3)) (trans z (idx 1))))))

(defskeleton envelope-plus
  (vars (n v data) (pcr-id pcr-id-0 text) (k aik akey) (tpm chan))
  (deflistener
    (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k) aik))
  (defstrand alice 4 (n n) (v v) (pcr-id pcr-id-0) (k k) (aik aik)
    (tpm tpm))
  (non-orig aik)
  (uniq-orig n v)
  (conf tpm)
  (traces
    ((recv
       (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k) aik))
      (send
        (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k)
          aik)))
    ((send tpm (cat "extend" pcr-id-0 n))
      (send tpm
        (cat "create-req" pcr-id-0 (hash (hash "0" n) "obtain")))
      (recv (enc "created" k pcr-id-0 (hash (hash "0" n) "obtain") aik))
      (send (enc v k))))
  (label 39)
  (unrealized (0 0) (1 2))
  (preskeleton)
  (origs (v (1 3)) (n (1 0)))
  (comment "Not a skeleton"))

(defskeleton envelope-plus
  (vars (n v data) (pcr-id pcr-id-0 pcr-id-1 text) (k aik akey)
    (pt pt-0 pt-1 pval) (tpm tpm-0 tpm-1 chan) (pcr locn))
  (deflistener
    (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k) aik))
  (defstrand alice 4 (n n) (v v) (pcr-id pcr-id-0) (k k) (aik aik)
    (tpm tpm))
  (defstrand tpm-create-key 2 (pcrval (hash (hash "0" n) "obtain"))
    (pcr-id pcr-id-0) (k k) (aik aik) (tpm tpm))
  (defstrand tpm-quote 3 (nonce (enc v k))
    (current-value (hash (hash "0" n) "refuse")) (pcr-id pcr-id)
    (aik aik) (tpm tpm-0) (pcr pcr))
  (defstrand tpm-extend-enc 3 (value "refuse")
    (current-value (hash "0" n)) (pcr-id pcr-id-1) (tpm tpm-1)
    (pcr pcr))
  (defstrand tpm-extend-enc 3 (value n) (current-value "0")
    (pcr-id pcr-id-0) (tpm tpm) (pcr pcr))
  (precedes ((1 0) (5 0)) ((1 1) (2 0)) ((1 3) (3 0)) ((2 1) (1 2))
    ((3 2) (0 0)) ((4 2) (3 1)) ((5 2) (4 1)))
  (non-orig aik (invk k))
  (uniq-orig n v k)
  (gen-st (hash "0" n) (hash (hash "0" n) "refuse"))
  (conf tpm)
  (auth tpm)
  (leads-to ((4 2) (3 1)) ((5 2) (4 1)))
  (operation nonce-test (contracted (pcr-id-2 pcr-id-0) (tpm-2 tpm)) n
    (5 0) (ch-msg tpm (cat "extend" pcr-id-0 n)))
  (strand-map 0 1 2 3 4 5)
  (traces
    ((recv
       (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k) aik))
      (send
        (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k)
          aik)))
    ((send tpm (cat "extend" pcr-id-0 n))
      (send tpm
        (cat "create-req" pcr-id-0 (hash (hash "0" n) "obtain")))
      (recv (enc "created" k pcr-id-0 (hash (hash "0" n) "obtain") aik))
      (send (enc v k)))
    ((recv tpm (cat "create-req" pcr-id-0 (hash (hash "0" n) "obtain")))
      (send
        (enc "created" k pcr-id-0 (hash (hash "0" n) "obtain") aik)))
    ((recv tpm-0 (cat "quote" pcr-id (enc v k)))
      (load pcr (cat pt (hash (hash "0" n) "refuse")))
      (send
        (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k)
          aik)))
    ((recv tpm-1 (cat "extend" pcr-id-1 "refuse"))
      (load pcr (cat pt-0 (hash "0" n)))
      (stor pcr (cat pt (hash (hash "0" n) "refuse"))))
    ((recv tpm (cat "extend" pcr-id-0 n)) (load pcr (cat pt-1 "0"))
      (stor pcr (cat pt-0 (hash "0" n)))))
  (label 46)
  (parent 39)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((n n) (v v) (k k) (aik aik) (pcr-id pcr-id) (pcr-id-0 pcr-id-0)
        (tpm tpm))))
  (origs (pt-0 (5 2)) (pt (4 2)) (n (1 0)) (k (2 1)) (v (1 3))))

(comment "Nothing left to do")

(defprotocol envelope-plus basic
  (defrole tpm-power-on
    (vars (current-value mesg) (pcr locn) (tpm chan))
    (trace (recv tpm "power on") (load pcr current-value)
      (stor pcr "0")))
  (defrole tpm-extend-enc
    (vars (value current-value mesg) (pcr-id text) (pcr locn)
      (tpm chan))
    (trace (recv tpm (cat "extend" pcr-id value))
      (load pcr current-value) (stor pcr (hash current-value value))
      (send "ext ok")))
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
    (vars (n v data) (pcr-id text) (k aik akey) (tpm chan))
    (trace (send tpm (cat "extend" pcr-id n))
      (send tpm (cat "create-req" pcr-id (hash (hash "0" n) "obtain")))
      (recv (enc "created" k pcr-id (hash (hash "0" n) "obtain") aik))
      (send (enc v k)))
    (non-orig aik)
    (uniq-orig n v)
    (conf tpm)
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
        (and (p "tpm-extend-enc" z (idx 2))
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
  (defrule ordered-extends
    (forall ((y z strd) (pcr locn))
      (implies
        (and (p "tpm-extend-enc" y (idx 3))
          (p "tpm-extend-enc" z (idx 3))
          (p "tpm-extend-enc" "pcr" y pcr)
          (p "tpm-extend-enc" "pcr" z pcr))
        (or
          (= y z)
          (prec y (idx 2) z (idx 1))
          (prec z (idx 2) y (idx 1))))))
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
  (defgenrule trRl_tpm-extend-enc-at-2
    (forall ((z strd))
      (implies (p "tpm-extend-enc" z (idx 3)) (trans z (idx 2)))))
  (defgenrule trRl_tpm-extend-enc-at-1
    (forall ((z strd))
      (implies (p "tpm-extend-enc" z (idx 3)) (trans z (idx 1))))))

(defskeleton envelope-plus
  (vars (n v data) (pcr-id pcr-id-0 text) (k aik akey) (tpm chan))
  (deflistener
    (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k) aik))
  (deflistener v)
  (defstrand alice 4 (n n) (v v) (pcr-id pcr-id-0) (k k) (aik aik)
    (tpm tpm))
  (non-orig aik)
  (uniq-orig n v)
  (conf tpm)
  (traces
    ((recv
       (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k) aik))
      (send
        (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k)
          aik))) ((recv v) (send v))
    ((send tpm (cat "extend" pcr-id-0 n))
      (send tpm
        (cat "create-req" pcr-id-0 (hash (hash "0" n) "obtain")))
      (recv (enc "created" k pcr-id-0 (hash (hash "0" n) "obtain") aik))
      (send (enc v k))))
  (label 47)
  (unrealized (0 0) (1 0) (2 2))
  (preskeleton)
  (origs (v (2 3)) (n (2 0)))
  (comment "Not a skeleton"))

(defskeleton envelope-plus
  (vars (n v data) (pcr-id pcr-id-0 pcr-id-1 pcr-id-2 text) (k aik akey)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval)
    (tpm tpm-0 tpm-1 tpm-2 tpm-3 chan) (pcr pcr-0 locn))
  (deflistener
    (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k) aik))
  (deflistener v)
  (defstrand alice 4 (n n) (v v) (pcr-id pcr-id-0) (k k) (aik aik)
    (tpm tpm))
  (defstrand tpm-create-key 2 (pcrval (hash (hash "0" n) "obtain"))
    (pcr-id pcr-id-0) (k k) (aik aik) (tpm tpm))
  (defstrand tpm-decrypt 4 (m v)
    (current-value (hash (hash "0" n) "obtain")) (pcr-id pcr-id-0) (k k)
    (aik aik) (tpm tpm-0) (pcr pcr))
  (defstrand tpm-extend-enc 3 (value "obtain")
    (current-value (hash "0" n)) (pcr-id pcr-id-1) (tpm tpm-1)
    (pcr pcr))
  (defstrand tpm-extend-enc 3 (value n) (current-value "0")
    (pcr-id pcr-id-0) (tpm tpm) (pcr pcr))
  (defstrand tpm-quote 3 (nonce (enc v k))
    (current-value (hash (hash "0" n) "refuse")) (pcr-id pcr-id)
    (aik aik) (tpm tpm-2) (pcr pcr-0))
  (defstrand tpm-extend-enc 3 (value "refuse")
    (current-value (hash "0" n)) (pcr-id pcr-id-2) (tpm tpm-3)
    (pcr pcr-0))
  (defstrand tpm-extend-enc 3 (value n) (current-value "0")
    (pcr-id pcr-id-0) (tpm tpm) (pcr pcr-0))
  (precedes ((2 0) (6 0)) ((2 0) (9 0)) ((2 1) (3 0)) ((2 3) (4 0))
    ((2 3) (7 0)) ((3 1) (2 2)) ((4 3) (1 0)) ((5 2) (4 2))
    ((6 2) (5 1)) ((7 2) (0 0)) ((8 2) (7 1)) ((9 2) (8 1)))
  (non-orig aik (invk k))
  (uniq-orig n v k)
  (gen-st (hash "0" n) (hash (hash "0" n) "obtain")
    (hash (hash "0" n) "refuse"))
  (conf tpm)
  (auth tpm)
  (leads-to ((5 2) (4 2)) ((6 2) (5 1)) ((8 2) (7 1)) ((9 2) (8 1)))
  (operation nonce-test (contracted (pcr-id-3 pcr-id-0) (tpm-4 tpm)) n
    (9 0) (ch-msg tpm (cat "extend" pcr-id-0 n)))
  (strand-map 0 1 2 3 4 5 6 7 8 9)
  (traces
    ((recv
       (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k) aik))
      (send
        (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k)
          aik))) ((recv v) (send v))
    ((send tpm (cat "extend" pcr-id-0 n))
      (send tpm
        (cat "create-req" pcr-id-0 (hash (hash "0" n) "obtain")))
      (recv (enc "created" k pcr-id-0 (hash (hash "0" n) "obtain") aik))
      (send (enc v k)))
    ((recv tpm (cat "create-req" pcr-id-0 (hash (hash "0" n) "obtain")))
      (send
        (enc "created" k pcr-id-0 (hash (hash "0" n) "obtain") aik)))
    ((recv tpm-0 (cat "decrypt" (enc v k)))
      (recv (enc "created" k pcr-id-0 (hash (hash "0" n) "obtain") aik))
      (load pcr (cat pt (hash (hash "0" n) "obtain"))) (send v))
    ((recv tpm-1 (cat "extend" pcr-id-1 "obtain"))
      (load pcr (cat pt-0 (hash "0" n)))
      (stor pcr (cat pt (hash (hash "0" n) "obtain"))))
    ((recv tpm (cat "extend" pcr-id-0 n)) (load pcr (cat pt-1 "0"))
      (stor pcr (cat pt-0 (hash "0" n))))
    ((recv tpm-2 (cat "quote" pcr-id (enc v k)))
      (load pcr-0 (cat pt-2 (hash (hash "0" n) "refuse")))
      (send
        (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k)
          aik)))
    ((recv tpm-3 (cat "extend" pcr-id-2 "refuse"))
      (load pcr-0 (cat pt-3 (hash "0" n)))
      (stor pcr-0 (cat pt-2 (hash (hash "0" n) "refuse"))))
    ((recv tpm (cat "extend" pcr-id-0 n)) (load pcr-0 (cat pt-4 "0"))
      (stor pcr-0 (cat pt-3 (hash "0" n)))))
  (label 59)
  (parent 47)
  (realized)
  (shape)
  (maps
    ((0 1 2)
      ((n n) (v v) (k k) (aik aik) (pcr-id pcr-id) (pcr-id-0 pcr-id-0)
        (tpm tpm))))
  (origs (pt-3 (9 2)) (pt-2 (8 2)) (pt-0 (6 2)) (pt (5 2)) (k (3 1))
    (n (2 0)) (v (2 3))))

(comment "Nothing left to do")

(defprotocol envelope-plus-2 basic
  (defrole tpm-power-on
    (vars (current-value mesg) (pcr locn) (tpm chan))
    (trace (recv tpm "power on") (load pcr current-value)
      (stor pcr "0")))
  (defrole tpm-extend-enc
    (vars (value current-value mesg) (pcr-id text) (pcr locn)
      (tpm chan))
    (trace (recv tpm (cat "extend" pcr-id value))
      (load pcr current-value) (stor pcr (hash current-value value))
      (send "ext ok")))
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
    (vars (n v data) (pcr-id text) (k aik akey) (tpm chan))
    (trace (send tpm (cat "extend" pcr-id n))
      (send tpm (cat "create-req" pcr-id (hash (hash "0" n) "obtain")))
      (recv (enc "created" k pcr-id (hash (hash "0" n) "obtain") aik))
      (send (enc v k)))
    (non-orig aik)
    (uniq-orig n v)
    (conf tpm)
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
        (and (p "tpm-extend-enc" z (idx 2))
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
  (defrule pcr-id-identifies-pcr
    (forall ((y z strd) (pcr-id text) (pcr pcr-0 locn))
      (implies
        (and (p "tpm-extend-enc" y (idx 3))
          (p "tpm-extend-enc" z (idx 3))
          (p "tpm-extend-enc" "pcr-id" y pcr-id)
          (p "tpm-extend-enc" "pcr-id" z pcr-id)
          (p "tpm-extend-enc" "pcr" y pcr)
          (p "tpm-extend-enc" "pcr" z pcr-0))
        (= pcr pcr-0))))
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
  (defgenrule trRl_tpm-extend-enc-at-2
    (forall ((z strd))
      (implies (p "tpm-extend-enc" z (idx 3)) (trans z (idx 2)))))
  (defgenrule trRl_tpm-extend-enc-at-1
    (forall ((z strd))
      (implies (p "tpm-extend-enc" z (idx 3)) (trans z (idx 1))))))

(defskeleton envelope-plus-2
  (vars (v n data) (pcr-id text) (k aik akey) (tpm chan))
  (deflistener v)
  (defstrand alice 4 (n n) (v v) (pcr-id pcr-id) (k k) (aik aik)
    (tpm tpm))
  (non-orig aik)
  (uniq-orig v n)
  (conf tpm)
  (traces ((recv v) (send v))
    ((send tpm (cat "extend" pcr-id n))
      (send tpm (cat "create-req" pcr-id (hash (hash "0" n) "obtain")))
      (recv (enc "created" k pcr-id (hash (hash "0" n) "obtain") aik))
      (send (enc v k))))
  (label 60)
  (unrealized (0 0) (1 2))
  (preskeleton)
  (origs (v (1 3)) (n (1 0)))
  (comment "Not a skeleton"))

(defskeleton envelope-plus-2
  (vars (v n data) (pcr-id pcr-id-0 text) (k aik akey)
    (pt pt-0 pt-1 pval) (tpm tpm-0 tpm-1 chan) (pcr locn))
  (deflistener v)
  (defstrand alice 4 (n n) (v v) (pcr-id pcr-id) (k k) (aik aik)
    (tpm tpm))
  (defstrand tpm-create-key 2 (pcrval (hash (hash "0" n) "obtain"))
    (pcr-id pcr-id) (k k) (aik aik) (tpm tpm))
  (defstrand tpm-decrypt 4 (m v)
    (current-value (hash (hash "0" n) "obtain")) (pcr-id pcr-id) (k k)
    (aik aik) (tpm tpm-0) (pcr pcr))
  (defstrand tpm-extend-enc 3 (value "obtain")
    (current-value (hash "0" n)) (pcr-id pcr-id-0) (tpm tpm-1)
    (pcr pcr))
  (defstrand tpm-extend-enc 3 (value n) (current-value "0")
    (pcr-id pcr-id) (tpm tpm) (pcr pcr))
  (precedes ((1 0) (5 0)) ((1 1) (2 0)) ((1 3) (3 0)) ((2 1) (1 2))
    ((3 3) (0 0)) ((4 2) (3 2)) ((5 2) (4 1)))
  (non-orig aik (invk k))
  (uniq-orig v n k)
  (gen-st (hash "0" n) (hash (hash "0" n) "obtain"))
  (conf tpm)
  (auth tpm)
  (leads-to ((4 2) (3 2)) ((5 2) (4 1)))
  (operation nonce-test (contracted (pcr-id-1 pcr-id) (tpm-2 tpm)) n
    (5 0) (ch-msg tpm (cat "extend" pcr-id n)))
  (strand-map 0 1 2 3 4 5)
  (traces ((recv v) (send v))
    ((send tpm (cat "extend" pcr-id n))
      (send tpm (cat "create-req" pcr-id (hash (hash "0" n) "obtain")))
      (recv (enc "created" k pcr-id (hash (hash "0" n) "obtain") aik))
      (send (enc v k)))
    ((recv tpm (cat "create-req" pcr-id (hash (hash "0" n) "obtain")))
      (send (enc "created" k pcr-id (hash (hash "0" n) "obtain") aik)))
    ((recv tpm-0 (cat "decrypt" (enc v k)))
      (recv (enc "created" k pcr-id (hash (hash "0" n) "obtain") aik))
      (load pcr (cat pt (hash (hash "0" n) "obtain"))) (send v))
    ((recv tpm-1 (cat "extend" pcr-id-0 "obtain"))
      (load pcr (cat pt-0 (hash "0" n)))
      (stor pcr (cat pt (hash (hash "0" n) "obtain"))))
    ((recv tpm (cat "extend" pcr-id n)) (load pcr (cat pt-1 "0"))
      (stor pcr (cat pt-0 (hash "0" n)))))
  (label 68)
  (parent 60)
  (realized)
  (shape)
  (maps ((0 1) ((v v) (n n) (pcr-id pcr-id) (k k) (aik aik) (tpm tpm))))
  (origs (pt-0 (5 2)) (pt (4 2)) (k (2 1)) (n (1 0)) (v (1 3))))

(comment "Nothing left to do")

(defprotocol envelope-plus-2 basic
  (defrole tpm-power-on
    (vars (current-value mesg) (pcr locn) (tpm chan))
    (trace (recv tpm "power on") (load pcr current-value)
      (stor pcr "0")))
  (defrole tpm-extend-enc
    (vars (value current-value mesg) (pcr-id text) (pcr locn)
      (tpm chan))
    (trace (recv tpm (cat "extend" pcr-id value))
      (load pcr current-value) (stor pcr (hash current-value value))
      (send "ext ok")))
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
    (vars (n v data) (pcr-id text) (k aik akey) (tpm chan))
    (trace (send tpm (cat "extend" pcr-id n))
      (send tpm (cat "create-req" pcr-id (hash (hash "0" n) "obtain")))
      (recv (enc "created" k pcr-id (hash (hash "0" n) "obtain") aik))
      (send (enc v k)))
    (non-orig aik)
    (uniq-orig n v)
    (conf tpm)
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
        (and (p "tpm-extend-enc" z (idx 2))
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
  (defrule pcr-id-identifies-pcr
    (forall ((y z strd) (pcr-id text) (pcr pcr-0 locn))
      (implies
        (and (p "tpm-extend-enc" y (idx 3))
          (p "tpm-extend-enc" z (idx 3))
          (p "tpm-extend-enc" "pcr-id" y pcr-id)
          (p "tpm-extend-enc" "pcr-id" z pcr-id)
          (p "tpm-extend-enc" "pcr" y pcr)
          (p "tpm-extend-enc" "pcr" z pcr-0))
        (= pcr pcr-0))))
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
  (defgenrule trRl_tpm-extend-enc-at-2
    (forall ((z strd))
      (implies (p "tpm-extend-enc" z (idx 3)) (trans z (idx 2)))))
  (defgenrule trRl_tpm-extend-enc-at-1
    (forall ((z strd))
      (implies (p "tpm-extend-enc" z (idx 3)) (trans z (idx 1))))))

(defskeleton envelope-plus-2
  (vars (n v data) (pcr-id pcr-id-0 text) (k aik akey) (tpm chan))
  (deflistener
    (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k) aik))
  (defstrand alice 4 (n n) (v v) (pcr-id pcr-id-0) (k k) (aik aik)
    (tpm tpm))
  (non-orig aik)
  (uniq-orig n v)
  (conf tpm)
  (traces
    ((recv
       (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k) aik))
      (send
        (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k)
          aik)))
    ((send tpm (cat "extend" pcr-id-0 n))
      (send tpm
        (cat "create-req" pcr-id-0 (hash (hash "0" n) "obtain")))
      (recv (enc "created" k pcr-id-0 (hash (hash "0" n) "obtain") aik))
      (send (enc v k))))
  (label 69)
  (unrealized (0 0) (1 2))
  (preskeleton)
  (origs (v (1 3)) (n (1 0)))
  (comment "Not a skeleton"))

(defskeleton envelope-plus-2
  (vars (n v data) (pcr-id pcr-id-0 pcr-id-1 text) (k aik akey)
    (pt pt-0 pt-1 pval) (tpm tpm-0 tpm-1 chan) (pcr locn))
  (deflistener
    (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k) aik))
  (defstrand alice 4 (n n) (v v) (pcr-id pcr-id-0) (k k) (aik aik)
    (tpm tpm))
  (defstrand tpm-create-key 2 (pcrval (hash (hash "0" n) "obtain"))
    (pcr-id pcr-id-0) (k k) (aik aik) (tpm tpm))
  (defstrand tpm-quote 3 (nonce (enc v k))
    (current-value (hash (hash "0" n) "refuse")) (pcr-id pcr-id)
    (aik aik) (tpm tpm-0) (pcr pcr))
  (defstrand tpm-extend-enc 3 (value "refuse")
    (current-value (hash "0" n)) (pcr-id pcr-id-1) (tpm tpm-1)
    (pcr pcr))
  (defstrand tpm-extend-enc 3 (value n) (current-value "0")
    (pcr-id pcr-id-0) (tpm tpm) (pcr pcr))
  (precedes ((1 0) (5 0)) ((1 1) (2 0)) ((1 3) (3 0)) ((2 1) (1 2))
    ((3 2) (0 0)) ((4 2) (3 1)) ((5 2) (4 1)))
  (non-orig aik (invk k))
  (uniq-orig n v k)
  (gen-st (hash "0" n) (hash (hash "0" n) "refuse"))
  (conf tpm)
  (auth tpm)
  (leads-to ((4 2) (3 1)) ((5 2) (4 1)))
  (operation nonce-test (contracted (pcr-id-2 pcr-id-0) (tpm-2 tpm)) n
    (5 0) (ch-msg tpm (cat "extend" pcr-id-0 n)))
  (strand-map 0 1 2 3 4 5)
  (traces
    ((recv
       (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k) aik))
      (send
        (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k)
          aik)))
    ((send tpm (cat "extend" pcr-id-0 n))
      (send tpm
        (cat "create-req" pcr-id-0 (hash (hash "0" n) "obtain")))
      (recv (enc "created" k pcr-id-0 (hash (hash "0" n) "obtain") aik))
      (send (enc v k)))
    ((recv tpm (cat "create-req" pcr-id-0 (hash (hash "0" n) "obtain")))
      (send
        (enc "created" k pcr-id-0 (hash (hash "0" n) "obtain") aik)))
    ((recv tpm-0 (cat "quote" pcr-id (enc v k)))
      (load pcr (cat pt (hash (hash "0" n) "refuse")))
      (send
        (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k)
          aik)))
    ((recv tpm-1 (cat "extend" pcr-id-1 "refuse"))
      (load pcr (cat pt-0 (hash "0" n)))
      (stor pcr (cat pt (hash (hash "0" n) "refuse"))))
    ((recv tpm (cat "extend" pcr-id-0 n)) (load pcr (cat pt-1 "0"))
      (stor pcr (cat pt-0 (hash "0" n)))))
  (label 76)
  (parent 69)
  (realized)
  (shape)
  (maps
    ((0 1)
      ((n n) (v v) (k k) (aik aik) (pcr-id pcr-id) (pcr-id-0 pcr-id-0)
        (tpm tpm))))
  (origs (pt-0 (5 2)) (pt (4 2)) (n (1 0)) (k (2 1)) (v (1 3))))

(comment "Nothing left to do")

(defprotocol envelope-plus-2 basic
  (defrole tpm-power-on
    (vars (current-value mesg) (pcr locn) (tpm chan))
    (trace (recv tpm "power on") (load pcr current-value)
      (stor pcr "0")))
  (defrole tpm-extend-enc
    (vars (value current-value mesg) (pcr-id text) (pcr locn)
      (tpm chan))
    (trace (recv tpm (cat "extend" pcr-id value))
      (load pcr current-value) (stor pcr (hash current-value value))
      (send "ext ok")))
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
    (vars (n v data) (pcr-id text) (k aik akey) (tpm chan))
    (trace (send tpm (cat "extend" pcr-id n))
      (send tpm (cat "create-req" pcr-id (hash (hash "0" n) "obtain")))
      (recv (enc "created" k pcr-id (hash (hash "0" n) "obtain") aik))
      (send (enc v k)))
    (non-orig aik)
    (uniq-orig n v)
    (conf tpm)
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
        (and (p "tpm-extend-enc" z (idx 2))
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
  (defrule pcr-id-identifies-pcr
    (forall ((y z strd) (pcr-id text) (pcr pcr-0 locn))
      (implies
        (and (p "tpm-extend-enc" y (idx 3))
          (p "tpm-extend-enc" z (idx 3))
          (p "tpm-extend-enc" "pcr-id" y pcr-id)
          (p "tpm-extend-enc" "pcr-id" z pcr-id)
          (p "tpm-extend-enc" "pcr" y pcr)
          (p "tpm-extend-enc" "pcr" z pcr-0))
        (= pcr pcr-0))))
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
  (defgenrule trRl_tpm-extend-enc-at-2
    (forall ((z strd))
      (implies (p "tpm-extend-enc" z (idx 3)) (trans z (idx 2)))))
  (defgenrule trRl_tpm-extend-enc-at-1
    (forall ((z strd))
      (implies (p "tpm-extend-enc" z (idx 3)) (trans z (idx 1))))))

(defskeleton envelope-plus-2
  (vars (n v data) (pcr-id pcr-id-0 text) (k aik akey) (tpm chan))
  (deflistener
    (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k) aik))
  (deflistener v)
  (defstrand alice 4 (n n) (v v) (pcr-id pcr-id-0) (k k) (aik aik)
    (tpm tpm))
  (non-orig aik)
  (uniq-orig n v)
  (conf tpm)
  (traces
    ((recv
       (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k) aik))
      (send
        (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k)
          aik))) ((recv v) (send v))
    ((send tpm (cat "extend" pcr-id-0 n))
      (send tpm
        (cat "create-req" pcr-id-0 (hash (hash "0" n) "obtain")))
      (recv (enc "created" k pcr-id-0 (hash (hash "0" n) "obtain") aik))
      (send (enc v k))))
  (label 77)
  (unrealized (0 0) (1 0) (2 2))
  (preskeleton)
  (origs (v (2 3)) (n (2 0)))
  (comment "Not a skeleton"))

(defskeleton envelope-plus-2
  (vars (n v data) (pcr-id pcr-id-0 pcr-id-1 pcr-id-2 text) (k aik akey)
    (pt pt-0 pt-1 pt-2 pt-3 pt-4 pval)
    (tpm tpm-0 tpm-1 tpm-2 tpm-3 chan) (pcr locn))
  (deflistener
    (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k) aik))
  (deflistener v)
  (defstrand alice 4 (n n) (v v) (pcr-id pcr-id-0) (k k) (aik aik)
    (tpm tpm))
  (defstrand tpm-create-key 2 (pcrval (hash (hash "0" n) "obtain"))
    (pcr-id pcr-id-0) (k k) (aik aik) (tpm tpm))
  (defstrand tpm-decrypt 4 (m v)
    (current-value (hash (hash "0" n) "obtain")) (pcr-id pcr-id-0) (k k)
    (aik aik) (tpm tpm-0) (pcr pcr))
  (defstrand tpm-extend-enc 3 (value "obtain")
    (current-value (hash "0" n)) (pcr-id pcr-id-1) (tpm tpm-1)
    (pcr pcr))
  (defstrand tpm-extend-enc 3 (value n) (current-value "0")
    (pcr-id pcr-id-0) (tpm tpm) (pcr pcr))
  (defstrand tpm-quote 3 (nonce (enc v k))
    (current-value (hash (hash "0" n) "refuse")) (pcr-id pcr-id)
    (aik aik) (tpm tpm-2) (pcr pcr))
  (defstrand tpm-extend-enc 3 (value "refuse")
    (current-value (hash "0" n)) (pcr-id pcr-id-2) (tpm tpm-3)
    (pcr pcr))
  (defstrand tpm-extend-enc 3 (value n) (current-value "0")
    (pcr-id pcr-id-0) (tpm tpm) (pcr pcr))
  (precedes ((2 0) (6 0)) ((2 0) (9 0)) ((2 1) (3 0)) ((2 3) (4 0))
    ((2 3) (7 0)) ((3 1) (2 2)) ((4 3) (1 0)) ((5 2) (4 2))
    ((6 2) (5 1)) ((7 2) (0 0)) ((8 2) (7 1)) ((9 2) (8 1)))
  (non-orig aik (invk k))
  (uniq-orig n v k)
  (gen-st (hash "0" n) (hash (hash "0" n) "obtain")
    (hash (hash "0" n) "refuse"))
  (conf tpm)
  (auth tpm)
  (leads-to ((5 2) (4 2)) ((6 2) (5 1)) ((8 2) (7 1)) ((9 2) (8 1)))
  (operation nonce-test
    (contracted (pcr-0 pcr) (pcr-id-3 pcr-id-0) (tpm-4 tpm)) n (9 0)
    (ch-msg tpm (cat "extend" pcr-id-0 n)))
  (strand-map 0 1 2 3 4 5 6 7 8 9)
  (traces
    ((recv
       (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k) aik))
      (send
        (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k)
          aik))) ((recv v) (send v))
    ((send tpm (cat "extend" pcr-id-0 n))
      (send tpm
        (cat "create-req" pcr-id-0 (hash (hash "0" n) "obtain")))
      (recv (enc "created" k pcr-id-0 (hash (hash "0" n) "obtain") aik))
      (send (enc v k)))
    ((recv tpm (cat "create-req" pcr-id-0 (hash (hash "0" n) "obtain")))
      (send
        (enc "created" k pcr-id-0 (hash (hash "0" n) "obtain") aik)))
    ((recv tpm-0 (cat "decrypt" (enc v k)))
      (recv (enc "created" k pcr-id-0 (hash (hash "0" n) "obtain") aik))
      (load pcr (cat pt (hash (hash "0" n) "obtain"))) (send v))
    ((recv tpm-1 (cat "extend" pcr-id-1 "obtain"))
      (load pcr (cat pt-0 (hash "0" n)))
      (stor pcr (cat pt (hash (hash "0" n) "obtain"))))
    ((recv tpm (cat "extend" pcr-id-0 n)) (load pcr (cat pt-1 "0"))
      (stor pcr (cat pt-0 (hash "0" n))))
    ((recv tpm-2 (cat "quote" pcr-id (enc v k)))
      (load pcr (cat pt-2 (hash (hash "0" n) "refuse")))
      (send
        (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k)
          aik)))
    ((recv tpm-3 (cat "extend" pcr-id-2 "refuse"))
      (load pcr (cat pt-3 (hash "0" n)))
      (stor pcr (cat pt-2 (hash (hash "0" n) "refuse"))))
    ((recv tpm (cat "extend" pcr-id-0 n)) (load pcr (cat pt-4 "0"))
      (stor pcr (cat pt-3 (hash "0" n)))))
  (label 89)
  (parent 77)
  (realized)
  (shape)
  (maps
    ((0 1 2)
      ((n n) (v v) (k k) (aik aik) (pcr-id pcr-id) (pcr-id-0 pcr-id-0)
        (tpm tpm))))
  (origs (pt-3 (9 2)) (pt-2 (8 2)) (pt-0 (6 2)) (pt (5 2)) (k (3 1))
    (n (2 0)) (v (2 3))))

(comment "Nothing left to do")
