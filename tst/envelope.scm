(herald "Envelope Protocol" (bound 50))

;; This is the refusal token
(defmacro (refuse n v k aik)
  (enc "quote" (hash (hash "0" n) "refuse") (enc v k) aik))

;;; This protocol tracks the TPM's PCR state
;;; by sending a message with the current PCR
;;; value encrypted by a hashed secret key.
;;; The hash is used to prevent a confusion with
;;; the key for an encrypted session.

(defprotocol envelope basic

  ;; Power on sets the pcr to 0
  (defrole tpm-power-on
    (vars (pcrkey skey))
    (trace
     (recv "power on")
     (send (enc "0" (hash pcrkey))))
    (non-orig pcrkey))

  ;; The extend command takes the value to
  ;; extend and the current PCR value (in the
  ;; form of a message encrypted with the special
  ;; PCR state key) and produces the hash of the
  ;; two values (by sending it encrypted in the
  ;; special PCR state key).
  (defrole tpm-extend
    (vars (value current-value mesg) (pcrkey skey))
    (trace
     (recv (cat "extend" value))
     (recv (enc current-value (hash pcrkey))) ;; MSR lhs (deleted)
     (send (enc (hash current-value value) (hash pcrkey))) ;; MSR rhs
     (send "ext ok"))
    (non-orig pcrkey))

  ;; The extend command can also occur within an
  ;; encrypted session.  We assume some session key already exists
  (defrole tpm-extend-enc
    (vars (value current-value mesg) (pcrkey esk skey))
    (trace
     (recv (enc "extend" value esk))
     (recv (enc current-value (hash pcrkey))) ;; MSR lhs (deleted)
     (send (enc (hash current-value value) (hash pcrkey))) ;; MSR rhs
     (send "ext ok"))
    (non-orig pcrkey esk))

  ;; The TPM must retrieve the current pcr value.  Notice that
  ;; the nonce is of sort mesg, which allows non-atomic values.
  (defrole tpm-quote
    (vars (nonce current-value mesg) (pcrkey skey) (aik akey))
    (trace
     (recv (cat "quote" nonce))
     (recv (enc current-value (hash pcrkey))) ;; MSR lhs (not deleted)
     (send (enc "quote" current-value nonce aik)))
    (non-orig aik pcrkey))

  ;; This role creates a key whose use is restricted to a
  ;; requested pcr value (since we only model one pcr).
  ;; It doesn't create or change any TPM state.
  (defrole tpm-create-key
    (vars (k aik akey) (pcrval mesg) (esk skey))
    (trace
     (recv (enc "create key" pcrval esk)) ;; encryption prevents weird shapes
     (send (enc "created" k pcrval aik)));; no tpm state is set
    (uniq-orig k)
    (non-orig (invk k) aik esk))

  ;; This role receives an encryption and a previously
  ;; made key structure that restricts the decryption key
  ;; to be used with a certain pcr value.  It retrieves the
  ;; current value and checks that it matches before decrypting.
  (defrole tpm-decrypt
    (vars (m pcrvals mesg) (k aik akey) (pcrkey skey))
    (trace
     (recv (cat "decrypt" (enc m k)))
     (recv (enc "created" k pcrvals aik))
     (recv (enc pcrvals (hash pcrkey))) ;; MSR lhs (not deleted)
     (send m))
    (non-orig aik pcrkey))

  ;; Alice extends a pcr with a fresh nonce in an encrypted
  ;; session.  She has the TPM create a new key whose use is
  ;; bound to the hash of pcr value she just created with the
  ;; string "obtain".  She then encrypts her fresh secret with
  ;; this newly created key.
  (defrole alice
    (vars (n v data) (esk skey) (k aik akey))
    (trace
     (send (enc "extend" n esk))
     (send (enc "create key" (hash (hash "0" n) "obtain") esk))
     (recv (enc "created" k (hash (hash "0" n) "obtain") aik))
     (send (enc v k)))
    (uniq-orig n v)
    (non-orig aik esk)))

;(comment
(defskeleton envelope
  (vars (v data))
  (deflistener v)
  (defstrand alice 4 (v v)))

(defskeleton envelope
  (vars (n v data) (k aik akey))
  (deflistener (refuse n v k aik))
  (defstrand alice 4 (n n) (v v) (k k) (aik aik)))
;)

(defskeleton envelope
  (vars (n v data) (k aik akey))
  (deflistener (refuse n v k aik))
  (deflistener v)
  (defstrand alice 4 (n n) (v v) (k k) (aik aik)))
