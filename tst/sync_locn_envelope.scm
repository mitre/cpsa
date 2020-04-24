(herald "Envelope Protocol, location-based version"
   	;;   (reverse-nodes)
	;; (try-old-strands)
	(check-nonces)
	(bound 30)
	(limit 6000)) 

;;; This file analyzes the Envelope Protocol using three rules sets.
;;; For each rule set, it checks three scenarios.  In every scenario,
;;; an Alice strand runs to completion.  In the first scenario, the
;;; obtain token is listened for.  In the second, a listener for the
;;; refusal token is included.  In the third scenario, both listeners
;;; are included.  The third scenario should be impossible, but rules
;;; are required to accurately model state.
;;;
;;; The first rule set is empty and the answer to the third scenario
;;; shows a case is which the TPM's PCR state splits.  The second rule
;;; set forces TPM extends to be linearly ordered.  However, in this
;;; case, there are two TPMs when there should be one as Alice uses
;;; one TPM storage key to communicate with both TPMs.  The final rule
;;; set includes a rule about storage keys and thus accurately models
;;; state.
;;;
;;; Macros are used to avoid copying roles and scenarios.

;; This is the refusal token
(defmacro (refuse pcr-id n v k aik)
  (enc "quote" pcr-id (hash (hash "0" n) "refuse") (enc v k) aik))

;;; This protocol tracks the TPM's PCR state
;;; by sending a message with the current PCR
;;; value encrypted by a hashed secret key.
;;; The hash is used to prevent a confusion with
;;; the key for an encrypted session.

(defmacro (roles)
  (^
   ;; Power on sets the pcr to 0
   (defrole tpm-power-on 
     (vars (current-value mesg) (pcr locn) (tpm chan)) 
     (trace
      (recv tpm "power on")
      (load pcr current-value) 
      (stor pcr "0")))

   ;; The extend command takes the value to extend and the current PCR
   ;; value and produces the hash of the two values.
   ;;     (defrole tpm-extend
   ;;        (vars (value current-value mesg) (pcr locn))
   ;;        (trace
   ;;         (recv (cat "extend" value))
   ;;         (recv pcr current-value)		    ;; MSR lhs (deleted)
   ;;         (stor pcr (hash current-value value)) ;; MSR rhs
   ;;         (send "ext ok")))

   ;; The extend command can also occur within an
   ;; encrypted session.  We assume some session key already exists
   (defrole tpm-extend-enc
     (vars (value current-value mesg) (pcr-id nonce text) (pcr locn) (tpm chan))
     (trace
      (send tpm (cat "token" nonce))
      (recv tpm (cat "extend" pcr-id value (hash pcr-id value nonce)))
      (load pcr current-value)		    ;; MSR lhs (deleted)
      (stor pcr (hash current-value value)) ;; MSR rhs
      (send "ext ok"))
     (uniq-orig nonce))

   ;; The TPM must retrieve the current pcr value.  Notice that
   ;; the nonce is of sort mesg, which allows non-atomic values.
   (defrole tpm-quote
     (vars (nonce current-value mesg) (pcr-id text) (aik akey) (pcr locn) (tpm chan))
     (trace
      (recv tpm (cat "quote" pcr-id nonce))
      (load pcr current-value) ;; MSR lhs (not deleted)
      (send (enc "quote" pcr-id current-value nonce aik))))

   ;; This role creates a key whose use is restricted to a
   ;; requested pcr value (since we only model one pcr).
   ;; It doesn't create or change any TPM state.
   (defrole tpm-create-key
     (vars (k aik akey) (pcr-id text) (pcrval mesg) (tpm chan))
     (trace
      (recv tpm (cat "create-req" pcr-id pcrval))
      (send (enc "created" k pcr-id pcrval aik))) ;; no tpm state is set
     (uniq-orig k)
     (non-orig (invk k))
     (auth tpm)			; Weird shapes without auth 
     )
   
   ;; This role receives an encryption and a previously
   ;; made key structure that restricts the decryption key
   ;; to be used with a certain pcr value.  It retrieves the
   ;; current value and checks that it matches before decrypting.
   (defrole tpm-decrypt
     (vars (m current-value mesg) (pcr-id text) (k aik akey) (pcr locn) (tpm chan))
     (trace
      (recv tpm (cat "decrypt" (enc m k)))
      (recv (enc "created" k pcr-id current-value aik))
      (load pcr current-value) ;; MSR lhs (not deleted)
      (send m))
     (non-orig aik))

   ;; Alice extends a pcr with a fresh nonce in an encrypted
   ;; session.  She has the TPM create a new key whose use is
   ;; bound to the hash of pcr value she just created with the
   ;; string "obtain".  She then encrypts her fresh secret with
   ;; this newly created key.
   (defrole alice
     (vars (n v data) (pcr-id nonce text) (k aik akey) (tpm tpmconf chan))
     (trace
      (recv tpm (cat "token" nonce))
      (send tpmconf (cat "extend" pcr-id n (hash pcr-id n nonce)))
      (send tpm (cat "create-req" pcr-id (hash (hash "0" n) "obtain")))
      ;; (enc "create key" (hash (hash "0" n) "obtain") esk)
      (recv (enc "created" k pcr-id (hash (hash "0" n) "obtain") aik))
      (send (enc v k)))
     (neq (k aik))
     (uniq-orig n v)
     (non-orig aik)
     (conf tpmconf))))

(defmacro (genStV-rules)
  (^
   
;;      (defrule genStV-if-hashed-tpm-extend 
;;        (forall
;;         ((z strd) (v1 v2 mesg))
;;         (implies
;;          (and
;;   	(p "tpm-extend" z 2)
;;   	(p "tpm-extend" "current-value" z (hash v1 v2)))
;;          (gen-st (hash v1 v2)))))

   (defrule genStV-if-hashed-tpm-power-on
     (forall
      ((z strd) (v1 v2 mesg))
      (implies
       (and
	(p "tpm-power-on" z 2)
	(p "tpm-power-on" "current-value" z (hash v1 v2)))
       (gen-st (hash v1 v2)))))

   (defrule genStV-if-hashed-tpm-extend-enc 
     (forall
      ((z strd) (v1 v2 mesg))
      (implies
       (and
	(p "tpm-extend-enc" z 3)
	(p "tpm-extend-enc" "current-value" z (hash v1 v2)))
       (gen-st (hash v1 v2)))))

   (defrule genStV-if-hashed-tpm-decrypt
     (forall
      ((z strd) (v1 v2 mesg))
      (implies
       (and
	(p "tpm-decrypt" z 3)
	(p "tpm-decrypt" "current-value" z (hash v1 v2)))
       (gen-st (hash v1 v2)))))

   (defrule genStV-if-hashed-tpm-quote
     (forall
      ((z strd) (v1 v2 mesg))
      (implies
       (and
	(p "tpm-quote" z 2)
	(p "tpm-quote" "current-value" z (hash v1 v2)))
       (gen-st (hash v1 v2)))))

;;      (defrule genStV-not-catted-tpm-power-on
;;        (forall
;;         ((z strd) (v1 v2 mesg))
;;         (implies
;;          (and 
;;   	(p "tpm-power-on" z 2)
;;   	(p "tpm-power-on" "current-value" z (cat v1 v2)))
;;          (false))))
;;   
;;      (defrule genStV-not-catted-tpm-extend-enc 
;;        (forall
;;         ((z strd) (v1 v2 mesg))
;;         (implies
;;          (and
;;   	(p "tpm-extend-enc" z 2)
;;   	(p "tpm-extend-enc" "current-value" z (cat v1 v2)))
;;          (false))))
;;   
;;      (defrule genStV-not-catted-tpm-decrypt
;;        (forall
;;         ((z strd) (v1 v2 mesg))
;;         (implies
;;          (and
;;   	(p "tpm-decrypt" z 3)
;;   	(p "tpm-decrypt" "current-value" z (cat v1 v2)))
;;          (false))))
;;   
;;      (defrule genStV-not-catted-tpm-quote
;;        (forall
;;         ((z strd) (v1 v2 mesg))
;;         (implies
;;          (and
;;   	(p "tpm-quote" z 2)
;;   	(p "tpm-quote" "current-value" z (cat v1 v2)))
   ;;          (false))))
   ))

(defprotocol envelope basic
  (roles)
  (genStV-rules)
  ) 


(defskeleton envelope
  (vars (v data))
  (deflistener v)
  (defstrand alice 5 (v v)))

(defskeleton envelope
  (vars (n v data) (k aik akey) (pcr-id text))
  (deflistener (refuse pcr-id n v k aik))
  (defstrand alice 5 (n n) (v v) (k k) (aik aik)))

(defskeleton envelope
  (vars (n v data) (k aik akey) (pcr-id text))
  (deflistener (refuse pcr-id n v k aik))
  (deflistener v) 
  (defstrand alice 5 (n n) (v v) (k k) (aik aik)))

(defskeleton envelope
  (vars (n v data) (k aik akey) (pcr-id text))
  (deflistener (refuse pcr-id n v k aik))
  (deflistener v) 
  (defstrand alice 5 (n n) (v v) (k k) (aik aik))
  (facts (no-state-split)))

;;   (defprotocol envelope-plus basic
;;     (roles)
;;     (genStV-rules)
;;   
;;     (defrule ordered-extends
;;       (forall ((y z strd) (pcr locn))
;;   	    (implies
;;   	     (and (p "tpm-extend-enc" y 4)
;;   		  (p "tpm-extend-enc" z 4)
;;   		  (p "tpm-extend-enc" "pcr" y pcr)
;;   		  (p "tpm-extend-enc" "pcr" z pcr))
;;   	     (or (= y z)
;;   		 (prec y 3 z 2)
;;   		 (prec z 3 y 2))))))
;;   
;;   
;;   (defskeleton envelope-plus
;;     (vars (v data))
;;     (deflistener v)
;;     (defstrand alice 5 (v v)))
;;   
;;   (defskeleton envelope-plus
;;     (vars (n v data) (k aik akey) (pcr-id text))
;;     (deflistener (refuse pcr-id n v k aik))
;;     (defstrand alice 5 (n n) (v v) (k k) (aik aik)))
;;   
;;   (defskeleton envelope-plus
;;     (vars (n v data) (k aik akey) (pcr-id text))
;;     (deflistener (refuse pcr-id n v k aik))
;;     (deflistener v)
;;     (defstrand alice 5 (n n) (v v) (k k) (aik aik)))


(defprotocol envelope-plus-2 basic
  (roles)
  (genStV-rules)

  (defrule pcr-id-identifies-pcr 
    (forall ((y z strd) (pcr-id text) (pcr pcr-0 locn))
	    (implies
	     (and (p "tpm-extend-enc" y 3)
		  (p "tpm-extend-enc" z 3)
		  (p "tpm-extend-enc" "pcr-id" y pcr-id) 
		  (p "tpm-extend-enc" "pcr-id" z pcr-id)
		  (p "tpm-extend-enc" "pcr" y pcr)
		  (p "tpm-extend-enc" "pcr" z pcr-0))
	     (= pcr pcr-0))))) 

(defskeleton envelope-plus-2
  (vars (v data))
  (deflistener v)
  (defstrand alice 5 (v v)))

(defskeleton envelope-plus-2
  (vars (n v data) (k aik akey) (pcr-id text))
  (deflistener (refuse pcr-id n v k aik))
  (defstrand alice 5 (n n) (v v) (k k) (aik aik)))

(defskeleton envelope-plus-2
  (vars (n v data) (k aik akey) (pcr-id text))
  (deflistener (refuse pcr-id n v k aik))
  (deflistener v)
  (defstrand alice 5 (n n) (v v) (k k) (aik aik)))

(defskeleton envelope-plus-2
  (vars (n v data) (k aik akey) (pcr-id text))
  (deflistener (refuse pcr-id n v k aik))
  (deflistener v) 
  (defstrand alice 5 (n n) (v v) (k k) (aik aik))
  (facts (no-state-split)))

