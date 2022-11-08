(defprotocol weird basic
  (defrole originator
    (vars (k skey))
    (trace (send k))
    (uniq-orig k))
  (defrole guesser
    (vars (k skey) (a name))
    (trace (send (enc a k))))
  (defrole encryptor
    (vars (k skey) (a name))
    (trace (recv (enc a k)))))

;;; CPSA mistakenly concludes this is a skeleton.
(defskeleton weird
  (vars (k skey))
  (defstrand originator 1 (k k))
  (defstrand guesser 1 (k k)))

;;; CPSA mistakenly concludes it is possible for the encryptor to
;;; acquire k.
(defskeleton weird
  (vars (k skey))
  (defstrand originator 1 (k k))
  (defstrand encryptor 1 (k k)))

(defskeleton weird
  (vars (k skey))
  (defstrand originator 1 (k k))
  (defstrand encryptor 1 (k k))
  (precedes ((0 0) (1 0))))


(defprotocol weird-gen basic
  (defrole originator
    (vars (k skey))
    (trace (send k))
    (uniq-gen k))
  (defrole guesser
    (vars (k skey) (a name))
    (trace (send (enc a k))))
  (defrole encryptor
    (vars (k skey) (a name))
    (trace (recv (enc a k)))))

(defskeleton weird-gen
  (vars (k skey))
  (defstrand originator 1 (k k))
  (defstrand guesser 1 (k k)))

(defskeleton weird-gen
  (vars (k skey))
  (defstrand originator 1 (k k))
  (defstrand encryptor 1 (k k)))

(defskeleton weird-gen
  (vars (k skey))
  (defstrand originator 1 (k k))
  (defstrand encryptor 1 (k k))
  (precedes ((0 0) (1 0))))
