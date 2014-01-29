;; This protocol shows that it is possible to prune
;; two strands of a parent skeleton after augmenting
;; with a new strand.

(defprotocol nonaug-prune basic
  (defrole orig
    (vars (n text) (A B name) (k akey))
    (trace
     (send (enc n B B k))
     (send (enc n A k))
     (recv (enc n A A A k)))
    (uniq-orig n)
    (non-orig (invk k)))
  (defrole trans1
    (vars (n text) (A C name) (k akey))
    (trace
     (recv (enc n A A k))
     (recv (enc n A k))
     (send (enc n n C k))))
  (defrole trans2
    (vars (n text) (A name) (k akey))
    (trace
     (recv (enc n A k))
     (send (enc n A A A k))))
)

;; (defskeleton nonaug-prune
;;   (vars (n text) (A B C name) (k akey))
;;   (defstrand trans1 3 (n n) (A A) (C C) (k k))
;;   (defstrand orig 3 (n n) (A A) (B B) (k k))
;;   (precedes ((1 0) (0 0)) ((0 2) (1 2))))

;; (defskeleton nonaug-prune
;;   (vars (n text) (A B name) (k akey))
;;   (defstrand orig 3 (n n) (A A) (B B) (k k)))

(defskeleton nonaug-prune
  (vars (n text) (A B name) (k akey))
  (defstrand trans2 2 (n n) (A B) (k k))
  (defstrand trans2 2 (n n) (A A) (k k))
  (defstrand orig 3 (n n) (A A)(B B) (k k))
  (precedes ((2 0) (0 0)) ((2 0) (1 0))))
