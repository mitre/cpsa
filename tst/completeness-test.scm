;; In this protocol an initiator verifies the liveness
;; of a responder via the first two messages of a
;; Needham-Schroeder exchange.  The initiator then
;; sends an ok message to a probe who is waiting
;; to hear if the responder is live.

(defprotocol completeness-test basic
 (defrole init
   (vars (a b name) (n text) (s skey))
   (trace
    (send (enc a n (pubk b)))
    (recv (enc n (pubk a)))
    (send (enc "ok" s))))
 (defrole resp
   (vars (a b name) (n text))
   (trace
    (recv (enc a n (pubk b)))
    (send (enc n (pubk a)))))
 (defrole probe
   (vars (s skey))
   (trace
    (recv (enc "ok" s)))))

;; These first two skeletons should be compared to
;; each other.  They only differ in the order in which
;; the strands are listed.  CPSA should find the same
;; shapes for both of them.  However, CPSA 1.5.3
;; only finds one shape for the first one.

(defskeleton completeness-test
  (vars (b name) (n text) (s skey))
  (defstrand init 3 (b b) (n n))
  (defstrand probe 1 (s s))
  (non-orig s (privk b))
  (uniq-orig n))

(defskeleton completeness-test
  (vars (b name) (n text) (s skey))
  (defstrand probe 1 (s s))
  (defstrand init 3 (b b) (n n))
  (non-orig s (privk b))
  (uniq-orig n))

(defskeleton completeness-test
  (vars (b name) (n text) (s skey))
  (defstrand init 2 (b b) (n n))
  (defstrand probe 1 (s s))
  (non-orig s (privk b))
  (uniq-orig n))

(defskeleton completeness-test
  (vars (b name) (n text) (s skey))
  (defstrand probe 1 (s s))
  (defstrand init 2 (b b) (n n))
  (non-orig s (privk b))
  (uniq-orig n))
