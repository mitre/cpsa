(herald puzzle_example)

;; Note that (ltk a b) \not= (ltk b a).  If we have a shared key with
;; this symmetry, then we need a lttle more structure in the middle
;; msg.  

(defprotocol puzzle basic 
  (defrole init
    (vars (a b name) (na payload text) (s skey))
    (trace
     (send na)
     (recv (enc na s (ltk a b)))
     (send (enc payload s))))

  (defrole resp
    (vars (a b name) (na payload text) (s skey))
    (trace
     (recv na)
     (send (enc na s (ltk a b)))
     (recv (enc payload s)))))

(defskeleton puzzle
  (vars (a b name) (na payload text) (s skey))
  (defstrand init 3 (a a) (b b) (na na) (payload payload))
  (uniq-orig na payload)
  (non-orig (ltk a b)))

(defskeleton puzzle
  (vars (a b name) (na payload text) (s skey))
  (defstrand init 3 (a a) (b b) (na na) (payload payload))
  (deflistener payload)
  (uniq-orig na payload)
  (non-orig (ltk a b)))

(defskeleton puzzle
  (vars (na payload text) (a b name) (s skey))
  (defstrand init 3 (na na) (payload payload) (a a) (b b) (s s))
  (defstrand resp 2 (na na) (a a) (b b) (s s))
  (deflistener s)
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (ltk a b))
  (uniq-orig s na payload))

(defskeleton puzzle
  (vars (na payload text) (a b name) (s skey))
  (defstrand init 3 (na na) (payload payload) (a a) (b b) (s s))
  (defstrand resp 2 (na na) (a a) (b b) (s s))
  (deflistener payload)
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
  (non-orig (ltk a b))
  (uniq-orig s na payload))

(defskeleton puzzle
  (vars (a b name) (na payload text) (s skey))
  (defstrand resp 3 (a a) (b b) (s s) (payload payload))
  (uniq-orig s)
  (non-orig (ltk a b)))

(defskeleton puzzle
  (vars (a b name) (na payload text) (s skey))
  (defstrand resp 3 (a a) (b b) (s s) (payload payload))
  (deflistener s)
  (uniq-orig s)
  (non-orig (ltk a b)))

(defskeleton puzzle
  (vars (payload na text) (a b name) (s skey))
  (defstrand resp 3 (na na) (payload payload) (a a) (b b) (s s))
  (defstrand init 3 (na na) (payload payload) (a a) (b b) (s s))
  (deflistener payload)
  (precedes ((0 1) (1 1)) ((1 2) (0 2)))
  (non-orig (ltk a b))
  (uniq-orig s payload))
