(herald perrig-song)

(defprotocol perrig-song basic
  (defrole init
    (vars (na nb text) (a b name) (c chan))
    (trace
     (send na)
     (recv c (cat na nb a b))
     (send nb)))

  (defrole resp
    (vars (na nb text) (a b name) (c chan))
    (trace
     (recv na)
     (send c (cat na nb a b))
     (recv nb))))

;;; this query should bring in a matching
;;; run of resp of height 2.

(defskeleton perrig-song
  (vars (na nb text) (a b name) (c chan))
  (defstrand init 2 (na na) (c c))
  (uniq-orig na)
  (auth c))

;;; this query should bring in a matching
;;; run of init of height 3.

(defskeleton perrig-song
  (vars (na nb text) (a b name) (c chan))
  (defstrand resp 3 (nb nb) (c c))
  (uniq-orig nb)
  (conf c))

;;; these two should be realized as-is.

(defskeleton perrig-song
  (vars (na nb text) (a b name) (c chan))
  (defstrand init 2 (na na) (c c))
  (uniq-orig na)
  (conf c))

(defskeleton perrig-song
  (vars (na nb text) (a b name) (c chan))
  (defstrand resp 3 (nb nb) (c c))
  (uniq-orig nb)
  (auth c))
