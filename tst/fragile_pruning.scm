;;; Illustrates how delicate pruning must be:
;;; to find a shape we must allow 3 almost
;;; identical instances of "adder", without
;;; pruning them even though they are renamings of
;;; each other.
;;; This goes to show that pruning is not justified
;;; in some cases even when the two strands are
;;; isomorphic.  What is lost by pruning here is merely
;;; the ability for a fresh variable of sort text to
;;; unify with a different already-existing variable of
;;; sort text without unifying the two existing ones.

(defprotocol fragile_pruning basic
  (defrole init (vars (k akey) (n n1 n2 n3 text))
    (trace
	(send (enc n k))
      (recv (enc n n1 k))
      (recv (enc n n2 k))
      (recv (enc n n3 k))
      (send (enc n n1 n2 n3 k))
      (recv (enc n n1 n2 n3 n k))
    )
    (uniq-orig n)
    (non-orig (invk k))
  )
  (defrole adder (vars (k akey) (n new text))
    (trace
      (recv (enc n k))
      (send (enc n new k))
    )
    (uniq-orig new)
  )
  (defrole final (vars (k akey) (n n1 n2 n3 text))
    (trace
       (recv (enc n n1 n2 n3 k))
       (send (enc n n1 n2 n3 n k))
    )
  )
)

(defskeleton fragile_pruning
  (vars (k akey) (n n1 n2 n3  text))
  (defstrand init 6 (k k) (n n) (n1 n1) (n2 n2) (n3 n3))
  (uniq-orig n1 n2 n3)
)
