;;; Attempt to make a protocol that reduces several strands by hulling at once

(defprotocol crushing basic
  (defrole init (vars (k akey) (n n1 n2 n3 text))
    (trace
	(send (enc n k))
      (recv (enc n n1 (invk k)))
      (recv (enc n n2 (invk k)))
      (recv (enc n n3 (invk k)))
      (send (enc n n1 n2 n3 (invk k)))
      (recv (enc n n1 n2 n3 n (invk k)))
    )
    (uniq-orig n)
    (non-orig (invk k))
  )
  (defrole adder (vars (k akey) (n new text))
    (trace
      (recv (enc n k))
      (send (enc n new (invk k)))
    )
    (uniq-orig new)
  )
  (defrole twister (vars (k akey) (n n1 n2 n3 text))
    (trace
       (recv (enc n n1 n2 n3 (invk k)))
       (send (enc n n2 n3 n1 n (invk k)))
    )
  )
)

(defskeleton crushing
  (vars (k akey) (n n1 n2 n3  text))
  (defstrand init 6 (k k) (n n) (n1 n1) (n2 n2) (n3 n3))
  (uniq-orig n1 n2 n3)
)
