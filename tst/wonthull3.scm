;;;  Wonthull 3:  Demonstrates a subtle incompleteness.
;;;
;;;  Demonstrates that the deorigination incompleteness
;;; is not inherently linked to point and position of
;;; origination.

(defprotocol wonthull3 basic
  (defrole init (vars (a name) (x1 x2 x3 x4 text))
    (trace
      (send (enc x3 (pubk a)))
      (send (cat (enc x1 x2 (pubk a)) (enc x3 x2 (pubk a))))
	(recv (enc "okay" x3 x4 (pubk a)))
    )
    (uniq-orig x3)
    (non-orig (privk a))
  )
  (defrole resp (vars (a name) (y1 y2 y3 text))
     (trace
       (recv (enc y1 y2 (pubk a)) )
       (send (enc "okay" y3 y1 (pubk a)) )
     )
  )
)

(defskeleton wonthull3
  (vars (a name) (n text) (x1 x2 x3 x4 text))
  (defstrand init 3)
)

(defskeleton wonthull3
  (vars (a name) (n text) (x1 x2 x3 x4 text))
  (defstrand init 3 (x2 x3) (x4 x1))
  (defstrand resp 2 (y1 x1) (y2 x3) (y3 x3))
  (precedes ((0 1) (1 0)) ((1 1) (0 2)))
)
