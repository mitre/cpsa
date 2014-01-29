;;;  Wonthull 2:  Demonstrates a subtle incompleteness.
;;;
;;;  From Wonthull 1, the difference here is that
;;; Wonthull 2 should be able to do augmentation with
;;; non-trivial deorigination immediately after the POV.
;;;  Interestingly, Wonthull 2 (without deorigination)
;;; actually finds the missing shape, but via variable
;;; separation.

(defprotocol wonthull2 basic
  (defrole init (vars (a name) (x1 x2 x3 x4 text))
    (trace
      (send (cat (enc x1 x3 (pubk a)) (enc x3 x2 (pubk a))))
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

(defskeleton wonthull2
  (vars (a name) (n text) (x1 x2 x3 x4 text))
  (defstrand init 2)
)

(defskeleton wonthull2
  (vars (a name) (n text) (x1 x2 x3 x4 text))
  (defstrand init 2 (x2 x3) (x4 x1))
  (defstrand resp 2 (y1 x1) (y2 x3) (y3 x3))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
)
