;;;  Wonthull:  Demonstrates a subtle incompleteness.
;;;
;;;  The second POV skeleton given is a shape not produced
;;;   or covered in the first search.  The problem is that an
;;;   augmentation is attempted only with the most general
;;;   version of the responder strand that uses x3 as y1, not
;;;   the more specific version in which this does not lead to
;;;   x3 being originated in more than one place.)

(defprotocol wonthull basic
  (defrole init (vars (a name) (x1 x2 x3 x4 text))
    (trace
      (send (cat (enc x1 x2 (pubk a)) (enc x3 x2 (pubk a))))
	(recv (enc "okay" x3 x4 (pubk a)))
    )
    (uniq-orig x1 x2 x3)
    (non-orig (privk a))
  )
  (defrole resp (vars (a name) (y1 y2 y3 text))
     (trace
       (recv (enc y1 y2 (pubk a)) )
       (send (enc "okay" y3 y1 (pubk a)) )
     )
  )
)

(defskeleton wonthull
  (vars)
  (defstrand init 2)
)

(defskeleton wonthull
  (vars (a name) (n text) (x1 x2 x3 x4 text))
  (defstrand init 2 (a a) (x1 x1) (x2 x3) (x3 x3) (x4 x1))
  (defstrand resp 2 (a a) (y1 x1) (y2 x3) (y3 x3))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))
)
