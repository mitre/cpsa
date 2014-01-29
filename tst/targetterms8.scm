;;; Target terms experiment
;
;  This example demonstrates the need for the solved filter condition "2a",
; which we had suspected was necessary for months but until now we were not
; sure.
;
;
;  The initiator sends out an encryption {|n1 {|a n2|} |}, with both levels
; of encryption being under an asymmetric key whose inverse is assumed to be
; non-originating.  n1 is freshly chosen.  The initiator expects to receive
; {|a n1|}.
;
;  The responder takes {|n1 {|m|} |} and outputs {|m|}.
;
;  The initial POV (which is just the init 2 role) is dead because we don't
; have condition 2a in the solved predicate.  If we did, we could try an
; augmentation or displacement for a length-1 init strand with n1 being
; used as the value for n2.  Hulling would require that this unify with the
; existing init strand, and the result would be an init strand in which n1
; and n2 are unified.  (Our second POV is this skeleton).
;
;  However, the escape set after this map is no bigger than it was; it consists
; of only {|n1 {|a n1|} |}, which is in the image of the old escape set, so
; we don't meet condition 2.  We do meet condition 2a, since the target term
; (a n1) is not an image of any old target term (the old target terms were only
; n1 and (n1 {|a n2|}).
;
;  Note that the first POV is dead (in CPSA 2.2.2) but the second POV is not,
; and leads to a shape.

(defprotocol targetterms8 basic
  (defrole init (vars (a name) (n1 n2 text) (k akey))
    (trace
	(send (enc n1 (enc a n2 k) k))
      (recv (enc a n1 k))
    )
    (uniq-orig n1)
    (non-orig (invk k))
)
  (defrole resp (vars (n1 text) (m mesg) (k akey))
    (trace
     (recv (enc n1 (enc m k) k))
     (send (enc m k))
    ))
)

(comment First POV)
(defskeleton targetterms8
  (vars (a name) (n1 n2 text) (k akey))
  (defstrand init 2 (a a) (n1 n1) (n2 n2) (k k))
)

(comment Second POV)
(defskeleton targetterms8
  (vars (a name) (n1 text) (k akey))
  (defstrand init 2 (a a) (n1 n1) (n2 n1) (k k))
)

(comment "This is the shape.  We don't need it because we find it from the second POV.")
(comment (defskeleton targetterms8
  (vars (a name) (n1 text) (k akey) )
  (defstrand init 2 (a a) (n1 n1) (n2 n1) (k k))
  (defstrand resp 2 (n1 n1) (k k) (m (cat a n1)))
  (precedes ((0 0) (1 0)) ((1 1) (0 1)))))
