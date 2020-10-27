;; Yahalom protocol

(herald yahalom
	(bound 20)
	)

(defprotocol yahalom basic

  (defrole init
    (vars (pub1 pub2 chan) (a b s name) (na nb text)
	  (kab skey) (pkg mesg))
    (trace
     (send pub1 (cat a na))
     (recv pub2 (cat (enc b kab na nb (ltk a s)) pkg))
     (send pub1 (cat pkg
		     (enc nb kab)))
     )
    (uniq-orig na)
    (inputs pub1 pub2 a b (ltk a s))
    (outputs kab)
    )

  (defrole resp
    (vars (pub1 pub2 chan) (b a s name) (na nb text) (kab skey))
    (trace
     (recv pub1 (cat a na))
     (send pub2 (cat b (enc a na nb (ltk b s))))
     (recv pub1 (cat (enc a kab (ltk b s))
		     (enc nb kab)))
     )
    (uniq-orig nb)
    (inputs pub1 pub2 b (ltk b s))
    (outputs a kab)
    )

  (defrole serv-init
    (vars (pub chan) (s a b name) (na nb text))
    (trace
     (recv pub (cat b (enc a na nb (ltk b s))))
     )
    (inputs pub b (ltk b s))
    (outputs a na nb)
    )

  (defrole serv-complete
    (vars (pub chan) (s a b name) (na nb text) (kab skey))
    (trace
     (send pub (cat (enc b kab na nb (ltk a s))
		    (enc a kab (ltk b s))))
     )
    (uniq-orig kab)
    (inputs pub a b (ltk a s) (ltk b s) na nb)
    (outputs kab)
    )

  )

(defskeleton yahalom
  (vars (a b s name))
  (defstrand init 3 (a a) (b b) (s s))
  (non-orig (ltk a s) (ltk b s))
  )

(defskeleton yahalom
  (vars (b a s name))
  (defstrand resp 3 (b b) (a a) (s s))
  (non-orig (ltk b s) (ltk a s))
  )

(defskeleton yahalom
  (vars (s b name))
  (defstrand serv-init 1 (s s) (b b))
  (non-orig (ltk b s))
  )
