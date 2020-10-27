;; Simplified Otway-Rees protocol
;; As described in "Prudent Engineering Practices"
;; by Abadi and Needham

(herald otway-rees)

(defprotocol otway-rees basic

  (defrole init
    (vars (pub chan) (a b s name) (na text) (kab skey))
    (trace
     (send pub (cat a b na))
     (recv pub (enc na a b kab (ltk a s)))
     )
    (uniq-orig na)
    (inputs pub a b (ltk a s))
    (outputs kab)
    )

  (defrole resp
    (vars (pub1 pub2 chan) (b a s name) (na nb text) (kab skey)
	  (pkg mesg))
    (trace
     (recv pub1 (cat a b na))
     (send pub2 (cat a b na nb))
     (recv pub2 (cat pkg (enc nb a b kab (ltk b s))))
     (send pub1 pkg)
     )
    (uniq-orig nb)
    (inputs pub1 pub2 b (ltk b s))
    (outputs a kab)
    )

  (defrole serv
    (vars (pub chan) (s a b name) (na nb text) (kab skey))
    (trace
     (recv pub (cat a b na nb))
     (send pub (cat (enc na a b kab (ltk a s))
		    (enc nb a b kab (ltk b s))))
     )
    (uniq-orig kab)
    (inputs pub a b (ltk a s) (ltk b s))
    (outputs kab)
    )

  )

(defskeleton otway-rees
  (vars (a s name))
  (defstrand init 2 (a a) (s s))
  (non-orig (ltk a s))
  )

(defskeleton otway-rees
  (vars (b s name))
  (defstrand resp 4 (b b) (s s))
  (non-orig (ltk b s))
  )

(defskeleton otway-rees
  (vars (s a b name))
  (defstrand serv 2 (s s) (a a) (b b))
  (non-orig (ltk a s) (ltk b s))
  )
