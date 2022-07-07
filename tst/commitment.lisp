(herald commitment)

(defprotocol commit
  (defrole bidder
    (vars (a b name) (n data) (quote outcome text))
    (trace
     (send (enc "bid" (hash a b n quote) (privk "sig" a)))
     (recv (enc "receipt" (hash a b n quote) (privk "sig" b)))
     (send (cat n quote))
     (recv (enc "result" a b n quote outcome (privk "sig" b)))))

  (defrole auctioneer 
    (vars (a b name) (n data) (quote outcome text) (sealed mesg))
    (trace
     (recv (enc "bid" sealed (privk "sig" a)))
     (send (enc "receipt" sealed (privk "sig" b)))
     (recv (cat n quote))
     (cheq sealed (hash a b n quote))
     (send (enc "result" a b n quote outcome (privk "sig" b))))))

(defskeleton commit
  (vars (a b name) (n data) (quote outcome text) (sealed mesg))
  (defstrand auctioneer 4 (a a))	; full height:  cheq doesn't
					; count separately
  (non-orig (privk "sig" a)))



