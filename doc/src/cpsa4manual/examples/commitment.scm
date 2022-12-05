(herald commitment) 

(defprotocol commit basic 
  (defrole bidder
    (vars (a b name) (n data) (quote outcome text))
    (trace
     (send (enc "bid" (hash a b n quote) (privk "sig" a)))
     (recv (enc "receipt" (hash a b n quote) (privk "sig" b)))
     (send (cat n quote))
     (recv (enc "result" a b n quote outcome (privk "sig" b)))))

  (defrole bid-trash  
    (vars (a b name) (n data) (outcome trash text))
    (trace
     (send (enc "bid" (hash n trash) (privk "sig" a)))
     (recv (enc "receipt" (hash n trash) (privk "sig" b)))))

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

(defskeleton commit
  (vars (a b name) (n data) (quote outcome text) (sealed mesg))
  (defstrand auctioneer 2 (a a))	; up to last recv
  (non-orig (privk "sig" a)))

(defskeleton commit
  (vars (n data) (quote outcome text) (a b name))
  (defstrand auctioneer 4 (sealed (hash a b n quote)) (n n)
    (quote quote) (outcome outcome) (a a) (b b))
  (defstrand bidder 1 (n n) (quote quote) (a a) (b b))
  (uniq-gen n)
  (non-orig (privk "sig" a)))


