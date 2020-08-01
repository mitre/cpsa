(herald "SWAG"
	(bound 28)
	)

(defmacro (la payload)
  (enc payload auth-akey))

(defmacro (lc payload)
  (enc payload conf-akey))

(defmacro (lac payload)
  (enc payload k-local))

(defmacro (lra)
  (non-orig auth-akey))

(defmacro (lrc)
  (non-orig (invk conf-akey)))

(defmacro (lrac)
  (non-orig k-local))

(defmacro (local payload)
  (lac payload))

(defmacro (local-restriction)
  (lrac))

(defmacro (watch-key-init w k)
  (cat "watch key 0" w k))

(defmacro (watch-key w k)
  (cat "watch key" w k))

(defmacro (bio-cert w p n bio provo)
  (enc n (hash w p n bio) (privk "sign" provo)))

(defmacro (watch-bio w p n bio provo)
  (cat "watch bio" w p (bio-cert w p n bio provo)))

(defmacro (bio-msg w p nprovo bio provo)
  (cat "bio" w nprovo p (bio-cert w p nprovo bio provo)))

(defmacro (db-bio w p nprovo bio k nprovo)
  (cat "db-rec" w p bio k nprovo))

(defmacro (entry-pkg w p n-w nprovo bio provo)
    (cat "pkg" w p n-w (bio-cert w p nprovo bio provo)))

(defmacro (cred-pkg w p n-w n-ts ts k)
    (enc "cred pkg" w p ts n-ts (hash "chal k" k n-w))
  )

;; this operation is robust against an adversary
;; who can get n-w and (hash "chal k" k n-w)
(defmacro (entry-confirm n-w n-ts k)
  (enc "confirm" n-w (hash "chal k" k n-ts)))

(defmacro (watch-stored-cred w p ts h k)
    (enc "watch cred" w p ts h k)
  )

(defmacro (db-daily w p h)
    (cat "db-daily" w p h)
    )

(defmacro (db-daily-ws w p ws h)
    (cat "db-daily-ws" w p ws (hash "seed" ws h)))

(defmacro (db-daily-rec w p ws h)		; subsequent recipient can't infer nonces 
    (cat "db-daily-ws" w p ws h))

(defmacro (login-req w p ws nl-w h)
    (cat nl-w (enc "login-req" w p ws (hash nl-w h))))

(defmacro (login-challenge w p ws nl-w s n-ws h)
    (enc "login-chal" w p ws s n-ws (hash nl-w h)))

(defmacro (login-conf n-ws s)
    (enc n-ws s))

(defmacro (host-beacon-data w p ws nl-w n-ws s)
    (cat "host-beacon-data" w p ws nl-w n-ws s))

(defmacro (w-beacon-data w p ws nl-w n-ws s)
    (cat "w-beacon-data" w p ws nl-w n-ws s))

(defprotocol swag basic

  ;; provision-roles

  (defrole w-create
       (vars (w name)			; the watch name, ie GUID 
	     (auth-akey
	      conf-akey akey)	  ; "keys" representing local delivery
					; with integrity or confidentiality resp.  
	     (k		   ; watchs new, long term intrinsic secret 
	      k-local	   ; "key" representing local secure delivery 
	      skey)
	     (old mesg)
	     (wkey locn)) 
       (trace
	(send (local (cat w k)))
	(load wkey old)
	(stor wkey (watch-key-init w k))
	)
       (uniq-orig w k)
       (critical-sections (1 2))
       (local-restriction))
   
     (defrole w-bio
       (vars (w p provo name)	 ; the watch, the person, the provider
	     (auth-akey
	      conf-akey akey)	  ; "keys" representing local delivery
					; with integrity or confidentiality resp.  
	     (k-local k skey)   
	     (nprovo now fpt text) (bio data)
	     (old mesg)
	     (wkey wbio locn)
	     )
       (trace
	(recv (local (cat p now fpt)))
	(load wkey (watch-key-init w k))
	(stor wkey (watch-key w (enc k fpt)))
	(recv (local (bio-msg w p nprovo bio provo)))
	(send (local nprovo))
	(load wbio old)
	(stor wbio (watch-bio w p nprovo bio provo))
	)
       (critical-sections (1 2) (5 6))
       (gen-st (watch-key-init w k))
       (local-restriction))

     (defrole impress-fpt
       (vars (p name)
	     (k-local skey)
	     (auth-akey
	      conf-akey akey)
	     (fpt now text))		; fpt is the fingerprint
       (trace
	(send (local (cat p now fpt)))
	)
       (local-restriction)
       )	     

     (defrole provide-bio
       (vars (w p provo name)
	     (k k-local skey)
	     (auth-akey
	      conf-akey akey)
	     (nprovo text)
	     (bio data)
	     (old mesg)
	     (dbio locn)
	     )
       (trace
	(recv (local (cat w k)))
	(send (local (bio-msg w p nprovo bio provo)))  
	(recv (local nprovo))
	(load dbio old)
	(stor dbio (db-bio w p nprovo bio k nprovo))
	)
       (uniq-orig nprovo)
       (critical-sections (3 4))
       (local-restriction)
       )

     ;; turnstile-roles

     (defrole w-turnstile
       (vars (w p ts provo name) ; watch, person, turnstile provisioner
	     (k k-local skey)
	     (auth-akey
	      conf-akey akey)
	     (n-w n-ts now fpt 		; fpt is the fingerprint 
		  nprovo text)
	     (bio data)
	     (wkey wbio wcred locn)
	     (old mesg)
	     )
       (trace
	(recv (local (cat p now fpt)))	   ; fingerprint impression 

	(load wkey (watch-key w (enc k fpt)))
	(load wbio (watch-bio w p nprovo bio provo)) ; retrieve state values
	
	(send (local
	       (entry-pkg w p n-w nprovo bio provo)))
	(recv (local
	       (cred-pkg w p n-w n-ts ts k)))
	(send (entry-confirm n-w n-ts k))
	
	(load wcred old)
	(stor wcred (watch-stored-cred w p ts (hash n-w n-ts) k))
	)
       (uniq-orig n-w)
       (local-restriction)
       (gen-st (watch-key w (enc k fpt))(watch-bio w p nprovo bio provo))
       (critical-sections (6 7))
       )

     (defrole turnstile
       (vars (w p ts provo name) ; watch, person, turnstile, provisioner
	     (k k-local skey)
	     (auth-akey
	      conf-akey akey)
	     (n-w n-ts nprovo
		  text)
	     (bio data)
	     (dbio dcred locn)
	     (old mesg)
	     )
       (trace
	(load dbio (db-bio w p nprovo bio k nprovo))
	
	(recv (local
	       (entry-pkg w p n-w nprovo bio provo)))
	(send (local
	       (cred-pkg w p n-w n-ts ts k)))
	(recv (entry-confirm n-w n-ts k))

	(load dcred old)
	(stor dcred (db-daily w p (hash n-w n-ts)))
	)
       (uniq-orig n-ts)
       (local-restriction)
       (gen-st (db-bio w p nprovo bio k nprovo))
       (critical-sections (4 5))
       )

     ;; workstation-roles 

     (defrole specialize-to-host
       (vars (w p ws name)
     	     (n-w n-ts text) (h old mesg) (dcred hcred locn))
       (trace
     	(load dcred (db-daily w p h))
     	(load hcred old)
     	(stor hcred (db-daily-ws w p ws h))
     	)
       (gen-st (db-daily w p h))
       (critical-sections (1 2))
       )
     
     (defrole host-login 
       (vars (w p ts ws name)	; watch, person turnstile, workstation
     	     (s k k-local skey)
     	     (nl-w n-ws text) (bio data) (h old mesg) (hcred hsess locn))
       (trace
     	(load hcred (db-daily-rec w p ws h))

     	(recv (login-req w p ws nl-w h))
     	(send (login-challenge w p ws nl-w s n-ws h))
     	(recv (login-conf n-ws s))

     	(load hsess old)
     	(stor hsess (host-beacon-data w p ws nl-w n-ws s))
     	)
       (gen-st (db-daily-rec w p ws h))
       (critical-sections (4 5))
       )

     (defrole w-login
       (vars (w p ts ws name) (h old mesg) ; watch, person turnstile, workstation
       	     (s k k-local skey) (fpt now nprovo n-w n-ts nl-w n-ws text)
       	     (wkey wcred wsess locn)
       	     )
       (trace
       	(recv (local (cat p now fpt)))	; fingerprint impression 
  
       	(load wkey (watch-key w (enc k fpt)))
       	(load wcred (watch-stored-cred w p ts h k))
  
       	(send (login-req w p ws nl-w (hash "seed" ws h)))
       	(recv (login-challenge w p ws nl-w s n-ws (hash "seed" ws h)))
       	(send (login-conf n-ws s))
  
       	(load wsess old)
       	(stor wsess (w-beacon-data w p ws nl-w n-ws s))
       	)
       (local-restriction)
       (gen-st
       	(watch-key w (enc k fpt))
       	(watch-stored-cred w p ts h k)
       	)
       (critical-sections (6 7))
       )

     (defrole w-beacon
       (vars (w p ts ws name)	; watch, person turnstile, workstation
     	     (s k k-local skey)
     	     (nl-w n-ws count text)
     	     (wsess locn)
     	     )
       (trace
     	(load wsess (w-beacon-data w p ws nl-w n-ws s))
     	(send (enc "beacon" w p ws (hash nl-w n-ws) count s))
     	)
       (gen-st (w-beacon-data w p ws nl-w n-ws s))
       )

     (defrole host-recv-beacon
       (vars (w p ts ws name)	; watch, person turnstile, workstation
     	     (s k k-local skey)
     	     (nl-w n-ws count text)
     	     (hsess locn)
     	     )
       (trace
     	(load hsess (host-beacon-data w p ws nl-w n-ws s))
     	(recv (enc "beacon" w p ws (hash nl-w n-ws) count s))
     	)
       (gen-st (host-beacon-data w p ws nl-w n-ws s))
       )

     (defrule fpt-deliver-once
       (forall
     	((z1 z2 strd) (now text))
     	(implies (and (p "w-bio" "now" z1 now)
     		      (p "w-turnstile" "now" z2 now))
     		 (= z1 z2))))
     
     ;; (defrule fpt-deliver-once-again
     ;;   (forall
     ;;    ((z1 z2 strd) (now text))
     ;;    (implies (and (p "w-bio" "now" z1 now)
     ;; 		   (p "w-login" "now" z2 now)) 
     ;; 	      (= z1 z2))))
     
     ;; (defrule fpt-deliver-once-yet-again
     ;;   (forall
     ;;    ((z1 z2 strd) (now text))
     ;;    (implies (and (p "w-turnstile" "now" z1 now)
     ;; 		   (p "w-login" "now" z2 now))
     ;; 	      (= z1 z2))))
     
     )

(defskeleton swag
  (vars )
  (defstrand w-bio 7)
  (facts (no-state-split))
  )

(defskeleton swag
  (vars )
  (defstrand provide-bio 5)
  (facts (no-state-split))
  )

(defskeleton swag
  (vars )
  (defstrand w-turnstile 8)
  (facts (no-state-split))
  )

(defskeleton swag
  (vars )
  (defstrand turnstile 6)
  (facts (no-state-split))
  )

;; (defskeleton swag
;;   (vars )
;;   (defstrand host-login 6)
;;   (facts (no-state-split))
;;   )

;; (defskeleton swag
;;   (vars )
;;   (defstrand w-login 8)
;;   (facts (no-state-split))
;;   )

