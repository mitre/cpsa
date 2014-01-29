(comment "CPSA 2.3.1")
(comment "All input read from kelly1.scm")

(defprotocol kelly1 basic
  (defrole client
    (vars (C A S name) (Ns request Check policy response text))
    (trace (send (cat C S request))
      (recv (cat S C (enc response Ns (privk S))))
      (send (cat C A Check (pubk S)))
      (recv (cat A C (enc policy (pubk S) Ns (privk A))))))
  (defrole appraiser
    (vars (C A S name) (N Ns hello Quote measurements Check policy text)
      (AIK name))
    (trace (recv (cat S A hello)) (send (cat A S N))
      (recv
        (cat S A (enc Quote measurements N Ns (pubk S) (privk AIK))
          (pubk S))) (recv (cat C A Check (pubk S)))
      (send (cat A C (enc policy (pubk S) Ns (privk A)))))
    (non-orig (privk A) (privk AIK))
    (uniq-orig N))
  (defrole server
    (vars (C A S name)
      (N Ns hello Quote measurements request response text) (AIK name))
    (trace (send (cat S A hello)) (recv (cat A S N))
      (send
        (cat S A (enc Quote measurements N Ns (pubk S) (privk AIK))
          (pubk S))) (recv (cat C S request))
      (send (cat S C (enc response Ns (privk S)))))
    (non-orig (privk S) (privk AIK))
    (uniq-orig Ns)))

(defskeleton kelly1
  (vars (Ns request Check policy response text) (A C S name))
  (defstrand client 4 (Ns Ns) (request request) (Check Check)
    (policy policy) (response response) (C C) (A A) (S S))
  (non-orig (privk A))
  (traces
    ((send (cat C S request))
      (recv (cat S C (enc response Ns (privk S))))
      (send (cat C A Check (pubk S)))
      (recv (cat A C (enc policy (pubk S) Ns (privk A))))))
  (label 0)
  (unrealized (0 3))
  (origs)
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton kelly1
  (vars
    (Ns request Check policy response N hello Quote measurements Check-0
      text) (A C S C-0 AIK name))
  (defstrand client 4 (Ns Ns) (request request) (Check Check)
    (policy policy) (response response) (C C) (A A) (S S))
  (defstrand appraiser 5 (N N) (Ns Ns) (hello hello) (Quote Quote)
    (measurements measurements) (Check Check-0) (policy policy) (C C-0)
    (A A) (S S) (AIK AIK))
  (precedes ((1 4) (0 3)))
  (non-orig (privk A) (privk AIK))
  (uniq-orig N)
  (operation encryption-test (added-strand appraiser 5)
    (enc policy (pubk S) Ns (privk A)) (0 3))
  (traces
    ((send (cat C S request))
      (recv (cat S C (enc response Ns (privk S))))
      (send (cat C A Check (pubk S)))
      (recv (cat A C (enc policy (pubk S) Ns (privk A)))))
    ((recv (cat S A hello)) (send (cat A S N))
      (recv
        (cat S A (enc Quote measurements N Ns (pubk S) (privk AIK))
          (pubk S))) (recv (cat C-0 A Check-0 (pubk S)))
      (send (cat A C-0 (enc policy (pubk S) Ns (privk A))))))
  (label 1)
  (parent 0)
  (unrealized (1 2))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton kelly1
  (vars
    (Ns request Check policy response N hello Quote measurements Check-0
      hello-0 text) (A C S C-0 AIK A-0 name))
  (defstrand client 4 (Ns Ns) (request request) (Check Check)
    (policy policy) (response response) (C C) (A A) (S S))
  (defstrand appraiser 5 (N N) (Ns Ns) (hello hello) (Quote Quote)
    (measurements measurements) (Check Check-0) (policy policy) (C C-0)
    (A A) (S S) (AIK AIK))
  (defstrand server 3 (N N) (Ns Ns) (hello hello-0) (Quote Quote)
    (measurements measurements) (A A-0) (S S) (AIK AIK))
  (precedes ((1 1) (2 1)) ((1 4) (0 3)) ((2 2) (0 1)) ((2 2) (1 2)))
  (non-orig (privk A) (privk S) (privk AIK))
  (uniq-orig Ns N)
  (operation encryption-test (added-strand server 3)
    (enc Quote measurements N Ns (pubk S) (privk AIK)) (1 2))
  (traces
    ((send (cat C S request))
      (recv (cat S C (enc response Ns (privk S))))
      (send (cat C A Check (pubk S)))
      (recv (cat A C (enc policy (pubk S) Ns (privk A)))))
    ((recv (cat S A hello)) (send (cat A S N))
      (recv
        (cat S A (enc Quote measurements N Ns (pubk S) (privk AIK))
          (pubk S))) (recv (cat C-0 A Check-0 (pubk S)))
      (send (cat A C-0 (enc policy (pubk S) Ns (privk A)))))
    ((send (cat S A-0 hello-0)) (recv (cat A-0 S N))
      (send
        (cat S A-0 (enc Quote measurements N Ns (pubk S) (privk AIK))
          (pubk S)))))
  (label 2)
  (parent 1)
  (unrealized (0 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton kelly1
  (vars
    (Ns request Check policy response hello Check-0 N hello-0 Quote
      measurements request-0 text) (A C S C-0 C-1 A-0 AIK name))
  (defstrand client 4 (Ns Ns) (request request) (Check Check)
    (policy policy) (response response) (C C) (A A) (S S))
  (defstrand appraiser 5 (N N) (Ns Ns) (hello hello) (Quote Quote)
    (measurements measurements) (Check Check-0) (policy policy) (C C-0)
    (A A) (S S) (AIK AIK))
  (defstrand server 5 (N N) (Ns Ns) (hello hello-0) (Quote Quote)
    (measurements measurements) (request request-0) (response response)
    (C C-1) (A A-0) (S S) (AIK AIK))
  (precedes ((1 1) (2 1)) ((1 4) (0 3)) ((2 2) (1 2)) ((2 4) (0 1)))
  (non-orig (privk A) (privk S) (privk AIK))
  (uniq-orig Ns N)
  (operation encryption-test (displaced 2 3 server 5)
    (enc response Ns (privk S)) (0 1))
  (traces
    ((send (cat C S request))
      (recv (cat S C (enc response Ns (privk S))))
      (send (cat C A Check (pubk S)))
      (recv (cat A C (enc policy (pubk S) Ns (privk A)))))
    ((recv (cat S A hello)) (send (cat A S N))
      (recv
        (cat S A (enc Quote measurements N Ns (pubk S) (privk AIK))
          (pubk S))) (recv (cat C-0 A Check-0 (pubk S)))
      (send (cat A C-0 (enc policy (pubk S) Ns (privk A)))))
    ((send (cat S A-0 hello-0)) (recv (cat A-0 S N))
      (send
        (cat S A-0 (enc Quote measurements N Ns (pubk S) (privk AIK))
          (pubk S))) (recv (cat C-1 S request-0))
      (send (cat S C-1 (enc response Ns (privk S))))))
  (label 3)
  (parent 2)
  (unrealized)
  (shape)
  (maps
    ((0)
      ((A A) (C C) (S S) (Ns Ns) (request request) (Check Check)
        (policy policy) (response response))))
  (origs (Ns (2 2)) (N (1 1))))

(comment "Nothing left to do")
