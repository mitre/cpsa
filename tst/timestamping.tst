(herald timestamping-service)

(comment "CPSA 4.4.3")
(comment "All input read from tst/timestamping.scm")

(defprotocol timestamping-service basic
  (defrole client
    (vars (alice alice_1 trent name) (n data) (h h_1 text) (t_1 l mesg))
    (trace (send (cat h alice))
      (recv (enc n alice h alice_1 h_1 t_1 l (privk trent)))))
  (defrole server
    (vars (alice alice_1 trent name) (n data) (h h_1 text)
      (t_1 l_1 mesg))
    (trace
      (recv
        (cat (enc (enc alice_1 h_1 t_1 l_1 (privk trent)) (pubk trent))
          h alice))
      (send
        (cat
          (enc n alice h alice_1 h_1 t_1 (hash alice_1 h_1 t_1 l_1)
            (privk trent))
          (enc
            (enc
              (hash alice h
                (enc n alice h alice_1 h_1 t_1
                  (hash alice_1 h_1 t_1 l_1) (privk trent))
                (hash alice_1 h_1 t_1 l_1)) (privk trent))
            (pubk trent)))))
    (uniq-orig n))
  (defrole origin
    (vars (alice alice_1 trent name) (n data) (h h_1 t_1 l_1 text))
    (trace (recv (enc (enc n (privk trent)) (pubk trent)))
      (send
        (enc
          (enc alice h
            (enc n alice h alice_1 h_1 t_1 (hash alice_1 h_1 t_1 l_1)
              (privk trent)) (hash alice_1 h_1 t_1 l_1) (privk trent))
          (pubk trent)))))
  (defrole big-bang
    (vars (n data) (trent name))
    (trace (send (enc (enc n (privk trent)) (pubk trent))))
    (uniq-orig n))
  (defgenrule neqRl_indx
    (forall ((x indx)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_strd
    (forall ((x strd)) (implies (fact neq x x) (false))))
  (defgenrule neqRl_mesg
    (forall ((x mesg)) (implies (fact neq x x) (false)))))

(defskeleton timestamping-service
  (vars (t_1 l mesg) (n data) (h h_1 text) (trent alice alice_1 name))
  (defstrand client 2 (t_1 t_1) (l l) (n n) (h h) (h_1 h_1)
    (alice alice) (alice_1 alice_1) (trent trent))
  (non-orig (privk trent))
  (traces
    ((send (cat h alice))
      (recv (enc n alice h alice_1 h_1 t_1 l (privk trent)))))
  (label 0)
  (unrealized (0 1))
  (origs)
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton timestamping-service
  (vars (t_1 l_1 mesg) (n data) (h h_1 text) (trent alice alice_1 name))
  (defstrand client 2 (t_1 t_1) (l (hash alice_1 h_1 t_1 l_1)) (n n)
    (h h) (h_1 h_1) (alice alice) (alice_1 alice_1) (trent trent))
  (defstrand server 2 (t_1 t_1) (l_1 l_1) (n n) (h h) (h_1 h_1)
    (alice alice) (alice_1 alice_1) (trent trent))
  (precedes ((1 1) (0 1)))
  (non-orig (privk trent))
  (uniq-orig n)
  (operation encryption-test (added-strand server 2)
    (enc n alice h alice_1 h_1 t_1 (hash alice_1 h_1 t_1 l_1)
      (privk trent)) (0 1))
  (strand-map 0)
  (traces
    ((send (cat h alice))
      (recv
        (enc n alice h alice_1 h_1 t_1 (hash alice_1 h_1 t_1 l_1)
          (privk trent))))
    ((recv
       (cat (enc (enc alice_1 h_1 t_1 l_1 (privk trent)) (pubk trent)) h
         alice))
      (send
        (cat
          (enc n alice h alice_1 h_1 t_1 (hash alice_1 h_1 t_1 l_1)
            (privk trent))
          (enc
            (enc
              (hash alice h
                (enc n alice h alice_1 h_1 t_1
                  (hash alice_1 h_1 t_1 l_1) (privk trent))
                (hash alice_1 h_1 t_1 l_1)) (privk trent))
            (pubk trent))))))
  (label 1)
  (parent 0)
  (unrealized (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton timestamping-service
  (vars (n data) (h h_1 t_1 l_1 text) (trent alice alice_1 name))
  (defstrand client 2 (t_1 t_1) (l (hash alice_1 h_1 t_1 l_1)) (n n)
    (h h) (h_1 h_1) (alice alice) (alice_1 alice_1) (trent trent))
  (defstrand origin 2 (n n) (h h) (h_1 h_1) (t_1 t_1) (l_1 l_1)
    (alice alice) (alice_1 alice_1) (trent trent))
  (precedes ((1 1) (0 1)))
  (non-orig (privk trent))
  (operation encryption-test (added-strand origin 2)
    (enc n alice h alice_1 h_1 t_1 (hash alice_1 h_1 t_1 l_1)
      (privk trent)) (0 1))
  (strand-map 0)
  (traces
    ((send (cat h alice))
      (recv
        (enc n alice h alice_1 h_1 t_1 (hash alice_1 h_1 t_1 l_1)
          (privk trent))))
    ((recv (enc (enc n (privk trent)) (pubk trent)))
      (send
        (enc
          (enc alice h
            (enc n alice h alice_1 h_1 t_1 (hash alice_1 h_1 t_1 l_1)
              (privk trent)) (hash alice_1 h_1 t_1 l_1) (privk trent))
          (pubk trent)))))
  (label 2)
  (parent 0)
  (unrealized (0 1) (1 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton timestamping-service
  (vars (n n-0 data) (h h_1 h_1-0 t_1 l_1 text)
    (trent alice alice_1 alice_1-0 name))
  (defstrand client 2
    (t_1
      (enc n-0 alice_1 h_1 alice_1-0 h_1-0 t_1
        (hash alice_1-0 h_1-0 t_1 l_1) (privk trent)))
    (l
      (hash alice_1 h_1
        (enc n-0 alice_1 h_1 alice_1-0 h_1-0 t_1
          (hash alice_1-0 h_1-0 t_1 l_1) (privk trent))
        (hash alice_1-0 h_1-0 t_1 l_1))) (n n) (h h) (h_1 h_1)
    (alice alice) (alice_1 alice_1) (trent trent))
  (defstrand server 2
    (t_1
      (enc n-0 alice_1 h_1 alice_1-0 h_1-0 t_1
        (hash alice_1-0 h_1-0 t_1 l_1) (privk trent)))
    (l_1 (hash alice_1-0 h_1-0 t_1 l_1)) (n n) (h h) (h_1 h_1)
    (alice alice) (alice_1 alice_1) (trent trent))
  (defstrand origin 2 (n n-0) (h h_1) (h_1 h_1-0) (t_1 t_1) (l_1 l_1)
    (alice alice_1) (alice_1 alice_1-0) (trent trent))
  (precedes ((1 1) (0 1)) ((2 1) (1 0)))
  (non-orig (privk trent))
  (uniq-orig n)
  (operation encryption-test (added-strand origin 2)
    (enc alice_1 h_1
      (enc n-0 alice_1 h_1 alice_1-0 h_1-0 t_1
        (hash alice_1-0 h_1-0 t_1 l_1) (privk trent))
      (hash alice_1-0 h_1-0 t_1 l_1) (privk trent)) (1 0))
  (strand-map 0 1)
  (traces
    ((send (cat h alice))
      (recv
        (enc n alice h alice_1 h_1
          (enc n-0 alice_1 h_1 alice_1-0 h_1-0 t_1
            (hash alice_1-0 h_1-0 t_1 l_1) (privk trent))
          (hash alice_1 h_1
            (enc n-0 alice_1 h_1 alice_1-0 h_1-0 t_1
              (hash alice_1-0 h_1-0 t_1 l_1) (privk trent))
            (hash alice_1-0 h_1-0 t_1 l_1)) (privk trent))))
    ((recv
       (cat
         (enc
           (enc alice_1 h_1
             (enc n-0 alice_1 h_1 alice_1-0 h_1-0 t_1
               (hash alice_1-0 h_1-0 t_1 l_1) (privk trent))
             (hash alice_1-0 h_1-0 t_1 l_1) (privk trent)) (pubk trent))
         h alice))
      (send
        (cat
          (enc n alice h alice_1 h_1
            (enc n-0 alice_1 h_1 alice_1-0 h_1-0 t_1
              (hash alice_1-0 h_1-0 t_1 l_1) (privk trent))
            (hash alice_1 h_1
              (enc n-0 alice_1 h_1 alice_1-0 h_1-0 t_1
                (hash alice_1-0 h_1-0 t_1 l_1) (privk trent))
              (hash alice_1-0 h_1-0 t_1 l_1)) (privk trent))
          (enc
            (enc
              (hash alice h
                (enc n alice h alice_1 h_1
                  (enc n-0 alice_1 h_1 alice_1-0 h_1-0 t_1
                    (hash alice_1-0 h_1-0 t_1 l_1) (privk trent))
                  (hash alice_1 h_1
                    (enc n-0 alice_1 h_1 alice_1-0 h_1-0 t_1
                      (hash alice_1-0 h_1-0 t_1 l_1) (privk trent))
                    (hash alice_1-0 h_1-0 t_1 l_1)) (privk trent))
                (hash alice_1 h_1
                  (enc n-0 alice_1 h_1 alice_1-0 h_1-0 t_1
                    (hash alice_1-0 h_1-0 t_1 l_1) (privk trent))
                  (hash alice_1-0 h_1-0 t_1 l_1))) (privk trent))
            (pubk trent)))))
    ((recv (enc (enc n-0 (privk trent)) (pubk trent)))
      (send
        (enc
          (enc alice_1 h_1
            (enc n-0 alice_1 h_1 alice_1-0 h_1-0 t_1
              (hash alice_1-0 h_1-0 t_1 l_1) (privk trent))
            (hash alice_1-0 h_1-0 t_1 l_1) (privk trent))
          (pubk trent)))))
  (label 3)
  (parent 1)
  (unrealized (2 0))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton timestamping-service
  (vars (n data) (h h_1 t_1 l_1 text) (trent alice alice_1 name))
  (defstrand client 2 (t_1 t_1) (l (hash alice_1 h_1 t_1 l_1)) (n n)
    (h h) (h_1 h_1) (alice alice) (alice_1 alice_1) (trent trent))
  (defstrand origin 2 (n n) (h h) (h_1 h_1) (t_1 t_1) (l_1 l_1)
    (alice alice) (alice_1 alice_1) (trent trent))
  (defstrand big-bang 1 (n n) (trent trent))
  (precedes ((1 1) (0 1)) ((2 0) (1 0)))
  (non-orig (privk trent))
  (uniq-orig n)
  (operation encryption-test (added-strand big-bang 1)
    (enc n (privk trent)) (1 0))
  (strand-map 0 1)
  (traces
    ((send (cat h alice))
      (recv
        (enc n alice h alice_1 h_1 t_1 (hash alice_1 h_1 t_1 l_1)
          (privk trent))))
    ((recv (enc (enc n (privk trent)) (pubk trent)))
      (send
        (enc
          (enc alice h
            (enc n alice h alice_1 h_1 t_1 (hash alice_1 h_1 t_1 l_1)
              (privk trent)) (hash alice_1 h_1 t_1 l_1) (privk trent))
          (pubk trent))))
    ((send (enc (enc n (privk trent)) (pubk trent)))))
  (label 4)
  (parent 2)
  (unrealized (0 1))
  (comment "1 in cohort - 1 not yet seen"))

(defskeleton timestamping-service
  (vars (n n-0 data) (h h_1 h_1-0 t_1 l_1 text)
    (trent alice alice_1 alice_1-0 name))
  (defstrand client 2
    (t_1
      (enc n-0 alice_1 h_1 alice_1-0 h_1-0 t_1
        (hash alice_1-0 h_1-0 t_1 l_1) (privk trent)))
    (l
      (hash alice_1 h_1
        (enc n-0 alice_1 h_1 alice_1-0 h_1-0 t_1
          (hash alice_1-0 h_1-0 t_1 l_1) (privk trent))
        (hash alice_1-0 h_1-0 t_1 l_1))) (n n) (h h) (h_1 h_1)
    (alice alice) (alice_1 alice_1) (trent trent))
  (defstrand server 2
    (t_1
      (enc n-0 alice_1 h_1 alice_1-0 h_1-0 t_1
        (hash alice_1-0 h_1-0 t_1 l_1) (privk trent)))
    (l_1 (hash alice_1-0 h_1-0 t_1 l_1)) (n n) (h h) (h_1 h_1)
    (alice alice) (alice_1 alice_1) (trent trent))
  (defstrand origin 2 (n n-0) (h h_1) (h_1 h_1-0) (t_1 t_1) (l_1 l_1)
    (alice alice_1) (alice_1 alice_1-0) (trent trent))
  (defstrand big-bang 1 (n n-0) (trent trent))
  (precedes ((1 1) (0 1)) ((2 1) (1 0)) ((3 0) (2 0)))
  (non-orig (privk trent))
  (uniq-orig n n-0)
  (operation encryption-test (added-strand big-bang 1)
    (enc n-0 (privk trent)) (2 0))
  (strand-map 0 1 2)
  (traces
    ((send (cat h alice))
      (recv
        (enc n alice h alice_1 h_1
          (enc n-0 alice_1 h_1 alice_1-0 h_1-0 t_1
            (hash alice_1-0 h_1-0 t_1 l_1) (privk trent))
          (hash alice_1 h_1
            (enc n-0 alice_1 h_1 alice_1-0 h_1-0 t_1
              (hash alice_1-0 h_1-0 t_1 l_1) (privk trent))
            (hash alice_1-0 h_1-0 t_1 l_1)) (privk trent))))
    ((recv
       (cat
         (enc
           (enc alice_1 h_1
             (enc n-0 alice_1 h_1 alice_1-0 h_1-0 t_1
               (hash alice_1-0 h_1-0 t_1 l_1) (privk trent))
             (hash alice_1-0 h_1-0 t_1 l_1) (privk trent)) (pubk trent))
         h alice))
      (send
        (cat
          (enc n alice h alice_1 h_1
            (enc n-0 alice_1 h_1 alice_1-0 h_1-0 t_1
              (hash alice_1-0 h_1-0 t_1 l_1) (privk trent))
            (hash alice_1 h_1
              (enc n-0 alice_1 h_1 alice_1-0 h_1-0 t_1
                (hash alice_1-0 h_1-0 t_1 l_1) (privk trent))
              (hash alice_1-0 h_1-0 t_1 l_1)) (privk trent))
          (enc
            (enc
              (hash alice h
                (enc n alice h alice_1 h_1
                  (enc n-0 alice_1 h_1 alice_1-0 h_1-0 t_1
                    (hash alice_1-0 h_1-0 t_1 l_1) (privk trent))
                  (hash alice_1 h_1
                    (enc n-0 alice_1 h_1 alice_1-0 h_1-0 t_1
                      (hash alice_1-0 h_1-0 t_1 l_1) (privk trent))
                    (hash alice_1-0 h_1-0 t_1 l_1)) (privk trent))
                (hash alice_1 h_1
                  (enc n-0 alice_1 h_1 alice_1-0 h_1-0 t_1
                    (hash alice_1-0 h_1-0 t_1 l_1) (privk trent))
                  (hash alice_1-0 h_1-0 t_1 l_1))) (privk trent))
            (pubk trent)))))
    ((recv (enc (enc n-0 (privk trent)) (pubk trent)))
      (send
        (enc
          (enc alice_1 h_1
            (enc n-0 alice_1 h_1 alice_1-0 h_1-0 t_1
              (hash alice_1-0 h_1-0 t_1 l_1) (privk trent))
            (hash alice_1-0 h_1-0 t_1 l_1) (privk trent))
          (pubk trent))))
    ((send (enc (enc n-0 (privk trent)) (pubk trent)))))
  (label 5)
  (parent 3)
  (realized)
  (shape)
  (maps
    ((0)
      ((trent trent) (alice alice) (alice_1 alice_1) (n n) (h h)
        (h_1 h_1)
        (t_1
          (enc n-0 alice_1 h_1 alice_1-0 h_1-0 t_1
            (hash alice_1-0 h_1-0 t_1 l_1) (privk trent)))
        (l
          (hash alice_1 h_1
            (enc n-0 alice_1 h_1 alice_1-0 h_1-0 t_1
              (hash alice_1-0 h_1-0 t_1 l_1) (privk trent))
            (hash alice_1-0 h_1-0 t_1 l_1))))))
  (origs (n-0 (3 0)) (n (1 1))))

(defskeleton timestamping-service
  (vars (n n-0 data) (h h_1 t_1 l_1 h-0 text)
    (trent alice alice_1 alice-0 name))
  (defstrand client 2 (t_1 t_1) (l (hash alice_1 h_1 t_1 l_1)) (n n)
    (h h) (h_1 h_1) (alice alice) (alice_1 alice_1) (trent trent))
  (defstrand origin 2 (n n) (h h) (h_1 h_1) (t_1 t_1) (l_1 l_1)
    (alice alice) (alice_1 alice_1) (trent trent))
  (defstrand big-bang 1 (n n) (trent trent))
  (defstrand server 2
    (t_1
      (enc n alice h alice_1 h_1 t_1 (hash alice_1 h_1 t_1 l_1)
        (privk trent))) (l_1 (hash alice_1 h_1 t_1 l_1)) (n n-0) (h h-0)
    (h_1 h) (alice alice-0) (alice_1 alice) (trent trent))
  (precedes ((1 1) (0 1)) ((2 0) (1 0)) ((2 0) (3 0)) ((3 1) (0 1)))
  (non-orig (privk trent))
  (uniq-orig n n-0)
  (operation encryption-test (added-strand server 2)
    (enc n alice h alice_1 h_1 t_1 (hash alice_1 h_1 t_1 l_1)
      (privk trent)) (0 1)
    (enc
      (enc alice h
        (enc n alice h alice_1 h_1 t_1 (hash alice_1 h_1 t_1 l_1)
          (privk trent)) (hash alice_1 h_1 t_1 l_1) (privk trent))
      (pubk trent)))
  (strand-map 0 1 2)
  (traces
    ((send (cat h alice))
      (recv
        (enc n alice h alice_1 h_1 t_1 (hash alice_1 h_1 t_1 l_1)
          (privk trent))))
    ((recv (enc (enc n (privk trent)) (pubk trent)))
      (send
        (enc
          (enc alice h
            (enc n alice h alice_1 h_1 t_1 (hash alice_1 h_1 t_1 l_1)
              (privk trent)) (hash alice_1 h_1 t_1 l_1) (privk trent))
          (pubk trent))))
    ((send (enc (enc n (privk trent)) (pubk trent))))
    ((recv
       (cat
         (enc
           (enc alice h
             (enc n alice h alice_1 h_1 t_1 (hash alice_1 h_1 t_1 l_1)
               (privk trent)) (hash alice_1 h_1 t_1 l_1) (privk trent))
           (pubk trent)) h-0 alice-0))
      (send
        (cat
          (enc n-0 alice-0 h-0 alice h
            (enc n alice h alice_1 h_1 t_1 (hash alice_1 h_1 t_1 l_1)
              (privk trent))
            (hash alice h
              (enc n alice h alice_1 h_1 t_1 (hash alice_1 h_1 t_1 l_1)
                (privk trent)) (hash alice_1 h_1 t_1 l_1))
            (privk trent))
          (enc
            (enc
              (hash alice-0 h-0
                (enc n-0 alice-0 h-0 alice h
                  (enc n alice h alice_1 h_1 t_1
                    (hash alice_1 h_1 t_1 l_1) (privk trent))
                  (hash alice h
                    (enc n alice h alice_1 h_1 t_1
                      (hash alice_1 h_1 t_1 l_1) (privk trent))
                    (hash alice_1 h_1 t_1 l_1)) (privk trent))
                (hash alice h
                  (enc n alice h alice_1 h_1 t_1
                    (hash alice_1 h_1 t_1 l_1) (privk trent))
                  (hash alice_1 h_1 t_1 l_1))) (privk trent))
            (pubk trent))))))
  (label 6)
  (parent 4)
  (unrealized (3 0))
  (comment "2 in cohort - 2 not yet seen"))

(defskeleton timestamping-service
  (vars (n n-0 data) (h h_1 t_1 l_1 h-0 text)
    (trent alice alice_1 alice-0 name))
  (defstrand client 2 (t_1 t_1) (l (hash alice_1 h_1 t_1 l_1)) (n n)
    (h h) (h_1 h_1) (alice alice) (alice_1 alice_1) (trent trent))
  (defstrand origin 2 (n n) (h h) (h_1 h_1) (t_1 t_1) (l_1 l_1)
    (alice alice) (alice_1 alice_1) (trent trent))
  (defstrand big-bang 1 (n n) (trent trent))
  (defstrand server 2
    (t_1
      (enc n alice h alice_1 h_1 t_1 (hash alice_1 h_1 t_1 l_1)
        (privk trent))) (l_1 (hash alice_1 h_1 t_1 l_1)) (n n-0) (h h-0)
    (h_1 h) (alice alice-0) (alice_1 alice) (trent trent))
  (precedes ((1 1) (3 0)) ((2 0) (1 0)) ((3 1) (0 1)))
  (non-orig (privk trent))
  (uniq-orig n n-0)
  (operation encryption-test (displaced 4 1 origin 2)
    (enc alice h
      (enc n alice h alice_1 h_1 t_1 (hash alice_1 h_1 t_1 l_1)
        (privk trent)) (hash alice_1 h_1 t_1 l_1) (privk trent)) (3 0))
  (strand-map 0 1 2 3)
  (traces
    ((send (cat h alice))
      (recv
        (enc n alice h alice_1 h_1 t_1 (hash alice_1 h_1 t_1 l_1)
          (privk trent))))
    ((recv (enc (enc n (privk trent)) (pubk trent)))
      (send
        (enc
          (enc alice h
            (enc n alice h alice_1 h_1 t_1 (hash alice_1 h_1 t_1 l_1)
              (privk trent)) (hash alice_1 h_1 t_1 l_1) (privk trent))
          (pubk trent))))
    ((send (enc (enc n (privk trent)) (pubk trent))))
    ((recv
       (cat
         (enc
           (enc alice h
             (enc n alice h alice_1 h_1 t_1 (hash alice_1 h_1 t_1 l_1)
               (privk trent)) (hash alice_1 h_1 t_1 l_1) (privk trent))
           (pubk trent)) h-0 alice-0))
      (send
        (cat
          (enc n-0 alice-0 h-0 alice h
            (enc n alice h alice_1 h_1 t_1 (hash alice_1 h_1 t_1 l_1)
              (privk trent))
            (hash alice h
              (enc n alice h alice_1 h_1 t_1 (hash alice_1 h_1 t_1 l_1)
                (privk trent)) (hash alice_1 h_1 t_1 l_1))
            (privk trent))
          (enc
            (enc
              (hash alice-0 h-0
                (enc n-0 alice-0 h-0 alice h
                  (enc n alice h alice_1 h_1 t_1
                    (hash alice_1 h_1 t_1 l_1) (privk trent))
                  (hash alice h
                    (enc n alice h alice_1 h_1 t_1
                      (hash alice_1 h_1 t_1 l_1) (privk trent))
                    (hash alice_1 h_1 t_1 l_1)) (privk trent))
                (hash alice h
                  (enc n alice h alice_1 h_1 t_1
                    (hash alice_1 h_1 t_1 l_1) (privk trent))
                  (hash alice_1 h_1 t_1 l_1))) (privk trent))
            (pubk trent))))))
  (label 7)
  (parent 6)
  (realized)
  (shape)
  (maps
    ((0)
      ((trent trent) (alice alice) (alice_1 alice_1) (n n) (h h)
        (h_1 h_1) (t_1 t_1) (l (hash alice_1 h_1 t_1 l_1)))))
  (origs (n-0 (3 1)) (n (2 0))))

(defskeleton timestamping-service
  (vars (n n-0 data) (h h_1 t_1 l_1 h-0 text)
    (trent alice alice_1 alice-0 name))
  (defstrand client 2 (t_1 t_1) (l (hash alice_1 h_1 t_1 l_1)) (n n)
    (h h) (h_1 h_1) (alice alice) (alice_1 alice_1) (trent trent))
  (defstrand origin 2 (n n) (h h) (h_1 h_1) (t_1 t_1) (l_1 l_1)
    (alice alice) (alice_1 alice_1) (trent trent))
  (defstrand big-bang 1 (n n) (trent trent))
  (defstrand server 2
    (t_1
      (enc n alice h alice_1 h_1 t_1 (hash alice_1 h_1 t_1 l_1)
        (privk trent))) (l_1 (hash alice_1 h_1 t_1 l_1)) (n n-0) (h h-0)
    (h_1 h) (alice alice-0) (alice_1 alice) (trent trent))
  (defstrand origin 2 (n n) (h h) (h_1 h_1) (t_1 t_1) (l_1 l_1)
    (alice alice) (alice_1 alice_1) (trent trent))
  (precedes ((1 1) (0 1)) ((2 0) (1 0)) ((2 0) (4 0)) ((3 1) (0 1))
    ((4 1) (3 0)))
  (non-orig (privk trent))
  (uniq-orig n n-0)
  (operation encryption-test (added-strand origin 2)
    (enc alice h
      (enc n alice h alice_1 h_1 t_1 (hash alice_1 h_1 t_1 l_1)
        (privk trent)) (hash alice_1 h_1 t_1 l_1) (privk trent)) (3 0))
  (strand-map 0 1 2 3)
  (traces
    ((send (cat h alice))
      (recv
        (enc n alice h alice_1 h_1 t_1 (hash alice_1 h_1 t_1 l_1)
          (privk trent))))
    ((recv (enc (enc n (privk trent)) (pubk trent)))
      (send
        (enc
          (enc alice h
            (enc n alice h alice_1 h_1 t_1 (hash alice_1 h_1 t_1 l_1)
              (privk trent)) (hash alice_1 h_1 t_1 l_1) (privk trent))
          (pubk trent))))
    ((send (enc (enc n (privk trent)) (pubk trent))))
    ((recv
       (cat
         (enc
           (enc alice h
             (enc n alice h alice_1 h_1 t_1 (hash alice_1 h_1 t_1 l_1)
               (privk trent)) (hash alice_1 h_1 t_1 l_1) (privk trent))
           (pubk trent)) h-0 alice-0))
      (send
        (cat
          (enc n-0 alice-0 h-0 alice h
            (enc n alice h alice_1 h_1 t_1 (hash alice_1 h_1 t_1 l_1)
              (privk trent))
            (hash alice h
              (enc n alice h alice_1 h_1 t_1 (hash alice_1 h_1 t_1 l_1)
                (privk trent)) (hash alice_1 h_1 t_1 l_1))
            (privk trent))
          (enc
            (enc
              (hash alice-0 h-0
                (enc n-0 alice-0 h-0 alice h
                  (enc n alice h alice_1 h_1 t_1
                    (hash alice_1 h_1 t_1 l_1) (privk trent))
                  (hash alice h
                    (enc n alice h alice_1 h_1 t_1
                      (hash alice_1 h_1 t_1 l_1) (privk trent))
                    (hash alice_1 h_1 t_1 l_1)) (privk trent))
                (hash alice h
                  (enc n alice h alice_1 h_1 t_1
                    (hash alice_1 h_1 t_1 l_1) (privk trent))
                  (hash alice_1 h_1 t_1 l_1))) (privk trent))
            (pubk trent)))))
    ((recv (enc (enc n (privk trent)) (pubk trent)))
      (send
        (enc
          (enc alice h
            (enc n alice h alice_1 h_1 t_1 (hash alice_1 h_1 t_1 l_1)
              (privk trent)) (hash alice_1 h_1 t_1 l_1) (privk trent))
          (pubk trent)))))
  (label 8)
  (parent 6)
  (seen 7)
  (seen-ops (7 (operation generalization deleted (1 0))))
  (realized)
  (comment "1 in cohort - 0 not yet seen"))

(comment "Nothing left to do")
