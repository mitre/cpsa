#!/usr/bin/guile \
-e main -s
!#
(use-modules (ice-9 pretty-print))
;;; For an R6RS script, add an import statement.

;;; Synopsis: renumber strands in skeletons

;;; A permutation of length n is represented as a list of natural
;;; numbers that contains all the numbers less than n.

;;; This program renumbers all the skeletons in a file that have the
;;; same number of strands as is the length of the permutation.
;;; Everything else is passed through unchanged.

;;; Usage: cpsaperm [-h] [-o FILE] FILE INT...
;;; where INT... specifies a permutation.
;;; Use - in place of FILE for the standard port

;;; Example: cpsaperm -o out.txt in.txt 1 0
;;; Swaps the strands in skeletons with two strands.

;;; This program does not check that the given permutation is in fact
;;; a valid permutation, so be sure to check your output carefully.
;;; Make sure your permutation has no repeats.

;;; John D. Ramsdell -- October 2012

;;; Create a function that applies a permutation to a form
(define (apply-perm perm)
  (let ((n (length perm)))
    (lambda (form)
      (let ((skel (parse-skel form)))
	(cond ((not skel) form)		; Ignore non-skeletons
	      ;; Ignore skeletons with the wrong number of strands
	      ((not (= n (length (skel-strands skel)))) form)
	      (else
	       (let ((skel (apply-perm-to-skel perm skel)))
		  `(defskeleton
		    ,(skel-protocol skel)
		    ,(skel-vars skel)
		    ,@(append (skel-strands skel) (skel-alist skel))))))))))

;;; A skeleton is represented as list with the following fields.

(define (skel-protocol skel) (car skel))
(define (skel-vars skel) (cadr skel))
(define (skel-strands skel) (caddr skel))
(define (skel-alist skel) (cdddr skel))
(define (make-skel protocol vars strands alist)
  (cons protocol (cons vars (cons strands alist))))

;;; Creates a skeleton structure or returns #f on error.
(define (parse-skel form)
  (and (skel? form)
       (let loop ((body (cdddr form)) (strands '()))
	 (cond ((null? body)
		(make-skel (cadr form) (caddr form)
			   (reverse strands) body))
	       ((or (eq? 'defstrand (caar body))
		    (eq? 'deflistener (caar body)))
		(loop (cdr body) (cons (car body) strands)))
	       (else
		(make-skel (cadr form) (caddr form)
			   (reverse strands) body))))))

;;; Is form a defskeleton

(define (skel? form)
  (and (list? form)
       (<= 4 (length form))
       (eq? 'defskeleton (car form))
       (alist? (cddr form))))

(define (alist? form)			; Is form a list of pairs?
  (or (null? form)
      (and (pair? form)
	   (pair? (car form))
	   (alist? (cdr form)))))

;;; To apply a permutation to a skeleton, permute the strands and the
;;; node orderings.
(define (apply-perm-to-skel perm skel)
  (let ((strands (skel-strands skel)))
    (make-skel
     (skel-protocol skel)
     (skel-vars skel)
     (map (lambda (index)
	    (list-ref strands index))
	  perm)
     (map (apply-perm-to-alist perm) (skel-alist skel)))))

;;; Apply a permutation to the node orderings
(define (apply-perm-to-alist perm)
  (lambda (entry)
    (if (eq? (car entry) 'precedes)
	(cons (car entry)
	      (map (apply-perm-to-pair perm) (cdr entry)))
	entry)))

(define (apply-perm-to-pair perm)
  (lambda (ordered-pair)
    (if (and (list? ordered-pair) (= 2 (length ordered-pair)))
	(list (apply-perm-to-node perm (car ordered-pair))
	      (apply-perm-to-node perm (cadr ordered-pair)))
	ordered-pair)))

(define (apply-perm-to-node perm node)
    (if (and (list? node) (= 2 (length node)))
	(list (list-ref perm (car node)) (cadr node))
	node))

;;; The main driver loop and command-line processing

;;; The main loop calls the transformer on each S-expression read from
;;; the current input.

(define (filter perm)
  (let ((transformer (apply-perm perm)))
    (lambda ()
      (do ((form (read) (read)))
	  ((eof-object? form))
	(pretty-print (transformer form))))))

;;; A file description is #f for the standard port, or a file name
;;; that is a non-empty string that does not start with hyphen.

(define (file-description? file)
   (or (not file)
       (and (> (string-length file) 0)
	    (not (char=? #\- (string-ref file 0))))))

;;; After command-line processing, this routine opens files as needed.

(define (go input output perm)
  (let ((thunk (filter perm)))
    (cond ((not (file-description? input))
	   (display-error "bad input file name"))
	  ((not (file-description? output))
	   (display-error "bad output file name"))
	  (input
	   (with-input-from-file input
	     (lambda ()
	       (if output
		   (with-output-to-file output thunk)
		   (thunk)))))
	  (output
	   (with-output-to-file output thunk))
	  (else
	   (thunk)))))

;;; Parse command-line arguments and pass the result to the go function.

(define (main args)
  (let loop ((args (cdr args)) (output #f))
    (cond ((null? args) 		; No input file specified
	   (display-error "bad args"))
	  ((string=? (car args) "-h")
	   (display-help))		; Print help message
	  ((string=? (car args) "-o")
	   (if (null? (cdr args))
	       (display-error "bad args")
	       (loop (cddr args) (cadr args)))) ; Found an output file
	  ((string=? (car args) "-")
	   (check-perm #f output (cdr args)))
	  (else					; Found input file
	   (check-perm (car args) output (cdr args))))))

;;; Make sure a permutation is a list of non-negative integers less
;;; that the length of the permutation.
(define (check-perm input output args)
  (let ((n (length args)))
    (let loop ((args args) (perm '()))
      (if (null? args)
	  (go input output (reverse perm))
	  (let ((index (string->number (car args))))
	    (if (and (integer? index)
		     (not (negative? index))
		     (< index n))
		(loop (cdr args) (cons index perm))
		(display-error "bad permutation")))))))

(define (display-help)
  (display-error "cpsaperm [-h] [-o FILE] FILE INT...")
  (display-error "where INT... specifies a permutation.")
  (display-error "Use - as FILE for the standard input."))

(define (display-error obj)
  (display obj (current-error-port))
  (newline (current-error-port)))

;;; For an R6RS script, add the following:
;;; (main (command-line))
