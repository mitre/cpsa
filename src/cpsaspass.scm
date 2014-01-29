#!/usr/bin/guile \
-e main -s
!#
(use-modules (ice-9 pretty-print))
;;; For an R6RS script, add an import statement.

(define (consume form)
  (let ((label (skel-label form))
	(vars (skel-assq 'vars form))
	(theorems (skel-assq 'obligations form)))
    (if (and label vars theorems)     ; Translate when parts available
	(translate label (cdr vars) (cdr theorems)))))

;;; Is form a defskeleton that can be used with assq?

(define (skel? form)
  (and (pair? form)
       (eq? 'defskeleton (car form))
       (pair? (cdr form))
       (alist? (cddr form))))

(define (alist? form)			; Is form a list of pairs?
  (or (null? form)
      (and (pair? form)
	   (pair? (car form))
	   (alist? (cdr form)))))

;;; Extract pieces from the top-level form

(define (skel-assq key form)
  (and (skel? form)
       (assq key (cddr form))))

(define (skel-label form)
  (and (skel? form)
       (let ((form (skel-assq 'label form)))
	 (and form
	      (pair? (cdr form))
	      (null? (cddr form))
	      (number? (cadr form))
	      (cadr form)))))

;;; A stub for the translator

(define (translate label vars theorems)
  (pretty-print `(deftheorems ,label (vars ,@vars) ,@theorems)))

;;; The main driver loop and command-line processing

;;; The main loop calls consume on each S-expression read from the
;;; current input.

(define (filter)
  (do ((form (read) (read)))
      ((eof-object? form))
    (consume form)))

;;; A file description is #f for the standard port, or a file name
;;; that is a non-empty string that does not start with hyphen.

(define (file-description? file)
   (or (not file)
       (and (> (string-length file) 0)
	    (not (char=? #\- (string-ref file 0))))))

;;; After command-line processing, this routine opens files as needed.

(define (go input output)
  (cond ((not (file-description? input))
	 (display-error "bad input file name"))
	((not (file-description? output))
	 (display-error "bad output file name"))
	(input
	 (with-input-from-file input
	   (lambda ()
	     (if output
		 (with-output-to-file output filter)
		 (filter)))))
	(output
	 (with-output-to-file output filter))
	(else
	 (filter))))

;;; Parse command-line arguments and pass the result to the go function.

(define (main args)
  (let loop ((args (cdr args)) (output #f))
    (cond ((null? args) 		; No input file specified
	   (go #f output))
	  ((string=? (car args) "-h")
	   (display-help))		; Print help message
	  ((string=? (car args) "-o")
	   (if (null? (cdr args))
	       (display-error "bad args")
	       (loop (cddr args) (cadr args)))) ; Found an output file
	  ((null? (cdr args))		; An input file was specified
	   (go (car args) output))
	  (else
	   (display-error "bad args")))))

(define (display-help)
  (display-error "cpsaspass [-h] [-o FILE] [FILE]"))

(define (display-error obj)
  (display obj (current-error-port))
  (newline (current-error-port)))

;;; For an R6RS script, add the following:
;;; (main (command-line))
