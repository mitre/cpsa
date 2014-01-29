#!/usr/bin/guile \
-e main -s
!#
;;; For an R6RS script, add an import statement.

(define parents '())
(define realized '())

;; This program looks for shapes that have no unrealized parent.
(define (consume form)
  (let ((label (skel-label form))
	(parent (skel-assq 'parent form))
	(seen (skel-assq 'seen form))
	(unrealized (skel-assq 'unrealized form)))
    (if label
	(begin
	  (if parent
	      (set! parents (cons (cons label (cadr parent)) parents)))
	  (if seen
	      (for-each
	       (lambda (child)
		 (if (not (equal? child label))
		     (set! parents (cons (cons child label) parents))))
	       (cdr seen)))
	  (set! realized
		(cons (cons label (and unrealized (null? (cdr unrealized))))
		      realized))))))

(define (summarize)
  (for-each
   (lambda (realized)
     (let ((label (car realized)))
     (if (and (shape? label)
	      (have-parents? label)
	      (parents-realized? label))
	 (begin (write label) (newline)))))
   realized))

;;; A shape is realised and is not a parent
(define (shape? label)
  (and (realized? label)
       (let loop ((parents parents))
	 (or (null? parents)
	     (and (not (equal? label (cdar parents)))
		  (loop (cdr parents)))))))

;;; Does this skeleton have at least one parent?
(define (have-parents? label)
  (let loop ((parents parents))
    (and (not (null? parents))
	 (or (equal? label (caar parents))
	     (loop (cdr parents))))))

;;; Does this skeleton have only realized parents?
(define (parents-realized? label)
  (let loop ((parents parents))
    (or (null? parents)
	(and (or (not (equal? label (caar parents)))
		 (realized? (cdar parents)))
	     (loop (cdr parents))))))

(define (realized? label)
  (let loop ((realized realized))
    (cond ((null? realized) #f)
	  ((equal? label (caar realized)) (cdar realized))
	  (else (loop (cdr realized))))))

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

;;; The main driver loop and command-line processing

;;; The main loop calls consume on each S-expression read from the
;;; current input.

(define (filter)
  (do ((form (read) (read)))
      ((eof-object? form) (summarize))
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
  (display-error "genshape [-h] [-o FILE] [FILE]"))

(define (display-error obj)
  (display obj (current-error-port))
  (newline (current-error-port)))

;;; For an R6RS script, add the following:
;;; (main (command-line))
