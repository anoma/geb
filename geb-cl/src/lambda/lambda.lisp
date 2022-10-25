(in-package #:geb.lambda)

;; Don't even bother to make data structures, just quote our forms

(named-readtables:in-readtable :fare-quasiquote)

;; we are being lazy no need for defclass for something so short lived
;; IMO
(defstruct context
  (depth   0          :type fixnum)
  (mapping (fset:map) :type fset:map))

(defstruct index
  (depth 0 :type fixnum))

(-> curry-lambda (t) t)
(defun curry-lambda (term)
  "Takes a lambda term and expands all the arguments"
  (match term
    (`(lambda ,param ,body)
      (let ((body (curry-lambda body)))
        (mvfoldr (cl:lambda (param body)
                   (list 'lambda param body))
                 (butlast param)
                 (list 'lambda (car (last param)) body))))
    ((cons x xs)
     (cons (curry-lambda x)
           (curry-lambda xs)))
    (a a)))

(-> nameless (t &optional context) t)
(defun nameless (term &optional (context (make-context)))
  context
  (match term
    (`(lambda ,param ,body)
      (let ((new-depth (1+ (context-depth context))))
        (list 'lambda (nameless body
                            (make-context
                             :depth new-depth
                             :mapping (fset:with (context-mapping context)
                                                 param
                                                 (- new-depth)))))))
    ((cons f xs)
     (cons (nameless f context) (nameless xs context)))
    ;; we only care if it's in the map, if it isn't ignore it!
    ((guard a (and (atom a)))
     (let ((depth (fset:@ (context-mapping context) a)))
       (if depth
           (make-index :depth (+ (context-depth context) depth))
           a)))
    (a a)))
