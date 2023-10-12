(in-package :geb.vampir)

;; We use CL streams as they are much better for concatenating to, and
;; have us worry less. they are a mutable interface however.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; FORMAT RUNDOWN FOR THOSE WHO ARE UNFAMILIAR
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; https://www.cs.cmu.edu/Groups/AI/html/cltl/clm/node257.html

;; DSL FOR NEWLINES AND CONTROL OF IT

;; ~4I  = (pprint-indent :block   4)
;; ~4:I = (pprint-indent :current 4)
;; ~_   = (pprint-newline :linear)
;; ~@_  = (pprint-newline :miser)
;; ~:@_ = (pprint-newline :mandatory)
;; ~:_  = (pprint-newline :fill)


;; FOR PRINTING NORMALLY NOTE THESE TAKE ARGUMENTS!

;; ~(~a~)    = print symbol lower case instead of upper case
;; ~{~A~}    = prints a list element by element.

;; ~{~A~^ ~} = prints a list element by element, the last element of
;;             the list does not print the extra space
;; EXAMPLE:
;; VAMPIR> (format nil "~{~A~^ ~}" (list 1 2 3 4 5))
;; "1 2 3 4 5"
;; VAMPIR> (format nil "~{~A ~}" (list 1 2 3 4 5))
;; "1 2 3 4 5 "

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; TopLevel Extraction
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Statement Extraction
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmethod print-object ((pub spc:pub) stream)
  (pprint-logical-block (stream nil)
    (format stream "~I~{pub ~(~a~)~^~:@_~}" (spc:wires pub))))

(defmethod print-object ((alias spc:alias) stream)
  (pprint-logical-block (stream nil)
    (format stream "def ~(~a~)" (spc:name alias))
    (format stream "~4I~{ ~@_~(~a~)~} " (spc:inputs alias))

    ;; no more output circuits, but may it rest here
    ;; (when (spc:outputs alias)
    ;;   (format stream "~@_->~{ ~@_~(~a~)~} " (spc:outputs alias)))

    (format stream "~0I= ~@_{~2I")
    (extract-constraint-list (spc:body alias) stream)
    (format stream "~0I~:@_};")))

(-> extract-constraint-list (spc:constraint-list &optional stream) stream)
(defun extract-constraint-list (cs &optional (stream *standard-output*))
  (format stream "~{~:@_~A~^;~}" cs)
  stream)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Constraint Extraction
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmethod print-object ((bind spc:bind) stream)
  (pprint-logical-block (stream nil)
    (cond ((cdr (spc:names bind))
           (format stream "def (~{~A~^, ~}) = " (spc:names bind)))
          ((spc:names bind)
           (format stream "def ~{~A~^, ~} = " (spc:names bind))))
    (format stream "~2I~_~A" (spc:value bind))))

(defmethod print-object ((eql spc:equality) stream)
  (pprint-logical-block (stream nil)
    (format stream "~A ~2:I= ~4I~@_~A" (spc:lhs eql) (spc:rhs eql))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Expression Extraction
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(-> extract-expression (spc:expression &optional stream) stream)
(defun extract-expression (expr &optional (stream *standard-output*))
  "Extract-expression is like a `print-object' but adds an extra set
of ()'s for any non normal form"
  (etypecase-of spc:expression expr
    (spc:infix
     (pprint-logical-block (stream nil :prefix "(" :suffix ")")
       (print-object expr stream)))
    (spc:application
     (pprint-logical-block (stream nil :prefix "(" :suffix ")")
       (print-object expr stream)))
    ((or spc:tuple spc:normal-form spc:curly)
     (print-object expr stream))
    (geb.extension.spec:common-sub-expression
     (extract-expression (geb.spec:obj expr) stream)))
  stream)

(defmethod print-object ((infix spc:infix) stream)
  (extract-expression (spc:lhs infix) stream)
  (format stream " ~A " (spc:op infix))
  (extract-expression (spc:rhs infix) stream))

(defmethod print-object ((application spc:application) stream)
  (format stream "~(~a~)" (spc:func application))
  ;; put fill printing?
  (dolist (expr (spc:arguments application))
    (format stream " ")
    (extract-expression expr stream)))

(defmethod print-object ((wire spc:wire) stream)
  (format stream "~(~a~)" (spc:var wire)))

(defmethod print-object ((tup spc:tuple) stream)
  (pprint-logical-block (stream nil :prefix "(" :suffix ")")
    (format stream "~{~(~a~)~^, ~}" (spc:wires tup))))

(defmethod print-object ((curly spc:curly) stream)
  (format stream "{~A}" (spc:value curly)))

(defmethod print-object ((const spc:constant) stream)
  (format stream "~(~a~)" (spc:const const)))

(defmethod print-object ((brackets spc:brackets) stream)
  (format stream "[]"))
