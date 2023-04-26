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
;; CL-USER> (format nil "~{~A~^ ~}" (list 1 2 3 4 5))
;; "1 2 3 4 5"
;; CL-USER> (format nil "~{~A ~}" (list 1 2 3 4 5))
;; "1 2 3 4 5 "


(in-package #:geb.extension.spec)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Subst Constructor Printer
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmethod print-object ((obj common-sub-expression) stream)
  (print-unreadable-object (obj stream)
    (print-object (obj obj) stream)))
