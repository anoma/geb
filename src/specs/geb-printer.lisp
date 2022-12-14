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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; TopLevel Extraction
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package :geb.spec)

;; normal s-expression pretty printer.
;; only doing this as Ι think we want to be reflective in the future.
;; We can make other printers if we want.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Subst Constructor Printer
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun same-type-to-list (pair type &optional acc)
  "converts the given type to a list format"
  (if (typep (mcadr pair) type)
      (same-type-to-list (mcadr pair) type (cons (mcar pair) acc))
      (reverse (list* (mcadr pair) (mcar pair) acc))))

(-> pair-to-list (pair &optional list) list)
(defun pair-to-list (pair &optional acc)
  "converts excess pairs to a list format"
  (if (typep (mcdr pair) 'pair)
      (pair-to-list (mcdr pair)
                    (cons (mcar pair) acc))
      (reverse (list* (mcdr pair) (mcar pair) acc))))

;; Prefix Prod, collapse
(defmethod print-object ((obj prod) stream)
  (pprint-logical-block (stream nil :prefix "(" :suffix ")")
    (format stream "×~0:I ~{~W~^~_ ~}" (same-type-to-list obj 'prod))))

;; Prefix coprod, collapse
(defmethod print-object ((obj coprod) stream)
  (pprint-logical-block (stream nil :prefix "(" :suffix ")")
    (format stream "+~0:I ~{~W~^~_ ~}" (same-type-to-list obj 'coprod))))

(defmethod print-object ((obj so1) stream)
  (format stream "s-1"))

(defmethod print-object ((obj so0) stream)
  (format stream "s-0"))

(defmethod print-object ((obj alias) stream)
  (format stream "~W" (name obj)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Subst Morphism Printer
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmethod print-object ((obj terminal) stream)
  (pprint-logical-block (stream nil :prefix "(" :suffix ")")
    (format stream "->1~1:I ~W" (obj obj))))

(defmethod print-object ((obj init) stream)
  (pprint-logical-block (stream nil :prefix "(" :suffix ")")
    (format stream "0->~1:I ~W" (obj obj))))

(defmethod print-object ((obj inject-left) stream)
  (pprint-logical-block (stream nil :prefix "(" :suffix ")")
    (format stream "->left~1:I ~W ~_~W" (mcar obj) (mcadr obj))))

(defmethod print-object ((obj inject-right) stream)
  (pprint-logical-block (stream nil :prefix "(" :suffix ")")
    (format stream "->right~1:I ~W ~_~W" (mcar obj) (mcadr obj))))

(defmethod print-object ((obj project-left) stream)
  (pprint-logical-block (stream nil :prefix "(" :suffix ")")
    (format stream "<-left~1:I ~W ~_~W" (mcar obj) (mcadr obj))))

(defmethod print-object ((obj project-right) stream)
  (pprint-logical-block (stream nil :prefix "(" :suffix ")")
    (format stream "<-right~1:I ~W ~_~W" (mcar obj) (mcadr obj))))

(defmethod print-object ((obj case) stream)
  (pprint-logical-block (stream nil :prefix "(" :suffix ")")
    (format stream "case~1:I ~W ~_~W" (mcar obj) (mcadr obj))))

(defmethod print-object ((obj comp) stream)
  (pprint-logical-block (stream nil :prefix "(" :suffix ")")
    (format stream "∘~0:I ~{~W~^~_ ~}" (same-type-to-list obj 'comp))))

(defmethod print-object ((obj distribute) stream)
  (pprint-logical-block (stream nil :prefix "(" :suffix ")")
    (format stream "dist~1:I ~W ~_~W ~_~W" (mcar obj) (mcadr obj) (mcaddr obj))))

(defmethod print-object ((obj pair) stream)
  (pprint-logical-block (stream nil :prefix "(" :suffix ")")
    (format stream "~-1I~{~W~^~_ ~}" (pair-to-list obj))))

(defmethod print-object ((obj functor) stream)
  (pprint-logical-block (stream nil :prefix "(" :suffix ")")
    (format stream "FUNCTOR<>")))
