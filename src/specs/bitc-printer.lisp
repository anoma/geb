(in-package #:geb.bitc.spec)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Subst Constructor Printer
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; we are going to be super lazy about this, just make a format
(defmacro easy-printer (class-name)
  `(defmethod print-object ((obj ,class-name) stream)
     (format stream "~A"
             (cons ',class-name
                   (mapcar #'cdr (geb.mixins:to-pointwise-list obj))))))

(easy-printer compose)
(easy-printer fork)
(easy-printer parallel)
(easy-printer swap)
(easy-printer one)
(easy-printer zero)
(easy-printer ident)
(easy-printer drop)
(easy-printer branch)

(defmethod print-object ((obj ident) stream)
  (print-unreadable-object (obj stream :type nil :identity nil)
    (format stream "IDENT")))
