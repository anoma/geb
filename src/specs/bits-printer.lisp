;; TO DO: 


(in-package #:geb.bits.spec)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Subst Constructor Printer
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; we are going to be super lazy about this, just make a format
(defmacro easy-printer (class-name)
  `(defmethod print-object ((obj ,class-name) stream)
     (print-object (cons ',class-name
                         (mapcar #'cdr (geb.mixins:to-pointwise-list obj)))
                   stream)))

(easy-printer compose)
(easy-printer fork)
(easy-printer parallel)
(easy-printer negation)
(easy-printer conjunction)
(easy-printer swap)
(easy-printer true)
(easy-printer false)
(easy-printer identity)
(easy-printer drop)
(easy-printer branch)

(defmethod print-object ((obj ident) stream)
  (print-unreadable-object (obj stream :type nil :identity nil)
    (format stream "IDENT")))
