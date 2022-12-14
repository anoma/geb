(in-package :geb.poly)

(defgeneric to-vampir (morphism value)
  (:documentation "Turns a POLY term into a Vamp-IR term with a given value"))

(defun to-circuit (morphism name)
  "Turns a POLY term into a Vamp-IR Gate with the given name"
  (let ((wire (vamp:make-wire :var :x)))
    (vamp:make-alias :name name
                     :inputs (list wire)
                     :body (list (to-vampir morphism wire)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Poly to Vampir Implementation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; we could get exhaustion here over poly, with
;; subclass-responsibility implemented for any value that does not
;; match.
;;
;; See geb:to-poly
;;
;; to see what that style of code is like as apposed to this.
(defmethod to-vampir ((obj <poly>) value)
  (subclass-responsibility obj))

(-> direct-fields-to-list-vampir (geb.mixins:direct-pointwise-mixin) list)
(defun direct-fields-to-list (obj)
  (mapcar #'cdr (geb.mixins:to-pointwise-list obj)))

;; all of this is likely wrong, as we are taking morph-isms which
;; evaluate to themselves but I'm unsure of how this works on an input
;; level

(defmethod to-vampir ((obj integer) value)
  "Numbers act like a constant function, ignoring input"
  (declare (ignore value))
  (vamp:make-constant :const obj))

(defmethod to-vampir ((obj ident) value)
  "Identity acts as the identity function"
  value)

(defun infix-creation (symbol obj value)
  (vamp:make-infix :op symbol
                   :lhs (to-vampir (mcar obj) value)
                   :rhs (to-vampir (mcadr obj) value)))

(defmethod to-vampir ((obj +) value)
  "Propagates the value and adds them"
  (infix-creation :+ obj value))

(defmethod to-vampir ((obj *) value)
  "Propagates the value and times them"
  (infix-creation :* obj value))

(defmethod to-vampir ((obj -) value)
  "Propagates the value and subtracts them"
  (infix-creation :- obj value))

(defmethod to-vampir ((obj /) value)
  ;; this should error
  (infix-creation :/ obj value))

(defmethod to-vampir ((obj compose) value)
  (to-vampir (mcar obj)
             (to-vampir (mcadr obj) value)))

(defmethod to-vampir ((obj mod) value)
  (error "mod logic not in yet"))

(defmethod to-vampir ((obj if-zero) value)
  (error "mod logic not in yet"))

(defmethod to-vampir ((obj if-lt) value)
  (error "mod logic not in yet"))
