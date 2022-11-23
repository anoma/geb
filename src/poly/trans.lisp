(in-package :geb.poly.trans)

(defgeneric moprh-to-poly (morphism)
  (:documentation "Turns a GEB:SUBSTMORPH into a POLY"))


;; I really should move where this function lives
;; probably best to move where all transition functions live!?
(defgeneric poly-to-vampir (morphism value)
  (:documentation "Turns a POLY term into a Vamp-IR term with a given value"))

(defun poly-to-circuit (morphism)
  "Turns a POLY term into a Vamp-IR Gate"
  morphism
  (error "not implemented"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Morph to Poly Implementation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; we could get exhaustion here over poly, with
;; subclass-responsibility implemented for any value that does not
;; match. See the commented code.
(defmethod morph-to-poly ((obj geb:<substmorph>))
  ;; (typecase-of poly obj
  ;;   (otherwise (subclass-responsibility obj)))
  (subclass-responsibility obj))

(defmethod morph-to-poly ((obj geb:<substobj>))
  (declare (ignore obj))
  ident)

(defmethod morph-to-poly ((obj geb:init))
  (declare (ignore obj))
  0)

(defmethod morph-to-poly ((obj geb:terminal))
  (declare (ignore obj))
  0)

(defmethod morph-to-poly ((obj geb:inject-left))
  (declare (ignore obj))
  ident)

(defmethod morph-to-poly ((obj geb:inject-right))
  (+ (obj-to-nat (mcar obj)) ident))

(defmethod morph-to-poly ((obj geb:comp))
  (compose (morph-to-poly (mcar obj))
           (morph-to-poly (mcadr obj))))

(defmethod morph-to-poly ((obj geb:case))
  obj
  (error "not implemented"))

(defmethod morph-to-poly ((obj geb:pair))
  obj
  (error "not implemented"))

(defmethod morph-to-poly ((obj geb:project-right))
  (let ((nat (obj-to-nat (mcadr obj))))
    (if (zerop nat)
        nat
        (mod ident nat))))

(defmethod morph-to-poly ((obj geb:project-left))
  (let ((nat (obj-to-nat (mcar obj))))
    (if (zerop nat)
        nat
        (/ ident nat))))

(defmethod morph-to-poly ((obj geb:distribute))
  (let ((cx (obj-to-nat (mcar obj)))
        (cy (obj-to-nat (mcadr obj)))
        (cz (obj-to-nat (mcaddr obj))))
    (if (and (zerop cy) (zerop cz))
        0
        (let* ((yz   (+ cy cz))
               (xin  (/ ident yz))
               (yzin (mod ident yz)))
          (if-lt yzin cy
                 (+ (* cy xin) yzin)
                 (+ (* cz xin) (- yzin cy) (* cx cy)))))))

(defun obj-to-nat (obj)
  (so-card-alg obj))

(defgeneric so-card-alg (obj)
  (:documentation "Gets the cardinality of the given object"))

(defmethod so-card-alg ((obj geb:<substobj>))
  ;; we don't use the cata morphism so here we are. Doesn't give me
  ;; much extra
  (match-of geb:substobj obj
    (geb:alias        (so-card-alg (obj obj)))
    ((geb:prod a b)   (cl:* (so-card-alg a)
                            (so-card-alg b)))
    ((geb:coprod a b) (cl:+ (so-card-alg a)
                            (so-card-alg b)))
    (geb:so0          1)
    (geb:so1          1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Poly to Vampir Implementation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; we could get exhaustion here over poly, with
;; subclass-responsibility implemented for any value that does not
;; match. See the commented code.
(defmethod poly-to-vampir ((obj <poly>) value)
  ;; (typecase-of poly obj
  ;;   (otherwise (subclass-responsibility obj)))
  (subclass-responsibility obj))

(-> direct-fields-to-list-vampir (geb.mixins:direct-pointwise-mixin) list)
(defun direct-fields-to-list (obj)
  (mapcar #'cdr (geb.mixins:to-pointwise-list obj)))

;; all of this is likely wrong, as we are taking morph-isms which
;; evaluate to themselves but I'm unsure of how this works on an input
;; level

(defmethod poly-to-vampir ((obj integer) value)
  "Numbers act like a constant function, ignoring input"
  (declare (ignore value))
  (make-constant :const obj))

(defmethod poly-to-vampir ((obj ident) value)
  "Identity acts as the identity function"
  value)

(defun infix-creation (symbol obj value)
  (make-infix :op symbol
              :lhs (poly-to-vampir (mcar obj) value)
              :rhs (poly-to-vampir (mcadr obj) value)))

(defmethod poly-to-vampir ((obj +) value)
  "Propagates the value and adds them"
  (infix-creation :+ obj value))

(defmethod poly-to-vampir ((obj *) value)
  "Propagates the value and times them"
  (infix-creation :* obj value))

(defmethod poly-to-vampir ((obj -) value)
  "Propagates the value and subtracts them"
  (infix-creation :- obj value))


(defmethod poly-to-vampir ((obj /) value)
  ;; this should error
  (infix-creation :/ obj value))

(defmethod poly-to-vampir ((obj compose) value)
  (poly-to-vampir (mcar obj)
                  (poly-to-vampir (mcadr obj) value)))

(defmethod poly-to-vampir ((obj mod) value)
  (error "mod logic not in yet"))

(defmethod poly-to-vampir ((obj if-zero) value)
  (error "mod logic not in yet"))

(defmethod poly-to-vampir ((obj if-lt) value)
  (error "mod logic not in yet"))
