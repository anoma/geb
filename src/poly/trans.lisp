(in-package :geb.poly.trans)

(defgeneric to-vampir (morphism value let-vars)
  (:documentation "Turns a POLY term into a Vamp-IR term with a given value"))

(defun to-circuit (morphism name)
  "Turns a POLY term into a Vamp-IR Gate with the given name"
  (labels ((make-alias (name morphism)
             (let ((wire (vamp:make-wire :var :x)))
               (multiple-value-bind (results lets) (to-vampir morphism wire nil)
                 (vamp:make-alias :name name
                                  :inputs (list wire)
                                  :body (reverse (cons results lets)))))))
    (multiple-value-bind (morphism map) (ext:common-sub-expressions morphism)
      (append (mapcar
               (lambda (x)
                 (let ((term (car x))
                       (name (cdr x)))
                   (make-alias name term)))
               (fset:convert 'list map))
              (list (make-alias name morphism))))))

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
(defmethod to-vampir ((obj <poly>) value let-vars)
  (declare (ignore value let-vars))
  (subclass-responsibility obj))

(-> direct-fields-to-list-vampir (geb.mixins:direct-pointwise-mixin) list)
(defun direct-fields-to-list (obj)
  (mapcar #'cdr (geb.mixins:to-pointwise-list obj)))

;; all of this is likely wrong, as we are taking morph-isms which
;; evaluate to themselves but I'm unsure of how this works on an input
;; level

(defmethod to-vampir ((obj integer) value let-vars)
  "Numbers act like a constant function, ignoring input"
  (declare (ignore value))
  (values
   (vamp:make-constant :const obj)
   let-vars))

(defmethod to-vampir ((obj ident) value let-vars)
  "Identity acts as the identity function"
  (values value let-vars))

(defun infix-creation (symbol obj value let-vars)
  (mvlet* ((lhs let-vars (to-vampir (mcar obj)  value let-vars))
           (rhs let-vars (to-vampir (mcadr obj) value let-vars)))
    (values (vamp:make-infix :op symbol :lhs lhs :rhs rhs)
            let-vars)))

(defun infix (op lhs rhs)
  (vamp:make-infix :op op :lhs lhs :rhs rhs))

(defmethod to-vampir ((obj +) value let-vars)
  "Propagates the value and adds them"
  (infix-creation :+ obj value let-vars))

(defmethod to-vampir ((obj *) value let-vars)
  "Propagates the value and times them"
  (infix-creation :* obj value let-vars))

(defmethod to-vampir ((obj -) value let-vars)
  "Propagates the value and subtracts them"
  (infix-creation :- obj value let-vars))

(defmethod to-vampir ((obj /) value let-vars)
  ;; this should error
  (infix-creation :/ obj value let-vars))

(defmethod to-vampir ((obj compose) value let-vars)
  (mvlet* ((fst let-vars (to-vampir (mcadr obj) value let-vars))
           (fst-wire (vamp:make-wire :var (gensym "C")))
           (fst-var  (vamp:make-bind :names (list fst-wire) :value fst)))
    (to-vampir (mcar obj) fst-wire (cons fst-var let-vars))))

(defmethod to-vampir ((obj if-zero) value let-vars)
  "The PREDICATE that comes in must be 1 or 0 for the formula to work out."
  ;; need to optimize this, we are computing predicate twice which is
  ;; very bad
  (multiple-value-bind (predicate then else) obj
    (mvlet* ((predicate let-vars (to-vampir predicate value let-vars))
             (then      let-vars (to-vampir then value let-vars))
             (else      let-vars (to-vampir else value let-vars)))
      ;; bool × then + (1 - bool) × else
      (let* ((pred      (vamp:make-wire :var (gensym "ZP")))
             (pred-bind (vamp:make-bind :names (list pred)
                                        :value predicate)))
        (values
         (infix :+
                (infix :* pred then)
                (infix :*
                       (infix :- (vamp:make-constant :const 1) pred)
                       else))
         (cons pred-bind let-vars))))))

(defmethod to-vampir ((obj mod) value let-vars)
  (mvlet* ((car  let-vars (to-vampir (mcar obj)  value let-vars))
           (cadr let-vars (to-vampir (mcadr obj) value let-vars)))
    (values (geb.vampir:mod32 car cadr)
            let-vars)))

(defmethod to-vampir ((obj if-lt) value let-vars)
  (mvlet* ((car  let-vars (to-vampir (mcar obj)  value let-vars))
           (cadr let-vars (to-vampir (mcadr obj) value let-vars))
           (then let-vars (to-vampir (then obj)  value let-vars))
           (else let-vars (to-vampir (else obj)  value let-vars)))
    (values (geb.vampir:pwless32 car cadr then else)
            let-vars)))

(defmethod to-vampir ((obj geb.extension.spec:common-sub-expression) value let-vars)
  (if (typep (obj obj) 'ident)
      (to-vampir (obj obj) value let-vars)
      ;; functions are only 1 argument big ☹
      (values (vamp:make-application :func (name obj)
                                     :arguments (list value))
              let-vars)))
