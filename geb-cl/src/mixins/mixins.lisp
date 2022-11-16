(in-package :geb.mixins)

(defclass pointwise-mixin () ()
  (:documentation "Provides the service of giving point wise
                   operations to classes"))

(defclass direct-pointwise-mixin (pointwise-mixin) ()
  (:documentation "Works like `POINTWISE-MIXIN`, however functions on
                   `POINTWISE-MIXIN`s will only operate on direct-slots
                   instead of all slots the class may contain.

                   Further all `DIRECT-POINTWISE-MIXIN`'s are `POINTWISE-MIXIN`'s"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; API for Pointwise
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; my way of coping with no meta classes by default
(defgeneric pointwise-slots (obj)
  (:documentation "Works like C2MOP:COMPUTE-SLOTS however on the object
                   rather than the class")
  ;; should we specialize it on pointwise-mixin instead? Should all
  ;; objects be able to give their pointwise slots?
  (:method ((object standard-object))
    (c2mop:compute-slots (class-of object))))

(defgeneric obj-equalp (object1 object2)
  (:documentation "Compares objects with pointwise equality. This is a
                   much weaker form of equality comparison than
                   STANDARD-OBJECT EQUALP, which does the much
                   stronger pointer quality")
  (:method ((obj1 standard-object) (obj2 standard-object))
    "for non pointwise objects, compute the standard equalp"
    (equalp obj1 obj2)))

(defgeneric to-pointwise-list (obj)
  (:documentation "Turns a given object into a pointwise LIST. listing
                   the KEYWORD slot-name next to their value.")
  (:method ((obj pointwise-mixin))
    (mapcar (lambda (x)
              (cons (util:symbol-to-keyword x)
                    (slot-value obj x)))
            (mapcar #'c2mop:slot-definition-name
                    (pointwise-slots obj)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Instances
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmethod pointwise-slots ((object direct-pointwise-mixin))
  "Works like the normal POINTWISE-SLOTS however we only work on
   direct slot values"
  (c2mop:class-direct-slots (class-of object)))

(defmethod obj-equalp ((obj1 pointwise-mixin) (obj2 pointwise-mixin))
  (obj-equalp (to-pointwise-list obj1)
              (to-pointwise-list obj2)))

(defmethod obj-equalp ((obj1 list) (obj2 list))
  (or (eq obj1 obj2)
      (and (consp obj1)
           (consp obj2)
           (obj-equalp (car obj1) (car obj2))
           (obj-equalp (cdr obj1) (cdr obj2)))))

;; I should implement it for arrays as well!
(defmethod obj-equalp ((obj1 t) (obj2 t))
  (equalp obj1 obj2))
