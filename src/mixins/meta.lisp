(in-package :geb.mixins)

(defclass meta-mixin ()
  ((metadata :initform (tg:make-weak-hash-table :test 'eq :weakness :key)
             :allocation :class
             :accessor meta))
  (:documentation
   "Use my service if you want to have metadata capabilities associated
with the given object. @MIXIN-PERFORMANCE covers my performance
characteristics"))

(-> meta-insert (meta-mixin t t &key (:weak t)) t)
(defun meta-insert (object key value &key weak)
  "Inserts a value into storage. If the key is a one time object, then
the insertion is considered to be volatile, which can be reclaimed
when no more references to the data exists.

If the data is however a constant like a string, then the insertion is
considered to be long lived and will always be accessible

The :weak keyword specifies if the pointer stored in the value is weak"
  (let ((hash (or (gethash object (meta object))
                  (setf (gethash object (meta object))
                        (tg:make-weak-hash-table :test 'equalp
                                                 :weakness :key)))))
    (setf (gethash key hash)
          (if weak (tg:make-weak-pointer value) value))))

(-> meta-lookup (meta-mixin t) t)
(defun meta-lookup (object key)
  "Lookups the requested key in the metadata table of the object. We
look past weak pointers if they exist"
  (let ((table (gethash object (meta object))))
    (when table
      (let ((value (gethash key table)))
        (if (tg:weak-pointer-p value) (tg:weak-pointer-value value) value)))))

;; We need a custom copy for the meta-object

(defmethod geb.utils:copy-instance ((object meta-mixin) &rest initargs
                                    &key &allow-other-keys)
  (declare (ignorable initargs))
  (let ((new-object (call-next-method))
        (table      (gethash object (meta object))))
    (when table
      (setf (gethash new-object (meta object)) ; should point to the same table
            table))
    new-object))
