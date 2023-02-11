(in-package :geb.mixins)

(defclass meta-mixin ()
  ((metadata :initform (tg:make-weak-hash-table :test 'eq :weakness :key)
             :allocation :class
             :accessor meta))
  (:documentation
   "Use my service if you want to have metadata capabilities associated
with the given object. @MIXIN-PERFORMANCE covers my performance
characteristics"))

(-> meta-insert (meta-mixin t t) t)
(defun meta-insert (object key value)
  "Inserts a value into storage. If the key is a one time object, then
the insertion is considered to be volatile, which can be reclaimed
when no more references to the data exists.

If the data is however a constant like a string, then the insertion is
considered to be long lived and will always be accessible"
  (let ((hash (or (gethash object (meta object))
                  (setf (gethash object (meta object))
                        (tg:make-weak-hash-table :test 'equalp
                                                 :weakness :key)))))
    (setf (gethash key hash)
          value)))

(-> meta-lookup (meta-mixin t) t)
(defun meta-lookup (object key)
  "Lookups the requested key in the metadata table of the object"
  (let ((table (gethash object (meta object))))
    (when table
      (gethash key table))))
