(in-package :geb.poly.trans)

(defgeneric moprh-to-poly (morphism)
  (:documentation "Turns a GEB:SUBSTMORPH into a POLY"))

(defmethod morph-to-poly ((obj geb:<substmorph>))
  (error "Subclass Responsbility for ~A" (class-name (class-of obj))))

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

(defmethod morph-to-poly ((obj geb:case))
  (+ (obj-to-nat (mcar obj)) ident))

(defmethod morph-to-poly ((obj geb:comp))
  (compose (morph-to-poly (mcar obj))
           (morph-to-poly (mcadr obj))))


(defun obj-to-nat (obj)
  obj
  (error "not implemented"))
