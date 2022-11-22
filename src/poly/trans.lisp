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

(defmethod morph-to-poly ((obj geb:comp))
  (compose (morph-to-poly (mcar obj))
           (morph-to-poly (mcadr obj))))

(defmethod morph-to-poly ((obj geb:case))
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
  obj
  (error "not implemented"))
