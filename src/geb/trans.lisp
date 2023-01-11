;; Transition or Translation functions about geb

(in-package :geb)

(defgeneric to-poly (morphism)
  (:documentation "Turns a @GEB-SUBSTMORPH into a POLY:POLY"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Morph to Poly Implementation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This maintains exhaustion while leaving it open to extension. you
;; can subclass <substmorph>, without having to update the exhaustion
;; set, however you'll need to properly implement the interface
;; methods on it.

;; Hopefully I can form a complete list somewhere, so one can see the
;; interface functions intended.

;; We could have also derived this from methods, these are equivalent,
;; so both styles are acceptable
(defmethod to-poly ((obj <substmorph>))
  (typecase-of substmorph obj
    (alias        (error "impossible"))
    (substobj     (error "impossible"))
    (init          0)
    (terminal      0)
    (inject-left   poly:ident)
    (inject-right  (poly:+ (obj-to-nat (mcar obj)) poly:ident))
    (comp          (poly:compose (to-poly (mcar obj))
                                 (to-poly (mcadr obj))))
    (project-right (let ((nat (obj-to-nat (mcadr obj))))
                     (if (zerop nat)
                         nat
                         (poly:mod poly:ident nat))))
    (project-left  (let ((nat (obj-to-nat (mcar obj))))
                     (if (zerop nat)
                         nat
                         (poly:/ poly:ident nat))))
    (distribute    (let ((cx (obj-to-nat (mcar obj)))
                         (cy (obj-to-nat (mcadr obj)))
                         (cz (obj-to-nat (mcaddr obj))))
                     (if (and (zerop cy) (zerop cz))
                         0
                         (let* ((yz   (poly:+ cy cz))
                                (xin  (poly:/ poly:ident yz))
                                (yzin (poly:mod poly:ident yz)))
                           (poly:if-lt yzin cy
                                       (poly:+ (poly:* cy xin) yzin)
                                       (poly:+ (poly:* cz xin)
                                               (poly:- yzin cy)
                                               (poly:* cx cy)))))))
    (pair          (let* ((z  (codom (mcdr obj)))
                          (cz (obj-to-nat z)))
                     (poly:* cz (poly:+ (to-poly (mcar obj))
                                        (to-poly (mcdr obj))))))
    (case          (let* ((f      (mcar obj))
                          (x      (dom f))
                          (cx     (obj-to-nat x))
                          (poly-g (to-poly (mcadr obj))))
                     (if (zerop cx)
                         poly-g
                         (poly:if-lt poly:ident cx
                                     (to-poly f)
                                     (poly:compose poly-g
                                                   (poly:- poly:ident cx))))))
    (otherwise (subclass-responsibility obj))))

;; put here just to avoid confusion
(defmethod to-poly ((obj alias))
  (to-poly (obj obj)))

(defmethod to-poly ((obj <substobj>))
  (declare (ignore obj))
  poly:ident)

(defun obj-to-nat (obj)
  (so-card-alg obj))
