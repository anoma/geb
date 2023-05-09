;; Transition or Translation functions about geb

(in-package :geb.trans)

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
                         ;; we want to bitshift it by the size
                         (poly:/
                          (poly:- poly:ident
                                  ;; we need to remove the right value
                                  ;; we are doing project-right
                                  (to-poly (<-right (mcar obj) (mcadr obj))))
                          nat))))
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
                     (poly:+ (poly:* cz (to-poly (mcar obj)))
                             (to-poly (mcdr obj)))))
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
(defmethod to-poly ((obj <substobj>))
  (declare (ignore obj))
  poly:ident)

(defun obj-to-nat (obj)
  (so-card-alg obj))

(defmethod to-circuit ((obj <substmorph>) name)
  "Turns a @GEB-SUBSTMORPH to a Vamp-IR Term"
  (to-circuit (to-bitc obj) name))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Morph to Bitc Implementation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmethod bitwidth ((obj <substobj>))
  (typecase-of substobj obj
    (so0     0)
    (so1     0)
    (coprod  (+ 1 (max (bitwidth (mcar obj)) (bitwidth (mcadr obj)))))
    (prod    (+ (bitwidth (mcar obj)) (bitwidth (mcadr obj))))
    (otherwise (subclass-responsibility obj))))

(defmethod to-bitc ((obj <substmorph>))
  (typecase-of substmorph obj
    (substobj
     (bitc:ident (bitwidth obj)))
    (comp
     (bitc:compose (to-bitc (mcar obj))
                   (to-bitc (mcadr obj))))
    ;; This should never occure, but if it does, it produces a
    ;; constant morphism onto an all 0s list
    (init
     (let* ((list (zero-list (bitwidth (mcar obj))))
            (len  (length list)))
       (cond ((= 0 len) (bitc:drop 0))
             ((= 1 len) bitc:zero)
             (t         (apply #'bitc:parallel list)))))
    ;; Terminal maps any bit-list onto the empty bit-list
    (terminal
     (bitc:drop (bitwidth (mcar obj))))

    ;; Inject-left x -> x + y tags the x with a 0, indicating left,
    ;;   and pads the encoded x with as many zeros as would be needed
    ;;   to store either an x or a y.
    (inject-left
     (let ((car-width  (bitwidth (mcar obj)))
           (cadr-width (bitwidth (mcadr obj))))
       (apply #'bitc:parallel
              (append (list bitc:zero (bitc:ident car-width))
                      (zero-list (padding-bits cadr-width
                                               car-width))))))
    ;; Inject-right y -> x + y tags the y with a 1, indicating right,
    ;;   and pads the encoded y with as many zeros as would be needed
    ;;   to store either an x or a y.
    (inject-right
     (let ((car-width  (bitwidth (mcar obj)))
           (cadr-width (bitwidth (mcadr obj))))
       (apply #'bitc:parallel
              (append (list bitc:one (bitc:ident cadr-width))
                      (zero-list (padding-bits car-width
                                               cadr-width))))))

    ;; Case translates directly into a branch. The sub-morphisms of
    ;; case are padded with drop so they have the same input lengths.
    (case
      (let ((car-width  (bitwidth (dom (mcar obj))))
            (cadr-width (bitwidth (dom (mcadr obj)))))
        (bitc:branch (bitc:parallel (to-bitc (mcar obj))
                                    (bitc:drop
                                     (padding-bits cadr-width car-width)))
                     (bitc:parallel (to-bitc (mcadr obj))
                                    (bitc:drop
                                     (padding-bits car-width cadr-width))))))
    ;; project-left just drops any bits not being used to encode the
    ;; first component.
    (project-left
     (bitc:parallel (bitc:ident (bitwidth (mcar obj)))
                    (bitc:drop (bitwidth (mcadr obj)))))

    ;; project-right just drops any bits not being used to encode the
    ;; second component.
    (project-right
     (bitc:parallel (bitc:drop (bitwidth (mcar obj)))
                    (bitc:ident (bitwidth (mcadr obj)))))

    ;; Pair will copy the input and run the encoded morphisms in pair
    ;; on the two copied subvetors.
    (pair
     (bitc:compose (bitc:parallel (to-bitc (mcar obj)) (to-bitc (mcdr obj)))
                   (bitc:fork (bitwidth (dom (mcar obj))))))
    ;; a * (b + c) will be encoded as [a] [0 or 1] [b or c]. By
    ;; swapping the [0 or 1] with [a], we get an encoding for (a * b)
    ;; + (a * c).
    (distribute
     (bitc:parallel (bitc:swap (bitwidth (mcar obj)) 1)
                    (bitc:ident (max (bitwidth (mcadr obj))
                                     (bitwidth (mcaddr obj))))))
    (otherwise (subclass-responsibility obj))))

(defun zero-list (length)
  (make-list length :initial-element bitc:zero))

(-> padding-bits ((integer 0) (integer 0)) (integer 0))
(defun padding-bits (number number2)
  "
```lisp
(max number number2)
```
is the bits needed to store NUMBER or NUMBER2

Thus if we want to calculate the number of padding bits needed then we
should calculate

```lisp
(- (max number number2) number2)
```

We use an optimized version in actual code, which happens to compute the same result"
  (max (- number number2) 0))
