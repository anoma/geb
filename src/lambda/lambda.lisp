(in-package #:geb.lambda.main)

(defclass fun-type (geb.mixins:direct-pointwise-mixin geb.mixins:cat-obj)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :documentation "")))

(defun fun-type (mcar mcadr)
  (make-instance 'fun-type :mcar mcar :mcadr mcadr))

;; Below we list all possible ways of getting a term of the exponential,
;; namely: projections, casing, absurd, lambda-abstraction and application

;; Problem: this covers only canonical costructors. E.g. calling on
;; (app (fst (pair (lamb so1 (unit)) (unit))) (unit))

(defun hom-cod (ctx f)
  (cond ((typep f 'fst)     (if (typep (term f) 'pair)
                                (hom-cod ctx (ltm (term f)))
                                (hom-cod ctx (term f))))
        ((typep f 'snd)     (if (typep (term f) 'pair)
                                (hom-cod ctx (rtm (term f)))
                                (hom-cod ctx (term f))))
        ((typep f 'case-on) (hom-cod
                             (cons (mcar (type-of1 ctx (on f))) ctx)
                                          (ltm f)))
        ((typep f 'absurd)  (hom-cod ctx (term f)))
        ((typep f 'lamb)    (mcadr (type-of1 ctx f)))
        ((typep f 'app)     (hom-cod ctx (fun f)))
        ((typep f 'index)   (mcadr (type-of1 ctx f)))
        (t                  (error "not a valid STLC exponential term"))))

(-> index-check (fixnum list) cat-obj)
(defun index-check (i ctx)
  (let ((l (length ctx)))
    (if (< i l)
        (nth (- l (+ i 1)) ctx)
        (error "argument exceeds length of context"))))

      ;; Gives type of a given lambda term with the caveat of producing a stand-in of the exponential object

(defmethod type-of1 (ctx (tterm <stlc>))
  (match-of stlc tterm
    ((absurd tcod)       tcod)
    (unit                so1)
    ((left rty term)     (coprod (type-of1 ctx term) rty))
    ((right lty term)    (coprod lty (type-of1 ctx term)))
    ((case-on on ltm)       (if (typep (type-of1 ctx on) 'coprod)
                             (type-of1 (cons  (mcar (type-of1 ctx on)) ctx) ltm)
                             (error "type of on not of coproduct type")))
    ((pair ltm rtm)      (prod (type-of1 ctx ltm) (type-of1 ctx rtm)))
    ((fst term)          (if (typep (type-of1 ctx term) 'prod)
                             (mcar (type-of1 ctx term))
                             (error "type of term not of product type")))
    ((snd term)          (if (typep (type-of1 ctx term) 'prod)
                             (mcadr (type-of1 ctx term))
                             (error "type of term not of product type")))
    ((lamb tdom term)    (fun-type tdom
                                   (type-of1 (cons tdom ctx) term)))
    ((app fun)           (hom-cod ctx fun))
    ((index pos)         (index-check pos ctx))))

;; Changes exp-aux to so-hom-obj

(defun type-of2 (t1)
    (cond ((typep t1 'prod)     (prod (type-of2 (mcar t1))
                                      (type-of2 (mcadr t1))))
          ((typep t1 'coprod)   (coprod (type-of2 (mcar t1))
                                        (type-of2 (mcadr t1))))
          ((typep t1 'fun-type) (so-hom-obj (type-of2 (mcar t1))
                                            (type-of2 (mcadr t1))))
          (t                    t1)))

(defun inf-pass (context term)
  (type-of2 (type-of1 context term)))

;; Annotated type-inferencer. Types are accessible through ttype function

;;Problem with equalp here, does not recognize same types, e.g. in pair case after projecting

(defmethod well-defp (ctx (tterm <stlc>))
  (match-of stlc tterm
    ((absurd term)       (and (well-defp ctx term)
                                   (geb.mixins:obj-equalp (type-of1 ctx term) so0)))
    (unit                     t)
    ((left term)          (and (well-defp ctx term)
                                   (geb.mixins:obj-equalp (mcar
                                            (type-of1 ctx tterm))
                                           (type-of1 ctx term))))
    ((right term)         (and (well-defp ctx term)
                                   (geb.mixins:obj-equalp (mcadr
                                            (type-of1 ctx tterm))
                                           (type-of1 ctx term))))
    ((case-on on ltm rtm)  (and (well-defp (cons  (mcar (type-of1 ctx on)) ctx)
                                           ltm)
                                (well-defp (cons  (mcadr (type-of1 ctx on)) ctx)
                                           rtm)
                                (well-defp ctx on)))
    ((pair ltm rtm)        (and (well-defp ctx ltm)
                                (well-defp ctx rtm)
                                (geb.mixins:obj-equalp (mcar (type-of1 ctx tterm))
                                        (type-of1 ctx ltm))
                                (geb.mixins:obj-equalp (mcadr (type-of1 ctx tterm))
                                        (type-of1 ctx rtm))))
    ((fst term)               (and (well-defp ctx term)
                                   (geb.mixins:obj-equalp (type-of1 ctx tterm)
                                           (mcar (type-of1 ctx term)))))
    ((snd term)               (and (well-defp ctx term)
                                   (geb.mixins:obj-equalp (type-of1 ctx tterm)
                                           (mcadr (type-of1 ctx term)))))
    ((lamb tdom term)          (and (well-defp (cons tdom ctx) term)
                                    (geb.mixins:obj-equalp (mcar (type-of1 ctx tterm))
                                            tdom)
                                    (geb.mixins:obj-equalp (mcadr (type-of1 ctx tterm))
                                            (type-of1 (cons tdom ctx) term))))
    ((app fun term)           (and (well-defp ctx fun)
                                   (well-defp ctx term)
                                   (geb.mixins:obj-equalp (type-of1 ctx term)
                                           (mcar (type-of1 ctx fun)))
                                   (geb.mixins:obj-equalp (type-of1 ctx tterm)
                                           (mcadr (type-of1 ctx fun)))))
    ((index pos)                (< pos (length ctx)))))
