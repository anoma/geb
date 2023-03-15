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

;; Problem: this covers only canonical costructors, might need to
;; further extend the definition

(defun hom-cod (ctx f)
  (let ((rec  (ann-term1 ctx f)))
   (cond ((typep f 'fst)     (let ((tt (term f)))
                               (if (typep tt 'pair)
                                   (hom-cod ctx (ltm tt))
                                   (hom-cod ctx tt))))
         ((typep f 'snd)     (let ((tt (term f)))
                               (if (typep tt 'pair)
                                   (hom-cod ctx (rtm tt))
                                   (hom-cod ctx tt))))
         ((typep f 'case-on) (hom-cod
                              (cons (mcar (ttype (ann-term1 ctx (on f))))
                                    ctx)
                              (ltm f)))
         ((typep f 'absurd)  (hom-cod ctx (term f)))
         ((typep f 'lamb)    (mcadr (ttype rec)))
         ((typep f 'app)     (hom-cod ctx (fun f)))
         ((typep f 'index)   (mcadr (ttype rec)))
         (t                  (error "not a valid STLC exponential term")))))

(-> index-check (fixnum list) cat-obj)
(defun index-check (i ctx)
  (let ((l (length ctx)))
    (if (< i l)
        (nth (- l (+ i 1)) ctx)
        (error "argument exceeds length of context"))))

;; Types all terms inside a given lambda term with respect to a context
;; with the caveat of producing a stand-in of the exponential object

;; We assume that the compiler receives all the info using the exp-aux
;; class instead of the usual hom-obj for the well-defp predicate

(defmethod ann-term1 (ctx (tterm <stlc>))
  ;; cahce check
  (if (ttype tterm)
      tterm
      (match-of stlc tterm
        ((absurd tcod term) (absurd tcod (ann-term1 ctx term) :ttype tcod))
        (unit               (unit :ttype so1))
        ((left rty term)    (let ((lant (ann-term1 ctx term)))
                              (left rty
                                    lant
                                    :ttype (coprod (ttype lant) rty))))
        ((right lty term)   (let ((rant (ann-term1 ctx term)))
                              (right lty
                                     rant
                                     :ttype (coprod lty (ttype rant)))))
        ((pair ltm rtm)     (let ((lant (ann-term1 ctx ltm))
                                  (rant (ann-term1 ctx rtm)))
                              (pair lant
                                    rant
                                    :ttype (prod (ttype lant) (ttype rant)))))
        ((fst term)         (let* ((ann-term     (ann-term1 ctx term))
                                   (type-of-term (ttype (ann-term1 ctx term))))
                              (if (typep type-of-term 'prod)
                                  (fst ann-term
                                       :ttype (mcar type-of-term))
                                  (error "type of term not of product type"))))
        ((snd term)          (let* ((ann-term     (ann-term1 ctx term))
                                    (type-of-term (ttype ann-term)))
                               (if (typep type-of-term 'prod)
                                   (snd ann-term :ttype (mcadr type-of-term))
                                   (error "type of term not of product type"))))
        ((lamb tdom term)   (let ((ant (ann-term1 (cons tdom ctx) term)))
                              (lamb tdom
                                    ant
                                    :ttype (fun-type tdom (ttype ant)))))
        ((app fun term)     (app (ann-term1 ctx fun)
                                 (ann-term1 ctx term)
                                 :ttype (hom-cod ctx fun)))
        ((index pos)        (index pos
                                   :ttype (index-check pos ctx)))
        ((case-on on ltm rtm)
         (let* ((ann-on     (ann-term1 ctx on))
                (type-of-on (ttype ann-on))
                (ann-left   (ann-term1 (cons (mcar type-of-on) ctx) ltm))
                (ann-right  (ann-term1 (cons (mcadr type-of-on) ctx) rtm)))
           (if (typep type-of-on 'coprod)
               (case-on ann-on ann-left ann-right :ttype (ttype ann-left))
               (error "type of on not of coproduct type")))))))

;; Changes the stand in Geb term with exponential stand-ins
;; to one containing actual hom-objects

(defun exp-to-hom (t1)
    (cond ((typep t1 'prod)     (prod (exp-to-hom (mcar t1))
                                      (exp-to-hom (mcadr t1))))
          ((typep t1 'coprod)   (coprod (exp-to-hom (mcar t1))
                                        (exp-to-hom (mcadr t1))))
          ((typep t1 'fun-type) (so-hom-obj (exp-to-hom (mcar t1))
                                            (exp-to-hom (mcadr t1))))
          (t                    t1)))

;; Changes all annotated terms' types to actual Geb objects

(defun ann-term2 (tterm)
  (match-of stlc tterm
    ((absurd tcod term)    (absurd (fun-to-hom tcod)
                                   (ann-term2 term)
                                   :ttype (exp-to-hom (ttype tterm))))
    (unit                   tterm)
    ((right lty term)       (right (exp-to-hom lty)
                                  (ann-term2 term)
                                  :ttype (exp-to-hom (ttype tterm))))
    ((left rty term)        (left (exp-to-hom rty)
                                 (ann-term2 term)
                                 :ttype (exp-to-hom (ttype tterm))))
    ((case-on on ltm rtm)  (case-on (ann-term2 on)
                                    (ann-term2 ltm)
                                    (ann-term2 rtm)
                                    :ttype (exp-to-hom (ttype tterm))))
    ((pair ltm rtm)        (pair (ann-term2 ltm)
                                 (ann-term2 rtm)
                                 :ttype (exp-to-hom (ttype tterm))))
    ((fst term)            (fst (ann-term2 term)
                                :ttype (exp-to-hom (ttype tterm))))
    ((snd term)            (snd (ann-term2 term)
                                :ttype (exp-to-hom (ttype tterm))))
    ((lamb tdom term)      (lamb (exp-to-hom tdom)
                                 (ann-term2 term)
                                 :ttype (exp-to-hom (ttype tterm))))
    ((app fun term)        (app (ann-term2 fun)
                                (ann-term2 term)
                                :ttype (exp-to-hom (ttype tterm))))
    ((index pos)           (index pos
                                  :ttype (exp-to-hom (ttype tterm))))))

(defun annotated-term (ctx term)
  (ann-term2 (ann-term1 ctx term)))


;; Produces a type of a lambda term in a context
;; with a stand-in for the exponential object

(defun type-of-exp-aux (ctx tterm)
  (ttype (ann-term1 ctx tterm)))

;; Actual type info

(defun type-of-term (ctx tterm)
  (exp-to-hom (type-of-exp-aux ctx tterm)))

;;Predicate checking that a term in a given context is well-typed

(defmethod well-defp (ctx (tterm <stlc>))
  (match-of stlc tterm
    ((absurd)                 (and (well-defp       ctx (term tterm))
                                   (geb.mixins:obj-equalp (type-of-exp-aux ctx (term tterm))
                                                          so0)))
    (unit                     t)
    ((left)                   (and (well-defp       ctx (term tterm))
                                   (geb.mixins:obj-equalp (mcar (type-of-exp-aux ctx tterm))
                                                          (type-of-exp-aux ctx (term tterm)))))
    ((right)                  (and (well-defp       ctx (term tterm))
                                   (geb.mixins:obj-equalp (mcadr (type-of-exp-aux ctx tterm))
                                                          (type-of-exp-aux ctx (term tterm)))))
    ((case-on on ltm rtm)     (let ((mcartoon (cons  (mcar (type-of-exp-aux ctx on)) ctx))
                                    (mcadrtoon (cons  (mcadr (type-of-exp-aux ctx on)) ctx)))
                                (and (well-defp mcartoon
                                                ltm)
                                     (well-defp mcadrtoon
                                                rtm)
                                     (well-defp ctx on)
                                     (geb.mixins:obj-equalp (type-of-exp-aux mcartoon ltm)
                                                            (type-of-exp-aux mcadrtoon rtm)))))
    ((pair ltm rtm)           (let ((ttot (type-of-exp-aux ctx tterm)))
                                (and (well-defp ctx ltm)
                                     (well-defp ctx rtm)
                                     (geb.mixins:obj-equalp (mcar ttot)
                                                            (type-of-exp-aux ctx ltm))
                                     (geb.mixins:obj-equalp (mcadr ttot)
                                                            (type-of-exp-aux ctx rtm)))))
    ((fst)                    (and (well-defp       ctx (term tterm))
                                   (geb.mixins:obj-equalp (type-of-exp-aux ctx tterm)
                                                          (mcar (type-of-exp-aux ctx (term tterm))))))
    ((snd)                    (and (well-defp       ctx (term tterm))
                                   (geb.mixins:obj-equalp (type-of-exp-aux ctx tterm)
                                                          (mcadr (type-of-exp-aux ctx (term tterm))))))
    ((lamb tdom term)         (let ((ttot (type-of-exp-aux ctx tterm)))
                                (and (well-defp (cons tdom ctx) term)
                                     (geb.mixins:obj-equalp (mcar ttot)
                                                            tdom)
                                     (geb.mixins:obj-equalp (mcadr ttot)
                                                            (type-of-exp-aux (cons tdom ctx) term)))))
    ((app fun)                (let ((tofun  (type-of-exp-aux ctx fun)))
                                (and (well-defp ctx fun)
                                     (well-defp       ctx (term tterm))
                                     (geb.mixins:obj-equalp (type-of-exp-aux ctx (term tterm))
                                                            (mcar tofun))
                                     (geb.mixins:obj-equalp (type-of-exp-aux ctx tterm)
                                                            (mcadr tofun)))))
    ((index pos)              (< pos (length ctx)))))
