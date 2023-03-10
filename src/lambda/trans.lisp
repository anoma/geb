(in-package :geb.lambda.trans)

(named-readtables:in-readtable :fare-quasiquote)

(deftype stlc-context () `list)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Main Transformers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgeneric compile-checked-term (context term)
  (:documentation "Compiles a checked term into SubstMorph category"))

(-> to-poly (list <stlc>) (or geb.poly:<poly> geb.poly:poly))
(defun to-poly (context obj)
  (assure (or geb.poly:<poly> geb.poly:poly)
    (~>> obj
         (compile-checked-term context)
         geb:to-poly)))

(-> to-circuit (list <stlc> keyword) geb.vampir.spec:statement)
(defun to-circuit (context obj name)
  (assure geb.vampir.spec:statement
    (~> (to-poly context obj)
        (geb.poly:to-circuit name))))

(defmethod empty ((class (eql (find-class 'list)))) nil)

(defmethod compile-checked-term (context (tterm <stlc>))
  (if (well-defp context tterm)
      (assure <substmorph>
        (match-of stlc tterm
          ((absurd tcod term)
           (comp (init tcod)
                 (compile-checked-term context term)))
          (unit
           (terminal (stlc-ctx-to-mu context)))
          ((left term)
           (comp (->left (mcar (inf-pass context tterm)) (mcadr (inf-pass context tterm)))
                 (compile-checked-term context term)))
          ((right term)
           (comp (->right (mcar (inf-pass context tterm)) (mcadr (inf-pass context tterm)))
                 (compile-checked-term context term)))
          ((case-on on ltm rtm)
           (comp (mcase (curry (compile-checked-term (cons (mcar (inf-pass context on)) context)
                                                     ltm))
                        (curry (compile-checked-term (cons (mcadr (inf-pass context on)) context)
                                                     rtm)))
                 (compile-checked-term context on)))
          ((pair ltm rtm)
           (geb:pair (compile-checked-term context ltm)
                     (compile-checked-term context rtm)))
          ((fst term)
           (comp (<-left (mcar (inf-pass context term)) (mcadr (inf-pass context term)))
                 (compile-checked-term context term)))
          ((snd term)
           (comp (<-right (mcar (inf-pass context term)) (mcadr (inf-pass context term)))
                 (compile-checked-term context term)))
          ((lamb tdom term)
           (curry (commutes-left
                   (compile-checked-term (cons tdom context) term))))
          ((app fun term)
           (comp
            (so-eval (type-of2 (mcar (type-of1 context fun)))
                     (type-of2 (mcadr (type-of1 context fun))))
            (geb:pair (compile-checked-term context
                                            fun)
                      (compile-checked-term context
                                            term))))
          ((index pos)
           (stlc-ctx-proj context pos))))
      (error "not a well-defined term in said context")))

(-> stlc-ctx-to-mu (stlc-context) substobj)
(defun stlc-ctx-to-mu (context)
  "Converts a generic [<STLC>][type] context into a [SUBSTMORPH][type]"
  (mvfoldr #'prod context so1))

(-> so-hom (substobj substobj) (or t substobj))
(defun so-hom (dom cod)
  "Computes the hom-object of two [SUBSTMORPH]s"
  (geb:so-hom-obj dom cod))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Utility Functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun stlc-ctx-proj (context depth)
  (if (zerop depth)
      (<-left (car context)
              (stlc-ctx-to-mu (cdr context)))
      (comp (stlc-ctx-proj (cdr context) (1- depth))
            (<-right (car context)
                     (stlc-ctx-to-mu (cdr context))))))

(defun index-to-projection (depth typ-a typ-b prod)
  (if (zerop depth)
      (comp (<-left typ-a typ-b) prod)
      (comp (index-to-projection (1- depth) (mcar typ-b) (mcadr typ-b) prod)
            (<-right typ-a typ-b))))

(-> index-to-obj (fixnum t) t)
(defun index-to-obj (depth typ)
  (if (zerop depth)
      (mcar typ)
      (index-to-obj (1- depth) (mcadr typ))))

(-> call-objmap (functor t) t)
(defun call-objmap (functor-body arg)
  (funcall (obj functor-body) arg))

(-> call-morphmap (functor t t t) t)
(defun call-morphmap (functor-body typ-a typ-b arg)
  (funcall (func functor-body) typ-a typ-b arg))
