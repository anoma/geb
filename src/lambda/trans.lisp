(in-package :geb.lambda.trans)

(named-readtables:in-readtable :fare-quasiquote)

(deftype stlc-context () `list)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Main Transformers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgeneric compile-checked-term (context type term)
  (:documentation "Compiles a checked term into SubstMorph category"))

(-> to-poly (list t <stlc>) (or geb.poly:<poly> geb.poly:poly))
(defun to-poly (context type obj)
  (assure (or geb.poly:<poly> geb.poly:poly)
    (~>> obj
         (compile-checked-term context type)
         geb:to-poly)))

(-> to-circuit (list t <stlc> keyword) geb.vampir.spec:statement)
(defun to-circuit (context type obj name)
  (assure geb.vampir.spec:statement
    (~> (to-poly context type obj)
        (geb.poly:to-circuit name))))

(defmethod empty ((class (eql (find-class 'list)))) nil)

(defmethod compile-checked-term (context type (term <stlc>))
  (assure <substmorph>
    (match-of stlc term
      ((absurd type v)
       (comp (init type)
             (compile-checked-term context so0 v)))
      (unit
       (terminal (stlc-ctx-to-mu context)))
      ((left lty rty term)
       (assert (typep type '(or alias coprod)) nil "invalid lambda type to left ~A" type)
       ;; (assert
           ;; (geb.mixins:obj-equalp (coprod lty rty) (class-of type))
           ;; nil "Types should match for left ~A ~A ~A" lty rty type)
       (comp (->left (mcar type) (mcadr type))
             (compile-checked-term context (mcar type) term)))
      ((right lty rty term)
       (assert (typep type '(or alias coprod)) nil "invalid lambda type to right ~A" type)
       ;; (assert
           ;; (geb.mixins:obj-equalp (coprod lty rty) (class-of type))
           ;; nil "Types should match for right ~A ~A ~A" lty rty type)
       (comp (->right (mcar type) (mcadr type))
             (compile-checked-term context (mcar type) term)))
      ((case-on lty rty cod on l r)
       (comp (mcase (curry (compile-checked-term (cons lty context) cod l))
                    (curry (compile-checked-term (cons rty context) cod r)))
             (compile-checked-term context (coprod lty rty) on)))
      ;; I would make an alias, but people would need a newer version of sbcl
      ((geb.lambda.spec:pair lty rty l r)
       (pair (compile-checked-term context lty l)
             (compile-checked-term context rty r)))
      ((fst lty rty value)
       (assert (geb.mixins:obj-equalp (class-of lty) (class-of type)) nil "Types should match on fst: ~A ~A"
               term type)
       (comp (<-left lty rty) (compile-checked-term context (prod lty rty) value)))
      ((snd lty rty value)
       (assert (geb.mixins:obj-equalp (class-of rty) (class-of type)) nil "Types should match on fst: ~A ~A"
               term type)
       (comp (<-right lty rty) (compile-checked-term context (prod lty rty) value)))
      ((lamb vty tty term)
       (curry (commutes-left
               (compile-checked-term (cons vty context) tty term))))
      ((app dom com f x)
       (assert (geb.mixins:obj-equalp dom type) nil "Types should match for application: ~A ~A" dom type)
       (comp
        (so-eval dom com)
        (pair (compile-checked-term context dom f)
              (compile-checked-term context com x))))
      ((index i)
       (stlc-ctx-proj context i)))))

(-> stlc-ctx-to-mu (stlc-context) substobj)
(defun stlc-ctx-to-mu (context)
  "Converts a generic [<STLC>][type] context into a [SUBSTMORPH][type]"
  (mvfoldr #'prod context so1))

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
