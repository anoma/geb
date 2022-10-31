(in-package :geb.lambda-conversion)

(named-readtables:in-readtable :fare-quasiquote)

(deftype stlc-context () `list)

(-> stlc-to-ccc (stlc-context t) t)
(defun stlc-to-ccc (context term)
  (match term
    (`(unit)
      (let ((dom (stlc-ctx-to-mu context)))
        (list dom so1 (terminal dom))))
    ;; Left Right Extension
    (`(left ,term ,type-other)
      (match (stlc-to-ccc context term)
        ((list dom cod m)
         (list dom
               (coprod cod type-other)
               (comp (left-> cod type-other) m)))
        (_ nil)))
    (`(right ,type-other ,term)
      (match (stlc-to-ccc context term)
        ((list dom cod m)
         (list dom
               (coprod type-other cod)
               (comp (right-> type-other cod) m)))
        (_ nil)))
    ;; Cons Car and Cdr extension
    (`(pair ,t1 ,t2)
      (match (list (stlc-to-ccc context t1)
                   (stlc-to-ccc context t2))
        ((list (list dom1 cod1 m1)
               (list dom2 cod2 m2))
         ;; TODO :: check that the doms are the same
         dom1
         (list dom2 (prod cod1 cod2) (pair m1 m2)))
        (_ nil)))
    (`(car ,x)
      (match (stlc-to-ccc context x)
        ((list dom (prod codl codr) m) (list dom codl (comp (<-left codl codr) m)))
        (_                             nil)))

    (`(cdr ,x)
      (match (stlc-to-ccc context x)
        ((list dom (prod codl codr) m) (list dom codr (comp (<-right codl codr) m)))
        (_                             nil)))

    ;; variable indexing
    ((index depth)
     (let* ((context-value   (nth depth context))
            (values-to-point (take depth context))
            (prod-context    (stlc-ctx-to-mu context))
            (proj-index      (<-left context-value
                                     (stlc-ctx-to-mu (drop depth context)))))
       (list (stlc-ctx-to-mu context)
             context-value
             (if values-to-point
                 (comp proj-index
                       (mvfold (lambda (term x prod-context-left)
                                 (values
                                  (comp term (<-right x prod-context-left))
                                  (mcadr prod-context-left)))
                               (cdr values-to-point)
                               (<-right (car values-to-point)
                                        prod-context)
                               (mcadr prod-context)))
                 proj-index))))
    (`(lambda ,vty ,term)
      (stlc-to-ccc (cons vty context) term))
    ((cons f x)
     (match (list (stlc-to-ccc context f)
                  (stlc-to-ccc context x))
       ((list (list fdom fcod fm)
              (list xdom xcod xm))
        ;; TODO :: check that the doms are the same
        xcod fdom
        (list xdom fcod (comp fm xm)))
       (_ nil)))))

(-> stlc-ctx-to-mu (stlc-context) substobj)
(defun stlc-ctx-to-mu (context)
  (mvfoldr #'prod context so1))


;; returns a functor
(defun convert-term (term)
  (match term
    (`(lambda ,body)
      (let ((functor-body (convert-term body)))
        (make-functor
         :obj (lambda (a)
                (!-> a (call-objmap functor-body a)))
         ;; functions in geb -> geb
         :func (func functor-body))))
    ((index depth)
     (make-functor
      :obj  (lambda (a)     (index-to-obj depth a))
      :func (lambda (m a b) (index-to-projection depth a b m))))
    ;; application case
    ((cons f x)
     (let ((func (convert-term f))
           (arg  (convert-term x)))
       (make-functor
        :obj (lambda (a)
               (call-objmap func (call-objmap arg a)))
        :func (lambda (a b m)
                (comp (call-morphmap (func func)
                                     (call-objmap func a)
                                     (call-objmap func b)
                                     m)
                      (call-morphmap (func arg)
                                     (call-objmap arg a)
                                     (call-objmap arg b)
                                     m))))))
    (_
     (make-functor
      :obj (lambda (a) a)
      :func (lambda (a b m)
              (declare (ignore a b))
              m)))
    ;; (`(car ,a)
    ;;   (make-functor
    ;;    :obj  (convert-cont a)
    ;;    ;; functions in geb -> geb
    ;;    :func (convert-term a)))
    ;; (`(cdr ,a)
    ;;   (make-functor
    ;;    :obj  (convert-cont a)
    ;;    ;; functions in geb -> geb
    ;;    :func (convert-term a)))
    ;; (`(cons ,a ,b)
    ;;   (make-functor
    ;;    :obj  (convert-cont body)
    ;;    ;; functions in geb -> geb
    ;;    :func (convert-term body)))
    ))


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

(defmethod geb:mcar ((alias alias))
  (mcar (obj alias)))

(defmethod geb:mcadr ((alias alias))
  (mcadr (obj alias)))

(def test-case
  (nameless (curry-lambda `(lambda (x y)
                             (if x y false)))))

(def test-type
  (!-> (prod geb-bool:bool
             (prod geb-bool:bool
                   so1))
       geb-bool:bool))

(call-objmap (convert-term test-case) test-type)


(stlc-to-ccc nil (nameless `(lambda (x ,so1) x)))

(stlc-to-ccc nil (nameless `(lambda (x ,so1) (car (pair x x)))))
