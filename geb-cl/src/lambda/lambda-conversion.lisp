(in-package :geb.lambda-conversion)

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
