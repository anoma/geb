(in-package :geb.vampir)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Boolean
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *bool*
  (let ((x-wire (make-wire :var :x))
        (one    (make-constant :const 1)))
    (make-alias
     :name   :bool
     :inputs (list :x)
     :body   (list (make-equality
                    :lhs (make-infix :op :*
                                     :lhs x-wire
                                     :rhs (make-infix :lhs x-wire :rhs one :op :-))
                    :rhs (make-constant :const 0))
                   x-wire))))

(defun bool (x)
  (make-application :func :bool :arguments (list x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Next-range definition for an inductive definition of range
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defun int-range31 (a)
  (make-application :func :intrange31
                    :arguments (list a)))

(defun mod32 (a b)
  (make-application :func :mod32
                    :arguments (list a b)))

(defun pwless32 (f g p q)
  (make-application :func :pwless32
                    :arguments (list f g p q)))

(defun less32 (a b)
  (make-application :func :less32
                    :arguments (list a b)))

(defun next-range (range x)
  (make-application :func :next_range
                    :arguments (list range x)))

(defun int-range32 (a)
  (make-application :func :intrange32
                    :arguments (list a)))

(defun negative32 (a)
  (make-application
   :func :negative32
   :arguments (list a)))

(defun non-negative32 (a)
  (make-application :func :nonnegative32
                    :arguments (list a)))

(defun vamp-range (of)
  (labels ((in-plus (n)
             (if (= n 0)
                 (make-wire :var :a0)
                 (make-infix :op :+
                             :lhs (in-plus (- n 1))
                             :rhs (make-infix
                                   :op :*
                                   :lhs (make-constant :const (expt 2 n))
                                   :rhs (make-wire
                                         :var (intern
                                               (format nil "A~a" n) :keyword))))))
           (in-tuple (i)
             (make-wire :var (intern (format nil "A~a" i) :keyword))))
    (make-alias
     :name (intern (format nil "range~A" of) :keyword)
     :inputs (list :a)
     :body
     (append (mapcar
              (lambda (i y)
                (spc:make-bind
                 :names (list (make-wire :var y))
                 :value
                 (bool
                  (make-application
                   :func :fresh
                   :arguments
                   (list
                    (make-infix :op :%
                                :lhs
                                (make-infix :op :\\
                                            :rhs (make-constant :const i)
                                            :lhs (make-wire :var :A))
                                :rhs (make-constant :const 2)))))))
              (mapcar (lambda (x) (expt 2 x))
                      (alexandria:iota of))
              (mapcar (lambda (x) (intern (format nil "A~a" x) :keyword))
                      (alexandria:iota of)))
             (list
              (make-equality :lhs (make-wire :var :a)
                             :rhs (in-plus (1- of )))
              (make-tuples :wires
                           (append (mapcar #'in-tuple (alexandria:iota of))
                                   (list (make-wire :var :|()|)))))))))

(defun range31 (a)
  (make-application
   :func :range31
   :arguments (list a)))

(defun range32 (a)
  (make-application
   :func :range32
   :arguments (list a)))

(defun pwmod32 (f g x)
  (make-application :func :pwmod32
                    :arguments (list f g x)))

(defun negative31 (a)
  (make-application
   :func :negative31
   :arguments (list a)))

(defparameter *base-range*
  (make-alias
   :name :base_range
   :inputs (list (make-constant :const 0))
   :body
   (list (make-wire :var :[]))))

(defparameter *next-range*
  (let ((a-wire (make-wire :var :a)))
    (make-alias
     :name :next_range
     :inputs (list :range :a)
     :body
     (list
      (make-bind
       :names (list (make-wire :var :a0))
       :value (make-application
               :func :bool
               :arguments (list
                           (make-application
                            :func :fresh
                            :arguments
                            (list
                             (make-infix :op :%
                                         :lhs a-wire
                                         :rhs (make-constant :const 2)))))))
      (make-bind :names (list (make-wire :var :a1))
                 :value
                 (make-application :func :fresh
                                   :arguments
                                   (list
                                    (make-infix :op :\\
                                                :lhs a-wire
                                                :rhs (make-constant :const 2)))))
      (make-infix :op :|:|
                      :lhs (make-wire :var :a0)
                      :rhs (make-application :func :range
                                             :arguments
                                             (list (make-wire :var :a1))))))))
(defparameter *range-n*
  (make-alias
   :name :range_n
   :inputs (list :n)
   :body
   (list (make-application :func :iter
                           :arguments (list (make-wire :var :n)
                                            (make-wire :var :next_range)
                                            (make-wire :var :base_range))))))

(defun range-n (n a)
  (make-application :func :range_n
                    :arguments (list n
                                     a)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; List operations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *hd*
  (make-alias
   :name :hd
   :inputs (list :|(h:t)|)
   :body
   (list (make-wire :var :h))))

(defparameter *tl*
  (make-alias
   :name :tl
   :inputs (list :|(h:t)|)
   :body
   (list (make-wire :var :t))))

(defun hd (a)
  (make-application :func :hd
                    :arguments (list a)))
(defun tl (a)
  (make-application :func :tl
                    :arguments (list a)))

(defparameter *n-th*
  (make-alias
   :name :n_th
   :inputs (list :lst :n)
   :body
   (list
    (make-application :func :hd
                      :arguments
                      (list (make-application
                             :func :iter
                             :arguments
                             (list (make-wire :var :n)
                                   (make-wire :var :tl)
                                   (make-wire :var :lst))))))))

(defun n-th (lst n)
  (make-application :func :nth
                    :arguments (list lst n)))

(defparameter *negative*
  (let ((num (make-wire :var :n)))
    (make-alias
     :name :negative
     :inputs (list :n :a)
     :body
     (list (make-application
            :func :nth
            :arguments
            (list (range-n
                   (make-infix :op :+
                               :lhs num
                               :rhs (make-constant :const 1))
                   (make-infix :op :+
                               :lhs (make-wire :var :a)
                               :rhs
                               (make-infix :op :^
                                           :lhs (make-constant :const 2)
                                           :rhs num)))
                  num))))))

(defun negative (n a)
  (make-application :func :negative
                    :arguments (list n a)))

(defparameter *nonnegative*
  (make-alias
   :name :nonnegative
   :inputs (list :n :a)
   :body
   (list (make-infix :op :-
                     :lhs  (make-constant :const 1)
                     :rhs (make-application
                           :func :negative
                           :arguments (list (make-constant :const :n)
                                            (make-wire :var :a)))))))

(defun nonnegative (n a)
  (make-application :func :nonnegative
                    :arguments (list n a)))

(defparameter *mod-n*
  (let ((numb   (make-constant :const :n))
        (a-wire (make-wire :var :a))
        (b-wire (make-wire :var :b))
        (q-wire (make-wire :var :q))
        (r-wire (make-wire :var :r)))
    (make-alias :name :mod32
                :inputs (list :n :a :b)
                :body (list
                       (make-equality :lhs (make-application :func :nonnegative
                                                             :arguments (list numb b-wire))
                                      :rhs (make-constant :const 0))
                       (make-bind :names (list q-wire)
                                  :value (make-application
                                          :func :fresh
                                          :arguments (list (make-infix :op :/
                                                                       :lhs a-wire
                                                                       :rhs b-wire))))
                       (make-bind :names (list r-wire)
                                  :value (make-application
                                          :func :fresh
                                          :arguments (list (make-infix :op :%
                                                                       :lhs a-wire
                                                                       :rhs b-wire))))
                       (make-equality :lhs (make-application
                                            :func :nonnegative
                                            :arguments (list numb r-wire))
                                      :rhs (make-constant :const :0))
                       (make-equality :lhs a-wire
                                      :rhs (make-infix
                                            :op :+
                                            :lhs (make-infix :op :*
                                                             :lhs b-wire
                                                             :rhs q-wire)
                                            :rhs q-wire))
                       (make-equality :lhs (make-application :func :negative 
                                                             :arguments (list numb
                                                                              (make-infix :op :-
                                                                                          :lhs r-wire
                                                                                          :rhs b-wire)))
                                      :rhs (make-constant :const 0))
                       r-wire))))

(defun mod-n (n a b)
  (make-application :func :mod-n
                    :arguments (list n a b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Primitive operations with range checks
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *plus-range*
  (let ((plus (make-infix :op :+
                          :lhs (make-wire :var :x1)
                          :rhs (make-wire :var :x2))))
    (make-alias
     :name :plus_range
     :inputs (list :n :x1 :x2)
     :body (list (make-application :func :range_n
                                   :arguments (list (make-wire :var :n)
                                                    plus))
                 plus))))

(defun plus-range (n x1 x2)
  (make-application :func :plus_range
                    :arguments (list n x1 x2)))

(defparameter *mult-range*
  (let ((times (make-infix :op :*
                           :lhs (make-wire :var :x1)
                           :rhs (make-wire :var :x2))))
    (make-alias
     :name :mult_range
     :inputs (list :n :x1 :x2)
     :body (list (make-application :func :mult_range
                                   :arguments (list (make-wire :var :n)
                                                    times))
                 times))))

(defun mult-range (n x1 x2)
  (make-application :func :mult_range
                    :arguments (list n x1 x2)))

(defparameter *minus-range*
  (let ((minus (make-infix :op :-
                           :lhs (make-wire :var :x1)
                           :rhs (make-wire :var :x2))))
    (make-alias
     :name :minus_range
     :inputs (list :n :x1 :x2)
     :body (list (make-equality :lhs (negative (make-wire :var :n)
                                               minus)
                                :rhs (make-constant :const 1))
                 minus))))

(defun minus-range (n x1 x2)
  (make-application :func :minus_range
                    :arguments (list n x1 x2)))

(defparameter *isZero*
  (let ((one (make-constant :const 1))
        (wire-a (make-wire :var :a))
        (wire-ai (make-wire :var :ai))
        (wire-b  (make-wire :var :b)))
    (make-alias
     :name :isZero
     :inputs (list :a)
     :body (list (make-bind :names (list wire-ai)
                            :value (make-application
                                    :func :fresh
                                    :arguments (list (make-infix :op :\|
                                                                 :lhs one
                                                                 :rhs wire-a))))
                 (make-bind :names (list wire-b)
                            :value (make-infix :op :-
                                               :lhs one
                                               :rhs (make-infix :op :*
                                                                :lhs wire-ai
                                                                :rhs wire-a)))
                 (make-equality :lhs (make-infix :op :*
                                                 :lhs wire-a
                                                 :rhs wire-b)
                                :rhs (make-constant :const 0))
                 (make-infix :op :-
                             :lhs one
                             :rhs wire-b)))))

(defun isZero (a)
  (make-application :func :isZero
                    :arguments (list a)))

(-> cons-deconstruct (&rest keyword) list)
(defun cons-deconstruct (&rest symbols)
  (list
   (reduce (lambda (x pattern)
             (make-infix :lhs (make-wire :var x)
                         :rhs pattern
                         :op :|:|))
           (butlast symbols)
           :from-end t
           :initial-value (make-wire :var (car (last symbols))))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Operations on Lists
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *combine-aux*
  (make-alias
   :name :combine-aux
   :inputs (list :x :y)
   :body (list (make-infix :op :+
                           :lhs (make-wire :var :x)
                           :rhs (make-infix :op :*
                                            :lhs (make-constant :const 2)
                                            :rhs (make-wire :var :y))))))

(defparameter *combine*
  (make-alias
   :name :combine
   :inputs (list :xs)
   :body (list (make-application :func :fold
                                 :arguments (list (make-wire :var :xs)
                                                  (make-wire :var :combine_aux)
                                                  (make-constant :const 0))))))

(defun combine (xs)
  (make-application :func :combine
                    :arguments (list xs)))

(defparameter *take-base*
  (make-alias
   :name :take_base
   :inputs (list :lst)
   :body (list (make-brackets))))

(defparameter *take-ind*
  (make-alias
   :name :take_ind
   :inputs (list :take (cons-deconstruct :h :t))
   :body (list (make-infix :lhs (make-wire :var :h)
                           :rhs (make-application
                                 :func :take
                                 :arguments (list (make-wire :var t)))
                           :op :|:|))))

(defparameter *take*
  (make-alias
   :name :take
   :inputs (list :n)
   :body (list (make-application :func :iter
                                 :arguments (list (make-wire :var :n)
                                                  (make-wire :var :take_ind)
                                                  (make-wire :var :take_base))))))

(defparameter *drop-ith-rec*
  (make-alias
   :name :drop_ith_rec
   :inputs (list (cons-deconstruct :h :t))
   :body (list (make-infix :lhs (make-wire :var :h)
                           :rhs (make-application
                                 :func :take
                                 :arguments (list (make-wire :var :t)))
                           :op :|:|))))

(defparameter *drop-ith*
  (let ((one (make-constant :const 1)))
    (make-alias
     :name :drop_ith
     :inputs (list :n)
     :body (list (make-application
                  :func :iter
                  :arguments (list (make-wire :var :n)
                                   (make-wire :var :drop_ith_rec)
                                   (make-application
                                    :func :fun
                                    :arguments
                                    (list (make-infix :lhs (make-wire :var :h)
                                                      :rhs one
                                                      :op :|:|)
                                          (make-curly :value one)))))))))

(defun drop-ith (n)
  (make-application :func :drop_ith
                    :arguments (list n)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Range
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *int-range32*
  (make-alias :name :intrange32
              :inputs (list :a)
              :body
              (list
               (range32
                (make-infix
                 :op :+
                 :lhs (make-wire :var :a)
                 :rhs (make-constant :const 2147483648))))))




(defparameter *negative32*
  (flet ((wires (num)
           (make-wire :var (intern (format nil "A~a" num) :keyword))))
    (make-alias
     :name   :negative32
     :inputs (list :a)
     :body
     (list (make-bind
            :names (append (mapcar #'wires (alexandria:iota 32))
                           (list (make-wire :var :|()|)))
            :value (int-range32 (make-wire :var :a)))
           (make-wire :var :a31)))))

(defparameter *non-negative32*
  (make-alias :name :nonnegative32
              :inputs (list :a)
              :body (list
                     (make-infix :op :-
                                 :lhs (make-constant :const 1)
                                 :rhs (negative32 (make-wire :var :a))))))
(defparameter *range31*
  (vamp-range 31))

(defparameter *range32*
  (vamp-range 32))

(defparameter *int-range31*
  (make-alias :name :intrange31
              :inputs (list :a)
              :body (list (range31
                           (make-infix :op :+
                                       :lhs (make-wire :var :a)
                                       :rhs (make-constant :const (expt 2 30)))))))


(defparameter *negative31*
  (flet ((wires (num)
           (make-wire :var (intern (format nil "A~a" num) :keyword))))
    (make-alias
     :name   :negative31
     :inputs (list :a)
     :body
     (list (make-bind
            :names (append (mapcar #'wires (alexandria:iota 31))
                           (list (make-wire :var :|()|)))
            :value (int-range31 (make-wire :var :a)))
           (make-wire :var :a30)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; "Less than"
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *less32*
  (let ((a-wire (make-wire :var :a))
        (b-wire (make-wire :var :b)))
    (make-alias :name :less32
                :inputs (list :a :b)
                :body (list
                       (make-application :func :intrange31
                                         :arguments (list a-wire))
                       (make-application :func :intrange31
                                         :arguments (list b-wire))
                       (make-application :func :negative32
                                         :arguments (list
                                                     (make-infix :op :-
                                                                 :lhs a-wire
                                                                 :rhs b-wire)))))))

(defparameter *pwless32*
  (let ((t-wire (make-wire :var :t))
        (p-wire (make-wire :var :p))
        (q-wire (make-wire :var :q))
        (f-wire (make-wire :var :f))
        (g-wire (make-wire :var :g)))
    (make-alias :name :pwless32
                :inputs (list :f :g :p :q)
                :body
                (list
                 (make-bind :names (list t-wire)
                            :value (less32 f-wire g-wire))
                 (make-infix :op :+
                             :lhs (make-infix :op :*
                                              :lhs (make-infix :op :-
                                                               :lhs (make-constant :const 1)
                                                               :rhs t-wire)
                                              :rhs p-wire)
                             :rhs (make-infix :op :*
                                              :lhs t-wire
                                              :rhs q-wire))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Pointwise modulus
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *mod32*
  (let ((a-wire (make-wire :var :a))
        (b-wire (make-wire :var :b))
        (q-wire (make-wire :var :q))
        (r-wire (make-wire :var :r)))
    (make-alias :name :mod32
                :inputs (list :a :b)
                :body (list
                       (make-equality :lhs (make-application :func :nonnegative32
                                                             :arguments (list b-wire))
                                      :rhs (make-constant :const 0))
                       (make-bind :names (list q-wire)
                                  :value (make-application
                                          :func :fresh
                                          :arguments (list (make-infix :op :\\
                                                                       :lhs a-wire
                                                                       :rhs b-wire))))
                       (make-bind :names (list r-wire)
                                  :value (make-application
                                          :func :fresh
                                          :arguments (list (make-infix :op :%
                                                                       :lhs a-wire
                                                                       :rhs b-wire))))
                       (make-equality :lhs (make-application
                                            :func :nonnegative32
                                            :arguments (list r-wire))
                                      :rhs (make-constant :const :0))
                       (make-equality :lhs a-wire
                                      :rhs (make-infix
                                            :op :+
                                            :lhs (make-infix :op :*
                                                             :lhs b-wire
                                                             :rhs q-wire)
                                            :rhs q-wire))
                       (make-equality :lhs (make-application :func :less32
                                                             :arguments (list r-wire b-wire))
                                      :rhs (make-constant :const 0))
                       r-wire))))

(defparameter *pwmod32*
  (let ((x-wire (make-wire :var :x)))
    (make-alias :name :pwmod32
                :inputs (list :f :g :x)
                :body
                (list
                 (make-application
                  :func :mod32
                  :arguments (list (make-application :func :f
                                                     :arguments (list x-wire))
                                   (make-application :func :g
                                                     :arguments (list x-wire))))))))


(defparameter *standard-library*
  (list
   *bool*
   *base-range*
   *next-range*
   *range-n*
   *hd*
   *tl*
   *n-th*
   *negative*
   *plus-range*
   *mult-range*
   *minus-range*
   *isZero*
   *combine-aux*
   *combine*
   *take-base*
   *take-ind*
   *take*
   *drop-ith-rec*
   *drop-ith*
   *nonnegative*
   *mod-n*))

(-> extract (list &optional (or null stream)) (or null stream))
(defun extract (stmts &optional (stream *standard-output*))
  (let ((*print-pretty*      t)
        (*print-miser-width* 40))
    ;; don't use the standard library for now
    (format stream "~{~A~^~%~}" stmts))
  stream)
