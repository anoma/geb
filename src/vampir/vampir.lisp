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
      (make-equality :lhs a-wire
                     :rhs
                     (make-infix :op :+
                                 :lhs (make-wire :var :a0)
                                 :rhs (make-infix :op :*
                                                  :lhs (make-constant :const 2)
                                                  :rhs (make-wire :var :a1))))
      (make-tuples :wires (list
                           (make-wire :var :a0)
                           (make-application :func :range
                                             :arguments
                                             (list (make-wire :var :a1)))))))))

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
   *range31*
   *range32*
   *int-range31*
   *int-range32*
   *negative31*
   *negative32*
   *non-negative32*
   *less32*
   *mod32*
   *pwmod32*
   *next-range*))

(-> extract (list &optional stream) stream)
(defun extract (stmts &optional (stream *standard-output*))
  (let ((*print-pretty*      t)
        (*print-miser-width* 40))
    (format stream "~{~A~^~%~}" (append *standard-library* stmts)))
  stream)
