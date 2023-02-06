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
;; Range inductive definition up to 32-bits
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


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

(defun next-range (range x)
  (make-application :func :next_range
                    :arguments (list range x)))
