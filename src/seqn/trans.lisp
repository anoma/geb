(in-package :geb.seqn.trans)

(defun remove0-dom (morphism)
  (remove 0 (dom morphism)))

;; Add range-n function

(defun range-constraints-dom (domain)
  (cond ((null domain) nil)
        ((not (cdr domain))
         (list (geb.vampir:range-n
                (vamp:make-constant :const (car domain))
                (vamp:make-wire :var
                                (intern (format nil "X~a" 1))))))
        (t
         (cons (geb.vampir:range-n
                (vamp:make-constant :const (car (last domain)))
                (vamp:make-wire :var (intern (format nil "X~a" (length domain)))))
          (range-constraints-dom (butlast domain))))))

(defmethod to-circuit ((morphism <seqn>) name)
  "Turns a SeqN term into a Vamp-IR Gate with the given name
Note that what is happening is that we look at the domain of the morphism
and skip 0es, making non-zero entries into wires"
  (let* ((wire-count (length (dom morphism)))
         (wires (loop for i from 1 to wire-count
                      collect (vamp:make-wire
                               :var (intern
                                     (format nil "X~a" (- wire-count i))
                                     :keyword)))))
    (list
     (vamp:make-alias
      :name name
      :inputs (cdr (reverse wires))
      :body
      (list
       (vamp:make-tuples
        :wires
        (mapcar #'to-vampir-opt
                (remove nil
                        (filter-map (lambda (x)
                                      (unless (zerop (car x))
                                        (cadr x)))
                                    (prod-list (cod morphism)
                                               (to-vampir morphism wires nil)))))))))))

(defun test-call (circuit)
  "Given a compiled VampIR function with name foo and arguments x1...xn prints
an equality as foo x1 ... xn = y"
  (let ((inputs (vamp:inputs circuit))
        (name   (vamp:name circuit)))
    (list (vamp:make-equality
           :lhs (if (zerop (length inputs))
                    (vamp:make-wire :var name)
                    (vamp:make-application :func name :arguments inputs))
           :rhs (vamp:make-wire :var :y)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; SeqN to Vamp-IR Compilation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmethod to-vampir ((obj <seqn>) values constraints)
  "The method takes a list of values, i.e. a list of wires with
0-wide entries removed and spits out a list of wires to be later
made into a tuple or a single entry if the codomain is isomorphic
to (n) for some n"
  (declare (ignore constraints))
  (declare (ignore values))
  (geb.utils:subclass-responsibility obj))

(defun const-check (obj1 obj2)
  (and (typep obj1 'vamp:constant)
       (typep obj2 'vamp:constant)))

(defmethod to-vampir-opt ((obj vamp:application))
  (let* ((zero (vamp:make-constant :const 0))
         (one (vamp:make-constant :const 1))
         (car (car (vamp:arguments obj)))
         (optcar (to-vampir-opt car)))
    (cond  ((obj-equalp (vamp:func obj) :isZero)
            (if (typep optcar 'vamp:constant)
                (if (zerop (vamp:const optcar))
                    zero
                    one)
                (geb.vampir:isZero optcar)))
           ((obj-equalp (vamp:func obj) :negative)
            (let ((optcadr (to-vampir-opt (cadr (vamp:arguments obj)))))
              (if (typep optcadr 'vamp:constant)
                  (if (< (vamp:const optcadr) 0)
                      zero
                      one)
                  (geb.vampir:negative car optcadr))))
           (t (vamp:make-application
               :func (vamp:func obj)
               :arguments (mapcar 'to-vampir-opt (vamp:arguments obj)))))))

(defmethod to-vampir-opt ((obj vamp:constant))
  obj)

(defmethod to-vampir-opt ((obj vamp:wire))
  obj)

(defmethod to-vampir-opt ((obj vamp:infix))
  (let*  ((lhs (vamp:lhs obj))
          (rhs (vamp:rhs obj))
          (oplhs (to-vampir-opt lhs))
          (oprhs (to-vampir-opt rhs))
          (ob+ (obj-equalp (vamp:op obj) :+))
          (ob- (obj-equalp (vamp:op obj) :-))
          (ob/ (obj-equalp (vamp:op obj) :/))
          (ob* (obj-equalp (vamp:op obj) :*)))
    (if (const-check oplhs
                     oprhs)
        (let ((constl (vamp:const oplhs))
              (constr (vamp:const oprhs)))
          (cond (ob+  (vamp:make-constant
                       :const (+ constl constr)))
                (ob- (vamp:make-constant
                      :const (- constl constr)))
                (ob* (vamp:make-constant
                      :const (* constl constr)))
                (ob/ (vamp:make-constant
                      :const
                      (multiple-value-bind (q)
                          (floor constl
                                 constr)
                        q)))))
        (cond (ob+ (make-opt-plus oplhs oprhs))
              (ob- (make-opt-minus oplhs oprhs))
              (ob/ (make-opt-divide oplhs oprhs))
              (ob* (make-opt-times oplhs oprhs))))))

(defun infix-creation (symbol value1 value2)
  (vamp:make-infix :op symbol
                   :lhs value1
                   :rhs value2))

;; Make wire function accessing the wire list

(defmethod to-vampir ((obj id) inputs constraints)
  "Given a tuple (x1,...,xn) does nothing with it"
  (declare (ignore constraints))
  inputs)

(defmethod to-vampir ((obj composition) inputs constraints)
  "Compile the MCADR after feeding in appropriate
inputs and then feed them as entries to compiled MCAR"
  (to-vampir (mcar obj)
             (to-vampir (mcadr obj) inputs constraints)
             constraints))

(defmethod to-vampir ((obj parallel-seq) inputs constraints)
  "Compile MCAR and MCADR and then apppend the tuples"
  (let* ((mcar (mcar obj))
         (mcadr (mcadr obj))
         (lmcar (length (dom mcar))))
    (append (to-vampir mcar
                       (subseq inputs 0 lmcar)
                       constraints)
            (to-vampir mcadr
                       (subseq inputs
                               lmcar)
                       constraints))))

(defmethod to-vampir ((obj fork-seq) inputs constraints)
  "Given a tuple (x1,...,xn) copies it twice"
  (declare (ignore constraints))
  ;; Since we feed in wires, simply ask for its list of wires and appent
  (append inputs inputs))

(defmethod to-vampir ((obj drop-nil) inputs constraints)
  "Drops everything by producing nothing"
  (declare (ignore inputs constraints))
  (list (vamp:make-constant :const 0)))

(defmethod to-vampir ((obj remove-right) inputs constraints)
  "We do not have nul inputs so does nothing"
  (declare (ignore constraints))
  (butlast inputs))

(defmethod to-vampir ((obj remove-left) inputs constraints)
  "We do not have nul inputs so does nothing"
  (declare (ignore constraints))
  (cdr inputs))

(defmethod to-vampir ((obj drop-width) inputs constraints)
  "The compilation does not produce dropping with domain inputs
wider than codomain ones appropriately. Hence we do not require range
checks here and simply project"
  (declare (ignore constraints))
  inputs)

(defmethod to-vampir ((obj inj-length-left) inputs constraints)
  "Look at the MCAR. Look at non-null wide entries and place
0-es in the outputs otherwise ignore"
  (declare (ignore constraints))
  (append inputs
          (make-list (length  (mcadr obj))
                     :initial-element (vamp:make-constant :const 0))))

(defmethod to-vampir ((obj inj-length-right) inputs constraints)
  "Look at the MCADR. Look at non-null wide entries and place
0-es in the outputs "
  (declare (ignore constraints))
  (append (make-list (length  (mcar obj))
                     :initial-element (vamp:make-constant :const 0))
          inputs))

(defmethod to-vampir ((obj inj-size) inputs constraints)
  "During th ecompilation procedure the domain will not have larger
width than the codomain so we simply project"
  (declare (ignore constraints))
  inputs)

(defmethod to-vampir ((obj branch-seq) inputs constraints)
  "With the leftmost input being 1 or 0, pointwise do usual bit
branching. If 0 run the MCAR, if 1 run the MCADR"
  (let* ((car   (car inputs))
         (left  (to-vampir (mcar obj) (cdr inputs) constraints))
         (right (to-vampir (mcadr obj) (cdr inputs) constraints)))
    (mapcar (lambda (x)
              (infix-creation
               :+
               (infix-creation :*
                               (infix-creation :-
                                               (vamp:make-constant :const 1)
                                               car)
                               (car x))
               (infix-creation :* car (cadr x))))
            (prod-list left right))))

(defmethod to-vampir ((obj shift-front) inputs constraints)
  "Takes the MCADR entry and moves it upward leaving everything
else fixed. Note that we have to be careful as inputs will have 0es
removed already and hence we cannot count as usual"
  (declare (ignore constraints))
  (let* ((mcadr (mcadr obj))
         (mmcadr (1- mcadr)))
    (append (list (nth mmcadr inputs))
            (subseq inputs 0 mmcadr)
            (subseq inputs mcadr))))

(defmethod to-vampir ((obj zero-bit) inputs constraints)
  (declare (ignore inputs constraints))
  (list (vamp:make-constant :const 0)))

(defmethod to-vampir ((obj one-bit) inputs constraints)
  (declare (ignore inputs  constraints))
  (list (vamp:make-constant :const 1)))

(defmethod to-vampir ((obj seqn-add) inputs constraints)
  (declare (ignore constraints))
  (list (infix-creation :+ (car inputs) (cadr inputs))))

(defmethod to-vampir ((obj seqn-subtract) inputs constraints)
  (declare (ignore constraints))
  (list (infix-creation :- (car inputs) (cadr inputs))))

(defmethod to-vampir ((obj seqn-multiply) inputs constraints)
  (declare (ignore constraints))
  (list (infix-creation :* (car inputs) (cadr inputs))))

(defmethod to-vampir ((obj seqn-divide) inputs constraints)
  (declare (ignore constraints))
  (list (infix-creation :/ (car inputs) (cadr inputs))))

(defmethod to-vampir ((obj seqn-nat) inputs constraints)
  (declare (ignore constraints))
  (list (vamp:make-constant :const (mcadr obj))))

(defmethod to-vampir ((obj seqn-concat) inputs constraints)
  (declare (ignore constraints))
  (list (infix-creation :+
                        (infix-creation :* (car inputs)
                                        (vamp:make-constant
                                         :const (expt 2 (mcadr obj))))
                        (cadr inputs))))

(defmethod to-vampir ((obj seqn-decompose) inputs constraints)
  (declare (ignore constraints))
  (let* ((mcar (mcar obj))
         (car (car inputs))
         (rng  (vamp:make-application
                :func :range_n
                :arguments (list (vamp:make-constant :const mcar)
                                 car)))
         (lst  (list (vamp:make-constant :const (1- mcar))
                     rng)))
    (list (vamp:make-application :func :n_th
                                 :arguments lst)
          (geb.vampir:combine
           (vamp:make-application :func :drop_ith
                                  :arguments lst)))))

(defun range-depth (x)
  (let ((cadr (cadr (vamp:arguments x))))
    (if (not (typep cadr 'vamp:application))
        0
        (1+ (range-depth (cadr (vamp:arguments (car (vamp:arguments cadr)))))))))

(defmethod to-vampir ((obj seqn-eq) inputs constraints)
  (declare (ignore constraints))
  (list (geb.vampir:isZero (infix-creation :-
                                           (car inputs)
                                           (cadr inputs)))
        (vamp:make-constant :const 0)))

(defmethod to-vampir ((obj seqn-lt) inputs constraints)
  (declare (ignore constraints))
  (list (geb.vampir:negative (vamp:make-constant :const (mcar obj))
                             (infix-creation :-
                                             (car inputs)
                                             (cadr inputs)))
        (vamp:make-constant :const 0)))

(defmethod to-vampir ((obj seqn-mod) inputs constraints)
  (declare (ignore constraints))
  (let ((car (car inputs))
        (cadr (cadr inputs)))
    (if (const-check car cadr)
        (list (vamp:make-constant :const (mod (vamp:const car) (vamp:const cadr))))
        (list (geb.vampir:mod-n (vamp:make-constant :const (mcar obj))
                                car cadr)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; happens when the first input is constant
(defun optimize-decompose (obj first-input)
  (if (>= (vamp:const first-input) (expt 2 (1- obj)))
      (list (vamp:make-constant
             :const 1)
            (vamp:make-constant
             :const (- (vamp:const first-input) (expt 2 (1- obj)))))
      (list (vamp:make-constant
             :const 0)
            first-input)))

(defun make-opt-plus (value1 value2)
  (let ((base (infix-creation :+
                              value1
                              value2)))
    (cond ((typep value1 'vamp:constant)
           (if (zerop (vamp:const value1))
               value2
               base))
          ((typep value2 'vamp:constant)
           (if (zerop (vamp:const value2))
               value1
               base))
          (t
           base))))

(defun make-opt-minus (value1 value2)
  (let ((base (infix-creation :-
                              value1
                              value2)))
    (cond ((typep value2 'vamp:constant)
           (if (zerop (vamp:const value2))
               value1
               base))
          (t
           base))))

(defun make-opt-divide (value1 value2)
  (let ((base (infix-creation :/
                              value1
                              value2)))
    (cond ((typep value2 'vamp:constant)
           (if (= (vamp:const value2) 1)
               value1
               base))
          (t
           base))))

(defun make-opt-times (value1 value2)
  (let ((base (infix-creation :*
                              value1
                              value2))
        (zero (vamp:make-constant :const 0)))
    (cond ((typep value1 'vamp:constant)
           (cond ((zerop (vamp:const value1))
                  zero)
                 ((= (vamp:const value1) 1)
                  value2)
                 (t
                  base)))
          ((typep value2 'vamp:constant)
           (cond ((zerop (vamp:const value2))
                  zero)
                 ((= (vamp:const value2) 1)
                  value1)
                 (t
                  base)))
          (t
           base))))
