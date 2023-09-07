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
                      collect (vamp:make-wire :var (intern (format nil "X~a" i)
                                                           :keyword)))))
    (list
     (vamp:make-alias
      :name name
      :inputs wires
      :body
      (append
       (range-constraints-dom (dom morphism))
       (list
        (vamp:make-tuples
         :wires
         (remove nil
                 (filter-map (lambda (x)
                               (unless (zerop (car x))
                                 (cadr x)))
                             (prod-list (cod morphism)
                                        (to-vampir morphism wires nil)))))))))))

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
    (cond
      ((not (typep car 'vamp:constant))
       (mapcar (lambda (x) (optimize-branch x car)) (prod-list left right)))
      ((= (vamp:const car) 0)
       left)
      (t
       right))))

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

(defun const-check (inputs)
  (and (typep (car inputs) 'vamp:constant)
       (typep (cadr inputs) 'vamp:constant)))

(defmethod to-vampir ((obj seqn-add) inputs constraints)
  (declare (ignore constraints))
  (let ((car (car inputs))
        (cadr (cadr inputs))
        (mcar (mcar obj)))
    (if (const-check inputs)
        (let ((plus (+ (vamp:const car)
                       (vamp:const cadr))))
          (if (> (expt 2 mcar) plus)
              (vamp:make-constant :const plus)
              (error "Range Exceeded")))
        (list (geb.vampir:plus-range (vamp:make-constant :const mcar)
                                     car
                                     cadr)))))

(defmethod to-vampir ((obj seqn-subtract) inputs constraints)
  (declare (ignore constraints))
  (let ((car (car inputs))
        (cadr (cadr inputs)))
    (if (const-check inputs)
        (let ((minus (- (vamp:const car) (vamp:const cadr))))
          (if (<= 0 minus)
              (vamp:make-constant :const minus)
              (error "Subtraction Produces Negative Numbers")))
        (list (geb.vampir:minus-range (vamp:make-constant :const (mcar obj))
                                      car
                                      cadr)))))

(defmethod to-vampir ((obj seqn-multiply) inputs constraints)
  (declare (ignore constraints))
  (let ((car (car inputs))
        (cadr (cadr inputs))
        (mcar (mcar obj)))
    (if (const-check inputs)
        (let ((mult (* (vamp:const car) (vamp:const cadr))))
          (if (> (expt 2 mcar) mult)
              (vamp:make-constant :const mult)
              (error "Range Exceeded")))
        (list (geb.vampir:mult-range (vamp:make-constant :const mcar)
                                     car
                                     cadr)))))

(defmethod to-vampir ((obj seqn-divide) inputs constraints)
  (declare (ignore constraints))
  (let ((car (car inputs))
        (cadr (cadr inputs)))
    (if (const-check inputs)
        (vamp:make-constant
         :const
         (multiple-value-bind (q) (floor (vamp:const car) (vamp:const cadr)) q))
        (list (make-opt-divide (car inputs) (cadr inputs))))))

(defmethod to-vampir ((obj seqn-nat) inputs constraints)
  (declare (ignore constraints))
  (list (vamp:make-constant :const (mcadr obj))))

(defmethod to-vampir ((obj seqn-concat) inputs constraints)
  (declare (ignore constraints))
  (let ((car (car inputs))
        (cadr (cadr inputs)))
    (if (const-check inputs)
        (list (vamp:make-constant
               :const (+ (* (expt 2 (mcadr obj)) (vamp:const car))
                         (vamp:const cadr))))
        (list (make-opt-plus (make-opt-times car
                                             (vamp:make-constant
                                              :const (expt 2 (mcadr obj))))
                             cadr)))))

(defmethod to-vampir ((obj seqn-decompose) inputs constraints)
  (declare (ignore constraints))
  (let* ((mcar (mcar obj))
         (car (car inputs))
         (rng  (vamp:make-application
                :func :range_n
                :arguments (list (vamp:make-constant :const mcar)
                                 car)))
         (lst  (list (vamp:make-constant :const (1- mcar))
                     rng))
         (dpth (range-depth rng)))
    (cond ((typep car 'vamp:constant)
           (optimize-decompose mcar car))
          ((zerop dpth)
           (list (vamp:make-application :func :n_th
                                        :arguments lst)
                 (geb.vampir:combine
                  (vamp:make-application :func :drop_ith
                                         :arguments lst))))
          (t
           (list (vamp:make-application
                  :func :n_th
                  :arguments
                  (list
                   (vamp:make-constant :const (1- mcar))
                   (geb.utils:apply-n dpth
                                      (lambda (x)
                                        (cadr (vamp:arguments
                                               (car (vamp:arguments
                                                     (cadr (vamp:arguments x)))))))
                                      rng)))
                 (geb.vampir:combine
                  (vamp:make-application :func :drop_ith :arguments lst)))))))

(defun range-depth (x)
  (let ((cadr (cadr (vamp:arguments x))))
    (if (not (typep cadr 'vamp:application))
        0
        (1+ (range-depth (cadr (vamp:arguments (car (vamp:arguments cadr)))))))))

(defmethod to-vampir ((obj seqn-eq) inputs constraints)
  (declare (ignore constraints))
  (let ((car (car inputs))
        (cadr (cadr inputs))
        (zero (vamp:make-constant :const 0)))
    (if (const-check inputs)
        (if (zerop (- (vamp:const car) (vamp:const cadr)))
            (list zero
                  zero)
            (list (vamp:make-constant :const 1)
                  zero))
        (list (geb.vampir:isZero (make-opt-minus (car inputs)
                                                 (cadr inputs)))
              zero))))

(defmethod to-vampir ((obj seqn-lt) inputs constraints)
  (declare (ignore constraints))
  (let ((car (car inputs))
        (cadr (cadr inputs))
        (zero (vamp:make-constant :const 0)))
    (if (const-check inputs)
        (if (< (vamp:const car) (vamp:const cadr))
            (list zero
                  zero)
            (list (vamp:make-constant :const 1)
                  zero))
        (list (geb.vampir:negative (vamp:make-constant :const (mcar obj))
                                   (make-opt-minus car
                                                   cadr))
              zero))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun optimize-branch (inp first-input)
  (let* ((carobj (car inp))
         (cadrobj (cadr inp))
         (ifzero (make-opt-minus (vamp:make-constant :const 1) first-input))
         (ifone  (make-opt-times first-input cadrobj))
         (output (make-opt-plus (make-opt-times ifzero carobj) ifone)))
    (cond ((and (typep carobj 'vamp:constant)
                (typep cadrobj 'vamp:constant))
           (let* ((carobjnum (vamp:const carobj))
                  (cadrobjnum (vamp:const cadrobj))
                  (careq0 (zerop carobjnum))
                  (careq1 (= carobjnum 1))
                  (cadreq0 (zerop carobjnum))
                  (cadreq1 (= carobjnum 1)))
             (cond ((= carobjnum cadrobjnum 0)
                    (vamp:make-constant :const 0))
                   ((and careq0
                         (not cadreq1))
                    ifone)
                   ((and careq0
                         cadreq1)
                    first-input)
                   ((and (not careq1)
                         cadreq0)
                    (make-opt-times ifzero carobj))
                   ((and careq1
                         cadreq0)
                    ifzero)
                   ((and (= carobjnum cadrobjnum 1))
                    (make-opt-plus ifzero
                                   first-input))
                   (t output))))
          ((typep carobj 'vamp:constant)
           (let ((carobjnum (vamp:const carobj)))
             (cond ((zerop carobjnum)
                    (make-opt-times first-input
                                    cadrobj))
                   ((= carobjnum 1)
                    (make-opt-plus ifzero ifone))
                   (t output))))
          ((typep cadrobj 'vamp:constant)
           (let ((cadrobjnum (vamp:const cadrobj)))
             (cond ((zerop cadrobjnum)
                    (make-opt-times ifzero carobj))
                   ((= cadrobjnum 1)
                    (make-opt-plus (make-opt-times ifzero
                                                   carobj)
                                   first-input))
                   (t  output))))
          (t output))))


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
