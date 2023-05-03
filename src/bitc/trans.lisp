(in-package :geb.bitc.trans)

(defmethod to-circuit ((morphism <bitc>) name)
  "Turns a BITC term into a Vamp-IR Gate with the given name"
  (let* ((wire-count (dom morphism))
         (wires (loop for i from 1 to wire-count
                      collect (vamp:make-wire :var (intern (format nil "x~a" i)
                                                           :keyword)))))
    (list
     (vamp:make-alias :name name
                      :inputs wires
                      :body (list (vamp:make-tuples :wires (to-vampir morphism wires nil)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Bits to Vampir Implementation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmethod to-vampir ((obj <bitc>) values constraints)
  (declare (ignore constraints))
  (declare (ignore values))
  (subclass-responsibility obj))

(defun infix-creation (symbol value1 value2)
  (vamp:make-infix :op symbol
                   :lhs value1
                   :rhs value2))

(defmethod to-vampir ((obj compose) values constraints)
  (to-vampir (mcar obj)
             (to-vampir (mcadr obj) values constraints)
             constraints))

(defmethod to-vampir ((obj fork) values constraints)
  "Copy input n intput bits into 2*n output bits"
  (declare (ignore constraints))
  (append values values))

(defmethod to-vampir ((obj parallel) values constraints)
  "Take n + m bits, execute car the n bits and cadr on the m bits and
  concat the results from car and cadr"
  (let* ((car  (mcar obj))
         (cadr (mcadr obj))
         (cx   (dom car))
         (inp1 (subseq values 0 cx))
         (inp2 (subseq values cx)))
    (append (to-vampir car inp1 constraints)
            (to-vampir cadr inp2 constraints))))

(defmethod to-vampir ((obj swap) values constraints)
  "Turn n + m bits into m + n bits by swapping"
  (declare (ignore constraints))
  (let ((n (mcar obj)))
    (append (subseq values n)
            (subseq values 0 n))))

(defmethod to-vampir ((obj one) values constraints)
  "Produce a bitvector of length 1 containing 1"
  (declare (ignore values constraints))
  (list (vamp:make-constant :const 1)))

(defmethod to-vampir ((obj zero) values constraints)
  "Produce a bitvector of length 1 containing 0"
  (declare (ignore values constraints))
  (list (vamp:make-constant :const 0)))

(defmethod to-vampir ((obj ident) values constraints)
  (declare (ignore constraints))
  "turn n bits into n bits by doing nothing"
  values)

(defmethod to-vampir ((obj drop) values constraints)
  "turn n bits into an empty bitvector"
  (declare (ignore values constraints))
  nil)

(defmethod to-vampir ((obj branch) values constraints)
  "Look at the first bit.

  If its 0, run f on the remaining bits.

  If its 1, run g on the remaining bits."
  (let ((x (car values))
        (xs (cdr values))
        (f (mcar obj))
        (g (mcadr obj))
        (one (vamp:make-constant :const 1)))
    (mapcar (lambda (f-elem g-elem)
              (infix-creation :+
                              (infix-creation :* (infix-creation :- one x) f-elem)
                              (infix-creation :* x g-elem)))
            (to-vampir f xs constraints)
            (to-vampir g xs constraints))))
