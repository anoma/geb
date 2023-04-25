(in-package :geb.bitc.trans)

(defgeneric to-vampir (morphism values)
  (:documentation "Turns a BITC term into a Vamp-IR term with a given value"))

(defun to-circuit (morphism name)
  "Turns a BITC term into a Vamp-IR Gate with the given name"
  (let* ((wire-count (dom morphism))
         (wires (loop for i from 1 to wire-count
                      collect (vamp:make-wire :var (intern (format nil "x~a" i)
                                                           :keyword)))))
    (vamp:make-alias :name name
                     :inputs wires
                     :body (list (vamp:make-tuples :wires (to-vampir morphism wires))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Bits to Vampir Implementation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmethod to-vampir ((obj <bitc>) values)
  (declare (ignore values))
  (subclass-responsibility obj))

(defun infix-creation (symbol value1 value2)
  (vamp:make-infix :op symbol
                   :lhs value1
                   :rhs value2))

(defmethod to-vampir ((obj compose) values)
  (to-vampir (mcar obj)
             (to-vampir (mcadr obj) values)))

(defmethod to-vampir ((obj fork) values)
  "Copy input n intput bits into 2*n output bits"
  (append values values))

(defmethod to-vampir ((obj parallel) values)
  "Take n + m bits, execute car the n bits and cadr on the m bits and
  concat the results from car and cadr"
  (let* ((car  (mcar obj))
         (cadr (mcadr obj))
         (cx   (dom car))
         (inp1 (subseq values 0 cx))
         (inp2 (subseq values cx)))
    (append (to-vampir car inp1)
            (to-vampir cadr inp2))))

(defmethod to-vampir ((obj swap) values)
  "Turn n + m bits into m + n bits by swapping"
  (let ((n (mcar obj)))
    (append (subseq values n)
            (subseq values 0 n))))

(defmethod to-vampir ((obj one) values)
  "Produce a bitvector of length 1 containing 1"
  (declare (ignore values))
  (list (vamp:make-constant :const 1)))

(defmethod to-vampir ((obj zero) values)
  "Produce a bitvector of length 1 containing 0"
  (declare (ignore values))
  (list (vamp:make-constant :const 0)))

(defmethod to-vampir ((obj ident) values)
  "turn n bits into n bits by doing nothing"
  values)

(defmethod to-vampir ((obj drop) values)
  "turn n bits into an empty bitvector"
  (declare (ignore values))
  nil)

(defmethod to-vampir ((obj branch) values)
  "Look at the first bit.

  If its 1, run f on the remaining bits.

  If its 0, run g on the remaining bits."
  (let ((x (car values))
        (xs (cdr values))
        (f (mcar obj))
        (g (mcadr obj))
        (one (vamp:make-constant :const 1)))
    (mapcar (lambda (f-elem g-elem)
              (infix-creation :+
                              (infix-creation :* (infix-creation :- one x) f-elem)
                              (infix-creation :* x g-elem)))
            (to-vampir f xs)
            (to-vampir g xs))))
