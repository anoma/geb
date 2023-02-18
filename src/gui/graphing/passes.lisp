(in-package :geb-gui.graphing.passes)

(-> fold-right-cases (node) node)
(defun fold-right-cases (node)
  (when (typep (representation node) 'case)
    ;; abstract out this dumb logic
    ;; all of this is to add the labels
    (let* ((linearized (linearize-right-case node))
           (note-node  (make-squash :value node))
           (len        (length linearized)))
      (setf (children node)
            nil)
      (mapcar (lambda (x index)
                (apply-note note-node
                            (make-note :from (value x)
                                       :note (format nil "χ~A"
                                                     (number-to-under index))
                                       :value x)))
              (reverse linearized)
              (alexandria:iota len :step -1 :start len)))
    (setf (children node)
          (linearize-right-case node)))
  (setf (children node)
        (mapcar #'fold-right-cases (children node)))
  node)

(defun number-to-digits (number &optional rem)
  (multiple-value-bind (cont flored) (floor number 10)
      (if (and (zerop cont) (zerop flored))
          rem
          (number-to-digits cont (cons flored rem)))))

(defun digit-to-under (digit)
  (cl:case digit
    (0 "₀") (1 "₁") (2 "₂") (3 "₃") (4 "₄")
    (5 "₅") (6 "₆") (7 "₇") (8 "₈") (9 "₉")
    (t "?")))

(defun number-to-under (index)
  (format nil "~{~A~}" (mapcar #'digit-to-under (number-to-digits index))))

(-> linearize-right-case (node) list)
(defun linearize-right-case (node)
  (if (typep (representation node) 'case)
      (let ((children (children node)))
        (append (butlast children)
                (linearize-right-case (car (last children)))))
      (list node)))
