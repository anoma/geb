(in-package :geb-gui)

(defmacro center-column-cell ((stream &rest args &key &allow-other-keys)
                              &body x)
  `(formatting-column (,stream ,@args)
     (formatting-cell (,stream :align-x :center :align-y :center)
       ,@x)))

(defun present-object (object stream)
  (present object (presentation-type-of object) :stream stream))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Counter API
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgeneric counter (object))

(defvar *alphabet*
  (map 'string #'code-char (alexandria:iota (- 91 65) :start 65)))

(serapeum:-> gen-name (t) string)
(defun gen-name (view)
  (let ((count (counter view)))
    (incf (counter view))
    (if (>= count (length *alphabet*))
        (format nil "A~A" (- count (length *alphabet*)))
        (string (char *alphabet* count)))))
