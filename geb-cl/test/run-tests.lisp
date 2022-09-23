(in-package :geb-test)

(defparameter *all-tests*
  (list 'geb))

(defun run-tests ()
  (mapc #'run! *all-tests*))
