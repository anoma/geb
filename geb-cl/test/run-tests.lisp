(in-package :geb-test)

(defparameter *all-tests*
  (list 'geb 'geb.lambda 'geb.lambda-conversion))

(defun run-tests ()
  (mapc #'run! *all-tests*))
