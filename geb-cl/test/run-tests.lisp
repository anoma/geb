(in-package :geb-test)

(defparameter *all-tests*
  (list 'geb 'geb.lambda))

(defun run-tests ()
  (mapc #'run! *all-tests*))
