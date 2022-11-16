(in-package :geb-test)

(defparameter *all-tests*
  (list 'geb 'geb.lambda 'geb.lambda-conversion))

(defun run-tests (&key (debug nil))
  (mapc (if debug #'debug! #'run!) *all-tests*))
