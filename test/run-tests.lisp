(in-package :geb-test)

(defparameter *all-tests*
  (list 'geb 'geb.lambda 'geb.lambda-experimental 'geb.lambda-conversion))

;; This just dumps the interactive information doesn't prompt you
(defclass noisy-interactive (plain interactive)
  ())

(defclass noisy-summary (interactive summary)
  ())

(defun run-tests-error ()
  (let ((tests (parachute:status (geb-test:run-tests))))
    (if (eq :failed tests)
        (error "tests failed")
        tests)))

;; we have summary
(defun run-tests (&key
                    (interactive? nil)
                    (summary?     nil)
                    (plain?       t)
                    (designators '(geb-test-suite)))
  "Here we run all the tests. We have many flags to determine how the
tests ought to work

```lisp
(run-tests :plain? nil :interactive? t) ==> 'interactive
(run-tests :summary? t :interactive? t) ==> 'noisy-summary
(run-tests :interactive? t)             ==> 'noisy-interactive
(run-tests :summary? t)                 ==> 'summary
(run-tests)                             ==> 'plain

(run-tests :designators '(geb geb.lambda)) ==> run only those packages
```
"
  (test designators
    :report (cond ((and summary? interactive?) 'noisy-summary)
                  (summary?                    'summary)
                  ((and plain? interactive?)   'noisy-interactive)
                  (interactive?                'interactive)
                  (t                           'plain))))

#+slynk
(defun profile-all ()
  (let* ((packages
           (list-all-packages))
         (alu-packages
           (remove-if-not (lambda (p)
                            (let ((search (search "GEB" (package-name p))))
                              (and search (= 0 search))))
                          packages))
         (without-aluser
             (remove-if (lambda (p)
                          (member (package-name p) '("geb-test")
                                  :test #'equalp))
                        alu-packages)))
    (mapc (lambda (alu)
            (slynk-backend:profile-package alu t t))
          without-aluser)))

#+slynk
(defun unprofile-all ()
  (slynk-backend:unprofile-all))

#+slynk
(defun profiler-report ()
  (slynk-backend:profile-report))

#+slynk
(defun profiler-reset ()
  (slynk-backend:profile-reset))

#+ccl
(defun code-coverage (&optional path)
  "generates code coverage, for CCL the coverage can be found at

[CCL test coverage](../docs/tests/report.html)

[SBCL test coverage](../docs/tests/cover-index.html)

simply run this function to generate a fresh one
"
  (ccl:reset-incremental-coverage)
  (ccl:reset-coverage)

  (setq ccl:*compile-code-coverage* t)
  (asdf:compile-system :geb :force t)
  (asdf:compile-system :geb/test :force t)

  (let ((coverage (make-hash-table)))
    ;; we want to note that some code loads before we can even test
    ;; it, so mark these under their own section
    (setf (gethash 'alucard.startup coverage)
          (ccl:get-incremental-coverage))
    (mapc (lambda (test)
            (run-tests :summary? t :designators test)
            (when test
              (setf (gethash test coverage)
                    (ccl:get-incremental-coverage))))
          (parachute:children (find-test 'geb-test-suite)))
    (ccl:report-coverage (if path
                             ;; this is bad by god fix
                             (format nil "~Areport.html" path)
                             #p"../docs/tests/report.html")
                         :tags coverage))

  (setq ccl:*compile-code-coverage* nil)
  (asdf:compile-system :geb :force t)
  (asdf:compile-system :geb/test :force t))

#+sbcl
(eval-when (:compile-toplevel :load-toplevel :execute)
  (require :sb-cover))

#+sbcl
(defun code-coverage (&optional (path nil))
  "generates code coverage, for CCL the coverage can be found at

[CCL test coverage](../docs/tests/report.html)

[SBCL test coverage](../docs/tests/cover-index.html)

simply run this function to generate a fresh one
"
  nil
  (declaim (optimize (sb-cover:store-coverage-data 3)))
  (asdf:oos 'asdf:load-op :geb :force t)
  (asdf:oos 'asdf:load-op :geb/test :force t)
  (run-tests :summary? t)
  (sb-cover:report (if path path "../docs/tests/"))

  (declaim (optimize (sb-cover:store-coverage-data 3)))
  (asdf:oos 'asdf:load-op :geb :force t)
  (asdf:oos 'asdf:load-op :geb/test :force t))

#-(or sbcl ccl)
(defun code-coverage (&optional path)
  "generates code coverage, for CCL the coverage can be found at

[CCL test coverage](../docs/tests/report.html)

[SBCL test coverage](../docs/tests/cover-index.html)

simply run this function to generate a fresh one
"
  path)
