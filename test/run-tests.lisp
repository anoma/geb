(in-package :geb-test)

(defparameter *all-tests*
  (list 'geb 'geb.lambda 'geb.lambda-conversion))

;; This just dumps the interactive information doesn't prompt you
(defclass noisy-interactive (plain interactive)
  ())

(defclass noisy-summary (interactive summary)
  ())

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
