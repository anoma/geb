(pax:define-package :geb-test
  (:shadowing-import-from :geb :prod :case)
  (:shadowing-import-from :parachute :name)
  (:shadowing-import-from :serapeum  :true)
  (:local-nicknames  (#:poly #:geb.poly)
                     (#:lambda #:geb.lambda))
  (:use #:serapeum #:cl #:geb #:parachute #:geb.mixins))

(in-package :geb-test)

(define-test geb-test-suite
  :serial nil)

(pax:defsection @geb-test-manual (:title "Testing")
  "We use [parachute](https://quickref.common-lisp.net/parachute.html)
as our testing framework.

Please read the
[manual](https://quickref.common-lisp.net/parachute.html) for extra
features and how to better lay out future tests"
  (run-tests pax:function)
  (code-coverage pax:function))
