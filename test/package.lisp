(pax:define-package :geb-test
  (:shadowing-import-from :geb :prod :case)
  (:shadowing-import-from :parachute :name)
  (:shadowing-import-from :serapeum  :true)
  (:shadow :value :children)
  (:local-nicknames  (#:poly #:geb.poly)
                     (#:bitc #:geb.bitc)
                     (#:lambda #:geb.lambda))
  (:use #:geb.common #:parachute))

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
  (run-tests-error pax:function)
  (code-coverage pax:function))
