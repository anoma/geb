(defpackage :geb-test
  (:shadowing-import-from :geb :prod :case)
  (:use #:serapeum #:cl #:geb #:fiveam)
  (:local-nicknames)
  (:export #:run-tests))

(in-package :geb-test)
