(defpackage :geb-test
  (:shadowing-import-from :geb :prod :case)
  (:use #:serapeum #:cl #:geb #:fiveam #:geb.mixins)
  (:local-nicknames (:conversion :geb.lambda-conversion))
  (:export #:run-tests))

(in-package :geb-test)
