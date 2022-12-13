(pax:define-package #:geb-docs/docs
  (:use #:cl)
  (:import-from #:geb        #:@geb)
  (:import-from #:geb.mixins #:@mixins)
  (:import-from #:geb.utils  #:@geb-utils-manual)
  (:import-from #:geb-test   #:@geb-test-manual)
  (:import-from #:geb.poly   #:@poly-manual)
  (:import-from #:geb.specs  #:@geb-specs)
  (:export build-docs))
