(in-package :geb.utils)

(muffle-package-variance
 (uiop:define-package #:geb.poly.trans
   (:mix #:geb.poly.spec #:cl #:serapeum #:geb.utils #:geb.vampir.spec))

 (defpackage #:geb.poly
   (:use #:geb.utils #:geb.poly.spec #:cl)
   (:shadowing-import-from #:geb.poly.spec :+ :* :/ :- :mod)))

(in-package :geb.poly.trans)

(in-package :geb.poly)
(cl-reexport:reexport-from :geb.poly.spec)
