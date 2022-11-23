(in-package :geb.utils)

(muffle-package-variance
 (defpackage #:geb.poly
   (:local-nicknames (:vamp :geb.vampir.spec))
   (:use #:geb.utils #:geb.poly.spec #:cl #:serapeum)
   (:shadowing-import-from #:geb.poly.spec :+ :* :/ :- :mod)))

(in-package :geb.poly)
(cl-reexport:reexport-from :geb.poly.spec)
