(in-package :geb.utils)

(muffle-package-variance
 (defpackage #:geb.poly
   (:local-nicknames (:vamp :geb.vampir.spec))
   (:use #:geb.utils #:geb.poly.spec #:cl #:serapeum)
   (:shadowing-import-from #:geb.poly.spec :+ :* :/ :- :mod)))

(in-package :geb.poly)
(cl-reexport:reexport-from :geb.poly.spec)

(pax:defsection @poly-manual (:title "Polynomial Specification")
  "This covers a GEB view of Polynomials. In particular this type will
be used in translating GEB's view of Polynomials into Vampir"
  (@poly              pax:section)
  (@poly-constructors pax:section))
