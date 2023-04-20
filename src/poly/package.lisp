(in-package :geb.utils)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; trans module
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(muffle-package-variance
 (defpackage #:geb.poly.trans
   (:local-nicknames (:vamp :geb.vampir.spec)
                     (:ext  :geb.extensions))
   (:use #:geb.common #:geb.poly.spec)
   (:shadowing-import-from #:geb.poly.spec :+ :* :/ :- :mod)))

(in-package :geb.poly.trans)

(pax:defsection @poly-trans (:title "Polynomial Transformations")
  "This covers transformation functions from"
  (to-vampir  pax:generic-function)
  (to-circuit pax:function))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; poly module
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(geb.utils:muffle-package-variance
 (uiop:define-package #:geb.poly
   (:use #:geb.common)
   (:shadowing-import-from #:geb.poly.spec :+ :* :/ :- :mod)
   (:use-reexport #:geb.poly.trans #:geb.poly.spec)))

(in-package :geb.poly)

(pax:defsection @poly-manual (:title "Polynomial Specification")
  "This covers a GEB view of Polynomials. In particular this type will
be used in translating GEB's view of Polynomials into Vampir"
  (@poly              pax:section)
  (@poly-constructors pax:section)
  (@poly-trans        pax:section))
