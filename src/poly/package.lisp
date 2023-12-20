(in-package :geb.utils)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; trans module
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(muffle-package-variance
 (defpackage #:geb.poly.trans
   (:local-nicknames (:vamp :geb.vampir.spec)
                     (:ext  :geb.extensions))
   (:use #:geb.common #:geb.poly.spec)
   (:shadowing-import-from #:geb.poly.spec :+ :* :/ :- :mod)
   (:export #:@poly-trans)))

(in-package :geb.poly.trans)

(pax:defsection @poly-trans (:title "Polynomial Transformations")
  "This covers transformation functions from"
  (to-circuit (method () (<poly> t)))
  (to-vampir  (method () (integer t t)))
  (to-vampir  (method () (ident t t)))
  (to-vampir  (method () (+ t t)))
  (to-vampir  (method () (* t t)))
  (to-vampir  (method () (- t t)))
  (to-vampir  (method () (/ t t)))
  (to-vampir  (method () (compose t t)))
  (to-vampir  (method () (if-zero t t)))
  (to-vampir  (method () (if-lt t t)))
  (to-vampir  (method () (mod t t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; poly module
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(geb.utils:muffle-package-variance
 (defpackage #:geb.poly.main
   (:use #:geb.common)
   (:local-nicknames (#:poly #:geb.poly.spec))
   (:export #:@poly-api)))

(in-package :geb.poly.main)

(pax:defsection @poly-api (:title "Polynomial API")
  "This covers the polynomial API"
  (gapply             (method () (poly:<poly> t)))
  (gapply             (method () (integer t))))

(geb.utils:muffle-package-variance
 (uiop:define-package #:geb.poly
   (:use #:geb.common)
   (:shadowing-import-from #:geb.poly.spec :+ :* :/ :- :mod)
   (:use-reexport #:geb.poly.trans #:geb.poly.spec #:geb.poly.main)
   (:export #:@poly-manual)))

(in-package :geb.poly)

(pax:defsection @poly-manual (:title "Polynomial Specification")
  "This covers a GEB view of Polynomials. In particular this type will
be used in translating GEB's view of Polynomials into Vampir"
  (@poly              pax:section)
  (@poly-api          pax:section)
  (@poly-constructors pax:section)
  (@poly-trans        pax:section))
