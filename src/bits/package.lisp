(in-package :geb.utils)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; trans module
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(muffle-package-variance
 (defpackage #:geb.bits.trans
   (:local-nicknames (:vamp :geb.vampir.spec))
   (:use #:geb.common #:geb.bits.spec)
   (:shadowing-import-from #:geb.bits.spec :+ :* :/ :- :mod)))

(in-package :geb.bits.trans)

(pax:defsection @bits-trans (:title "Bits (Boolean Circuit) Transformations")
  "This covers transformation functions from"
  (to-vampir  pax:generic-function)
  (to-circuit pax:function))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; bits module
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(geb.utils:muffle-package-variance
 (uiop:define-package #:geb.bits
   (:use #:geb.common)
   ;(:shadowing-import-from #:geb.bits.spec )
   (:use-reexport #:geb.bits.trans #:geb.bits.spec)))

(in-package :geb.bits)

(pax:defsection @bits-manual (:title "Bits (Boolean Circuit) Specification")
  "This covers a GEB view of Boolean Circuits. In particular this type will
be used in translating GEB's view of Boolean Circuits into Vampir"
  (@bits              pax:section)
  (@bits-constructors pax:section)
  (@bits-trans        pax:section))
