(in-package :geb.utils)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; trans module
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(muffle-package-variance
 (defpackage #:geb.bitc.trans
   (:local-nicknames (:vamp :geb.vampir.spec))
   (:use #:geb.common #:geb.bitc.spec)
   (:shadowing-import-from #:geb.bitc.spec #:drop #:fork)))

(in-package :geb.bitc.trans)

(pax:defsection @bitc-trans (:title "Bits (Boolean Circuit) Transformations")
  "This covers transformation functions from"
  (to-circuit (pax:method () (<bitc> t)))
  (to-vampir  (pax:method () (compose t)))
  (to-vampir  (pax:method () (fork t)))
  (to-vampir  (pax:method () (parallel t)))
  (to-vampir  (pax:method () (swap t)))
  (to-vampir  (pax:method () (one t)))
  (to-vampir  (pax:method () (zero t)))
  (to-vampir  (pax:method () (ident t)))
  (to-vampir  (pax:method () (drop t)))
  (to-vampir  (pax:method () (branch t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; bitc module
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(geb.utils:muffle-package-variance
 (uiop:define-package #:geb.bitc.main
   (:use #:geb.common #:geb.mixins)
   (:shadowing-import-from #:geb.bitc.spec #:drop #:fork)
   (:use-reexport #:geb.bitc.trans #:geb.bitc.spec)))

(geb.utils:muffle-package-variance
 (uiop:define-package #:geb.bitc
   (:use #:geb.common)
   (:shadowing-import-from #:geb.bitc.spec :fork :drop)
   (:use-reexport #:geb.bitc.trans #:geb.bitc.spec #:geb.bitc.main)))

(in-package :geb.bitc.main)

(in-package :geb.bitc)

(pax:defsection @bitc-manual (:title "Bits (Boolean Circuit) Specification")
  "This covers a GEB view of Boolean Circuits. In particular this type will
be used in translating GEB's view of Boolean Circuits into Vampir"
  (@bitc              pax:section)
  (@bitc-constructors pax:section)
  (@bitc-trans        pax:section))
