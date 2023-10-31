(geb.utils:muffle-package-variance
 (uiop:define-package #:geb.extensions
   (:documentation "Special algorithms for extensions")
   (:mix #:common-lisp #:geb.utils #:geb.extension.spec #:geb.mixins #:serapeum)))

(in-package :geb.extensions)

(pax:defsection @extensions  (:title "Geb Extension API")
  "Here we cover features entailed by the extensions."

  (@sub-expressions pax:document))

(pax:defsection @sub-expressions (:title "Sub Expression API")
  "Here we cover functions regarding common sub-expressions"
  (keep-unique            function)
  (compute-common-usages  function)
  (common-sub-expressions function))
