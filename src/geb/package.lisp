(pax:define-package #:geb
  (:documentation "Gödel, Escher, Bach categorical model")
  (:use #:common-lisp #:serapeum #:geb.mixins #:geb.utils #:geb.spec)
  (:local-nicknames (#:poly #:geb.poly.spec))
  (:shadowing-import-from #:geb.spec :left :right :prod :case)
  (:export :prod :case :mcar :mcadr :mcaddr :mcdr :name :func :obj))

(uiop:define-package #:geb-bool
  (:documentation "Defines out booleans for the geb language")
  (:mix #:geb #:serapeum #:common-lisp)
  (:export
   :bool :mfasle :mtrue :snot
   :higher-and :higher-or))

(in-package #:geb)
(cl-reexport:reexport-from :geb.spec)

(pax:defsection @geb (:title "The Geb Model")
  "Everything here relates directly to the underlying machinery of
   GEB, or to abstractions that help extend it."
  (@geb-categories   pax:section)
  (@geb-accessors    pax:section)
  (@geb-constructors pax:section)
  (@geb-api          pax:section)
  (@geb-examples     pax:section))

(pax:defsection @geb-api (:title "API")
  "Various functions that make working with GEB easier"
  (pair-to-list      pax:function)
  (same-type-to-list pax:function)
  (mlist             pax:function)
  (commutes          pax:function)
  (!->               pax:function)
  (so-eval           pax:function)
  (so-card-alg       pax:generic-function)
  (so-card-alg       (pax:method () (<substobj>)))
  (@geb-translation  pax:section))

(pax:defsection @geb-translation (:title "Translation Functions")
  "These cover various conversions from @GEB-SUBSTMORPH and @GEB-SUBSTMU
into other categorical data structures."
  (to-poly pax:generic-function))

(pax:defsection @geb-examples (:title "Examples")
  "PLACEHOLDER: TO SHOW OTHERS HOW EXAMPLES WORK"
  "Let's see the transcript of a real session of someone working
  with GEB:

  ```cl-transcript
  (values (princ :hello) (list 1 2))
  .. HELLO
  => :HELLO
  => (1 2)

  (+ 1 2 3 4)
  => 10
  ```")
