;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; API module
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(geb.utils:muffle-package-variance
 (defpackage #:geb.main
   (:documentation "Gödel, Escher, Bach categorical model")
   (:use #:common-lisp #:geb.generics #:serapeum #:geb.mixins #:geb.utils #:geb.spec)
   (:local-nicknames (#:poly #:geb.poly.spec))
   (:shadowing-import-from #:geb.spec :left :right :prod :case)
   (:export :prod :case :mcar :mcadr :mcaddr :mcdr :name :func :obj :dom :codom)))

(in-package #:geb.main)

(pax:defsection @geb-utility (:title "Utility")
  "Various utility functions ontop of @GEB-CATEGORIES"
  (pair-to-list      pax:function)
  (same-type-to-list pax:function)
  (cleave            pax:function)
  (const             pax:function)
  (commutes          pax:function)
  (commutes-left     pax:function)
  (!->               pax:function)
  (so-eval           pax:function)
  (so-hom-obj        pax:function)
  (so-card-alg       pax:generic-function)
  (so-card-alg       (pax:method () (<substobj>)))
  (curry             pax:function)
  (text-name         pax:generic-function))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Standard Library throughout the codebase
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(geb.utils:muffle-package-variance
 (uiop:define-package #:geb.common
   (:documentation "Provides the standard library for any GEB code")
   (:shadowing-import-from #:geb.spec :left :right :prod :case)
   (:import-from #:trivia #:match)
   (:use-reexport #:geb.mixins #:geb.generics #:geb.spec #:geb.main #:geb.utils
                  #:serapeum #:common-lisp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; trans module
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(geb.utils:muffle-package-variance
 (defpackage #:geb.trans
   (:documentation "Gödel, Escher, Bach categorical model")
   (:use #:common-lisp #:serapeum #:geb.mixins #:geb.utils #:geb.spec #:geb.main)
   (:local-nicknames (#:poly #:geb.poly.spec))
   (:shadowing-import-from #:geb.spec :left :right :prod :case)
   (:export :prod :case :mcar :mcadr :mcaddr :mcdr :name :func :obj)))

(in-package #:geb.trans)

(pax:defsection @geb-translation (:title "Translation Functions")
  "These cover various conversions from @GEB-SUBSTMORPH and @GEB-SUBSTMU
into other categorical data structures."
  (to-poly    pax:generic-function)
  (to-circuit pax:function))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; bool module
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(geb.utils:muffle-package-variance
 (uiop:define-package #:geb-bool
   (:documentation "Defines out booleans for the geb language")
   (:mix #:geb.main #:geb.spec #:serapeum #:common-lisp)
   (:shadow :false :true :not :and :or)
   (:export
    :bool :fasle :true :not :and :or)))

(in-package #:geb-bool)

(pax:defsection @geb-bool (:title "Booleans")
  "Here we define out the idea of a boolean. It comes naturally from the
concept of coproducts. In ML they often define a boolean like

```haskell
data Bool = False | True
```

We likewise define it with coproducts

```lisp
(def bool (coprod so1 so1))

(def true  (->right so1 so1))
(def false (->left  so1 so1))
```

The functions given work on this."
  (true      pax:symbol-macro)
  (false     pax:symbol-macro)
  (false-obj pax:symbol-macro)
  (true-obj  pax:symbol-macro)
  (bool      pax:symbol-macro)
  (not       pax:symbol-macro)
  (and       pax:symbol-macro)
  (or        pax:symbol-macro))


(geb.utils:muffle-package-variance
 (uiop:define-package #:geb
   (:documentation "Gödel, Escher, Bach categorical model")
   (:use #:geb.common)
   (:use-reexport #:geb.spec #:geb.trans #:geb.main)))

(in-package #:geb)

(pax:defsection @geb (:title "The Geb Model")
  "Everything here relates directly to the underlying machinery of
   GEB, or to abstractions that help extend it."
  (@mixins-cat       pax:section)
  (@generics         pax:section)
  (@geb-categories   pax:section)
  (@geb-accessors    pax:section)
  (@geb-constructors pax:section)
  (@geb-api          pax:section)
  (@geb-examples     pax:section))

(pax:defsection @geb-api (:title "API")
  "Various forms and structures built on-top of @GEB-CATEGORIES"
  (gapply                     (pax:method () (<substmorph> t)))
  (geb-bool::@geb-bool        pax:section)
  (geb.trans:@geb-translation pax:section)
  (@geb-utility               pax:section))

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
