(in-package :geb.utils)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; API module
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(geb.utils:muffle-package-variance
 (uiop:define-package #:geb.lambda.main
   (:documentation "A basic lambda calculus model")
   (:mix #:geb.lambda.spec #:geb.common #:common-lisp)
   (:reexport #:geb.lambda.spec)))

(in-package #:geb.lambda.main)

(pax:defsection @lambda-api (:title "Main functionality")
  "This covers the main API for the STLC module"

  (ann-term1          pax:generic-function)
  (hom-cod            pax:function)
  (index-check        pax:function)
  (fun-to-hom         pax:function)
  (ann-term2          pax:function)
  (annotated-term     pax:function)
  (type-of-term-w-fun pax:function)
  (type-of-term       pax:function)
  (well-defp          pax:generic-function)
  (fun-type           pax:class)
  (fun-type           pax:function)
  (errorp             pax:function)

  (mcar              (pax:method () (fun-type)))
  (mcadr             (pax:method () (fun-type)))

  (maybe             (pax:method () (fun-type))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; trans module
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package :geb.utils)

(geb.utils:muffle-package-variance
 (uiop:define-package #:geb.lambda.trans
   (:documentation "A basic lambda translator into other parts of geb")
   (:mix #:geb.lambda.spec #:geb.common #:common-lisp :geb.lambda.main)))

(in-package #:geb.lambda.trans)

(pax:defsection @utility (:title "Utility Functionality")
  "These are utility functions relating to translating lambda terms to other types"
  (stlc-ctx-to-mu  pax:function)
  (so-hom  pax:function))

(pax:defsection @stlc-conversion (:title "Transition Functions")
  "These functions deal with transforming the data structure to other
data types"

  "One important note about the lambda conversions is that all
transition functions except [TO-CAT] do not take a context.

Thus if the [\\<STLC\\>] term contains free variables, then call
[TO-CAT] and give it the desired context before calling
any other transition functions"
  (to-cat     (pax:method () (t <stlc>)))
  (to-poly    (pax:method () (<stlc>)))
  (to-bitc    (pax:method () (<stlc>)))
  (to-circuit (pax:method () (<stlc> t)))
  (@utility   pax:section))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; lambda module
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package :geb.utils)

(geb.utils:muffle-package-variance
 (uiop:define-package #:geb.lambda
   (:documentation "A basic lambda calculus model")
   (:mix #:geb.lambda.spec #:geb.lambda.trans #:geb.common #:common-lisp)
   (:use-reexport #:geb.lambda.spec #:geb.lambda.main #:geb.lambda.trans)))

(in-package #:geb.lambda)

(pax:defsection @stlc (:title "The Simply Typed Lambda Calculus model")
  "This covers GEB's view on simply typed lambda calculus

This serves as a useful frontend for those wishing to write a compiler
to GEB and do not wish to target the categorical model.

If one is targeting their compiler to the frontend, then the following
code should be useful for you.

```lisp
(in-package :geb.lambda.main)

MAIN>
(to-circuit
 (lamb (list (coprod so1 so1))
              (index 0))
 :id)
(def id x1 = {
   (x1)
 };)

MAIN>
(to-circuit
 (lamb (list (coprod so1 so1))
              (case-on (index 0)
                              (lamb (list so1)
                                           (right so1 (unit)))
                              (lamb (list so1)
                                           (left so1 (unit)))))
 :not)
(def not x1 = {
   (((1 - x1) * 1) + (x1 * 0), ((1 - x1) * 1) + (x1 * 0))
 };)

MAIN> (to-circuit (lamb (list geb-bool:bool)
                        (left so1 (right so1 (index 0)))) :foo)
(def foo x1 = {
   (0, 1, x1)
 };)
```

For testing purposes, it may be useful to go to the `BITC` backend and
run our interpreter


```lisp
MAIN>
(gapply (to-bitc
         (lamb (list (coprod so1 so1))
               (case-on (index 0)
                        (lamb (list so1)
                              (right so1 (unit)))
                        (lamb (list so1)
                              (left so1 (unit))))))
        #*1)
#*00
MAIN>
(gapply (to-bitc
         (lamb (list (coprod so1 so1))
               (case-on (index 0)
                        (lamb (list so1)
                              (right so1 (unit)))
                        (lamb (list so1)
                              (left so1 (unit))))))
        #*0)
#*11
```

"
  (@lambda-specs pax:section)
  (@lambda-api  pax:section)
  (@stlc-conversion pax:section))
