(in-package :geb.utils)

(defun symbol-to-keyword (symbol)
  "Turns a [symbol] into a [keyword]"
  (intern (symbol-name symbol) :keyword))

(defmacro muffle-package-variance (&rest package-declarations)
  "Muffle any errors about package variance and stating exports out of order.
This is particularly an issue for SBCL as it will error when using MGL-PAX
to do the [export] instead of DEFPACKAGE.

This is more modular thank
[MGL-PAX:DEFINE-PACKAGE](https://melisgl.Githubc.io/mgl-pax-world/mgl-pax-manual.html#MGL-PAX:DEFINE-PACKAGE%20MGL-PAX:MACRO)
in that this can be used with any package creation function like
[UIOP:DEFINE-PACKAGE](https://privet-kitty.github.io/etc/uiop.html#UIOP_002fPACKAGE).

Here is an example usage:

```lisp
     (geb.utils:muffle-package-variance
       (uiop:define-package #:geb.lambda-conversion
         (:mix #:trivia #:geb #:serapeum #:common-lisp)
         (:export
          :compile-checked-term :stlc-ctx-to-mu)))
```"
  `(locally (declare #+sbcl (sb-ext:muffle-conditions sb-int:package-at-variance))
     (handler-bind (#+sbcl (sb-int:package-at-variance #'muffle-warning))
       ,@package-declarations)))
