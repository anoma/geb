(in-package :geb.utils)

(defun subclass-responsibility (obj)
  "Denotes that the given method is the subclasses
   responsibility. Inspired from Smalltalk"
  (error "Subclass Responsbility for ~A" (class-name (class-of obj))))

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
  `(eval-when (:compile-toplevel :load-toplevel :execute)
     (locally (declare #+sbcl (sb-ext:muffle-conditions sb-int:package-at-variance))
       (handler-bind (#+sbcl (sb-int:package-at-variance #'muffle-warning))
         ,@package-declarations))))

(defmacro make-pattern (object-name &rest constructor-names)
  "make pattern matching position style instead of record style. This
removes the record constructor style, however it can be brought back
if wanted

```lisp
(defclass alias (<substmorph> <substobj>)
  ((name :initarg :name
         :accessor name
         :type     symbol
         :documentation \"The name of the GEB object\")
   (obj :initarg :obj
        :accessor obj
        :documentation \"The underlying geb object\"))
  (:documentation \"an alias for a geb object\"))

(make-pattern alias name obj)
```"
  `(trivia.level2:defpattern ,object-name
       (&optional ,@constructor-names)
     (list 'and
           (list 'type ',object-name)
           ,@(mapcar (lambda (x)
                       `(list 'trivia.level2:access '',x ,x))
                     constructor-names))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Generic type constructions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftype list-of (ty)
  "Allows us to state a list contains a given type.

-------------

*NOTE*

This does not type check the whole list, but only the first
element. This is an issue with how lists are defined in the
language. Thus this should be be used for intent purposes.

-------------

For a more proper version that checks all elements please look at writing code like

```cl
(deftype normal-form-list ()
  `(satisfies normal-form-list))

(defun normal-form-list (list)
  (and (listp list)
       (every (lambda (x) (typep x 'normal-form)) list)))

(deftype normal-form ()
  `(or wire constant))
```

Example usage of this can be used with `typep`

```cl-transcript
(typep '(1 . 23) '(list-of fixnum))
=> NIL

(typep '(1 23) '(list-of fixnum))
=> T

(typep '(1 3 4 \"hi\" 23) '(list-of fixnum))
=> T

(typep '(1 23 . 5) '(list-of fixnum))
=> T
```

Further this can be used in type signatures

```cl
(-> foo (fixnum) (list-of fixnum))
(defun foo (x)
  (list x))
```
"
  `(cons ,ty (or null cons)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;               Generic Constructors declarations
;; These aren't needed but serve as a good place to put a default doc.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgeneric mcar (obj)
  (:documentation
   "Can be seen as calling CAR on a generic CLOS
[object](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_o.htm#object)"))
(defgeneric mcdr (obj)
  (:documentation "Similar to MCAR, however acts like a CDR for
                   [classes] that we wish to view as a SEQUENCE"))
(defgeneric mcadr (obj)
  (:documentation "like MCAR but for the CADR"))

(defgeneric mcaddr (obj)
  (:documentation "like MCAR but for the CADDR"))

(defgeneric mcadddr (obj)
  (:documentation "like MCAR but for the CADDDR"))

(defgeneric obj (obj)
  (:documentation
   "Grabs the underlying
[object](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_o.htm#object)"))

(defgeneric name (obj)
  (:documentation
   "the name of the given
[object](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_o.htm#object)"))

(defgeneric func (obj)
  (:documentation
   "the function of the
[object](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_o.htm#object)"))

(defgeneric predicate (obj)
  (:documentation
   "the PREDICATE of the
[object](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_o.htm#object)"))

(defgeneric then (obj)
  (:documentation
   "the then branch of the
[object](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_o.htm#object)"))

(defgeneric else (obj)
  (:documentation
   "the then branch of the
[object](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_o.htm#object)"))
