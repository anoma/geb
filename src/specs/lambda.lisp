(in-package #:geb.lambda.spec)

;; maybe expand this macro and change each defconstant into a proper
;; class declaration. We avoid typing it as we don't actually want to
;; be exhaustive, but rather open.
(defunion stlc
  (absurd (cod geb.spec:substmorph) (value t))
  unit
  (left (lty geb.spec:substmorph) (rty geb.spec:substmorph) (value t))
  (right (lty geb.spec:substmorph) (rty geb.spec:substmorph) (value t))
  (case-on (lty geb.spec:substmorph)
           (rty geb.spec:substmorph)
           (cod geb.spec:substmorph)
           (on t) (left t) (right t))
  (pair (lty geb.spec:substmorph) (rty geb.spec:substmorph) (left t) (right t))
  (fst  (lty geb.spec:substmorph) (rty geb.spec:substmorph) (value t))
  (snd  (lty geb.spec:substmorph) (rty geb.spec:substmorph) (value t))
  (lamb (vty geb.spec:substmorph) (tty geb.spec:substmorph) (value t))
  (app  (dom geb.spec:substmorph) (cod geb.spec:substmorph) (func t) (obj t))
  (index (index fixnum)))

;; because we are doing this with a struct and not a class, however
;; since serapeum defines out `make-load-form' to the
;; read-only-structs we can derive it like such

(defmethod geb.mixins:obj-equalp ((obj1 <stlc>) (obj2 <stlc>))
  (when (equalp (type-of obj1) (type-of obj2))
    (every (lambda (x y) (geb.mixins:obj-equalp x y))
           (make-load-form obj1)
           (make-load-form obj2))))

(defstruct-read-only typed-stlc
  (value unit :type <stlc>)
  (type t :type t))

(defun typed (v typ)
  "Puts together the type declaration with the value itself for lambda terms"
  (make-typed-stlc :value v :type typ))
