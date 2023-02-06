(in-package :geb-test)

(define-test geb.lambda.trans
  :parent geb-test-suite)

(def so-unit-type
  geb:so1)

(def stlc-unit-term
  geb.lambda.spec:unit)

(def so-unit-term
  (geb:terminal so-unit-type))

(define-test compile-checked-term :parent geb.lambda.trans
  (is obj-equalp
      (lambda:compile-checked-term nil so-unit-type stlc-unit-term)
      so-unit-term
      "compile unit"))

(define-test stlc-ctx-to-mu :parent compile-checked-term
  (is equalp
      (lambda:stlc-ctx-to-mu nil)
      geb:so1
      "compile in a nil context"))

(define-test fold-singleton-unit-context :parent compile-checked-term
  (is obj-equalp
      (lambda:stlc-ctx-to-mu (list geb:so1))
      (geb:prod geb:so1 geb:so1)
      "fold singleton unit context"))

(define-test fold-singleton-bool-context :parent compile-checked-term
  (is obj-equalp
      (lambda:stlc-ctx-to-mu (list geb-bool:bool))
      (geb:prod geb-bool:bool geb:so1)
      "fold singleton bool context"))

(define-test fold-multi-object-context :parent compile-checked-term
  (is obj-equalp
      (lambda:stlc-ctx-to-mu  (list geb-bool:bool geb:so0 geb:so1))
      (geb:prod geb-bool:bool (geb:prod geb:so0 (geb:prod geb:so1 geb:so1)))
      "fold multi-object context"))
