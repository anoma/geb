(in-package :geb-test)

(define-test geb.lambda.trans
  :parent geb-test-suite)

(def bool geb-bool:bool)

(def so-void-type
  geb:so0)

(def so-unit-type
  geb:so1)

(def stlc-unit-term
  (geb.lambda.spec:unit))

(def so-unit-term
  (geb:terminal so-unit-type))

(def unit-to-bool-left-circuit
  (to-circuit
   (lambda:left so-unit-type (lambda:unit))
   :tc_unit_to_bool_left))

(def unit-to-bool-right-circuit
  (to-circuit
   (lambda:right so-unit-type stlc-unit-term)
   :tc_unit_to_bool_right))

(def pair-bool-stlc
  (lambda:pair
   (lambda:right so-unit-type stlc-unit-term)
   (lambda:left so-unit-type stlc-unit-term)))

(def pair-bool-circuit
  (to-circuit
   (lambda:pair
    (lambda:right so-unit-type stlc-unit-term)
    (lambda:left so-unit-type stlc-unit-term))
   :tc_pair_bool))

(def fst-bool-circuit
  (to-circuit
   (lambda:fst pair-bool-stlc)
   :tc_fst_bool))

(def unit-to-unit-circuit
  (to-circuit stlc-unit-term :tc_unit_to_unit))

(def void-to-unit-circuit
  (to-circuit
   (to-cat (list so-void-type)
           (lambda:absurd so-unit-type (lambda:index 0)))
   :tc_void_to_unit))

(def issue-58-circuit
  (to-circuit
    (lambda:case-on
      (lambda:left so-unit-type stlc-unit-term)
      (lambda:lamb
       (list so-unit-type)
       (lambda:right so-unit-type stlc-unit-term))
      (lambda:lamb
       (list so-unit-type)
       (lambda:left so-unit-type stlc-unit-term)))
    :tc_issue_58))

(define-test compile-checked-term :parent geb.lambda.trans
  (is obj-equalp
      (to-cat nil stlc-unit-term)
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

(define-test so-hom-so1-so1 :parent compile-checked-term
  (is equalp
      (lambda:so-hom geb:so1 geb:so1)
      geb:so1
      "compute hom(so1,so1)"))

(define-test vampir-test-unit-to-unit
  :parent geb.lambda.trans
  (of-type list unit-to-unit-circuit))

(define-test vampir-test-void-to-unit
  :parent geb.lambda.trans
  (of-type list void-to-unit-circuit))

(define-test vampir-test-unit-to-bool-left
  :parent geb.lambda.trans
  (of-type list unit-to-bool-left-circuit))

(define-test vampir-test-unit-to-bool-right
  :parent geb.lambda.trans
  (of-type list unit-to-bool-right-circuit))

(define-test vampir-test-pair-bool
  :parent geb.lambda.trans
  (of-type list pair-bool-circuit))

(define-test vampir-test-issue-58
  :parent geb.lambda.trans
  (of-type list issue-58-circuit))
