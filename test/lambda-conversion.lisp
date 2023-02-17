(in-package :geb-test)

(define-test geb.lambda.trans
  :parent geb-test-suite)

(def bool geb-bool:bool)

(def so-unit-type
  geb:so1)

(def stlc-unit-term
  geb.lambda.spec:unit)

(def so-unit-term
  (geb:terminal so-unit-type))

(def unit-to-bool-left-circuit
  (lambda:to-circuit
    nil bool
    (lambda:left stlc-unit-term)
    :tc_unit_to_bool_left))

(def unit-to-bool-right-circuit
  (lambda:to-circuit
    nil bool
    (lambda:right stlc-unit-term)
    :tc_unit_to_bool_right))

(def pair-bool-stlc
  (lambda:pair bool bool
               (lambda:right stlc-unit-term)
               (lambda:left stlc-unit-term)))

(def pair-bool-circuit
  (lambda:to-circuit
   nil (geb:prod bool bool)
   (lambda:pair bool bool
                (lambda:right stlc-unit-term)
                (lambda:left stlc-unit-term))
   :tc_pair_bool))

(def fst-bool-circuit
  (lambda:to-circuit
   nil bool
   (lambda:fst bool bool pair-bool-stlc)
   :tc_fst_bool))

(def unit-to-unit-circuit
  (lambda:to-circuit nil so-unit-type stlc-unit-term :tc_unit_to_unit))

(def issue-58-circuit
  (lambda:to-circuit
    nil
    (coprod so-unit-type so-unit-type)
    (lambda:case-on
      so-unit-type so-unit-type
      (coprod so-unit-type so-unit-type)
      (lambda:left stlc-unit-term)
      (lambda:lamb
        so-unit-type (coprod so-unit-type so-unit-type)
        (lambda:right stlc-unit-term))
      (lambda:lamb
        so-unit-type (coprod so-unit-type so-unit-type)
        (lambda:left stlc-unit-term))
      )
    :tc_issue_58))

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

(define-test vampir-test-unit-to-unit
  :parent geb.lambda.trans
  (of-type geb.vampir.spec:alias unit-to-unit-circuit))

(define-test vampir-test-unit-to-bool-left
  :parent geb.lambda.trans
  (of-type geb.vampir.spec:alias unit-to-bool-left-circuit))

(define-test vampir-test-unit-to-bool-right
  :parent geb.lambda.trans
  (of-type geb.vampir.spec:alias unit-to-bool-right-circuit))

(define-test vampir-test-pair-bool
  :parent geb.lambda.trans
  (of-type geb.vampir.spec:alias pair-bool-circuit))

(define-test vampir-test-issue-58
  :parent geb.lambda.trans
  (of-type geb.vampir.spec:alias issue-58-circuit))
