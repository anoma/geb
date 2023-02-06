(in-package :geb-test)

(def bool geb-bool:bool)

(defun morph-to-vampir (morph name)
  (poly::to-circuit (geb:to-poly morph) name))

(defun stlc-to-morph (ctx ty term)
  (lambda:compile-checked-term ctx ty term))

(defun stlc-to-vampir (ctx ty term name)
  (morph-to-vampir (stlc-to-morph ctx ty term) name))

(define-test geb-poly :parent geb-test-suite)

(def test-circuit-1
  (poly::to-circuit (poly:+ 1 (poly:+ poly:ident (poly:* 3 poly:ident)))
    :tc_1))

(define-test vampir-converter
  :parent geb-poly
  (of-type geb.vampir.spec:alias test-circuit-1))

(def test-morph-2 (<-left so1 bool))

(def test-poly-2 (geb::to-poly test-morph-2))

(def test-circuit-2 (morph-to-vampir test-morph-2 :tc_2))

(define-test vampir-test-2
  :parent geb-poly
  (of-type geb.vampir.spec:alias test-circuit-2))

(def unit-to-unit-circuit
  (stlc-to-vampir nil so-unit-type stlc-unit-term :tc_unit_to_unit))

(define-test vampir-test-unit-to-unit
  :parent geb-poly
  (of-type geb.vampir.spec:alias unit-to-unit-circuit))

(def unit-to-bool-left-circuit
  (stlc-to-vampir
    nil bool
    (lambda:left stlc-unit-term)
    :tc_unit_to_bool_left))

(define-test vampir-test-unit-to-bool-left
  :parent geb-poly
  (of-type geb.vampir.spec:alias unit-to-bool-left-circuit))

(def unit-to-bool-right-circuit
  (stlc-to-vampir
    nil bool
    (lambda:right stlc-unit-term)
    :tc_unit_to_bool_right))

(define-test vampir-test-unit-to-bool-right
  :parent geb-poly
  (of-type geb.vampir.spec:alias unit-to-bool-right-circuit))

(def pair-bool-stlc
  (lambda:pair bool bool
    (lambda:right stlc-unit-term)
    (lambda:left stlc-unit-term)))

(def pair-bool-circuit
  (stlc-to-vampir
   nil (geb:prod bool bool)
   (lambda:pair bool bool
     (lambda:right stlc-unit-term)
     (lambda:left stlc-unit-term))
   :tc_pair_bool))

(define-test vampir-test-pair-bool
  :parent geb-poly
  (of-type geb.vampir.spec:alias pair-bool-circuit))

(def fst-bool-circuit
  (stlc-to-vampir
   nil bool
   (lambda:fst bool bool pair-bool-stlc)
   :tc_fst_bool))
