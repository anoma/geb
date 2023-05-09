(in-package :geb-test)

(define-test geb.lambda.trans
  :parent geb-test-suite)

(def pair-bool-stlc
  (lambda:pair
   (lambda:right so1 (lambda:unit))
   (lambda:left so1 (lambda:unit))))

(def lambda-not-with-lambda
  (lambda:lamb
   (list (coprod so1 so1))
   (lambda:case-on (lambda:index 0)
                   (lambda:lamb (list so1) (lambda:right so1 (lambda:unit)))
                   (lambda:lamb (list so1) (lambda:left so1 (lambda:unit))))))

(def lambda-not-without-lambda
  (lambda:lamb
   (list (coprod so1 so1))
   (lambda:case-on (lambda:index 0)
                   (lambda:right so1 (lambda:unit))
                   (lambda:left so1 (lambda:unit)))))

(def lambda-pairing
  (lambda:lamb (list geb-bool:bool)
               (lambda:pair (lambda:right so1 (lambda:index 0))
                            (lambda:left so1 (lambda:index 0)))))

(def issue-58-circuit
  (to-circuit
   (lambda:case-on
    (lambda:left so1 (lambda:unit))
    (lambda:lamb (list so1) (lambda:right so1 (lambda:unit)))
    (lambda:lamb (list so1) (lambda:left so1 (lambda:unit))))
   :tc_issue_58))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                    Interpreter tests                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-test lambda.trans-eval :parent geb.lambda.trans)

(define-test lambda.case-works-as-expected :parent lambda.trans-eval
  (is equalp #*0 (gapply (to-bitc lambda-not-with-lambda) #*1))
  (is equalp #*1 (gapply (to-bitc lambda-not-with-lambda) #*0))
  (is equalp
      (gapply (to-bitc lambda-not-without-lambda) #*0)
      (gapply (to-bitc lambda-not-with-lambda) #*0))
  (is equalp
      (gapply (to-bitc lambda-not-without-lambda) #*1)
      (gapply (to-bitc lambda-not-with-lambda) #*1)))

(define-test lambda.preserves-pair :parent lambda.trans-eval
  (is obj-equalp
      (list (right (right so1))
            (left (right so1)))
      (gapply (to-cat nil lambda-pairing) (list (right so1) so1))))


(define-test gapply-bool-id :parent lambda.trans-eval
  (is obj-equalp
      (right so1)
      (gapply
       (to-cat nil (lambda:lamb (list (coprod so1 so1)) (geb.lambda:index 0)))
       (list (right so1) so1)))
  (is obj-equalp
      (left so1)
      (gapply
       (to-cat nil (lambda:lamb (list (coprod so1 so1)) (geb.lambda:index 0)))
       (list (left so1) so1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;               Compile checked term tests                  ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-test compile-checked-term :parent geb.lambda.trans
  (is obj-equalp
      (to-cat nil (lambda:unit))
      (geb:terminal so1)
      "compile unit"))

(define-test stlc-ctx-to-mu :parent compile-checked-term
  (is equalp
      (lambda:stlc-ctx-to-mu nil)
      so1
      "compile in a nil context"))

(define-test fold-singleton-unit-context :parent compile-checked-term
  (is obj-equalp
      (lambda:stlc-ctx-to-mu (list so1))
      (prod so1 so1)
      "fold singleton unit context"))

(define-test fold-singleton-bool-context :parent compile-checked-term
  (is obj-equalp
      (lambda:stlc-ctx-to-mu (list geb-bool:bool))
      (prod geb-bool:bool so1)
      "fold singleton bool context"))

(define-test fold-multi-object-context :parent compile-checked-term
  (is obj-equalp
      (lambda:stlc-ctx-to-mu  (list geb-bool:bool so0 so1))
      (prod geb-bool:bool (prod so0 (prod so1 so1)))
      "fold multi-object context"))

(define-test so-hom-so1-so1 :parent compile-checked-term
  (is equalp
      (lambda:so-hom so1 so1)
      so1
      "compute hom(so1,so1)"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                Vampir Extractions Tests                   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; vampir extraction tests, make better tests please.

(define-test lambda-vampir-test :parent geb.lambda.trans
  (of-type list (to-circuit
                 (lambda:left so1 (lambda:unit))
                 :tc_unit_to_bool_left))
  (of-type list (to-circuit
                 (lambda:right so1 (lambda:unit))
                 :tc_unit_to_bool_right))
  (of-type list (to-circuit (lambda:fst pair-bool-stlc) :tc_fst_bool))
  (of-type list (to-circuit (lambda:unit) :tc_unit_to_unit))
  (of-type list (to-circuit (to-cat (list so0)
                                    (lambda:absurd so1 (lambda:index 0)))
                            :tc_void_to_unit))
  (of-type list issue-58-circuit))
