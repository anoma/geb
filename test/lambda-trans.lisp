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

(def proper-not
  (lambda:lamb
   (list (coprod so1 so1))
   (lambda:case-on (lambda:index 0)
                   (lambda:right so1 (lambda:index 0))
                   (lambda:left so1 (lambda:index 0)))))

(def lambda-pairing
  (lambda:lamb (list geb-bool:bool)
               (lambda:pair (lambda:right so1 (lambda:index 0))
                            (lambda:left so1 (lambda:index 0)))))

(def bool-id
  (lambda:lamb (list (coprod so1 so1)) (geb.lambda:index 0)))

(def case-error-left
  (lambda:case-on (lambda:left so1 (lambda:unit))
                  (lambda:err so1)
                  (lambda:unit)))

(def case-error-right
  (lambda:case-on (lambda:left so1 (lambda:unit))
                  (lambda:unit)
                  (lambda:err so1)))

(def case-error-top
  (lambda:case-on (lambda:err (coprod so1 so1))
                  (lambda:unit)
                  (lambda:unit)))

(def context-dependent-case
  (lambda:case-on (lambda:index 0)
                  (lambda:err so1)
                  (lambda:unit)))

(def one-bit
  (lambda:bit-choice 1))

(def plus-one
  (lambda:lamb (list (nat-width 24)) (lambda:plus (lambda:index 0)
                                                  one-bit)))
(def minus-one
  (lambda:lamb (list (nat-width 24)) (lambda:minus (lambda:index 0)
                                                   one-bit)))

(def less-than-1 (lambda:lamb (list (nat-width 24))
                              (lambda:case-on (lambda:lamb-lt (lambda:index 0)
                                                              one-bit)
                                              (lambda:bit-choice 0)
                                              (lambda:bit-choice 1))))
(def is-1 (lambda:lamb (list (nat-width 24))
                       (lambda:case-on (lambda:lamb-eq (lambda:index 0)
                                                       one-bit)
                                       (lambda:bit-choice 0)
                                       (lambda:bit-choice 1))))

(def issue-58-circuit
  (to-circuit
   (lambda:case-on
    (lambda:left so1 (lambda:unit))
    (lambda:lamb (list so1) (lambda:right so1 (lambda:unit)))
    (lambda:lamb (list so1) (lambda:left so1 (lambda:unit))))
   :tc_issue_58))

(defparameter *issue-94-circuit*
  (lambda:app (lambda:lamb (list (lambda:fun-type
                                  (lambda:fun-type (coprod so1 so1)
                                                   (coprod so1 so1))
                                  (coprod so1 so1)))
                           (lambda:app (lambda:index 0)
                                       (list (lambda:lamb (list (coprod so1 so1))
                                                          (lambda:index 0)))))
              (list (lambda:lamb (list (lambda:fun-type (coprod so1 so1)
                                                        (coprod so1 so1)))
                                 (lambda:left so1 (lambda:unit))))))


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
      (gapply (to-bitc lambda-not-with-lambda) #*1))
  (is equalp (list 0 0) (gapply (to-seqn lambda-not-with-lambda) (list 1 0 0)))
  (is equalp (list 1 0) (gapply (to-seqn lambda-not-with-lambda) (list 0 0 0)))
  (is equalp (gapply (to-seqn lambda-not-without-lambda) (list 0 0 0))
             (gapply (to-seqn lambda-not-with-lambda) (list 0 0 0)))
  (is equalp (gapply (to-seqn lambda-not-without-lambda) (list 1 0 0))
             (gapply (to-seqn lambda-not-with-lambda) (list 1 0 0))))

(define-test lambda.preserves-pair :parent lambda.trans-eval
  (is obj-equalp
      (list (right (right so1))
            (left (right so1)))
      (gapply (to-cat nil lambda-pairing) (list (right so1) so1))))


(define-test gapply-bool-id :parent lambda.trans-eval
  (is obj-equalp
      (right so1)
      (gapply
       (to-cat nil bool-id)
       (list (right so1) so1)))
  (is obj-equalp
      (left so1)
      (gapply
       (to-cat nil bool-id)
       (list (left so1) so1)))
  (is obj-equalp #*0 (gapply (to-bitc bool-id) #*0))
  (is obj-equalp #*1 (gapply (to-bitc bool-id) #*1))
  (is obj-equalp (list 0 0) (gapply (to-seqn bool-id) (list 0 0 0)))
  (is obj-equalp (list 1 0) (gapply (to-seqn bool-id) (list 1 0 0))))

(define-test lambda.not-works :parent lambda.trans-eval
  (is obj-equalp (left so1)  (gapply (to-cat nil proper-not)
                                     (list (geb:right so1) so1)))
  (is obj-equalp (right so1) (gapply (to-cat nil proper-not)
                                     (list (geb:left so1) so1)))
  (is equalp #*0 (gapply (to-bitc proper-not) #*1))
  (is equalp #*1 (gapply (to-bitc proper-not) #*0))
  (is equalp (list 0 0) (gapply (to-seqn proper-not) (list 1 0 0)))
  (is equalp (list 1 0) (gapply (to-seqn proper-not) (list 0 0 0))))

(define-test error-handling-case :parent lambda.trans-eval
  (is obj-equalp (left so1) (gapply (to-cat nil case-error-left)
                                    (list so1)))
  (is obj-equalp (right so1) (gapply (to-cat nil case-error-right)
                                     (list so1)))
  (is obj-equalp (left so1) (gapply (to-cat nil case-error-top)
                                    (list so1)))
  (is obj-equalp (left so1) (gapply (to-cat (list (coprod so1 so1))
                                            context-dependent-case)
                                    (list (right
                                           (left
                                            (right so1)))
                                          so1)))
  (is obj-equalp (right so1) (gapply (to-cat (list (coprod so1 so1))
                                             context-dependent-case)
                                     (list (right
                                            (right
                                             (right so1)))
                                           so1))))

(define-test arithmetic-compilation :parent lambda.trans-eval
  (is obj-equalp 1 (gapply (to-cat nil plus-one) (list 0 so1)))
  (is obj-equalp 2 (gapply (to-cat nil plus-one) (list 1 so1)))
  (is obj-equalp (list 1) (gapply (to-seqn plus-one) (list 0 0)))
  (is obj-equalp (list 2) (gapply (to-seqn plus-one) (list 1 0)))
  (is obj-equalp 0 (gapply (to-cat nil less-than-1) (list 0 so1)))
  (is obj-equalp 1 (gapply (to-cat nil less-than-1) (list 1 so1)))
  (is obj-equalp (list 0) (gapply (to-seqn less-than-1) (list 0 so1)))
  (is obj-equalp (list 1) (gapply (to-seqn less-than-1) (list 1 so1)))
  (is obj-equalp 0 (gapply (to-cat nil is-1) (list 1 so1)))
  (is obj-equalp 1 (gapply (to-cat nil is-1) (list 0 so1)))
  (is obj-equalp (list 0) (gapply (to-seqn is-1) (list 1 so1)))
  (is obj-equalp (list 1) (gapply (to-seqn is-1) (list 0 so1))))

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

(define-test issue-94-compiles :parent geb.lambda.trans
  (parachute:finish
   (geb.entry:compile-down :stlc t
                           :entry "geb-test::*issue-94-circuit*"
                           :stream nil)))
