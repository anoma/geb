(in-package :geb-test)

(define-test geb.trans :parent geb-test-suite)

(def geb.pair-of-size-4
  (to-bitc
   (pair (->right so1 bool)
         (->left so1 bool))))

(define-test geb.trans-pair :parent geb.trans
  (is = 4 (codom geb.pair-of-size-4)
      "both objects have max size of 2, pair them size 4")
  (is = 1 (dom   geb.pair-of-size-4)
      "Our input is bool, thus 1 bit")
  (is obj-equalp #*1100 (gapply geb.pair-of-size-4 #*1)
      "Right should tag it with 1, with our 1 injected and our left should
       always be 00")
  (is obj-equalp #*1000 (gapply geb.pair-of-size-4 #*0)
      "Right should tag it with 1, with our 0 injected and our left should
       always be 00"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                    Interpreter tests                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-test geb.trans-eval :parent geb.trans)

(def bitc-yes
  (gapply (to-bitc dec:inj-yes) #*))

(def bitc-no
  (gapply (to-bitc dec:inj-no) #*))

(def bitc-maybe
  (gapply (to-bitc dec:inj-maybe) #*))

(defun bitc-pair (&rest morphisms)
  "pairs the constructors and then calls bitc. only with constructors"
  (gapply (to-bitc (apply #'pair morphisms)) #*))

(define-test geb.trans-eval-maybe :parent geb.trans-eval
  ;; merge tests
  (is equalp
      bitc-yes
      (gapply (to-bitc dec:merge-opinion)
              (bitc-pair dec:inj-maybe dec:inj-yes)))
  (is equalp
      bitc-maybe
      (gapply (to-bitc dec:merge-opinion)
              (bitc-pair dec:inj-no dec:inj-yes)))
  (is equalp
      bitc-no
      (gapply (to-bitc dec:merge-opinion)
              (bitc-pair dec:inj-no dec:inj-maybe)))
  (is equalp
      bitc-no
      (gapply (to-bitc dec:merge-opinion)
              (bitc-pair dec:inj-maybe dec:inj-no)))

  ;; promote and demote tests
  (is equalp bitc-no    (gapply (to-bitc dec:demote) bitc-no))
  (is equalp bitc-no    (gapply (to-bitc dec:demote) bitc-maybe))
  (is equalp bitc-maybe (gapply (to-bitc dec:demote) bitc-yes))
  (is equalp bitc-yes   (gapply (to-bitc dec:promote) bitc-yes))
  (is equalp bitc-yes   (gapply (to-bitc dec:promote) bitc-maybe))
  (is equalp bitc-maybe (gapply (to-bitc dec:promote) bitc-no)))
