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
