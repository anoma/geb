(in-package :geb-test)

(define-test geb-seqn :parent geb-test-suite)

(define-test seqn-evaluates-and-correctly
  :parent geb-seqn
  (is obj-equalp (list 1 0) (gapply (geb.common:to-seqn geb-bool:and) (list 1 0 1 0)))
  (is obj-equalp (list 0 0) (gapply (geb.common:to-seqn geb-bool:and) (list 1 0 0 0)))
  (is obj-equalp (list 0 0) (gapply (geb.common:to-seqn geb-bool:and) (list 0 0 1 0)))
  (is obj-equalp (list 0 0) (gapply (geb.common:to-seqn geb-bool:and) (list 0 0 0 0))))

(define-test seqn-de-compose
  :parent geb-seqn
  (is obj-equalp (list 1 0) (gapply (seqn:seqn-decompose 3) (list 4)))
  (is obj-equalp (list 4) (gapply (seqn:seqn-concat 1 2) (list 1 0)))
  (is obj-equalp (list 4) (gapply (seqn:composition (seqn:seqn-concat 1 2)
                                                    (seqn:seqn-decompose 3))
                                  (list 4)))
  (is obj-equalp (list 1 0) (gapply (seqn:composition (seqn:seqn-decompose 3)
                                                      (seqn:seqn-concat 1 2))
                                    (list 1 0))))


