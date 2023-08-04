(in-package :geb.utils)

(muffle-package-variance
 (uiop:define-package #:geb.seqn.main
   (:mix #:geb.mixins #:geb.generics #:geb.spec
         #:geb.extension.spec #:geb.seqn.spec
         #:serapeum #:common-lisp)))

(in-package :geb.seqn.main)

(pax:defsection @seqn-api (:title "seqn api")
  "this covers the seqn api"
  (fill-in             pax:function)
  (prod-list           pax:function)
  (seq-max-fill        pax:function)
  (width              (pax:method () (<seqn>)))
  (width               pax:generic-function)
  (inj-coprod-parallel pax:function)
  (zero-list           pax:function)
  (dom    (pax:method () (<seqn>)))
  (dom    (pax:generic-function))
  (cod    (pax:method () (<seqn>)))
  (cod    (pax:generic-function)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; trans module
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(geb.utils:muffle-package-variance
 (defpackage #:geb.seqn.trans
   (:local-nicknames (#:vamp #:geb.vampir.spec))
   (:use #:geb.mixins #:geb.generics #:geb.spec
         #:geb.extension.spec #:geb.seqn.spec #:geb.seqn.main
         #:serapeum #:common-lisp)
   (:shadowing-import-from #:common-lisp #:case)
   (:shadowing-import-from #:geb.spec #:prod)))

(in-package :geb.seqn.trans)

(pax:defsection @seqb-trans (:title "Seqn Transformations")
  "This covers transformation functions from"
  (to-circuit (pax:method () (<seqn> t)))
  (to-vampir  (pax:method () (id t t)))
  (to-vampir  (pax:method () (composition t t)))
  (to-vampir  (pax:method () (parallel-seq t t)))
  (to-vampir  (pax:method () (fork-seq t t)))
  (to-vampir  (pax:method () (drop-nil t t)))
  (to-vampir  (pax:method () (remove-right t t)))
  (to-vampir  (pax:method () (remove-left t t)))
  (to-vampir  (pax:method () (drop-width t t)))
  (to-vampir  (pax:method () (inj-length-left t t)))
  (to-vampir  (pax:method () (inj-length-right t t)))
  (to-vampir  (pax:method () (inj-size t t)))
  (to-vampir  (pax:method () (branch-seq t t)))
  (to-vampir  (pax:method () (shift-front t t)))
  (to-vampir  (pax:method () (zero-bit t t)))
  (to-vampir  (pax:method () (one-bit t t)))
  (to-vampir  (pax:method () (seqn-add t t)))
  (to-vampir  (pax:method () (seqn-subtract t t)))
  (to-vampir  (pax:method () (seqn-multiply t t)))
  (to-vampir  (pax:method () (seqn-divide t t)))
  (to-vampir  (pax:method () (seqn-nat t t)))
  (to-vampir  (pax:method () (seqn-concat t t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; seqn module
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(geb.utils:muffle-package-variance
 (uiop:define-package #:geb.seqn
     (:mix #:geb.mixins #:geb.generics #:geb.spec #:geb.seqn.trans
           #:geb.seqn.spec #:geb.seqn.main #:common-lisp)))

(in-package :geb.seqn)

(pax:defsection @seqn-manual (:title "Seqn Specification")
  "This covers a GEB view of multibit sequences. In particular this type will
be used in translating GEB's view of multibit sequences into Vampir"
  (@seqn              pax:section)
  (@seqn-constructors pax:section)
  (@seqn-api          pax:section)
  (@seqn-trans        pax:section))
