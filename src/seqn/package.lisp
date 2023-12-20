(in-package :geb.utils)

(muffle-package-variance
 (uiop:define-package #:geb.seqn.main
   (:mix #:geb.mixins #:geb.generics #:geb.spec
         #:geb.extension.spec #:geb.seqn.spec
         #:serapeum #:common-lisp)
   (:export :cod :dom #:@seqn-api)))

(in-package :geb.seqn.main)

(pax:defsection @seqn-api (:title "seqn api")
  "this covers the seqn api"
  (fill-in             function)
  (prod-list           function)
  (seq-max-fill        function)
  (width              (method () (<substobj>)))
  (width              (method () (<natobj>)))
  (inj-coprod-parallel function)
  (zero-list           function)
  (dom                 (method () (<seqn>)))
  (cod                 (method () (<seqn>)))
  (well-defp-cat       (method () (<seqn>)))
  (gapply              (method () (<seqn> t))))

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
  (to-circuit (method () (<seqn> t)))
  (test-call  function)
  (to-vampir  (method () (id t t)))
  (to-vampir  (method () (composition t t)))
  (to-vampir  (method () (parallel-seq t t)))
  (to-vampir  (method () (fork-seq t t)))
  (to-vampir  (method () (drop-nil t t)))
  (to-vampir  (method () (remove-right t t)))
  (to-vampir  (method () (remove-left t t)))
  (to-vampir  (method () (drop-width t t)))
  (to-vampir  (method () (inj-length-left t t)))
  (to-vampir  (method () (inj-length-right t t)))
  (to-vampir  (method () (inj-size t t)))
  (to-vampir  (method () (branch-seq t t)))
  (to-vampir  (method () (shift-front t t)))
  (to-vampir  (method () (zero-bit t t)))
  (to-vampir  (method () (one-bit t t)))
  (to-vampir  (method () (seqn-add t t)))
  (to-vampir  (method () (seqn-subtract t t)))
  (to-vampir  (method () (seqn-multiply t t)))
  (to-vampir  (method () (seqn-divide t t)))
  (to-vampir  (method () (seqn-nat t t)))
  (to-vampir  (method () (seqn-concat t t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; seqn module
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(geb.utils:muffle-package-variance
 (uiop:define-package #:geb.seqn
   (:mix #:geb.mixins #:geb.generics #:geb.spec #:geb.seqn.trans
         #:geb.seqn.spec #:geb.seqn.main #:common-lisp)
   (:export #:@seqn-manual)))

(in-package :geb.seqn)

(pax:defsection @seqn-manual (:title "Seqn Specification")
  "This covers a GEB view of multibit sequences. In particular this type will
be used in translating GEB's view of multibit sequences into Vampir"
  (@seqn              pax:section)
  (@seqn-constructors pax:section)
  (@seqn-api          pax:section)
  (geb.seqn.trans::@seqb-trans pax:section))
