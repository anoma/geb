(geb.utils:muffle-package-variance
 (uiop:define-package #:geb-gui.core
   (:use #:geb.common)))

(in-package :geb-gui.core)

(pax:defsection @graphing-core (:title "The GEB Graphizer Core")
  "This section covers the graphing procedure in order to turn a GEB
object into a format for a graphing backend."
  ;; please write more, me.  Put this is the API section, not
  ;; here... we should talk about the backends here!!!!!!!
  "The core types that facilittate the functionality"
  (note type)
  (node class)
  (node-note class)
  (squash-note class)
  (make-note function)
  (make-squash function)
  (graphize generic-function)
  (value generic-function)
  (cons-note function)
  (apply-note function)
  (representation generic-function)
  (children       generic-function)
  (determine-text-and-object-from-node function)
  (noterize-children                   function)
  (notorize-children-with-index-schema function))


(geb.utils:muffle-package-variance
 (uiop:define-package #:geb-gui.graphing.passes
   (:mix #:geb-gui.core
         #:geb.common
         #:common-lisp)
   (:export #:@pass-manual)))

(in-package :geb-gui.graphing.passes)

(pax:defsection @pass-manual (:title "The GEB Graphizer Passes")
  "This changes how the graph is visualized, simplifying the graph in
ways that are intuitive to the user"
  (passes function))


(geb.utils:muffle-package-variance
 (uiop:define-package #:geb-gui.graphing
   (:mix #:geb-gui.core
         #:geb-gui.graphing.passes
         #:geb.common
         #:common-lisp)
   (:reexport #:geb-gui.core #:geb-gui.graphing.passes)
   (:export #:@graphing-manual)))

(in-package :geb-gui.graphing)

(pax:defsection @graphing-manual (:title "The GEB Graphizer")
  "This section covers the GEB Graph representation"
  (geb-gui.core::@graphing-core pax:section)
  (@pass-manual pax:section))
