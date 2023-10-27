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
  (note pax::type)
  (node pax::class)
  (node-note pax::class)
  (squash-note pax::class)
  (make-note pax::function)
  (make-squash pax::function)
  (graphize pax::generic-function)
  (value pax::generic-function)
  (cons-note pax::function)
  (apply-note pax::function)
  (representation pax::generic-function)
  (children       pax::generic-function)
  (determine-text-and-object-from-node pax::function)
  (noterize-children                   pax::function)
  (notorize-children-with-index-schema pax::function))


(geb.utils:muffle-package-variance
 (uiop:define-package #:geb-gui.graphing.passes
   (:mix #:geb-gui.core
         #:geb.common
         #:common-lisp)))

(in-package :geb-gui.graphing.passes)

(pax:defsection @pass-manual (:title "The GEB Graphizer Passes")
  "This changes how the graph is visualized, simplifying the graph in
ways that are intuitive to the user"
  (passes pax::function))


(geb.utils:muffle-package-variance
 (uiop:define-package #:geb-gui.graphing
   (:mix #:geb-gui.core
         #:geb-gui.graphing.passes
         #:geb.common
         #:common-lisp)
   (:reexport #:geb-gui.core #:geb-gui.graphing.passes)))

(in-package :geb-gui.graphing)

(pax:defsection @graphing-manual (:title "The GEB Graphizer")
  "This section covers the GEB Graph representation"
  (geb-gui.core::@graphing-core pax:section)
  (@pass-manual pax::section))
