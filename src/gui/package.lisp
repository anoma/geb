(geb.utils:muffle-package-variance
 (defpackage #:geb-gui
   (:local-nicknames (#:graph #:geb-gui.graphing))
   (:use :clim :clim-lisp)
   (:export #:@geb-exporter #:@geb-gui-manual #:@geb-exporter)))

(in-package :geb-gui)

(pax:defsection @geb-gui-manual (:title "The GEB GUI")
  "This section covers the suite of tools that help visualize geb
objects and make the system nice to work with"
  (@geb-visualizer pax:section)
  (@geb-exporter   pax:section)
  (geb-gui.graphing:@graphing-manual pax:section))

(pax:defsection @geb-visualizer (:title "Visualizer")
  "The GEB visualizer deals with visualizing any objects found in the GEB:@GEB-CATEGORIES

if the visualizer gets a GEB:@GEB-SUBSTMORPH, then it will show how
the [GEB:SUBSTMORPH][type] changes any incoming term.

if the visualizer gets a GEB:@GEB-SUBSTMU, then it shows the data
layout of the term, showing what kind of data "
  (visualize       pax:function)
  (kill-running    pax:function)
  (@visaulizer-aid pax:section))

(pax:defsection @geb-exporter (:title "Export Visualizer")
  "This works like the normal visualizer except it exports it to a
  file to be used by other projects or perhaps in papers"
  (svg pax:function))

(pax:defsection @visaulizer-aid (:title "Aiding the Visualizer")
  "One can aid the visualization process a bit, this can be done by
simply placing ALIAS around the object, this will place it
in a box with a name to better identify it in the graphing procedure.")
