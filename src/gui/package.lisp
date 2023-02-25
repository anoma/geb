(geb.utils:muffle-package-variance
 (defpackage #:geb-gui
   (:local-nicknames (#:graph #:geb-gui.graphing))
   (:use :clim :clim-lisp)))

(in-package :geb-gui)

(pax:defsection @geb-gui-manual (:title "The GEB GUI")
  "This section covers the suite of tools that help visualize geb
objects and make the system nice to work with"
  (@geb-visualizer pax:section)
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

(pax:defsection @visaulizer-aid (:title "Aiding the Visualizer")
  "One can aid the visualization process a bit, this can be done by
simply playing [GEB:ALIAS][type] around the object, this will place it
in a box with a name to better identify it in the graphing procedure.")
