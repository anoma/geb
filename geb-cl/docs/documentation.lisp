(pax:define-package #:geb-docs/docs
  (:use #:cl)
  (:import-from #:geb
                #:@geb)
  (:import-from #:geb.mixins
                #:@mixins)
  (:export build-docs))

(in-package geb-docs/docs)

(pax:defsection @index (:title "The GEB Manual")
  "Welcome to the GEB project."
  (@links           pax:section)
  (@getting-started pax:section)
  (@model           pax:section)
  (@geb             pax:section)
  (@motivation      pax:section)
  (@mixins          pax:section))

(pax:defsection @links (:title "Links")
  "
Here is the [official repository](https://github.com/anoma/geb/tree/main/geb-cl)
and the [HTML documentation](https://anoma.github.io/geb/) for the latest version")

;; please insert more text here about category theory
(pax:defsection @model (:title "Categorical Model")
  "The GEB theoretical model is one of category theory"
  (@morphisms pax:section)
  (@objects pax:section))

(pax:defsection @morphisms (:title "Morphisms"))

(pax:defsection @objects (:title "Objects"))

(pax:defsection @getting-started (:title "Getting Started")
  "Welcome to the GEB Project")

(pax:defsection @motivation (:title "motivation"))

(defun geb-sections ()
  (list @index))

(defun geb-pages ()
  `((:objects
     (, @index)
     :source-uri-fn
     ,(pax:make-github-source-uri-fn :geb "https://github.com/anoma/geb"))))

(defun build-docs ()
  (mgl-pax:update-asdf-system-readmes
   @index :geb)
  (mgl-pax:update-asdf-system-html-docs
   @index :geb
   :target-dir (asdf/system:system-relative-pathname :geb "../docs/")
   :pages (geb-pages)))

(pax:register-doc-in-pax-world :geb (geb-sections) (geb-pages))
