(pax:define-package #:geb-docs/docs
  (:use #:cl)
  (:import-from #:geb
                #:@geb)
  (:import-from #:geb.mixins
                #:@mixins)
  (:export build-docs))

(in-package geb-docs/docs)

(pax:defsection @index (:title "The GEB Manual")
  "Welcome to the GEB project"
  (@geb    pax:section)
  (@mixins pax:section))

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
