(in-package :geb)

(defun geb-sections ()
  (list geb:@geb))

(defun geb-pages ()
  `((:objects
     (,geb:@geb)
     :source-uri-fn
     ,(pax:make-github-source-uri-fn :geb "https://github.com/anoma/geb"))))

(defun build-docs ()
  (mgl-pax:update-asdf-system-readmes
   geb:@geb :geb)
  (mgl-pax:update-asdf-system-html-docs
   geb:@geb :geb
   :target-dir (asdf/system:system-relative-pathname :geb "../docs/")
   :pages (geb-pages)))

(pax:register-doc-in-pax-world :geb (geb-sections) (geb-pages))
