(in-package :geb)

(defun build-docs ()
  (mgl-pax:update-asdf-system-readmes
   geb:@geb :geb)
  (mgl-pax:update-asdf-system-html-docs
   geb:@geb :geb :target-dir (asdf/system:system-relative-pathname :geb "../docs/")))
