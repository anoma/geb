(asdf:defsystem :geb
  :depends-on (:trivia :alexandria :serapeum :fset :fare-quasiquote-extras
                       ;; wed are only importing this for now until I
                       ;; give good instructions to update the asdf of sbcl
                       :cl-reexport
                       :mgl-pax)
  :version "0.0.1"
  :description "Gödel, Escher, Bach, a categorical view of computation"
  :author "Mariari"
  :license "MIT"
  :pathname "src/"
  :components
  ((:module util
    :serial t
    :description "Internal utility functions"
    :components ((:file package)
                 (:file utils)))
   (:module mixins
    :serial t
    :description "Mixin Utility Functions"
    :depends-on (util)
    :components ((:file package)
                 (:file mixins)))
   (:module vampir
    :serial t
    :description "The Vampir Extraction Module"
    :components ((:file package)
                 (:file spec)
                 (:file vampir)))
   (:module specs
    :serial t
    :depends-on (util mixins)
    :description "Internal utility functions"
    :components ((:file package)
                 (:file geb)
                 (:file geb-printer)
                 (:file lambda)
                 (:file poly)
                 (:file poly-printer)
                 ;; HACK: to make the package properly refer to the
                 ;; right symbols
                 (:file ../util/package)))
   (:module geb
    :serial t
    :description "The Main Geb Module"
    :depends-on (util specs)
    :components ((:file package)
                 (:file geb)
                 (:file bool)
                 (:file trans)))
   (:module poly
    :serial t
    :description "Polynomial"
    :depends-on (util geb vampir specs)
    :components ((:file package)
                 (:file trans)))
   (:module lambda
    :serial t
    :depends-on (geb specs)
    :description "A simple Lambda calculus model"
    :components ((:file package)
                 (:file lambda)
                 (:file lambda-conversion))))
  :in-order-to ((asdf:test-op (asdf:test-op :geb/test))))

(asdf:defsystem :geb/gui
  :depends-on (:geb :mcclim :clim :bordeaux-threads)
  :description "geb gui presenter"
  :pathname "src/gui/"
  :serial t
  :components ((:file package)
               (:file gui))
  :in-order-to ((asdf:test-op (asdf:test-op :geb/test))))

(asdf:defsystem :geb/test
  :depends-on (:geb :parachute)
  :description "Testing geb"
  :pathname "test/"
  :serial t
  :components
  ((:file package)
   (:file geb)
   (:file lambda)
   (:file lambda-conversion)
   (:file poly)
   (:file run-tests))
  :perform (asdf:test-op (o s)
                         (uiop:symbol-call :geb-test :run-tests)))

(asdf:defsystem :geb/documentation
  :depends-on (:geb :MGL-PAX/FULL :cl-environments
                    :geb/test :pythonic-string-reader)
  :description "geb full documentation exploration"
  :pathname "docs/"
  :serial t
  :components ((:file documentation))
  :in-order-to ((asdf:test-op (asdf:test-op :geb/test))))

