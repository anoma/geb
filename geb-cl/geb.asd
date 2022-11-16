(asdf:defsystem :geb
  :depends-on (:trivia :alexandria :serapeum :fset :fare-quasiquote-extras
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
   (:module lambda
    :serial t
    :depends-on (bool)
    :description "A simple Lambda calculus model"
    :components ((:file package)
                 (:file spec)
                 (:file lambda)
                 (:file lambda-conversion)))
   (:file package :depends-on ())
   (:file spec    :depends-on (package mixins))
   (:file printer :depends-on (package spec))
   (:file geb     :depends-on (package spec))
   (:file bool    :depends-on (geb package spec)))
  :in-order-to ((asdf:test-op (asdf:test-op :geb/test))))

(asdf:defsystem :geb/test
  :depends-on (:geb :fiveam)
  :description "Testing geb"
  :pathname "test/"
  :serial t
  :components
  ((:file package)
   (:file geb)
   (:file lambda)
   (:file lambda-conversion)
   (:file run-tests))
  :perform (asdf:test-op (o s)
                         (uiop:symbol-call :geb-test :run-tests)))

(asdf:defsystem :geb/documentation
  :depends-on (:geb :fiveam :MGL-PAX/FULL)
  :description "geb full documentation exploration"
  :serial t
  :pathname "docs/"
  :serial t
  :components ((:file documentation))
  :perform (asdf:test-op (o s)
                         (uiop:symbol-call :geb-test :run-tests))
  :in-order-to ((asdf:test-op (asdf:test-op :geb/test))))

