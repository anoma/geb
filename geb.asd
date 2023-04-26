
(asdf:defsystem :geb
  :depends-on (:trivia :alexandria :serapeum :fset :fare-quasiquote-extras
                       ;; wed are only importing this for now until I
                       ;; give good instructions to update the asdf of sbcl
                       :cl-reexport
                       :mgl-pax
                       :command-line-arguments)
  :version "0.2.0"
  :description "Gödel, Escher, Bach, a categorical view of computation"
  :build-pathname "../build/geb.image"
  :entry-point "geb.entry::entry"

  :build-operation "program-op"
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
                 (:file meta)
                 (:file mixins)
                 (:file cat)))
   (:module vampir
    :serial t
    :description "The Vampir Extraction Module"
    :components ((:file package)
                 (:file spec)
                 (:file print)
                 (:file vampir)))
   (:module geb
    :serial t
    :description "The Main Geb Module"
    :depends-on (util specs)
    :components ((:file package)
                 (:file geb)
                 (:file bool)))
   (:module poly
    :serial t
    :description "Polynomial"
    :depends-on (util geb vampir specs)
    :components ((:file package)))
   (:module bits
    :serial t
    :description "Bits (Boolean Circuits)"
    :depends-on (util geb vampir specs)
    :components ((:file package)))
   (:module lambda
    :serial t
    :depends-on (geb specs)
    :description "A simple Lambda calculus model"
    :components ((:file package)
                 (:module experimental
                  :serial t
                  :description "Experimental lambda code"
                  :components
                  ((:file package)
                   (:file lambda)))
                 (:file lambda)))
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
                 (:file bits)
                 (:file bits-printer)
                 ;; HACK: to make the package properly refer to the
                 ;; right symbols
                 (:file ../util/package)))
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;; !IMPORTANT!
   ;; All trans files go here, as they rely on other trans files
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   (:module trans
    :description "All the trans modules so they can all know about the
    other transformation functions before we compile them!"
    :pathname "../src/"
    :components ((:file lambda/trans)
                 (:file geb/trans)
                 (:file poly/trans)
                 (:file bits/trans)))
   (:module entry
    :serial t
    :description "Entry point for the geb codebase"
    :depends-on (util geb vampir specs poly bits lambda)
    :components ((:file package)
                 (:file entry))))
  :in-order-to ((asdf:test-op (asdf:test-op :geb/test))))

(asdf:defsystem :geb/gui
  :depends-on (:geb :mcclim :clim :bordeaux-threads :mcclim-dot)
  :description "geb gui presenter"
  :pathname "src/gui/"
  :serial t
  :components ((:module graphing
                :serial t
                :description "The graphing algorithm"
                :components ((:file package)
                             (:file core)
                             (:file passes)))
               (:file package)
               (:file common-abstractions)
               (:file shapes)
               (:file present-graph)
               (:file show-view)
               (:file stick-view)
               (:file list-view)
               (:file gui)
               (:file commands))
  :in-order-to ((asdf:test-op (asdf:test-op :geb/test))))

(asdf:defsystem :geb/test
  :depends-on (:geb :parachute :geb/gui)
  :description "Testing geb"
  :pathname "test/"
  :serial t
  :components
  ((:file package)
   (:file meta)
   (:file geb)
   (:file lambda)
   (:file lambda-experimental)
   (:file lambda-conversion)
   (:file poly)
   (:file bits)
   (:file pipeline)
   (:module gui
    :serial t
    :components ((:file test)
                 (:file graphing)))
   (:file run-tests))
  :perform (asdf:test-op (o s)
                         (uiop:symbol-call :geb-test :run-tests-error)))


(asdf:defsystem :geb/documentation
  :depends-on (:geb :mgl-pax/navigate :MGL-PAX/FULL :cl-environments
               :geb/test :pythonic-string-reader
               :geb/gui)
  :description "geb full documentation exploration"
  :pathname "docs/"
  :serial t
  :components ((:file package)
               (:file glossery)
               (:file documentation))
  :in-order-to ((asdf:test-op (asdf:test-op :geb/test))))


(defun load-docs-with-symbol-macro (&optional (ql nil))
  (if ql
      (progn (ql:quickload :mgl-pax/navigate)
             (ql:quickload :geb/documentation))
      (progn (asdf:load-system :mgl-pax/navigate)
             (asdf:load-system :geb/documentation))))

(defun make-system ()
  (handler-case (asdf:load-system :geb)
    (error (c)
      (declare (ignorable c))
      (ql:quickload :geb)))
  (asdf:make :geb))
