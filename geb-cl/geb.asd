(asdf:defsystem :geb
  :depends-on (:trivia :alexandria :serapeum)
  :version "0.0.1"
  :description "Gödel, Escher, Bach, a categorical view of computation"
  :author "Mariari"
  :license "MIT"
  :pathname "src/"
  :components
  ((:file package)
   (:file spec    :depends-on (package))
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
  ((:file "package")
   (:file "geb")
   (:file "run-tests"))
  :perform (asdf:test-op (o s)
                         (uiop:symbol-call :geb-test :run-tests)))
