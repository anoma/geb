(in-package :geb.entry)

(defparameter +command-line-spec+
  '((("input" #\i)
     :type string :documentation "Input geb file location")
    (("entry-point" #\e)
     :type string :documentation "The function to run, should be fully qualified I.E. geb::my-main")
    (("stlc" #\l)
     :type boolean :optional t :documentation "Use the simply typed lambda calculus frontend")
    (("output" #\o)
     :type string :optional t :documentation "Save the output to a file rather than printing")
    (("version" #\v)
     :type boolean :optional t :documentation "Prints the current version of the compiler")
    (("vampir" #\p)
     :type string :optional t :documentation "Return a vamp-ir expression")
    (("test" #\t)
     :type boolean :optional t :documentation "Prints a test equality with public parameters")
    (("help" #\h #\?)
     :type boolean :optional t :documentation "The current help message")))

(defun entry ()
  (setf uiop:*command-line-arguments* (uiop:command-line-arguments))
  (command-line-arguments:handle-command-line
   +command-line-spec+
   #'argument-handlers
   :name "geb"))

(defparameter *no-input-text*
  "Please provide an input file with -p or see the help command with -h")

(defun argument-handlers (&key help stlc output input entry-point vampir test version)
  (flet ((run (stream)
           (cond (help
                  (command-line-arguments:show-option-help +command-line-spec+
                                                           :sort-names t))
                 (version
                  (format stream (asdf:component-version (asdf:find-system :geb))))
                 ((null input)
                  (format stream *no-input-text*))
                 (t
                  (load input)
                  (compile-down :vampir vampir
                                :stlc stlc
                                :entry entry-point
                                :test test
                                :stream stream)))))
    (if output
        (with-open-file (file output :direction :output
                                     :if-exists :overwrite
                                     :if-does-not-exist :create)
          (run file))
        (run *standard-output*))))

;; this code is very bad please abstract out many of the components
(defun compile-down (&key vampir stlc entry test (stream *standard-output*))
  (let* ((name        (read-from-string entry))
         (eval        (eval name))
         (vampir-name (renaming-scheme (intern (symbol-name name) 'keyword))))
    (cond ((and vampir stlc test)
           (let ((circuit (to-circuit eval vampir-name)))
             (geb.vampir:extract (append circuit
                                         (geb.seqn.trans:test-call
                                          (car circuit)))
                                 stream)
             (format stream ";")))
          ((and vampir stlc)
           (geb.vampir:extract (to-circuit eval vampir-name) stream))
          ((and vampir test)
           (let ((circuit (to-circuit eval vampir-name)))
             (geb.vampir:extract (append circuit
                                         (geb.seqn.trans:test-call
                                          (car circuit)))
                                 stream)
             (format stream ";")))
          (stlc
           (format stream "~A" (to-cat nil eval)))
          (vampir
           (geb.vampir:extract (to-circuit eval vampir-name) stream))
          (t
           (format stream eval)))))

;; Very bad of me, copying alucard code, please move elsewhere as
;; well!!

(-> renaming-scheme (symbol) keyword)
(defun renaming-scheme (symb)
  "Renames certain names to be valid for vampir"
  ;; the n here mutates a once only list, so no mutation at all!
  ;; at least after the first substitute
  (intern
   (~>> symb symbol-name
        (substitute #\_ #\-)
        (nsubstitute #\V #\&)
        (string-trim "*")
        (nsubstitute #\V #\%))
   :keyword))
