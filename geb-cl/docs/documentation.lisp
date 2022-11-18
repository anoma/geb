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
  "Welcome to the GEB Project!"
  (@installation pax:section)
  (@loading pax:section))

(pax:defsection @installation (:title "installation")
  "This project uses [common lisp](https://common-lisp.net/), so a few
   dependencies are needed to get around the code-base and start hacking. Namely:

1. [lisp with quicklisp](https://lisp-lang.org/learn/getting-started/).

2. [Emacs](https://en.wikipedia.org/wiki/Emacs) along with one of the following:

    - [sly](https://github.com/joaotavora/sly)

        + [sly user manual](http://joaotavora.github.io/sly/)

    - [slime](https://github.com/slime/slime)

         + [slime user manual](http://www.chiark.greenend.org.uk/doc/slime/slime.pdf)")

(pax:defsection @loading (:title "loading")
  "Now that we have an environment setup, we can load the project, this
   can be done in a few steps.

1. Open the `REPL` (sbcl (terminal), `M-x` sly, `M-x` swank)

     - For the terminal, this is just calling the [common
       lisp](https://common-lisp.net/) implementation from the
       terminal.

          `user@system:geb-directory % sbcl`.

     - For Emacs, this is simply calling either `M-x sly` or `M-x slime`
       if you are using either [sly](https://github.com/joaotavora/sly) or [slime](https://github.com/slime/slime)


2. From Emacs: open `geb.asd` and press `C-ck` (`sly-compile-and-load-file`, or
   `swank-compile-and-load-file` if you are using swank).

Now that we have the file open, we can now load the system by
writing:

```lisp
;; only necessary for the first time!
(ql:quickload :geb/documentation)

;; if you want to load it in the future
(asdf:load-system :geb/documentation)

;; if you want to load the codbase and run tests at the same time
(asdf:test-system :geb/documentation)

;; if you want to run the tests once the system is loaded!
(geb-test:run-tests)
```")


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
