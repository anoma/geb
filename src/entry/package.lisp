(in-package :geb.utils)

(muffle-package-variance
 (defpackage #:geb.entry
   (:documentation "Entry point for the geb codebase")
   (:local-nicknames  (#:poly #:geb.poly)
                      (:lambda     :geb.lambda))
   (:use #:serapeum #:common-lisp)))


(in-package :geb.entry)

(pax:defsection @geb-entry (:title "Geb as a binary")
  "The standard way to use geb currently is by loading the code into
one's lisp environment

```lisp
(ql:quickload :geb)
```

However, one may be interested in running geb in some sort of
compilation process, that is why we also give out a binary for people
to use

An example use of this binary is as follows

```bash
mariari@Gensokyo % ./geb.image -i \"foo.lisp\" -e \"geb.lambda.spec::*entry*\" -l -v -o \"foo.pir\"

mariari@Gensokyo % cat foo.pir
def *entry* x {
  0
}%
mariari@Gensokyo % ./geb.image -i \"foo.lisp\" -e \"geb.lambda.spec::*entry*\" -l -v
def *entry* x {
  0
}

./geb.image -h
  -i --input                      string   Input geb file location
  -e --entry-point                string   The function to run, should be fully qualified I.E.
                                           geb::my-main
  -l --stlc                       boolean  Use the simply typed lambda calculus frontend
  -o --output                     string   Save the output to a file rather than printing
  -v --vampir                     string   Return a vamp-ir expression
  -h -? --help                    boolean  The current help message

```

starting from a file *foo.lisp* that has

```lisp
(in-package :geb.lambda.spec)

(defparameter *entry*
  (typed unit geb:so1))
```

inside of it.

The command needs an entry-point (-e or --entry-point), as we are
simply call LOAD on the given file, and need to know what to
translate.

from STLC, we expect the form to be wrapped in the
GEB.LAMBDA.SPEC.TYPED which takes both the type and the value to
properly have enough context to evaluate.

It is advised to bind this to a parameter like in our example as -e
expects a symbol.

the -l flag means that we are not expecting a geb term, but rather a
lambda frontend term, this is to simply notify us to compile it as a
lambda term rather than a geb term. In time this will go away"
  (compile-down pax:function))
