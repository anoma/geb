(in-package geb-docs/docs)

(pax:defsection @glossery (:title "Glossery")
  (@closed-type pax:glossary-term)
  (@open-type pax:glossary-term)
  (@clos pax:glossary-term))

(pax:define-glossary-term
    @closed-type (:title "closed type")
    "A closed type is a type that can not be extended dynamically.
A good example of this kind of term is an ML
[ADT](https://en.wikipedia.org/wiki/Algebraic_data_type)

```haskell
data Tree = Empty
          | Leaf Int
          | Node Tree Tree
```

In our lisp code we have a very similar convention

```lisp
(in-package :geb.spec)

(deftype substmorph ()
  `(or substobj
       alias
       comp init terminal case pair distribute
       inject-left inject-right
       project-left project-right))
```

This type is closed, as only one of GEB:SUBSTOBJ, GEB:INJECT-LEFT,
GEB:INJECT-RIGHT etc can form the GEB:SUBSTMORPH type

The main benefit of this form is that we can be exhaustive over what can be found in GEB:SUBSTBOOL

```lisp
(defun so-hom-obj (x z)
  (match-of substobj x
    (so0          so1)
    (so1          z)
    (alias        (so-hom-obj (obj x) z))
    ((coprod x y) (prod (so-hom-obj x z)
                        (so-hom-obj y z)))
    ((prod x y)   (so-hom-obj x (so-hom-obj y z)))))
```
If we forget a case, like GEB:COPROD it wanrs us with an non exhaustion warning.

Meaning that if we update definitions this works well.

------


The main downside is that we can not extend the type after the fact,
meaning that all interfaces on SO-HOM-OBJ must take the unaltered
type. This is in stark contrast to @OPEN-TYPES. To find out more about
the trade offs and usage in the code-base read the section @OPEN-CLOSED.
")

(pax:define-glossary-term
    @open-type (:title "open type")
    "An open type is a type that can be extended by user code down the
line. A good example of this in ML is the [type class
system](https://en.wikipedia.org/wiki/Type_class) found in Haskell.

In our code base, it is simple as creating a @CLOS term

```lisp
(defclass <substobj> (direct-pointwise-mixin) ())
```

and to create a child of it all we need to do is.

```lisp
(defclass so0 (<substobj>) ())
```

Now any methods on GEB:\\<SUBSTOBJ\\> will cover GEB:SO0.

-------

The main disadvantaged of these is that exhaustion can not be checked,
and thus the user has to know what methods to fill out. In a system
with a bit more checks this is not a problem in practice. To find out
more about the trade offs and usage in the code-base read the section
@OPEN-CLOSED.
")

(pax:define-glossary-term
    @clos (:title "Common Lisp Object System (CLOS)")
    "The object system found in CL. Has great features like a [Meta Object
Protocol](http://community.schemewiki.org/?meta-object-protocol) that
helps it facilitate extensions.")


