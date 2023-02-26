(in-package :geb-bool)

;; I need a defadt macro, all this is all derivable, trivial so even?

;; Also I want a variable to control so Ι can expand these names
;; only, as Ι pretty print.

(def false-obj (alias false (so1)))
(def true-obj (alias true (so1)))

(def true (alias true (->right false-obj true-obj)))
(def false (alias false (->left false-obj true-obj)))

(def bool (alias bool (coprod false-obj true-obj)))

;; TODO make my own custom def macro so they are with the defn!

(setf (documentation 'bool 'pax:symbol-macro)
      "The Boolean Type, composed of a coproduct of two unit objects

```lisp
(coprod so1 so1)
```")

(setf (documentation 'true 'pax:symbol-macro)
      "The true value of a boolean type. In this case we've defined true as
the right unit")

(setf (documentation 'false 'pax:symbol-macro)
      "The false value of a boolean type. In this case we've defined true as
the left unit")

(defun so-uncurry (x y f)
  x y f)

;; we are seeing a trend in definitions!
;; this gives us a peek at what to make macros over
(def not
  (alias not
         (mcase true false)))

(setf (documentation 'not 'pax:symbol-macro)
      "Turns a TRUE into a FALSE and vice versa")

;; this is curried and,
(def cand
  (pair (const false bool)
        bool))

(def iso1
  (flet ((bool-from (x)
           (<-left bool x)))
    (mcase (comp (->left bool bool)
                 (bool-from false-obj))
           (comp (->right bool bool)
                 (bool-from true-obj)))))

(def and-on-sum
  (mcase (const false bool) bool))

(def and-more-verbose
  (comp and-on-sum iso1 (distribute bool false-obj true-obj)))

(def and
  (comp (mcase (const false (prod bool false-obj))
               (<-left bool true-obj))
        (distribute bool false-obj true-obj)))

(def or
  (pair bool
        (const true bool)))

;; (def sand
;;   (alias and
;;          ))
