(in-package :geb-bool)

;; I need a defadt macro, all this is all derivable, trivial so even?

;; Also I want a variable to control so Ι can expand these names
;; only, as Ι pretty print.

(def true (alias true (right-> so1 so1)))

(def false (alias false (left-> so1 so1)))

(def bool (alias bool (coprod so1 so1)))

;; TODO make my own custom def macro so they are with the defn!

(setf (documentation 'bool 'pax:symbol-macro)
      "The Boolean Type, composed of a coproduct of two unit objects ")

(setf (documentation 'true 'pax:symbol-macro)
      "The true value of a boolean type. In this case we've defined true as
the right unit")

(setf (documentation 'false 'pax:symbol-macro)
      "The false value of a boolean type. In this case we've defined true as
the left unit")

;; TODO :: refactor this to remove the x call, and instead use
;; (terminal (codomain f))
(defun so-const (f x)
  "composition of the term and it's terminal type" ; ???
  ;; Is this right!? hard to tell with Idris's unification
  (comp f (terminal x)))

(defun so-uncurry (x y f)
  x y f)

;; we are seeing a trend in definitions!
;; this gives us a peek at what to make macros over
(def not
  (alias not
         (mcase true false)))

(setf (documentation 'not 'pax:symbol-macro)
      "Turns a TRUE into a FALSE and vice versa")

(def and
  (pair (so-const false bool)
        bool))

(def or
  (pair bool
        (so-const true bool)))

;; (def sand
;;   (alias and
;;          ))
