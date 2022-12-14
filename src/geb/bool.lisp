(in-package :geb-bool)

;; I need a defadt macro, all this is all derivable, trivial so even?

;; Also I want a variable to control so Ι can expand these names
;; only, as Ι pretty print.

(def mtrue (alias true (right-> so1 so1)))

(def mfalse (alias false (left-> so1 so1)))

(def bool (alias bool (coprod so1 so1)))

;; we are seeing a trend in definitions!
;; this gives us a peek at what to make macros over
(def snot
  (alias not
         (mcase mtrue mfalse)))

;; TODO :: refactor this to remove the x call, and instead use
;; (terminal (codomain f))
(defun so-const (f x)
  "composition of the term and it's terminal type" ; ???
  ;; Is this right!? hard to tell with Idris's unification
  (comp f (terminal x)))

(defun so-uncurry (x y f)
  x y f)

(def higher-and
  (pair (so-const mfalse bool)
        bool))

(def higher-or
  (pair bool
        (so-const mtrue bool)))

;; (def sand
;;   (alias and
;;          ))
