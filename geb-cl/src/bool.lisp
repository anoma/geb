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

(defun so-const (f x)
  "composition of the term and it's terminal type" ; ???
  ;; Is this right!? hard to tell with Idris's unification
  (comp f (terminal x)))

(defun so-eval (x z)
  ;; should we have better ways of preserving aliases?
  (match-of substobj x
    ((alias _ x)  (so-eval x z))
    ((so0)        (comp (init z) (<-right so1 so0)))
    ((so1)        (<-left z so1))
    ((coprod a b) (mcase (comp (so-eval a z)
                               (error "idk how to hole fill"))
                         (comp (so-eval b z)
                               (error "idk how to hole fill"))))
    ((prod a b)
     a b (error "please fix"))))

(defun so-uncurry (x y f)
  x y f)

(def higher-and
  (pair bool
        ;; Is this right!? hard to tell with Idris's unification
        (so-const mtrue bool)))

(def higher-or
  ;; Is this right!? hard to tell with Idris's unification
  (pair (so-const mfalse bool)
        bool))

;; (def sand
;;   (alias and
;;          ))
