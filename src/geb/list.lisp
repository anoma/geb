(in-package :geb-list)

(defparameter *nil* (alias nil (so1)))

(defparameter *cons-type* (reference 'cons))

(defparameter *list*
  (alias list
         (coprod *nil* *cons-type*)))

;; we should register this somewhere for checking if we care
(defparameter *canonical-cons-type*
  (opaque 'cons
          (prod geb-bool:bool *list*)))

(defparameter *cons*
  (alias cons-μ
         (opaque-morph (prod geb-bool:bool *list*)
                       :codom *cons-type*)))

(defparameter *car*
  (alias car
         (opaque-morph (<-left geb-bool:bool *list*)
                       :dom *cons-type*)))

(defparameter *cdr*
  (alias cdr
         (opaque-morph (<-right geb-bool:bool *list*)
                       :dom *cons-type*)))

(def cons->list
  (->right *nil* *cons-type*))

(def nil->list
  (->left *nil* *cons-type*))

(defun cons-on-list (terminal-morphism)
  "Cons an element onto a list, assuming our value can be created from
[SO1][class]"
  (comp *cons* (pair (comp terminal-morphism (terminal *list*))
                     *list*)))


;; let the optimizer handle this
(defun cons-on-nil (terminal-morphism)
  "Cons an element onto a nil, assuming our value can be created from
[SO1][class]"
  (comp (cons-on-list terminal-morphism)
        nil->list))

;; let the optimizer handle this
(defun cons-on-cons (terminal-morphism)
  "Cons an element onto a cons, assuming our value can be created from
[SO1][class]"
  (comp (cons-on-list terminal-morphism)
        cons->list))

(def silly-example
  (comp (mcase nil->list
               (comp cons->list (cons-on-cons geb-bool:true)))
        cons->list *cons*))

(def silly-example-cdring
  (comp (cons-on-cons geb-bool:false)
        (mcase (cons-on-nil geb-bool:true)
               *cons-type*)
        *cdr* (cons-on-list geb-bool:true) *cdr*))
