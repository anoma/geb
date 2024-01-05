(in-package :geb.mixins)

(defclass cat-morph () ()
  (:documentation
   "I offer the service of being a base categorical morphism with no
extensions"))

(defclass cat-obj () ()
  (:documentation
   "I offer the service of being a base category objects with no
extensions"))


(defgeneric dom (cat-morph)
  (:documentation "Grabs the domain of the morphism. Returns a [CAT-OBJ][class]"))

(defgeneric codom (cat-morph)
  (:documentation "Grabs the codomain of the morphism. Returns a [CAT-OBJ][class]"))

(defgeneric curry-prod (cat-morph cat-left cat-right)
  (:documentation "Curries the given product type given the
product. This returns a [CAT-MORPH][class].

This interface version takes the left and right product type to
properly dispatch on. Instances should specialize on the CAT-RIGHT argument

Use [GEB.MAIN:CURRY][function] instead."))
