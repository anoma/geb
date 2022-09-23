(in-package :geb)

(deftype substobj ()
  `(or alias prod coprod so0 so1))

;; we say that id doesn't exist, as we don't need the tag. If we find
;; that to ill typed (substobj is a substmorph as far as type checking
;; is concerned without an explicit id constrcutor), then we can
;; include it and remove it from the or type here.
(deftype substmorph ()
  `(or substobj
       alias
       comp init terminal case pair distribute
       inject-left inject-right
       project-left project-right))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Subst Constructor Objects
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defclass alias ()
  ((name :initarg :name
         :accessor name
         :type     symbol
         :documentation "The name of the GEB object")
   (obj :initarg :obj
        :accessor obj
        :documentation "The underlying geb object"))
  (:documentation "an alias for a geb object"))

;; these could be keywords, but maybe in the future not?
(defclass so0 ()
  ()
  (:documentation "The Initial/Unit Object"))

(defclass so1 ()
  ()
  (:documentation "The Terminal/Void Object"))

;; please make better names and documentation strings!

(defclass prod ()
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :documentation ""))
  (:documentation "the product"))

(defclass coprod ()
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :documentation ""))
  (:documentation "the coproduct"))


;; please make better names

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Subst Morphism Objects
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defclass comp ()
  ((mcar :initarg :mcar
         :accessor mcar
         :type substmorph
         :documentation "The first composed morphism")
   (mcadr :initarg :mcadr
          :type substmorph
          :accessor mcadr
          :documentation "the second morphism"))
  (:documentation "Composition of morphism"))

(defclass init ()
  ((obj :initarg :obj
        :accessor obj
        :type substobj
        :documentation ""))
  (:documentation "The initial Morphism"))

(defclass terminal ()
  ((obj :initarg :obj
        :accessor obj
        :type substobj
        :documentation ""))
  (:documentation "The terminal Morhpism"))

;; Please name all of these better plz

(defclass inject-left ()
  ((mcar :initarg :mcar
         :accessor mcar
         :type substobj
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :type substobj
          :documentation ""))
  (:documentation ""))

(defclass inject-right ()
  ((mcar :initarg :mcar
         :accessor mcar
         :type substobj
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :type substobj
          :documentation ""))
  (:documentation ""))

(defclass case ()
  ((mcar :initarg :mcar
         :accessor mcar
         :type substmorph
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :type substmorph
          :documentation ""))
  (:documentation "Casing on objects"))

(defclass pair ()
  ((mcar :initarg :mcar
         :accessor mcar
         :type substmorph
         :documentation "Head of the pair cell")
   (mcadr :initarg :mcdr
          :accessor mcdr
          :type substmorph
          :documentation "Tail of the pair cell"))
  (:documentation "Consing Morphisms"))

(defclass project-left ()
  ((mcar :initarg :mcar
         :accessor mcar
         :type substobj
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :type substobj
          :documentation ""))
  (:documentation ""))

(defclass project-right ()
  ((mcar :initarg :mcar
         :accessor mcar
         :type substobj
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :type substobj
          :documentation ""))
  (:documentation ""))

(defclass distribute ()
  ((mcar :initarg :mcar
         :accessor mcar
         :type substobj
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :type substobj
          :documentation "")
   (mcaddr :initarg :mcaddr
           :accessor mcaddr
           :type substobj
           :documentation ""))
  (:documentation "The distribute law"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Constructors for the base types
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; this is considered bad style, one should call their constructors
;; make, but it does not matter

(defparameter *so0* (make-instance 'so0))
(def so0 *so0*)
(defparameter *so1* (make-instance 'so1))
(def so1 *so1*)

(-> prod (t t) prod)
(defun prod (car cadr)
  (values
   (make-instance 'prod :mcar car :mcadr cadr)))

(-> coprod (t t) coprod)
(defun coprod (car cadr)
  (values
   (make-instance 'coprod :mcar car :mcadr cadr)))

(defmacro alias (name obj)
  `(make-alias :name ',name :obj ,obj))

(-> make-alias (&key (:name symbol) (:obj t)) alias)
(defun make-alias (&key name obj)
  (values
   (make-instance 'alias :name name :obj obj)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Constructors for the morphism constructors
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; we could type the objects more if wanted

(-> comp (substmorph substmorph) comp)
(defun comp (car cadr)
  (values
   (make-instance 'comp :mcar car :mcadr cadr)))

(-> init (substobj) init)
(defun init (obj)
  (values
   (make-instance 'init :obj obj)))

(-> terminal (substobj) terminal)
(defun terminal (obj)
  (values
   (make-instance 'terminal :obj obj)))

(-> left-> (substobj substobj) inject-left)
(defun left-> (mcar mcadr)
  "injects left constructor"
  (values
   (make-instance 'inject-left :mcar mcar :mcadr mcadr)))

(-> right-> (substobj substobj) inject-right)
(defun right-> (mcar mcadr)
  "injects right constructor"
  (values
   (make-instance 'inject-right :mcar mcar :mcadr mcadr)))

(-> <-left (substobj substobj) project-left)
(defun <-left (mcar mcadr)
  "projects left constructor"
  (values
   (make-instance 'project-left :mcar mcar :mcadr mcadr)))

(-> <-right (substobj substobj) project-right)
(defun <-right (mcar mcadr)
  "projects right constructor"
  (values
   (make-instance 'project-right :mcar mcar :mcadr mcadr)))

(-> mcase (substmorph substmorph) case)
(defun mcase (mcar mcadr)
  (values
   (make-instance 'case :mcar mcar :mcadr mcadr)))

(-> pair (substmorph substmorph) pair)
(defun pair (mcar mcdr)
  (values
   (make-instance 'pair :mcar mcar :mcdr mcdr)))

(-> distribute (substobj substobj substobj) distribute)
(defun distribute (mcar mcadr mcaddr)
  (values
   (make-instance 'distribute :mcar mcar :mcadr mcadr :mcaddr mcaddr)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Pattern Matching conveniences
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro make-pattern (object-name &rest constructor-names)
  "make pattern matching position style instead of record style. This
removes the record constructor style, however it can be brought back
if wanted"
  `(trivia.level2:defpattern ,object-name
       (&optional ,@constructor-names)
     (list 'and
           (list 'type ',object-name)
           ,@(mapcar (lambda (x)
                       `(list 'trivia.level2:access '',x ,x))
                     constructor-names))))

;; less safe than I wanted due to the names can be out of sync, but
;; w/e I can fix it with a better defclass macro
(make-pattern alias  name obj)
(make-pattern prod   mcar mcadr)
(make-pattern so1    mcar mcadr)
(make-pattern so0    mcar mcadr)
(make-pattern coprod mcar mcadr)
(make-pattern init          obj)
(make-pattern terminal      obj)
(make-pattern comp          mcar mcadr)
(make-pattern inject-left   mcar mcadr)
(make-pattern inject-right  mcar mcadr)
(make-pattern case          mcar mcadr)
(make-pattern pair          mcar mcadr)
(make-pattern project-left  mcar mcadr)
(make-pattern project-right mcar mcadr)
(make-pattern distribute    mcar mcadr mcaddr)
