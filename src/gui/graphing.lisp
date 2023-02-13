(in-package #:geb-gui.graphing)

(defclass note ()
  ((value :initarg :value
          :accessor value
          :type node
          :documentation "The value")
   (note :initarg :note
         :accessor note
         :documentation "A note on where the node came from")
   (from :initarg :from
         :accessor from
         :type (or <substobj> <substmorph>)
         :documentation "The representation value that made the note"))
  (:documentation
   "A note is only made in the event a node is shared, further, since the
node is shared, we should label the edge. That is what the note slot is for

a NOTE can look like π₁ or π₂ for [PROJECT-LEFT][class] and
[PROJECT-RIGHT][class] respectively

Further the FROM slot serves as a way of documenting what original
expression the arrow is coming from, as the VALUE is just the node to
share, and not information on what the arrow represents.

The NOTE and FROM information should be stored on the object in which the arrow is coming from thus.

x --> y

where x and y are elements of [NODE][class]

The information should be stored on the x [NODE][class]. If no notes
exist, then the x [NODE][class]'s REPRESENTATION is taken instead to
uniquely identify what the arrow should be labeled as and represents"))

(defclass node (meta-mixin)
  ;; this is the data we end up showing
  ((value :initarg :value
          :accessor value
          :documentation "The value to display")
   ;; this is the real data this is representing
   (representation :initarg :representation
                   :accessor representation
                   :documentation "The real data backing the presentation")
   (children :initarg :children
             :type list
             :accessor children
             :documentation "The children "))
  (:documentation "I represent a graphical node structure. I contain my children and a
value to display, along with the representation for which the node really stands for.

Further, we derive the meta-mixin, as it's important for arrow drawing
to know if we are the left or the right or the nth child of a
particular node. This information is tracked, by storing the object
that goes to it in the meta table and recovering the note."))


(defgeneric graphize (morph goals stack)
  (:documentation
   "Turns a morphism into a node graph.

Goals is a list of [NOTE][class] of a [NODE][class] without children, and a
note saying which morphism it came from. To be stored in the object
pointing to the goal node.

Once the morphism is done drawing and goals are done, then the stack
of morphisms are continued at, and are the children of the last goal,
or if none exist, the last drawn node."))

(-> continue-graphizing (node list list) node)
(defun continue-graphizing (node goals stack)
  "Continues the computation, applying the goals and stack as appropriate"
  stack
  (cond (goals
         (let ((goal (car goals)))
           (meta-insert node (value goal) (list (note goal) (from goal)))
           (error "please implement me")))
        (t
         (error "please implement me"))))

(defmethod graphize ((morph <substmorph>) goals stack)
  (assure node
    (typecase-of substmorph morph
      ((or terminal init distribute inject-left inject-right project-left project-right)
       (make-instance 'node
                      ;; Since there is no note in this case, this
                      ;; representation will serve as the note as to
                      ;; how we should annotate the arrow.
                      :representation morph
                      ;; we display our object
                      :value (dom morph)
                      :children (list (graphize (codom morph) goals stack))))
      (alias
       (let ((node (graphize (obj morph) goals stack))
             (name (name morph)))
         (with-slots (value representation) node
           (setf value          (make-alias :name name :obj value))
           (setf representation (make-alias :name name :obj representation)))))
      (substobj
       (continue-graphizing (make-instance 'node :representation morph :value morph)
                            goals
                            stack))
      ;; the `fun' cases
      (case (error "implement me"))
      (comp (error "implement me"))
      (pair (error "implement me"))
      (otherwise
       (geb.utils:subclass-responsibility morph)))))
