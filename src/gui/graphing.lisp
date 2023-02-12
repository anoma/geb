(in-package #:geb-gui.graphing)

(defclass note ()
  ((value :initarg :value
        :accessor value
        :documentation "The value")
   (note :initarg :note
         :accessor note
         :documentation "A note on where the node came from")))

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
particular node."))


(defgeneric graphize (morph goals stack)
  (:documentation
   "Turns a morphism into a node graph.

Goals is a list of notes of a [NODE][class] without children, and a
note saying which morphism it came from. To be stored in the object
pointing to the goal node.

Once the morphism is done drawing and goals are done, then the stack
of morphisms are continued at, and are the children of the last goal,
or if none exist, the last drawn node."))

(-> continue-graphizing (node list list) node)
(defun continue-graphizing (node goals stack)
  "Continues the computation, applying the goals and stack as appropriate"
  goals stack
  node)

(defmethod graphize ((morph <substmorph>) goals stack)
  (assure node
    (typecase-of substmorph morph
      (substobj
       (continue-graphizing (make-instance 'node :representation morph :value morph)
                            goals
                            stack))
      (terminal (make-instance 'node
                               ;; should we be the entire moprhism or the car
                               :representation morph
                               ;; we display our object
                               :value (obj morph)
                               :children (graphize (shallow-copy-object so1)
                                                   goals
                                                   stack)))
      (alias)
      (init )
      (case)
      (inject-left )
      (inject-right )
      (comp )
      (pair)
      (distribute)
      (project-left)
      (project-right)
      (otherwise
       (geb.utils:subclass-responsibility morph)))))
