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
         :documentation "The representation value that made the note")
   (merge-p :initarg :merge-p
            :accessor merge-p
            :initform nil
            :documentation "Merging the node"))
  (:documentation
   "
### As Used by the Goal

A note is only made in the event a node is shared, further, since the
node is shared, we should label the edge. That is what the note slot is for

a NOTE can look like π₁ or π₂ for [PROJECT-LEFT][class] and
[PROJECT-RIGHT][class] respectively

Further the FROM slot serves as a way of documenting what original
expression the arrow is coming from, as the VALUE is just the node to
share., and not information on what the arrow represents.

### As used by the Stack

The NOTE and FROM serves as the same function, however the VALUE is
now the continuation where to continue the computation rather than a [NODE][class]

### General Information

The NOTE and FROM information should be stored on the object in which
the arrow is coming from thus.

```
x --> y
```

where x and y are elements of [NODE][class]

The information should be stored on the x [NODE][class]. If no notes
exist, then the x [NODE][class]'s REPRESENTATION is taken instead to
uniquely identify what the arrow should be labeled as and represents


The MERGE-P value notes if we should merge the note to the node left
to it. This makes it possible to remove redundant nodes such as:

```lisp
(COMP g f)
```

```
X -f-> Y --> Y -g-> Z
```

where the Y --> Y arrow is useless

This happens in the case of a STACK, however the same behavior can be
seen in the presence of case.

```lisp
(Case f g)
```



```
           χ₁
         -------> X -f-> A --\
[X + Y]--|                   ---> A
         -------> Y -g-> A --/
           χ₂
```

One may suggest that this can be handled in a pass like
MERGE-BORING-NODES with removing them if the displayed values are the
same, however it would potentially break alias functions in the future
when they will be displayed like GEB-BOOL:NOT that are A -> A"))

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
             :initform nil
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
  (cond (goals
         (multiple-value-bind (node continue-node) (add-goals node goals)
           (continue-graphizing continue-node nil stack)
           node))
        (stack
         (with-slots (from note merge-p value) (car stack)
           (let ((note-rest (make-note :from from
                                       :note note
                                       :value (graphize value goals (cdr stack))
                                       :merge-p merge-p)))
             (apply-note node note-rest))))
        (t
         node)))

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
       ;; we should stop the graph here, graph it internally then
       ;; present it better.
       (let ((node (graphize (obj morph) goals stack))
             (name (name morph)))
         (with-slots (value representation) node
           (setf value          (make-alias :name name :obj value))
           (setf representation (make-alias :name name :obj representation))
           node)))
      (substobj
       (continue-graphizing (make-instance 'node :representation morph :value morph)
                            goals
                            stack))
      ;; the `fun' cases
      ;; g 。f ⟹ dom f --> recurse stack g
      (comp
       (graphize (mcadr morph)
                 goals
                 (cons (make-note :from morph :note "。" :value (mcar morph) :merge-p t)
                       stack)))
      (case (error "implement me"))
      (pair (error "implement me"))
      (otherwise
       (geb.utils:subclass-responsibility morph)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Note Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun make-note (&rest initargs &key from note value merge-p &allow-other-keys)
  (declare (ignore from note value merge-p))
  (apply #'make-instance 'note initargs))

(defmethod print-object ((note note) stream)
  (print-unreadable-object (note stream :type nil)
    (with-slots (value note from merge-p) note
      from
      (format stream "NOTE: ~A ~@_VALUE: ~A ~@_MERGE-P: ~A"
              note value merge-p))))

(-> toggle-merge (note) note)
(defun toggle-merge (note)
  (with-slots (value note from merge-p) note
    (assure note
      (make-note :from from :note note :value value :merge-p (not merge-p)))))

(-> update-meta-data-with-note (node note) t)
(defun update-meta-data-with-note (node note)
  "Inserts the NOTE into the NODE"
  (with-slots (value note from) note
    (meta-insert node value (list note from))))

(defun simplify (goals)
  "We remove the number of MERGE-P's such that only one can exist, and
if it does exist, it would be the very first node only


THUS:

```lisp
(list (x :merge-p nil) (y :merge-p t) (z :merge-p t))
```

would end up with

```lisp
(list (z :merge-p nil)
```
"
  (cond ((null (cdr goals))
         goals)
        ((and (merge-p (car goals)) (merge-p (cadr goals)))
         (simplify (cdr goals)))
        ((merge-p (cadr goals))
         (simplify (cons (toggle-merge (cadr goals)) (cddr goals))))
        (t
         (cons (car goals) (simplify (cdr goals))))))


(-> apply-note (node note) node)
(defun apply-note (node note)
  "Here we apply the note to the node. Updating the child and of the
node and setting any meta data as needed. The node is then returned

If the MERGE-P flag is on, then the note is considered to be the
canonical node, and no values are set, but the note itself is returned"
  (assure node
    (if (merge-p note)
        (value note)
        (progn
          (update-meta-data-with-note node note)
          (push (value note) (children node))
          node))))

(-> add-goals (node list) (values node node))
(defun add-goals (node notes)
  "Adds the goals onto the current node.

Due to the merge-p part of a note, we return two values

1. the node to be returned
2. the child node to continue the computation from
"
  (let* ((goals       (simplify notes))
         (return-node (apply-note node (car goals))))
    (values return-node
            (mvfold (lambda (node note) (apply-note node note) (value note))
                    (cdr goals)
                    (value (car goals))))))
