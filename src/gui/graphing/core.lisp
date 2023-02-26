(in-package #:geb-gui.core)

(deftype note ()
  "A note is a note about a new node in the graph or a note about a
NODE which should be merged into an upcoming NODE.

An example of a [NODE-NOTE][class] would be in the case of pair

```lisp
(pair g f)
```

```
               Π₁
     --f--> Y------
X----|            |-----> [Y × Z]
     --g--> Z-----
               Π₂
```



An example of a [MERGE-NOTE][class]

```lisp
(Case f g)
(COMP g f)
```

```
           χ₁
         -------> X --f---\
[X + Y]--|                ---> A
         -------> Y --g---/
           χ₂

X -f-> Y --> Y -g-> Z
```

Notice that in the pair case, we have a note and a shared node to
place down, where as in both of the [MERGE-NOTE][class] examples, the
Note at the end is not pre-pended by any special information"
  `(or node-note squash-note))

(defclass node-note ()
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
         :documentation "The representation value that made the note")))

(defclass squash-note ()
  ((value :initarg :value
          :accessor value
          :type node
          :documentation "The value"))
  (:documentation "This note should be squashed into another note and or node."))

(defclass node (meta-mixin)
  ;; this is the data we end up showing
  (;; this is the real data this is representing
   (value :initarg :value
          :accessor value
          :documentation "The value to display")
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


(defgeneric graphize (morph notes)
  (:documentation
   "Turns a morphism into a node graph.

The NOTES serve as a way of sharing and continuing computation.

If the NOTE is a :SHARED NOTE then it represents a [NODE][class]
without children, along with saying where it came from. This is to be
stored in parent of the NOTE

If the NOTE is a :CONTINUE NOTE, then the computation is continued at
the spot.

The parent field is to set the note on the parent if the NOTE is going
to be merged"))

(-> continue-graphizing (node list) node)
(defun continue-graphizing (node notes)
  "Continues the computation, applying the NOTES as appropriate"
  (apply-notes node notes))

(defmethod graphize ((morph <substmorph>) notes)
  (assure node
    (cond
      ((and (has-aliasp morph)
            (typep morph '<substobj>))
       (let ((node (continue-graphizing
                    (make-instance 'node :representation morph :value morph)
                    notes))
             (name (meta-lookup morph :alias)))
         (with-slots (value) node
           (setf value (make-alias :name name :obj value))
           node)))
      ((has-aliasp morph)
       (let ((node-codom (make-note :from morph
                                    :note (symbol-name (meta-lookup morph :alias))
                                    :value (graphize (codom morph) notes)))
             ;; TODO :: Replace me with the full (obj morph) instead.
             (node (make-squash :value (graphize (dom morph) nil))))
         (apply-note node node-codom)
         (value node)))
      (t
       (typecase-of substmorph morph
         ((or terminal init distribute inject-left inject-right project-left project-right)
          ;; Since there is no note in this case, this
          ;; representation will serve as the note as to
          ;; how we should annotate the arrow.
          (make-instance 'node :representation morph
                               :value (dom morph)
                               :children (list (graphize (codom morph) notes))))
         (substobj
          (continue-graphizing (make-instance 'node :representation morph :value morph)
                               notes))
         ;; (comp g f)
         ;; X --f--> Y --g--> Z
         (comp
          (graphize (mcadr morph)
                    (list (make-squash :value (graphize (mcar morph) notes)))))
         ;; (case g f)
         ;;             χ₁
         ;;           ------> X ----g----
         ;; [X × Y]--|                  |---> A
         ;;           ------> Y ----f----
         ;;             χ₂
         (case
             (let ((goal (make-squash :value (graphize (codom morph) nil))))
               (flet ((make-child (node)
                        (graphize node (cons-note goal notes))))
                 (notorize-children-with-index-schema
                  "χ"
                  (make-instance 'node
                                 :representation morph
                                 :value (dom morph)
                                 :children (list (make-child (mcar morph))
                                                 (make-child (mcadr morph))))))))
         ;; (pair g f)
         ;;                Π₁
         ;;      ---g--> Y ------
         ;;     /                \
         ;; X---                  ---> [Y × Z]
         ;;     \                /
         ;;      ---f--> Z ------
         ;;                Π₂
         (pair
          (let ((goal (graphize (codom morph) nil)))
            (flet ((make-child (node note)
                     (graphize node
                               (cons-note (make-note :from morph
                                                     :note note
                                                     :value goal)
                                          notes))))
              (cut-children
               (make-instance 'node
                              :value (dom morph)
                              :representation morph
                              :children (list (make-child (mcar morph) "Π₁")
                                              (make-child (mcdr morph) "Π₂")))))))
         (otherwise
          (geb.utils:subclass-responsibility morph)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; cutting a node
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(-> cut-node (node) list)
(defun cut-node (node)
  "removes a node from the graph preserving the NOTEs between the node
and it's children.

Creates a list of notes that preserve the original intent of the link"
  (mapcar (lambda (x)
            (let ((note (determine-text-and-object-from-node node x)))
              (make-note :from (cadr note)
                         :note (car note)
                         :value x)))
          (children node)))

(-> cut-children (node) node)
(defun cut-children (node)
  "Removes the direct CHILDREN from the graph, connecting the grand
CHILDREN to the current node, preserving any notes that may have exited"
  (let* ((noted-node (make-squash :value node))
         (grand-kids (mapcan #'cut-node (children node))))
    (setf (children node) nil)
    (dolist (c (reverse grand-kids) node)
      (apply-note noted-node c))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Noterizing Children
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(-> notorize-children-with-index-schema (string node) node)
(defun notorize-children-with-index-schema (prefix node)
  "Notorizes the node with a prefix appended with the subscripted number"
  (noterize-children
   node
   (lambda (x index)
     (declare (ignore x))
     (format nil "~A~A" prefix (number-to-under index)))))

(-> noterize-children (node (-> (node fixnum) string)) node)
(defun noterize-children (node func)
  "Applies a specified note to the CHILDREN of the NODE.

It does this by applying FUNC on all the CHILDREN and the index of the
child in the list"
  (let* ((note-node (make-squash :value node))
         (children  (children node))
         (len       (length children)))
    (setf (children node) nil)
    (mapc (lambda (x index)
            (apply-note note-node
                        (make-note :from (value x)
                                   :note (funcall func x index)
                                   :value x)))
     (reverse children)
     (alexandria:iota len :step -1 :start len))
    node))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Note Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun make-note (&rest initargs &key from note value &allow-other-keys)
  (declare (ignore from note value))
  (apply #'make-instance 'node-note initargs))

(defun make-squash (&rest initargs &key value &allow-other-keys)
  (declare (ignore value))
  (apply #'make-instance 'squash-note initargs))

(defmethod print-object ((note node-note) stream)
  (print-unreadable-object (note stream :type nil)
    (with-slots (value note) note
      (format stream "NOTE: ~A ~@_VALUE: ~A" note value))))

(defmethod print-object ((note squash-note) stream)
  (print-unreadable-object (note stream :type nil)
    (with-slots (value) note
      (format stream "VALUE: ~A" value))))

(-> update-meta-data-with-note (node node-note) t)
(defun update-meta-data-with-note (node note)
  "Inserts the NOTE into the NODE"
  (with-slots (value note from) note
    (meta-insert node value (list note from))))

(-> cons-note (note list) list)
(defun cons-note (note notes)
  "Adds a note to the notes list."
  (if (null notes)
      (list note)
      (etypecase-of note (car notes)
        (node-note
         (cons note notes))
        (squash-note
         (etypecase-of note note
           (node-note   (cons (make-note :from (from note)
                                         :note (note note)
                                         :value (value (car notes)))
                              (cdr notes)))
           (squash-note notes))))))

;; node, squash

(-> apply-note (note note) node)
(defun apply-note (note-to-be-on note)
  "Here we apply the NOTE to the NODE.

In the case of a new node, we record down the information in the note,
and set the note as the child of the current NODE. The NODE is
returned.

In the case of a squash-note, we instead just return the squash-note
as that is the proper NODE to continue from"
  (assure node
    (etypecase-of note note
      (node-note (let ((node (value note-to-be-on)))
                   (update-meta-data-with-note node note)
                   (push (value note) (children node))
                   node))
      (squash-note
       (etypecase-of note note-to-be-on
         (node-note
          (push (value note)
                (children (value note-to-be-on)))
          (value note-to-be-on))
         (squash-note
          (value note)))))))

(-> apply-notes (node list) node)
(defun apply-notes (node notes)
  "apply the NOTES onto the current NODE."
  (let* ((notes-with-node (cons-note (make-squash :value node) notes)))
    ;; collapse the nodes, these should all be nodes, due to how we
    ;; constructed it
    (mvfold (lambda (note child-note)
              (apply-note note child-note)
              child-note)
            (cdr notes-with-node)
            (car notes-with-node))
    (assure node
      (value (car notes-with-node)))))

(defun determine-text-and-object-from-node (from to)
  "Helps lookup the text from the node"
  (or (meta-lookup from to)
      (list (geb:text-name (representation from))
            (representation from))))
