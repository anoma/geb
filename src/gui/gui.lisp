(in-package :geb-gui)

;; My first horrible gui attempt, lets go!

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Main Data and View
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defclass show-view (view) ())

(defparameter *the-data* nil)

(defvar *running* nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Running the application
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun visualize (object &optional (async t))
  (flet ((run ()
           (let ((*the-data* object))
             (run-frame-top-level (make-application-frame 'display-clim)))))
    (if async
        (push (bt:make-thread #'run) *running*)
        (funcall #'run))))

(defun kill-running ()
  (flet ((destroy-alive (x)
           (when (bt:thread-alive-p x)
             (bt:destroy-thread x))))
    (mapcar #'destroy-alive *running*)
    (setf *running* nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Application Frame and drawing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-application-frame display-clim ()
  ((%top-task :initform *the-data* :accessor root))
  (:panes
   (make-pane :application
              :width 600
              :height 800
              :display-function #'generate-graph
              :display-time t
              :default-view (make-instance 'show-view))
   (interactor :interactor :height 100 :width 100))
  (:layouts
   (default (vertically ()
              (9/10 make-pane)
              (1/10 interactor)))))

;; Likely will remove this, good to start with, but not useful yet.
(defun generate-graph (frame pane)
  (graph-object (root frame) pane))

(defun graph-object (object pane)
  (format-graph-from-roots
   (list object)
   #'present-object
   #'visual-children
   :stream pane
   :maximize-generations t
   :center-nodes t
   ;; :orientation :vertical
   :generation-separation 20
   :within-generation-separation 20
   :arc-drawing-options (list :line-thickness 1.4 :head-width 5)))

(defun present-object (object stream)
  (present object (presentation-type-of object) :stream stream))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Children API
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgeneric visual-children (obj)
  (:documentation "The visual-children of the given node"))

(defmethod visual-children ((obj geb.mixins:pointwise-mixin))
  (mapcar #'cdr (geb.mixins:to-pointwise-list obj)))

;; we want to visualize it in the presentation not in the graph
(defmethod visual-children ((obj geb:alias))
  nil)
(defmethod visual-children ((obj geb:prod))
  nil)

(defmethod visual-children ((obj t))
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Presentation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-presentation-method present ((object geb:alias)
                                     (type   geb:alias)
                                     (pane   extended-output-stream)
                                     (view   show-view)
                                     &key)
  (surrounding-output-with-border (pane :shape :rectangle :background +alice-blue+)
    (format pane "~W" (intern (symbol-name (geb:name object))))
    (graph-object (geb:obj object) pane)))

(define-presentation-method present ((object geb:prod)
                                     (type   geb:prod)
                                     (stream extended-output-stream)
                                     (view   show-view)
                                     &key)
  (surrounding-output-with-border (stream)
    (formatting-table (stream :x-spacing "  ")
      ;; dumb hack
      (dolist (x (serapeum:intersperse nil (geb:same-type-to-list object 'geb:prod)))
        (formatting-column (stream)
          (formatting-cell (stream :align-x :center :align-y :center)
            (if x
                (present-object x stream)
                (progn
                  (draw-line* stream 0 0 15 15)
                  (draw-line* stream 0 15 15 0)
                  (draw-circle* stream 7.5 7.5 10 :filled nil)))))))))

(define-presentation-method present ((object geb:coprod)
                                     (type   geb:coprod)
                                     (stream extended-output-stream)
                                     (view   show-view)
                                     &key)
  )

(define-presentation-method present ((object geb:<substmorph>)
                                     (type   geb:<substmorph>)
                                     (stream extended-output-stream)
                                     (view   show-view)
                                     &key)
  )

(define-presentation-method present ((object geb:<substobj>)
                                     (type   geb:<substobj>)
                                     (stream extended-output-stream)
                                     (view   show-view)
                                     &key)
  )

(define-presentation-method present ((object geb:so0)
                                     (type   geb:so0)
                                     (pane   extended-output-stream)
                                     (view   show-view)
                                     &key)
  (format pane "0"))

(define-presentation-method present ((object geb:so1)
                                     (type   geb:so1)
                                     (pane   extended-output-stream)
                                     (view   show-view)
                                     &key)
  (format pane "1"))

(define-presentation-method present ((object symbol)
                                     (type   symbol)
                                     (stream extended-output-stream)
                                     (view   show-view)
                                     &key))
;; todo remove
(define-presentation-method present ((object string)
                                     (type   string)
                                     (stream extended-output-stream)
                                     (view   show-view)
                                     &key)
  (format stream object))
