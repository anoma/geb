(in-package :geb-gui)

;; My first horrible gui attempt, lets go!

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Main Data and View
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defclass show-view (view)
  ((counter :initform 0 :initarg :counter :accessor counter)))

;; Graph view of products and coproducts
(defclass stick-view (show-view) ())

;; A List view of products and corpodcuts
(defclass list-view (show-view) ())

(defparameter *the-data* nil)

(defvar *running* nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Running the application
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun visualize (object &optional (async t))
  "Visualizes both GEB:@GEB-SUBSTMU and GEB:@GEB-SUBSTMORPH objects"
  (flet ((run ()
           (let ((*the-data* object))
             (run-frame-top-level (make-application-frame 'display-clim)))))
    (if async
        (push (bt:make-thread #'run) *running*)
        (funcall #'run))))

(defun kill-running ()
  "Kills all threads and open gui objects created by VISUALIZE"
  (flet ((destroy-alive (x)
           (when (bt:thread-alive-p x)
             (bt:destroy-thread x))))
    (mapcar #'destroy-alive *running*)
    (setf *running* nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Application Frame and drawing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-application-frame display-clim ()
  ((%top-task :initform *the-data* :accessor root)
   (%graph-p  :initform t :accessor graph-p)
   (counter :initform 0 :initarg :counter :accessor counter))
  (:panes
   (make-pane :application
              :width 600
              :height 800
              :display-function #'display-app
              :display-time t
              :default-view (make-instance 'show-view))
   (interactor :interactor :height 100 :width 100))
  (:layouts
   (default (vertically ()
              (9/10 make-pane)
              (1/10 interactor)))))

(defun display-app (frame pane)
  (cond ((typep (root frame) 'graph:node)
         (graph-node (root frame) pane))
        ((graph-p frame)
         (display-graph frame pane))
        (t
         (present-object (root frame) pane))))

(defun display-graph (frame pane)
  ;; cache this later
  (graph-node (graph:graphize (root frame) nil) pane))

(defun graph-node (object pane)
  (format-graph-from-roots
   (list object)
   #'present-object
   (lambda (node)
     (graph::children node))
   :stream pane
   :maximize-generations t
   :center-nodes t
   :merge-duplicates t
   ;; :orientation :vertical
   :generation-separation 50
   :within-generation-separation 20
   :arc-drawer #'my-arc-drawer
   :arc-drawing-options (list :line-thickness 1.4 :head-width 5)))

(defun my-arc-drawer (stream from-node to-node x1 y1 x2 y2
                            &rest drawing-options
                            &key &allow-other-keys)
  (declare (ignore from-node to-node))
  (apply #'draw-arrow* stream x1 y1 x2 y2 drawing-options))

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
  (geb:same-type-to-list obj 'geb:prod))

(defmethod visual-children ((obj t))
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Counter API
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar *alphabet*
  (map 'string #'code-char (alexandria:iota (- 91 65) :start 65)))

(serapeum:-> gen-name (t) string)
(defun gen-name (view)
  (let ((count (counter view)))
    (incf (counter view))
    (if (>= count (length *alphabet*))
        (format nil "A~A" (- count (length *alphabet*)))
        (string (char *alphabet* count)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Shapes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun cross-circle (stream radius)
  (draw-line* stream 0      0       (* radius 2) (* radius 2))
  (draw-line* stream 0 (* radius 2) (* radius 2) 0)
  (draw-circle* stream radius radius (+ 3 radius) :filled nil))

(defun plus-circle (stream radius)
  (draw-line* stream    0   radius (* radius 2) radius)
  (draw-line* stream radius    0      radius   (* radius 2))
  (draw-circle* stream radius radius radius :filled nil))

(defun draw-text-arrow* (sheet text x1 y1 x2 y2 &rest rest-args &key &allow-other-keys)
  ;; 10 / length
  ;; resize it better plz
  (format sheet "~A~A"
          (make-string (+ (floor (- (abs (- x2 x1))
                                    (text-size sheet text))
                                 10)
                          1)
                       :initial-element #\space)
          text)
  ;; (format pane "    π₁" )
  (apply #'draw-arrow* sheet x1 y1 x2 y2 rest-args))

(defun xbar (stream)
  "Draw an x with a bar over it"
  (with-room-for-graphics (stream)
    (with-text-face (stream :italic)
      (princ #\x stream)
      (draw-line* stream 0 0 (text-size stream #\x) 0))))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Abstractions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Has to come before the presentation methods probably due to load order
(defmacro center-column-cell ((stream &rest args &key &allow-other-keys)
                              &body x)
  `(formatting-column (,stream ,@args)
     (formatting-cell (,stream :align-x :center :align-y :center)
       ,@x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Graph Presenter
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-presentation-method present ((object graph:node)
                                     (type graph:node)
                                     (pane extended-output-stream)
                                     (view show-view)
                                     &key)
  ;; update this to be better later
  (present-object (graph::value object) pane))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Presentation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO Abstract out the dualities better

(define-presentation-method present ((object geb:alias)
                                     (type   geb:alias)
                                     (pane   extended-output-stream)
                                     (view   show-view)
                                     &key)
  (surrounding-output-with-border (pane :shape :rectangle :background +alice-blue+)
    (formatting-table (pane)
      (formatting-row (pane)
        (formatting-cell (pane)
          (format pane "~W" (intern (symbol-name (geb:name object))))))
      (formatting-row (pane)
        (formatting-cell (pane)
          (present-object (geb:obj object) pane))))))
;; (graph-object (geb:obj object) pane)

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
                (cross-circle stream 7.5))))))))

(define-presentation-method present ((object geb:coprod)
                                     (type   geb:coprod)
                                     (stream extended-output-stream)
                                     (view   show-view)
                                     &key)
  (surrounding-output-with-border (stream)
    (formatting-table (stream :x-spacing "  ")
      ;; dumb hack
      (dolist (x (serapeum:intersperse nil (geb:same-type-to-list object 'geb:coprod)))
        (center-column-cell (stream)
          (if x
              (present-object x stream)
              (plus-circle stream 10.5)))))))

(define-presentation-method present ((object geb:project-left)
                                     (type   geb:project-left)
                                     (pane   extended-output-stream)
                                     (view   show-view)
                                     &key)
  (formatting-table (pane)
    (center-column-cell (pane) (present-object
                                (geb:prod (geb:mcar object) (geb:mcadr object))
                                pane))
    (center-column-cell (pane) (draw-text-arrow* pane "π₁" 0 0 50 0))
    (center-column-cell (pane) (present-object (geb:mcar object) pane))))

(define-presentation-method present ((object geb:project-right)
                                     (type   geb:project-right)
                                     (pane   extended-output-stream)
                                     (view   show-view)
                                     &key)
  (formatting-table (pane)
    (center-column-cell (pane) (present-object
                                (geb:prod (geb:mcar object) (geb:mcadr object))
                                pane))
    (center-column-cell (pane) (draw-text-arrow* pane "π₂" 0 0 50 0))
    (center-column-cell (pane) (present-object (geb:mcadr object) pane))))


(define-presentation-method present ((object geb:inject-left)
                                     (type   geb:inject-left)
                                     (pane   extended-output-stream)
                                     (view   show-view)
                                     &key)
  (formatting-table (pane)
    (center-column-cell (pane) (present-object (geb:mcar object) pane))
    (center-column-cell (pane) (draw-text-arrow* pane "ι₁" 0 0 50 0))
    (center-column-cell (pane) (present-object
                                (geb:coprod (geb:mcar object) (geb:mcadr object))
                                pane))))

(define-presentation-method present ((object geb:inject-right)
                                     (type   geb:inject-right)
                                     (pane   extended-output-stream)
                                     (view   show-view)
                                     &key)
  (formatting-table (pane)
    (center-column-cell (pane) (present-object (geb:mcar object) pane))
    (center-column-cell (pane) (draw-text-arrow* pane "ι₂" 0 0 50 0))
    (center-column-cell (pane) (present-object
                                (geb:coprod (geb:mcar object) (geb:mcadr object))
                                pane))))

(define-presentation-method present ((object geb:terminal)
                                     (type   geb:terminal)
                                     (pane   extended-output-stream)
                                     (view   show-view)
                                     &key)
  (formatting-table (pane)
    (center-column-cell (pane) (present-object (geb:mcar object) pane))
    (center-column-cell (pane) (draw-text-arrow* pane "" 0 0 50 0))
    (center-column-cell (pane) (present-object geb:so1 pane))))

(define-presentation-method present ((object geb:distribute)
                                     (type   geb:distribute)
                                     (pane   extended-output-stream)
                                     (view   show-view)
                                     &key)
  (formatting-table (pane)
    (center-column-cell (pane) (present-object
                                (geb:prod (geb:mcar object)
                                          (geb:coprod (geb:mcadr object)
                                                      (geb:mcaddr object)))
                                pane))
    (center-column-cell (pane) (draw-text-arrow* pane "Dist" 0 0 50 0))
    (center-column-cell (pane) (present-object
                                (geb:coprod (geb:prod (geb:mcar object)
                                                      (geb:mcadr object))
                                            (geb:prod (geb:mcar object)
                                                      (geb:mcaddr object)))
                                pane))))

(define-presentation-method present ((object geb:comp)
                                     (type   geb:comp)
                                     (pane   extended-output-stream)
                                     (view   show-view)
                                     &key)
  (formatting-table (pane)
    (center-column-cell (pane) (present-object (geb:mcadr object) pane))
    (center-column-cell (pane) (draw-arrow* pane 0 0 50 0))
    (center-column-cell (pane) (present-object (geb:mcar object) pane))))

;; Dumb please remove once better system #23 is in.
(define-presentation-method present ((object geb:pair)
                                     (type   geb:pair)
                                     (pane   extended-output-stream)
                                     (view   show-view)
                                     &key)
  (surrounding-output-with-border (pane :shape :drop-shadow)
    (formatting-table (pane)
      (formatting-row (pane)
        (formatting-cell (pane :align-x :center)
          (format pane "Pair")))
      (formatting-row (pane)
        (formatting-cell (pane)
          (present-object (geb.utils:mcar object) pane)))
      (formatting-row (pane)
        (formatting-cell (pane)
          (present-object (geb.utils:mcdr object) pane))))))

(define-presentation-method present ((object geb:case)
                                     (type   geb:case)
                                     (pane   extended-output-stream)
                                     (view   show-view)
                                     &key)
  (surrounding-output-with-border (pane :shape :drop-shadow)
    (formatting-table (pane)
      (formatting-row (pane)
        (formatting-cell (pane :align-x :center)
          (format pane "Case")))
      (formatting-row (pane)
        (formatting-cell (pane)
          (present-object (geb.utils:mcar object) pane)))
      (formatting-row (pane)
        (formatting-cell (pane)
          (present-object (geb.utils:mcadr object) pane))))))

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
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Stick View
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; likely wrong, as it'll do it recursively, but need to fix it later
(define-presentation-method present ((object geb:coprod)
                                     (type   geb:coprod)
                                     (pane   extended-output-stream)
                                     (view   stick-view)
                                     &key)
  (format pane "+")
  ;; (graph-object object pane)
  )

(define-presentation-method present ((object geb:prod)
                                     (type   geb:prod)
                                     (pane   extended-output-stream)
                                     (view   stick-view)
                                     &key)
  (format pane "×")
  ;; (graph-object object pane)
  )

(define-display-clim-command (com-quit :name t) ()
  (frame-exit *application-frame*))

(define-display-clim-command (com-redisplay :name t) ()
  (redisplay-frame-panes *application-frame* :force-p t))

(define-display-clim-command (com-swap :name t) ()
  (setf (graph-p *application-frame*)
        (not (graph-p *application-frame*)))
  (redisplay-frame-panes *application-frame* :force-p t))

(define-presentation-method present ((object geb:init)
                                     (type   geb:init)
                                     (pane   extended-output-stream)
                                     (view   show-view)
                                     &key)
  (formatting-table (pane)
    (center-column-cell (pane) (present-object geb:so0 pane))
    (center-column-cell (pane) (draw-text-arrow* pane "" 0 0 50 0))
    (center-column-cell (pane) (present-object (geb:mcar object) pane))))
