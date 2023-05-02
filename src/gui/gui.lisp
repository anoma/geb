(in-package :geb-gui)

;; My first horrible gui attempt, lets go!

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Main Data
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
  ;; please me refactor this out, Ι hate it
  ((%top-task :initform *the-data* :accessor root)
   (%original :initform *the-data* :accessor orig)
   (%graph-p  :initform t :accessor graph-p)
   (%dot-p    :initform t :accessor dot-p)
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
         (graph-dot (root frame) pane))
        ((graph-p frame)
         (display-graph frame pane))
        (t
         (handler-case (present-object (root frame) pane)
           (error (c)
             (declare (ignore c))
             (format pane "issue displaying, please call swap to get it back into a graph~%")
             (display-graph frame pane))))))

(defun display-graph (frame pane)
  (apply (if (dot-p frame)
             #'graph-dot
             #'graph-node)
         (list (graph:passes (graph:graphize (root frame) nil)) pane)))
