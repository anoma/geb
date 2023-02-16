(in-package :geb-gui)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Main Data and View
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defclass show-view (view)
  ((counter :initform 0 :initarg :counter :accessor counter)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Abstractions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Has to come before the presentation methods probably due to load order


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;                            Presentation                                ;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; General Presentation
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
      ;; (formatting-row (pane)
      ;;   (formatting-cell (pane)
      ;;     (present-object (geb:obj object) pane)))
      )))

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
;; Presentation: Box View
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


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
