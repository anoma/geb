(in-package :geb-gui)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Main Data and View
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Graph view of products and coproducts
(defclass stick-view (show-view) ())

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
  (stick-graph object pane))

(define-presentation-method present ((object geb:prod)
                                     (type   geb:prod)
                                     (pane   extended-output-stream)
                                     (view   stick-view)
                                     &key)
  (format pane "×")
  (stick-graph object pane))
