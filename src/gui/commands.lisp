(in-package :geb-gui)

(define-display-clim-command (com-quit :name t) ()
  (frame-exit *application-frame*))

(define-display-clim-command (com-redisplay :name t) ()
  (redisplay-frame-panes *application-frame* :force-p t))

(define-display-clim-command (com-swap :name t) ()
  (setf (graph-p *application-frame*)
        (not (graph-p *application-frame*)))
  (redisplay-frame-panes *application-frame* :force-p t))

(define-display-clim-command (com-dot :name t) ()
  (setf (dot-p *application-frame*)
        (not (dot-p *application-frame*)))
  (redisplay-frame-panes *application-frame* :force-p t))
