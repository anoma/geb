(in-package :geb-gui)

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
  (apply #'draw-arrow* sheet x1 y1 x2 y2 rest-args))

(defun xbar (stream)
  "Draw an x with a bar over it"
  (with-room-for-graphics (stream)
    (with-text-face (stream :italic)
      (princ #\x stream)
      (draw-line* stream 0 0 (text-size stream #\x) 0))))

