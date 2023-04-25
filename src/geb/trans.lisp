;; Transition or Translation functions about geb

(in-package :geb.trans)

(defgeneric to-poly (morphism)
  (:documentation "Turns a @GEB-SUBSTMORPH into a POLY:POLY"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Morph to Poly Implementation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This maintains exhaustion while leaving it open to extension. you
;; can subclass <substmorph>, without having to update the exhaustion
;; set, however you'll need to properly implement the interface
;; methods on it.

;; Hopefully I can form a complete list somewhere, so one can see the
;; interface functions intended.

;; We could have also derived this from methods, these are equivalent,
;; so both styles are acceptable
(defmethod to-poly ((obj <substmorph>))
  (typecase-of substmorph obj
    (substobj     (error "impossible"))
    (init          0)
    (terminal      0)
    (inject-left   poly:ident)
    (inject-right  (poly:+ (obj-to-nat (mcar obj)) poly:ident))
    (comp          (poly:compose (to-poly (mcar obj))
                                 (to-poly (mcadr obj))))
    (project-right (let ((nat (obj-to-nat (mcadr obj))))
                     (if (zerop nat)
                         nat
                         (poly:mod poly:ident nat))))
    (project-left  (let ((nat (obj-to-nat (mcar obj))))
                     (if (zerop nat)
                         nat
                         (poly:/ poly:ident nat))))
    (distribute    (let ((cx (obj-to-nat (mcar obj)))
                         (cy (obj-to-nat (mcadr obj)))
                         (cz (obj-to-nat (mcaddr obj))))
                     (if (and (zerop cy) (zerop cz))
                         0
                         (let* ((yz   (poly:+ cy cz))
                                (xin  (poly:/ poly:ident yz))
                                (yzin (poly:mod poly:ident yz)))
                           (poly:if-lt yzin cy
                                       (poly:+ (poly:* cy xin) yzin)
                                       (poly:+ (poly:* cz xin)
                                               (poly:- yzin cy)
                                               (poly:* cx cy)))))))
    (pair          (let* ((z  (codom (mcdr obj)))
                          (cz (obj-to-nat z)))
                     (poly:+ (poly:* cz (to-poly (mcar obj)))
                             (to-poly (mcdr obj)))))
    (case          (let* ((f      (mcar obj))
                          (x      (dom f))
                          (cx     (obj-to-nat x))
                          (poly-g (to-poly (mcadr obj))))
                     (if (zerop cx)
                         poly-g
                         (poly:if-lt poly:ident cx
                                     (to-poly f)
                                     (poly:compose poly-g
                                                   (poly:- poly:ident cx))))))
    (otherwise (subclass-responsibility obj))))

;; put here just to avoid confusion
(defmethod to-poly ((obj <substobj>))
  (declare (ignore obj))
  poly:ident)

(defun obj-to-nat (obj)
  (so-card-alg obj))

(-> to-circuit (<substmorph> keyword) geb.vampir.spec:statement)
(defun to-circuit (obj name)
  "Turns a @GEB-SUBSTMORPH to a Vamp-IR Term"
  (assure geb.vampir.spec:statement
    (geb.poly:to-circuit (to-poly obj) name)))






(defmethod to-bits ((obj <substobj>))
  (typecase-of substobj obj
    (so0     0)
    (so1     0)
    (coprod  (+ 1 (max (to-bits (mcar obj)) (to-bits (mcadr obj)))))
    (prod    (+ (to-bits (mcar obj)) (to-bits (mcadr obj))))
    (otherwise (subclass-responsibility obj))))

(defmethod to-bits ((obj <substmorph>))
  (typecase-of substmorph obj
    (substobj     (error "impossible"))
    ;toBits[comp[f__]] := toBits /@ comp[f]
    (comp          (bits:compose (to-bits (mcar obj))
                                 (to-bits (mcadr obj))))
    ; toBits[init[x_]] := par @@ Table[False, bitWidth@x]
    (init          (apply #'bits:parallel (make-list (to-bits (mcar obj)) :initial-element bits:false)))
    ; toBits[terminal[x_]] := drop[bitWidth@x]
    (terminal      (bits:drop (to-bits (mcar obj))))
    ;toBits[injectLeft[mcar_, mcadr_]] :=
    ; par @@ Join[{False, id[bitWidth@mcar]}, Table[False, Max[bitWidth@mcar, bitWidth@mcadr] - bitWidth@mcar]]
    (inject-left   (apply #'bits:parallel (append (list bits:false (bits:identity (to-bits (mcar obj))))
                                                  (make-list (- (max (to-bits (mcar obj)) (to-bits (mcadr obj))) (to-bits (mcar obj))) :initial-element bits:false)
                                          )))
    ;toBits[injectRight[mcar_,mcadr_]]:=
    ;  par@@Join[{True,id[bitWidth@mcadr]},Table[False, Max[bitWidth@mcar, bitWidth@mcadr] - bitWidth@mcadr]]
    (inject-right  (apply #'bits:parallel (append (list bits:true (bits:identity (to-bits (mcadr obj)))) 
                                                  (make-list (- (max (to-bits (mcar obj)) (to-bits (mcadr obj))) (to-bits (mcadr obj))) :initial-element bits:false)
                                          )))
    ;toBits[case[mcar_,mcadr_]]:=
    ;  branch[
    ;    par[toBits@mcar,id[Max[dom@mcar,dom@mcadr]-dom@mcar]],
    ;    par[toBits@mcadr,id[Max[dom@mcar,dom@mcadr]-dom@mcadr]]
    ;  ]
    (case          (bits:branch (bits:parallel (to-bits (mcar obj))  (bits:identity (- (max (dom (mcar obj)) (dom (mcadr obj))) (dom (mcar obj)))))
                                (bits:parallel (to-bits (mcadr obj)) (bits:identity (- (max (dom (mcar obj)) (dom (mcadr obj))) (dom (mcadr obj)))))))
    ; toBits[projectRight[mcar_, mcadr_]] := par[drop[bitWidth@mcar], id[bitWidth@mcadr]]
    (project-left  (bits:parallel (bits:identity (to-bits (mcar obj))) (bits:drop (to-bits (mcadr obj)))))
    ; toBits[projectLeft[mcar_, mcadr_]] := par[id[bitWidth@mcar], drop[bitWidth@mcadr]]
    (project-right (bits:parallel (bits:drop (to-bits (mcar obj))) (bits:identity (to-bits (mcadr obj)))))
    ; toBits[pair[mcar_, mcdr_]] := comp[par[toBits[mcar], toBits[mcdr]], fork[dom[mcar]]]
    (pair          (bits:compose (bits:parallel (to-bits (mcar obj)) (to-bits (mcdr obj))) (bits:fork (dom (mcar obj)))))
    ;toBits[distribute[mcar_, mcadr_, mcaddr_]] :=
    ;  par[swap[bitWidth[mcar], 1], id[Max[bitWidth@mcadr, bitWidth@mcaddr]]]
    (distribute    (bits:parallel (bits:swap (to-bits (mcar obj)) 1) (bits:identity (max (to-bits (mcadr obj)) (to-bits (mcaddr obj))))))
    (otherwise (subclass-responsibility obj))))

