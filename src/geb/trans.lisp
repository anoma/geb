;; Transition or Translation functions about geb

(in-package :geb.trans)

(defgeneric to-poly (morphism)
  (:documentation "Turns a @GEB-SUBSTMORPH into a POLY:POLY"))

(defgeneric to-bitc (morphism)
  (:documentation "Turns a @GEB-SUBSTMORPH into a bitc:BITC"))

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

(-> to-circuit (<substmorph> keyword) list)
(defun to-circuit (obj name)
  "Turns a @GEB-SUBSTMORPH to a Vamp-IR Term"
  (assure list
    (geb.poly:to-circuit (to-poly obj) name)))






(defmethod to-bitc ((obj <substobj>))
  (typecase-of substobj obj
    (so0     0)
    (so1     0)
    (coprod  (+ 1 (max (to-bitc (mcar obj)) (to-bitc (mcadr obj)))))
    (prod    (+ (to-bitc (mcar obj)) (to-bitc (mcadr obj))))
    (otherwise (subclass-responsibility obj))))

(defmethod to-bitc ((obj <substmorph>))
  (typecase-of substmorph obj
    (substobj     (error "impossible"))
    ;toBits[comp[f__]] := toBits /@ comp[f]
    (comp          (bitc:compose (to-bitc (mcar obj))
                                 (to-bitc (mcadr obj))))
    ; toBits[init[x_]] := par @@ Table[False, bitWidth@x]
    (init          (apply #'bitc:parallel (make-list (to-bitc (mcar obj)) :initial-element bitc:zero)))
    ; toBits[terminal[x_]] := drop[bitWidth@x]
    (terminal      (bitc:drop (to-bitc (mcar obj))))
    ;toBits[injectLeft[mcar_, mcadr_]] :=
    ; par @@ Join[{False, id[bitWidth@mcar]}, Table[False, Max[bitWidth@mcar, bitWidth@mcadr] - bitWidth@mcar]]
    (inject-left   (apply #'bitc:parallel (append (list bitc:zero (bitc:ident (to-bitc (mcar obj))))
                                                  (make-list (- (max (to-bitc (mcar obj)) (to-bitc (mcadr obj))) (to-bitc (mcar obj))) :initial-element bitc:zero)
                                          )))
    ;toBits[injectRight[mcar_,mcadr_]]:=
    ;  par@@Join[{True,id[bitWidth@mcadr]},Table[False, Max[bitWidth@mcar, bitWidth@mcadr] - bitWidth@mcadr]]
    (inject-right  (apply #'bitc:parallel (append (list bitc:one (bitc:ident (to-bitc (mcadr obj)))) 
                                                  (make-list (- (max (to-bitc (mcar obj)) (to-bitc (mcadr obj))) (to-bitc (mcadr obj))) :initial-element bitc:zero)
                                          )))
    ;toBits[case[mcar_,mcadr_]]:=
    ;  branch[
    ;    par[toBits@mcar,id[Max[dom@mcar,dom@mcadr]-dom@mcar]],
    ;    par[toBits@mcadr,id[Max[dom@mcar,dom@mcadr]-dom@mcadr]]
    ;  ]
    (case          (bitc:branch (bitc:parallel (to-bitc (mcar obj))  (bitc:ident (- (max (bitc:dom (mcar obj)) (bitc:dom (mcadr obj))) (bitc:dom (mcar obj)))))
                                (bitc:parallel (to-bitc (mcadr obj)) (bitc:ident (- (max (bitc:dom (mcar obj)) (bitc:dom (mcadr obj))) (bitc:dom (mcadr obj)))))))
    ; toBits[projectRight[mcar_, mcadr_]] := par[drop[bitWidth@mcar], id[bitWidth@mcadr]]
    (project-left  (bitc:parallel (bitc:ident (to-bitc (mcar obj))) (bitc:drop (to-bitc (mcadr obj)))))
    ; toBits[projectLeft[mcar_, mcadr_]] := par[id[bitWidth@mcar], drop[bitWidth@mcadr]]
    (project-right (bitc:parallel (bitc:drop (to-bitc (mcar obj))) (bitc:ident (to-bitc (mcadr obj)))))
    ; toBits[pair[mcar_, mcdr_]] := comp[par[toBits[mcar], toBits[mcdr]], fork[dom[mcar]]]
    (pair          (bitc:compose (bitc:parallel (to-bitc (mcar obj)) (to-bitc (mcdr obj))) (bitc:fork (bitc:dom (mcar obj)))))
    ;toBits[distribute[mcar_, mcadr_, mcaddr_]] :=
    ;  par[swap[bitWidth[mcar], 1], id[Max[bitWidth@mcadr, bitWidth@mcaddr]]]
    (distribute    (bitc:parallel (bitc:swap (to-bitc (mcar obj)) 1) (bitc:ident (max (to-bitc (mcadr obj)) (to-bitc (mcaddr obj))))))
    (otherwise (subclass-responsibility obj))))

