(in-package :geb.bits.trans)

(defgeneric to-vampir (morphism values)
  (:documentation "Turns a BITS term into a Vamp-IR term with a given value"))

(defun to-circuit (morphism name)
  "Turns a BITS term into a Vamp-IR Gate with the given name"
  (let ((wire (vamp:make-wire :var :x)))
    (vamp:make-alias :name name
                     :inputs (list wire)
                     :body (list (to-vampir morphism wire)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Bits to Vampir Implementation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmethod to-vampir ((obj <bits>) values)
  (declare (ignore values))
  (subclass-responsibility obj))

(-> direct-fields-to-list-vampir (geb.mixins:direct-pointwise-mixin) list)
(defun direct-fields-to-list (obj)
  (mapcar #'cdr (geb.mixins:to-pointwise-list obj)))

(defun infix-creation (symbol obj value1 value2)
  (vamp:make-infix :op symbol
                   :lhs value
                   :rhs value2))


(defmethod to-vampir ((obj compose) values)
  (to-vampir (mcar obj)
             (to-vampir (mcadr obj) values)))

(defmethod to-vampir ((obj fork) values)
  ; toElem[fork[n_]] := Function[{inp}, Flatten[{inp, inp}, 1]]
  (append values values))

(defmethod to-vampir ((obj parallel) values)
  ; toElem[par[car_, cadr_]] :=
  ;   Function[{inp},
  ;     Module[{cx, inp1, inp2},
  ;     cx = dom[car];
  ;     inp1 = inp[[1 ;; cx]];
  ;     inp2 = inp[[cx + 1 ;; All]];
  ;     Flatten[{toElem[car][inp1], toElem[cadr][inp2]}, 1]
  ;   ]]
  (let* ((car (mcar obj))
         (cadr (mcadr obj))
         (cx (dom car))
         (inp1 (subseq values 0 cx))
         (inp2 (subseq values cx)))
    (concatenate 'list (to-vampir car inp1) (to-vampir cadr inp2))))

(defmethod to-vampir ((obj negation) values)
  ; toElem[neg] := {1 - #[[1]]} &
  (list (infix-creation :- (make-constant :const 1) (car values))))

(defmethod to-vampir ((obj conjunction) values)
  ; toElem[conj] := {#[[1]] * #[[2]]} &
  (list (infix-creation :* (car values) (car (cdr values)))))

(defmethod to-vampir ((obj swap) values)
  ; toElem[swap[n_, m_]] := Flatten[{#[[n + 1 ;; All]], #[[1 ;; n]]}, 1] &
  (let ((n (mcar obj)))
       (append (subseq values (1 + n)) (subseq values 0 (1 + n)))))

(defmethod to-vampir ((obj true) values)
  ; toElem[True] := {1} &
  (declare (ignore values))
  (list (vamp:make-constant :const 1)))

(defmethod to-vampir ((obj false) values)
  ; toElem[False] := {0} &
  (declare (ignore values))
  (list (vamp:make-constant :const 0)))

(defmethod to-vampir ((obj identity) values)
  ; toElem[id[_]] := # &
  values)

(defmethod to-vampir ((obj drop) values)
  ; toElem[drop[_]] := {} &
  (declare (ignore values))
  nil)

(defmethod to-vampir ((obj branch) values)
  ; toElem[branch[f_, g_]][{x_, values__}] :=
  ;   Thread@Plus[
  ;     Times[1 - x, #] & /@ toElem[f][{values}],
  ;     Times[x, #] & /@ toElem[g][{values}]
  ;   ]
  (let* ((x (car values))
         (rest-values (cdr values))
         (f (mcar obj))
         (g (mcadr obj))
         (f-elems (to-vampir f rest-values))
         (g-elems (to-vampir g rest-values)))
    (mapcar #'(lambda (f-elem g-elem)
                (infix-creation :+
                  (infix-creation :* (infix-creation :- 1 x) f-elem)
                  (infix-creation :* x g-elem)))
            f-elems g-elems)))
