(in-package #:geb.lambda.main)

(defclass fun-type (geb.mixins:direct-pointwise-mixin geb.mixins:cat-obj)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :documentation ""))
  (:documentation
   "Stand-in for the [SO-HOM-OBJ][GEB.MAIN:SO-HOM-OBJ] object. It does not have
any computational properties and can be seen as just a function of two arguments
with accessors [MCAR][generic-function] to the first argument and
[MCADR][generic-function] to the second argument. There is an evident canonical
way to associate [FUN-TYPE][class] and [SO-HOM-OBJ][GEB.MAIN:SO-HOM-OBJ]
pointwise."))

(defun fun-type (mcar mcadr)
  (make-instance 'fun-type :mcar mcar :mcadr mcadr))

(-> index-check (fixnum list) cat-obj)
(defun index-check (i ctx)
  "Given an natural number I and a context, checks that the context is of
length at least I and then produces the Ith entry of the context counted
from the left starting with 0."
  (let ((l (length ctx)))
    (if (< i l)
        (nth i ctx)
        (error "Argument exceeds length of context"))))

;; Types all terms inside a given lambda term with respect to a context
;; with the caveat of producing a stand-in of the exponential object

;; We assume that the compiler receives all the info using the exp-aux
;; class instead of the usual hom-obj for the well-defp predicate


(defgeneric ann-term1 (ctx tterm)
  (:documentation
   "Given a list of [SUBSTOBJ][GEB.SPEC:SUBSTOBJ] objects with
[SO-HOM-OBJ][GEB.MAIN:SO-HOM-OBJ] occurences replaced by [FUN-TYPE][class]
and an [STLC][type] similarly replacing type occurences of the hom object
to [FUN-TYPE][class], provides the [TTYPE][generic-function] accessor to all
subterms as well as the term itself, using [FUN-TYPE][class]. Once again,
note  that it is important for the context and term to be giving as
per above description. While not always, not doing so result in an error upon
evaluation. As an example of a valid entry we have

```lisp
 (ann-term1 (list so1 (fun-type so1 so1)) (app (index 1) (list (index 0))))
```

while

```lisp
(ann-term1 (list so1 (so-hom-obj so1 so1)) (app (index 1) (list (index 0))))
```

produces an error trying to use [HOM-COD]. This warning applies to other
functions taking in context and terms below as well.

Moreover, note that for terms whose typing needs addition of new context
we append contexts on the left rather than on the right contra usual type
theoretic notation for the convenience of computation. That means, e.g. that
asking for a type of a lambda term as below produces:

```lisp
LAMBDA> (ttype (term (ann-term1 (lambda (list so1 so0) (index 0)))))
s-1
```

as we count indeces from the left of the context while appending new types to
the context on the left as well. For more info check [LAMB][class]"))


(defmethod ann-term1 (ctx (tterm <stlc>))
  ;; cahce check
  (if (ttype tterm)
      tterm
      (match-of stlc tterm
        ((absurd tcod term) (absurd tcod (ann-term1 ctx term) :ttype tcod))
        (unit               (unit :ttype so1))
        ((left rty term)    (let ((lant (ann-term1 ctx term)))
                              (left rty
                                    lant
                                    :ttype (coprod (ttype lant) rty))))
        ((right lty term)   (let ((rant (ann-term1 ctx term)))
                              (right lty
                                     rant
                                     :ttype (coprod lty (ttype rant)))))
        ((pair ltm rtm)     (let ((lant (ann-term1 ctx ltm))
                                  (rant (ann-term1 ctx rtm)))
                              (pair lant
                                    rant
                                    :ttype (prod (ttype lant) (ttype rant)))))
        ((fst term)         (let* ((ann-term     (ann-term1 ctx term))
                                   (type-of-term (ttype (ann-term1 ctx term))))
                              (if (typep type-of-term 'prod)
                                  (fst ann-term
                                       :ttype (mcar type-of-term))
                                  (error "type of term not of product type"))))
        ((snd term)          (let* ((ann-term     (ann-term1 ctx term))
                                    (type-of-term (ttype ann-term)))
                               (if (typep type-of-term 'prod)
                                   (snd ann-term :ttype (mcadr type-of-term))
                                   (error "type of term not of product type"))))
        ((lamb tdom term)   (let ((ant (ann-term1 (append tdom ctx) term)))
                              (lamb tdom
                                    ant
                                    :ttype (fun-type (reduce #'prod tdom) (ttype ant)))))
        ((app fun term)     (let ((anfun (ann-term1 ctx fun)))
                              (app anfun
                                   (mapcar (lambda (trm) (ann-term1 ctx trm)) term)
                                   :ttype (mcadr (ttype anfun)))))
        ((index pos)        (index pos
                                   :ttype (index-check pos ctx)))
        ((err ttype)        (err ttype))
        ((plus ltm rtm)        (let ((ant (ann-term1 ctx ltm)))
                                 (plus ant
                                       (ann-term1 ctx rtm)
                                       :ttype (ttype ant))))
        ((times ltm rtm)        (let ((ant (ann-term1 ctx ltm)))
                                  (times ant
                                         (ann-term1 ctx rtm)
                                         :ttype (ttype ant))))
        ((minus ltm rtm)        (let ((ant (ann-term1 ctx ltm)))
                                  (minus ant
                                         (ann-term1 ctx rtm)
                                         :ttype (ttype ant))))
        ((divide ltm rtm)        (let ((ant (ann-term1 ctx ltm)))
                                   (divide ant
                                           (ann-term1 ctx rtm)
                                           :ttype (ttype ant))))
        ((bit-choice bitv)       (bit-choice bitv
                                             :ttype (nat-width (array-total-size bitv))))
        ((lamb-eq ltm rtm)         (lamb-eq (ann-term1 ctx ltm)
                                            (ann-term1 ctx rtm)
                                            :ttype (coprod so1 so1)))
        ((lamb-lt ltm rtm)         (lamb-lt (ann-term1 ctx ltm)
                                            (ann-term1 ctx rtm)
                                            :ttype (coprod so1 so1)))
        ((modulo ltm rtm)          (let ((ant (ann-term1 ctx ltm)))
                                     (modulo ant
                                             (ann-term1 ctx rtm)
                                             :ttype (ttype ant))))
        ((case-on on ltm rtm)
         (let* ((ann-on     (ann-term1 ctx on))
                (type-of-on (ttype ann-on))
                (ann-left   (ann-term1 (cons  (mcar type-of-on) ctx) ltm))
                (ann-right  (ann-term1 (cons (mcadr type-of-on) ctx) rtm)))
           (if (typep type-of-on 'coprod)
               (case-on ann-on ann-left ann-right :ttype (ttype ann-left))
               (error "type of on not of coproduct type")))))))

;; Changes the stand in Geb term with exponential stand-ins
;; to one containing actual hom-objects
(defun fun-to-hom (t1)
  "Given a [SUBSTOBJ][GEB.SPEC:SUBSTOBJ] whose subobjects might have a
[FUN-TYPE][class] occurence replaces all occurences of [FUN-TYPE][class] with a
suitable [SO-HOM-OBJ][GEB.MAIN:SO-HOM-OBJ], hence giving a pure
[SUBSTOBJ][GEB.SPEC:SUBSTOBJ]

```lisp
LAMBDA> (fun-to-hom (fun-type geb-bool:bool geb-bool:bool))
(× (+ GEB-BOOL:FALSE GEB-BOOL:TRUE) (+ GEB-BOOL:FALSE GEB-BOOL:TRUE))
```"
  (cond ((typep t1 'prod)     (prod (fun-to-hom (mcar t1))
                                    (fun-to-hom (mcadr t1))))
        ((typep t1 'coprod)   (coprod (fun-to-hom (mcar t1))
                                      (fun-to-hom (mcadr t1))))
        ((typep t1 'fun-type) (so-hom-obj (fun-to-hom (mcar t1))
                                          (fun-to-hom (mcadr t1))))
        (t                    t1)))

;; Changes all annotated terms' types to actual Geb objects

(defun ann-term2 (tterm)
  "Given an [STLC][type] term with a [TTYPE][generic-function] accessor from
[ANN-TERM1][generic-function] - i.e. including possible [FUN-TYPE][class]
occurences - re-annotates the term and its subterms with actual
[SUBSTOBJ][GEB.SPEC:SUBSTOBJ] objects."
  (match-of stlc tterm
    ((absurd tcod term)    (absurd (fun-to-hom tcod)
                                   (ann-term2 term)
                                   :ttype (fun-to-hom (ttype tterm))))
    (unit                   tterm)
    ((right lty term)       (right (fun-to-hom lty)
                                   (ann-term2 term)
                                   :ttype (fun-to-hom (ttype tterm))))
    ((left rty term)        (left (fun-to-hom rty)
                                  (ann-term2 term)
                                  :ttype (fun-to-hom (ttype tterm))))
    ((case-on on ltm rtm)  (case-on (ann-term2 on)
                                    (ann-term2 ltm)
                                    (ann-term2 rtm)
                                    :ttype (fun-to-hom (ttype tterm))))
    ((pair ltm rtm)        (pair (ann-term2 ltm)
                                 (ann-term2 rtm)
                                 :ttype (fun-to-hom (ttype tterm))))
    ((fst term)            (fst (ann-term2 term)
                                :ttype (fun-to-hom (ttype tterm))))
    ((snd term)            (snd (ann-term2 term)
                                :ttype (fun-to-hom (ttype tterm))))
    ((lamb tdom term)      (lamb (mapcar #'fun-to-hom tdom)
                                 (ann-term2 term)
                                 :ttype (fun-to-hom (ttype tterm))))
    ((app fun term)        (app (ann-term2 fun)
                                (mapcar #'ann-term2 term)
                                :ttype (fun-to-hom (ttype tterm))))
    ((index pos)           (index pos
                                  :ttype (fun-to-hom (ttype tterm))))
    ((err ttype)           (err (fun-to-hom ttype)))
    ((or plus
         times
         minus
         divide
         modulo
         bit-choice
         lamb-eq
         lamb-lt)
     tterm)))

(defun annotated-term (ctx term)
  "Given a context consisting of a list of [SUBSTOBJ][GEB.SPEC:SUBSTOBJ]
with occurences of [SO-HOM-OBJ][GEB.MAIN:SO-HOM-OBJ] replaced by
[FUN-TYPE][class] and an [STLC][type] term with similarly replaced occurences
of [SO-HOM-OBJ][GEB.MAIN:SO-HOM-OBJ], provides an [STLC][type] with all
subterms typed, i.e. providing the [TTYPE][generic-function] accessor,
which is a pure [SUBSTOBJ][GEB.SPEC:SUBSTOBJ]"
  (ann-term2 (ann-term1 ctx term)))


;; Produces a type of a lambda term in a context
;; with a stand-in for the exponential object

(defun type-of-term-w-fun (ctx tterm)
  "Given a context consisting of a list of [SUBSTOBJ][GEB.SPEC:SUBSTOBJ] with
occurences of [SO-HOM-OBJ][GEB.MAIN:SO-HOM-OBJ] replaced by [FUN-TYPE][class]
and an [STLC][type] term with similarly replaced occurences of
[SO-HOM-OBJ][GEB.MAIN:SO-HOM-OBJ], gives out a type of the whole term with
occurences of [SO-HOM-OBJ][GEB.MAIN:SO-HOM-OBJ] replaced by [FUN-TYPE][class]."
  (ttype (ann-term1 ctx tterm)))

;; Actual type info

(defun type-of-term (ctx tterm)
  "Given a context consisting of a list of [SUBSTOBJ][GEB.SPEC:SUBSTOBJ] with
occurences of [SO-HOM-OBJ][GEB.MAIN:SO-HOM-OBJ] replaced by [FUN-TYPE][class]
and an [STLC][type] term with similarly replaced occurences of
[SO-HOM-OBJ][GEB.MAIN:SO-HOM-OBJ], provides the type of the whole term,
which is a pure [SUBSTOBJ][type]."
  (fun-to-hom (type-of-term-w-fun ctx tterm)))

;;Predicate checking that a term in a given context is well-typed

(defgeneric well-defp (ctx tterm)
  (:documentation
   "Given a context consisting of a list of [SUBSTOBJ][GEB.SPEC:SUBSTOBJ]
with occurences of [SO-HOM-OBJ][GEB.MAIN:SO-HOM-OBJ] replaced by
[FUN-TYPE][class] and an [STLC][type] term with similarly replaced
occurences of [SO-HOM-OBJ][GEB.MAIN:SO-HOM-OBJ], checks that the term
is well-defined in the context based on structural rules of simply
typed lambda calculus. returns the t if it is, otherwise returning
nil"))

(defmethod well-defp (ctx (tterm <stlc>))
  (labels ((check (tterm)
             (match-of stlc tterm
               ((absurd)
                (and (check (term tterm))
                     (obj-equalp (ttype (term tterm)) so0)))
               ((left term)
                (and (check term)
                     (obj-equalp (mcar (ttype tterm)) (ttype term))))
               ((right term)
                (and (check term)
                     (obj-equalp (mcadr (ttype tterm)) (ttype term))))
               ((pair ltm rtm)
                (and (check ltm)
                     (check rtm)))
               ((fst term)
                (and (check term)
                     (obj-equalp (ttype tterm) (mcar (ttype term)))))
               ((snd term)
                (and (check term)
                     (obj-equalp (ttype tterm) (mcadr (ttype term)))))
               ((case-on on ltm rtm)
                (and (check ltm)
                     (check rtm)
                     (check on)
                     (obj-equalp (ttype ltm) (ttype rtm))))
               ((lamb tdom term)
                (let ((lambda-type (ttype tterm)))
                  (and (check term)
                       (obj-equalp (mcar lambda-type) (reduce #'prod tdom))
                       (obj-equalp (mcadr lambda-type) (ttype term)))))
               ((app fun term)
                (and (check fun)
                     (check (reduce #'pair term :from-end t))
                     (typep (ttype fun) 'fun-type)
                     (obj-equalp (ttype fun)
                                 (fun-type (reduce #'prod
                                                   (mapcar #'ttype term)
                                                   :from-end t)
                                           (ttype tterm)))))
               ((or plus
                    minus
                    divide
                    times
                    modulo)
                (obj-equalp (ttype (ltm tterm))
                            (ttype (rtm tterm))))
               ((or lamb-eq
                    lamb-lt)
                t)
               (index t)
               (unit t)
               (err t)
               (bit-choice t))))
    (let ((term (ignore-errors
                 (ann-term1 ctx tterm))))
      (and term (check term)))))

(defun errorp (tterm)
  "Evaluates to true iff the term has an error subterm."
  (cond ((or (typep tterm 'index)
             (typep tterm 'unit)
             (typep tterm 'bit-choice))
         nil)
        ((typep tterm 'err)       t)
        ((typep tterm 'case-on)   (or (errorp (on tterm))
                                      (errorp (rtm tterm))
                                      (errorp (ltm tterm))))
        ((typep tterm 'pair)      (or (errorp (ltm tterm))
                                      (errorp (rtm tterm))))
        ((typep tterm 'app)       (or (errorp (fun tterm))
                                      (some #'identity
                                            (mapcar
                                             (lambda (x) (errorp x))
                                             (term tterm)))))
        ((or (typep tterm 'plus)
             (typep tterm 'minus)
             (typep tterm 'times)
             (typep tterm 'divide)
             (typep tterm 'lamb-eq)
             (typep tterm 'lamb-lt)
             (typep tterm 'modulo))
         (or (errorp (ltm tterm))
             (errorp (rtm tterm))))
        (t                        (errorp (term tterm)))))

(defun dispatch (tterm)
  "A dispatch refering the class of a term to its function"
  (typecase tterm
    (absurd #'absurd)
    (unit   #'unit)
    (left   #'left)
    (right   #'right)
    (case-on #'case-on)
    (fst #'fst)
    (snd #'snd)
    (pair #'pair)
    (lamb #'lamb)
    (app #'app)
    (index #'index)
    (err #'err)
    (bit-choice #'bit-choice)
    (plus #'plus)
    (minus #'minus)
    (divide #'divide)
    (times #'times)
    (lamb-eq #'lamb-eq)
    (lamb-lt #'lamb-lt)
    (modulo  #'modulo)))

(defun dispatch-arith (tterm)
  "A dispatch refering the class of an arithmetic term
to its corresponding operation"
  (typecase tterm
    (plus #'+)
    (minus #'-)
    (divide #'floor)
    (times #'*)
    (lamb-eq #'=)
    (lamb-lt #'<)
    (modulo #'mod)))

(defun index-excess (tterm)
  "Checks all indeces occuring in a term which will be substituted.
If position exceeds n, adds depth to the index. Necessary for
beta-substitution of indices which point outside of the app term"
  (labels ((rec (n tterm)
             (typecase tterm
               (absurd    (absurd (tcod tterm)
                                  (rec n (term tterm))))
               (left      (left (rty tterm)
                                (rec n (term tterm))))
               (right     (right (lty tterm)
                                 (rec n (term tterm))))
               (case-on   (case-on (rec n (on tterm))
                                   (rec (1+ n) (ltm tterm))
                                   (rec (1+ n) (rtm tterm))))
               (fst       (fst (rec n (term tterm))))
               (snd       (snd (rec n (term tterm))))
               (lamb      (lamb (tdom tterm)
                                (rec (1+ n) (term tterm))))
               (app       (app (rec n (fun tterm))
                               (list (rec n (car (term tterm))))))
               (index     (if (>= (pos tterm) n)
                              (index (1+ (pos tterm)))
                              tterm))
               ((or unit
                    err
                    bit-choice)
                tterm)
               ((or plus
                    times
                    minus
                    divide
                    lamb-eq
                    lamb-lt
                    pair
                    modulo)
                (funcall (dispatch tterm)
                         (rec n (ltm tterm))
                         (rec n (rtm tterm)))))))
    (rec 0 tterm)))

(defun index-lack (n tterm)
  "Checks if a term has made substitutions and decreases the index
of term accordingly"
  (labels ((rec (n tterm)
             (if (typep tterm 'list)
                 tterm
                 (typecase tterm
                   (absurd    (absurd (tcod tterm)
                                      (rec n (term tterm))))
                   (left      (left (rty tterm)
                                    (rec n (term tterm))))
                   (right     (right (lty tterm)
                                     (rec n (term tterm))))
                   (case-on   (case-on (rec n (on tterm))
                                       (rec (1+ n) (ltm tterm))
                                       (rec (1+ n) (rtm tterm))))
                   (fst       (fst (rec n (term tterm))))
                   (snd       (snd (rec n (term tterm))))
                   (lamb      (lamb (tdom tterm)
                                    (rec (1+ n) (term tterm))))
                   (app      (app (rec n (fun tterm))
                                  (list (rec n (car (term tterm))))))
                   (index     (if (> (pos tterm) n)
                                  (index (1- (pos tterm)))
                                  tterm))
                   ((or unit
                        err
                        bit-choice)
                    tterm)
                   ((or plus
                        times
                        minus
                        divide
                        lamb-eq
                        lamb-lt
                        pair
                        modulo)
                    (funcall (dispatch tterm)
                             (rec n (ltm tterm))
                             (rec n (rtm tterm))))))))
    (rec n tterm)))

(defun delist (tterm)
  "We mark substituted terms by listing them. This function recovers the car
of the list."
  (if (typep tterm 'list)
      (car tterm)
      (typecase tterm
        (absurd  (absurd (tcod tterm)
                         (delist (term tterm))))
        (left    (left (rty tterm)
                       (delist (term tterm))))
        (right   (right (lty tterm)
                        (delist (term tterm))))
        (case-on (case-on (delist (on tterm))
                          (delist (ltm tterm))
                          (delist (rtm tterm))))
        (fst     (fst (delist (term tterm))))
        (snd     (snd (delist (term tterm))))
        (lamb    (lamb (tdom tterm)
                       (delist (term tterm))))
        (app     (app (delist (fun tterm))
                      (list (delist (car (term tterm))))))
        ((or unit
             err
             index
             bit-choice)
         tterm)
        ((or plus
             times
             minus
             divide
             lamb-eq
             lamb-lt
             pair
             modulo)
         (funcall (dispatch tterm)
                  (delist (ltm tterm))
                  (delist (rtm tterm)))))))

(defun sub (ind term-to-replace sub-in)
  "Substitutes the occurence of index (ind) inside of the top
subterms of sub-on by term-to-replace. We mark replaced terms by
listing them"
  (typecase sub-in
    (absurd   (absurd (tcod sub-in) (sub ind
                                         term-to-replace
                                         (term sub-in))))
    (left     (left (rty sub-in) (sub ind
                                      term-to-replace
                                      (term sub-in))))
    (right     (right (lty sub-in) (sub ind
                                        term-to-replace
                                        (term sub-in))))
    (case-on   (case-on (sub ind
                             term-to-replace
                             (on sub-in))
                        (sub (1+ ind)
                             (index-excess term-to-replace)
                             (ltm sub-in))
                        (sub (1+ ind)
                             (index-excess term-to-replace)
                             (rtm sub-in))))
    (fst        (fst (substitute ind
                                 term-to-replace
                                 (term sub-in))))
    (snd        (snd (substitute ind
                                 term-to-replace
                                 (term sub-in))))
    (lamb      (lamb (tdom sub-in)
                     (sub (1+ ind)
                          (index-excess term-to-replace)
                          (term sub-in))))
    (app        (app (sub ind term-to-replace (fun sub-in))
                     (list (sub ind term-to-replace (car (term sub-in))))))
    (index      (if (= (pos sub-in) ind)
                    (list term-to-replace)
                    sub-in))
    ((or unit
         err
         bit-choice)
     sub-in)
    ((or plus
         times
         minus
         divide
         lamb-eq
         lamb-lt
         pair
         modulo)
     (funcall (dispatch sub-in)
              (sub ind term-to-replace (ltm sub-in))
              (sub ind term-to-replace (rtm sub-in))))))

(defun reducer (tterm)
  "Reduces a given Lambda term by applying explict beta-reduction
when possible alongside arithmetic simplification. We assume that the
lambda and app terms are  1-argument"
  (typecase tterm
    (absurd   (absurd (tcod tterm) (reducer (term tterm))))
    (left     (left (rty tterm) (reducer (term tterm))))
    (right    (right (lty tterm) (reducer (term tterm))))
    (case-on  (let ((on (on tterm))
                    (ltm (ltm tterm))
                    (rtm (rtm tterm)))
                (cond ((typep on 'left)  (substitute-zero on ltm))
                      ((typep on 'right) (substitute-zero on rtm))
                      (t                 (case-on (reducer on)
                                                  (reducer ltm)
                                                  (reducer rtm))))))
    (pair     (pair (reducer (ltm tterm))
                    (reducer (rtm tterm))))
    (fst      (let ((term (term tterm)))
                (if (typep (reducer term) 'pair)
                    (reducer (ltm term))
                    (fst (reducer term)))))
    (snd      (let ((term (term tterm)))
                (if (typep (reducer term) 'pair)
                    (reducer (rtm term))
                    (snd (reducer term)))))
    (lamb     (lamb (tdom tterm) (reducer (term tterm))))
    (app
     (let ((fun (fun tterm))
           (term (car (term tterm))))
       (cond ((typep fun 'lamb)
              (substitute-zero (reducer term) (reducer (term fun))))
             ((and (typep fun 'case-on)
                   (typep (ltm fun) 'lamb)
                   (typep (rtm fun) 'lamb))
              (let ((irec (index-excess (reducer term))))
                (flet ((zero-index (term)
                         (substitute-zero irec (reducer (term term)))))
                  (reducer (case-on (reducer (on fun))
                                    (zero-index (ltm fun))
                                    (zero-index (rtm fun)))))))
             ((and (typep fun 'case-on)
                   (typep (ltm fun) 'lamb)
                   (typep (rtm fun) 'case-on))
              (reducer (case-on (reducer (on fun))
                                (substitute-zero (index-excess (reducer term))
                                                 (reducer (term (ltm fun))))
                                (reducer (app (rtm fun)
                                              (list (index-excess term)))))))
             ((and (typep fun 'case-on)
                   (typep (ltm fun) 'lamb)
                   (typep (rtm fun) 'case-on))
              (reducer (case-on (reducer (on fun))
                                (reducer (app (ltm fun)
                                              (list (index-excess term))))
                                (substitute-zero (index-excess (reducer term))
                                                 (reducer (term (rtm fun)))))))
             ((typep fun 'err)
              (err (mcadr (ttype fun))))
             (t (app (reducer fun) (list (reducer term)))))))
    ((or lamb-eq
         lamb-lt)
     (let ((ltm (ltm tterm))
           (rtm (rtm tterm)))
       (if (and (typep ltm 'bit-choice)
                (typep rtm 'bit-choice))
           (if (funcall (dispatch-arith tterm)
                        (bitv ltm)
                        (bitv rtm))
               (left so1 (unit))
               (right so1 (unit)))
           (funcall (dispatch tterm)
                    (reducer ltm)
                    (reducer rtm)))))
    ((or plus
         times
         minus
         divide
         modulo)
     (let ((ltm (ltm tterm))
           (rtm (rtm tterm)))
       (if (and (typep ltm 'bit-choice)
                (typep rtm 'bit-choice))
           (bit-choice
            (funcall (dispatch-arith tterm)
                     (bitv ltm)
                     (bitv rtm)))
           (funcall (dispatch tterm)
                    (reducer ltm)
                    (reducer rtm)))))
    ((or unit
         index
         err
         bit-choice)
     tterm)))

(defun substitute-zero (replaced-term replacing-term)
  "Substitutes the zero'th index, and properly marks it"
  (delist (index-lack 0 (sub 0 replaced-term replacing-term))))
