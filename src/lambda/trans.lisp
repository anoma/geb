(in-package :geb.lambda.trans)

(named-readtables:in-readtable :fare-quasiquote)

(deftype stlc-context () `list)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Main Transformers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgeneric compile-checked-term (context term)
  (:documentation "Compiles a checked term in an appropriate context into the
morphism of the GEB category. In detail, it takes a context and a term with
following restrictions: Terms come from [STLC][class]  with occurences of
[SO-HOM-OBJ][GEB.MAIN:SO-HOM-OBJ] replaced by [FUN-TYPE][class] and should
come without the slow of [TTYPE][generic-function] accessor filled for any of
the subterms. Context should be a list of [SUBSTOBJ][GEB.SPEC:SUBSTOBJ] with
the caveat that instead of [SO-HOM-OBJ][GEB.MAIN:SO-HOM-OBJ] we ought to use
[FUN-TYPE][class], a stand-in for the internal hom object with explicit
accessors to the domain and the codomain. Once again, note that it is important
for the context and term to be giving as per above description. While not
always, not doing so result in an error upon evaluation. As an example of a
valid entry we have

```lisp
 (compile-checked-term (list so1 (fun-type so1 so1)) (app (index 0) (index 1)))
```

while

```lisp
(compile-checked-term (list so1 (so-hom-obj so1 so1)) (app (index 0) (index 1)))
```

produces an error. Error of such kind mind pop up both on the level of evaluating
[WELL-DEFP][generic-function] and [ANN-TERM1][generic-function]."))

(-> to-poly (list <stlc>) (or geb.poly:<poly> geb.poly:poly))
(defun to-poly (context obj)
  (assure (or geb.poly:<poly> geb.poly:poly)
    (~>> obj
         (compile-checked-term context)
         geb:to-poly)))

(-> to-circuit (list <stlc> keyword) geb.vampir.spec:statement)
(defun to-circuit (context obj name)
  (assure geb.vampir.spec:statement
    (~> (to-poly context obj)
        (geb.poly:to-circuit name))))

(defmethod empty ((class (eql (find-class 'list)))) nil)

(defun maybe (f)
  "Takes a morphism f : a -> b in Geb and produces
Maybe(f) : (1 + a) -> (1 + b)"
  (mcase (->left so1 (codom f)) (comp (->right so1 (codom f)) f)))

(defmethod compile-err (context (tterm <stlc>))
  (labels ((rec (context tterm)
             (match-of stlc tterm
               ((absurd tcod term)
                (comp (maybe (init tcod))
                      (rec context term)))     
               (unit
                (comp (->right so1 so1) (terminal (stlc-ctx-to-mu context))))
               ((left rty term)
                (let ((tott (ttype tterm)))
                  (comp (maybe (->left (mcar tott) rty))
                        (rec context term))))    
               ((right term)
                (let ((tott (ttype tterm)))
                  (comp (maybe (->right (mcar tott) (mcadr tott)))
                        (rec context term))))
               ((case-on on ltm rtm)
                (let ((toon (ttype on)))
                  (comp (maybe (mcase (curry (rec
                                              (cons (mcar toon) context) ltm))
                                      (curry (rec
                                              (cons (mcadr toon) context) rtm))))
                        (rec context on))))
               ((pair ltm rtm)
                (let ((lty  (ttype ltm))
                      (rty  (ttype rtm))
                      (pty  (prod (ttype ltm) (ttype rtm)))
                      (1lty (coprod so1 (ttype ltm))))
                  ;; correctness was checked in Agda
                  ;; may need further optimization
                  (comp (mcase (->left so1 pty)
                               (mcase (comp (->left so1 pty)
                                            (terminal rty))
                                      (->right so1 pty))) 
                        (comp (geb.main:coprod-mor (terminal (prod 1lty
                                                                   so1))
                                          (comp (geb.main:coprod-mor
                                                 (<-left rty so1)
                                                 (commutes rty lty))
                                                (comp (distribute rty so1 lty)
                                                      (commutes 1lty
                                                                rty))))
                              (distribute 1lty
                                          so1 rty)))))
               ((fst term)
                (let ((tottt (ttype term)))
                  (comp (maybe (<-left (mcar tottt) (mcadr tottt)))
                        (rec context term))))
               ((snd term)
                (let ((tottt (ttype term)))
                  (comp (maybe (<-right (mcar tottt) (mcadr tottt)))
                        (compile-checked-term context term))))
               ((lamb tdom term)
                
                t)  
               ((app fun term)
                (let ((tofun (ttype fun)))
                  (comp
                   (so-eval (fun-to-hom (mcar tofun))
                            (fun-to-hom (mcadr tofun)))
                   (geb:pair (rec context
                                  fun)
                             (rec context
                                  term)))))
               ((index pos)
                (comp (->right so1 (nth pos context)) (stlc-ctx-proj context pos)))
               ((err ttype)
                (comp (->left so1 ttype) (terminal (stlc-ctx-to-mu context)))))))
    (let ((ann-term (ann-term1 context tterm)))
      (if (well-defp context ann-term)
          (rec context ann-term)
          (error "not a well-defined ~A in said ~A" tterm context)))))

(defmethod compile-checked-term (context (tterm <stlc>))
  (labels ((rec (context tterm)
             (match-of stlc tterm
               ((absurd tcod term)
                (comp (init tcod)
                      (rec context term))) 
               (unit
                (terminal (stlc-ctx-to-mu context)))
               ((left term)
                (let ((tott (ttype tterm)))
                  (comp (->left (mcar tott) (mcadr tott))
                        (rec context term))))
               ((right term)
                (let ((tott (ttype tterm)))
                  (comp (->right (mcar tott) (mcadr tott))
                        (rec context term))))
               ((case-on on ltm rtm)
                (let ((toon (ttype on)))
                  (comp (mcase (curry (rec
                                       (cons (mcar toon) context) ltm))
                               (curry (rec
                                       (cons (mcadr toon) context) rtm)))
                        (rec context on))))
               ((pair ltm rtm)
                (geb:pair (rec context ltm)
                          (rec context rtm)))
               ((fst term)
                (let ((tottt (ttype term)))
                  (comp (<-left (mcar tottt) (mcadr tottt))
                        (rec context term))))
               ((snd term)
                (let ((tottt (ttype term)))
                  (comp (<-right (mcar tottt) (mcadr tottt))
                        (compile-checked-term context term))))
               ((lamb tdom term)
                (curry (commutes-left
                        (rec (cons tdom context) term))))
               ((app fun term)
                (let ((tofun (ttype fun)))
                  (comp
                   (so-eval (fun-to-hom (mcar tofun))
                            (fun-to-hom (mcadr tofun)))
                   (geb:pair (rec context
                                  fun)
                             (rec context
                                  term)))))
               ((index pos)
                (stlc-ctx-proj context pos))
               ((err ttype)
                (comp (->left so1 ttype) (terminal (stlc-ctx-to-mu context)))))))
    (let ((ann-term (ann-term1 context tterm)))
      (if (well-defp context ann-term)
          (rec context ann-term)
          (error "not a well-defined ~A in said ~A" tterm context)))))

(-> stlc-ctx-to-mu (stlc-context) substobj)
(defun stlc-ctx-to-mu (context)
  "Converts a generic [<STLC>][type] context into a
[SUBSTMORPH][GEB.SPEC:SUBSTMORPH]. Note that usually contexts can be interpreted
in a category as a $\Sigma$-type, which in a non-dependent setting gives us a
usual [PROD][type]"
  (mvfoldr #'prod (mapcar #'fun-to-hom context) so1))

(app (lamb
      (fun-type
       (fun-type
        (coprod so1 so1)
        (coprod so1 so1))
       (coprod so1 so1))
      (app
       (index 0)
       (lamb (coprod so1 so1)
             (index 1))))
      (lamb
       (fun-type (coprod so1 so1)
                 (coprod so1 so1))
        (left so1 (unit))))

(-> so-hom (substobj substobj) (or t substobj))
(defun so-hom (dom cod)
  "Computes the hom-object of two [SUBSTMORPH]s"
  (geb:so-hom-obj dom cod))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Utility Functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun stlc-ctx-proj (context depth)
  "Given a context, we interpret it as a [PROD][type] object of appropriate
length with fibrations given by [PROD][type] projections."
  (if (zerop depth)
      (<-left (fun-to-hom (car context))
              (stlc-ctx-to-mu (cdr context)))
      (comp (stlc-ctx-proj (cdr context) (1- depth))
            (<-right (fun-to-hom (car context))
                     (stlc-ctx-to-mu (cdr context))))))

(defun index-to-projection (depth typ-a typ-b prod)
  (if (zerop depth)
      (comp (<-left typ-a typ-b) prod)
      (comp (index-to-projection (1- depth) (mcar typ-b) (mcadr typ-b) prod)
            (<-right typ-a typ-b))))

(-> index-to-obj (fixnum t) t)
(defun index-to-obj (depth typ)
  (if (zerop depth)
      (mcar typ)
      (index-to-obj (1- depth) (mcadr typ))))

(-> call-objmap (functor t) t)
(defun call-objmap (functor-body arg)
  (funcall (obj functor-body) arg))

(-> call-morphmap (functor t t t) t)
(defun call-morphmap (functor-body typ-a typ-b arg)
  (funcall (func functor-body) typ-a typ-b arg))
