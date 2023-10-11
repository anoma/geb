(in-package :geb.lambda.trans)

(named-readtables:in-readtable :fare-quasiquote)

(deftype stlc-context () `list)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Main Transformers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmethod to-bitc ((obj <stlc>))
  "I convert a lambda term into a [GEB.BITC.SPEC:BITC] term

Note that [\\<STLC\\>] terms with free variables require a context,
and we do not supply them here to conform to the standard interface

If you want to give a context, please call [to-cat] before
calling me"
  (~>> obj
       (to-cat nil)
       geb.common:to-bitc))

(defmethod to-poly ((obj <stlc>))
  "I convert a lambda term into a [GEB.POLY.SPEC:POLY] term

Note that [\\<STLC\\>] terms with free variables require a context,
and we do not supply them here to conform to the standard interface

If you want to give a context, please call [to-cat] before
calling me"
  (~>> obj
       (to-cat nil)
       geb.common:to-poly))

(defmethod to-seqn ((obj <stlc>))
  "I convert a lambda term into a [GEB.SEQN.SPEC:SEQN] term

Note that [\\<STLC\\>] terms with free variables require a context,
and we do not supply them here to conform to the standard interface

If you want to give a context, please call [to-cat] before
calling me"
  (~>> obj
       (to-cat nil)
       geb.common:to-seqn))

(defmethod to-circuit ((obj <stlc>) name)
  "I convert a lambda term into a vampir term

Note that [\\<STLC\\>] terms with free variables require a context,
and we do not supply them here to conform to the standard interface

If you want to give a context, please call [to-cat] before
calling me"
  (assure list
    (~> (to-seqn obj)
        (geb.common:to-circuit name))))

(defmethod empty ((class (eql (find-class 'list)))) nil)

(defmethod to-cat (context (tterm <stlc>))
  "Compiles a checked term in said context to a Geb morphism. If the term has
an instance of an erorr term, wraps it in a Maybe monad, otherwise, compiles
according to the term model interpretation of STLC"
  (if (errorp tterm)
      (to-cat-err context tterm)
      (to-cat-cor context tterm)))

(defun maybe-comp (ob)
  "Takes a [SUBSTOBJ][GEB.SPEC:SUBSTOBJ] with possible fun-type instances
and removes them"
  (fun-to-hom (maybe ob)))

(defun maybe-rest (ob)
  "Takes a Geb object wrapped in Maybe and gives out the part without the
error node"
  (mcadr (maybe-comp ob)))

(defun dispatch (tterm)
  (typecase tterm
    (plus #'nat-add)
    (minus #'nat-sub)
    (times #'nat-mult)
    (divide #'nat-div)
    (lamb-eq #'nat-eq)
    (lamb-lt #'nat-lt)
    (modulo #'nat-mod)))

(defparameter *int* (nat-width 24)
  "A Juvix stand-in for a type of integers of their bit-choice.
In this version, the choice is that of 24-bits.")

(def int *int*)

(defmethod to-cat-err (context (tterm <stlc>))
  "Compiles a checked term with an error term in an appropriate context into the
morphism of the GEB category using a Maybe monad wrapper, that is, given a
context G and a term t of type A produces a morphism with domain
(stlc-ctx-maybe context) and codomain (maybe A).

Terms come from [STLC][type] with occurences of [SO-HOM-OBJ][GEB.COMMON:SO-HOM-OBJ]
replaced by [FUN-TYPE][class] and should come without the slow of
[TTYPE][generic-function] accessor filled for any of the subterms. Context should
be a list of [SUBSTOBJ][GEB.SPEC:SUBSTOBJ] with the caveat that instead of
[SO-HOM-OBJ][GEB.COMMON:SO-HOM-OBJ] we ought to use [FUN-TYPE][class], a stand-in
for the internal hom object with explicit accessors to the domain and the
codomain. Once again, note that it is important for the context and term to be
giving as per above description. While not always, not doing so result in an
error upon evaluation. As an example of a valid entry we have

```lisp
 (to-cat-err (list so1 (fun-type so1 so1)) (app (index 1) (list (error so1))))
```

while

```lisp
(to-cat-err (list so1 (so-hom-obj so1 so1)) (app (index 1) (list (error so1))))
```

produces an error. Error of such kind mind pop up both on the level of evaluating
[WELL-DEFP][generic-function] and [ANN-TERM1][generic-function].

Moreover, note that for terms whose typing needs addition of new context
we append contexts on the left rather than on the right contra usual type
theoretic notation for the convenience of computation. That means, e.g. that
asking for a type of a lambda term as below produces:

```lisp
LAMBDA> (ttype (term (ann-term1 nil (lamb (list so1 so0) (index 0)))))
s-1
```

as we count indeces from the left of the context while appending new types to
the context on the left as well. For more info check [LAMB][class]

Note that the Maybe wrapper also applies to the context elements due to
functoriality concerns. Hence if one wanted to check the whether the term
(case-on (index 0) (err so1) (unit)) with a bool in contexts fails on the
left entry, one would need to evaluate

```lisp
LAMBDA> (gapply  (to-cat (list (coprod so1 so1))
                         (case-on (index 0)
                                  (err so1)
                                  (unit)))
                         (list (geb:right (geb:left (geb:right so1))) so1))
(left s-1)
```

and hence get an error part of the wrapper. While evaluating the right branch
will be done by:

```lisp
  LAMBDA> (gapply  (to-cat (list (coprod so1 so1))
                           (case-on (index 0)
                                    (err so1)
                                    (unit)))
                   (list (geb:right (geb:right (geb:right so1))) so1))
(right s-1)
```

This follows from the fact that bool arapped in maybe is 1 + (bool + bool)"
  (labels ((rec (context tterm)
             (match-of stlc tterm
               ((absurd tcod term)
                (comp  (mcase (->left so1 (maybe-rest tcod))
                              (init (maybe-comp tcod)))
                       (rec context term)))
               (unit
                (comp (->right so1 so1)
                      (terminal (stlc-ctx-maybe context))))
               ((left rty term)
                (comp  (->right so1 (maybe-rest (ttype tterm)))
                       (comp (->left (maybe-comp (ttype term))
                                     (maybe-comp rty))
                             (rec context term))))
               ((right lty term)
                (comp (->right so1 (maybe-rest (ttype tterm)))
                      (comp  (->right (maybe-comp lty)
                                      (maybe-comp (ttype term)))
                             (rec context term))))
               ((case-on on ltm rtm)
                (let ((mcartoon  (mcar (ttype on)))
                      (mcadrtoon (mcadr (ttype on)))
                      (ctx       (stlc-ctx-maybe context)))
                  (comp (mcase (comp (->left so1 (maybe-rest (ttype tterm)))
                                     (terminal (prod ctx so1)))
                               (comp (mcase (commutes-left
                                             (rec
                                              (cons mcartoon
                                                    context)
                                              ltm))
                                            (commutes-left
                                             (rec
                                              (cons mcadrtoon
                                                    context)
                                              rtm)))
                                     (distribute ctx
                                                 (maybe-comp mcartoon)
                                                 (maybe-comp mcadrtoon))))
                        (comp (distribute ctx
                                          so1
                                          (maybe-rest (coprod mcartoon
                                                              mcadrtoon)))
                              (geb:pair ctx (rec context on))))))
               ((pair ltm rtm)
                (let ((lty  (ttype ltm))
                      (rty  (ttype rtm)))
                  (comp (->right so1 (prod (maybe-comp lty)
                                           (maybe-comp rty)))
                        (geb:pair (rec context ltm)
                                  (rec context rtm)))))
               ((fst term)
                (let ((mcarttot (mcar (ttype term))))
                  (comp (mcase (->left so1 (maybe-rest mcarttot))
                               (<-left (maybe-comp mcarttot)
                                       (maybe (mcadr (ttype term)))))
                        (rec context term))))
               ((snd term)
                (let ((mcadrttot (mcadr (ttype term))))
                  (comp (mcase (->left so1 (maybe-rest mcadrttot))
                               (<-right (maybe-comp (mcar (ttype term)))
                                        (maybe-comp mcadrttot)))
                        (rec context term))))
               ((lamb tdom term)
                (comp (->right so1 (maybe-rest (fun-to-hom (ttype tterm))))
                      (apply-n (length tdom)
                               #'(lambda (x) (curry (commutes-left x)))
                               (rec (append
                                     (mapcar #'maybe-comp tdom)
                                     context) term))))
               ((app fun term)
                (let ((tofun (ttype fun)))
                  (comp
                   (mcase (->left so1 (maybe-rest tofun))
                          (commutes-left
                           (so-eval (maybe-comp (mcar tofun))
                                    (maybe-comp (mcadr tofun)))))
                   (comp (distribute (reduce #'prod
                                             (mapcar #'maybe-comp term)
                                             :from-end t)
                                     so1
                                     (maybe-rest tofun))
                         (geb:pair (reduce #'geb:pair
                                           (mapcar #'(lambda (x) (rec context x)) term)
                                           :from-end t)
                                   (rec context
                                        fun))))))
               ((index pos)
                (stlc-ctx-proj (mapcar #'maybe context) pos))
               ((bit-choice bitv)
                (comp (comp (->right so1 (ttype tterm))
                            (nat-const (ttype tterm) (reduce
                                                      #'(lambda (a b)
                                                          (+ (ash a 1) b))
                                                      bitv)))
                      (terminal (stlc-ctx-maybe context))))
               ((err ttype)
                (comp (->left so1 (maybe-comp ttype))
                      (terminal (stlc-ctx-maybe context))))
               ((or plus
                    minus
                    times
                    divide
                    lamb-eq
                    lamb-lt
                    modulo)
                (let ((tyltm (ttype (ltm tterm))))
                  (labels ((arith (op)
                             (comp (mcase (terminal (prod (maybe tyltm)
                                                          so1))
                                          (commutes-left (comp
                                                          (mcase (terminal (prod tyltm
                                                                                 so1))
                                                                 (funcall op tyltm))
                                                          (distribute tyltm
                                                                      so1
                                                                      tyltm))))
                                   (comp (distribute (maybe tyltm)
                                                     so1
                                                     tyltm)
                                         (geb:pair (rec context (ltm tterm))
                                                   (rec context (rtm tterm)))))))
                    (arith (dispatch tterm))))))))
    (if (not (well-defp context tterm))
        (error "not a well-defined ~A in said ~A" tterm context)
        (rec context (ann-term1 context tterm)))))

(defmethod to-cat-cor (context (tterm <stlc>))
  "Compiles a checked term in an appropriate context into the
morphism of the GEB category. In detail, it takes a context and a term with
following restrictions: Terms come from [STLC][type]  with occurences of
[SO-HOM-OBJ][GEB.COMMON:SO-HOM-OBJ] replaced by [FUN-TYPE][class] and should
come without the slow of [TTYPE][generic-function] accessor filled for any of
the subterms. Context should be a list of [SUBSTOBJ][GEB.SPEC:SUBSTOBJ] with
the caveat that instead of [SO-HOM-OBJ][GEB.COMMON:SO-HOM-OBJ] we ought to use
[FUN-TYPE][class], a stand-in for the internal hom object with explicit
accessors to the domain and the codomain. Once again, note that it is important
for the context and term to be giving as per above description. While not
always, not doing so result in an error upon evaluation. As an example of a
valid entry we have

```lisp
 (to-cat-cor (list so1 (fun-type so1 so1)) (app (index 1) (list (index 0))))
```

while

```lisp
(to-cat-cor (list so1 (so-hom-obj so1 so1)) (app (index 1) (list (index 0))))
```

produces an error. Error of such kind mind pop up both on the level of evaluating
[WELL-DEFP][generic-function] and [ANN-TERM1][generic-function].

Moreover, note that for terms whose typing needs addition of new context
we append contexts on the left rather than on the right contra usual type
theoretic notation for the convenience of computation. That means, e.g. that
asking for a type of a lambda term as below produces:

```lisp
LAMBDA> (ttype (term (ann-term1 nil (lamb (list so1 so0) (index 0)))))
s-1
```

as we count indeces from the left of the context while appending new types to
the context on the left as well. For more info check [LAMB][class]

Finally, note that the compilation uncurries the final morphism. That is,
if the type of the term is an exponential object, [TO-CAT-COR] uncurries the
morphism in the Geb category instead producing a morphism into the domain
of the exponential from a corresponding product. If the exponential is
iterated, so is the uncurrying."
  (labels ((rec (context tterm)
             (match-of stlc tterm
               ((absurd tcod term)
                (comp (init tcod)
                      (rec context term)))
               (unit
                (terminal (stlc-ctx-to-mu context)))
               ((left rty term)
                (comp (->left (ttype term) rty)
                      (rec context term)))
               ((right lty term)
                (comp (->right lty (ttype term))
                      (rec context term)))
               ((case-on on ltm rtm)
                (let ((mcartoon  (mcar (ttype on)))
                      (mcadrtoon (mcadr (ttype on)))
                      (ctx       (stlc-ctx-to-mu context)))
                  (comp (mcase (commutes-left (rec
                                               (cons (fun-to-hom mcartoon) context) ltm))
                               (commutes-left (rec
                                               (cons  (fun-to-hom mcadrtoon) context) rtm)))
                        (comp (distribute ctx mcartoon mcadrtoon)
                              (geb:pair ctx (rec context on))))))
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
                        (to-cat context term))))
               ((lamb tdom term)
                (apply-n (length tdom)
                         #'(lambda (x) (curry (commutes-left x)))
                         (rec (append tdom context) term)))
               ((app fun term)
                (let ((tofun (ttype fun))
                      (reducify (reduce #'geb:pair
                                        (mapcar #'(lambda (x) (rec context x))
                                                term)
                                        :from-end t)))
                  (if (typep fun 'lamb)
                      (comp (to-cat-cor context fun)
                            (geb:pair reducify
                                      (stlc-ctx-to-mu context)))
                      (comp
                       (so-eval (fun-to-hom (mcar tofun))
                                (fun-to-hom (mcadr tofun)))
                       (geb:pair (rec context fun)
                                 reducify)))))
               ((index pos)
                (stlc-ctx-proj context pos))
               ((bit-choice bitv)
                (comp (nat-const 24
                                 bitv)
                      (terminal (stlc-ctx-to-mu context))))
               (err
                (error "Not meant for the compiler"))
               ((or plus
                    minus
                    times
                    divide
                    lamb-eq
                    lamb-lt
                    modulo)
                (let ((ltm (ltm tterm)))
                  (labels ((arith (op)
                             (comp (funcall op (num (ttype ltm)))
                                   (geb:pair (rec context ltm)
                                             (rec context (rtm tterm))))))
                    (arith (dispatch tterm)))))))
           (rec1 (ctx tterm)
             (if (typep tterm 'lamb)
                 (rec1 (append (tdom tterm) ctx)
                       (term tterm))
                 (list ctx tterm))))
    (if (not (well-defp context tterm))
        (error "not a well-defined ~A in said ~A" tterm context)
        (let* ((term (geb.lambda.main:reducer tterm))
               (recc (rec1 context term))
               (car (car recc)))
          (rec car
               (ann-term1 car
                          (cadr recc)))))))

(-> stlc-ctx-to-mu (stlc-context) substobj)
(defun stlc-ctx-to-mu (context)
  "Converts a generic [<STLC>][type] context into a
[SUBSTMORPH][GEB.SPEC:SUBSTMORPH]. Note that usually contexts can be interpreted
in a category as a $\Sigma$-type$, which in a non-dependent setting gives us a
usual [PROD][class]

```lisp
LAMBDA> (stlc-ctx-to-mu (list so1 (fun-to-hom (fun-type geb-bool:bool geb-bool:bool))))
(× s-1
   (× (+ GEB-BOOL:FALSE GEB-BOOL:TRUE) (+ GEB-BOOL:FALSE GEB-BOOL:TRUE))
   s-1)
```"
  (mvfoldr #'prod (mapcar #'fun-to-hom context) so1))

(defun stlc-ctx-maybe (context)
  "Takes a context seen as product of appropriate [SUBSTOBJ][GEB.SPEC:SUBSTOBJ]
and iteratively applies Maybe to its elements."
  (mvfoldr #'prod (mapcar (lambda (x) (maybe-comp x)) context) so1))

(-> so-hom (substobj substobj) (or t substobj))
(defun so-hom (dom cod)
  "Computes the hom-object of two [SUBSTMORPH]s"
  (so-hom-obj dom cod))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Utility Functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defun stlc-ctx-proj (context depth)
  "Given a context, we interpret it as a [PROD][class] object of appropriate
length with fibrations given by [PROD][class] projections."
  (if (zerop depth)
      (<-left (fun-to-hom (car context))
              (stlc-ctx-to-mu (cdr context)))
      (comp (stlc-ctx-proj (cdr context) (1- depth))
            (<-right (fun-to-hom (car context))
                     (stlc-ctx-to-mu (cdr context))))))

(defun prod-rem (num obj)
  "Given a product A0 x A1 x ... x An and a positive integer k gives a
corresponding composition of morphisms projecting to Ak x ... x An"
  (if (= num 1)
      (<-right (mcar obj) (mcadr obj))
      (comp (<-right (mcar (apply-n (- num 1) #'mcadr obj))
                     (apply-n num #'mcadr obj))
            (prod-rem (1- num) obj))))

(defun prod-proj (num obj)
  "Given a product A0 x ... x An and an integer k less than n gives a
corresponding composition of projection morphism to Ak"
  (if (zerop num)
      (<-left (mcar obj) (mcadr obj))
      (let ((codm (codom (prod-rem num obj))))
        (comp (<-left (mcar codm) codm)
              (prod-rem num obj)))))

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
