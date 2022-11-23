(in-package #:geb.lambda.spec)

;; maybe expand this macro and change each defconstant into a proper
;; class declaration. We avoid typing it as we don't actually want to
;; be exhaustive, but rather open.
(defunion stlc
  (absurd (value t))
  unit
  (left (value t))
  (right (value t))
  (case-on (lty geb.spec:substmorph)
           (rty geb.spec:substmorph)
           (cod geb.spec:substmorph)
           (on t) (left t) (right t))
  (pair (lty geb.spec:substmorph) (rty geb.spec:substmorph) (left t) (right t))
  (fst  (lty geb.spec:substmorph) (rty geb.spec:substmorph) (value t))
  (snd  (lty geb.spec:substmorph) (rty geb.spec:substmorph) (value t))
  (lamb (vty geb.spec:substmorph) (tty geb.spec:substmorph) (value t))
  (app  (dom geb.spec:substmorph) (cod geb.spec:substmorph) (func t) (obj t))
  (index (index fixnum)))
