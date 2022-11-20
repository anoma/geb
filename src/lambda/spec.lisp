(in-package #:geb.lambda.spec)

;; maybe expand this macro and change each defconstant into a proper
;; class declaration. We avoid typing it as we don't actually want to
;; be exhaustive, but rather open.
(defunion stlc
  (absurd (value t))
  unit
  (left (value t))
  (right (value t))
  (case-on (lty geb:substmorph)
           (rty geb:substmorph)
           (cod geb:substmorph)
           (on t) (left t) (right t))
  (pair (lty geb:substmorph) (rty geb:substmorph) (left t) (right t))
  (fst  (lty geb:substmorph) (rty geb:substmorph) (value t))
  (snd  (lty geb:substmorph) (rty geb:substmorph) (value t))
  (lamb (vty geb:substmorph) (tty geb:substmorph) (value t))
  (app  (dom geb:substmorph) (cod geb:substmorph) (func t) (obj t))
  (index (index fixnum)))
