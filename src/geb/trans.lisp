;; Transition or Translation functions about geb

(in-package :geb.trans)

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
                         ;; we want to bitshift it by the size
                         (poly:/
                          (poly:- poly:ident
                                  ;; we need to remove the right value
                                  ;; we are doing project-right
                                  (to-poly (<-right (mcar obj) (mcadr obj))))
                          nat))))
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

(defmethod to-circuit ((obj <substmorph>) name)
  "Turns a @GEB-SUBSTMORPH to a Vamp-IR Term"
  (to-circuit (to-seqn obj) name))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Morph to Bitc Implementation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmethod bitwidth ((obj <substobj>))
  (typecase-of substobj obj
    (so0     0)
    (so1     0)
    (coprod  (+ 1 (max (bitwidth (mcar obj)) (bitwidth (mcadr obj)))))
    (prod    (+ (bitwidth (mcar obj)) (bitwidth (mcadr obj))))
    (otherwise (subclass-responsibility obj))))

(defmethod to-bitc ((obj <substmorph>))
  (typecase-of substmorph obj
    (substobj
     (bitc:ident (bitwidth obj)))
    (comp
     (bitc:compose (to-bitc (mcar obj))
                   (to-bitc (mcadr obj))))
    ;; This should never occure, but if it does, it produces a
    ;; constant morphism onto an all 0s list
    (init
     (let* ((list (zero-list (bitwidth (mcar obj))))
            (len  (length list)))
       (cond ((= 0 len) (bitc:drop 0))
             ((= 1 len) bitc:zero)
             (t         (apply #'bitc:parallel list)))))
    ;; Terminal maps any bit-list onto the empty bit-list
    (terminal
     (bitc:drop (bitwidth (mcar obj))))

    ;; Inject-left x -> x + y tags the x with a 0, indicating left,
    ;;   and pads the encoded x with as many zeros as would be needed
    ;;   to store either an x or a y.
    (inject-left
     (let ((car-width  (bitwidth (mcar obj)))
           (cadr-width (bitwidth (mcadr obj))))
       (apply #'bitc:parallel
              (append (list bitc:zero (bitc:ident car-width))
                      (zero-list (padding-bits cadr-width
                                               car-width))))))
    ;; Inject-right y -> x + y tags the y with a 1, indicating right,
    ;;   and pads the encoded y with as many zeros as would be needed
    ;;   to store either an x or a y.
    (inject-right
     (let ((car-width  (bitwidth (mcar obj)))
           (cadr-width (bitwidth (mcadr obj))))
       (apply #'bitc:parallel
              (append (list bitc:one (bitc:ident cadr-width))
                      (zero-list (padding-bits car-width
                                               cadr-width))))))

    ;; Case translates directly into a branch. The sub-morphisms of
    ;; case are padded with drop so they have the same input lengths.
    (case
      (let ((car-width  (bitwidth (dom (mcar obj))))
            (cadr-width (bitwidth (dom (mcadr obj)))))
        (bitc:branch (bitc:parallel (to-bitc (mcar obj))
                                    (bitc:drop
                                     (padding-bits cadr-width car-width)))
                     (bitc:parallel (to-bitc (mcadr obj))
                                    (bitc:drop
                                     (padding-bits car-width cadr-width))))))
    ;; project-left just drops any bits not being used to encode the
    ;; first component.
    (project-left
     (bitc:parallel (bitc:ident (bitwidth (mcar obj)))
                    (bitc:drop (bitwidth (mcadr obj)))))

    ;; project-right just drops any bits not being used to encode the
    ;; second component.
    (project-right
     (bitc:parallel (bitc:drop (bitwidth (mcar obj)))
                    (bitc:ident (bitwidth (mcadr obj)))))

    ;; Pair will copy the input and run the encoded morphisms in pair
    ;; on the two copied subvetors.
    (pair
     (bitc:compose (bitc:parallel (to-bitc (mcar obj)) (to-bitc (mcdr obj)))
                   (bitc:fork (bitwidth (dom (mcar obj))))))
    ;; a * (b + c) will be encoded as [a] [0 or 1] [b or c]. By
    ;; swapping the [0 or 1] with [a], we get an encoding for (a * b)
    ;; + (a * c).
    (distribute
     (bitc:parallel (bitc:swap (bitwidth (mcar obj)) 1)
                    (bitc:ident (max (bitwidth (mcadr obj))
                                     (bitwidth (mcaddr obj))))))
    (otherwise (subclass-responsibility obj))))

(defun zero-list (length)
  (make-list length :initial-element bitc:zero))

(-> padding-bits ((integer 0) (integer 0)) (integer 0))
(defun padding-bits (number number2)
  "
```lisp
(max number number2)
```
is the bits needed to store NUMBER or NUMBER2

Thus if we want to calculate the number of padding bits needed then we
should calculate

```lisp
(- (max number number2) number2)
```

We use an optimized version in actual code, which happens to compute the same result"
  (max (- number number2) 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Geb to Seqn Implementation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmethod to-seqn ((obj <substobj>))
  "Preserves identity morphims"
  (seqn:id (geb.common:width obj)))

(defmethod to-seqn ((obj geb.extension.spec:<natobj>))
  (seqn:id (geb.common:width obj)))

(defmethod to-seqn ((obj comp))
  "Preserves composition"
  (seqn:composition (to-seqn (mcar obj))
                    (to-seqn (mcadr obj))))

(defmethod to-seqn ((obj init))
  "Produces a list of zeroes
Currently not aligning with semantics of drop-width
as domain and codomain can be of differing lengths"
  (seqn:drop-width (list 0)
                   (width (mcar obj))))

(defmethod to-seqn ((obj terminal))
  "Drops everything to the terminal object,
i.e. to nothing"
  (drop-nil (width (mcar obj))))

(defmethod to-seqn ((obj inject-left))
  "Injects an x by marking its entries with 0
and then inserting as padded bits if necessary"
  (let ((l1 (width (mcar obj)))
        (l3 (width (coprod (mcar obj)
                              (mcadr obj)))))
    ;; (a1,...,an) -> (0, a1,...,an) -> (1, max(a1, b1),..., max(an, 0) or max(an, bn))
    ;; if lengths match
    (composition (parallel-seq zero-bit
                               (inj-coprod-parallel l1 l3))
                 (inj-length-right (list 0)
                                   l1))))

(defmethod to-seqn ((obj inject-right))
  "Injects an x by marking its entries with 1
and then inserting as padded bits if necessary"
  (let ((l2 (width (mcadr obj)))
        (l3 (width (coprod (mcar obj)
                              (mcadr obj)))))
    (composition (parallel-seq one-bit
                               (inj-coprod-parallel l2
                                                    l3))
                 (inj-length-right (list 0)
                                   l2))))

(defmethod to-seqn ((obj case))
  "Cases by forgetting the padding and if necessary dropping
the extra entries if one of the inputs had more of them to start
with"
  (let* ((lft (dom (mcar obj)))
         (rt  (dom (mcadr obj)))
         (cpr (dom obj))
         (wlft (width lft))
         (wrt  (width rt))
         (mcar (mcar obj))
         (mcadr (mcadr obj))
         (lengthleft (length wlft))
         (lengthright (length wrt)))
    (labels
        ((funor (x y z)
           (composition (to-seqn z)
                        (composition (remove-right x)
                                     (parallel-seq
                                      (drop-width (butlast
                                                   (cdr (width cpr))
                                                   (- (length y)
                                                      (length x)))
                                                  x)
                                      (drop-nil (nthcdr (1+ (length x))
                                                        (width cpr)))))))
         (funinj (x y)
           (composition (to-seqn x)
                        (drop-width (cdr (width cpr)) y))))
      (cond ((< lengthleft lengthright)
             ;; branch on the left counts the first entries of an occuring and drops the rest
             ;; then injects it into the smaller bit sizes if necessary
             ;; (max(a1, b1),,,.,(max (an, bn),..., max(0, bm))) -> (a1,...,an,0)
             ;; -> (a1,....,an)
             ;; branch on the right is just injecting
             ;; (max(a1, b1),..., max(0, bn)) -> (b1, ...., bn) -> codom))
             (branch-seq (funor wlft wrt mcar) (funinj mcadr wrt)))
            ((< lengthright lengthleft)
             (branch-seq (funinj mcar wlft) (funor wrt wlft mcadr)))
            ((= lengthright lengthleft)
             (branch-seq (funinj mcar wlft) (funinj mcadr wrt)))))))

(defmethod to-seqn ((obj project-left))
  "Takes a list of an even length and cuts the right half"
  (let ((sw (width (mcar obj))))
    (composition (remove-right sw)
                 (parallel-seq (id sw)
                               (drop-nil (width (mcadr obj)))))))

(defmethod to-seqn  ((obj project-right))
  "Takes a list of an even length and cuts the left half"
  (let ((sw (width (mcadr obj))))
    (composition (remove-left sw)
                 (parallel-seq (drop-nil (width (mcar obj)))
                               (id sw)))))

(defmethod to-seqn ((obj pair))
  "Forks entries and then applies both morphism
on corresponding entries"
  (composition (parallel-seq (to-seqn (mcar obj))
                             (to-seqn (mcdr obj)))
               (fork-seq (width (dom obj)))))

(defmethod to-seqn ((obj distribute))
  "Given A x (B + C) simply moves the 1-bit entry
to the front and keep the same padding relations to
get ((A x B) + (A x C)) as times appends sequences"
  (shift-front (width (dom obj))
               (1+ (length (width (mcar obj))))))

(defmethod to-seqn ((obj geb.extension.spec:nat-add))
  "Addition is interpreted as addition"
  (seqn-add (geb.extension.spec:num obj)))

(defmethod to-seqn ((obj geb.extension.spec:nat-mult))
  "Multiplication is interpreted as multiplication"
  (seqn-multiply (geb.extension.spec:num obj)))

(defmethod to-seqn ((obj geb.extension.spec:nat-sub))
  "Subtraction is interpreted as subtraction"
  (seqn-subtract (geb.extension.spec:num obj)))

(defmethod to-seqn ((obj geb.extension.spec:nat-div))
  "Division is interpreted as divition"
  (seqn-divide (geb.extension.spec:num obj)))

(defmethod to-seqn ((obj geb.extension.spec:nat-mod))
  "Modulo is interpreted as modulo"
  (seqn-mod (geb.extension.spec:num obj)))

(defmethod to-seqn ((obj geb.extension.spec:nat-const))
  "A choice of a natural number is the same exact choice in SeqN"
  (seqn-nat (geb.extension.spec:num obj) (geb.extension.spec:pos obj)))

(defmethod to-seqn ((obj geb.extension.spec:nat-inj))
  "Injection of bit-sizes is interpreted in the same maner in SeqN"
  (let ((num (geb.extension.spec:num obj)))
    (inj-size num (1+ num))))

(defmethod to-seqn ((obj geb.extension.spec:nat-concat))
  "Concatenation is interpreted as concatenation"
  (seqn-concat (geb.extension.spec:num-left obj)
               (geb.extension.spec:num-right obj )))

(defmethod to-seqn ((obj geb.extension.spec:one-bit-to-bool))
  "Iso interpreted in an evident manner"
  (inj-length-left (list 1) (list 0)))

(defmethod to-seqn ((obj geb.extension.spec:nat-decompose))
  "Decomposition is interpreted on the nose"
  (seqn-decompose (geb.extension.spec:num obj)))

(defmethod to-seqn ((obj geb.extension.spec:nat-eq))
  "Equality predicate is interpreted on the nose"
  (seqn-eq (geb.extension.spec:num obj)))

(defmethod to-seqn ((obj geb.extension.spec:nat-lt))
  "Equality predicate is interpreted on the nose"
  (seqn-lt (geb.extension.spec:num obj)))
