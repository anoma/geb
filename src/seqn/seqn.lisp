(in-package :geb.seqn.main)

(defun fill-in (num seq)
  "Fills in extra inputs on the right with 0-oes"
  (geb.utils:apply-n num (lambda (x) (append x (list 0))) seq))

(defun zero-list (n)
  (make-list n :initial-element 0))

(defun prod-list (l1 l2)
  "Takes two lists of same length and gives pointwise product
where first element come from first list and second from second

```lisp
SEQN> (prod-list (list 1 2) (list 3 4))
((1 3) (2 4))
```"
  (mapcar #'list l1 l2))

(defun seq-max-fill (seq1 seq2)
  "Takes two lists, makes them same length by adding 0es on the right
where necessary and takes their pointwise product"
  (let ((l1 (length seq1))
        (l2 (length seq2)))
    (if (< l1 l2)
        (prod-list (fill-in (- l2 l1) seq1) seq2)
        (prod-list seq1 (fill-in (- l1 l2) seq2)))))

(defun max-list (lst)
  (max (car lst) (cadr lst)))

(defmethod width ((obj <substobj>))
  (typecase-of substobj obj
    (so0 (list 0))
    (so1 (list 0))
    (coprod (cons 1
                  (mapcar #'max-list
                          (seq-max-fill (width (mcar obj))
                                        (width (mcadr obj))))))
    (prod (append (width (mcar obj))
                  (width (mcadr obj))))
    (otherwise (geb.utils:subclass-responsibility obj))))

(defmethod width ((obj <natobj>))
  (typecase-of natobj obj
    (nat-width (list (num obj)))
    (otherwise (geb.utils:subclass-responsibility obj))))

(defun inj-coprod-parallel (obj copr)
  "takes an width(A) or width(B) already transformed with a width(A+B)
and gives an appropriate injection of (a1,...,an) into
(max (a1, b1), ...., max(an, bn),...) i.e. where the maxes are being
taken during the width operation without filling in of the smaller object"
  (let* ((lng (length obj))
         (lngcoprod (1- (length copr)))
         (dif (- lngcoprod lng))
         (cdr (cdr copr)))
    (if (= lng lngcoprod)
        (drop-width obj cdr)
        (composition (drop-width (append obj (zero-list dif))
                                 cdr)
                     (inj-length-left obj (zero-list dif))))))

(defmethod dom ((x <seqn>))
  "Gives the domain of a morphism in SeqN.
For a less formal desription consult the specs file"
  (typecase-of seqn x
    (composition      (dom (mcadr x)))
    (fork-seq         (mcar x))
    (parallel-seq     (append (dom (mcar x)) (dom (mcadr x))))
    (id               (mcar x))
    (drop-nil         (mcar x))
    (remove-right     (append (mcar x) (list 0)))
    (remove-left      (cons 0 (mcar x)))
    (drop-width       (mcar x))
    (inj-length-left  (mcar x))
    (inj-length-right (mcadr x))
    (inj-size         (list (mcar x)))
    (branch-seq       (cons 1 (dom (mcar x))))
    (zero-bit         (list 0))
    (one-bit          (list 0))
    (shift-front      (mcar x))
    (seqn-add         (list (mcar x) (mcar x)))
    (seqn-subtract    (list (mcar x) (mcar x)))
    (seqn-multiply    (list (mcar x) (mcar x)))
    (seqn-divide      (list (mcar x) (mcar x)))
    (seqn-mod         (list (mcar x) (mcar x)))
    (seqn-nat         (list 0))
    (seqn-concat      (list (mcar x) (mcadr x)))
    (seqn-decompose   (list (mcar x)))
    (seqn-eq          (list (mcar x) (mcar x)))
    (seqn-lt          (list (mcar x) (mcar x)))
    (otherwise (geb.utils:subclass-responsibility x))))

(defmethod cod ((x <seqn>))
  "Gives the codomain of a morphism in SeqN.
For a less formal description consult the specs file"
  (typecase-of seqn x
    (composition      (cod (mcar x)))
    (fork-seq         (append  (mcar x) (mcar x)))
    (parallel-seq     (append (cod (mcar x)) (cod (mcadr x))))
    (id               (mcar x))
    (drop-nil         (list 0))
    (remove-right     (mcar x))
    (remove-left      (mcar x))
    (drop-width       (mcadr x))
    (inj-length-left  (append (mcar x) (mcadr x)))
    (inj-length-right (append (mcar x) (mcadr x)))
    (inj-size         (list (mcadr x)))
    (branch-seq       (cod (mcar x)))
    (zero-bit         (list 1))
    (one-bit          (list 1))
    (shift-front      (let ((mcar (mcar x))
                            (mcadr (mcadr x)))
                        (append (cons (nth (1- mcadr) mcar)
                                      (subseq mcar 0 (1- mcadr)))
                                (subseq mcar mcadr))))
    (seqn-add         (list (mcar x)))
    (seqn-subtract    (list (mcar x)))
    (seqn-multiply    (list (mcar x)))
    (seqn-divide      (list (mcar x)))
    (seqn-nat         (list (mcar x)))
    (seqn-mod         (list (mcar x)))
    (seqn-concat      (list (+ (mcar x) (mcadr x))))
    (seqn-decompose   (list 1 (1- (mcar x))))
    (seqn-eq          (list 1 0))
    (seqn-lt          (list 1 0))
    (otherwise (geb.utils:subclass-responsibility x))))

(defmethod gapply ((morphism <seqn>) vector)
  "Takes a list of vectors of natural numbers and gives out their evaluations.
Currently does not correspond directly to the intended semantics but
is capable of succesfully evaluating all compiled terms"
  (etypecase-of seqn morphism
    (id               vector)
    (composition      (gapply (mcar morphism)
                              (gapply (mcadr morphism) vector)))
    (parallel-seq     (append (gapply (mcar morphism)
                                      (subseq vector
                                              0 (length (dom (mcar morphism)))))
                              (gapply (mcadr morphism)
                                      (subseq vector
                                              (length (dom (mcar morphism)))))))
    (fork-seq         (append vector vector))
    (drop-nil         (list 0))
    (remove-right     (butlast vector))
    (remove-left      (cdr vector))
    (drop-width       vector)
    (inj-length-left  (append vector
                              (make-list (length (mcadr morphism))
                                         :initial-element 0)))
    (inj-length-right (append (make-list (length (mcar morphism))
                                         :initial-element 0)
                              vector))
    (inj-size         vector)
    (branch-seq       (if (= 0 (car vector))
                          (gapply (mcar morphism)
                                  (cdr vector))
                          (gapply (mcadr morphism)
                                  (cdr vector))))
    (shift-front      (append (cons (nth (1- (mcadr morphism))
                                         vector)
                                    (subseq vector 0 (1- (mcadr morphism))))
                              (subseq vector (mcadr morphism))))
    (zero-bit         (list 0))
    (one-bit          (list  1))
    (seqn-add         (list (+ (car vector) (cadr vector))))
    (seqn-subtract    (list (- (car vector) (cadr vector))))
    (seqn-multiply    (list (* (car vector) (cadr vector))))
    (seqn-divide      (list (multiple-value-bind (q)
                                (floor (car vector) (cadr vector)) q)))
    (seqn-mod         (list (mod (car vector) (cadr vector))))
    (seqn-nat         (list (mcadr morphism)))
    (seqn-concat      (list (+ (* (expt 2 (mcadr morphism)) (car vector))
                               (cadr vector))))
    (seqn-decompose   (if (>= (car vector)  (expt 2 (1- (mcar morphism))))
                          (list 1 (- (car vector) (expt 2 (1- (mcar morphism)))))
                          (list 0 (car vector))))
    (seqn-eq          (if (= (car vector) (cadr vector))
                          (list 0 0)
                          (list 1 0)))
    (seqn-lt          (if (< (car vector) (cadr vector))
                          (list 0 0)
                          (list 1 0)))))

(defmethod well-defp-cat ((morph <seqn>))
  (etypecase-of seqn morph
    (composition
     (let* ((mcar  (mcar morph))
            (mcadr (mcadr morph))
            (dom (dom mcar))
            (cod (cod mcadr)))
       (if (and (well-defp-cat mcar)
                (well-defp-cat mcadr)
                (obj-equalp dom
                            cod))
           t
           (error "Co(Domains) do not match for ~A with domain
                                    of MCAR ~A1 and codomain of MCADR ~A2."
                  morph cod dom))))
    (parallel-seq
     (if (and (well-defp-cat (mcar morph))
              (well-defp-cat (mcadr morph)))
         t
         (error "Not well-defined parallel composition ~A" morph)))
    (branch-seq
     (let* ((mcar (mcar morph))
            (mcadr (mcadr morph))
            (dom1  (dom mcar))
            (dom2  (dom mcadr))
            (cod1  (cod mcar))
            (cod2  (cod mcadr)))
       (if (and (well-defp-cat mcar)
                (well-defp-cat mcadr)
                (obj-equalp dom1 dom2)
                (obj-equalp cod1 cod2))
           t
           (error "Not a well-defined branching ~A.
                                   ~A1 has dom ~a1 and cod ~a2.
                                   ~A2 has dom ~a3 and cod ~a4"
                  morph mcar dom1 cod1 mcadr dom2 cod2))))
    (shift-front
     (if (>= (length (mcar morph))
             (mcadr morph))
         t
         (error "Wrong shift-length for ~A" morph)))
    ((or id
         fork-seq
         drop-nil
         drop-width
         remove-right
         remove-left
         inj-length-left
         inj-length-right
         inj-size
         zero-bit
         one-bit
         seqn-add
         seqn-multiply
         seqn-divide
         seqn-subtract
         seqn-mod
         seqn-nat
         seqn-concat
         seqn-decompose
         seqn-eq
         seqn-lt)
     t)))
