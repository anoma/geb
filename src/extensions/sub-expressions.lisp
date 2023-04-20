(in-package :geb.extensions)

(deftype obj-morph () `(or cat-obj cat-morph t))

(-> can-continuep (t) boolean)
(defun can-continuep (term)
  (and (or (typep term 'pointwise-mixin)
           (typep term 'list))
       (not (typep term 'cat-obj))
       (not (typep term 'number))
       (not (typep term 'string))
       (not (typep term 'geb.vampir.spec:constant))))

(-> common-sub-expressions (obj-morph) (values obj-morph fset:map))
(defun common-sub-expressions (term)
  "Compute common sub-expressions and return an object with the
appropriate sub-expressions uniquely identified"
  (if (can-continuep term)
      (keep-unique term (compute-common-usages term))
      (values term (fset:empty-map))))

(-> compute-common-usages (obj-morph) fset:bag)
(defun compute-common-usages (obj)
  ;; we are going to be smart about this
  ;; no manual recursion, we don't need that
  (labels ((reduce-fn (bag term)
             (cond ((not (can-continuep term))
                    bag)
                   ;; we don't want to actually add
                   ;; to a total that is already
                   ;; count
                   ((fset:member? term bag)
                    (fset:with bag term))
                   (t
                    (recursive (fset:with bag term) term))))
           (recursive (bag term)
             (if (listp term)
                 (reduce #'reduce-fn term :initial-value bag)
                 (reduce-pointwise #'reduce-fn term bag))))
    (values
     (fset:filter-pairs (lambda (x y) (declare (ignore x)) (<= 2 y))
                        (recursive (fset:empty-bag) obj)))))

(-> keep-unique (obj-morph fset:bag) (values obj-morph fset:map))
(defun keep-unique (obj bag)
  "given a BAG and an term, mark each term which appears in the bag as a
[COMMON-SUB-EXPRESSION][type].

We also return the map of names that each common expression is had,
for further processing.

This is part two of the COMMON-SUB-EXPRESSIONS pass."
  (let ((mapping (fset:image (lambda (x y)
                               (declare (ignore y))
                               (values x (gensym)))
                             (fset:convert 'fset:map bag))))
    (labels ((recursive (obj)
               (if (not (can-continuep obj))
                   (values obj mapping)
                   (let ((looked  (fset:lookup mapping obj))
                         (new-obj
                           (if (listp obj)
                               (mapcar #'recursive obj)
                               (map-pointwise #'recursive obj))))
                     (if looked
                         (make-common-sub-expression :obj new-obj :name looked)
                         new-obj)))))
      (values (recursive obj) mapping))))
