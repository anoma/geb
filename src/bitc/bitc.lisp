(defmethod dom ((x <bitc>))
  (assure substobj
    (typecase-of bitc x
      (compose          (dom (mcadr x)))
      (fork             (dom (mcar x)))
      (parallel         (+ (dom (mcar x)) (dom (mcadr x))))
      (swap             (+ (mcar x) (mcadr x)))
      (one              0)
      (zero             0)
      (ident            (mcar x))
      (drop             (mcar x))
      (branch           (+ 1 (dom (mcar x))))
      (otherwise
       (subclass-responsibility x)))))

(defmethod codom ((x <bitc>))
  (assure substobj
    (typecase-of bitc x
      (compose          (codom (mcar x)))
      (fork             (* 2 (codom (mcar x))))
      (parallel         (+ (codom (mcar x)) (codom (mcadr x))))
      (swap             (+ (mcar x) (mcadr x)))
      (one              1)
      (zero             1)
      (ident            (mcar x))
      (drop             0)
      (branch           (codom (mcar x)))
      (otherwise
       (subclass-responsibility x)))))
