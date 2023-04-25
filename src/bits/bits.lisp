(defmethod dom ((x <bits>))
  (assure substobj
    (typecase-of bits x
      (compose          (dom (mcadr x)))
      (fork             (dom (mcar x)))
      (parallel         (+ (dom (mcar x)) (dom (mcadr x))))
      (negation         1)
      (conjunction      2)
      (swap             (+ (mcar x) (mcadr x)))
      (true             0)
      (false            0)
      (identity         (mcar x))
      (drop             (mcar x))
      (branch           (+ 1 (dom (mcar x))))
      (otherwise
       (subclass-responsibility x)))))

(defmethod codom ((x <bits>))
  (assure substobj
    (typecase-of bits x
      (compose          (codom (mcar x)))
      (fork             (* 2 (codom (mcar x))))
      (parallel         (+ (codom (mcar x)) (codom (mcadr x))))
      (negation         1)
      (conjunction      1)
      (swap             (+ (mcar x) (mcadr x)))
      (true             1)
      (false            1)
      (identity         (mcar x))
      (drop             0)
      (branch           (codom (mcar x)))
      (otherwise
       (subclass-responsibility x)))))
