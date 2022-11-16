(in-package :geb.utils)

(defun symbol-to-keyword (symbol)
  (intern (symbol-name symbol) :keyword))
