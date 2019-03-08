;; Copyright (C) 2018, University of British Columbia
;; Written by Yan Peng (Oct 2018)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software
;;
(in-package "ASP")

;; easy-fix is a macro for defining a fty::deffixtype when we've got a
;;   recognizer function and a default value.
(defun easy-fix-fn (type-name default-value)
  (b* ((type-str (symbol-name type-name))
       (type-pred (intern-in-package-of-symbol (concatenate 'string type-str "-P") type-name))
       (type-fix (intern-in-package-of-symbol (concatenate 'string type-str "-FIX") type-name))
       (type-fix-lemma (intern-in-package-of-symbol (concatenate 'string type-str "-FIX-WHEN-" type-str "-P") type-name))
       (type-equiv (intern-in-package-of-symbol (concatenate 'string type-str "-EQUIV") type-name)))
    `(defsection ,type-name
       (define ,type-fix ((x ,type-pred))
         :returns(fix-x ,type-pred)
         (mbe :logic (if (,type-pred x) x ,default-value)
              :exec  x)
         ///
         (more-returns
          (fix-x (implies (,type-pred x) (equal fix-x x))
                 :hints(("Goal" :in-theory (enable ,type-fix)))
                 :name ,type-fix-lemma)))
       (deffixtype ,type-name
         :pred   ,type-pred
         :fix    ,type-fix
         :equiv  ,type-equiv
         :define t
         :topic  ,type-name))))

(defmacro easy-fix (type-name default-value)
  `(make-event (easy-fix-fn ',type-name ',default-value)))

