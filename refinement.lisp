(in-package "ASP")

(include-book "std/util/define" :dir :system)
(include-book "tools/bstar" :dir :system)
(include-book "centaur/fty/top" :dir :system) ; for defalist, etc.
(include-book "misc/eval" :dir :system)
(include-book "projects/smtlink/top" :dir :system)
(value-triple (tshell-ensure))
(add-default-hints '((SMT::SMT-computed-hint clause)))

(encapsulate (((module1 * *) => *)
              ((module2 * *) => *)
              ((env1 * *) => *)
              ((env2 * *) => *)
              ((inv1 *) => *)
              ((inv2 *) => *))
  (local (defun module1 (s1 s2) (declare (ignore s1 s2)) t))
  (local (defun module2 (s1 s2) (declare (ignore s1 s2)) t))
  (local (defun env1 (s1 s2) (declare (ignore s1 s2)) t))
  (local (defun env2 (s1 s2) (declare (ignore s1 s2)) t))
  (local (defun inv1 (s) (declare (ignore s)) t))
  (local (defun inv2 (s) (declare (ignore s)) t))

  (defthm inv1-holds-for-module1&env1
    (implies (and (inv1 s1) (module1 s1 s2) (env1 s1 s2))
		  	     (inv1 s2)))

  (defthm inv2-holds-for-module2&env2
    (implies (and (inv2 s1) (module2 s1 s2) (env2 s1 s2))
			       (inv2 s2)))

  (defthm env2-holds-if-inv1&inv2-for-module1
    (implies (and (inv1 s1) (inv2 s1) (module1 s1 s2))
			       (env2 s1 s2)))

  (defthm env1-holds-if-inv1&inv2-for-module2
    (implies (and (inv1 s1) (inv2 s1) (module2 s1 s2))
			       (env1 s1 s2)))
  )

(defthm inv1&inv2-holds-for-module1&module2
  (implies (and (inv1 s1) (inv2 s1) (module1 s1 s2) (module2 s1 s2))
		       (and (inv1 s2) (inv2 s2))))

