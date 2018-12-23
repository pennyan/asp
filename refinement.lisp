(in-package "ASP")

(include-book "std/util/define" :dir :system)
(include-book "tools/bstar" :dir :system)
(include-book "centaur/fty/top" :dir :system) ; for defalist, etc.
(include-book "misc/eval" :dir :system)
(include-book "projects/smtlink/top" :dir :system)
(value-triple (tshell-ensure))
(add-default-hints '((SMT::SMT-computed-hint clause)))

(include-book "env")
(include-book "asp")

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

;; (Module1 s1 s2) = (and (Lenv0 s1 s2) (Renv1 s1 s2))
;; (Env1 s1 s2)    = (and (Renv0 s1 s2) (Lenv1 s1 s2))
;; (Module2 s1 s2) = (asp-stage s1 s2)
;; (Env2 s1 s2)    = (and (Lenv2 s1 s2) (Renv2 s1 s2))

(defthm inv1&inv2-holds-for-module1&module2
  (implies (and (inv1 s1) (inv2 s1) (module1 s1 s2) (module2 s1 s2))
           (and (inv1 s2) (inv2 s2))))

(defthm thm1
  (implies (and (gstate-t-p s1)
                (gstate-t-p s2)
                (rationalp inf)

                (lenv-p el0)
                (renv-p er0)
                (env-connection el0 er0)
                (valid-interval (lenv->delta el0))
                (valid-interval (renv->delta er0))
                (equal (lenv->delta el0)
                       (renv->delta er0))
                (lenv-step el0 s1 s2 inf)
                (renv-step er0 s1 s2 inf)

                (lenv-p el1)
                (renv-p er1)
                (env-connection el1 er1)
                (valid-interval (lenv->delta el1))
                (valid-interval (renv->delta er1))
                (equal (lenv->delta el1)
                       (renv->delta er1))
                (lenv-step el1 s1 s2 inf)
                (renv-step er1 s1 s2 inf)

                (invariant-env el0 er0 s1 inf)
                (invariant-env el1 er1 s1 inf))
           (and (invariant-env el0 er0 s2 inf)
                (invariant-env el1 er1 s2 inf)))
  :hints (("Goal"
           :smtlink
           (:fty (lenv renv interval gtrace sig-value gstate gstate-t
                       sig-path-list sig-path sig sig-target
                       asp-env-testbench asp-my-bench integer-list
                       sig-value-list)
                 :functions ((sigs-in-bool-table
                              :formals ((sigs sig-path-listp)
                                        (st gstate-p))
                              :returns ((ok booleanp))
                              :level 3))
                 :evilp t
                 )))
  )

(defthm thm2
  (implies (and (gstate-t-p s1)
                (gstate-t-p s2)
                (rationalp inf)

                (asp-stage-p a)
                (lenv-p el2)
                (renv-p er2)
                (asp-internal-connection a)
                (asp-connection a el2 er2)
                (valid-interval (asp-stage->delta a))
                (valid-interval (lenv->delta el2))
                (valid-interval (renv->delta er2))
                (equal (asp-stage->delta a)
                       (lenv->delta el2))
                (equal (asp-stage->delta a)
                       (renv->delta er2))

                (lenv-step el2 s1 s2 inf)
                (renv-step er2 s1 s2 inf)
                (asp-step a s1 s2 inf)

                (invariant-asp-stage a el2 er2 s1 inf))
           (invariant-asp-stage a el2 er2 s2 inf))
    :hints (("Goal"
           :smtlink
           (:fty (asp-stage lenv renv interval gtrace sig-value gstate gstate-t
                            sig-path-list sig-path sig sig-target
                            asp-env-testbench asp-my-bench integer-list
                            sig-value-list)
	               :functions ((sigs-in-bool-table :formals ((sigs sig-path-listp)
						                                               (st gstate-p))
					                                       :returns ((ok booleanp))
					                                       :level 5))
                 :evilp t
                 )))
  )

(defthm thm3
  (implies (and (gstate-t-p s1)
                (gstate-t-p s2)
                (rationalp inf)

                (lenv-p el0)
                (renv-p er0)
                (env-connection el0 er0)
                (valid-interval (lenv->delta el0))
                (valid-interval (renv->delta er0))
                (equal (lenv->delta el0)
                       (renv->delta er0))

                (lenv-p el1)
                (renv-p er1)
                (env-connection el1 er1)
                (valid-interval (lenv->delta el1))
                (valid-interval (renv->delta er1))
                (equal (lenv->delta el1)
                       (renv->delta er1))

                (asp-stage-p a)
                (lenv-p el2)
                (renv-p er2)
                (asp-internal-connection a)
                (asp-connection a el2 er2)
                (valid-interval (asp-stage->delta a))
                (valid-interval (lenv->delta el2))
                (valid-interval (renv->delta er2))
                (equal (asp-stage->delta a)
                       (lenv->delta el2))
                (equal (asp-stage->delta a)
                       (renv->delta er2))

                (invariant-env el0 er0 s1 inf)
                (invariant-env el1 er1 s1 inf)
                (invariant-asp-stage a el2 er2 s1 inf)

                (lenv-step el0 s1 s2 inf)
                (renv-step er1 s1 s2 inf))
           (and (lenv-step el2 s1 s2 inf)
                (renv-step er2 s1 s2 inf)))
  :hints (("Goal"
           :smtlink
           (:fty (asp-stage lenv renv interval gtrace sig-value gstate gstate-t
                            sig-path-list sig-path sig sig-target
                            asp-env-testbench asp-my-bench integer-list
                            sig-value-list)
	               :functions ((sigs-in-bool-table :formals ((sigs sig-path-listp)
						                                               (st gstate-p))
					                                       :returns ((ok booleanp))
					                                       :level 5))
                 :smt-fname "x.py"
                 :smt-dir "smtpy"
                 :evilp t
                 )))
  )
