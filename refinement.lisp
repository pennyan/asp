;; Copyright (C) 2018, University of British Columbia
;; Written by Yan Peng (Oct 2018)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software
;;
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

(define inv1-example ((el0 lenv-p)
                      (er0 renv-p)
                      (el1 lenv-p)
                      (er1 renv-p)
                      (s gstate-t-p))
  :returns (v booleanp)
  (and (invariant-env el0 er0 s)
       (invariant-env el1 er1 s)))

(define module1-example ((el0 lenv-p)
                         (er1 renv-p)
                         (s1 gstate-t-p)
                         (s2 gstate-t-p))
  :returns (v booleanp)
  (and (lenv-step el0 s1 s2)
       (renv-step er1 s1 s2)))

(define env1-example ((er0 renv-p)
                      (el1 lenv-p)
                      (s1 gstate-t-p)
                      (s2 gstate-t-p))
  :returns (v booleanp)
  (and (renv-step er0 s1 s2)
       (lenv-step el1 s1 s2)))

(define constraints1-example ((el0 lenv-p)
                              (er0 renv-p)
                              (el1 lenv-p)
                              (er1 renv-p))
  :returns (v booleanp)
  (and (env-connection el0 er0)
       (valid-interval (lenv->delta el0))
       (valid-interval (renv->delta er0))
       (equal (lenv->delta el0)
              (renv->delta er0))
       (env-connection el1 er1)
       (valid-interval (lenv->delta el1))
       (valid-interval (renv->delta er1))
       (equal (lenv->delta el1)
              (renv->delta er1))))

(defthm thm1
  (implies (and (gstate-t-p s1)
                (gstate-t-p s2)
                (lenv-p el0)
                (renv-p er0)
                (lenv-p el1)
                (renv-p er1)

                (constraints1-example el0 er0 el1 er1)

                (module1-example el0 er1 s1 s2)
                (env1-example er0 el1 s1 s2)
                (inv1-example el0 er0 el1 er1 s1))
           (inv1-example el0 er0 el1 er1 s2))
  :hints (("Goal"
           :smtlink
           (:fty (lenv renv time-interval delay-interval
                       gtrace sig-value gstate gstate-t
                       sig-path-list sig-path sig sig-target
                       asp-env-testbench asp-my-bench integer-list
                       sig-value-list maybe-rational)
                 :functions ((sigs-in-bool-table
                              :formals ((sigs sig-path-listp)
                                        (st gstate-p))
                              :returns ((ok booleanp))
                              :level 3))
                 :evilp t
                 ))))

(define inv2-example ((a asp-stage-p)
                      (el lenv-p)
                      (er renv-p)
                      (s gstate-t-p))
  :returns (v booleanp)
  (invariant-asp-stage a el er s))

(define module2-example ((a asp-stage-p)
                         (s1 gstate-t-p)
                         (s2 gstate-t-p))
  :returns (v booleanp)
  (asp-step a s1 s2))

(define env2-example ((el lenv-p)
                      (er renv-p)
                      (s1 gstate-t-p)
                      (s2 gstate-t-p))
  :returns (v booleanp)
  (and (lenv-step el s1 s2)
       (renv-step er s1 s2)))

(define constraints2-example ((a asp-stage-p)
                              (el lenv-p)
                              (er renv-p))
  :returns (v booleanp)
  (and (asp-internal-connection a)
       (asp-connection a el er)
       (valid-interval (asp-stage->delta a))
       (valid-interval (lenv->delta el))
       (valid-interval (renv->delta er))
       (equal (asp-stage->delta a)
              (lenv->delta el))
       (equal (asp-stage->delta a)
              (renv->delta er))))

(defthm thm2
  (implies (and (gstate-t-p s1)
                (gstate-t-p s2)
                (asp-stage-p a)
                (lenv-p el2)
                (renv-p er2)
                (constraints2-example a el2 er2)

                (module2-example a s1 s2)
                (env2-example el2 er2 s1 s2)
                (inv2-example a el2 er2 s1))
           (inv2-example a el2 er2 s2))
  :hints (("Goal"
           :smtlink
           (:fty (asp-stage lenv renv time-interval delay-interval
                            gtrace sig-value gstate gstate-t
                            sig-path-list sig-path sig sig-target
                            asp-env-testbench asp-my-bench integer-list
                            sig-value-list maybe-rational)
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
                (lenv-p el0)
                (renv-p er0)
                (lenv-p el1)
                (renv-p er1)
                (constraints1-example el0 er0 el1 er1)

                (asp-stage-p a)
                (lenv-p el2)
                (renv-p er2)
                (constraints2-example a el2 er2)

                (inv1-example el0 er0 el1 er1 s1)
                (inv2-example a el2 er2 s1)

                (module1-example el0 er1 s1 s2)
                ;; need these constraints
                (equal el0 el2)
                (equal er1 er2))
           (env2-example el2 er2 s1 s2))
  :hints (("Goal"
           :smtlink
           (:fty (asp-stage lenv renv time-interval delay-interval
                            gtrace sig-value gstate gstate-t
                            sig-path-list sig-path sig sig-target
                            asp-env-testbench asp-my-bench integer-list
                            sig-value-list maybe-rational)
                 :functions ((sigs-in-bool-table :formals ((sigs sig-path-listp)
                                                           (st gstate-p))
                                                 :returns ((ok booleanp))
                                                 :level 5))
                 :evilp t
                 )))
  )

(defthm thm4
  (implies (and (gstate-t-p s1)
                (gstate-t-p s2)
                (lenv-p el0)
                (renv-p er0)
                (lenv-p el1)
                (renv-p er1)
                (constraints1-example el0 er0 el1 er1)

                (asp-stage-p a)
                (lenv-p el2)
                (renv-p er2)
                (constraints2-example a el2 er2)

                (inv1-example el0 er0 el1 er1 s1)
                (inv2-example a el2 er2 s1)

                (module2-example a s1 s2)
                ;; need these constraints
                (equal (asp-stage->left a) er0)
                (equal (asp-stage->right a) el1))
           (env1-example er0 el1 s1 s2))
  :hints (("Goal"
           :smtlink
           (:fty (asp-stage lenv renv time-interval delay-interval
                            gtrace sig-value gstate gstate-t
                            sig-path-list sig-path sig sig-target
                            asp-env-testbench asp-my-bench integer-list
                            sig-value-list maybe-rational)
                 :functions ((sigs-in-bool-table :formals ((sigs sig-path-listp)
                                                           (st gstate-p))
                                                 :returns ((ok booleanp))
                                                 :level 5))
                 :evilp t
                 )))
  )

(defthm thm5
  (implies (and (gstate-t-p s1)
                (gstate-t-p s2)
                (lenv-p el0)
                (renv-p er0)
                (lenv-p el1)
                (renv-p er1)
                (constraints1-example el0 er0 el1 er1)

                (asp-stage-p a)
                (lenv-p el2)
                (renv-p er2)
                (constraints2-example a el2 er2)

                (inv1-example el0 er0 el1 er1 s1)
                (inv2-example a el2 er2 s1)
                (module1-example el0 er1 s1 s2)
                (module2-example a s1 s2)

                ;; additional constraints
                (equal el0 el2)
                (equal er1 er2)
                (equal (asp-stage->left a) er0)
                (equal (asp-stage->right a) el1))
           (and (inv1-example el0 er0 el1 er1 s2)
                (inv2-example a el2 er2 s2)
                ))
  :hints (("Goal"
           :in-theory (e/d ()
                           (thm1 thm2 thm3 thm4))
           :use ((:instance thm1)
                 (:instance thm2)
                 (:instance thm3)
                 (:instance thm4))))
  )
