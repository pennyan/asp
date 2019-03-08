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

(include-book "asp-pipe")

(defprod asp-ring
  ((p asp-pipeline-p)))

(define asp-ring-connection ((r asp-ring-p))
  :returns (v booleanp)
  (equal (lenv->left-internal (asp-pipeline->el (asp-ring->p r)))
         (renv->right-internal (asp-pipeline->er (asp-ring->p r)))))

(define asp-ring-constraints ((r asp-ring-p))
  :returns (v booleanp)
  (and (asp-ring-connection r)
       (asp-pipeline-constraints (asp-ring->p r))))

(define asp-ring-step ((r asp-ring-p)
                       (s1 gstate-t-p)
                       (s2 gstate-t-p))
  :returns (v booleanp)
  (b* (((asp-ring r) (asp-ring-fix r)))
    (asp-pipeline-step r.p s1 s2)))

(define asp-ring-trace ((r asp-ring-p)
                        (tr gtrace-p))
  :returns (b booleanp)
  :measure (len tr)
  (b* (((unless (consp (gtrace-fix tr))) t)
       (first (car (gtrace-fix tr)))
       (rest (cdr (gtrace-fix tr)))
       ((unless (consp (gtrace-fix rest))) t)
       (second (car (gtrace-fix rest))))
    (and (asp-ring-step r first second)
         (asp-ring-trace r rest))))

(define invariant-asp-ring ((r asp-ring-p)
                            (s gstate-t-p))
  :returns (ok booleanp)
  (b* (((asp-ring r) (asp-ring-fix r)))
    (invariant-asp-pipeline r.p s)))

(define invariant-asp-ring-trace ((r asp-ring-p)
                                  (tr gtrace-p))
  :returns (ok booleanp)
  :measure (len tr)
  (b* (((unless (consp (gtrace-fix tr))) t)
       (first (car (gtrace-fix tr)))
       (rest (cdr (gtrace-fix tr))))
    (and (invariant-asp-ring r first)
         (invariant-asp-ring-trace r rest))))

(defthm asp-ring-invariant-step-thm
  (implies (and (asp-ring-p r)
                (gstate-t-p s1)
                (gstate-t-p s2)
                (asp-ring-constraints r)
                (asp-ring-step r s1 s2)
                (invariant-asp-ring r s1))
           (invariant-asp-ring r s2))
  :hints (("Goal"
           :expand ((asp-ring-constraints r)
                    (asp-ring-step r s1 s2)
                    (invariant-asp-ring r s1)
                    (invariant-asp-ring r s2)))))

(defthm asp-ring-invariant-trace-thm
  (implies (and (asp-ring-p r)
                (gtrace-p tr)
                (consp (gtrace-fix tr))
                (consp (gtrace-fix (cdr (gtrace-fix tr))))
                (asp-ring-constraints r)
                (asp-ring-trace r tr)
                (invariant-asp-ring r (car (gtrace-fix tr))))
           (invariant-asp-ring-trace r tr))
  :hints (("Goal"
           :in-theory (e/d (invariant-asp-ring-trace)
                           ())
           :expand ((asp-ring-trace r tr)
                    (invariant-asp-ring-trace r tr)))
          ("Subgoal *1/1'"
           :use ((:instance asp-ring-invariant-step-thm
                            (r r)
                            (s1 (car tr))
                            (s2 (car (cdr tr))))))
          ))

(define asp-ring-hazard-free-step ((r asp-ring-p)
                                   (s1 gstate-t-p)
                                   (s2 gstate-t-p))
  :returns (ok booleanp)
  (b* (((asp-ring r) (asp-ring-fix r)))
    (asp-pipeline-hazard-free-step r.p s1 s2)))

(define asp-ring-hazard-free-trace ((r asp-ring-p)
                                    (tr gtrace-p))
  :returns (ok booleanp)
  :measure (len tr)
  (b* (((unless (consp (gtrace-fix tr))) t)
       (first (car (gtrace-fix tr)))
       (rest (cdr (gtrace-fix tr)))
       ((unless (consp (gtrace-fix rest))) t)
       (second (car (gtrace-fix rest))))
    (and (asp-ring-hazard-free-step r first second)
         (asp-ring-hazard-free-trace r rest))))

(defthm asp-ring-hazard-free-step-thm
  (implies (and (asp-ring-p r)
                (gstate-t-p s1)
                (gstate-t-p s2)
                (asp-ring-constraints r)
                (asp-ring-step r s1 s2)
                (invariant-asp-ring r s1))
           (asp-ring-hazard-free-step r s1 s2))
  :hints (("Goal" :in-theory (e/d (asp-ring-constraints
                                   asp-ring-step
                                   invariant-asp-ring
                                   asp-ring-hazard-free-step)
                                  ()))))

(defthm asp-ring-hazard-free-trace-thm
  (implies (and (asp-ring-p r)
                (gtrace-p tr)
                (consp (gtrace-fix tr))
                (consp (gtrace-fix (cdr (gtrace-fix tr))))
                (asp-ring-constraints r)
                (asp-ring-trace r tr)
                (invariant-asp-ring r (car (gtrace-fix tr))))
           (asp-ring-hazard-free-trace r tr))
  :hints (("Goal"
           :in-theory (e/d (asp-ring-hazard-free-trace)
                           ())
           :expand ((asp-ring-trace r tr)
                    (asp-ring-hazard-free-trace r tr)))
          ("Subgoal *1/2"
           :use ((:instance asp-ring-hazard-free-step-thm
                            (r r)
                            (s1 (car tr))
                            (s2 (car (cdr tr))))))))
