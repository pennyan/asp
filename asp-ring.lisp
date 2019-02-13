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

(define invariant-asp-ring ((r asp-ring-p)
                            (s gstate-t-p))
  :returns (ok booleanp)
  (b* (((asp-ring r) (asp-ring-fix r)))
    (invariant-asp-pipeline r.p s)))

(define asp-ring-hazard-free-step ((r asp-ring-p)
                                   (s1 gstate-t-p)
                                   (s2 gstate-t-p))
  :returns (ok booleanp)
  (b* (((asp-ring r) (asp-ring-fix r)))
    (asp-pipeline-hazard-free-step r.p s1 s2)))

(defthm asp-ring-hazard-free-thm
  (implies (and (asp-ring-p r)
                (gstate-t-p s1)
                (gstate-t-p s2)
                (asp-ring-constraints p)
                (asp-ring-step p s1 s2)
                (invariant-asp-ring p s1))
           (asp-ring-hazard-free-step p s1 s2))
  :hints (("Goal" :in-theory (e/d (asp-ring-constraints
                                   asp-ring-step
                                   invariant-asp-ring
                                   asp-ring-hazard-free-step)
                                  ()))))
