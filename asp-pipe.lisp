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

(define interval-constraints ((el lenv-p)
                              (er renv-p))
  :returns (v booleanp)
  (and (valid-interval (lenv->delta el))
       (valid-interval (renv->delta er))
       (equal (lenv->delta el)
              (renv->delta er))))

(defprod lr
  ((el lenv-p)
   (er renv-p)))

(deflist asp-stage-list
  :elt-type asp-stage
  :true-listp t)

(defprod asp-pipeline
  ((el lenv-p)
   (stages asp-stage-list-p)
   (er renv-p)))

(encapsulate ()
  (local
   (defthm crock
     (implies (and (asp-stage-list-p x) x)
              (o< (len (cdr x))
                  (len x)))))

  (define asp-pipeline-connections ((p asp-pipeline-p))
    :returns (v booleanp)
    :measure (len (asp-pipeline->stages p))
    (b* (((asp-pipeline p) (asp-pipeline-fix p))
         ((unless (consp p.stages))
          (env-connection p.el p.er))
         ((asp-stage first) (car p.stages))
         (rest (cdr p.stages))
         ((unless (and (env-connection p.el first.left)
                       (asp-internal-connection first)))
          nil)
         (p-tl (make-asp-pipeline :el first.right
                                  :stages rest
                                  :er p.er)))
      (asp-pipeline-connections p-tl)))

  (define asp-pipeline-time-intervals ((p asp-pipeline-p))
    :returns (v booleanp)
    :measure (len (asp-pipeline->stages p))
    (b* (((asp-pipeline p) (asp-pipeline-fix p))
         ((unless (consp p.stages))
          (interval-constraints p.el p.er))
         ((asp-stage first) (car p.stages))
         (rest (cdr p.stages))
         ((unless (interval-constraints p.el first.left))
          nil)
         (p-tl (make-asp-pipeline :el first.right
                                  :stages rest
                                  :er p.er)))
      (asp-pipeline-time-intervals p-tl)))

  (define asp-pipeline-constraints ((p asp-pipeline-p))
    :returns (v booleanp)
    (and (asp-pipeline-connections p)
         (asp-pipeline-time-intervals p)))

  (define asp-stage-list-step ((al asp-stage-list-p)
                               (s1 gstate-t-p)
                               (s2 gstate-t-p)
                               (inf rationalp))
    :returns (v booleanp)
    :measure (len al)
    (b* ((al (asp-stage-list-fix al))
         ((unless (consp al)) t)
         ((asp-stage first) (car al))
         (rest (cdr al))
         ((unless (asp-step first s1 s2 inf))
          nil))
      (asp-stage-list-step rest s1 s2 inf)))

  (define asp-pipeline-step ((p asp-pipeline-p)
                             (s1 gstate-t-p)
                             (s2 gstate-t-p)
                             (inf rationalp))
    :returns (v booleanp)
    (b* (((asp-pipeline p) (asp-pipeline-fix p)))
      (and (lenv-step p.el s1 s2 inf)
           (renv-step p.er s1 s2 inf)
           (asp-stage-list-step p.stages s1 s2 inf))))

  (define invariant-asp-pipeline ((p asp-pipeline-p)
                                  (s gstate-t-p)
                                  (inf rationalp))
    :returns (ok booleanp)
    :measure (len (asp-pipeline->stages p))
    (b* (((asp-pipeline p) (asp-pipeline-fix p))
         (s (gstate-t-fix s))
         ((unless (consp p.stages))
          (invariant-env p.el p.er s inf))
         ((asp-stage first) (car p.stages))
         (rest (cdr p.stages))
         ((unless (invariant-env p.el first.left s inf))
          nil)
         (p-tl (make-asp-pipeline :el first.right
                                  :stages rest
                                  :er p.er)))
      (invariant-asp-pipeline p-tl s inf)))
  )

(defthm asp-pipeline-step-thm
  (implies (and (asp-pipeline-p p)
                (consp (asp-pipeline->stages p))
                (gstate-t-p s1)
                (gstate-t-p s2)
                (rationalp inf)
                (lenv-step (asp-stage->right (car (asp-pipeline->stages p)))
                           s1 s2 inf)
                (asp-stage-list-step (cdr (asp-pipeline->stages p))
                                     s1 s2 inf)
                (renv-step (asp-pipeline->er p)
                           s1 s2 inf))
           (asp-pipeline-step
            (asp-pipeline (asp-stage->right (car (asp-pipeline->stages p)))
                          (cdr (asp-pipeline->stages p))
                          (asp-pipeline->er p))
            s1 s2 inf))
  :hints (("Goal" :in-theory (e/d (asp-pipeline-step) ()))))

(defthm invariant-asp-pipeline-thm
  (implies (and (asp-pipeline-p p)
                (gstate-t-p s1)
                (gstate-t-p s2)
                (rationalp inf)
                (asp-pipeline-constraints p)
                (asp-pipeline-step p s1 s2 inf)

                (invariant-asp-pipeline p s1 inf))
           (invariant-asp-pipeline p s2 inf))
  :hints (("Goal"
           :in-theory (e/d (invariant-asp-pipeline
                            asp-pipeline-constraints
                            interval-constraints
                            asp-pipeline-step
                            asp-step)
                           ())
           ;; I expanded functions that are recursive and put non-recursive
           ;; ones in enabled functions
           :expand ((asp-pipeline-connections p)
                    (asp-pipeline-time-intervals p)
                    (asp-stage-list-step (asp-pipeline->stages p) s1 s2 inf))
           :induct (invariant-asp-pipeline p s1 inf))
          ))

