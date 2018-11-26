(in-package "ASP")
;; simplify(gstate_sub_t.statev(gtrace.car(gtrace.cdr(m[tr])))).sexpr()

(include-book "std/util/define" :dir :system)
(include-book "tools/bstar" :dir :system)
(include-book "centaur/fty/top" :dir :system) ; for defalist, etc.
(include-book "projects/smtlink/top" :dir :system)
(value-triple (tshell-ensure))
(add-default-hints '((SMT::SMT-computed-hint clause)))

(include-book "util")

;; -------------------------------------
;;       signal paths
(defprod sig
  ((module symbolp)
   (index integerp)))

(deflist sig-path
  :elt-type sig-p
  :true-listp t)

(deflist sig-path-list
  :elt-type sig-path
  :pred sig-path-listp
  :true-listp t)

;; -------------------------------------
;;       value type

;; -------------------------------------
;;        trace
(defprod sig-value
  ((value booleanp)
   (time rationalp)))

(defalist gstate
  :key-type sig-path-p
  :val-type sig-value-p
  :true-listp t)

(defprod gstate-t
  ((statet rationalp)
   (statev gstate-p)))

(deflist gtrace
  :elt-type gstate-t-p
  :true-listp t)

(define sigs-in-bool-table ((sigs sig-path-listp)
                            (st gstate-p))
  :returns (ok booleanp)
  :measure (len sigs)
  :hints (("Goal" :in-theory (enable sig-path-list-fix)))
  (b* ((sigs (sig-path-list-fix sigs))
       (st (gstate-fix st))
       ((unless (consp (sig-path-list-fix sigs))) t)
       (first (car (sig-path-list-fix sigs)))
       (rest (cdr (sig-path-list-fix sigs)))
       (first-v (assoc-equal first (gstate-fix st)))
       ((unless (consp (smt::magic-fix 'sig-path_sig-value first-v)))
        nil))
    (sigs-in-bool-table rest st))
  )

(define sigs-in-bool-trace ((sigs sig-path-listp)
                            (tr gtrace-p))
  :returns (ok booleanp)
  :measure (len (gtrace-fix tr))
  :hints (("Goal" :in-theory (enable gtrace-fix)))
  (b* ((sigs (sig-path-list-fix sigs))
       (tr (gtrace-fix tr))
       ((unless (consp (sig-path-list-fix sigs))) t)
       ((unless (consp (gtrace-fix tr))) t)
       (first (car (gtrace-fix tr)))
       (rest (cdr (gtrace-fix tr)))
       ((unless (sigs-in-bool-table sigs (gstate-t->statev first))) nil))
    (sigs-in-bool-trace sigs rest)))

;; --------------------------------------
;; stage

(defprod interval
  ((lo rationalp)
   (hi rationalp)))

(define valid-interval ((i interval-p))
  :returns (ok booleanp)
  (b* ((i (interval-fix i)))
    (and (> (interval->lo i) 0)
         (< (interval->lo i) (interval->hi i)))))

(defprod asp-stage
  ((go-full sig-path-p)
   (go-empty sig-path-p)
   (full sig-path-p)
   (empty sig-path-p)
   (full-internal sig-path-p)

   (delta-t1 interval-p)
   (delta-t2 interval-p)
   ))

;; =====================================================
;; targets and trigger time
(defprod target-tuple
  ((target booleanp)
   (valid booleanp)))

(defoption maybe-rational rationalp)

;; -----------------------------------------------------
;; target and trigger-time functions for the stage

;; empty ^ go_full ->(delta_t1) full_internal
;; full ^ go_empty ->(delta_t1) not(full_internal)
;; input signals should all be previous state
(define full-internal-target ((full sig-value-p) (empty sig-value-p)
                              (go-full sig-value-p) (go-empty sig-value-p)
                              (full-internal sig-value-p))
  :returns (target target-tuple-p)
  (b* ((full (sig-value-fix full))
       (empty (sig-value-fix empty))
       (go-full (sig-value-fix go-full))
       (go-empty (sig-value-fix go-empty))
       (full-internal (sig-value-fix full-internal))
       ((if (not (or (and (sig-value->value go-full)
                          (sig-value->value empty))
                     (and (sig-value->value go-empty)
                          (sig-value->value full)))))
        (make-target-tuple
         :target (sig-value->value full-internal)
         :valid t))
       ((if (not (and (sig-value->value go-full)
                      (sig-value->value empty))))
        (make-target-tuple
         :target nil
         :valid t))
       ((if (not (and (sig-value->value go-empty)
                      (sig-value->value full))))
        (make-target-tuple
         :target t
         :valid t)))
    (make-target-tuple
     :target nil
     :valid nil)))

(define full-internal-trigger-time ((full sig-value-p) (empty sig-value-p)
                                    (go-full sig-value-p) (go-empty sig-value-p)
                                    (full-internal sig-value-p))
  :returns (trigger-time maybe-rational-p)
  (b* ((full (sig-value-fix full))
       (empty (sig-value-fix empty))
       (go-full (sig-value-fix go-full))
       (go-empty (sig-value-fix go-empty))
       (full-internal (sig-value-fix full-internal))
       (target-tuple (full-internal-target full empty go-full go-empty
                                           full-internal))
       (target (target-tuple->target target-tuple))
       (valid (target-tuple->valid target-tuple))
       ((unless valid)
        (maybe-rational-some
         (min (max (sig-value->time go-empty)
                   (sig-value->time full))
              (max (sig-value->time go-full)
                   (sig-value->time empty)))))
       ((if (equal target (sig-value->value full-internal)))
        (maybe-rational-fix nil))
       ((if (equal target t))
        (maybe-rational-some
         (max (sig-value->time go-full)
              (sig-value->time empty)))))
    ;; target == nil
    (maybe-rational-some
     (max (sig-value->time go-empty)
          (sig-value->time full)))))

;; full_interval ->(delta_t2) full ^ not(empty)
;; not(full_interval) ->(delta_t2) not(full) ^ empty
(define full-target ((full sig-value-p) (full-internal sig-value-p))
  :returns (target target-tuple-p)
  (b* ((full (sig-value-fix full))
       (full-internal (sig-value-fix full-internal))
       ((if (equal (sig-value->value full-internal)
                   (sig-value->value full)))
        (make-target-tuple
         :target (sig-value->value full)
         :valid t)))
    (make-target-tuple
     :target (sig-value->value full-internal)
     :valid t)))

(define full-trigger-time ((full sig-value-p)
                           (full-internal sig-value-p))
  :returns (trigger-time maybe-rational-p)
  (b* ((full (sig-value-fix full))
       (full-internal (sig-value-fix full-internal))
       (target (full-target full full-internal))
       ((if (equal target (sig-value->value full)))
        (maybe-rational-fix nil)))
    ;; target == full-internal
    (maybe-rational-some
     (sig-value->time full-internal))))

(define empty-target ((empty sig-value-p) (full-internal sig-value-p))
  :returns (target target-tuple-p)
  (b* ((empty (sig-value-fix empty))
       (full-internal (sig-value-fix full-internal))
       ((if (not (equal (sig-value->value full-internal)
                        (sig-value->value empty))))
        (make-target-tuple
         :target (sig-value->value empty)
         :valid t)))
    (make-target-tuple
     :target (sig-value->value full-internal)
     :valid t)))

(define empty-trigger-time ((empty sig-value-p)
                            (full-internal sig-value-p))
  :returns (trigger-time maybe-rational-p)
  (b* ((empty (sig-value-fix empty))
       (full-internal (sig-value-fix full-internal))
       (target (empty-target empty full-internal))
       ((if (equal target (sig-value->value empty)))
        (maybe-rational-fix nil)))
    ;; target == full-internal
    (maybe-rational-some
     (sig-value->time full-internal))))

;; -----------------------------------------------------
;; signal transition constraints function -- for both env and the stage

;; target-tuple is the target value calculated based on the prev state
;; trigger-time is the trigger time calculated based on the prev state
;; This function states constraints on the next state based on target-tuple and
;; trigger-time
(define signal-transition-constraints ((sig-prev sig-value-p)
                                       (tnext rationalp)
                                       (sig-next sig-value-p)
                                       (target-tuple target-tuple-p)
                                       (trigger-time maybe-rational-p)
                                       (delay interval-p))
  :returns (constraints booleanp)
  (b* ((sig-prev (sig-value-fix sig-prev))
       (sig-next (sig-value-fix sig-next))
       (delay (interval-fix delay))
       (target (target-tuple->target target-tuple))
       (valid (target-tuple->valid target-tuple))
       ;; If trigger-time is nil, this means the target is already achieved
       ;; we don't need any constraints on trigger-time
       ((if (equal trigger-time
                   (maybe-rational-fix nil)))
        (implies (and valid
                      (equal (sig-value->value sig-prev) target))
                 (equal (sig-value->value sig-next)
                        (sig-value->value sig-prev)))))
    (and
     ;; If previous state is not target value,
     (implies (and valid (not (equal (sig-value->value sig-prev) target)))
              ;; if state hasn't changed yet, then there should still be time
              (and (implies (equal (sig-value->value sig-prev)
                                   (sig-value->value sig-next))
                            (< tnext (+ trigger-time (interval->hi delay))))
                   ;; if state already changed, then time should be after
                   ;; minimum time
                   (implies (not (equal (sig-value->value sig-prev)
                                        (sig-value->value sig-next)))
                            (>= tnext (+ trigger-time (interval->lo delay))))))
     ;; If it's a failure state, we don't constrain the value, but any change
     ;; will have to be after minimum delay
     (implies
      (and (not valid) (not (equal (sig-value->value sig-prev)
                                   (sig-value->value sig-next))))
      (<= (+ trigger-time (interval->lo delay)) tnext)))))

;; =====================================================
;; stepping function
(define asp-sigs ((a asp-stage-p))
  :returns (l sig-path-listp)
  (b* ((a (asp-stage-fix a))
       (go-full (asp-stage->go-full a))
       (go-empty (asp-stage->go-empty a))
       (full (asp-stage->full a))
       (empty (asp-stage->empty a))
       (full-internal (asp-stage->full-internal a)))
    (cons full-internal
          (sig-path-list-fix
           (cons empty
                 (sig-path-list-fix
                  (cons full
                        (sig-path-list-fix
                         (cons go-full
                               (sig-path-list-fix
                                (cons go-empty (sig-path-list-fix nil))))))))))))

(define time-consistent-when-signal-doesnt-change ((sig-prev sig-value-p)
                                                   (sig-next sig-value-p))
  :returns (ok booleanp)
  (b* ((sig-prev (sig-value-fix sig-prev))
       (sig-next (sig-value-fix sig-next))
       (x-prev (sig-value->value sig-prev))
       (x-next (sig-value->value sig-next))
       (x-time-prev (sig-value->time sig-prev))
       (x-time-next (sig-value->time sig-next)))
    (implies (equal x-next x-prev)
             (equal x-time-next x-time-prev))))

(define time-set-when-signal-change ((sig-prev sig-value-p)
                                     (sig-next sig-value-p)
                                     (time rationalp))
  :returns (ok booleanp)
  (b* ((sig-prev (sig-value-fix sig-prev))
       (sig-next (sig-value-fix sig-next))
       (x-prev (sig-value->value sig-prev))
       (x-next (sig-value->value sig-next))
       (x-time-next (sig-value->time sig-next)))
    (implies (not (equal x-next x-prev))
             (equal x-time-next time))))

(define nondecreasing-time ((tprev rationalp)
                            (tnext rationalp))
  :returns (ok booleanp)
  (<= tprev tnext))

(defthm crock
  (implies (and (gstate-p s)
                (consp (assoc-equal k s)))
           (sig-value-p (cdr (assoc-equal k s)))))

(define asp-step ((a asp-stage-p)
                  (tprev rationalp) (prev gstate-p)
                  (tnext rationalp) (next gstate-p))
  :returns (ok booleanp)
  ;; Need a theorem that says if sigs-in-bool-table, then assoc-equal is not nil
  :guard-hints (("Goal" :in-theory (e/d (sigs-in-bool-table asp-sigs))))
  (b* ((a (asp-stage-fix a))
       (prev (gstate-fix prev))
       (next (gstate-fix next))
       ((unless (sigs-in-bool-table (asp-sigs a) prev)) nil)
       ((unless (sigs-in-bool-table (asp-sigs a) next)) nil)
       (go-full (asp-stage->go-full a))
       (go-empty (asp-stage->go-empty a))
       (full (asp-stage->full a))
       (empty (asp-stage->empty a))
       (full-internal (asp-stage->full-internal a))
       (delta-t1 (asp-stage->delta-t1 a))
       (delta-t2 (asp-stage->delta-t2 a))
       (go-full-prev (cdr (smt::magic-fix
                           'sig-path_sig-value
                           (assoc-equal go-full (gstate-fix prev)))))
       (go-full-next (cdr (smt::magic-fix
                           'sig-path_sig-value
                           (assoc-equal go-full (gstate-fix next)))))
       (go-empty-prev (cdr (smt::magic-fix
                            'sig-path_sig-value
                            (assoc-equal go-empty (gstate-fix prev)))))
       (go-empty-next (cdr (smt::magic-fix
                            'sig-path_sig-value
                            (assoc-equal go-empty (gstate-fix next)))))
       (full-prev (cdr (smt::magic-fix
                        'sig-path_sig-value
                        (assoc-equal full (gstate-fix prev)))))
       (full-next (cdr (smt::magic-fix
                        'sig-path_sig-value
                        (assoc-equal full (gstate-fix next)))))
       (empty-prev (cdr (smt::magic-fix
                         'sig-path_sig-value
                         (assoc-equal empty (gstate-fix prev)))))
       (empty-next (cdr (smt::magic-fix
                         'sig-path_sig-value
                         (assoc-equal empty (gstate-fix next)))))
       (full-internal-prev (cdr (smt::magic-fix
                                 'sig-path_sig-value
                                 (assoc-equal full-internal
                                              (gstate-fix prev)))))
       (full-internal-next (cdr (smt::magic-fix
                                 'sig-path_sig-value
                                 (assoc-equal full-internal
                                              (gstate-fix next)))))
       ;; basic timing constraints
       ((unless (and (nondecreasing-time tprev tnext)
                     (time-consistent-when-signal-doesnt-change empty-prev empty-next)
                     (time-consistent-when-signal-doesnt-change full-prev full-next)
                     (time-consistent-when-signal-doesnt-change go-empty-prev go-empty-next)
                     (time-consistent-when-signal-doesnt-change go-full-prev
                                                                go-full-next)
                     (time-consistent-when-signal-doesnt-change full-internal-prev
                                                                full-internal-next)
                     (time-set-when-signal-change empty-prev empty-next tnext)
                     (time-set-when-signal-change full-prev full-next tnext)
                     (time-set-when-signal-change go-empty-prev go-empty-next tnext)
                     (time-set-when-signal-change go-full-prev go-full-next tnext)
                     (time-set-when-signal-change full-internal-prev full-internal-next
                                                  tnext)
                     ))
        nil)
       ;; full-internal specific constraints
       (fi-target
        (full-internal-target full-prev empty-prev go-full-prev
                              go-empty-prev full-internal-prev))
       (fi-time
        (full-internal-trigger-time full-prev empty-prev go-full-prev
                                    go-empty-prev full-internal-prev))
       ((unless (signal-transition-constraints full-internal-prev tnext
                                               full-internal-next fi-target
                                               fi-time delta-t1))
        nil)
       ;; full specific constraints
       (f-target (full-target full-prev full-internal-prev))
       (f-time (full-trigger-time full-prev full-internal-prev))
       ((unless (signal-transition-constraints full-prev tnext full-next
                                               f-target f-time delta-t2))
        nil)
       ;; empty specific constraints
       (e-target (empty-target empty-prev full-internal-prev))
       (e-time (full-trigger-time empty-prev full-internal-prev))
       ((unless (signal-transition-constraints empty-prev tnext empty-next
                                               e-target e-time delta-t2))
        nil))
    t))

(define asp-valid ((a asp-stage-p)
                   (tr gtrace-p))
  :returns (ok booleanp)
  :measure (len (gtrace-fix tr))
  :hints (("Goal" :in-theory (enable gtrace-fix)))
  (b* ((a (asp-stage-fix a))
       ((unless (consp (gtrace-fix (cdr (gtrace-fix tr))))) t)
       (first (car (gtrace-fix tr)))
       (rest (cdr (gtrace-fix tr)))
       (second (car (gtrace-fix rest)))
       ((unless (asp-step a
                          (gstate-t->statet first)
                          (gstate-t->statev first)
                          (gstate-t->statet second)
                          (gstate-t->statev second)))
        nil))
    (asp-valid a rest)))

;; -----------------------------------------------------
;; target and trigger-time functions for the environment

(define left-internal-target ((left-internal sig-value-p) (empty sig-value-p)
                              (go-full sig-value-p))
  :returns (target target-tuple-p)
  (b* ((empty (sig-value-fix empty))
       (go-full (sig-value-fix go-full))
       (left-internal (sig-value-fix left-internal))
       ((if (and (sig-value->value go-full)
                 (sig-value->value empty)))
        (make-target-tuple
         :target nil
         :valid t))
       ((if (not (sig-value->value go-full)))
        (make-target-tuple
         :target nil
         :valid t)))
    (make-target-tuple
     :target (sig-value->value left-internal)
     :valid t))
  )

(define left-internal-trigger-time ((left-internal sig-value-p) (empty sig-value-p)
                                    (go-full sig-value-p))
  :returns (trigger-time maybe-rational-p)
  (b* ((empty (sig-value-fix empty))
       (go-full (sig-value-fix go-full))
       (left-internal (sig-value-fix left-internal))
       (target (left-internal-target left-internal empty go-full))
       ((if (equal target (sig-value->value left-internal)))
        (maybe-rational-fix nil))
       ((if (equal target nil))
        (maybe-rational-some
         (max (sig-value->time go-full)
              (sig-value->time empty)))))
    ;; (equal target t)
    (maybe-rational-some
     (sig-value->time go-full))))

(define lenv-go-full-target ((left-internal sig-value-p)
                             (go-full sig-value-p))
  :returns (target target-tuple-p)
  (b* ((go-full (sig-value-fix go-full))
       (left-internal (sig-value-fix left-internal))
       ((if (not (equal (sig-value->value left-internal)
                        (sig-value->value go-full))))
        (make-target-tuple
         :target (sig-value->value left-internal)
         :valid t)))
    (make-target-tuple
     :target (sig-value->value go-full)
     :valid t))
  )

(define lenv-go-full-trigger-time ((left-internal sig-value-p)
                                   (go-full sig-value-p))
  :returns (trigger-time maybe-rational-p)
  (b* ((go-full (sig-value-fix go-full))
       (left-internal (sig-value-fix left-internal))
       (target (lenv-go-full-target left-internal go-full))
       ((if (equal target (sig-value->value go-full)))
        (maybe-rational-fix nil)))
    ;; target == full-internal
    (maybe-rational-some
     (sig-value->time left-internal))))


(define right-internal-target ((right-internal sig-value-p) (full sig-value-p)
                               (go-empty sig-value-p))
  :returns (target target-tuple-p)
  (b* ((full (sig-value-fix full))
       (go-empty (sig-value-fix go-empty))
       (right-internal (sig-value-fix right-internal))
       ((if (and (sig-value->value go-empty)
                 (sig-value->value full)))
        (make-target-tuple
         :target t
         :valid t))
       ((if (not (sig-value->value go-empty)))
        (make-target-tuple
         :target nil
         :valid t)))
    (make-target-tuple
     :target (sig-value->value right-internal)
     :valid t))
  )

(define right-internal-trigger-time ((right-internal sig-value-p) (full sig-value-p)
                                     (go-empty sig-value-p))
  :returns (trigger-time maybe-rational-p)
  (b* ((full (sig-value-fix full))
       (go-empty (sig-value-fix go-empty))
       (right-internal (sig-value-fix right-internal))
       (target (right-internal-target right-internal full go-empty))
       ((if (equal target (sig-value->value right-internal)))
        (maybe-rational-fix nil))
       ((if (equal target t))
        (maybe-rational-some
         (max (sig-value->time go-empty)
              (sig-value->time full)))))
    ;; (equal target t)
    (maybe-rational-some
     (sig-value->time go-empty))))


(define renv-go-empty-target ((right-internal sig-value-p)
                              (go-empty sig-value-p))
  :returns (target target-tuple-p)
  (b* ((go-empty (sig-value-fix go-empty))
       (right-internal (sig-value-fix right-internal))
       ((if (equal (sig-value->value right-internal)
                   (sig-value->value go-empty)))
        (make-target-tuple
         :target (not (sig-value->value right-internal))
         :valid t)))
    (make-target-tuple
     :target (sig-value->value go-empty)
     :valid t)))

(define renv-go-empty-trigger-time ((right-internal sig-value-p)
                                    (go-empty sig-value-p))
  :returns (trigger-time maybe-rational-p)
  (b* ((go-empty (sig-value-fix go-empty))
       (right-internal (sig-value-fix right-internal))
       (target (renv-go-empty-target right-internal go-empty))
       ((if (equal target (sig-value->value go-empty)))
        (maybe-rational-fix nil)))
    (maybe-rational-some
     (sig-value->time right-internal))))

;; -------------------------------------------------
;;             environment

(defprod lenv
  ((empty sig-path-p)
   (go-full sig-path-p)
   (left-internal sig-path-p)
   (delta-env interval-p)
   ))

(define lenv-sigs ((e lenv-p))
  :returns (l sig-path-listp)
  (b* ((e (lenv-fix e))
       (empty (lenv->empty e))
       (go-full (lenv->go-full e))
       (left-internal (lenv->left-internal e)))
    (cons empty (sig-path-list-fix
                 (cons go-full
                       (sig-path-list-fix
                        (cons left-internal
                              (sig-path-list-fix nil))))))))

(defprod renv
  ((full sig-path-p)
   (go-empty sig-path-p)
   (right-internal sig-path-p)
   (delta-env interval-p)
   ))

(define renv-sigs ((e renv-p))
  :returns (l sig-path-listp)
  (b* ((e (renv-fix e))
       (full (renv->full e))
       (go-empty (renv->go-empty e))
       (right-internal (renv->right-internal e)))
    (cons full (sig-path-list-fix
                (cons go-empty
                      (sig-path-list-fix
                       (cons right-internal
                             (sig-path-list-fix nil))))))))

(define lenv-step ((e lenv-p)
                   (tprev rationalp) (prev gstate-p)
                   (tnext rationalp) (next gstate-p))
  :returns (ok booleanp)
  ;; Need a theorem that says if sigs-in-bool-table, then assoc-equal is not nil
  :guard-hints (("Goal" :in-theory (e/d (sigs-in-bool-table lenv-sigs))))
  (b* ((e (lenv-fix e))
       (prev (gstate-fix prev))
       (next (gstate-fix next))
       ((unless (sigs-in-bool-table (lenv-sigs e) prev)) nil)
       ((unless (sigs-in-bool-table (lenv-sigs e) next)) nil)
       (empty (lenv->empty e))
       (go-full (lenv->go-full e))
       (left-internal (lenv->left-internal e))
       (delta-env (lenv->delta-env e))
       (empty-prev (cdr (smt::magic-fix
                         'sig-path_sig-value
                         (assoc-equal empty (gstate-fix prev)))))
       (empty-next (cdr (smt::magic-fix
                         'sig-path_sig-value
                         (assoc-equal empty (gstate-fix next)))))
       (go-full-prev (cdr (smt::magic-fix
                           'sig-path_sig-value
                           (assoc-equal go-full (gstate-fix prev)))))
       (go-full-next (cdr (smt::magic-fix
                           'sig-path_sig-value
                           (assoc-equal go-full (gstate-fix next)))))
       (left-internal-prev (cdr (smt::magic-fix
                                 'sig-path_sig-value
                                 (assoc-equal left-internal (gstate-fix prev)))))
       (left-internal-next (cdr (smt::magic-fix
                                 'sig-path_sig-value
                                 (assoc-equal left-internal (gstate-fix next)))))
       ((unless (and (nondecreasing-time tprev tnext)
                     (time-consistent-when-signal-doesnt-change empty-prev empty-next)
                     (time-consistent-when-signal-doesnt-change go-full-prev
                                                                go-full-next)
                     (time-consistent-when-signal-doesnt-change
                      left-internal-prev left-internal-next)
                     (time-set-when-signal-change empty-prev empty-next tnext)
                     (time-set-when-signal-change go-full-prev go-full-next
                                                  tnext)
                     (time-set-when-signal-change left-internal-prev
                                                  left-internal-next
                                                  tnext)
                     ))
        nil)
       ;; left-internal specific constraints:
       ;; Need to think about what to do when there's a timing constraint of +infinity
       (li-target
        (left-internal-target left-internal-prev empty-prev go-full-prev))
       (li-time
        (left-internal-trigger-time left-internal-prev empty-prev
                                    go-full-prev))
       ((unless (signal-transition-constraints left-internal-prev tnext
                                               left-internal-next li-target
                                               li-time delta-env))
        nil)
       ;; go-full specific constraints:
       (gf-target
        (lenv-go-full-target left-internal-prev go-full-prev))
       (gf-time
        (lenv-go-full-trigger-time left-internal-prev go-full-prev))
       ((unless (signal-transition-constraints go-full-prev tnext
                                               go-full-next gf-target
                                               gf-time delta-env))
        nil))
    t))

(define lenv-valid ((e lenv-p)
                    (tr gtrace-p))
  :returns (ok booleanp)
  :measure (len (gtrace-fix tr))
  :hints (("Goal" :in-theory (enable gtrace-fix)))
  (b* ((e (lenv-fix e))
       ((unless (consp (gtrace-fix (cdr (gtrace-fix tr))))) t)
       (first (car (gtrace-fix tr)))
       (rest (cdr (gtrace-fix tr)))
       (second (car (gtrace-fix rest)))
       ((unless (lenv-step e
                           (gstate-t->statet first)
                           (gstate-t->statev first)
                           (gstate-t->statet second)
                           (gstate-t->statev second)))
        nil))
    (lenv-valid e rest)))

(define renv-step ((e renv-p)
                   (tprev rationalp) (prev gstate-p)
                   (tnext rationalp) (next gstate-p))
  :returns (ok booleanp)
  ;; Need a theorem that says if sigs-in-bool-table, then assoc-equal is not nil
  :guard-hints (("Goal" :in-theory (e/d (sigs-in-bool-table renv-sigs))))
  (b* ((e (renv-fix e))
       (prev (gstate-fix prev))
       (next (gstate-fix next))
       ((unless (sigs-in-bool-table (renv-sigs e) prev)) nil)
       ((unless (sigs-in-bool-table (renv-sigs e) next)) nil)
       (full (renv->full e))
       (go-empty (renv->go-empty e))
       (right-internal (renv->right-internal e))
       (delta-env (renv->delta-env e))
       (full-prev (cdr (smt::magic-fix
                        'sig-path_sig-value
                        (assoc-equal full (gstate-fix prev)))))
       (full-next (cdr (smt::magic-fix
                        'sig-path_sig-value
                        (assoc-equal full (gstate-fix next)))))
       (go-empty-prev (cdr (smt::magic-fix
                            'sig-path_sig-value
                            (assoc-equal go-empty (gstate-fix prev)))))
       (go-empty-next (cdr (smt::magic-fix
                            'sig-path_sig-value
                            (assoc-equal go-empty (gstate-fix next)))))
       (right-internal-prev (cdr (smt::magic-fix
                                  'sig-path_sig-value
                                  (assoc-equal right-internal (gstate-fix prev)))))
       (right-internal-next (cdr (smt::magic-fix
                                  'sig-path_sig-value
                                  (assoc-equal right-internal (gstate-fix next)))))
       ((unless (and (nondecreasing-time tprev tnext)
                     (time-consistent-when-signal-doesnt-change full-prev full-next)
                     (time-consistent-when-signal-doesnt-change go-empty-prev
                                                                go-empty-next)
                     (time-consistent-when-signal-doesnt-change
                      right-internal-prev right-internal-next)
                     (time-set-when-signal-change full-prev full-next tnext)
                     (time-set-when-signal-change go-empty-prev go-empty-next
                                                  tnext)
                     (time-set-when-signal-change right-internal-prev
                                                  right-internal-next
                                                  tnext)
                     ))
        nil)
       ;; right-internal specific constraints:
       ;; Need to think about what to do when there's a timing constraint of +infinity
       (ri-target
        (right-internal-target right-internal-prev full-prev go-empty-prev))
       (ri-time
        (right-internal-trigger-time right-internal-prev full-prev
                                     go-empty-prev))
       ((unless (signal-transition-constraints right-internal-prev tnext
                                               right-internal-next ri-target
                                               ri-time delta-env))
        nil)
       ;; go-empty specific constraints:
       (ge-target
        (renv-go-empty-target right-internal-prev go-empty-prev))
       (ge-time
        (renv-go-empty-trigger-time right-internal-prev go-empty-prev))
       ((unless (signal-transition-constraints go-empty-prev tnext
                                               go-empty-next ge-target
                                               ge-time delta-env))
        nil))
    t)
  )

(define renv-valid ((e renv-p)
                    (tr gtrace-p))
  :returns (ok booleanp)
  :measure (len (gtrace-fix tr))
  :hints (("Goal" :in-theory (enable gtrace-fix)))
  (b* ((e (renv-fix e))
       ((unless (consp (gtrace-fix (cdr (gtrace-fix tr))))) t)
       (first (car (gtrace-fix tr)))
       (rest (cdr (gtrace-fix tr)))
       (second (car (gtrace-fix rest)))
       ((unless (renv-step e
                           (gstate-t->statet first)
                           (gstate-t->statev first)
                           (gstate-t->statet second)
                           (gstate-t->statev second)))
        nil))
    (renv-valid e rest)))

;; ------------------------------------------------------------
;;         define connection function of env to an asp-stage

(define asp-connection ((a asp-stage-p) (el lenv-p) (er renv-p))
  :returns (ok booleanp)
  (and (equal (asp-stage->go-full a)
              (lenv->go-full el))
       (equal (asp-stage->empty a)
              (lenv->empty el))
       (equal (asp-stage->go-empty a)
              (renv->go-empty er))
       (equal (asp-stage->full a)
              (renv->full er))
       )
  )

;; -----------------------------------------------------------------
;;       define how we count symbols in the fifo
(defoption maybe-integer integerp)

(define sym-count ((a asp-stage-p) (curr gstate-p))
  :returns (count maybe-integer-p)
  :guard-hints (("Goal" :in-theory (enable sigs-in-bool-table asp-sigs)))
  (b* ((a (asp-stage-fix a))
       (curr (gstate-fix curr))
       ((unless (sigs-in-bool-table (asp-sigs a) curr))
        (maybe-integer-fix nil))
       (go-full (asp-stage->go-full a))
       (go-empty (asp-stage->go-empty a))
       (full (asp-stage->full a))
       (empty (asp-stage->empty a))
       (go-full-curr (cdr (smt::magic-fix
                           'sig-path_sig-value
                           (assoc-equal go-full (gstate-fix curr)))))
       (go-empty-curr (cdr (smt::magic-fix
                            'sig-path_sig-value
                            (assoc-equal go-empty (gstate-fix curr)))))
       (full-curr (cdr (smt::magic-fix
                        'sig-path_sig-value
                        (assoc-equal full (gstate-fix curr)))))
       (empty-curr (cdr (smt::magic-fix
                         'sig-path_sig-value
                         (assoc-equal empty (gstate-fix curr))))))
    (cond ((and (not (and (sig-value->value go-full-curr)
                          (sig-value->value empty-curr)))
                (not (and (sig-value->value go-empty-curr)
                          (sig-value->value full-curr))))
           (maybe-integer-some 1))
          ((and (sig-value->value go-full-curr)
                (sig-value->value empty-curr))
           (maybe-integer-some 1))
          ((and (sig-value->value go-empty-curr)
                (sig-value->value full-curr))
           (maybe-integer-some 0))
          (t
           (maybe-integer-fix nil)))))

(defthm simple-yan
  (implies (and (asp-stage-p a)
                (lenv-p el)
                (renv-p er)
                (asp-connection a el er)
                (gtrace-p tr)
                (lenv-valid el tr)
                (renv-valid er tr)
                (asp-valid a tr)
                (valid-interval (asp-stage->delta-t1 a))
                (valid-interval (asp-stage->delta-t2 a))
                (valid-interval (lenv->delta-env el))
                (valid-interval (renv->delta-env er))
                (consp (gtrace-fix tr))
                (consp (gtrace-fix (cdr (gtrace-fix tr))))
                (equal (sym-count a (gstate-t->statev (car (gtrace-fix tr))))
                       (maybe-integer-some 1)))
           (equal (sym-count a
                             (gstate-t->statev
                              (car (gtrace-fix (cdr (gtrace-fix tr))))))
                             (maybe-integer-some 1)))
  :hints (("Goal"
           :smtlink
           (:fty (asp-stage env interval gtrace sig-value gstate gstate-t
                            sig-path-list sig-path sig maybe-integer)
                 :functions ((sigs-in-bool-table :formals ((sigs sig-path-listp)
                                                           (st gstate-p))
                                                 :returns ((ok booleanp))
                                                 :level 5)
                             (sigs-in-bool-trace :formals ((sigs sig-path-listp)
                                                           (tr gstate-p))
                                                 :returns ((ok booleanp))
                                                 :level 2)
                             (env-valid :formals ((e env-p)
                                                  (tr gtrace-p))
                                        :returns ((ok booleanp))
                                        :level 1)
                             (asp-valid :formals ((a asp-stage-p)
                                                  (tr gtrace-p))
                                        :returns ((ok booleanp))
                                        :level 1)
                             )
                 ))))
