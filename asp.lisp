(in-package "ASP")
;; m = test._SMT_.solver.model()
;; simplify(gstate_sub_t.statev(gtrace.car(gtrace.cdr(m[tr])))).sexpr()

(include-book "std/util/define" :dir :system)
(include-book "tools/bstar" :dir :system)
(include-book "centaur/fty/top" :dir :system) ; for defalist, etc.
(include-book "misc/eval" :dir :system)
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
(defoption maybe-rational rationalp)

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

   (delta interval-p)
   ))

;; =====================================================
;; targets and trigger time
(defprod target-tuple
  ((target booleanp)
   (valid booleanp)))

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
       (tp (full-internal-target full empty go-full go-empty
                                 full-internal))
       (target (target-tuple->target tp))
       (valid (target-tuple->valid tp))
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
       (tp (full-target full full-internal))
       (target (target-tuple->target tp))
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
     :target (not (sig-value->value full-internal))
     :valid t)))

(define empty-trigger-time ((empty sig-value-p)
                            (full-internal sig-value-p))
  :returns (trigger-time maybe-rational-p)
  (b* ((empty (sig-value-fix empty))
       (full-internal (sig-value-fix full-internal))
       (tp (empty-target empty full-internal))
       (target (target-tuple->target tp))
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
                                       (tp target-tuple-p)
                                       (trigger-time maybe-rational-p)
                                       (delay interval-p))
  :returns (constraints booleanp)
  (b* ((sig-prev (sig-value-fix sig-prev))
       (sig-next (sig-value-fix sig-next))
       (tp (target-tuple-fix tp))
       (delay (interval-fix delay))
       (target (target-tuple->target tp))
       (valid (target-tuple->valid tp))
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
                            (< tnext (+ (maybe-rational-some->val trigger-time)
                                        (interval->hi delay))))
                   ;; if state already changed, then time should be after
                   ;; minimum time
                   (implies (not (equal (sig-value->value sig-prev)
                                        (sig-value->value sig-next)))
                            (and (>= tnext (+ (maybe-rational-some->val
                                               trigger-time)
                                              (interval->lo delay)))
                                 ;; ;; Yan: added this constraints for bug fixing,
                                 ;; ;; not sure yet if this is right.
                                 (< (sig-value->time sig-next)
                                    (+ (maybe-rational-some->val trigger-time)
                                       (interval->hi delay)))
                                 ))))
     ;; If it's a failure state, we don't constrain the value, but any change
     ;; will have to be after minimum delay
     (implies
      (and (not valid) (not (equal (sig-value->value sig-prev)
                                   (sig-value->value sig-next))))
      (<= (+ (maybe-rational-some->val trigger-time)
             (interval->lo delay))
          tnext)))))

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

(define sig-time-<=-curr-time->=0 ((sig-curr sig-value-p)
                                   (tcurr rationalp))
  :returns (ok booleanp)
  (b* ((sig-curr (sig-value-fix sig-curr))
       (x-time-curr (sig-value->time sig-curr)))
    (and (>= x-time-curr 0)
         (<= x-time-curr tcurr))))

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
       (delta (asp-stage->delta a))
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
                     (sig-time-<=-curr-time->=0 empty-prev tprev)
                     (sig-time-<=-curr-time->=0 empty-next tnext)
                     (sig-time-<=-curr-time->=0 full-prev tprev)
                     (sig-time-<=-curr-time->=0 full-next tnext)
                     (sig-time-<=-curr-time->=0 go-empty-prev tprev)
                     (sig-time-<=-curr-time->=0 go-empty-next tnext)
                     (sig-time-<=-curr-time->=0 go-full-prev tprev)
                     (sig-time-<=-curr-time->=0 go-full-next tnext)
                     (sig-time-<=-curr-time->=0 full-internal-prev tprev)
                     (sig-time-<=-curr-time->=0 full-internal-next tnext)
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
                                               fi-time delta))
        nil)
       ;; full specific constraints
       (f-target (full-target full-prev full-internal-prev))
       (f-time (full-trigger-time full-prev full-internal-prev))
       ((unless (signal-transition-constraints full-prev tnext full-next
                                               f-target f-time delta))
        nil)
       ;; empty specific constraints
       (e-target (empty-target empty-prev full-internal-prev))
       (e-time (empty-trigger-time empty-prev full-internal-prev))
       ((unless (signal-transition-constraints empty-prev tnext empty-next
                                               e-target e-time delta))
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
         :target t
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
       (tp (left-internal-target left-internal empty go-full))
       (target (target-tuple->target tp))
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
       (tp (lenv-go-full-target left-internal go-full))
       (target (target-tuple->target tp))
       ((if (equal target (sig-value->value go-full)))
        (maybe-rational-fix nil)))
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
       (tp (right-internal-target right-internal full go-empty))
       (target (target-tuple->target tp))
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
       (tp (renv-go-empty-target right-internal go-empty))
       (target (target-tuple->target tp))
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
   (delta interval-p)
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
   (delta interval-p)
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
       (delta (lenv->delta e))
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
                     (sig-time-<=-curr-time->=0 empty-prev tprev)
                     (sig-time-<=-curr-time->=0 empty-next tnext)
                     (sig-time-<=-curr-time->=0 go-full-prev tprev)
                     (sig-time-<=-curr-time->=0 go-full-next tnext)
                     (sig-time-<=-curr-time->=0 left-internal-prev tprev)
                     (sig-time-<=-curr-time->=0 left-internal-next tnext)
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
       ((unless (cond ((equal li-time (maybe-rational-fix nil))
                       (implies (equal (sig-value->value left-internal-prev)
                                       (target-tuple->target li-target))
                                (equal (sig-value->value left-internal-next)
                                       (sig-value->value left-internal-prev))))
                      ((equal (sig-value->value go-full-prev) nil)
                       (implies (not (equal (sig-value->value left-internal-prev)
                                            (sig-value->value left-internal-next)))
                                (>= tnext (+ (maybe-rational-some->val li-time)
                                             (interval->lo delta)))))
                      (t (signal-transition-constraints left-internal-prev tnext
                                                        left-internal-next li-target
                                                        li-time delta))))
        nil)
       ;; go-full specific constraints:
       (gf-target
        (lenv-go-full-target left-internal-prev go-full-prev))
       (gf-time
        (lenv-go-full-trigger-time left-internal-prev go-full-prev))
       ((unless (signal-transition-constraints go-full-prev tnext
                                               go-full-next gf-target
                                               gf-time delta))
        nil)
       )
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
       (delta (renv->delta e))
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
                     (sig-time-<=-curr-time->=0 full-prev tprev)
                     (sig-time-<=-curr-time->=0 full-next tnext)
                     (sig-time-<=-curr-time->=0 go-empty-prev tprev)
                     (sig-time-<=-curr-time->=0 go-empty-next tnext)
                     (sig-time-<=-curr-time->=0 right-internal-prev tprev)
                     (sig-time-<=-curr-time->=0 right-internal-next tnext)
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
       ((unless (cond ((equal ri-time (maybe-rational-fix nil))
                       (implies (equal (sig-value->value right-internal-prev)
                                       (target-tuple->target ri-target))
                                (equal (sig-value->value right-internal-next)
                                       (sig-value->value right-internal-prev))))
                      ((equal (sig-value->value go-empty-prev) nil)
                       (implies (not (equal (sig-value->value right-internal-prev)
                                            (sig-value->value right-internal-next)))
                                (>= tnext (+ (maybe-rational-some->val ri-time)
                                             (interval->lo delta)))))
                      (t (signal-transition-constraints right-internal-prev tnext
                                                        right-internal-next ri-target
                                                        ri-time delta))))
        nil)
       ;; go-empty specific constraints:
       (ge-target
        (renv-go-empty-target right-internal-prev go-empty-prev))
       (ge-time
        (renv-go-empty-trigger-time right-internal-prev go-empty-prev))
       ((unless (signal-transition-constraints go-empty-prev tnext
                                               go-empty-next ge-target
                                               ge-time delta))
        nil)
       )
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

;; ========================================================================================
;;     a test for sort mismatch and stuff

(std::must-fail
(defthm simple-yan
  (implies (and (asp-stage-p a)
                (lenv-p el)
                (renv-p er)
                (asp-connection a el er)
                (gtrace-p tr)
                (lenv-valid el tr)
                (renv-valid er tr)
                (asp-valid a tr)
                (valid-interval (asp-stage->delta a))
                (valid-interval (lenv->delta el))
                (valid-interval (renv->delta er))
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
           (:fty (asp-stage lenv renv interval gtrace sig-value gstate gstate-t
                            sig-path-list sig-path sig maybe-integer
                            maybe-rational target-tuple)
                 :functions ((sigs-in-bool-table :formals ((sigs sig-path-listp)
                                                           (st gstate-p))
                                                 :returns ((ok booleanp))
                                                 :level 5)
                             (sigs-in-bool-trace :formals ((sigs sig-path-listp)
                                                           (tr gstate-p))
                                                 :returns ((ok booleanp))
                                                 :level 2)
                             (lenv-valid :formals ((e lenv-p)
                                                   (tr gtrace-p))
                                         :returns ((ok booleanp))
                                         :level 1)
                             (renv-valid :formals ((e renv-p)
                                                   (tr gtrace-p))
                                         :returns ((ok booleanp))
                                         :level 1)
                             (asp-valid :formals ((a asp-stage-p)
                                                  (tr gtrace-p))
                                        :returns ((ok booleanp))
                                        :level 1)
                             )
                 ))))
)


;; ========================================================================================
;;    The invariant

;; (define tag-b ((b booleanp) (n integerp))
;;   :returns (res booleanp)
;;   (declare (ignore n))
;;   (if (equal b t) t
;;     nil))

(define invariant-stage ((go-full sig-value-p)
                         (go-empty sig-value-p)
                         (full sig-value-p)
                         (empty sig-value-p)
                         (full-internal sig-value-p)
                         (delta interval-p)
                         (tcurr rationalp))
  :returns (ok booleanp)
  (b* ((go-full (sig-value-fix go-full))
       (go-empty (sig-value-fix go-empty))
       (full (sig-value-fix full))
       (empty (sig-value-fix empty))
       (full-internal (sig-value-fix full-internal))
       (delta (interval-fix delta)))
    (and
     ;; constraints on empty, go-full, and full-internal
     ;; if full-internal is excited to go true but hasn't yet,
     ;;   then time-now is less than the max delay for full-internal.
     (implies (and (sig-value->value empty)
                   (sig-value->value go-full)
                   (not (sig-value->value full-internal)))
              (> (+ (max (sig-value->time empty)
                         (sig-value->time go-full))
                    (interval->hi delta))
                 tcurr))
     ;; if full-internal is true and empty is still true
     ;;   then  full-internal went high at least delta.min after empty went high
     ;;     and time-now is less than the max delay for empty
     (implies (and (sig-value->value empty)
                   (sig-value->value full-internal))
              (and (<= (+ (sig-value->time empty)
                          (interval->lo delta))
                       (sig-value->time full-internal))))
     ;; if empty, go-full, and full-internal are all true,
     ;;   then full-internal must have recently gone high, and the
     ;;   high value on go-full is the one that enabled full-internal to go high
     ;;   Therefore, full-internal went high at least delta.min after go-full.
     (implies (and (sig-value->value empty)
                   (sig-value->value go-full)
                   (sig-value->value full-internal))
              (and (>= (sig-value->time full-internal)
                       (+ (sig-value->time go-full)
                          (interval->lo delta)))
                   (< (sig-value->time full-internal) ;; should be <  ?
                      (+ (max (sig-value->time empty)
                              (sig-value->time go-full))
                         (interval->hi delta)))))
     ;; empty tracks not full-internal
     (implies (equal (sig-value->value empty)
                     (not (sig-value->value full-internal)))
              (and (<= (+ (sig-value->time full-internal)
                          (interval->lo delta))
                       (sig-value->time empty))
                   (< (sig-value->time empty) ;; should be < ?
                      (+ (sig-value->time full-internal)
                         (interval->hi delta)))))
     (implies (equal (sig-value->value empty)
                     (sig-value->value full-internal))
              (and (> (sig-value->time full-internal)
                      (sig-value->time empty))
                   (> (+ (sig-value->time full-internal)
                         (interval->hi delta))
                      tcurr)))
     ;; ----------------------------------------------------
     ;; the corresponding constraints for full, go-empty, and full-internal
     ;; if full-internal is excited to go false but hasn't yet,
     ;;   then time-now is less than the max delay for full-internal.
     (implies (and (sig-value->value full)
                   (sig-value->value go-empty)
                   (sig-value->value full-internal))
              (> (+ (max (sig-value->time full)
                         (sig-value->time go-empty))
                    (interval->hi delta))
                 tcurr))
     ;; if full-internal is false and full is still true
     ;;   then  full-internal went low at least delta.min after full went high
     ;;     and time-now is less than the max delay for full
     (implies (and (sig-value->value full)
                   (not (sig-value->value full-internal)))
              (and (<= (+ (sig-value->time full)
                          (interval->lo delta))
                       (sig-value->time full-internal))))
     ;; if full, go-empty, and not(full-internal) are all true,
     ;;   then full-internal must have recently gone high, and the
     ;;   high value on go-empty is the one that enabled full-internal to go high
     ;;   Therefore, full-internal went high at least delta.min after go-empty.
     (implies (and (sig-value->value full)
                   (sig-value->value go-empty)
                   (not (sig-value->value full-internal)))
              (and (>= (sig-value->time full-internal)
                       (+ (sig-value->time go-empty)
                          (interval->lo delta)))
                   (< (sig-value->time full-internal)
                      (+ (max (sig-value->time full)
                              (sig-value->time go-empty))
                         (interval->hi delta)))))
     ;; full tracks full-internal
     (implies (equal (sig-value->value full)
                     (sig-value->value full-internal))
              (and (<= (+ (sig-value->time full-internal)
                          (interval->lo delta))
                       (sig-value->time full))
                   (< (sig-value->time full)
                      (+ (sig-value->time full-internal)
                         (interval->hi delta)))))
     (implies (equal (sig-value->value full)
                     (not (sig-value->value full-internal)))
              (and (> (sig-value->time full-internal)
                      (sig-value->time full))
                   (> (+ (sig-value->time full-internal)
                         (interval->hi delta))
                      tcurr)))
     )))

(define invariant-lenv ((go-full sig-value-p)
                        (empty sig-value-p)
                        (left-internal sig-value-p)
                        (delta interval-p)
                        (tcurr rationalp))
  :returns (ok booleanp)
  (b* ((go-full (sig-value-fix go-full))
       (empty (sig-value-fix empty))
       (left-internal (sig-value-fix left-internal))
       (delta (interval-fix delta)))
    (and
     ;; ----------------------------------------------------
     ;; the corresponding constraints for go-full, empty, and left-internal
     ;; if left-internal is excited to go false but hasn't yet,
     ;;   then time-now is less than the max delay for left-internal.
     (implies (and (sig-value->value go-full)
                   (sig-value->value empty)
                   (sig-value->value left-internal))
              (> (+ (max (sig-value->time go-full)
                         (sig-value->time empty))
                    (interval->hi delta))
                 tcurr))
     ;; if left-internal is false and go-full is still true
     ;;   then  full-internal went low at least delta.min after go-full went high
     ;;     and time-now is less than the max delay for go-full
     (implies (and (sig-value->value go-full)
                   (not (sig-value->value left-internal)))
              (and (<= (+ (sig-value->time go-full)
                          (interval->lo delta))
                       (sig-value->time left-internal))))
     ;; if go-full, empty, and not(left-internal) are all true,
     ;;   then left-internal must have recently gone high, and the
     ;;   high value on empty is the one that enabled full-internal to go high
     ;;   Therefore, full-internal went high at least delta.min after empty.
     (implies (and (sig-value->value go-full)
                   (sig-value->value empty)
                   (not (sig-value->value left-internal)))
              (and (>= (sig-value->time left-internal)
                       (+ (sig-value->time empty)
                          (interval->lo delta)))
                   (< (sig-value->time left-internal)
                      (+ (max (sig-value->time go-full)
                              (sig-value->time empty))
                         (interval->hi delta)))))
     ;; go-full tracks left-internal
     (implies (equal (sig-value->value go-full)
                     (sig-value->value left-internal))
              (and (<= (+ (sig-value->time left-internal)
                          (interval->lo delta))
                       (sig-value->time go-full))
                   (< (sig-value->time go-full)
                      (+ (sig-value->time left-internal)
                         (interval->hi delta)))))
     (implies (equal (sig-value->value go-full)
                     (not (sig-value->value left-internal)))
              (and (> (sig-value->time left-internal)
                      (sig-value->time go-full))
                   (> (+ (sig-value->time left-internal)
                         (interval->hi delta))
                      tcurr)))))
  )

(define invariant-renv ((go-empty sig-value-p)
                        (full sig-value-p)
                        (right-internal sig-value-p)
                        (delta interval-p)
                        (tcurr rationalp))
  :returns (ok booleanp)
  (b* ((go-empty (sig-value-fix go-empty))
       (full (sig-value-fix full))
       (right-internal (sig-value-fix right-internal))
       (delta (interval-fix delta)))
    (and
     ;; ----------------------------------------------------
     ;; the corresponding constraints for go-empty, full, and right-internal
     ;; if right-internal is excited to go true but hasn't yet,
     ;;   then time-now is less than the max delay for left-internal.
     (implies (and (sig-value->value go-empty)
                   (sig-value->value full)
                   (not (sig-value->value right-internal)))
              (> (+ (max (sig-value->time go-empty)
                         (sig-value->time full))
                    (interval->hi delta))
                 tcurr))
     ;; if right-internal is true and is go-empty still true
     ;;   then right-internal went high at least delta.min after go-empty went high
     ;;     and time-now is less than the max delay for go-empty
     (implies (and (sig-value->value go-empty)
                   (sig-value->value right-internal))
              (and (<= (+ (sig-value->time go-empty)
                          (interval->lo delta))
                       (sig-value->time right-internal))))
     ;; if go-empty, full, and right-internal are all true,
     ;;   then left-internal must have recently gone high, and the
     ;;   high value on empty is the one that enabled full-internal to go high
     ;;   Therefore, full-internal went high at least delta.min after empty.
     (implies (and (sig-value->value go-empty)
                   (sig-value->value full)
                   (sig-value->value right-internal))
              (and (>= (sig-value->time right-internal)
                       (+ (sig-value->time full)
                          (interval->lo delta)))
                   (< (sig-value->time right-internal)
                      (+ (max (sig-value->time go-empty)
                              (sig-value->time full))
                         (interval->hi delta)))))
     ;; go-empty tracks not(right-internal)
     (implies (equal (sig-value->value go-empty)
                     (not (sig-value->value right-internal)))
              (and (<= (+ (sig-value->time right-internal)
                          (interval->lo delta))
                       (sig-value->time go-empty))
                   (< (sig-value->time go-empty)
                      (+ (sig-value->time right-internal)
                         (interval->hi delta)))))
     (implies (equal (sig-value->value go-empty)
                     (sig-value->value right-internal))
              (and (> (sig-value->time right-internal)
                      (sig-value->time go-empty))
                   (> (+ (sig-value->time right-internal)
                         (interval->hi delta))
                      tcurr)))))
  )

;; ----------------------------------------------------------

(define interval-add ((itv1 interval-p) (itv2 interval-p))
  :returns (itv interval-p)
  (b* ((itv1 (interval-fix itv1))
       (itv2 (interval-fix itv2)))
    (make-interval :lo (+ (interval->lo itv1)
                          (interval->lo itv2))
                   :hi (+ (interval->hi itv1)
                          (interval->hi itv2)))))

(define interval-max ((itv1 interval-p) (itv2 interval-p))
  :returns (imax interval-p)
  (b* ((itv1 (interval-fix itv1))
       (itv2 (interval-fix itv2)))
    (make-interval :lo (max (interval->lo itv1)
                            (interval->lo itv2))
                   :hi (max (interval->hi itv1)
                            (interval->hi itv2)))))

(define full-internal-next-nil ((go-full sig-value-p)
                                (go-empty sig-value-p)
                                (full sig-value-p)
                                (empty sig-value-p)
                                (full-internal sig-value-p)
                                (left-internal sig-value-p)
                                (right-internal sig-value-p)
                                (delta interval-p)
                                (inf rationalp))
  :returns (bounds interval-p)
  (b* (;; fixing types
       (go-full (sig-value-fix go-full))
       (go-empty (sig-value-fix go-empty))
       (full (sig-value-fix full))
       (empty (sig-value-fix empty))
       (full-internal (sig-value-fix full-internal))
       (left-internal (sig-value-fix left-internal))
       (right-internal (sig-value-fix right-internal))
       (delta (interval-fix delta))
       ;; real logical constraints
       ;; ge-time: time for go-empty when it is (next or currently) true
       (ge-time (cond ((and (not (sig-value->value right-internal))
                            (sig-value->value go-empty))
                       (make-interval :lo (sig-value->time go-empty)
                                      :hi (sig-value->time go-empty)))
                      ((not (sig-value->value right-internal))
                       (interval-add (make-interval
                                      :lo (sig-value->time right-internal)
                                      :hi (sig-value->time right-internal))
                                     delta))
                      (t ;;right-internal.value
                       (make-interval :lo (+ (sig-value->time right-internal)
                                             (* 3 (interval->lo delta)))
                                      :hi (+ (sig-value->time right-internal)
                                             inf)))))
       ;; easy case -- just need to figure out when full-internal drops
       ((if (sig-value->value full-internal))
        ;; figure out bounds for full and go-empty.  Then, get the bound for full-internal
        (b* ((full-time (if (sig-value->value full)
                            (make-interval :lo (sig-value->time full)
                                           :hi (sig-value->time full))
                          (interval-add (make-interval :lo (sig-value->time full-internal)
                                                       :hi (sig-value->time full-internal))
                                        delta))))
          (interval-add (interval-max full-time ge-time) delta)))
       ;; hard case -- need to figure out when full-internal goes high so we
       ;; can then figure out when it drops again
       (empty-time (if (sig-value->value empty)
                       (make-interval :lo (sig-value->time empty)
                                      :hi (sig-value->time empty))
                     (interval-add (make-interval :lo (sig-value->time full-internal)
                                                  :hi (sig-value->time full-internal))
                                   delta)))
       (gf-time
        (cond ((sig-value->value go-full)
               (make-interval :lo (sig-value->time go-full)
                              :hi (sig-value->time go-full)))
              ((sig-value->value left-internal)
               (interval-add
                (make-interval :lo (sig-value->time left-internal)
                               :hi (sig-value->time left-internal))
                delta))
              (t ;;(not left-internal.value)
               (make-interval :lo (+ (sig-value->time left-internal)
                                     (* 3 (interval->lo delta)))
                              :hi (+ (sig-value->time left-internal) inf)))))
       ;; fi-t-time time bouds for next transition of full-internal to t
       (fi-t-time (interval-add (interval-max empty-time gf-time) delta))
       ;; now figure out bounds for full-internal going back to nil
       ;; full goes to t to enable full-internal going to nil
       (full-time (interval-add fi-t-time delta)))
    (interval-add (interval-max full-time ge-time) delta))
  )

(define full-internal-next-t ((go-full sig-value-p)
                              (go-empty sig-value-p)
                              (full sig-value-p)
                              (empty sig-value-p)
                              (full-internal sig-value-p)
                              (left-internal sig-value-p)
                              (right-internal sig-value-p)
                              (delta interval-p)
                              (inf rationalp))
  :returns (bounds interval-p)
  (b* (;; fixing types
       (go-full (sig-value-fix go-full))
       (go-empty (sig-value-fix go-empty))
       (full (sig-value-fix full))
       (empty (sig-value-fix empty))
       (full-internal (sig-value-fix full-internal))
       (left-internal (sig-value-fix left-internal))
       (right-internal (sig-value-fix right-internal))
       (delta (interval-fix delta))
       ;; real logical constraints
       ;; gf-time: time for go-full when it is (next or currently) true
       (gf-time (cond ((and (sig-value->value left-internal)
                            (sig-value->value go-full))
                       (make-interval :lo (sig-value->time go-full)
                                      :hi (sig-value->time go-full)))
                      ((sig-value->value left-internal)
                       (interval-add (make-interval
                                      :lo (sig-value->time left-internal)
                                      :hi (sig-value->time left-internal))
                                     delta))
                      (t ;;(not left-internal.value)
                       (make-interval :lo (+ (sig-value->time left-internal)
                                             (* 3 (interval->lo delta)))
                                      :hi (+ (sig-value->time left-internal)
                                             inf)))))
       ;; easy case -- just need to figure out when full-internal goes high
       ((if (not (sig-value->value full-internal)))
        ;; figure out bounds for empty and go-full.  Then, get the bound for full-internal
        (b* ((empty-time (if (sig-value->value empty)
                             (make-interval :lo (sig-value->time empty)
                                            :hi (sig-value->time empty))
                           (interval-add (make-interval :lo (sig-value->time full-internal)
                                                        :hi (sig-value->time full-internal))
                                         delta))))
          (interval-add (interval-max empty-time gf-time) delta)))
       ;; hard case -- need to figure out when full-internal goes low so we
       ;; can then figure out when it goes high again
       (full-time (if (sig-value->value full)
                      (make-interval :lo (sig-value->time full)
                                     :hi (sig-value->time full))
                    (interval-add (make-interval :lo (sig-value->time full-internal)
                                                 :hi (sig-value->time full-internal))
                                  delta)))
       (ge-time
        (cond ((sig-value->value go-empty)
               (make-interval :lo (sig-value->time go-empty)
                              :hi (sig-value->time go-empty)))
              ((not (sig-value->value right-internal))
               (interval-add
                (make-interval :lo (sig-value->time right-internal)
                               :hi (sig-value->time right-internal))
                delta))
              (t ;; right-internal.value
               (make-interval :lo (+ (sig-value->time right-internal)
                                     (* 3 (interval->lo delta)))
                              :hi (+ (sig-value->time right-internal) inf)))))
       ;; fi-nil-time time bounds for next transition of full-internal to nil
       (fi-nil-time (interval-add (interval-max full-time ge-time) delta))
       ;; now figure out bounds for full-internal going back to nil
       ;; empty goes to t to enable full-internal going to t
       (empty-time (interval-add fi-nil-time delta)))
    (interval-add (interval-max empty-time gf-time) delta))
  )

(define empty-next ((target booleanp)
                    (go-full sig-value-p)
                    (go-empty sig-value-p)
                    (full sig-value-p)
                    (empty sig-value-p)
                    (full-internal sig-value-p)
                    (left-internal sig-value-p)
                    (right-internal sig-value-p)
                    (delta interval-p)
                    (inf rationalp))
  :returns (bounds interval-p)
  (b* (;; fixing types
       (go-full (sig-value-fix go-full))
       (go-empty (sig-value-fix go-empty))
       (full (sig-value-fix full))
       (empty (sig-value-fix empty))
       (full-internal (sig-value-fix full-internal))
       (left-internal (sig-value-fix left-internal))
       (right-internal (sig-value-fix right-internal))
       (delta (interval-fix delta)))
    ;; the real logical constraints
    (interval-add
     (if (and (not (equal (sig-value->value empty) target))
              (not (equal (sig-value->value full-internal) target)))
         (make-interval :lo (sig-value->time full-internal)
                        :hi (sig-value->time full-internal))
       (if target
           (full-internal-next-nil go-full go-empty full empty full-internal
                                   left-internal right-internal delta inf)
         (full-internal-next-t go-full go-empty full empty full-internal
                               left-internal right-internal delta inf)))
     delta)))

(define full-next ((target booleanp)
                   (go-full sig-value-p)
                   (go-empty sig-value-p)
                   (full sig-value-p)
                   (empty sig-value-p)
                   (full-internal sig-value-p)
                   (left-internal sig-value-p)
                   (right-internal sig-value-p)
                   (delta interval-p)
                   (inf rationalp))
  :returns (bounds interval-p)
  (b* (;; fixing types
       (go-full (sig-value-fix go-full))
       (go-empty (sig-value-fix go-empty))
       (full (sig-value-fix full))
       (empty (sig-value-fix empty))
       (full-internal (sig-value-fix full-internal))
       (left-internal (sig-value-fix left-internal))
       (right-internal (sig-value-fix right-internal))
       (delta (interval-fix delta)))
    ;; the real logical constraints
    (interval-add
     (if (and (not (equal (sig-value->value full) target))
              (equal (sig-value->value full-internal) target))
         (make-interval :lo (sig-value->time full-internal)
                        :hi (sig-value->time full-internal))
       (if target
           (full-internal-next-t go-full go-empty full empty full-internal
                                   left-internal right-internal delta inf)
         (full-internal-next-nil go-full go-empty full empty full-internal
                               left-internal right-internal delta inf)))
     delta)))

(define left-internal-next-nil ((go-full sig-value-p)
                                (empty sig-value-p)
                                (full-internal sig-value-p)
                                (left-internal sig-value-p)
                                (delta interval-p)
                                (inf rationalp))
  :returns (bounds interval-p)
  (b* (;; fixing types
       (go-full (sig-value-fix go-full))
       (empty (sig-value-fix empty))
       (full-internal (sig-value-fix full-internal))
       (left-internal (sig-value-fix left-internal))
       (delta (interval-fix delta))
       ;; real logical constraints
       ;; empty: time for empty when it is (next or currently) true
       (empty-time (cond ((and (not (sig-value->value full-internal))
                               (sig-value->value empty))
                          (make-interval :lo (sig-value->time empty)
                                         :hi (sig-value->time empty)))
                         ((not (sig-value->value full-internal))
                          (interval-add (make-interval
                                         :lo (sig-value->time full-internal)
                                         :hi (sig-value->time full-internal))
                                        delta))
                         (t ;;full-internal.value
                          (make-interval :lo (+ (sig-value->time full-internal)
                                                (* 3 (interval->lo delta)))
                                         :hi (+ (sig-value->time full-internal)
                                                inf)))))
       ;; easy case -- just need to figure out when left-internal drops
       ((if (sig-value->value left-internal))
        ;; figure out bounds for empty and go-full.  Then, get the bound for left-internal
        (b* ((gf-time (if (sig-value->value go-full)
                          (make-interval :lo (sig-value->time go-full)
                                         :hi (sig-value->time go-full))
                        (interval-add (make-interval :lo (sig-value->time left-internal)
                                                     :hi (sig-value->time left-internal))
                                      delta))))
          (interval-add (interval-max empty-time gf-time) delta)))
       ;; hard case -- need to figure out when left-internal goes high so we
       ;; can then figure out when it drops again
       ;; li-t-time time bounds for next transition of left-internal to t
       (li-t-time (interval-add (make-interval :lo (sig-value->time left-internal)
                                               :hi (sig-value->time left-internal))
                                (make-interval :lo (* 2 (interval->lo delta))
                                               :hi inf)))
       ;; now figure out bounds for left-internal going back to nil
       ;; go-full goes to t to enable left-internal going to nil
       (gf-time (interval-add li-t-time delta)))
    (interval-add (interval-max gf-time empty-time) delta))
  )


(define left-internal-next-t ((go-full sig-value-p)
                              (empty sig-value-p)
                              (full-internal sig-value-p)
                              (left-internal sig-value-p)
                              (delta interval-p)
                              (inf rationalp))
  :returns (bounds interval-p)
  (b* (;; fixing types
       (go-full (sig-value-fix go-full))
       (empty (sig-value-fix empty))
       (full-internal (sig-value-fix full-internal))
       (left-internal (sig-value-fix left-internal))
       (delta (interval-fix delta))
       ;; real logical constraints
       ;; easy case -- just need to figure out when left-internal rises
       ((if (not (sig-value->value left-internal)))
        ;; left-internal should go high after 2 delta
        (interval-add (make-interval :lo (sig-value->time left-internal)
                                     :hi (sig-value->time left-internal))
                      (make-interval :lo (* 2 (interval->lo delta))
                                     :hi inf)))
       ;; hard case -- need to figure out when full-internal goes low so we
       ;; can then figure out when it goes high again
       (gf-time (if (sig-value->value go-full)
                    (make-interval :lo (sig-value->time go-full)
                                   :hi (sig-value->time go-full))
                  (interval-add (make-interval :lo (sig-value->time left-internal)
                                               :hi (sig-value->time left-internal))
                                delta)))
       ;; empty: time for empty when it is (next or currently) true
       (empty-time (cond ((and (not (sig-value->value full-internal))
                               (sig-value->value empty))
                          (make-interval :lo (sig-value->time empty)
                                         :hi (sig-value->time empty)))
                         ((not (sig-value->value full-internal))
                          (interval-add (make-interval
                                         :lo (sig-value->time full-internal)
                                         :hi (sig-value->time full-internal))
                                        delta))
                         (t ;;full-internal.value
                          (make-interval :lo (+ (sig-value->time full-internal)
                                                (* 3 (interval->lo delta)))
                                         :hi (+ (sig-value->time full-internal)
                                                inf)))))
       ;; li-nil-time time bounds for next transition of left-internal to nil
       (li-nil-time (interval-add (interval-max gf-time empty-time) delta)))
    ;; now figure out bounds for left-internal going back to t
    (interval-add li-nil-time (make-interval :lo (* 2 (interval->lo delta))
                                             :hi inf)))
  )

(define go-full-next ((target booleanp)
                      (go-full sig-value-p)
                      (empty sig-value-p)
                      (full-internal sig-value-p)
                      (left-internal sig-value-p)
                      (delta interval-p)
                      (inf rationalp))
  :returns (bounds interval-p)
  (b* (;; fixing types
       (go-full (sig-value-fix go-full))
       (empty (sig-value-fix empty))
       (full-internal (sig-value-fix full-internal))
       (left-internal (sig-value-fix left-internal))
       (delta (interval-fix delta)))
    ;; the real logical constraints
    (interval-add
     (if (and (not (equal (sig-value->value go-full) target))
              (equal (sig-value->value left-internal) target))
         (make-interval :lo (sig-value->time left-internal)
                        :hi (sig-value->time left-internal))
       (if target
           (left-internal-next-t go-full empty full-internal
                                   left-internal delta inf)
         (left-internal-next-nil go-full empty full-internal
                               left-internal delta inf)))
     delta)))

(define right-internal-next-t ((go-empty sig-value-p)
                               (full sig-value-p)
                               (full-internal sig-value-p)
                               (right-internal sig-value-p)
                               (delta interval-p)
                               (inf rationalp))
  :returns (bounds interval-p)
  (b* (;; fixing types
       (go-empty (sig-value-fix go-empty))
       (full (sig-value-fix full))
       (full-internal (sig-value-fix full-internal))
       (right-internal (sig-value-fix right-internal))
       (delta (interval-fix delta))
       ;; real logical constraints
       ;; full-time: time for full when it is (next or currently) true
       (full-time (cond ((and (sig-value->value full-internal)
                              (sig-value->value full))
                         (make-interval :lo (sig-value->time full)
                                        :hi (sig-value->time full)))
                        ((sig-value->value full-internal)
                         (interval-add (make-interval
                                        :lo (sig-value->time full-internal)
                                        :hi (sig-value->time full-internal))
                                       delta))
                        (t ;;(not full-internal.value)
                         (make-interval :lo (+ (sig-value->time full-internal)
                                               (* 3 (interval->lo delta)))
                                        :hi (+ (sig-value->time full-internal)
                                               inf)))))
       ;; easy case -- just need to figure out when right-internal goes high
       ((if (not (sig-value->value right-internal)))
        ;; figure out bounds for full and go-empty.  Then, get the bound for right-internal
        (b* ((ge-time (if (sig-value->value go-empty)
                          (make-interval :lo (sig-value->time go-empty)
                                         :hi (sig-value->time go-empty))
                        (interval-add (make-interval :lo (sig-value->time right-internal)
                                                     :hi (sig-value->time right-internal))
                                      delta))))
          (interval-add (interval-max full-time ge-time) delta)))
       ;; hard case -- need to figure out when right-internal goes low so we
       ;; can then figure out when it goes high again
       ;; ri-nil-time time bounds for next transition of right-internal to nil
       (ri-nil-time (interval-add (make-interval :lo (sig-value->time right-internal)
                                                 :hi (sig-value->time right-internal))
                                  (make-interval :lo (* 2 (interval->lo delta))
                                                 :hi inf)))
       ;; now figure out bounds for right-internal going back to t
       ;; go-empty goes to t to enable right-internal going to t
       (ge-time (interval-add ri-nil-time delta)))
    (interval-add (interval-max full-time ge-time) delta))
  )

(define right-internal-next-nil ((go-empty sig-value-p)
                                 (full sig-value-p)
                                 (full-internal sig-value-p)
                                 (right-internal sig-value-p)
                                 (delta interval-p)
                                 (inf rationalp))
  :returns (bounds interval-p)
  (b* (;; fixing types
       (go-empty (sig-value-fix go-empty))
       (full (sig-value-fix full))
       (full-internal (sig-value-fix full-internal))
       (right-internal (sig-value-fix right-internal))
       (delta (interval-fix delta))
       ;; real logical constraints
       ;; easy case -- just need to figure out when right-internal falls
       ((if (sig-value->value right-internal))
        ;; right-internal should go low after 2 delta
        (interval-add (make-interval :lo (sig-value->time right-internal)
                                     :hi (sig-value->time right-internal))
                      (make-interval :lo (* 2 (interval->lo delta))
                                     :hi inf)))
       ;; hard case -- need to figure out when right-internal goes high so we
       ;; can then figure out when it goes low again
       (ge-time (if (sig-value->value go-empty)
                    (make-interval :lo (sig-value->time go-empty)
                                   :hi (sig-value->time go-empty))
                  (interval-add (make-interval :lo (sig-value->time right-internal)
                                               :hi (sig-value->time right-internal))
                                delta)))
       ;; full: time for full when it is (next or currently) true
       (full-time (cond ((and (sig-value->value full-internal)
                              (sig-value->value full))
                         (make-interval :lo (sig-value->time full)
                                        :hi (sig-value->time full)))
                        ((sig-value->value full-internal)
                         (interval-add (make-interval
                                        :lo (sig-value->time full-internal)
                                        :hi (sig-value->time full-internal))
                                       delta))
                        (t ;;(not full-internal.value)
                         (make-interval :lo (+ (sig-value->time full-internal)
                                               (* 3 (interval->lo delta)))
                                        :hi (+ (sig-value->time full-internal)
                                               inf)))))
       ;; ri-t-time time bounds for next transition of right-internal to high
       (ri-t-time (interval-add (interval-max ge-time full-time) delta)))
    ;; now figure out bounds for right-internal going back to t
    (interval-add ri-t-time (make-interval :lo (* 2 (interval->lo delta))
                                           :hi inf)))
  )

(define go-empty-next ((target booleanp)
                       (go-empty sig-value-p)
                       (full sig-value-p)
                       (full-internal sig-value-p)
                       (right-internal sig-value-p)
                       (delta interval-p)
                       (inf rationalp))
  :returns (bounds interval-p)
  (b* (;; fixing types
       (go-empty (sig-value-fix go-empty))
       (full (sig-value-fix full))
       (full-internal (sig-value-fix full-internal))
       (right-internal (sig-value-fix right-internal))
       (delta (interval-fix delta)))
    ;; the real logical constraints
    (interval-add
     (if (and (not (equal (sig-value->value go-empty) target))
              (not (equal (sig-value->value right-internal) target)))
         (make-interval :lo (sig-value->time right-internal)
                        :hi (sig-value->time right-internal))
       (if target
           (right-internal-next-nil go-empty full full-internal
                                    right-internal delta inf)
         (right-internal-next-t go-empty full full-internal
                                right-internal delta inf)))
     delta)))

;; ------------------------------------------------------------------------------

;; starting from start of (and empty gf)
;; 1. last(li_down, fi_up) < first(empty_down, gf_down)
;; 2. last(empty_down, gf_down) < first(empty_up, gf_up)
(define interact-lenv ((go-full sig-value-p)
                       (go-empty sig-value-p)
                       (full sig-value-p)
                       (empty sig-value-p)
                       (full-internal sig-value-p)
                       (left-internal sig-value-p)
                       (right-internal sig-value-p)
                       (delta interval-p)
                       (inf rationalp))
  :returns (ok booleanp)
  (b* ((go-empty (sig-value-fix go-empty))
       (go-full (sig-value-fix go-full))
       (empty (sig-value-fix empty))
       (full (sig-value-fix full))
       (full-internal (sig-value-fix full-internal))
       (left-internal (sig-value-fix left-internal))
       (right-internal (sig-value-fix right-internal))
       (delta (interval-fix delta))
       ;; logical constraints
       (li_down (left-internal-next-nil go-full empty full-internal
                                        left-internal delta inf))
       (fi_up (full-internal-next-t go-full go-empty full empty full-internal
                                    left-internal right-internal delta inf))
       (empty_down (empty-next nil go-full go-empty full empty
                               full-internal left-internal right-internal
                               delta inf))
       (gf_down (go-full-next nil go-full empty full-internal
                              left-internal delta inf))
       (empty_up (empty-next t go-full go-empty full empty
                             full-internal left-internal right-internal
                             delta inf))
       (gf_up (go-full-next t go-full empty full-internal
                            left-internal delta inf))
       ((if (and (sig-value->value empty)
                 (sig-value->value go-full)))
        (and (< (max (interval->hi li_down)
                     (interval->hi fi_up))
                (min (interval->lo empty_down)
                     (interval->lo gf_down)))
             (< (max (interval->hi empty_down)
                     (interval->hi gf_down))
                (min (interval->lo empty_up)
                     (interval->lo gf_up))))))
    t)
  )

;; starting from start of (and full ge)
;; 1. last(fi_down, ri_up) < first(full_down, ge_down)
;; 2. last(full_down, ge_down) < first(full_up, ge_up)
(define interact-renv ((go-full sig-value-p)
                       (go-empty sig-value-p)
                       (full sig-value-p)
                       (empty sig-value-p)
                       (full-internal sig-value-p)
                       (left-internal sig-value-p)
                       (right-internal sig-value-p)
                       (delta interval-p)
                       (inf rationalp))
  :returns (ok booleanp)
  (b* ((go-empty (sig-value-fix go-empty))
       (go-full (sig-value-fix go-full))
       (empty (sig-value-fix empty))
       (full (sig-value-fix full))
       (full-internal (sig-value-fix full-internal))
       (left-internal (sig-value-fix left-internal))
       (right-internal (sig-value-fix right-internal))
       (delta (interval-fix delta))
       ;; logical constraints
       (fi_down (full-internal-next-nil go-full go-empty full empty full-internal
                                        left-internal right-internal delta
                                        inf))
       (ri_up (right-internal-next-t go-empty full full-internal
                                     right-internal delta inf))
       (full_down (full-next nil go-full go-empty full empty full-internal
                             left-internal right-internal delta inf))
       (ge_down (go-empty-next nil go-empty full full-internal right-internal
                               delta inf))
       (full_up (full-next t go-full go-empty full empty full-internal
                           left-internal right-internal delta inf))
       (ge_up (go-empty-next t go-empty full full-internal right-internal
                             delta inf))
       ((if (and (sig-value->value full)
                 (sig-value->value go-empty)))
        (and (< (max (interval->hi fi_down)
                     (interval->hi ri_up))
                (min (interval->lo full_down)
                     (interval->lo ge_down)))
             (< (max (interval->hi full_down)
                     (interval->hi ge_down))
                (min (interval->lo full_up)
                     (interval->lo ge_up))))))
    t)
  )

;; ------------------------------------------------------------------------------

(define invariant ((a asp-stage-p) (el lenv-p) (er renv-p)
                   (tcurr rationalp) (curr gstate-p)
                   (inf rationalp))
  :returns (ok booleanp)
  :guard-hints (("Goal" :in-theory (enable sigs-in-bool-table asp-sigs
                                           lenv-sigs renv-sigs)))
  (b* ((a (asp-stage-fix a))
       (el (lenv-fix el))
       (er (renv-fix er))
       (curr (gstate-fix curr))
       ((unless (sigs-in-bool-table (asp-sigs a) curr)) nil)
       ((unless (sigs-in-bool-table (lenv-sigs el) curr)) nil)
       ((unless (sigs-in-bool-table (renv-sigs er) curr)) nil)
       (go-empty-sig (asp-stage->go-empty a))
       (go-full-sig (asp-stage->go-full a))
       (empty-sig (asp-stage->empty a))
       (full-sig (asp-stage->full a))
       (full-internal-sig (asp-stage->full-internal a))
       (left-internal-sig (lenv->left-internal el))
       (right-internal-sig (renv->right-internal er))
       (delta (asp-stage->delta a))
       (go-empty (cdr (smt::magic-fix
                       'sig-path_sig-value
                       (assoc-equal go-empty-sig (gstate-fix curr)))))
       (go-full (cdr (smt::magic-fix
                      'sig-path_sig-value
                      (assoc-equal go-full-sig (gstate-fix curr)))))
       (empty (cdr (smt::magic-fix
                    'sig-path_sig-value
                    (assoc-equal empty-sig (gstate-fix curr)))))
       (full (cdr (smt::magic-fix
                   'sig-path_sig-value
                   (assoc-equal full-sig (gstate-fix curr)))))
       (full-internal (cdr (smt::magic-fix
                            'sig-path_sig-value
                            (assoc-equal full-internal-sig
                                         (gstate-fix curr)))))
       (left-internal (cdr (smt::magic-fix
                            'sig-path_sig-value
                            (assoc-equal left-internal-sig
                                         (gstate-fix curr)))))
       (right-internal (cdr (smt::magic-fix
                             'sig-path_sig-value
                             (assoc-equal right-internal-sig
                                          (gstate-fix curr))))))
  (and (invariant-stage go-full go-empty full empty full-internal delta tcurr)
       (invariant-lenv go-full empty left-internal delta tcurr)
       (invariant-renv go-empty full right-internal delta tcurr)
       (interact-lenv go-full go-empty full empty full-internal left-internal
                      right-internal delta inf)
       (interact-renv go-full go-empty full empty full-internal left-internal
                      right-internal delta inf))))

(define invariant-trace ((a asp-stage-p) (el lenv-p)
                         (er renv-p) (tr gtrace-p)
                         (inf rationalp))
  :returns (ok booleanp)
  :measure (len tr)
  (b* ((tr (gtrace-fix tr))
       ((unless (consp (gtrace-fix (cdr (gtrace-fix tr))))) t)
       (first (car (gtrace-fix tr)))
       (rest (cdr (gtrace-fix tr))))
    (and (invariant a el er (gstate-t->statet first) (gstate-t->statev first) inf)
         (invariant-trace a el er rest inf))))

(std::must-fail
(defthm invariant-check-contradiction
  (not (and (asp-stage-p a)
            (lenv-p el)
            (renv-p er)
            (asp-connection a el er)
            (gtrace-p tr)
            (lenv-valid el tr)
            (renv-valid er tr)
            (asp-valid a tr)
            (valid-interval (asp-stage->delta a))
            (valid-interval (lenv->delta el))
            (valid-interval (renv->delta er))
            (equal (interval->lo (asp-stage->delta a))
                   8)
            (equal (interval->hi (asp-stage->delta a))
                   10)
            (equal (interval->lo (asp-stage->delta a))
                   (interval->lo (lenv->delta el)))
            (equal (interval->hi (asp-stage->delta a))
                   (interval->hi (lenv->delta el)))
            (equal (interval->lo (asp-stage->delta a))
                   (interval->lo (renv->delta er)))
            (equal (interval->hi (asp-stage->delta a))
                   (interval->hi (renv->delta er)))
            (consp (gtrace-fix tr))
            (invariant a el er
                       (gstate-t->statet (car (gtrace-fix tr)))
                       (gstate-t->statev (car (gtrace-fix tr)))
                       1000))) ;; inf can be any value
  :hints (("Goal"
           :smtlink
           (:fty (asp-stage lenv renv interval gtrace sig-value gstate gstate-t
                            sig-path-list sig-path sig maybe-integer
                            maybe-rational target-tuple)
                 :functions ((sigs-in-bool-table :formals ((sigs sig-path-listp)
                                                           (st gstate-p))
                                                 :returns ((ok booleanp))
                                                 :level 5)
                             (sigs-in-bool-trace :formals ((sigs sig-path-listp)
                                                           (tr gstate-p))
                                                 :returns ((ok booleanp))
                                                 :level 2)
                             (lenv-valid :formals ((e lenv-p)
                                                   (tr gtrace-p))
                                         :returns ((ok booleanp))
                                         :level 1)
                             (renv-valid :formals ((e renv-p)
                                                   (tr gtrace-p))
                                         :returns ((ok booleanp))
                                         :level 1)
                             (asp-valid :formals ((a asp-stage-p)
                                                  (tr gtrace-p))
                                        :returns ((ok booleanp))
                                        :level 1)
                             )
                 ))))
)

(defthm invariant-thm
  (implies (and (asp-stage-p a)
                (lenv-p el)
                (renv-p er)
                (asp-connection a el er)
                (gtrace-p tr)
                (lenv-valid el tr)
                (renv-valid er tr)
                (asp-valid a tr)
                (valid-interval (asp-stage->delta a))
                (valid-interval (lenv->delta el))
                (valid-interval (renv->delta er))
                (equal (interval->lo (asp-stage->delta a))
                       8)
                (equal (interval->hi (asp-stage->delta a))
                       10)
                (equal (gstate-t->statet (car (gtrace-fix tr))) 8)
                (equal (interval->lo (asp-stage->delta a))
                       (interval->lo (lenv->delta el)))
                (equal (interval->hi (asp-stage->delta a))
                       (interval->hi (lenv->delta el)))
                (equal (interval->lo (asp-stage->delta a))
                       (interval->lo (renv->delta er)))
                (equal (interval->hi (asp-stage->delta a))
                       (interval->hi (renv->delta er)))
                (consp (gtrace-fix tr))
                (consp (gtrace-fix (cdr (gtrace-fix tr))))
                (invariant a el er
                           (gstate-t->statet (car (gtrace-fix tr)))
                           (gstate-t->statev (car (gtrace-fix tr)))
                           1000))
           (invariant a el er
                      (gstate-t->statet (car (gtrace-fix (cdr (gtrace-fix tr)))))
                      (gstate-t->statev (car (gtrace-fix (cdr (gtrace-fix
                                                               tr)))))
                      1000))
  :hints (("Goal"
           :smtlink
           (:fty (asp-stage lenv renv interval gtrace sig-value gstate gstate-t
                            sig-path-list sig-path sig maybe-integer
                            maybe-rational target-tuple)
                 :functions ((sigs-in-bool-table :formals ((sigs sig-path-listp)
                                                           (st gstate-p))
                                                 :returns ((ok booleanp))
                                                 :level 5)
                             (sigs-in-bool-trace :formals ((sigs sig-path-listp)
                                                           (tr gstate-p))
                                                 :returns ((ok booleanp))
                                                 :level 2)
                             (lenv-valid :formals ((e lenv-p)
                                                   (tr gtrace-p))
                                         :returns ((ok booleanp))
                                         :level 1)
                             (renv-valid :formals ((e renv-p)
                                                   (tr gtrace-p))
                                         :returns ((ok booleanp))
                                         :level 1)
                             (asp-valid :formals ((a asp-stage-p)
                                                  (tr gtrace-p))
                                        :returns ((ok booleanp))
                                        :level 1)
                             (tag-b :formals ((b booleanp)
                                              (n integerp))
                                    :returns ((res booleanp))
                                    :level 1)
                             )
                 ))))
