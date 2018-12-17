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
;;       need an fty compatible integer-list
(deflist integer-list
  :elt-type integerp
  :true-listp t)

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


(defthm sig-value-p--when--in-bool-table
  (implies (and (gstate-p st) (consp (assoc-equal foo st)))
           (sig-value-p (cdr (assoc-equal foo st)))))


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


;; =====================================================
;; some handy functions for signals
(deflist sig-value-list
  :elt-type sig-value-p
  :true-listp t)

(defprod sig-target
  ((value booleanp)
   (time interval-p)))

(define sig-target-from-signal ((sig sig-value-p))
  :returns (target sig-target-p)
  (make-sig-target :value (sig-value->value sig)
                   :time  (make-interval :lo (sig-value->time sig)
                                         :hi (sig-value->time sig))))

(define sig-and-fun ((sigs sig-value-list-p))
  :returns (v booleanp)
  :measure (len sigs)
  (b* ((sigs (sig-value-list-fix sigs))
       ((unless (consp (sig-value-list-fix sigs))) t)
       ((cons hd tl) (sig-value-list-fix sigs))
       ((unless (sig-value->value hd)) nil))
    (sig-and-fun tl)))

(defmacro sig-and (&rest rst)
  `(sig-and-fun (list ,@rst)))

(define sig-max-time-help ((sigs sig-value-list-p) (currmax rationalp))
  :returns (v rationalp :hyp :guard)
  :measure (len sigs)
  (b* ((sigs (sig-value-list-fix sigs))
       ((unless (consp (sig-value-list-fix sigs))) currmax)
       ((cons hd tl) (sig-value-list-fix sigs))
       (hd-time (sig-value->time hd))
       (newmax (if (< currmax hd-time) hd-time currmax)))
    (sig-max-time-help tl newmax)))

(define sig-max-time-fun ((sigs sig-value-list-p) (currmax rationalp))
  :returns (v interval-p)
  (b* ((u (sig-max-time-help sigs currmax)))
    (make-interval :lo u :hi u)))

(defmacro sig-max-time (sig0 &rest rst)
  `(sig-max-time-fun (list ,@rst) (sig-value->time ,sig0)))

(define sig-check-times ((prev sig-value-p)
                         (next sig-value-p)
                         (tprev rationalp)
                         (tnext rationalp))
  (b* ((prev (sig-value-fix prev))
       (next (sig-value-fix next))
       ((unless (<= tprev tnext)) nil)
       ((unless (<= 0 (sig-value->time prev))) nil)
       ((unless (<= (sig-value->time prev) (sig-value->time next))) nil)
       ((unless (<= (sig-value->time prev) tprev)) nil)
       ((unless (<= (sig-value->time next) tnext)) nil)
       ((unless (implies (equal (sig-value->value prev) (sig-value->value next))
                         (equal next prev)))
        nil))
    t))

(define sig-check-transition ((prev sig-value-p)
                              (next sig-value-p)
                              (target sig-target-p)
                              (tprev rationalp)
                              (tnext rationalp))
  :returns (ok booleanp)
  (b* ((prev (sig-value-fix prev))
       (next (sig-value-fix next))
       (target (sig-target-fix target))
       ((unless (sig-check-times prev next tprev tnext)) nil)
       ((unless (implies (not (equal (sig-value->value prev)
                                     (sig-value->value next)))
                         (and (equal (sig-value->value next)
                                     (sig-target->value target))
                              (equal (sig-value->time next) tnext)
                              (<= (interval->lo (sig-target->time target)) tnext))))
        nil)
       ((unless (implies (not (equal (sig-value->value next)
                                     (sig-target->value target)))
                         (< tnext (interval->hi (sig-target->time target)))))
        nil))
    t))

(defmacro state-get (sig st)
  `(cdr (smt::magic-fix
         'sig-path_sig-value
         (assoc-equal ,sig (gstate-fix ,st)))))

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
                   (prev gstate-t-p)
                   (next gstate-t-p))
  :returns (ok booleanp)
  ;; Need a theorem that says if sigs-in-bool-table, then assoc-equal is not nil
  :guard-hints (("Goal" :in-theory (e/d (sigs-in-bool-table lenv-sigs))))
  (b* ((e (lenv-fix e))
       ((gstate-t prev) (gstate-t-fix prev))
       ((gstate-t next) (gstate-t-fix next))
       ((unless (sigs-in-bool-table (lenv-sigs e) prev.statev)) nil)
       ((unless (sigs-in-bool-table (lenv-sigs e) next.statev)) nil)
       (empty (lenv->empty e))
       (gf (lenv->go-full e))
       (li (lenv->left-internal e))
       (delta (lenv->delta e))
       (empty-prev (state-get empty prev.statev))
       (empty-next (state-get empty next.statev))
       (gf-prev (state-get gf prev.statev))
       (gf-next (state-get gf next.statev))
       (li-prev (state-get li prev.statev))
       (li-next (state-get li next.statev))
       (li-target (if (sig-and empty-prev gf-prev)
                      (make-sig-target
                       :value nil
                       :time (interval-add (sig-max-time empty-prev gf-prev)
                                           delta))
                    (sig-target-from-signal li-prev)))
       ((unless (sig-check-transition li-prev li-next li-target prev.statet next.statet))
        nil)
       (gf-target (if (equal (sig-value->value gf-prev) (sig-value->value li-prev))
                      (sig-target-from-signal gf-prev)
                    (make-sig-target :value (sig-value->value li-prev)
                                     :time (interval-add (sig-max-time li-prev)
                                                         delta))))
       ((unless (sig-check-transition gf-prev gf-next gf-target prev.statet
                                      next.statet))
        nil)
       ((unless (sig-check-times empty-prev empty-next prev.statet next.statet))
        nil))
    t))


(define lenv-valid ((e lenv-p)
                    (tr gtrace-p))
  :returns (ok booleanp)
  :measure (len (gtrace-fix tr))
  :hints (("Goal" :in-theory (enable gtrace-fix)))
  (b* ((e (lenv-fix e))
       ((unless (consp (gtrace-fix tr))) t)
       ((cons first rest) (gtrace-fix tr))
       ((unless (consp (gtrace-fix rest))) t)
       (second (car (gtrace-fix rest)))
       ((unless (lenv-step e first second)) nil))
    (lenv-valid e rest)))

(define renv-step ((e renv-p)
                   (prev gstate-t-p)
                   (next gstate-t-p))
  :returns (ok booleanp)
  ;; Need a theorem that says if sigs-in-bool-table, then assoc-equal is not nil
  :guard-hints (("Goal" :in-theory (e/d (sigs-in-bool-table renv-sigs))))
  (b* ((e (renv-fix e))
       ((gstate-t prev) (gstate-t-fix prev))
       ((gstate-t next) (gstate-t-fix next))
       ((unless (sigs-in-bool-table (renv-sigs e) prev.statev)) nil)
       ((unless (sigs-in-bool-table (renv-sigs e) next.statev)) nil)
       (full (renv->full e))
       (ge (renv->go-empty e))
       (ri (renv->right-internal e))
       (delta (renv->delta e))
       (full-prev (state-get full prev.statev))
       (full-next (state-get full next.statev))
       (ge-prev (state-get ge prev.statev))
       (ge-next (state-get ge next.statev))
       (ri-prev (state-get ri prev.statev))
       (ri-next (state-get ri next.statev))
       (ri-target (if (sig-and full-prev ge-prev)
                      (make-sig-target
                       :value nil
                       :time (interval-add (sig-max-time full-prev ge-prev)
                                           delta))
                    (sig-target-from-signal ri-prev)))
       ((unless (sig-check-transition ri-prev ri-next ri-target prev.statet
                                      next.statet))
        nil)
       (ge-target (if (equal (sig-value->value ge-prev)
                             (sig-value->value ri-prev))
                      (sig-target-from-signal ge-prev)
                    (make-sig-target :value (sig-value->value ri-prev)
                                     :time (interval-add (sig-max-time ri-prev)
                                                         delta))))
       ((unless (sig-check-transition ge-prev ge-next ge-target prev.statet
                                      next.statet))
        nil)
       ((unless (sig-check-times full-prev full-next prev.statet next.statet))
        nil))
    t)
  )

(define renv-valid ((e renv-p)
                    (tr gtrace-p))
  :returns (ok booleanp)
  :measure (len (gtrace-fix tr))
  :hints (("Goal" :in-theory (enable gtrace-fix)))
  (b* ((e (renv-fix e))
       ((unless (consp (gtrace-fix tr))) t)
       ((cons first rest) (gtrace-fix tr))
       ((unless (consp (gtrace-fix rest))) t)
       (second (car (gtrace-fix rest)))
       ((unless (renv-step e first second)) nil))
    (renv-valid e rest)))

;; ------------------------------------------------------------
;;         define connection function of lenv to renv

;; need to rewrite
(define env-connection ((el lenv-p) (er renv-p))
  :returns (ok booleanp)
  (and (equal (lenv->go-full el)
              (renv->full er))
       (equal (lenv->empty el)
              (renv->go-empty er))
       )
  )


;; ========================================================================================
;;    The invariant

;; (define tag-b ((b booleanp) (n integerp))
;;   :returns (res booleanp)
;;   (declare (ignore n))
;;   (if (equal b t) t
;;     nil))

(defprod asp-stage-testbench
  ((go-full sig-value-p)
   (go-empty sig-value-p)
   (full sig-value-p)
   (empty sig-value-p)
   (full-internal sig-value-p)
   (left-internal sig-value-p)
   (right-internal sig-value-p)
   (delta interval-p)
   (inf rationalp)))

(defmacro use-asp-stage-testbench (tb bindings value)
  `(b* ((testbench (asp-stage-testbench-fix ,tb))
        (go-full (asp-stage-testbench->go-full testbench))
        (go-empty (asp-stage-testbench->go-empty testbench))
        (full (asp-stage-testbench->full testbench))
        (empty (asp-stage-testbench->empty testbench))
        (full-internal (asp-stage-testbench->full-internal testbench))
        (left-internal (asp-stage-testbench->left-internal testbench))
        (right-internal (asp-stage-testbench->right-internal testbench))
        (delta (asp-stage-testbench->delta testbench))
        (inf (asp-stage-testbench->inf testbench))
        ,@bindings)
     ,value))

(define invariant-stage-left-failed ((go-full sig-value-p)
                                     (empty sig-value-p)
                                     (full-internal sig-value-p)
                                     (delta interval-p)
                                     (tcurr rationalp)
                                     (failed integer-list-p))
  :returns (failed-clause integer-list-p)
  (b* ((go-full (sig-value-fix go-full))
       (empty (sig-value-fix empty))
       (full-internal (sig-value-fix full-internal))
       (delta (interval-fix delta))
       (failed (integer-list-fix failed))
       ;; constraints on empty, go-full, and full-internal
       ;; if full-internal is excited to go true but hasn't yet,
       ;;   then time-now is less than the max delay for full-internal.
       (failed (if (implies (and (sig-value->value empty)
                                 (sig-value->value go-full)
                                 (not (sig-value->value full-internal)))
                            (> (+ (max (sig-value->time empty)
                                       (sig-value->time go-full))
                                  (interval->hi delta))
                               tcurr))
                   failed
                 (cons 1 (integer-list-fix failed))))
       ;; if full-internal is true and empty is still true
       ;;   then  full-internal went high at least delta.min after empty went high
       ;;     and time-now is less than the max delay for empty
       (failed (if (implies (and (sig-value->value empty)
                                 (sig-value->value full-internal))
                            (and (<= (+ (sig-value->time empty)
                                        (interval->lo delta))
                                     (sig-value->time full-internal))))
                   failed
                 (cons 2 (integer-list-fix failed))))
       ;; if empty, go-full, and full-internal are all true,
       ;;   then full-internal must have recently gone high, and the
       ;;   high value on go-full is the one that enabled full-internal to go high
       ;;   Therefore, full-internal went high at least delta.min after go-full.
       (failed (if (implies (and (sig-value->value empty)
                                 (sig-value->value go-full)
                                 (sig-value->value full-internal))
                            (and (>= (sig-value->time full-internal)
                                     (+ (sig-value->time go-full)
                                        (interval->lo delta)))
                                 (< (sig-value->time full-internal)
                                    (+ (max (sig-value->time empty)
                                            (sig-value->time go-full))
                                       (interval->hi delta)))))
                   failed
                 (cons 3 (integer-list-fix failed))))
       ;; empty tracks not full-internal
       (failed (if (implies (equal (sig-value->value empty)
                                   (not (sig-value->value full-internal)))
                            (and (<= (+ (sig-value->time full-internal)
                                        (interval->lo delta))
                                     (sig-value->time empty))
                                 (< (sig-value->time empty)
                                    (+ (sig-value->time full-internal)
                                       (interval->hi delta)))))
                   failed
                 (cons 4 (integer-list-fix failed))))
       (failed (if (implies (equal (sig-value->value empty)
                                   (sig-value->value full-internal))
                            (and (> (sig-value->time full-internal)
                                    (sig-value->time empty))
                                 (> (+ (sig-value->time full-internal)
                                       (interval->hi delta))
                                    tcurr)))
                   failed
                 (cons 5 (integer-list-fix failed)))))
    failed))

(define invariant-stage-right-failed ((go-empty sig-value-p)
                                      (full sig-value-p)
                                      (full-internal sig-value-p)
                                      (delta interval-p)
                                      (tcurr rationalp)
                                      (failed integer-list-p))
  :returns (failed-clause integer-list-p)
  (b* ((go-empty (sig-value-fix go-empty))
       (full (sig-value-fix full))
       (full-internal (sig-value-fix full-internal))
       (delta (interval-fix delta))
       (failed (integer-list-fix failed))
       ;; ----------------------------------------------------
       ;; the corresponding constraints for full, go-empty, and full-internal
       ;; if full-internal is excited to go false but hasn't yet,
       ;;   then time-now is less than the max delay for full-internal.
       (failed (if (implies (and (sig-value->value full)
                                 (sig-value->value go-empty)
                                 (sig-value->value full-internal))
                            (> (+ (max (sig-value->time full)
                                       (sig-value->time go-empty))
                                  (interval->hi delta))
                               tcurr))
                   failed
                 (cons 6 (integer-list-fix failed))))
       ;; if full-internal is false and full is still true
       ;;   then  full-internal went low at least delta.min after full went high
       ;;     and time-now is less than the max delay for full
       (failed (if (implies (and (sig-value->value full)
                                 (not (sig-value->value full-internal)))
                            (and (<= (+ (sig-value->time full)
                                        (interval->lo delta))
                                     (sig-value->time full-internal))))
                   failed
                 (cons 7 (integer-list-fix failed))))
       ;; if full, go-empty, and not(full-internal) are all true,
       ;;   then full-internal must have recently gone high, and the
       ;;   high value on go-empty is the one that enabled full-internal to go high
       ;;   Therefore, full-internal went high at least delta.min after go-empty.
       (failed (if (implies (and (sig-value->value full)
                                 (sig-value->value go-empty)
                                 (not (sig-value->value full-internal)))
                            (and (>= (sig-value->time full-internal)
                                     (+ (sig-value->time go-empty)
                                        (interval->lo delta)))
                                 (< (sig-value->time full-internal)
                                    (+ (max (sig-value->time full)
                                            (sig-value->time go-empty))
                                       (interval->hi delta)))))
                   failed
                 (cons 8 (integer-list-fix failed))))
       ;; full tracks full-internal
       (failed (if (implies (equal (sig-value->value full)
                                   (sig-value->value full-internal))
                            (and (<= (+ (sig-value->time full-internal)
                                        (interval->lo delta))
                                     (sig-value->time full))
                                 (< (sig-value->time full)
                                    (+ (sig-value->time full-internal)
                                       (interval->hi delta)))))
                   failed
                 (cons 9 (integer-list-fix failed))))
       (failed (if (implies (equal (sig-value->value full)
                                   (not (sig-value->value full-internal)))
                            (and (> (sig-value->time full-internal)
                                    (sig-value->time full))
                                 (> (+ (sig-value->time full-internal)
                                       (interval->hi delta))
                                    tcurr)))
                   failed
                 (cons 10 (integer-list-fix failed)))))
    failed))

(define invariant-stage-failed ((go-full sig-value-p)
                                (go-empty sig-value-p)
                                (full sig-value-p)
                                (empty sig-value-p)
                                (full-internal sig-value-p)
                                (delta interval-p)
                                (tcurr rationalp))
  :returns (failed-clauses integer-list-p)
  (b* ((failed (integer-list-fix nil))
       (failed1 (invariant-stage-left-failed go-full empty full-internal delta
                                             tcurr failed))
       (total-failed (invariant-stage-right-failed go-empty full full-internal
                                                   delta tcurr failed1)))
    total-failed))

(define invariant-stage ((go-full sig-value-p)
                         (go-empty sig-value-p)
                         (full sig-value-p)
                         (empty sig-value-p)
                         (full-internal sig-value-p)
                         (delta interval-p)
                         (tcurr rationalp))
  :returns (ok booleanp)
  (equal (invariant-stage-failed go-full go-empty full empty full-internal
                                 delta tcurr)
         (integer-list-fix nil)))

(define invariant-lenv-failed ((go-full sig-value-p)
                               (empty sig-value-p)
                               (left-internal sig-value-p)
                               (delta interval-p)
                               (tcurr rationalp))
  :returns (failed-clauses integer-list-p)
  (b* ((go-full (sig-value-fix go-full))
       (empty (sig-value-fix empty))
       (left-internal (sig-value-fix left-internal))
       (delta (interval-fix delta))
       (failed (integer-list-fix nil))
       ;; ----------------------------------------------------
       ;; the corresponding constraints for go-full, empty, and left-internal
       ;; if left-internal is excited to go false but hasn't yet,
       ;;   then time-now is less than the max delay for left-internal.
       (failed (if (implies (and (sig-value->value go-full)
                                 (sig-value->value empty)
                                 (sig-value->value left-internal))
                            (> (+ (max (sig-value->time go-full)
                                       (sig-value->time empty))
                                  (interval->hi delta))
                               tcurr))
                   failed
                 (cons 1 (integer-list-fix failed))))
       ;; if left-internal is false and go-full is still true
       ;;   then  full-internal went low at least delta.min after go-full went high
       ;;     and time-now is less than the max delay for go-full
       (failed (if (implies (and (sig-value->value go-full)
                                 (not (sig-value->value left-internal)))
                            (and (<= (+ (sig-value->time go-full)
                                        (interval->lo delta))
                                     (sig-value->time left-internal))))
                   failed
                 (cons 2 (integer-list-fix failed))))
       ;; if go-full, empty, and not(left-internal) are all true,
       ;;   then left-internal must have recently gone high, and the
       ;;   high value on empty is the one that enabled full-internal to go high
       ;;   Therefore, full-internal went high at least delta.min after empty.
       (failed (if (implies (and (sig-value->value go-full)
                                 (sig-value->value empty)
                                 (not (sig-value->value left-internal)))
                            (and (>= (sig-value->time left-internal)
                                     (+ (sig-value->time empty)
                                        (interval->lo delta)))
                                 (< (sig-value->time left-internal)
                                    (+ (max (sig-value->time go-full)
                                            (sig-value->time empty))
                                       (interval->hi delta)))))
                   failed
                 (cons 3 (integer-list-fix failed))))
       ;; go-full tracks left-internal
       (failed (if (implies (equal (sig-value->value go-full)
                                   (sig-value->value left-internal))
                            (and (<= (+ (sig-value->time left-internal)
                                        (interval->lo delta))
                                     (sig-value->time go-full))
                                 (< (sig-value->time go-full)
                                    (+ (sig-value->time left-internal)
                                       (interval->hi delta)))))
                   failed
                 (cons 4 (integer-list-fix failed))))
       (failed (if (implies (equal (sig-value->value go-full)
                                   (not (sig-value->value left-internal)))
                            (and (> (sig-value->time left-internal)
                                    (sig-value->time go-full))
                                 (> (+ (sig-value->time left-internal)
                                       (interval->hi delta))
                                    tcurr)))
                   failed
                 (cons 5 (integer-list-fix failed)))))
    failed))

(define invariant-lenv ((go-full sig-value-p)
                        (empty sig-value-p)
                        (left-internal sig-value-p)
                        (delta interval-p)
                        (tcurr rationalp))
  :returns (ok booleanp)
  (equal (invariant-lenv-failed go-full empty left-internal delta tcurr)
         (integer-list-fix nil)))

(define invariant-renv-failed ((go-empty sig-value-p)
                               (full sig-value-p)
                               (right-internal sig-value-p)
                               (delta interval-p)
                               (tcurr rationalp))
  :returns (failed-clauses integer-list-p)
  (b* ((go-empty (sig-value-fix go-empty))
       (full (sig-value-fix full))
       (right-internal (sig-value-fix right-internal))
       (delta (interval-fix delta))
       (failed (integer-list-fix nil))
       ;; ----------------------------------------------------
       ;; the corresponding constraints for go-empty, full, and right-internal
       ;; if right-internal is excited to go true but hasn't yet,
       ;;   then time-now is less than the max delay for left-internal.
       (failed (if (implies (and (sig-value->value go-empty)
                                 (sig-value->value full)
                                 (not (sig-value->value right-internal)))
                            (> (+ (max (sig-value->time go-empty)
                                       (sig-value->time full))
                                  (interval->hi delta))
                               tcurr))
                   failed
                 (cons 1 (integer-list-fix failed))))
       ;; if right-internal is true and is go-empty still true
       ;;   then right-internal went high at least delta.min after go-empty went high
       ;;     and time-now is less than the max delay for go-empty
       (failed (if (implies (and (sig-value->value go-empty)
                                 (sig-value->value right-internal))
                            (and (<= (+ (sig-value->time go-empty)
                                        (interval->lo delta))
                                     (sig-value->time right-internal))))
                   failed
                 (cons 2 (integer-list-fix failed))))
       ;; if go-empty, full, and right-internal are all true,
       ;;   then left-internal must have recently gone high, and the
       ;;   high value on empty is the one that enabled full-internal to go high
       ;;   Therefore, full-internal went high at least delta.min after empty.
       (failed (if (implies (and (sig-value->value go-empty)
                                 (sig-value->value full)
                                 (sig-value->value right-internal))
                            (and (>= (sig-value->time right-internal)
                                     (+ (sig-value->time full)
                                        (interval->lo delta)))
                                 (< (sig-value->time right-internal)
                                    (+ (max (sig-value->time go-empty)
                                            (sig-value->time full))
                                       (interval->hi delta)))))
                   failed
                 (cons 3 (integer-list-fix failed))))
       ;; go-empty tracks not(right-internal)
       (failed (if (implies (equal (sig-value->value go-empty)
                                   (not (sig-value->value right-internal)))
                            (and (<= (+ (sig-value->time right-internal)
                                        (interval->lo delta))
                                     (sig-value->time go-empty))
                                 (< (sig-value->time go-empty)
                                    (+ (sig-value->time right-internal)
                                       (interval->hi delta)))))
                   failed
                 (cons 4 (integer-list-fix failed))))
       (failed (if (implies (equal (sig-value->value go-empty)
                                   (sig-value->value right-internal))
                            (and (> (sig-value->time right-internal)
                                    (sig-value->time go-empty))
                                 (> (+ (sig-value->time right-internal)
                                       (interval->hi delta))
                                    tcurr)))
                   failed
                 (cons 5 (integer-list-fix failed)))))
    failed))

(define invariant-renv ((go-empty sig-value-p)
                        (full sig-value-p)
                        (right-internal sig-value-p)
                        (delta interval-p)
                        (tcurr rationalp))
  :returns (ok booleanp)
  (equal (invariant-renv-failed go-empty full right-internal delta tcurr)
         (integer-list-fix nil)))

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

(set-ignore-ok t)

(define full-internal-next-nil ((testbench asp-stage-testbench-p))
  :returns (bounds interval-p)
  (use-asp-stage-testbench
   testbench
   (((if (sig-value->value full-internal)) ;; easy case -- just need to figure out when full-internal drops
     ;; figure out bounds for full and go-empty.  Then, get the bound for full-internal
     (b* ((full-time (if (sig-value->value full)
                         (make-interval :lo (sig-value->time full)
                                        :hi (sig-value->time full))
                       (interval-add (make-interval :lo (sig-value->time full-internal)
                                                    :hi (sig-value->time full-internal))
                                     delta)))
          (ge-time (cond ((sig-value->value go-empty)
                          (make-interval :lo (sig-value->time go-empty)
                                         :hi (sig-value->time go-empty)))
                         ((not (sig-value->value right-internal))
                          (interval-add (make-interval :lo (sig-value->time right-internal)
                                                       :hi (sig-value->time right-internal))
                                        delta))
                         (t
                          (make-interval
                           :lo (+ (sig-value->time right-internal) (* 3 (interval->lo delta)))
                           :hi (+ (sig-value->time right-internal) inf (interval->hi delta)))))))
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
                           :hi (+ (sig-value->time left-internal) inf (interval->hi delta))))))
    ;; fi-t-time time bouds for next transition of full-internal to t
    (fi-t-time (interval-add (interval-max empty-time gf-time) delta))
    ;; now figure out bounds for full-internal going back to nil
    ;; full goes to t to enable full-internal going to nil
    (full-time (interval-add fi-t-time delta))
    (right-internal-time (sig-value->time right-internal))
    (ge-time (cond ((and (not (sig-value->value right-internal))
                         (sig-value->value go-empty))
                    (make-interval :lo (sig-value->time go-empty)
                                   :hi (sig-value->time go-empty)))
                   ((not (sig-value->value right-internal))
                    (interval-add (make-interval
                                   :lo right-internal-time
                                   :hi right-internal-time)
                                  delta))
                   (t ;; right-internal must be t
                    (make-interval
                     :lo (+ right-internal-time (* 3 (interval->lo delta)))
                     :hi (+ right-internal-time inf (interval->hi delta)))))))
   (interval-add (interval-max full-time ge-time) delta)))

(define full-internal-next-t ((testbench asp-stage-testbench-p))
  :returns (bounds interval-p)
  (use-asp-stage-testbench
   testbench
   (((if (not (sig-value->value full-internal)))
     ;; easy case -- figure out bounds for empty and go-full going (or being) t.
     ;; Then, get the bound for the transition of full-internal to t.
     (b* ((empty-time (if (sig-value->value empty)
                          (make-interval :lo (sig-value->time empty)
                                         :hi (sig-value->time empty))
                        (interval-add (make-interval :lo (sig-value->time full-internal)
                                                     :hi (sig-value->time full-internal))
                                      delta)))
          (gf-time (cond ((sig-value->value go-full)
                          (make-interval :lo (sig-value->time go-full)
                                         :hi (sig-value->time go-full)))
                         ((sig-value->value left-internal)
                          (interval-add (make-interval :lo (sig-value->time left-internal)
                                                       :hi (sig-value->time left-internal))
                                        delta))
                         (t
                          (make-interval
                           :lo (+ (sig-value->time left-internal) (* 3 (interval->lo delta)))
                           :hi (+ (sig-value->time left-internal) inf (interval->hi delta)))))))
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
                           :hi (+ (sig-value->time right-internal) inf
                                  (interval->hi delta))))))
    ;; fi-nil-time time bounds for next transition of full-internal to nil
    (fi-nil-time (interval-add (interval-max full-time ge-time) delta))
    ;; now figure out bounds for full-internal going back to nil
    ;; empty goes to t to enable full-internal going to t
    (empty-time (interval-add fi-nil-time delta))
    (left-internal-time (sig-value->time left-internal))
    (gf-time (cond ((and (sig-value->value left-internal)
                         (sig-value->value go-full))
                    (make-interval :lo (sig-value->time go-full)
                                   :hi (sig-value->time go-full)))
                   ((sig-value->value left-internal)
                    (interval-add (make-interval
                                   :lo left-internal-time
                                   :hi left-internal-time)
                                  delta))
                   (t ;; left-internal must be nil
                    (make-interval
                     :lo (+ left-internal-time (* 3 (interval->lo delta)))
                     :hi (+ left-internal-time inf (interval->hi delta)))))))
   (interval-add (interval-max empty-time gf-time) delta)))

(define empty-next ((target booleanp) (testbench asp-stage-testbench-p))
  :returns (bounds interval-p)
  (use-asp-stage-testbench
   testbench nil
   (interval-add
    (if (and (not (equal (sig-value->value empty) target))
             (not (equal (sig-value->value full-internal) target)))
        (make-interval :lo (sig-value->time full-internal)
                       :hi (sig-value->time full-internal))
      (if target
          (full-internal-next-nil testbench)
        (full-internal-next-t testbench)))
    delta)))

(define full-next ((target booleanp)
                   (testbench asp-stage-testbench-p))
  :returns (bounds interval-p)
  (use-asp-stage-testbench
   testbench nil
   (interval-add
    (if (and (not (equal (sig-value->value full) target))
             (equal (sig-value->value full-internal) target))
        (make-interval :lo (sig-value->time full-internal)
                       :hi (sig-value->time full-internal))
      (if target
          (full-internal-next-t testbench)
        (full-internal-next-nil testbench)))
    delta)))

(define left-internal-next-nil ((testbench asp-stage-testbench-p))
  :returns (bounds interval-p)
  (use-asp-stage-testbench
   testbench
   (((if (sig-value->value left-internal)) ;; easy case -- just need to figure out when left-internal drops
     ;; figure out bounds for empty and go-full.  Then, get the bound for left-internal
     (b* ((empty-time  ;; when does empty become t ?
           (cond ((sig-value->value empty)  ;; it already is t
                  (make-interval :lo (sig-value->time empty)
                                 :hi (sig-value->time empty)))
                 ((not (sig-value->value full-internal)) ;; empty is nil, but full-internal is nil, just propagate (not full-internal) to empty
                  (interval-add (make-interval
                                 :lo (sig-value->time full-internal)
                                 :hi (sig-value->time full-internal))
                                delta))
                 (t ;; full-internal is t, it could become nil after 2*delta.lo, then add delta.lo to propagate to empty
                  (make-interval :lo (+ (sig-value->time full-internal)
                                        (* 3 (interval->lo delta)))
                                 :hi (+ (sig-value->time full-internal) ;; full-internal could stay low indefinitely
                                        inf)))))
          (gf-time (if (sig-value->value go-full)
                       (make-interval :lo (sig-value->time go-full)
                                      :hi (sig-value->time go-full))
                     (interval-add (make-interval :lo (sig-value->time left-internal)
                                                  :hi (sig-value->time left-internal))
                                   delta))))
       (interval-add (interval-max empty-time gf-time) delta)))
    ;; hard case -- need to figure out when left-internal goes high so we
    ;; can then figure out when it drops again
    ;; li-t-time time bounds for next transition of left-internal to t
    (empty-time (interval-add (full-internal-next-nil testbench) delta))
    (li-t-time (interval-add (make-interval :lo (sig-value->time left-internal)
                                            :hi (sig-value->time left-internal))
                             (make-interval :lo (* 2 (interval->lo delta))
                                            :hi inf)))
    ;; now figure out bounds for left-internal going back to nil
    ;; go-full goes to t to enable left-internal going to nil
    (gf-time (interval-add li-t-time delta)))
   (interval-add (interval-max gf-time empty-time) delta)))



(define left-internal-next-t ((testbench asp-stage-testbench-p))
  :returns (bounds interval-p)
  (use-asp-stage-testbench
   testbench
   ((li-nil-time (if (not (sig-value->value left-internal))
                     (make-interval :lo (sig-value->time left-internal)
                                    :hi (sig-value->time left-internal))
                   (left-internal-next-nil testbench))))
   (interval-add li-nil-time (make-interval :lo (* 2 (interval->lo delta))
                                            :hi inf))))

(define go-full-next ((target booleanp)
                      (testbench asp-stage-testbench-p))
  :returns (bounds interval-p)
  (use-asp-stage-testbench
   testbench nil
   (interval-add
    (if (and (not (equal (sig-value->value go-full) target))
             (equal (sig-value->value left-internal) target))
        (make-interval :lo (sig-value->time left-internal)
                       :hi (sig-value->time left-internal))
      (if target
          (left-internal-next-t testbench)
        (left-internal-next-nil testbench)))
    delta)))

(define right-internal-next-t ((testbench asp-stage-testbench-p))
  :returns (bounds interval-p)
  (use-asp-stage-testbench
   testbench
   (((if (not (sig-value->value right-internal))) ;; easy case -- just need to figure out when right-internal goes high
     ;; figure out bounds for full and go-empty.  Then, get the bound for right-internal
     (b* ((full-time  ;; when does full become t ?
           (cond ((sig-value->value full)  ;; it already is t
                  (make-interval :lo (sig-value->time full)
                                 :hi (sig-value->time full)))
                 ((sig-value->value full-internal) ;; full is nil, but full-internal is t, just propagate full-internal to full
                  (interval-add (make-interval
                                 :lo (sig-value->time full-internal)
                                 :hi (sig-value->time full-internal))
                                delta))
                 (t ;; full-internal is nil, it could become t after 2*delta.lo, then add delta.lo to propagate to full
                  (make-interval :lo (+ (sig-value->time full-internal)
                                        (* 3 (interval->lo delta)))
                                 :hi (+ (sig-value->time full-internal) ;; full-internal could stay low indefinitely
                                        inf)))))   ;; we could get a tighter bound by looking at left-internal, go-full, and empty
          ;; but I *really* hope we don't need to do that.
          (ge-time (if (sig-value->value go-empty)
                       (make-interval :lo (sig-value->time go-empty)
                                      :hi (sig-value->time go-empty))
                     (interval-add (make-interval :lo (sig-value->time right-internal)
                                                  :hi (sig-value->time right-internal))
                                   delta))))
       (interval-add (interval-max full-time ge-time) delta)))
    ;; hard case -- need to figure out when right-internal goes low so we
    ;; can then figure out when it goes high again
    ;; ri-nil-time time bounds for next transition of right-internal to nil
    (full-time (interval-add (full-internal-next-t testbench) delta))
    (ri-nil-time (interval-add (make-interval :lo (sig-value->time right-internal)
                                              :hi (sig-value->time right-internal))
                               (make-interval :lo (* 2 (interval->lo delta))
                                              :hi inf)))
    ;; now figure out bounds for right-internal going back to t
    ;; go-empty goes to t to enable right-internal going to t
    (ge-time (interval-add ri-nil-time delta)))
   (interval-add (interval-max full-time ge-time) delta))
  )

(define right-internal-next-nil ((testbench asp-stage-testbench-p))
  :returns (bounds interval-p)
  (use-asp-stage-testbench
   testbench
   ((ri-t-time (if (sig-value->value right-internal)
                   (make-interval :lo (sig-value->time right-internal)
                                  :hi (sig-value->time right-internal))
                 (right-internal-next-t testbench))))
   (interval-add ri-t-time (make-interval :lo (* 2 (interval->lo delta))
                                          :hi inf))))

(define go-empty-next ((target booleanp)
                       (testbench asp-stage-testbench-p))
  :returns (bounds interval-p)
  (use-asp-stage-testbench
   testbench nil
   (interval-add
    (if (and (not (equal (sig-value->value go-empty) target))
             (not (equal (sig-value->value right-internal) target)))
        (make-interval :lo (sig-value->time right-internal)
                       :hi (sig-value->time right-internal))
      (if target
          (right-internal-next-nil testbench)
        (right-internal-next-t testbench)))
    delta)))

;; ------------------------------------------------------------------------------

;; I'd like to take advantage of the near-symmetry of the left and right
;; interfaces.  Rather than refering to 'next-t' or 'next-nil', I'll write
;; 'next-ready' and 'next-idle'.  left-internal is 'ready' when it is t
;; and 'idle' when it is nil.  right-internal is ready when it is nil, and
;; idle when it is t.

(define internal-next-idle ((my-internal sig-value-p)
                            (my-external sig-value-p)
                            (your-internal sig-value-p)
                            (your-external sig-value-p)
                            (ready-is-t booleanp)
                            (delta interval-p))
  :returns(next-time interval-p)
  (if (equal (sig-value->value my-internal) ready-is-t)
      (interval-add (sig-max-time my-external your-external)
                    delta)
    (sig-time-to-interval my-internal)))

(define internal-next-ready ((my-internal sig-value-p)
                             (my-external sig-value-p)
                             (your-internal sig-value-p)
                             (your-external sig-value-p)
                             (ready-is-t booleanp)
                             (delta interval-p
                                    inf rationalp))
  :returns(next-time interval-p)
  (b* ((next-idle
        (internal-next-idle my-internal my-external your-internal
                            your-external ready-is-t delta)))
    (make-interval
     :lo (+ (interval->lo next-idle) (interval->lo delta))
     :hi (+ (interval->hi next-idle) inf (interval->hi delta)))))


;; starting from start of (and empty gf)
;; 1. last(li_idle, fi_up) < first(empty_down, gf_down)
;; 2. last(empty_down, gf_down) < first(empty_up, gf_up)
(define interact-lenv-failed ((testbench asp-stage-testbench-p))
  :returns (failed-clauses integer-list-p)
  (use-asp-stage-testbench
   testbench
   ((li_idle (internal-next-idle li lx ri rx t delta))
    (ri_idle (internal-next-idle ri rx li lx nil delta))
    (rx_down (external-next-idle ri rx li lix nil delta))
    (gf_down (if (sig-value->value go-full)
                 (go-full-next nil testbench)
               (make-interval :lo (sig-value->time go-full)
                              :hi (sig-value->time go-full))))
    (empty_up (empty-next t testbench))
    (gf_up (go-full-next t testbench))
    (failed (integer-list-fix nil))
    ;; logical constraints
    (failed (if (implies (and (sig-value->value lx)
                              (sig-value->value rx))
                         (< (max (interval->hi li_idle)
                                 (interval->hi ri_up))
                            (min (interval->lo lx_down)
                                 (interval->lo rx_down))))
                failed
              (cons 1 (integer-list-fix failed))))
    (failed (if (implies (or (and (sig-value->value rx)
                                  (or (sig-value->value lx)
                                      (sig-value->value ri)))
                             (and (sig-value->value lx)
                                  (or (sig-value->value rx)
                                      (not (sig-value->value li)))))
                         (< (max (interval->hi lx_down)
                                 (interval->hi rx_down))
                            (min (interval->lo lx_up)
                                 (interval->lo rx_up))))
                failed
              (cons 2 (integer-list-fix failed)))))
   failed))

(define interact-lenv ((testbench asp-stage-testbench-p))
  :returns (ok booleanp)
  (equal (interact-lenv-failed testbench)
         (integer-list-fix nil)))

;; starting from start of (and full ge)
;; 1. last(fi_down, ri_up) < first(full_down, ge_down)
;; 2. last(full_down, ge_down) < first(full_up, ge_up)
(define interact-renv-failed ((testbench asp-stage-testbench-p))
  :returns (failed-clauses integer-list-p)
  (use-asp-stage-testbench
   testbench
   ((fi_down (if (sig-value->value full-internal)
                 (full-internal-next-nil testbench)
               (make-interval :lo (sig-value->time full-internal)
                              :hi (sig-value->time full-internal))))
    (ri_up (if (sig-value->value right-internal)
               (make-interval :lo (sig-value->time right-internal)
                              :hi (sig-value->time right-internal))
             (right-internal-next-t testbench)))
    (full_down (if (sig-value->value full)
                   (full-next nil testbench)
                 (make-interval :lo (sig-value->time full)
                                :hi (sig-value->time full))))
    (ge_down (if (sig-value->value go-empty)
                 (go-empty-next nil testbench)
               (make-interval :lo (sig-value->time go-empty)
                              :hi (sig-value->time go-empty))))
    (full_up (full-next t testbench))
    (ge_up (go-empty-next t testbench))
    (failed (integer-list-fix nil))
    ;; logical constraints
    (failed (if (implies (and (sig-value->value full)
                              (sig-value->value go-empty))
                         (< (max (interval->hi fi_down)
                                 (interval->hi ri_up))
                            (min (interval->lo full_down)
                                 (interval->lo ge_down))))
                failed
              (cons 1 (integer-list-fix failed))))
    (failed (if (implies (or (and (sig-value->value full)
                                  (or (sig-value->value go-empty)
                                      (not (sig-value->value full-internal))))
                             (and (sig-value->value go-empty)
                                  (or (sig-value->value full)
                                      (sig-value->value right-internal))))
                         (< (max (interval->hi full_down)
                                 (interval->hi ge_down))
                            (min (interval->lo full_up)
                                 (interval->lo ge_up))))
                failed
              (cons 2 (integer-list-fix failed)))))
   failed))

(define interact-renv ((testbench asp-stage-testbench-p))
  :returns (ok booleanp)
  (equal (interact-renv-failed testbench)
         (integer-list-fix nil)))

(set-ignore-ok nil)

;; ------------------------------------------------------------------------------

(define invariant ((a asp-stage-p) (el lenv-p) (er renv-p)
                   (tcurr rationalp) (curr gstate-p)
                   (inf rationalp))
  :returns (ok booleanp)
  :guard-debug t
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
                                          (gstate-fix curr)))))
       (testbench (make-asp-stage-testbench
                   :go-full go-full
                   :go-empty go-empty
                   :full full
                   :empty empty
                   :full-internal full-internal
                   :left-internal left-internal
                   :right-internal right-internal
                   :delta delta
                   :inf inf)))
    (and (invariant-stage go-full go-empty full empty full-internal delta tcurr)
         (invariant-lenv go-full empty left-internal delta tcurr)
         (invariant-renv go-empty full right-internal delta tcurr)
         (interact-lenv testbench)
         (interact-renv testbench))))

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
                             maybe-rational target-tuple integer-list asp-stage-testbench)
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

(set-evisc-tuple (evisc-tuple 3   ; print-level
                              4   ; print-length
                              nil ; alist
                              nil ; hiding-cars
                              )
                 :iprint :same ; better yet, T
                 :sites :all)

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
                            maybe-rational target-tuple integer-list asp-stage-testbench)
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
                 :smt-fname "inv-theorem.py"
                 :smt-dir "smtpy"
                 :evilp t
                 ))))

