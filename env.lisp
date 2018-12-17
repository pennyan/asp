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
       (hd (car (sig-value-list-fix sigs)))
       (tl (cdr (sig-value-list-fix sigs)))
       ((unless (sig-value->value hd)) nil))
    (sig-and-fun tl)))

(defmacro sig-and (&rest rst)
  `(sig-and-fun (list ,@rst)))

(define sig-max-time-help ((sigs sig-value-list-p) (currmax rationalp))
  :returns (v rationalp :hyp :guard)
  :measure (len sigs)
  (b* ((sigs (sig-value-list-fix sigs))
       ((unless (consp (sig-value-list-fix sigs))) currmax)
       (hd (car (sig-value-list-fix sigs)))
       (tl (cdr (sig-value-list-fix sigs)))
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
  :returns (ok booleanp)
  (b* ((prev (sig-value-fix prev))
       (next (sig-value-fix next))
       ((unless (<= tprev tnext)) nil)
       ((unless (<= 0 (sig-value->time prev))) nil)
       ((unless (<= (sig-value->time prev) (sig-value->time next))) nil)
       ((unless (<= (sig-value->time prev) tprev)) nil)
       ((unless (<= (sig-value->time next) tnext)) nil)
       ((unless (implies (equal (sig-value->value prev)
                                (sig-value->value next))
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
                              (<= (interval->lo (sig-target->time target))
                                  tnext))))
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
  ((ack-in sig-path-p)
   (req-out sig-path-p)
   (left-internal sig-path-p)
   (delta interval-p)
   ))

(define lenv-sigs ((e lenv-p))
  :returns (l sig-path-listp)
  (b* ((e (lenv-fix e))
       (ack-in (lenv->ack-in e))
       (req-out (lenv->req-out e))
       (left-internal (lenv->left-internal e)))
    (cons ack-in (sig-path-list-fix
                  (cons req-out
                        (sig-path-list-fix
                         (cons left-internal
                               (sig-path-list-fix nil))))))))

(defprod renv
  ((req-in sig-path-p)
   (ack-out sig-path-p)
   (right-internal sig-path-p)
   (delta interval-p)
   ))

(define renv-sigs ((e renv-p))
  :returns (l sig-path-listp)
  (b* ((e (renv-fix e))
       (req-in (renv->req-in e))
       (ack-out (renv->ack-out e))
       (right-internal (renv->right-internal e)))
    (cons req-in (sig-path-list-fix
                  (cons ack-out
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
       (ack-in (lenv->ack-in e))
       (gf (lenv->req-out e))
       (li (lenv->left-internal e))
       (delta (lenv->delta e))
       (ack-in-prev (state-get ack-in prev.statev))
       (ack-in-next (state-get ack-in next.statev))
       (gf-prev (state-get gf prev.statev))
       (gf-next (state-get gf next.statev))
       (li-prev (state-get li prev.statev))
       (li-next (state-get li next.statev))
       (li-target (if (sig-and ack-in-prev gf-prev)
                      (make-sig-target
                       :value nil
                       :time (interval-add (sig-max-time ack-in-prev gf-prev)
                                           delta))
                    (sig-target-from-signal li-prev)))
       ((unless (sig-check-transition li-prev li-next li-target prev.statet
                                      next.statet))
        nil)
       (gf-target (if (equal (sig-value->value gf-prev)
                             (sig-value->value li-prev))
                      (sig-target-from-signal gf-prev)
                    (make-sig-target :value (sig-value->value li-prev)
                                     :time (interval-add (sig-max-time li-prev)
                                                         delta))))
       ((unless (sig-check-transition gf-prev gf-next gf-target prev.statet
                                      next.statet))
        nil)
       ((unless (sig-check-times ack-in-prev ack-in-next prev.statet
                                 next.statet))
        nil))
    t))


(define lenv-valid ((e lenv-p)
                    (tr gtrace-p))
  :returns (ok booleanp)
  :measure (len (gtrace-fix tr))
  :hints (("Goal" :in-theory (enable gtrace-fix)))
  (b* ((e (lenv-fix e))
       ((unless (consp (gtrace-fix tr))) t)
       (first (car (gtrace-fix tr)))
       (rest (cdr (gtrace-fix tr)))
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
       (req-in (renv->req-in e))
       (ge (renv->ack-out e))
       (ri (renv->right-internal e))
       (delta (renv->delta e))
       (req-in-prev (state-get req-in prev.statev))
       (req-in-next (state-get req-in next.statev))
       (ge-prev (state-get ge prev.statev))
       (ge-next (state-get ge next.statev))
       (ri-prev (state-get ri prev.statev))
       (ri-next (state-get ri next.statev))
       (ri-target (if (sig-and req-in-prev ge-prev)
                      (make-sig-target
                       :value nil
                       :time (interval-add (sig-max-time req-in-prev ge-prev)
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
       ((unless (sig-check-times req-in-prev req-in-next prev.statet
                                 next.statet))
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
       (first (car (gtrace-fix tr)))
       (rest (cdr (gtrace-fix tr)))
       ((unless (consp (gtrace-fix rest))) t)
       (second (car (gtrace-fix rest)))
       ((unless (renv-step e first second)) nil))
    (renv-valid e rest)))

;; ------------------------------------------------------------
;;         define connection function of lenv to renv

(define env-connection ((el lenv-p) (er renv-p))
  :returns (ok booleanp)
  (and (equal (lenv->req-out el)
              (renv->req-in er))
       (equal (lenv->ack-in el)
              (renv->ack-out er))
       )
  )


;; ========================================================================================
;;    The invariant

(defprod asp-env-testbench
  ((req sig-value-p)  ;; request -- from lenv to renv
   (ack sig-value-p)  ;; acknowledge -- from renv to lenv
   (li sig-value-p)   ;; internal state of lenv
   (ri sig-value-p)   ;; internal state of renv
   (delta interval-p)
   (inf rationalp)))

(defmacro with-asp-env-testbench (tb bindings value)
  `(b* ((testbench (asp-env-testbench-fix ,tb))
        ((sig-value req) (asp-env-testbench->req testbench))
        ((sig-value ack) (asp-env-testbench->ack testbench))
        ((sig-value li) (asp-env-testbench->li testbench))
        ((sig-value ri) (asp-env-testbench->ri testbench))
        (delta (asp-env-testbench->delta testbench))
        (inf (asp-env-testbench->inf testbench))
        ,@bindings)
     ,value))

(set-ignore-ok t)

(defprod asp-my-bench
  ((my-internal sig-value-p)
   (my-external sig-value-p)
   (your-internal sig-value-p)
   (your-external sig-value-p)
   (ready-is-t booleanp)
   (delta interval-p)
   (inf rationalp)))

(defmacro with-asp-my-bench (tb bindings value)
  `(b* ((mybench (asp-my-bench-fix ,tb))
        ((sig-value mi) (asp-my-bench->my-internal mybench))
        ((sig-value mx) (asp-my-bench->my-external mybench))
        ((sig-value yi) (asp-my-bench->your-internal mybench))
        ((sig-value yx) (asp-my-bench->your-external mybench))
        (ready-is-t (asp-my-bench->ready-is-t mybench))
        ((interval delta) (asp-my-bench->delta mybench))
        (inf (asp-my-bench->inf mybench))
        (ready (equal mi.value ready-is-t))
        ,@bindings)
     ,value))

(define leftbench ((testbench asp-env-testbench-p))
  :returns (myb asp-my-bench-p)
  (with-asp-env-testbench testbench nil
                          (make-asp-my-bench
                           :my-internal li
                           :my-external req
                           :your-internal ri
                           :your-external ack
                           :ready-is-t t
                           :delta delta
                           :inf inf)))

(define rightbench ((testbench asp-env-testbench-p))
  :returns (myb asp-my-bench-p)
  (with-asp-env-testbench testbench nil
                          (make-asp-my-bench
                           :my-internal ri
                           :my-external ack
                           :your-internal li
                           :your-external req
                           :ready-is-t nil
                           :delta delta
                           :inf inf)))


;; invariant-env-failed -- check that signal values and times are sane
;;   for a single asp* 'environment' element (i.e. lenv or renv).
;;   The signals we consider are:
;;     mi -- my-internal -- the internal state for the environment element
;;     mx -- my-external -- the output of this environment element.
;;           I.e. mx=req for lenv, and mx=ack for renv.
;;     yx -- your-external -- the input of this environment element, also
;;           the output of the other environment element, hence "your".
;;   The intended operation of the stage is
;;     (and mx yx) -delta-> (idle mi)
;;     (idle mi)   -delta-> (not mx)
;;     (idle mi)   -[delta.lo,inf)-> (ready mi)
;;     (ready mi)  -delta-> mx
;;   Where the notation above is
;;     pre-condition -DelayInterval-> post-condition.
;;   Finally, every signal, s, should satisfy
;;     0 <= s.time <=  tcurr
(define invariant-env-failed ((b asp-my-bench-p)
                              (tcurr rationalp))
  :returns (failed-clauses integer-list-p)
  (with-asp-my-bench b
                     ((fail-acc (integer-list-fix nil))
                      ;; Constraints for mi:
                      ;;   If (and mx yx (ready mi)),
                      ;;   then there is a pending action to set mi to idle
                      (fail-acc
                       (if (implies (and mx.value yx.value ready)
                                    (< tcurr (+ (max mx.time yx.time)
                                                delta.hi)))
                           fail-acc
                         (cons 1 (integer-list-fix fail-acc))))
                      ;;   If (and mx yx (not (ready mi))),
                      ;;   then the transition of mi to idle was enabled by the
                      ;;   current value of yx.
                      ;;   Thus mi.time >= yx.time + delta.lo
                      (fail-acc
                       (if (implies (and (not ready) mx.value yx.value)
                                    (and (<= (+ yx.time delta.lo) mi.time)
                                         (< mi.time (+ (max mx.time yx.time)
                                                       delta.hi))))
                           fail-acc
                         (cons 2 (integer-list-fix fail-acc))))
                      ;;   If (and mx (not (ready mi))),
                      ;;   then the transition of mi to idle was enabled by the
                      ;;   current value of mx.
                      ;;   Thus mi.time >= mx.time + delta.lo
                      (fail-acc (if (implies (and (not ready) mx.value)
                                             (<= (+ mx.time delta.lo) mi.time))
                                    fail-acc
                                  (cons 3 (integer-list-fix fail-acc))))
                      ;;   If (and (not mx) ready)
                      ;;   mx went low less than delta.hi after ready went low.
                      ;;   ready went high at least 2*delta.lo after ready went
                      ;;   low.
                      ;;   Therefore mx.time - delta.hi + 2*delta.lo < mi.time.
                      ;;   ALthough I don't think we need this one for the
                      ;;   invariant, I'm including it here for completeness.
                      (fail-acc
                       (if (implies (and (not mx.value) ready)
                                    (< (+ mx.time (- delta.hi) (* 2 delta.lo))
                                       mi.time))
                           fail-acc
                         (cons 4 (integer-list-fix fail-acc))))

                      ;;   Constraints for mx:  mx follows (ready mi).
                      ;;   If (equal mx my),
                      ;;   then (in mx.time (+ mi.time delta))
                      ;;   otherwise (<= mx.time mi.time)
                      (fail-acc
                       (if (implies (equal mx.value ready)
                                    (and (<= (+ yx.time delta.lo) mi.time)
                                         (< mi.time (+ (max mx.time yx.time)
                                                       delta.hi))))
                           fail-acc
                         (cons 5 (integer-list-fix fail-acc))))
                      (fail-acc
                       (if (implies (not (equal mx.value ready))
                                    (and (< mx.time mi.time)
                                         (< tcurr (+ mi.time delta.hi))))
                           fail-acc
                         (cons 6 (integer-list-fix fail-acc)))))
                     fail-acc))

(define invariant-lenv-failed ((b asp-env-testbench-p)
                               (tcurr rationalp))
  :returns (failed-clauses integer-list-p)
  (invariant-env-failed (leftbench b) tcurr))

(define invariant-lenv ((b asp-env-testbench-p)
                        (tcurr rationalp))
  :returns (ok booleanp)
  (equal (invariant-lenv-failed b tcurr)
         (integer-list-fix nil)))

(define invariant-renv-failed ((b asp-env-testbench-p)
                               (tcurr rationalp))
  :returns (failed-clauses integer-list-p)
  (invariant-env-failed (rightbench b) tcurr))

(define invariant-renv ((b asp-env-testbench-p)
                        (tcurr rationalp))
  :returns (ok booleanp)
  (equal (invariant-renv-failed b tcurr)
         (integer-list-fix nil)))


;; ----------------------------------------------------------

;; The functions internal-idle-time, internal-next-ready-time,
;; external-idle-time, and external-next-ready-time computes bounds on
;; when my-internal and my-external acquire 'ready' or 'idle' values.
;; These are used in to connect logical values with signal transition
;; times to show that the timing constraints for the interfaces are
;; sufficient to ensure correct operation.

;; internal-idle-time: time interval for when my-internal is idle.  If
;;   my-internal is already idle, just make an intervale where both bounds
;;   are mi.time.
(define internal-idle-time ((b asp-my-bench-p))
  :returns(next-time interval-p)
  (with-asp-my-bench b
                     (((if ready)
                       (interval-add (sig-max-time mx yx) delta)))
                     (make-interval :lo mi.time :hi mi.time)))

;; internal-next-ready-time: time interval for the *next* time that
;;   my-internal is ready.  If my-internal is idle, we determine bounds on
;;   when it can transition to ready.  If my-internal is currently ready,
;;   we calculate bounds on when it goes to idle and then goes back to
;;   ready again.  Hence the "next" in the function name.
(define internal-next-ready-time ((b asp-my-bench-p))
  :returns(next-time interval-p)
  (with-asp-my-bench
   b
   (((interval x) (interval-add (internal-idle-time b) delta)))
   (change-interval x :hi (+ x.hi inf))))

;; external-idle-time: time interval for the next time that my-external is
;;   idle.
(define external-idle-time ((b asp-my-bench-p))
  :returns(next-time interval-p)
  (with-asp-my-bench b nil
                     (interval-add (internal-idle-time b) delta)))

;; external-next-ready-time: time interval for the *next* time that
;;   my-external is ready.
(define external-next-ready-time ((b asp-my-bench-p))
  :returns(next-time interval-p)
  (with-asp-my-bench b nil
                     (interval-add (internal-next-ready-time b) delta)))

;; interact-env-failed -- check that signal values and times are sane for
;;   the interactions between a lenv and renv.  This is where we track
;;   how timing constraints guarantee logical requirements.
;; In particular, there is a race for reseting the internal states of the
;;   two interfaces and reseting their outputs.  We require that both
;;   internal states are reset before either output is reset.
;; The second constraint is that both outputs must be reset before either
;;   interface sets its output high again.
;; For both constraints, the invariant needs to keep track of bounds on the
;;   on the times at which various future events can occur based on the
;;   current state.  That's what the functions internal-idle-time, etc.
;;   above do.  When a state transition occurs, it should be consistent
;;   with these bounds.  Because the signal that changes the transition gets
;;   a specific time for the change, rather than the bounds that had been
;;   computed in the prior state, our bounds should be tightening with
;;   each constraint.
(define interact-env-failed ((b asp-env-testbench-p))
  :returns (failed-clauses integer-list-p)
  (with-asp-env-testbench b
                          ((lb (leftbench b))
                           (rb (rightbench b))
                           ((interval li_idle)  (internal-idle-time  lb))
                           ((interval lx_idle)  (external-idle-time  lb))
                           ((interval lx_ready) (external-next-ready-time lb))
                           ((interval ri_idle)  (internal-idle-time  rb))
                           ((interval rx_idle)  (external-idle-time  rb))
                           ((interval rx_ready) (external-next-ready-time rb))
                           (l-ready li.value)
                           (r-ready (not ri.value))
                           (failed-acc (integer-list-fix nil))
                           ;; once triggered (i.e. (and req ack)), both
                           ;; interfaces must reset their internal state to
                           ;; idle before either resets its output.
                           (failed-acc
                            (if (implies (and req.value ack.value)
                                         (< (max li_idle.hi ri_idle.hi)
                                            (min lx_idle.lo rx_idle.lo)))
                                failed-acc
                              (cons 1 (integer-list-fix failed-acc))))
                           ;; both outputs must be reset before either is set
                           ;; again for the next transfer.
                           (failed-acc
                            (if (implies
                                 (or (and ack.value (or req.value (not r-ready)))
                                     (and req.value (or ack.value (not l-ready))))
                                 (< (max lx_idle.hi  rx_idle.hi)
                                    (min lx_ready.lo rx_ready.lo)))
                                failed-acc
                              (cons 2 (integer-list-fix failed-acc)))))
                          failed-acc))

(define interact-env ((b asp-env-testbench-p))
  :returns (ok booleanp)
  (equal (interact-env-failed b)
         (integer-list-fix nil)))

;; ------------------------------------------------------------------------------

(define invariant ((left lenv-p) (right renv-p)
                   (tcurr rationalp) (curr gstate-p)
                   (inf rationalp))
  :returns (ok booleanp)
  :guard-debug t
  :guard-hints (("Goal" :in-theory (enable sigs-in-bool-table
                                           lenv-sigs renv-sigs)))
  (b* (((lenv left) (lenv-fix left))
       ((renv right) (renv-fix right))
       (curr (gstate-fix curr))
       ((unless (sigs-in-bool-table (lenv-sigs left) curr)) nil)
       ((unless (sigs-in-bool-table (renv-sigs right) curr)) nil)
       (delta left.delta)
       ((sig-value li)  (state-get left.left-internal curr))
       ((sig-value req) (state-get left.req-out curr))
       ((sig-value ack) (state-get right.ack-out curr))
       ((sig-value ri)  (state-get right.right-internal curr))
       (testbench (make-asp-env-testbench
                   :req req
                   :ack ack
                   :li li
                   :ri ri
                   :delta delta
                   :inf inf)))
    (and (invariant-lenv testbench tcurr)
         (invariant-renv testbench tcurr)
         (interact-env testbench))))

(define invariant-trace ((el lenv-p) (er renv-p) (tr gtrace-p)
                         (inf rationalp))
  :returns (ok booleanp)
  :measure (len tr)
  (b* ((tr (gtrace-fix tr))
       ((unless (consp (gtrace-fix tr))) t)
       (first (car (gtrace-fix tr)))
       (rest (cdr (gtrace-fix tr)))
       ((unless (consp (gtrace-fix rest))) t))
    (and (invariant el er (gstate-t->statet first) (gstate-t->statev first)
                    inf)
         (invariant-trace el er rest inf))))


stop

(std::must-fail
 (defthm invariant-check-contradiction
   (not (and (lenv-p el)
             (renv-p er)
             (env-connection el er)
             (gtrace-p tr)
             (lenv-valid el tr)
             (renv-valid er tr)
             (valid-interval (lenv->delta el))
             (valid-interval (renv->delta er))
             (equal (interval->lo (lenv->delta a))
                    8)
             (equal (interval->hi (lenv->delta a))
                    10)
             ;; (equal (gstate-t->statet (car (gtrace-fix tr))) 8)
             (equal (interval->lo (lenv->delta el))
                    (interval->lo (renv->delta er)))
             (equal (interval->hi (lenv->delta el))
                    (interval->hi (renv->delta er)))
             (consp (gtrace-fix tr))
             (consp (gtrace-fix (cdr (gtrace-fix tr))))
             (invariant el er
                        (gstate-t->statet (car (gtrace-fix tr)))
                        (gstate-t->statev (car (gtrace-fix tr)))
                        1000)))
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
                               :level 3)
                              (sig-max-time-help
                               :formals ((sigs sig-value-list-p)
                                         (currmax rationalp))
                               :returns ((v rationalp))
                               :level 2)
                              (sig-and-fun
                               :formals ((sigs sig-value-list-p))
                               :returns ((v booleanp))
                               :level 2)
                              (lenv-valid
                               :formals ((e lenv-p)
                                         (tr gtrace-p))
                               :returns ((ok booleanp))
                               :level 1)
                              (renv-valid
                               :formals ((e renv-p)
                                         (tr gtrace-p))
                               :returns ((ok booleanp))
                               :level 1)
                              )
                  :smt-fname "inv-theorem.py"
                  :smt-dir "smtpy"
                  :evilp t
                  ))))
 )

(defthm invariant-thm
  (implies (and (lenv-p el)
                (renv-p er)
                (env-connection el er)
                (gtrace-p tr)
                (lenv-valid el tr)
                (renv-valid er tr)
                (valid-interval (lenv->delta el))
                (valid-interval (renv->delta er))
                (equal (interval->lo (lenv->delta a))
                       8)
                (equal (interval->hi (lenv->delta a))
                       10)
                ;; (equal (gstate-t->statet (car (gtrace-fix tr))) 8)
                (equal (interval->lo (lenv->delta el))
                       (interval->lo (renv->delta er)))
                (equal (interval->hi (lenv->delta el))
                       (interval->hi (renv->delta er)))
                (consp (gtrace-fix tr))
                (consp (gtrace-fix (cdr (gtrace-fix tr))))
                (invariant el er
                           (gstate-t->statet (car (gtrace-fix tr)))
                           (gstate-t->statev (car (gtrace-fix tr)))
                           1000))
           (invariant el er
                      (gstate-t->statet (car (gtrace-fix (cdr (gtrace-fix tr)))))
                      (gstate-t->statev (car (gtrace-fix (cdr (gtrace-fix
                                                               tr)))))
                      1000))
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
                              :level 3)
                             (sig-max-time-help
                              :formals ((sigs sig-value-list-p)
                                        (currmax rationalp))
                              :returns ((v rationalp))
                              :level 2)
                             (sig-and-fun
                              :formals ((sigs sig-value-list-p))
                              :returns ((v booleanp))
                              :level 2)
                             (lenv-valid
                              :formals ((e lenv-p)
                                        (tr gtrace-p))
                              :returns ((ok booleanp))
                              :level 1)
                             (renv-valid
                              :formals ((e renv-p)
                                        (tr gtrace-p))
                              :returns ((ok booleanp))
                              :level 1)
                             )
                 :smt-fname "inv-theorem.py"
                 :smt-dir "smtpy"
                 :evilp t
                 ))))
