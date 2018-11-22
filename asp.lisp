(in-package "ASP")

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

;; -------------------------------------
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
       )
    (cond
     ;; full_interval ->(delta_t2) full ^ not(empty)
     ;; not(full_interval) ->(delta_t2) not(full) ^ empty
     ((and
       ;; if full changes, it should change after lo
       (implies (not (equal (sig-value->value full-prev)
                            (sig-value->value full-next)))
                (> tnext
                   (+ (sig-value->time full-internal-prev)
                      (interval->lo delta-t2))))
       ;; if full hasn't changed yet, the current time should be
       (implies (not (equal (sig-value->value full-next)
                            (sig-value->value full-internal-prev)))
                (<= tnext
                    (+ (sig-value->time full-internal-prev) ;; Should this be full-internal-prev??
                       (interval->hi delta-t2)))))
      t)
     ((and
       ;; if empty changes, it should change after lo
       (implies (not (equal (sig-value->value empty-prev)
                            (sig-value->value empty-next)))
                (> tnext
                   (+ (sig-value->time full-internal-prev)
                      (interval->lo delta-t2))))
       ;; if empty hasn't changed yet, the current time should be
       (implies (equal (sig-value->value empty-next)
                       (sig-value->value full-internal-prev))
                (<= tnext
                    (+ (sig-value->time full-internal-prev) ;; Should this be full-internal-prev??
                       (interval->hi delta-t2)))))
      t)
     ;; empty ^ go_full ->(delta_t1) full_internal
     ((and
       ;; if full_internal changes, it should change after lo
       (implies (not (equal (sig-value->value full-internal-prev)
                            (sig-value->value full-internal-next)))
                (and (> tnext
                        (+ (sig-value->time empty-prev)
                           (interval->lo delta-t1)))
                     (> tnext
                        (+ (sig-value->time go-full-prev)
                           (interval->lo delta-t1)))))
       ;; if full_internal hasn't changed yet, the current time should be
       (implies (and (equal t (sig-value->value empty-prev))
                     (equal t (sig-value->value go-full-prev))
                     (not (equal (sig-value->value full-internal-next)
                                 (sig-value->value go-full-prev))))
                (and (<= tnext
                         (+ (sig-value->time empty-prev)
                            (interval->hi delta-t1)))
                     (<= tnext
                         (+ (sig-value->time go-full-prev)
                            (interval->hi delta-t1))))))
      t)
     ;; full ^ go_empty ->(delta_t1) not(full_internal)
     ((and
       ;; if full_internal changes, it should change after lo
       (implies (not (equal (sig-value->value full-internal-prev)
                            (sig-value->value full-internal-next)))
                (and (> tnext
                        (+ (sig-value->time full-prev)
                           (interval->lo delta-t1)))
                     (> tnext
                        (+ (sig-value->time go-empty-prev)
                           (interval->lo delta-t1)))))
       ;; if full_internal hasn't changed yet, the current time should be
       (implies (and (equal t (sig-value->value full-prev))
                     (equal t (sig-value->value go-empty-prev))
                     (equal (sig-value->value full-internal-next)
                            (sig-value->value go-empty-prev)))
                (and (<= tnext
                         (+ (sig-value->time full-prev)
                            (interval->hi delta-t1)))
                     (<= tnext
                         (+ (sig-value->time go-empty-prev)
                            (interval->hi delta-t1))))))
      t)
     ;; Other cases are invalid steps
     (t (and (nondecreasing-time tprev tnext)
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
     ))
  )

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

;; -------------------------------------------------
;;             environment

(defprod env
  ((input sig-path-p)
   (output sig-path-p)
   (delta-env interval-p)
   ))

(define env-sigs ((e env-p))
  :returns (l sig-path-listp)
  (b* ((e (env-fix e))
       (input (env->input e))
       (output (env->output e)))
    (cons input
          (sig-path-list-fix
           (cons output (sig-path-list-fix
                         nil))))))

(define env-step ((e env-p)
                  (tprev rationalp) (prev gstate-p)
                  (tnext rationalp) (next gstate-p))
  :returns (ok booleanp)
  ;; Need a theorem that says if sigs-in-bool-table, then assoc-equal is not nil
  :guard-hints (("Goal" :in-theory (e/d (sigs-in-bool-table env-sigs))))
  (b* ((e (env-fix e))
       (prev (gstate-fix prev))
       (next (gstate-fix next))
       ((unless (sigs-in-bool-table (env-sigs e) prev)) nil)
       ((unless (sigs-in-bool-table (env-sigs e) next)) nil)
       (input (env->input e))
       (output (env->output e))
       (delta-env (env->delta-env e))
       (in-prev (cdr (smt::magic-fix
                      'sig-path_sig-value
                      (assoc-equal input (gstate-fix prev)))))
       (in-next (cdr (smt::magic-fix
                      'sig-path_sig-value
                      (assoc-equal input (gstate-fix next)))))
       (out-prev (cdr (smt::magic-fix
                       'sig-path_sig-value
                       (assoc-equal output (gstate-fix prev)))))
       (out-next (cdr (smt::magic-fix
                       'sig-path_sig-value
                       (assoc-equal output (gstate-fix next)))))
       )
    (cond
     ;; not(out) ->(delta_env_inf) out
     ((and
       ;; if out changes, it should change after lo
       (implies (not (equal (sig-value->value out-prev)
                            (sig-value->value out-next)))
                (> tnext
                   (+ (sig-value->time out-prev)
                      (interval->lo delta-env)))))
      t)
     ;; out ^ in ->(delta_env) not(out)
     ((and
       ;; if out changes, it should change after lo
       (implies (not (equal (sig-value->value out-prev)
                            (sig-value->value out-next)))
                (and (> tnext
                        (+ (sig-value->time in-prev)
                           (interval->lo delta-env)))
                     (> tnext
                        (+ (sig-value->time out-prev)
                           (interval->lo delta-env)))))
       ;; if out hasn't changed yet, the current time should be smaller than hi
       (implies (and (equal t (sig-value->value in-prev))
                     (equal t (sig-value->value out-prev))
                     (equal t (sig-value->value out-next)))
                (and (<= tnext
                         (+ (sig-value->time in-prev)
                            (interval->hi delta-env)))
                     (<= tnext
                         (+ (sig-value->time out-prev)
                            (interval->hi delta-env))))))
      t)
     (t (and (nondecreasing-time tprev tnext)
             (time-consistent-when-signal-doesnt-change in-prev in-next)
             (time-consistent-when-signal-doesnt-change out-prev out-next)
             (time-set-when-signal-change in-prev in-next tnext)
             (time-set-when-signal-change out-prev out-next tnext)
             ))))
  )

(define env-valid ((e env-p)
                   (tr gtrace-p))
  :returns (ok booleanp)
  :measure (len (gtrace-fix tr))
  :hints (("Goal" :in-theory (enable gtrace-fix)))
  (b* ((e (env-fix e))
       ((unless (consp (gtrace-fix (cdr (gtrace-fix tr))))) t)
       (first (car (gtrace-fix tr)))
       (rest (cdr (gtrace-fix tr)))
       (second (car (gtrace-fix rest)))
       ((unless (env-step e
                          (gstate-t->statet first)
                          (gstate-t->statev first)
                          (gstate-t->statet second)
                          (gstate-t->statev second)))
        nil))
    (env-valid e rest)))

;; ------------------------------------------------------------
;;         define connection function of env to an asp-stage

(define asp-connection ((a asp-stage-p) (el env-p) (er env-p))
  :returns (ok booleanp)
  (and (equal (asp-stage->go-full a)
              (env->output el))
       (equal (asp-stage->empty a)
              (env->input el))
       (equal (asp-stage->go-empty a)
              (env->output er))
       (equal (asp-stage->full a)
              (env->input er))
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
                (env-p el)
                (env-p er)
                (asp-connection a el er)
                (gtrace-p tr)
                (env-valid el tr)
                (env-valid er tr)
                (asp-valid a tr)
                (valid-interval (asp-stage->delta-t1 a))
                (valid-interval (asp-stage->delta-t2 a))
                (valid-interval (env->delta-env el))
                (valid-interval (env->delta-env er))
                (consp (gtrace-fix tr))
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
                                                 :level 1)
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
