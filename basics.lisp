(in-package "ASP")
(include-book "std/util/define" :dir :system)
(include-book "tools/bstar" :dir :system)
(include-book "centaur/fty/top" :dir :system) ; for defalist, etc.
(include-book "misc/eval" :dir :system)
(include-book "projects/smtlink/top" :dir :system)

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

(define mr-+ ((a maybe-rational-p) (b maybe-rational-p))
  :returns (c maybe-rational-p)
  (b* ((a (maybe-rational-fix a))
       (b (maybe-rational-fix b)))
    (cond ((equal a (maybe-rational-fix nil)) (maybe-rational-fix nil))
          ((equal b (maybe-rational-fix nil)) (maybe-rational-fix nil))
          (t (maybe-rational-some
              (+ (maybe-rational-some->val a)
                 (maybe-rational-some->val b)))))))

(define mr-scaler-* ((a rationalp) (b maybe-rational-p))
  :returns (c maybe-rational-p)
  (b* ((b (maybe-rational-fix b))
       ((if (equal b (maybe-rational-fix nil)))
        (maybe-rational-fix nil)))
    (maybe-rational-some (* a (maybe-rational-some->val b)))))

(define mr-hi-<= ((a maybe-rational-p) (b rationalp))
  :returns (ok booleanp)
  (b* ((a (maybe-rational-fix a))
       ((if (equal a (maybe-rational-fix nil))) nil))
    (<= (maybe-rational-some->val a) b)))

(define mr-hi-< ((a maybe-rational-p) (b rationalp))
  :returns (ok booleanp)
  (b* ((a (maybe-rational-fix a))
       ((if (equal a (maybe-rational-fix nil))) nil))
    (< (maybe-rational-some->val a) b)))

(define mr-hi-> ((a maybe-rational-p) (b rationalp))
  :returns (ok booleanp)
  (b* ((a (maybe-rational-fix a))
       ((if (equal a (maybe-rational-fix nil))) t))
    (> (maybe-rational-some->val a) b)))

(define mr-hi-max ((a maybe-rational-p) (b maybe-rational-p))
  :returns (c maybe-rational-p)
  (b* ((a (maybe-rational-fix a))
       (b (maybe-rational-fix b)))
    (cond ((or (equal a (maybe-rational-fix nil))
               (equal b (maybe-rational-fix nil)))
           (maybe-rational-fix nil))
          ((>= (maybe-rational-some->val a)
               (maybe-rational-some->val b))
           a)
          (t b))))

(defprod delay-interval
  ((lo rationalp)
   (hi rationalp)))

(define valid-interval ((i delay-interval-p))
  :returns (ok booleanp)
  (b* ((i (delay-interval-fix i)))
    (and (> (delay-interval->lo i) 0)
         (< (delay-interval->lo i) (delay-interval->hi i))
         (> (* 2 (delay-interval->lo i)) (delay-interval->hi i)))))

(defprod time-interval
  ((lo rationalp)
   (hi maybe-rational-p)))

(define interval-add ((itv1 time-interval-p) (itv2 delay-interval-p))
  :returns (itv time-interval-p)
  (b* ((itv1 (time-interval-fix itv1))
       (itv2 (delay-interval-fix itv2)))
    (make-time-interval :lo (+ (time-interval->lo itv1)
                               (delay-interval->lo itv2))
                        :hi (mr-+ (time-interval->hi itv1)
                                  (maybe-rational-some
                                   (delay-interval->hi itv2))))))

;; (define interval-max ((itv1 interval-p) (itv2 interval-p))
;;   :returns (imax interval-p)
;;   (b* ((itv1 (interval-fix itv1))
;;        (itv2 (interval-fix itv2)))
;;     (make-interval :lo (max (interval->lo itv1)
;;                             (interval->lo itv2))
;;                    :hi (max (interval->hi itv1)
;;                             (interval->hi itv2)))))

;; ----------------------------------------------------
(defoption maybe-gstate-t gstate-t-p)

;; =====================================================
;; some handy functions for signals
(deflist sig-value-list
  :elt-type sig-value-p
  :true-listp t)

(defprod sig-target
  ((value booleanp)
   (time time-interval-p)))

(define sig-target-from-signal ((sig sig-value-p))
  :returns (target sig-target-p)
  (make-sig-target :value (sig-value->value sig)
                   :time  (make-time-interval
                           :lo (sig-value->time sig)
                           :hi (maybe-rational-some (sig-value->time sig)))))

(defun sig-macro-help (sigs)
  (if (consp sigs)
      `(sig-value-list-fix
        (cons ,(car sigs) ,(sig-macro-help (cdr sigs))))
    `(sig-value-list-fix nil)))

(define sig-and-fun ((sigs sig-value-list-p))
  :returns (v booleanp)
  :measure (len sigs)
  (b* ((sigs (sig-value-list-fix sigs))
       ((unless (consp (sig-value-list-fix sigs))) t)
       (hd (car (sig-value-list-fix sigs)))
       (tl (cdr (sig-value-list-fix sigs)))
       ((unless (sig-value->value hd)) nil))
    (sig-and-fun tl)))

;; Yan's temporary solution
(define sig-and2 ((siga sig-value-p) (sigb sig-value-p))
  :returns (p booleanp)
  (and (sig-value->value siga)
       (sig-value->value sigb)))

(defmacro sig-and (&rest rst)
  (list 'sig-and-fun (sig-macro-help rst)))

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
  :returns (v time-interval-p)
  (b* ((u (sig-max-time-help sigs currmax)))
    (make-time-interval
     :lo u
     :hi (maybe-rational-some u))))

;; Yan's temporary solution
(define sig-max-time1 ((sig0 sig-value-p))
  :returns (vv time-interval-p)
  (make-time-interval
   :lo (sig-value->time sig0)
   :hi (maybe-rational-some (sig-value->time sig0))))

(define sig-max-time2 ((sig0 sig-value-p) (sig1 sig-value-p))
  :returns (vv time-interval-p)
  (b* ((v (max (sig-value->time sig0) (sig-value->time sig1))))
    (make-time-interval
     :lo v
     :hi (maybe-rational-some v))))

(defmacro sig-max-time (sig0 &rest rst)
  (list 'sig-max-time-fun (sig-macro-help rst) (list 'sig-value->time sig0)))
;; `(sig-max-time-fun (list ,@rst) (sig-value->time ,sig0)))

(define sig-check-times ((prev sig-value-p)
                         (next sig-value-p)
                         (tprev rationalp)
                         (tnext rationalp))
  :returns (ok booleanp)
  (b* ((prev (sig-value-fix prev))
       (next (sig-value-fix next))
       ((unless (<= tprev tnext)) nil)
       ;; ((unless (<= 0 (sig-value->time prev))) nil)
       ((unless (<= (sig-value->time prev) (sig-value->time next))) nil)
       ;; ((unless (<= (sig-value->time prev) tprev)) nil)
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
                              (<= (time-interval->lo (sig-target->time target))
                                  tnext)
                              (mr-hi-> (time-interval->hi (sig-target->time target))
                                       tnext))))
        nil)
       ((unless (implies (not (equal (sig-value->value next)
                                     (sig-target->value target)))
                         (mr-hi-> (time-interval->hi (sig-target->time target))
                                  tnext)))
        nil))
    t))

(defmacro state-get (sig st)
  `(cdr (smt::magic-fix
         'sig-path_sig-value
         (assoc-equal ,sig (gstate-fix ,st)))))

(define change-state ((curr gstate-t-p)
                      (path sig-path-p)
                      (value booleanp)
                      (time rationalp))
  :returns (new-curr gstate-t-p)
  (b* (((gstate-t curr) (gstate-t-fix curr))
       (path (sig-path-fix path))
       (sv (make-sig-value :value value :time time))
       (new-statev (acons path sv (gstate-fix curr.statev))))
    (make-gstate-t :statev new-statev
                   :statet time)))

(define maybe-gstate-merge ((xgstate maybe-gstate-t-p)
                            (ygstate maybe-gstate-t-p))
  :returns (zgstate maybe-gstate-t-p)
  (b* ((xgstate (maybe-gstate-t-fix xgstate))
       (ygstate (maybe-gstate-t-fix ygstate))
       ((if (equal xgstate (maybe-gstate-t-fix nil))) ygstate)
       ((if (equal ygstate (maybe-gstate-t-fix nil))) xgstate)
       ((gstate-t x) (maybe-gstate-t-some->val xgstate))
       ((gstate-t y) (maybe-gstate-t-some->val ygstate))
       ((if (<= x.statet y.statet)) xgstate))
    ygstate))

(define changed ((p sig-path-p)
                 (prev gstate-t-p)
                 (next gstate-t-p))
  :returns (changed? booleanp)
  (b* ((p (sig-path-fix p))
       (prev (gstate-t->statev (gstate-t-fix prev)))
       (next (gstate-t->statev (gstate-t-fix next)))
       (prev-v (assoc-equal p (gstate-fix prev)))
       ((unless (consp (smt::magic-fix 'sig-path_sig-value prev-v)))
        nil)
       (next-v (assoc-equal p (gstate-fix next)))
       ((unless (consp (smt::magic-fix 'sig-path_sig-value next-v)))
        nil)
       ((if (equal prev-v next-v)) nil))
    t))

