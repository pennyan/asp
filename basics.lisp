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

(defprod interval
  ((lo rationalp)
   (hi rationalp)))

(define valid-interval ((i interval-p))
  :returns (ok booleanp)
  (b* ((i (interval-fix i)))
    (and (> (interval->lo i) 0)
         (< (interval->lo i) (interval->hi i))
         (> (* 2 (interval->lo i)) (interval->hi i)))))

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

;; ----------------------------------------------------
(defoption maybe-gstate-t gstate-t-p)

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
  :returns (v interval-p)
  (b* ((u (sig-max-time-help sigs currmax)))
    (make-interval :lo u :hi u)))

;; Yan's temporary solution
(define sig-max-time1 ((sig0 sig-value-p))
  :returns (vv interval-p)
  (make-interval :lo (sig-value->time sig0)
                 :hi (sig-value->time sig0)))

(define sig-max-time2 ((sig0 sig-value-p) (sig1 sig-value-p))
  :returns (vv interval-p)
  (b* ((v (max (sig-value->time sig0) (sig-value->time sig1))))
    (make-interval :lo v :hi v)))

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
                              (<= (interval->lo (sig-target->time target))
                                  tnext)
                              (<  tnext
                                  (interval->hi (sig-target->time target))))))
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
