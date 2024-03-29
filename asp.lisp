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

(include-book "env")

;; --------------------------------------
(defprod asp-stage
  ((go-full sig-path-p)
   (empty sig-path-p)
   (go-empty sig-path-p)
   (full sig-path-p)
   (full-internal sig-path-p)

   (left renv-p)
   (right lenv-p)

   (delta delay-interval-p)))

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
                                (cons go-empty (sig-path-list-fix
                                                nil))))))))))))


(define asp-internal-connection ((a asp-stage-p))
  :returns (ok booleanp)
  (and (equal (asp-stage->go-full a)
              (renv->req-in (asp-stage->left a)))
       (equal (asp-stage->empty a)
              (renv->ack-out (asp-stage->left a)))
       (equal (asp-stage->go-empty a)
              (lenv->ack-in (asp-stage->right a)))
       (equal (asp-stage->full a)
              (lenv->req-out (asp-stage->right a)))
       (equal (asp-stage->full-internal a)
              (lenv->left-internal (asp-stage->right a)))
       (equal (renv->right-internal (asp-stage->left a))
              (asp-stage->full-internal a))
       (equal (asp-stage->delta a)
              (lenv->delta (asp-stage->right a)))
       (equal (asp-stage->delta a)
              (renv->delta (asp-stage->left a)))
       ))

;; =====================================================
;; stepping function
(define asp-step ((a asp-stage-p)
                  (prev gstate-t-p)
                  (next gstate-t-p))
  :returns (ok booleanp)
  (b* ((a (asp-stage-fix a)))
    (and (renv-step (asp-stage->left a) prev next)
         (lenv-step (asp-stage->right a) prev next))))

(define asp-valid ((a asp-stage-p)
                   (tr gtrace-p))
  :returns (ok booleanp)
  :measure (len (gtrace-fix tr))
  :hints (("Goal" :in-theory (enable gtrace-fix)))
  (b* ((a (asp-stage-fix a))
       ((unless (consp (gtrace-fix tr))) t)
       (first (car (gtrace-fix tr)))
       (rest (cdr (gtrace-fix tr)))
       ((unless (consp (gtrace-fix rest))) t)
       (second (car (gtrace-fix rest))))
    (and (asp-step a first second)
         (asp-valid a rest))))

;; ------------------------------------------------------------
;;         define connection function of env to an asp-stage

(define asp-connection ((a asp-stage-p) (el lenv-p) (er renv-p))
  :returns (ok booleanp)
  (and (env-connection el (asp-stage->left a))
       (env-connection (asp-stage->right a) er)))

;; ========================================================================================
;;    The invariant
(define invariant-asp-stage ((a asp-stage-p)
                             (el lenv-p) (er renv-p)
                             (curr gstate-t-p))
  :returns (ok booleanp)
  (b* (((asp-stage a) (asp-stage-fix a)))
    (and (invariant-env el (asp-stage->left a) curr)
         (invariant-env (asp-stage->right a) er curr))))

(define invariant-asp-stage-trace ((a asp-stage-p) (el lenv-p) (er renv-p)
                                   (tr gtrace-p))
  :returns (ok booleanp)
  :measure (len tr)
  (b* ((tr (gtrace-fix tr))
       ((unless (consp (gtrace-fix tr))) t)
       (first (car (gtrace-fix tr)))
       (rest (cdr (gtrace-fix tr)))
       ((unless (consp (gtrace-fix rest))) t))
    (and (invariant-asp-stage a el er first)
         (invariant-asp-stage-trace a el er rest))))

;; funny how this one takes a long time
;; (std::must-fail
;;  (defthm invariant-check-contradiction
;;    (not (and (asp-stage-p a)
;;              (lenv-p el)
;;              (renv-p er)
;;              (asp-internal-connection a)
;;              (asp-connection a el er)
;;              (gstate-t-p s1)
;;              (gstate-t-p s2)
;;              (lenv-step el s1 s2)
;;              (renv-step er s1 s2)
;;              (asp-step a s1 s2)
;;              (valid-interval (asp-stage->delta a))
;;              (valid-interval (lenv->delta el))
;;              (valid-interval (renv->delta er))
;;              (equal (asp-stage->delta a)
;;                     (lenv->delta el))
;;              (equal (asp-stage->delta a)
;;                     (renv->delta er))
;;              (invariant-asp-stage a el er s1)))
;;    :hints (("Goal"
;;             :smtlink
;;             (:fty (asp-stage lenv renv time-interval delay-interval
;;                              gtrace sig-value gstate gstate-t
;;                              sig-path-list sig-path sig sig-target
;;                              asp-env-testbench asp-my-bench integer-list
;;                              sig-value-list maybe-rational)
;; 	                :functions ((sigs-in-bool-table :formals ((sigs sig-path-listp)
;; 						                                                (st gstate-p))
;; 					                                        :returns ((ok booleanp))
;; 					                                        :level 5))
;;                   :evilp t
;;                   ))))
;;  )

(defthm invariant-asp-stage-step-thm
  (implies (and (asp-stage-p a)
                (lenv-p el)
                (renv-p er)
                (asp-internal-connection a)
                (asp-connection a el er)
                (gstate-t-p s1)
                (gstate-t-p s2)
                (lenv-step el s1 s2)
                (renv-step er s1 s2)
                (asp-step a s1 s2)
                (valid-interval (asp-stage->delta a))
                (valid-interval (lenv->delta el))
                (valid-interval (renv->delta er))
                (equal (asp-stage->delta a)
                       (lenv->delta el))
                (equal (asp-stage->delta a)
                       (renv->delta er))
                (invariant-asp-stage a el er s1))
           (invariant-asp-stage a el er s2))
  :hints (("Goal"
           :smtlink
           (:fty (asp-stage lenv renv time-interval delay-interval
                            gtrace sig-value gstate gstate-t
                            sig-path-list sig-path sig sig-target
                            asp-env-testbench asp-my-bench integer-list
                            sig-value-list maybe-rational)
	               :functions ((sigs-in-bool-table :formals ((sigs sig-path-listp)
						                                               (st gstate-p))
					                                       :returns ((ok booleanp))
					                                       :level 5))
                 :evilp t
                 ))))

;; --------------------------------------------------

(define asp-gate-hazard-free-step ((a asp-stage-p)
                                   (s gstate-t-p))
  :returns (v booleanp)
  :guard-hints (("Goal" :in-theory (e/d (sigs-in-bool-table
                                         asp-sigs)
                                        ())))
  (b* (((asp-stage a) (asp-stage-fix a))
       ((gstate-t s) (gstate-t-fix s))
       ((unless (sigs-in-bool-table (asp-sigs a) s.statev)) nil)
       (gf (state-get a.go-full s.statev))
       (em (state-get a.empty s.statev))
       (ge (state-get a.go-empty s.statev))
       (fl (state-get a.full s.statev))
       (fi (state-get a.full-internal s.statev)))
    (implies (and (sig-value->value gf)
                  (sig-value->value em)
                  (sig-value->value ge)
                  (sig-value->value fl))
             (and (implies (sig-value->value fi)
                           (< s.statet
                              (+ (max (sig-value->time ge)
                                      (sig-value->time fl))
                                 (delay-interval->lo a.delta))))
                  (implies (not (sig-value->value fi))
                           (< s.statet
                              (+ (max (sig-value->time gf)
                                      (sig-value->time em))
                                 (delay-interval->lo a.delta))))))))

(define asp-stage-hazard-free-step ((a asp-stage-p)
                                    (s1 gstate-t-p)
                                    (s2 gstate-t-p))
  :returns (v booleanp)
  (b* (((asp-stage a) (asp-stage-fix a)))
    (and (renv-hazard-free-step a.left s1 s2)
         (lenv-hazard-free-step a.right s1 s2)
         (asp-gate-hazard-free-step a s1)
         (asp-gate-hazard-free-step a s2))))

(defthm asp-stage-hazard-free-thm-lemma
  (implies (and (asp-stage-p a)
                (lenv-p el)
                (renv-p er)
                (asp-internal-connection a)
                (asp-connection a el er)
                (gstate-t-p s1)
                (gstate-t-p s2)
                (lenv-step el s1 s2)
                (renv-step er s1 s2)
                (asp-step a s1 s2)
                (valid-interval (asp-stage->delta a))
                (valid-interval (lenv->delta el))
                (valid-interval (renv->delta er))
                (equal (asp-stage->delta a)
                       (lenv->delta el))
                (equal (asp-stage->delta a)
                       (renv->delta er))
                (invariant-asp-stage a el er s1)
                (invariant-asp-stage a el er s2))
           (and (lenv-hazard-free-step el s1 s2)
                (renv-hazard-free-step er s1 s2)
                (asp-stage-hazard-free-step a s1 s2)))
  :hints (("Goal"
           :smtlink
           (:fty (asp-stage lenv renv time-interval delay-interval
                            gtrace sig-value gstate gstate-t
                            sig-path-list sig-path sig sig-target
                            asp-env-testbench asp-my-bench integer-list
                            sig-value-list maybe-rational)
                 :functions ((sigs-in-bool-table
                              :formals ((sigs sig-path-listp)
                                        (st gstate-p))
                              :returns ((ok booleanp))
                              :level 6))
                 :evilp t
                 ))))

(defthm asp-stage-hazard-free-thm
  (implies (and (asp-stage-p a)
                (lenv-p el)
                (renv-p er)
                (asp-internal-connection a)
                (asp-connection a el er)
                (gstate-t-p s1)
                (gstate-t-p s2)
                (lenv-step el s1 s2)
                (renv-step er s1 s2)
                (asp-step a s1 s2)
                (valid-interval (asp-stage->delta a))
                (valid-interval (lenv->delta el))
                (valid-interval (renv->delta er))
                (equal (asp-stage->delta a)
                       (lenv->delta el))
                (equal (asp-stage->delta a)
                       (renv->delta er))
                (invariant-asp-stage a el er s1))
           (and (lenv-hazard-free-step el s1 s2)
                (renv-hazard-free-step er s1 s2)
                (asp-stage-hazard-free-step a s1 s2))))

;; --------------------------------------------------
(define fi-step-oracle ((a asp-stage-p)
                        (s gstate-t-p))
  :returns (snext maybe-gstate-t-p)
  :guard-hints (("Goal" :in-theory (e/d (sigs-in-bool-table
                                         asp-sigs
                                         change-state)
                                        ())))
  (b* (((asp-stage a) (asp-stage-fix a))
       ((gstate-t s) s)
       ((unless (sigs-in-bool-table (asp-sigs a) s.statev))
        (maybe-gstate-t-fix nil))
       (fi (state-get a.full-internal s.statev))
       (gf (state-get a.go-full s.statev))
       (em (state-get a.empty s.statev))
       (ge (state-get a.go-empty s.statev))
       (fl (state-get a.full s.statev))
       ((sig-value fi) fi)
       ((sig-value gf) gf)
       ((sig-value em) em)
       ((sig-value ge) ge)
       ((sig-value fl) fl)
       (tnext1 (max s.statet
                    (+ (max gf.time em.time)
                       (delay-interval->lo a.delta))))
       (snext1 (change-state s a.full-internal t tnext1))
       (tnext2 (max s.statet
                    (+ (max ge.time fl.time)
                       (delay-interval->lo a.delta))))
       (snext2 (change-state s a.full-internal nil tnext2)))
    (cond ((and gf.value em.value (not fi.value)) (maybe-gstate-t-some snext1))
          ((and ge.value fl.value fi.value) (maybe-gstate-t-some snext2))
          (t (maybe-gstate-t-fix nil)))))

(define full-step-oracle ((a asp-stage-p)
                          (s gstate-t-p))
  :returns (snext maybe-gstate-t-p)
  :guard-hints (("Goal" :in-theory (e/d (sigs-in-bool-table
                                         asp-sigs)
                                        ())))
  (b* (((asp-stage a) (asp-stage-fix a))
       ((gstate-t s) s)
       ((unless (sigs-in-bool-table (asp-sigs a) s.statev))
        (maybe-gstate-t-fix nil))
       (fi (state-get a.full-internal s.statev))
       (fl (state-get a.full s.statev))
       ((sig-value fi) fi)
       ((sig-value fl) fl)
       (tnext (max s.statet
                   (+ fi.time (delay-interval->lo a.delta))))
       (snext (change-state s a.full fi.value tnext)))
    (if (not (equal fi.value fl.value))
        (maybe-gstate-t-some snext)
      (maybe-gstate-t-fix nil))))

(define empty-step-oracle ((a asp-stage-p)
                           (s gstate-t-p))
  :returns (snext maybe-gstate-t-p)
  :guard-hints (("Goal" :in-theory (e/d (sigs-in-bool-table
                                         asp-sigs)
                                        ())))
  (b* (((asp-stage a) (asp-stage-fix a))
       ((gstate-t s) s)
       ((unless (sigs-in-bool-table (asp-sigs a) s.statev))
        (maybe-gstate-t-fix nil))
       (fi (state-get a.full-internal s.statev))
       (em (state-get a.empty s.statev))
       ((sig-value fi) fi)
       ((sig-value em) em)
       (tnext (max s.statet
                   (+ fi.time (delay-interval->lo a.delta))))
       (snext (change-state s a.empty (not fi.value) tnext)))
    (if (equal fi.value em.value)
        (maybe-gstate-t-some snext)
      (maybe-gstate-t-fix nil))))

;; This is my first attempt at providing a witness for asp-stage-step.
;; This attempt isn't correct, because it proposes a change on
;; full-internal that either is allowed by left of asp-stage and disallowed
;; by right of asp-stage; or one that's allowed by the right but not by the
;; left. The correct proposer should disable such changes.
;; It's a pity because I don't get to use this below succinct (or lazy) way
;; of proposing next state then.
;; (maybe-gstate-merge (lenv-step-oracle a.right s inf)
;;                     (renv-step-oracle a.left s inf))
(define asp-stage-step-oracle ((a asp-stage-p)
                               (s gstate-t-p))
  :returns (snext maybe-gstate-t-p)
  (maybe-gstate-merge (empty-step-oracle a s)
                      (maybe-gstate-merge (fi-step-oracle a s)
                                          (full-step-oracle a s))))

(define asp-step-oracle ((el lenv-p)
                         (er renv-p)
                         (a asp-stage-p)
                         (s gstate-t-p))
  :returns (snext maybe-gstate-t-p)
  (maybe-gstate-merge (asp-stage-step-oracle a s)
                      (maybe-gstate-merge (lenv-step-oracle el s)
                                          (renv-step-oracle er s))))

(define asp-progress ((el lenv-p)
                      (er renv-p)
                      (a asp-stage-p)
                      (prev gstate-t-p)
                      (next gstate-t-p))
  :returns (pro? booleanp)
  (b* ((el (lenv-fix el))
       ((lenv el) el)
       (er (renv-fix er))
       ((renv er) er)
       (a (asp-stage-fix a))
       ((asp-stage a) a))
    (or (changed el.left-internal prev next)
        (changed el.req-out prev next)
        (changed er.right-internal prev next)
        (changed er.ack-out prev next)
        (changed a.full-internal prev next)
        (changed a.empty prev next)
        (changed a.full prev next))))

(define asp-distinct ((el lenv-p)
                      (er renv-p)
                      (a asp-stage-p))
  :returns (v booleanp)
  (b* (((lenv el) (lenv-fix el))
       ((renv er) (renv-fix er))
       ((asp-stage a) (asp-stage-fix a)))
    (and (equal el.left-internal
                (cons (make-sig :module 'sym :index 0) (sig-path-fix nil)))
         (equal er.right-internal
                (cons (make-sig :module 'sym :index 1) (sig-path-fix nil)))
         (equal a.empty
                (cons (make-sig :module 'sym :index 2) (sig-path-fix nil)))
         (equal a.go-full
                (cons (make-sig :module 'sym :index 3) (sig-path-fix nil)))
         (equal a.full-internal
                (cons (make-sig :module 'sym :index 4) (sig-path-fix nil)))
         (equal a.full
                (cons (make-sig :module 'sym :index 5) (sig-path-fix nil)))
         (equal a.go-empty
                (cons (make-sig :module 'sym :index 6) (sig-path-fix nil))))))

(defthm asp-deadlock-free
  (implies (and (asp-stage-p a)
                (lenv-p el)
                (renv-p er)
                (asp-internal-connection a)
                (asp-connection a el er)
                (gstate-t-p s1)
                (gstate-t-p s2)
                (valid-interval (asp-stage->delta a))
                (valid-interval (lenv->delta el))
                (valid-interval (renv->delta er))
                (equal (asp-stage->delta a)
                       (lenv->delta el))
                (equal (asp-stage->delta a)
                       (renv->delta er))
                (asp-distinct el er a)
                (invariant-asp-stage a el er s1)
                (invariant-asp-stage a el er s2)
                )
           (and (not (equal (asp-step-oracle el er a s1)
                            (maybe-gstate-t-fix nil)))
                (lenv-step el s1
                           (maybe-gstate-t-some->val
                            (asp-step-oracle el er a s1)))
                (renv-step er s1
                           (maybe-gstate-t-some->val
                            (asp-step-oracle el er a s1)))
                (asp-step a s1
                          (maybe-gstate-t-some->val
                           (asp-step-oracle el er a s1)))
                (asp-progress el er a s1
                              (maybe-gstate-t-some->val
                               (asp-step-oracle el er a s1)))))
  :hints (("Goal"
           :smtlink
           (:fty (asp-stage lenv renv time-interval delay-interval
                            gtrace sig-value gstate gstate-t
                            sig-path-list sig-path sig sig-target
                            asp-env-testbench asp-my-bench integer-list
                            sig-value-list maybe-gstate-t
                            maybe-rational)
                 :functions ((sigs-in-bool-table
                              :formals ((sigs sig-path-listp)
                                        (st gstate-p))
                              :returns ((ok booleanp))
                              :level 6))
                 :evilp t
                 ))))
