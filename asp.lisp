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

   (delta interval-p)))

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
                  (next gstate-t-p)
                  (inf rationalp))
  :returns (ok booleanp)
  (b* ((a (asp-stage-fix a)))
    (and (renv-step (asp-stage->left a) prev next inf)
         (lenv-step (asp-stage->right a) prev next inf))))

(define asp-valid ((a asp-stage-p)
                   (tr gtrace-p)
                   (inf rationalp))
  :returns (ok booleanp)
  :measure (len (gtrace-fix tr))
  :hints (("Goal" :in-theory (enable gtrace-fix)))
  (b* ((a (asp-stage-fix a))
       ((unless (consp (gtrace-fix tr))) t)
       (first (car (gtrace-fix tr)))
       (rest (cdr (gtrace-fix tr)))
       ((unless (consp (gtrace-fix rest))) t)
       (second (car (gtrace-fix rest))))
    (and (asp-step a first second inf)
         (asp-valid a rest inf))))

;; ------------------------------------------------------------
;;         define connection function of env to an asp-stage

(define asp-connection ((a asp-stage-p) (el lenv-p) (er renv-p))
  :returns (ok booleanp)
  (and (equal (asp-stage->go-full a)
              (lenv->req-out el))
       (equal (asp-stage->empty a)
              (lenv->ack-in el))
       (equal (asp-stage->go-empty a)
              (renv->ack-out er))
       (equal (asp-stage->full a)
              (renv->req-in er))))

;; ========================================================================================
;;    The invariant
(define invariant-asp-stage ((a asp-stage-p)
                             (el lenv-p) (er renv-p)
                             (curr gstate-t-p)
                             (inf rationalp))
  :returns (ok booleanp)
  (b* (((asp-stage a) (asp-stage-fix a)))
    (and (< 0 inf)
         (invariant-env el (asp-stage->left a) curr inf)
         (invariant-env (asp-stage->right a) er curr inf))))

(define invariant-asp-stage-trace ((a asp-stage-p) (el lenv-p) (er renv-p)
                                   (tr gtrace-p) (inf rationalp))
  :returns (ok booleanp)
  :measure (len tr)
  (b* ((tr (gtrace-fix tr))
       ((unless (consp (gtrace-fix tr))) t)
       (first (car (gtrace-fix tr)))
       (rest (cdr (gtrace-fix tr)))
       ((unless (consp (gtrace-fix rest))) t))
    (and (invariant-asp-stage a el er first inf)
         (invariant-asp-stage-trace a el er rest inf))))

(std::must-fail
 (defthm invariant-check-contradiction
   (not (and (asp-stage-p a)
             (lenv-p el)
             (renv-p er)
             (rationalp inf)
             (asp-internal-connection a)
             (asp-connection a el er)
             (gtrace-p tr)
             (lenv-step el (car (gtrace-fix tr))
                        (car (gtrace-fix (cdr (gtrace-fix tr))))
                        inf)
             (renv-step er (car (gtrace-fix tr))
                        (car (gtrace-fix (cdr (gtrace-fix tr))))
                        inf)
             (asp-step a (car (gtrace-fix tr))
                       (car (gtrace-fix (cdr (gtrace-fix tr))))
                       inf)
             (valid-interval (asp-stage->delta a))
             (valid-interval (lenv->delta el))
             (valid-interval (renv->delta er))
             (equal (asp-stage->delta a)
                    (lenv->delta el))
             (equal (asp-stage->delta a)
                    (renv->delta er))
             (consp (gtrace-fix tr))
             (consp (gtrace-fix (cdr (gtrace-fix tr))))
             (invariant-asp-stage a el er (car (gtrace-fix tr)) inf)))
   :hints (("Goal"
            :smtlink
            (:fty (asp-stage lenv renv interval gtrace sig-value gstate gstate-t
                             sig-path-list sig-path sig sig-target
                             asp-env-testbench asp-my-bench integer-list
                             sig-value-list)
	                :functions ((sigs-in-bool-table :formals ((sigs sig-path-listp)
						                                                (st gstate-p))
					                                        :returns ((ok booleanp))
					                                        :level 5))
                  :evilp t
                  ))))
 )

(defthm invariant-asp-stage-step-thm
  (implies (and (asp-stage-p a)
                (lenv-p el)
                (renv-p er)
                (rationalp inf)
                (asp-internal-connection a)
                (asp-connection a el er)
                (gstate-t-p s1)
                (gstate-t-p s2)
                (lenv-step el s1 s2 inf)
                (renv-step er s1 s2 inf)
                (asp-step a s1 s2 inf)
                (valid-interval (asp-stage->delta a))
                (valid-interval (lenv->delta el))
                (valid-interval (renv->delta er))
                (equal (asp-stage->delta a)
                       (lenv->delta el))
                (equal (asp-stage->delta a)
                       (renv->delta er))
                (invariant-asp-stage a el er s1 inf))
           (invariant-asp-stage a el er s2 inf))
  :hints (("Goal"
           :smtlink
           (:fty (asp-stage lenv renv interval gtrace sig-value gstate gstate-t
                            sig-path-list sig-path sig sig-target
                            asp-env-testbench asp-my-bench integer-list
                            sig-value-list)
	               :functions ((sigs-in-bool-table :formals ((sigs sig-path-listp)
						                                               (st gstate-p))
					                                       :returns ((ok booleanp))
					                                       :level 5))
                 :evilp t
                 ))))

;; --------------------------------------------------

(define asp-stage-hazard-free-step ((a asp-stage-p)
                                    (s1 gstate-t-p)
                                    (s2 gstate-t-p))
  :returns (v booleanp)
  :guard-hints (("Goal" :in-theory (e/d (sigs-in-bool-table
                                         asp-sigs)
                                        ())))
  (b* (((asp-stage a) (asp-stage-fix a))
       ((gstate-t s1) (gstate-t-fix s1))
       ((gstate-t s2) (gstate-t-fix s2))
       ((unless (sigs-in-bool-table (asp-sigs a) s1.statev)) nil)
       ((unless (sigs-in-bool-table (asp-sigs a) s2.statev)) nil)
       (gf-prev (state-get a.go-full s1.statev))
       (gf-next (state-get a.go-full s2.statev))
       (em-prev (state-get a.empty s1.statev))
       (em-next (state-get a.empty s2.statev))
       (ge-prev (state-get a.go-empty s1.statev))
       (ge-next (state-get a.go-empty s2.statev))
       (fl-prev (state-get a.full s1.statev))
       (fl-next (state-get a.full s2.statev)))
    (and (renv-hazard-free-step a.left s1 s2)
         (lenv-hazard-free-step a.right s1 s2)
         ;; (not (and (sig-value->value gf-prev)
         ;;           (sig-value->value em-prev)
         ;;           (sig-value->value ge-prev)
         ;;           (sig-value->value fl-prev)))
         ;; (not (and (sig-value->value gf-next)
         ;;           (sig-value->value em-next)
         ;;           (sig-value->value ge-next)
         ;;           (sig-value->value fl-next)))
         )))

(defthm asp-stage-hazard-free-thm-lemma
  (implies (and (asp-stage-p a)
                (lenv-p el)
                (renv-p er)
                (rationalp inf)
                (asp-internal-connection a)
                (asp-connection a el er)
                (gstate-t-p s1)
                (gstate-t-p s2)
                (rationalp inf)
                (lenv-step el s1 s2 inf)
                (renv-step er s1 s2 inf)
                (asp-step a s1 s2 inf)
                (valid-interval (asp-stage->delta a))
                (valid-interval (lenv->delta el))
                (valid-interval (renv->delta er))
                (equal (asp-stage->delta a)
                       (lenv->delta el))
                (equal (asp-stage->delta a)
                       (renv->delta er))
                (invariant-asp-stage a el er s1 inf)
                (invariant-asp-stage a el er s2 inf))
           (and (lenv-hazard-free-step el s1 s2)
                (renv-hazard-free-step er s1 s2)
                (asp-stage-hazard-free-step a s1 s2)))
  :hints (("Goal"
           :smtlink
           (:fty (asp-stage lenv renv interval gtrace sig-value gstate gstate-t
                            sig-path-list sig-path sig sig-target
                            asp-env-testbench asp-my-bench integer-list
                            sig-value-list)
                 :functions ((sigs-in-bool-table
                              :formals ((sigs sig-path-listp)
                                        (st gstate-p))
                              :returns ((ok booleanp))
                              :level 6))
                 :evilp t
                 :smt-fname "x.py"
                 :smt-dir "smtpy"
                 ))))
