(in-package "ASP")
;; (include-book "asp")

(define test-sig ((sig t))
  (b* (((unless (and (true-listp sig)
                     (consp sig)
                     (natp (nth 0 sig))))
        nil)
       (sym (intern$ (str::cat "sym" (str::natstr (nth 0 sig)))
                     "ASP")))
    `(list (make-sig :module ',sym :index ,(nth 1 sig)))))

(define test-delta ((delta t))
  (b* (((unless (true-listp delta))
        nil))
    `(make-interval
      :lo ,(nth 0 delta)
      :hi ,(nth 1 delta))))

(define test-sig-value ((sigv t))
  (b* (((unless (true-listp sigv))
        nil))
    `(make-sig-value :value ,(nth 0 sigv)
                     :time ,(nth 1 sigv))))

(set-ignore-ok t)
(define test-invariant ((sigs t) (deltas t)
                        (prev t) (next t)
                        (tprev t) (tnext t)
                        (inf t))
  :irrelevant-formals-ok t
  (declare (ignorable tprev prev))
  (b* (((unless (and (true-listp sigs)
                     (true-listp deltas)
                     (true-listp prev)
                     (true-listp next)))
        nil)
       (go-full (test-sig (nth 0 sigs)))
       (go-empty (test-sig (nth 1 sigs)))
       (full (test-sig (nth 2 sigs)))
       (empty (test-sig (nth 3 sigs)))
       (full-internal (test-sig (nth 4 sigs)))
       (left-internal (test-sig (nth 5 sigs)))
       (right-internal (test-sig (nth 6 sigs)))
       (delta-stage (test-delta (nth 0 deltas)))
       (delta-lenv (test-delta (nth 1 deltas)))
       (delta-renv (test-delta (nth 2 deltas)))
       (test-stage `(make-asp-stage :go-full ,go-full
                                    :go-empty ,go-empty
                                    :full ,full
                                    :empty ,empty
                                    :full-internal ,full-internal
                                    :delta ,delta-stage
                                    ))
       (test-lenv `(make-lenv :empty ,empty
                              :go-full ,go-full
                              :left-internal ,left-internal
                              :delta ,delta-lenv))
       (test-renv `(make-renv :full ,full
                              :go-empty ,go-empty
                              :right-internal ,right-internal
                              :delta ,delta-renv))
       (prev `(list (cons ,go-full ,(test-sig-value (nth 0 prev)))
                    (cons ,go-empty ,(test-sig-value (nth 1 prev)))
                    (cons ,full ,(test-sig-value (nth 2 prev)))
                    (cons ,empty ,(test-sig-value (nth 3 prev)))
                    (cons ,full-internal ,(test-sig-value (nth 4 prev)))
                    (cons ,left-internal ,(test-sig-value (nth 5 prev)))
                    (cons ,right-internal ,(test-sig-value (nth 6 prev)))))
       (next `(list (cons ,go-full ,(test-sig-value (nth 0 next)))
                    (cons ,go-empty  ,(test-sig-value (nth 1 next)))
                    (cons ,full  ,(test-sig-value (nth 2 next)))
                    (cons ,empty  ,(test-sig-value (nth 3 next)))
                    (cons ,full-internal  ,(test-sig-value (nth 4 next)))
                    (cons ,left-internal  ,(test-sig-value (nth 5 next)))
                    (cons ,right-internal  ,(test-sig-value (nth 6 next)))))
       (inv `(invariant ,test-stage ,test-lenv ,test-renv ,tnext ,next ,inf))
       (inv-stage `(invariant-stage ,test-stage ,tnext ,next))
       (inv-lenv `(invariant-lenv ,test-lenv ,tnext ,next))
       (inv-renv `(invariant-renv ,test-renv ,tnext ,next))
       (inv-interact-lenv `(interact-lenv ,test-stage ,test-lenv ,test-renv
                                          ,next ,inf))
       (inv-interact-renv `(interact-renv ,test-stage ,test-lenv ,test-renv
                                          ,next ,inf))
       )
    `(progn$
      (cw "Testing invariant on next state: ~q0~%" ,inv)
      (cw "Testing invariant on the stage: ~q0~%" ,inv-stage)
      (cw "Testing invariant on the left env: ~q0~%" ,inv-lenv)
      (cw "Testing invariant on the right env: ~q0~%" ,inv-renv)
      (cw "Testing invariant on the interaction with left env: ~q0~%" ,inv-interact-lenv)
      (cw "Testing invariant on the interaction with right env: ~q0~%" ,inv-interact-renv)
      )))

(defmacro test-invariant-macro (sigs deltas prev next tprev tnext)
  (b* ((cmd (test-invariant sigs deltas prev next tprev tnext 1000))
       (- (cw "cmd: ~q0" cmd)))
    cmd))

(test-invariant-macro ((11 10) (5 4) (3 2) (9 8) (13 12) (7 6) (1 0))
                      ((8 10) (8 10) (8 10))
                      ;; go-full go-empty full empty 
                      ((nil 7) (t 0) (t 0) (nil 6) (nil 8) (t 8) (t 8))
                      ((t 16) (t 0) (t 0) (t 16) (nil 8) (t 8) (t 8))
                      8 16)

(b* ((el (MAKE-LENV :EMPTY (LIST (MAKE-SIG :MODULE '|sym9| :INDEX 8))
                    :GO-FULL (LIST (MAKE-SIG :MODULE '|sym11| :INDEX 10))
                    :LEFT-INTERNAL (LIST (MAKE-SIG :MODULE '|sym7| :INDEX 6))
                    :DELTA (MAKE-INTERVAL :LO 8 :HI 10)))
     (er (MAKE-RENV :FULL (LIST (MAKE-SIG :MODULE '|sym3| :INDEX 2))
                    :GO-EMPTY (LIST (MAKE-SIG :MODULE '|sym5| :INDEX 4))
                    :RIGHT-INTERNAL (LIST (MAKE-SIG :MODULE '|sym1| :INDEX 0))
                    :DELTA (MAKE-INTERVAL :LO 8 :HI 10)))
     (a (MAKE-ASP-STAGE
         :GO-FULL (LIST (MAKE-SIG :MODULE '|sym11| :INDEX 10))
         :GO-EMPTY (LIST (MAKE-SIG :MODULE '|sym5| :INDEX 4))
         :FULL (LIST (MAKE-SIG :MODULE '|sym3| :INDEX 2))
         :EMPTY (LIST (MAKE-SIG :MODULE '|sym9| :INDEX 8))
         :FULL-INTERNAL (LIST (MAKE-SIG :MODULE '|sym13| :INDEX 12))
         :DELTA (MAKE-INTERVAL :LO 8 :HI 10)))
     (tcurr 16)
     (inf 1000)
     (curr (LIST (CONS (LIST (MAKE-SIG :MODULE '|sym11| :INDEX 10))
                       (MAKE-SIG-VALUE :VALUE T :TIME 16))
                 (CONS (LIST (MAKE-SIG :MODULE '|sym5| :INDEX 4))
                       (MAKE-SIG-VALUE :VALUE T :TIME 0))
                 (CONS (LIST (MAKE-SIG :MODULE '|sym3| :INDEX 2))
                       (MAKE-SIG-VALUE :VALUE T :TIME 0))
                 (CONS (LIST (MAKE-SIG :MODULE '|sym9| :INDEX 8))
                       (MAKE-SIG-VALUE :VALUE T :TIME 16))
                 (CONS (LIST (MAKE-SIG :MODULE '|sym13| :INDEX 12))
                       (MAKE-SIG-VALUE :VALUE NIL :TIME 8))
                 (CONS (LIST (MAKE-SIG :MODULE '|sym7| :INDEX 6))
                       (MAKE-SIG-VALUE :VALUE T :TIME 8))
                 (CONS (LIST (MAKE-SIG :MODULE '|sym1| :INDEX 0))
                       (MAKE-SIG-VALUE :VALUE T :TIME 8))))
       ((unless (sigs-in-bool-table (asp-sigs a) curr)) nil)
       ((unless (sigs-in-bool-table (lenv-sigs el) curr)) nil)
       ((unless (sigs-in-bool-table (renv-sigs er) curr)) nil)
       (go-empty (asp-stage->go-empty a))
       (go-full (asp-stage->go-full a))
       (empty (asp-stage->empty a))
       (full (asp-stage->full a))
       (full-internal (asp-stage->full-internal a))
       (left-internal (lenv->left-internal el))
       (right-internal (renv->right-internal er))
       (delta (asp-stage->delta a))
       (go-empty-curr (cdr (smt::magic-fix
                           'sig-path_sig-value
                           (assoc-equal go-empty (gstate-fix curr)))))
       (go-full-curr (cdr (smt::magic-fix
                           'sig-path_sig-value
                           (assoc-equal go-full (gstate-fix curr)))))
       (empty-curr (cdr (smt::magic-fix
                         'sig-path_sig-value
                         (assoc-equal empty (gstate-fix curr)))))
       (full-curr (cdr (smt::magic-fix
                         'sig-path_sig-value
                         (assoc-equal full (gstate-fix curr)))))
       (full-internal-curr (cdr (smt::magic-fix
                                 'sig-path_sig-value
                                 (assoc-equal full-internal
                                              (gstate-fix curr)))))
       (left-internal-curr (cdr (smt::magic-fix
                                 'sig-path_sig-value
                                 (assoc-equal left-internal
                                              (gstate-fix curr)))))
       (right-internal-curr (cdr (smt::magic-fix
                                  'sig-path_sig-value
                                  (assoc-equal right-internal
                                               (gstate-fix curr))))))
    (and
     ;; constraints for empty and go-full
     ;; full-internal fated to go to t
     (if (or (equal (full-internal-next-t empty-curr go-full-curr
                                          full-internal-curr
                                          left-internal-curr
                                          delta inf)
                    (maybe-interval-fix nil))
             (equal (go-full-next-nil go-full-curr left-internal-curr
                                      empty-curr delta)
                    (maybe-interval-fix nil)))
         t
       (implies (and (sig-value->value empty-curr)
                     (sig-value->value go-full-curr)
                     (not (sig-value->value full-internal-curr)))
                (< (interval->hi
                    (maybe-interval-some->val
                     (full-internal-next-t empty-curr go-full-curr
                                           full-internal-curr
                                           left-internal-curr
                                           delta inf)))
                   (interval->lo
                    (maybe-interval-some->val
                     (go-full-next-nil go-full-curr left-internal-curr
                                       empty-curr delta))))))
     ;; empty fated to go to nil
     (if (or (equal (empty-next-nil empty-curr go-full-curr
                                    full-internal-curr
                                    left-internal-curr
                                    delta inf)
                    (maybe-interval-fix nil))
             (equal (go-full-next-t go-full-curr left-internal-curr
                                    empty-curr
                                    delta inf)
                    (maybe-interval-fix nil)))
         t
       (implies (and (sig-value->value empty-curr)
                     (or (sig-value->value go-full-curr)
                         (sig-value->value full-internal-curr)))
                (< (interval->hi
                    (maybe-interval-some->val
                     (empty-next-nil empty-curr go-full-curr
                                     full-internal-curr
                                     left-internal-curr
                                     delta inf)))
                   (interval->lo
                    (maybe-interval-some->val
                     (go-full-next-t go-full-curr left-internal-curr
                                     empty-curr
                                     delta inf))))))
     ;; go-full fated to go to nil --failed
     (if (or (equal (go-full-next-nil go-full-curr left-internal-curr
                                      empty-curr delta)
                    (maybe-interval-fix nil))
             (equal (empty-next-t empty-curr full-curr
                                  go-empty-curr
                                  full-internal-curr
                                  right-internal-curr
                                  delta inf)
                    (maybe-interval-fix nil)))
         t
       (implies (and (sig-value->value go-full-curr)
                     (or (sig-value->value empty-curr)
                         (not (sig-value->value left-internal-curr))))
                (< (interval->hi
                    (maybe-interval-some->val
                     (go-full-next-nil go-full-curr left-internal-curr
                                       empty-curr delta)))
                   (interval->lo
                    (maybe-interval-some->val
                     (empty-next-t empty-curr full-curr
                                   go-empty-curr
                                   full-internal-curr
                                   right-internal-curr
                                   delta inf))))))
     ))

(b* ((a (MAKE-ASP-STAGE
         :GO-FULL (LIST (MAKE-SIG :MODULE '|sym11| :INDEX 10))
         :GO-EMPTY (LIST (MAKE-SIG :MODULE '|sym5| :INDEX 4))
         :FULL (LIST (MAKE-SIG :MODULE '|sym3| :INDEX 2))
         :EMPTY (LIST (MAKE-SIG :MODULE '|sym9| :INDEX 8))
         :FULL-INTERNAL (LIST (MAKE-SIG :MODULE '|sym13| :INDEX 12))
         :DELTA (MAKE-INTERVAL :LO 8 :HI 10)))
     (tprev 8)
     (tnext 16)
     (prev (LIST (CONS (LIST (MAKE-SIG :MODULE '|sym11| :INDEX 10))
                       (MAKE-SIG-VALUE :VALUE nil :TIME 7))
                 (CONS (LIST (MAKE-SIG :MODULE '|sym5| :INDEX 4))
                       (MAKE-SIG-VALUE :VALUE T :TIME 0))
                 (CONS (LIST (MAKE-SIG :MODULE '|sym3| :INDEX 2))
                       (MAKE-SIG-VALUE :VALUE T :TIME 0))
                 (CONS (LIST (MAKE-SIG :MODULE '|sym9| :INDEX 8))
                       (MAKE-SIG-VALUE :VALUE nil :TIME 6))
                 (CONS (LIST (MAKE-SIG :MODULE '|sym13| :INDEX 12))
                       (MAKE-SIG-VALUE :VALUE NIL :TIME 8))
                 (CONS (LIST (MAKE-SIG :MODULE '|sym7| :INDEX 6))
                       (MAKE-SIG-VALUE :VALUE T :TIME 8))
                 (CONS (LIST (MAKE-SIG :MODULE '|sym1| :INDEX 0))
                       (MAKE-SIG-VALUE :VALUE T :TIME 8))))
       (next (LIST (CONS (LIST (MAKE-SIG :MODULE '|sym11| :INDEX 10))
                               (MAKE-SIG-VALUE :VALUE T :TIME 16))
                         (CONS (LIST (MAKE-SIG :MODULE '|sym5| :INDEX 4))
                               (MAKE-SIG-VALUE :VALUE T :TIME 0))
                         (CONS (LIST (MAKE-SIG :MODULE '|sym3| :INDEX 2))
                               (MAKE-SIG-VALUE :VALUE T :TIME 0))
                         (CONS (LIST (MAKE-SIG :MODULE '|sym9| :INDEX 8))
                               (MAKE-SIG-VALUE :VALUE T :TIME 16))
                         (CONS (LIST (MAKE-SIG :MODULE '|sym13| :INDEX 12))
                               (MAKE-SIG-VALUE :VALUE NIL :TIME 8))
                         (CONS (LIST (MAKE-SIG :MODULE '|sym7| :INDEX 6))
                               (MAKE-SIG-VALUE :VALUE T :TIME 8))
                         (CONS (LIST (MAKE-SIG :MODULE '|sym1| :INDEX 0))
                               (MAKE-SIG-VALUE :VALUE T :TIME 8))))
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
       ;; ;; full-internal specific constraints
       ;; (fi-target
       ;;  (full-internal-target full-prev empty-prev go-full-prev
       ;;                        go-empty-prev full-internal-prev))
       ;; (fi-time
       ;;  (full-internal-trigger-time full-prev empty-prev go-full-prev
       ;;                              go-empty-prev full-internal-prev))
       ;; ((unless (signal-transition-constraints full-internal-prev tnext
       ;;                                         full-internal-next fi-target
       ;;                                         fi-time delta))
       ;;  nil)
       ;; ;; full specific constraints
       (f-target (full-target full-prev full-internal-prev))
       (f-time (full-trigger-time full-prev full-internal-prev))
       ;; ((unless (signal-transition-constraints full-prev tnext full-next
       ;;                                         f-target f-time delta))
       ;;  nil)
       ;; ;; empty specific constraints
       ;; (e-target (empty-target empty-prev full-internal-prev))
       ;; (e-time (empty-trigger-time empty-prev full-internal-prev))
       ;; ((unless (signal-transition-constraints empty-prev tnext empty-next
       ;;                                         e-target e-time delta))
       ;;  nil)
       )
  (signal-transition-constraints full-prev tnext full-next
                                 f-target f-time delta))
