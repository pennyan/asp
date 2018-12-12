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

(define pretty-print (failed-clauses)
  :guard t
  (if failed-clauses failed-clauses 'passed))

(set-ignore-ok t)
(define test-invariant ((sigs t) (deltas t)
                        (curr t) (tcurr t)
                        (inf t))
  :irrelevant-formals-ok t
  :verify-guards nil
  (b* (((unless (and (true-listp sigs)
                     (true-listp deltas)
                     (true-listp curr)))
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
       (curr `(list (cons ,go-full ,(test-sig-value (nth 0 curr)))
                    (cons ,go-empty ,(test-sig-value (nth 1 curr)))
                    (cons ,full ,(test-sig-value (nth 2 curr)))
                    (cons ,empty ,(test-sig-value (nth 3 curr)))
                    (cons ,full-internal ,(test-sig-value (nth 4 curr)))
                    (cons ,left-internal ,(test-sig-value (nth 5 curr)))
                    (cons ,right-internal ,(test-sig-value (nth 6 curr)))))
       (go-empty `(cdr (assoc-equal ,go-empty ,curr)))
       (go-full `(cdr (assoc-equal ,go-full ,curr)))
       (empty `(cdr (assoc-equal ,empty ,curr)))
       (full `(cdr (assoc-equal ,full ,curr)))
       (full-internal `(cdr (assoc-equal ,full-internal ,curr)))
       (left-internal `(cdr (assoc-equal ,left-internal ,curr)))
       (right-internal `(cdr (assoc-equal ,right-internal ,curr)))
       (inv `(invariant ,test-stage ,test-lenv ,test-renv ,tcurr ,curr ,inf))
       (inv-stage `(invariant-stage-failed ,go-full ,go-empty ,full ,empty
                                           ,full-internal ,delta-stage ,tcurr))
       (inv-lenv `(invariant-lenv-failed ,go-full ,empty ,left-internal ,delta-lenv ,tcurr))
       (inv-renv `(invariant-renv-failed ,go-empty ,full ,right-internal ,delta-renv ,tcurr))
       (inv-interact-lenv `(interact-lenv-failed ,go-full ,go-empty ,full ,empty
                                                 ,full-internal
                                                 ,left-internal ,right-internal
                                                 ,delta-stage ,inf))
       (inv-interact-renv `(interact-renv-failed ,go-full ,go-empty ,full ,empty
                                                 ,full-internal
                                                 ,left-internal ,right-internal
                                                 ,delta-stage ,inf))
       )
    `(progn$
      (cw "Current signal values:~%left-internal = ~q0, go-full = ~q1, empty = ~q2, full-internal = ~q3, full = ~q4, go-empty = ~q5, right-internal = ~q6"
          ,left-internal ,go-full ,empty ,full-internal ,full ,go-empty ,right-internal)
      (cw "~%Testing the whole invariant on curr state: ~q0" (if ,inv 'passed 'failed))
      (cw "Testing invariant on the stage: ~q0" (pretty-print ,inv-stage))
      (cw "Testing invariant on the left env: ~q0" (pretty-print ,inv-lenv))
      (cw "Testing invariant on the right env: ~q0" (pretty-print ,inv-renv))
      (cw "Testing invariant on the interaction with left env: ~q0"
          (pretty-print ,inv-interact-lenv))
      (cw "Testing invariant on the interaction with right env: ~q0"
          (pretty-print ,inv-interact-renv))
      )))

(defmacro test-invariant-macro (sigs deltas curr tcurr)
  (b* ((cmd (test-invariant sigs deltas curr tcurr 1000))
       ;; (- (cw "cmd: ~q0" cmd))
       )
    cmd))

;;(test-invariant-macro ((9 8) (5 4) (3 2) nil (11 10) (7 6) (1 0))
;;                      ((8 10) (8 10) (8 10))
;;                      ;; go-full go-empty full empty
;;                      ((nil 1) (t 0) (nil 7) (t 0) (t 8) (t 70609/10000) (t 8))
;;                      ;; ((nil 1) (t 0) (t 16) (t 0) (t 8) (t 70609/10000) (t 8))
;;                      8
;;                      ;; 16
;;                      )

