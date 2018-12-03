(in-package "ASP")
(include-book "asp")

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

(test-invariant-macro (nil (5 4) (3 2) (9 8) (11 10) (7 6) (1 0))
                      ((8 10) (8 10) (8 10))
                      ((t 0) (nil 0) (nil 0) (t 0) (t 8) (nil 8) (nil 8))
                      ((t 0) (t 169719/10000) (t 169719/10000)
                       (t 0) (t 8) (nil 8) (nil 8))
                      8 169719/10000)
