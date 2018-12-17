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
(define test-invariant ((sigs t) (delta t)
                        (curr t) (tcurr t)
                        (inf t))
  :irrelevant-formals-ok t
  :verify-guards nil
  (b* (((unless (and (true-listp sigs)
                     (true-listp delta)
                     (true-listp curr)))
        nil)
       (li (test-sig (nth 0 sigs)))
       (req (test-sig (nth 1 sigs)))
       (ack (test-sig (nth 2 sigs)))
       (ri (test-sig (nth 3 sigs)))
       (delta (test-delta delta))
       (test-lenv `(make-lenv :ack-in ,ack
                              :req-out ,req
                              :left-internal ,li
                              :delta ,delta))
       (test-renv `(make-renv :req-in ,req
                              :ack-out ,ack
                              :right-internal ,ri
                              :delta ,delta))
       (curr `(list (cons ,li ,(test-sig-value (nth 0 curr)))
                    (cons ,req ,(test-sig-value (nth 1 curr)))
                    (cons ,ack ,(test-sig-value (nth 2 curr)))
                    (cons ,ri ,(test-sig-value (nth 3 curr)))))
       (li `(cdr (assoc-equal ,li ,curr)))
       (req `(cdr (assoc-equal ,req ,curr)))
       (ack `(cdr (assoc-equal ,ack ,curr)))
       (ri `(cdr (assoc-equal ,ri ,curr)))
       (inv `(invariant ,test-lenv ,test-renv ,tcurr ,curr ,inf))
       (testbench `(make-asp-env-testbench
                    :req ,req
                    :ack ,ack
                    :li ,li
                    :ri ,ri
                    :delta ,delta
                    :inf ,inf))
       (inv-lenv `(invariant-lenv-failed ,testbench ,tcurr))
       (inv-renv `(invariant-renv-failed ,testbench ,tcurr))
       (inv-interact-env `(interact-env-failed ,testbench))
       )
    `(progn$
      (cw "Current signal values:~%left-internal = ~q0, req = ~q1, ack = ~q2, right-internal = ~q3"
          ,li ,req ,ack ,ri)
      (cw "~%Testing the whole invariant on curr state: ~q0" (if ,inv 'passed 'failed))
      (cw "Testing invariant on the left env: ~q0" (pretty-print ,inv-lenv))
      (cw "Testing invariant on the right env: ~q0" (pretty-print ,inv-renv))
      (cw "Testing invariant on the interaction between envs: ~q0"
          (pretty-print ,inv-interact-env))
      )))

(defmacro test-invariant-macro (sigs delta curr tcurr)
  (b* ((cmd (test-invariant sigs delta curr tcurr 1000))
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

