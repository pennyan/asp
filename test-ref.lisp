(in-package "ASP")
(include-book "std/util/define" :dir :system)
(include-book "tools/bstar" :dir :system)
(include-book "centaur/fty/top" :dir :system) ; for defalist, etc.
(include-book "rational2str")

(define pretty-print (failed-clauses)
  :guard t
  (if failed-clauses failed-clauses 'passed))

(define sig-value-to-string ((sv sig-value-p) (prec natp))
  :returns (s stringp)
  (b* (((unless (sig-value-p sv)) "???")
       ((sig-value sv) sv)
       (val  (coerce (if sv.value "t" "nil") 'list))
       (at   (coerce " @ " 'list))
       (tim (coerce (rational-to-string sv.time prec) 'list)))
    (coerce (append val at tim) 'string)))

(define interval-to-string ((iv interval-p) (prec natp))
  :returns (s stringp)
  (b* (((unless (interval-p iv)) "???")
       (prec (if (natp prec) prec 4))
       (lo (rational-to-string (interval->lo iv) prec))
       (hi (rational-to-string (interval->hi iv) prec)))
    (concatenate 'string "[" lo ", " hi ")")))

(define show-sig ((sig sig-path-p)
                  (st gstate-p)
                  (name stringp)
                  (prec natp))
  (b* ((sig (sig-path-fix sig))
       (st (gstate-fix st))
       (pair (assoc-equal sig st))
       ((unless pair)
        (cw "Sig ~p0 not found!~%" sig))
       (v (cdr (assoc-equal sig st))))
    (cw "  ~s0 = ~x1 @ ~s2~%" name (sig-value->value v)
        (rational-to-string (sig-value->time v) prec)
        :fmt-control-alist
        `((fmt-soft-right-margin . 1000)
          (fmt-hard-right-margin . 1000)))))

(define test ((cex t))
  :verify-guards nil
  (b* ((a (cdr (assoc 'a cex)))
       (el0 (cdr (assoc 'el0 cex)))
       (er0 (cdr (assoc 'er0 cex)))
       (el1 (cdr (assoc 'el1 cex)))
       (er1 (cdr (assoc 'er1 cex)))
       (el2 (cdr (assoc 'el2 cex)))
       (er2 (cdr (assoc 'er2 cex)))
       (s1 (cdr (assoc 's1 cex)))
       (s2 (cdr (assoc 's2 cex)))
       (inf (cdr (assoc 'inf cex)))
       (prec 8)
       (tprev (gstate-t->statet s1))
       (prevv (gstate-t->statev s1))
       (tnext (gstate-t->statet s2))
       (nextv (gstate-t->statev s2))
       (el0.li-path (lenv->left-internal el0))
       (el0.req-path (lenv->req-out el0))
       (er0.ack-path (renv->ack-out er0))
       (er0.ri-path (renv->right-internal er0))
       (el1.li-path (lenv->left-internal el1))
       (el1.req-path (lenv->req-out el1))
       (er1.ack-path (renv->ack-out er1))
       (er1.ri-path (renv->right-internal er1))

       (el2.li-path (lenv->left-internal el2))
       (a.gf-path (asp-stage->go-full a))
       (a.em-path (asp-stage->empty a))
       (a.fi-path (asp-stage->full-internal a))
       (a.fl-path (asp-stage->full a))
       (a.ge-path (asp-stage->go-empty a))
       (er2.ri-path  (renv->right-internal er2))
       (delta (asp-stage->delta a))
       (- (cw "-----------------------------------------------------~%"))
       (- (cw "(inf = ~s0,~% delta = [~s1, ~s2))~%"
              (rational-to-string inf prec)
              (rational-to-string (interval->lo delta) prec)
              (rational-to-string (interval->hi delta) prec)))
       (- (cw "prev: tprev = ~s0~%" (rational-to-string tprev prec)))
       (- (show-sig el0.li-path prevv "el0.li" prec))
       (- (show-sig el0.req-path prevv "el0.req" prec))
       (- (show-sig er0.ack-path prevv "er0.ack" prec))
       (- (show-sig er0.ri-path prevv "er0.ri" prec))
       (- (show-sig el1.li-path prevv "el1.li" prec))
       (- (show-sig el1.req-path prevv "el1.req" prec))
       (- (show-sig er1.ack-path prevv "er1.ack" prec))
       (- (show-sig er1.ri-path prevv "er1.ri" prec))

       (- (show-sig el2.li-path prevv "el2.li" prec))
       (- (show-sig a.gf-path prevv "a.gf" prec))
       (- (show-sig a.em-path prevv "a.em" prec))
       (- (show-sig a.fi-path prevv "a.fi" prec))
       (- (show-sig a.fl-path prevv "a.fl" prec))
       (- (show-sig a.ge-path prevv "a.ge" prec))
       (- (show-sig er2.ri-path prevv "er2.ri" prec))
       (- (cw "next: tnext = ~s0~%" (rational-to-string tnext prec)))
       (- (show-sig el0.li-path nextv "el0.li" prec))
       (- (show-sig el0.req-path nextv "el0.req" prec))
       (- (show-sig er0.ack-path nextv "er0.ack" prec))
       (- (show-sig er0.ri-path nextv "er0.ri" prec))
       (- (show-sig el1.li-path nextv "el1.li" prec))
       (- (show-sig el1.req-path nextv "el1.req" prec))
       (- (show-sig er1.ack-path nextv "er1.ack" prec))
       (- (show-sig er1.ri-path nextv "er1.ri" prec))

       (- (show-sig el2.li-path nextv "el2.li" prec))
       (- (show-sig a.gf-path nextv "a.gf" prec))
       (- (show-sig a.em-path nextv "a.em" prec))
       (- (show-sig a.fi-path nextv "a.fi" prec))
       (- (show-sig a.fl-path nextv "a.fl" prec))
       (- (show-sig a.ge-path nextv "a.ge" prec))
       (- (show-sig er2.ri-path nextv "er2.ri" prec))
       (- (cw "-----------------------------------------------------~%"))
       ;; (lstep  (lenv-step lenv prev next inf))
       ;; (lvalid (lenv-valid lenv tr inf))
       ;; (rstep  (renv-step renv prev next inf))
       ;; (rvalid (renv-valid renv tr inf))
       ;; (- (cw "lstep = ~x0, lvalid = ~x1, rstep=~x2, rvalid=~x3~%"
       ;;        lstep lvalid rstep rvalid))
       (- (cw "-----------------------------------------------------~%"))
       (- (cw "Testing invariant on next state for asp-stage~%"))
       (el2.li (cdr (assoc-equal el2.li-path nextv)))
       (a.gf (cdr (assoc-equal a.gf-path nextv)))
       (a.em (cdr (assoc-equal a.em-path nextv)))
       (a.fi (cdr (assoc-equal a.fi-path nextv)))
       (a.fl (cdr (assoc-equal a.fl-path nextv)))
       (a.ge (cdr (assoc-equal a.ge-path nextv)))
       (er2.ri (cdr (assoc-equal er2.ri-path nextv)))
       (testbench-left (make-asp-env-testbench
                        :req a.gf
                        :ack a.em
                        :li el2.li
                        :ri a.fi
                        :delta delta
                        :inf inf))
       (testbench-right (make-asp-env-testbench
                         :req a.fl
                         :ack a.ge
                         :li a.fi
                         :ri er2.ri
                         :delta delta
                         :inf inf))
       (inv (invariant-asp-stage a el2 er2 tnext nextv inf))
       (- (cw "~%Testing the whole invariant on next state: ~q0"
              (if inv 'passed 'failed)))
       (- (cw "----------------Left half---------------------~%"))
       (inv-lenv (invariant-lenv-failed testbench-left tnext))
       (- (cw "Testing invariant on the left env: ~q0"
              (pretty-print inv-lenv)))
       (inv-renv (invariant-renv-failed testbench-left tnext))
       (- (cw "Testing invariant on the right env: ~q0"
              (pretty-print inv-renv)))
       (inv-interact-env (interact-env-failed testbench-left))
       (- (cw "Testing invariant on the interaction between envs: ~q0"
              (pretty-print inv-interact-env)))
       ;; (lb (leftbench testbench-left))
       ;; (rb (rightbench testbench-left))
       ;; (- (cw "li_idle = ~s0~%"
       ;;        (interval-to-string (internal-idle-time  lb) prec)))
       ;; (- (cw "li_ready = ~s0~%"
       ;;        (interval-to-string (internal-next-ready-time  lb) prec)))
       ;; (- (cw "lx_idle = ~s0~%"
       ;;        (interval-to-string (external-idle-time  lb) prec)))
       ;; (- (cw "lx_ready = ~s0~%"
       ;;        (interval-to-string (external-next-ready-time  lb) prec)))
       ;; (- (cw "ri_idle = ~s0~%"
       ;;        (interval-to-string (internal-idle-time  rb) prec)))
       ;; (- (cw "ri_ready = ~s0~%"
       ;;        (interval-to-string (internal-next-ready-time  rb) prec)))
       ;; (- (cw "rx_idle = ~s0~%"
       ;;        (interval-to-string (external-idle-time  rb) prec)))
       ;; (- (cw "rx_ready = ~s0~%"
       ;;        (interval-to-string (external-next-ready-time rb) prec)))
       (- (cw "----------------Right half---------------------~%"))
       (inv-lenv (invariant-lenv-failed testbench-right tnext))
       (- (cw "Testing invariant on the left env: ~q0"
              (pretty-print inv-lenv)))
       (inv-renv (invariant-renv-failed testbench-right tnext))
       (- (cw "Testing invariant on the right env: ~q0"
              (pretty-print inv-renv)))
       (inv-interact-env (interact-env-failed testbench-right))
       (- (cw "Testing invariant on the interaction between envs: ~q0"
              (pretty-print inv-interact-env)))
       ;; (lb (leftbench testbench-right))
       ;; (rb (rightbench testbench-right))
       ;; (- (cw "li_idle = ~s0~%"
       ;;        (interval-to-string (internal-idle-time  lb) prec)))
       ;; (- (cw "li_ready = ~s0~%"
       ;;        (interval-to-string (internal-next-ready-time  lb) prec)))
       ;; (- (cw "lx_idle = ~s0~%"
       ;;        (interval-to-string (external-idle-time  lb) prec)))
       ;; (- (cw "lx_ready = ~s0~%"
       ;;        (interval-to-string (external-next-ready-time  lb) prec)))
       ;; (- (cw "ri_idle = ~s0~%"
       ;;        (interval-to-string (internal-idle-time  rb) prec)))
       ;; (- (cw "ri_ready = ~s0~%"
       ;;        (interval-to-string (internal-next-ready-time  rb) prec)))
       ;; (- (cw "rx_idle = ~s0~%"
       ;;        (interval-to-string (external-idle-time  rb) prec)))
       ;; (- (cw "rx_ready = ~s0~%"
       ;;        (interval-to-string (external-next-ready-time  rb) prec)))
       (- (cw "-----------------------------------------------------~%"))
       (- (cw "Testing invariant on next state for two envs~%"))
       (el0.li (cdr (assoc-equal el0.li-path nextv)))
       (el0.req (cdr (assoc-equal el0.req-path nextv)))
       (er0.ack (cdr (assoc-equal er0.ack-path nextv)))
       (er0.ri (cdr (assoc-equal er0.ri-path nextv)))
       (el1.li (cdr (assoc-equal el1.li-path nextv)))
       (el1.req (cdr (assoc-equal el1.req-path nextv)))
       (er1.ack (cdr (assoc-equal er1.ack-path nextv)))
       (er1.ri (cdr (assoc-equal er1.ri-path nextv)))
       (testbench-left (make-asp-env-testbench
                        :req el0.req
                        :ack er0.ack
                        :li el0.li
                        :ri er0.ri
                        :delta delta
                        :inf inf))
       (testbench-right (make-asp-env-testbench
                         :req el1.req
                         :ack er1.ack
                         :li el1.li
                         :ri er1.ri
                         :delta delta
                         :inf inf))
       (- (cw "----------------Left half---------------------~%"))
       (inv (invariant-env el0 er0 tnext nextv inf))
       (- (cw "~%Testing the whole invariant on next state for left: ~q0"
              (if inv 'passed 'failed)))
       (inv-lenv (invariant-lenv-failed testbench-left tnext))
       (- (cw "Testing invariant on the left env: ~q0"
              (pretty-print inv-lenv)))
       (inv-renv (invariant-renv-failed testbench-left tnext))
       (- (cw "Testing invariant on the right env: ~q0"
              (pretty-print inv-renv)))
       (inv-interact-env (interact-env-failed testbench-left))
       (- (cw "Testing invariant on the interaction between envs: ~q0"
              (pretty-print inv-interact-env)))
       (- (cw "----------------Right half---------------------~%"))
       (inv (invariant-env el1 er1 tnext nextv inf))
       (- (cw "~%Testing the whole invariant on next state for right: ~q0"
              (if inv 'passed 'failed)))
       (inv-lenv (invariant-lenv-failed testbench-right tnext))
       (- (cw "Testing invariant on the left env: ~q0"
              (pretty-print inv-lenv)))
       (inv-renv (invariant-renv-failed testbench-right tnext))
       (- (cw "Testing invariant on the right env: ~q0"
              (pretty-print inv-renv)))
       (inv-interact-env (interact-env-failed testbench-right))
       (- (cw "Testing invariant on the interaction between envs: ~q0"
       )
    nil))
