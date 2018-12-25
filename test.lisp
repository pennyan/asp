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
  (b* ((asp (cdr (assoc 'asp cex)))
       (lenv (cdr (assoc 'lenv cex)))
       (renv (cdr (assoc 'renv cex)))
       (prev (cdr (assoc 's1 cex)))
       (next (cdr (assoc 's2 cex)))
       (inf (cdr (assoc 'inf cex)))
       (prec 8)
       (tprev (gstate-t->statet prev))
       (prevv (gstate-t->statev prev))
       (tnext (gstate-t->statet next))
       (nextv (gstate-t->statev next))
       (li-path (lenv->left-internal lenv))
       (gf-path (asp-stage->go-full asp))
       (em-path (asp-stage->empty asp))
       (fi-path (asp-stage->full-internal asp))
       (fl-path (asp-stage->full asp))
       (ge-path (asp-stage->go-empty asp))
       (ri-path  (renv->right-internal renv))
       (delta (lenv->delta lenv))
       (- (cw "-----------------------------------------------------~%"))
       (- (cw "(inf = ~s0,~% delta = [~s1, ~s2))~%"
              (rational-to-string inf prec)
              (rational-to-string (interval->lo delta) prec)
              (rational-to-string (interval->hi delta) prec)))
       (- (cw "prev: tprev = ~s0~%" (rational-to-string tprev prec)))
       (- (show-sig li-path prevv "left-internal" prec))
       (- (show-sig gf-path prevv "go-full" prec))
       (- (show-sig em-path prevv "empty" prec))
       (- (show-sig fi-path prevv "full-internal" prec))
       (- (show-sig fl-path prevv "full" prec))
       (- (show-sig ge-path prevv "go-empty" prec))
       (- (show-sig ri-path prevv "right-internal" prec))
       (- (cw "next: tnext = ~s0~%" (rational-to-string tnext prec)))
       (- (show-sig li-path nextv "left-internal" prec))
       (- (show-sig gf-path nextv "go-full" prec))
       (- (show-sig em-path nextv "empty" prec))
       (- (show-sig fi-path nextv "full-internal" prec))
       (- (show-sig fl-path nextv "full" prec))
       (- (show-sig ge-path nextv "go-empty" prec))
       (- (show-sig ri-path nextv "right-internal" prec))
       (- (cw "-----------------------------------------------------~%"))
       (- (cw "Testing invariant on next state~%"))
       (li (cdr (assoc-equal li-path nextv)))
       (gf (cdr (assoc-equal gf-path nextv)))
       (em (cdr (assoc-equal em-path nextv)))
       (fi (cdr (assoc-equal fi-path nextv)))
       (fl (cdr (assoc-equal fl-path nextv)))
       (ge (cdr (assoc-equal ge-path nextv)))
       (ri (cdr (assoc-equal ri-path nextv)))
       (testbench-left (make-asp-env-testbench
                        :req gf
                        :ack em
                        :li li
                        :ri fi
                        :delta delta
                        :inf inf))
       (testbench-right (make-asp-env-testbench
                         :req fl
                         :ack ge
                         :li fi
                         :ri ri
                         :delta delta
                         :inf inf))
       (inv (invariant-asp-stage asp lenv renv next inf))
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
       (lb (leftbench testbench-left))
       (rb (rightbench testbench-left))
       (- (cw "li_idle = ~s0~%"
              (interval-to-string (internal-idle-time  lb) prec)))
       (- (cw "li_ready = ~s0~%"
              (interval-to-string (internal-next-ready-time  lb) prec)))
       (- (cw "lx_idle = ~s0~%"
              (interval-to-string (external-idle-time  lb) prec)))
       (- (cw "lx_ready = ~s0~%"
              (interval-to-string (external-next-ready-time  lb) prec)))
       (- (cw "ri_idle = ~s0~%"
              (interval-to-string (internal-idle-time  rb) prec)))
       (- (cw "ri_ready = ~s0~%"
              (interval-to-string (internal-next-ready-time  rb) prec)))
       (- (cw "rx_idle = ~s0~%"
              (interval-to-string (external-idle-time  rb) prec)))
       (- (cw "rx_ready = ~s0~%"
              (interval-to-string (external-next-ready-time rb) prec)))
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
       (lb (leftbench testbench-right))
       (rb (rightbench testbench-right))
       (- (cw "li_idle = ~s0~%"
              (interval-to-string (internal-idle-time  lb) prec)))
       (- (cw "li_ready = ~s0~%"
              (interval-to-string (internal-next-ready-time  lb) prec)))
       (- (cw "lx_idle = ~s0~%"
              (interval-to-string (external-idle-time  lb) prec)))
       (- (cw "lx_ready = ~s0~%"
              (interval-to-string (external-next-ready-time  lb) prec)))
       (- (cw "ri_idle = ~s0~%"
              (interval-to-string (internal-idle-time  rb) prec)))
       (- (cw "ri_ready = ~s0~%"
              (interval-to-string (internal-next-ready-time  rb) prec)))
       (- (cw "rx_idle = ~s0~%"
              (interval-to-string (external-idle-time  rb) prec)))
       (- (cw "rx_ready = ~s0~%"
              (interval-to-string (external-next-ready-time  rb) prec)))
       (- (cw "-----------------------------------------------------~%"))
       (lstep  (lenv-step lenv prev next inf))
       (rstep  (renv-step renv prev next inf))
       (- (cw "lstep = ~x0, rstep=~x1~%"
              lstep rstep))
       (- (cw "-----------------------------------------------------~%"))
       (lenv-hf (lenv-hazard-free-step (asp-stage->right asp) prev next))
       (renv-hf (renv-hazard-free-step (asp-stage->left asp) prev next))
       (- (cw "lhf = ~x0, rhf=~x1~%"
              lenv-hf renv-hf))
       )
    nil))
