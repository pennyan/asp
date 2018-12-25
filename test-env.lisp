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
  (b* ((lenv (cdr (assoc 'lenv cex)))
       (renv (cdr (assoc 'renv cex)))
       (prev (cdr (assoc 's1 cex)))
       (next (cdr (assoc 's2 cex)))
       (inf (cdr (assoc 'inf cex)))
       (prec 8)
       (tprev (gstate-t->statet prev))
       (prevv (gstate-t->statev prev))
       (tnext (gstate-t->statet next))
       (nextv (gstate-t->statev next))
       (li-path  (lenv->left-internal lenv))
       (req-path (lenv->req-out lenv))
       (ack-path (renv->ack-out renv))
       (ri-path  (renv->right-internal renv))
       (delta (lenv->delta lenv))
       (- (cw "-----------------------------------------------------~%"))
       (- (cw "prev: tprev = ~s0~%" (rational-to-string tprev prec)))
       (- (show-sig li-path prevv "left-internal" prec))
       (- (show-sig req-path prevv "req" prec))
       (- (show-sig ack-path prevv "ack" prec))
       (- (show-sig ri-path prevv "right-internal" prec))
       (- (cw "next: tnext = ~s0~%(inf = ~s1,~% delta = [~s2, ~s3))~%"
              (rational-to-string tnext prec)
              (rational-to-string inf prec)
              (rational-to-string (interval->lo delta) prec)
              (rational-to-string (interval->hi delta) prec)))
       (- (show-sig li-path nextv "left-internal" prec))
       (- (show-sig req-path nextv "req" prec))
       (- (show-sig ack-path nextv "ack" prec))
       (- (show-sig ri-path nextv "right-internal" prec))
       (- (cw "-----------------------------------------------------~%"))
       (lstep  (lenv-step lenv prev next inf))
       (rstep  (renv-step renv prev next inf))
       (- (cw "lstep = ~x0, rstep=~x1~%"
              lstep rstep))
       (- (cw "-----------------------------------------------------~%"))
       (- (cw "Testing invariant on next state~%"))
       (li  (cdr (assoc-equal li-path nextv)))
       (req (cdr (assoc-equal req-path nextv)))
       (ack (cdr (assoc-equal ack-path nextv)))
       (ri  (cdr (assoc-equal ri-path nextv)))
       (testbench (make-asp-env-testbench
                   :req req
                   :ack ack
                   :li li
                   :ri ri
                   :delta delta
                   :inf inf))
       (inv (invariant-env lenv renv next inf))
       (- (cw "~%Testing the whole invariant on next state: ~q0"
              (if inv 'passed 'failed)))
       (inv-lenv (invariant-lenv-failed testbench tnext))
       (- (cw "Testing invariant on the left env: ~q0"
              (pretty-print inv-lenv)))
       (inv-renv (invariant-renv-failed testbench tnext))
       (- (cw "Testing invariant on the right env: ~q0"
              (pretty-print inv-renv)))
       (inv-interact-env (interact-env-failed testbench))
       (- (cw "Testing invariant on the interaction between envs: ~q0"
              (pretty-print inv-interact-env)))
       (lb (leftbench testbench))
       (rb (rightbench testbench))
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
       (- (cw "-----------------------------------------------------~%"))
       (- (cw "li-excited: ~q0" (li-excited lenv prev inf)))
       (- (cw "req-excited: ~q0" (req-excited lenv prev inf)))
       (- (cw "ri-excited: ~q0" (ri-excited renv prev inf)))
       (- (cw "ack-excited: ~q0" (ack-excited renv prev inf)))
       )
    nil))
