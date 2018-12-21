(in-package "ASP")
(include-book "std/util/define" :dir :system)
(include-book "tools/bstar" :dir :system)
(include-book "centaur/fty/top" :dir :system) ; for defalist, etc.
;; (include-book "env")

(define pretty-print (failed-clauses)
  :guard t
  (if failed-clauses failed-clauses 'passed))

(define int-to-char-list ((i natp) (u character-listp))
  :returns (u2 character-listp)
  (b* ((u (character-list-fix u))
       ((if (zp i)) u)
       (rst (nonnegative-integer-quotient i 10))
       (lsd (- i (* 10 rst))))
    (int-to-char-list
     rst
     (cons (code-char (+ (char-code #\0) lsd)) u))))

(define frac-to-rev-char-list ((r rationalp) (u character-listp) (prec natp))
  :guard (<= 0 r)
  :measure (nfix prec)
  :returns (u2 character-listp)
  (b* ((u (character-list-fix u))
       ((if (equal 0 r)) u)
       ((if (zp prec)) u)
       (r10 (* 10 r))
       (d (nonnegative-integer-quotient (numerator r10) (denominator r10)))
       (rst (- r10 d))
       ((unless (and (<= 0 d) (< d 10) (<= 0 rst))) u))
    (frac-to-rev-char-list
     rst
     (cons (code-char (+ (char-code #\0) d)) u)
     (1- prec))))

(encapsulate nil
  (local (defthm stupid-lemma
           (implies (character-listp x) (character-listp (acl2::rev x)))))

  (define rational-to-string ((r rationalp) (prec natp))
    :returns (s stringp)
    :guard-debug t
    (b* ((abs-r (abs r))
	       (int-part (nonnegative-integer-quotient (numerator abs-r)
                                                 (denominator abs-r)))
	       (si (int-to-char-list int-part nil))
	       (si (cond ((< r 0) (cons #\- si))
                   ((> r 0) si)
                   (t '(#\0))))
	       (frac-part (- abs-r int-part))
	       (sf (if (<= frac-part 0)
		             nil
	             (cons #\. (acl2::rev
                          (frac-to-rev-char-list frac-part nil prec)))))
         (rem-num (rem (numerator abs-r) 524287))
         (rem-dem (rem (denominator abs-r) 524287))
         (hash (if (and (>= rem-num 0)
                        (>= rem-dem 0))
                   `(,@(int-to-char-list rem-num nil)
                     #\/
                     ,@(int-to-char-list rem-dem nil))
                 nil)))
      (coerce (append si sf
                      '(#\[ #\H #\A #\S #\H #\: )
                      hash
                      '(#\]))
              'string))))

(define sig-value-to-str ((sv sig-value-p) (prec natp))
  :returns (s stringp)
  (b* (((unless (sig-value-p sv)) "???")
       ((sig-value sv) sv)
       (val  (coerce (if sv.value "t" "nil") 'list))
       (at   (coerce " @ " 'list))
       (tim (coerce (rational-to-string sv.time prec) 'list)))
    (coerce (append val at tim) 'string)))

(define show-sig ((sig sig-path-p)
                  (st gstate-p)
                  (name stringp))
  (b* ((sig (sig-path-fix sig))
       (st (gstate-fix st))
       (pair (assoc-equal sig st))
       ((unless pair)
        (cw "Sig ~p0 not found!~%" sig))
       (v (cdr (assoc-equal sig st))))
    (cw "  ~s0 = ~x1 @ ~s2~%" name (sig-value->value v)
        (rational-to-string (sig-value->time v) 6)
        :fmt-control-alist
        `((fmt-soft-right-margin . 1000)
          (fmt-hard-right-margin . 1000)))))

(define test ((cex t))
  :verify-guards nil
  (b* ((lenv (cdr (assoc 'lenv cex)))
       (renv (cdr (assoc 'renv cex)))
       (tr (cdr (assoc 'tr cex)))
       (prev (car tr))
       (next (cadr tr))
       (inf (cdr (assoc 'inf cex)))
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
       (- (cw "prev: tprev = ~s0~%" (rational-to-string tprev 6)))
       (- (show-sig li-path prevv "left-internal"))
       (- (show-sig req-path prevv "req"))
       (- (show-sig ack-path prevv "ack"))
       (- (show-sig ri-path prevv "right-internal"))
       (- (cw "next: tnext = ~s0~%(inf = ~s1,~% delta = [~s2, ~s3))~%"
              (rational-to-string tnext 6)
              (rational-to-string inf 6)
              (rational-to-string (interval->lo delta) 6)
              (rational-to-string (interval->hi delta) 6)))
       (- (show-sig li-path nextv "left-internal"))
       (- (show-sig req-path nextv "req"))
       (- (show-sig ack-path nextv "ack"))
       (- (show-sig ri-path nextv "right-internal"))
       (- (cw "-----------------------------------------------------~%"))
       (lstep  (lenv-step lenv prev next inf))
       (lvalid (lenv-valid lenv tr inf))
       (rstep  (renv-step renv prev next inf))
       (rvalid (renv-valid renv tr inf))
       (- (cw "lstep = ~x0, lvalid = ~x1, rstep=~x2, rvalid=~x3~%"
              lstep lvalid rstep rvalid))
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
       (inv (invariant lenv renv tnext nextv inf))
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
              (pretty-print inv-interact-env))))
    nil))
