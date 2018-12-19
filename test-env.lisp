(in-package "ASP")
;; (include-book "asp")
;; have to define (cex) first, then load this file

(define pretty-print (failed-clauses)
  :guard t
  (if failed-clauses failed-clauses 'passed))

(set-ignore-ok t)
(define test-invariant ((lenv t) (renv t)
                        (tcurr t) (curr t)
                        (inf t))
  :irrelevant-formals-ok t
  :verify-guards nil
  (b* ((li (lenv->left-internal lenv))
       (req (lenv->req-out lenv))
       (ack (renv->ack-out renv))
       (ri (renv->right-internal renv))
       (- (cw "Current signal values:~%left-internal = ~q0, req = ~q1, ack = ~q2, right-internal = ~q3"
           li req ack ri))
       (delta (lenv->delta lenv))
       (inv (invariant lenv renv tcurr curr inf))
       (- (cw "~%Testing the whole invariant on curr state: ~q0"
              (if inv 'passed 'failed)))
       (li (cdr (assoc-equal li curr)))
       (req (cdr (assoc-equal req curr)))
       (ack (cdr (assoc-equal ack curr)))
       (ri (cdr (assoc-equal ri curr)))
       (testbench (make-asp-env-testbench
                   :req req
                   :ack ack
                   :li li
                   :ri ri
                   :delta delta
                   :inf inf))
       (inv-lenv (invariant-lenv-failed testbench tcurr))
       (- (cw "Testing invariant on the left env: ~q0"
              (pretty-print inv-lenv)))
       (inv-renv (invariant-renv-failed testbench tcurr))
       (- (cw "Testing invariant on the right env: ~q0"
              (pretty-print inv-renv)))
       (inv-interact-env (interact-env-failed testbench))
       (- (cw "Testing invariant on the interaction between envs: ~q0"
              (pretty-print inv-interact-env))))
    nil))


(define test ((cex t))
  :verify-guards nil
  (b* ((lenv (cdr (assoc 'lenv cex)))
       (renv (cdr (assoc 'renv cex)))
       (prev (cadr  (assoc 'tr cex)))
       (next (caddr (assoc 'tr cex)))
       (inf (cdr (assoc 'inf cex)))
       (nextt (gstate-t->statet next))
       (nextv (gstate-t->statev next))
       (- (cw "----------------------------------------------------- ~% ~
               Testing lenv-step~%"))
       (- (cw "~q0" (lenv-step lenv prev next inf)))
       (- (cw "----------------------------------------------------- ~% ~
               Testing renv-step~%"))
       (- (cw "~q0" (renv-step renv prev next inf)))
       (- (cw "----------------------------------------------------- ~% ~
               Testing invariant on next state~%"))
       (- (cw "~p0" (test-invariant lenv renv nextt nextv inf))))
    nil))
