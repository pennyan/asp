import x
from z3 import simplify, Solver, Not, sat, unsat, unknown
import re
from cex_basics import *

def z3numstr(num):
  return simplify(num).as_decimal(6)

def sig_line(foo, prev_v, nxt_v):
  foo_prev = x.maybe_usc_sig_usc_sub_usc_value.val(prev_v[foo[1]])
  foo_nxt = x.maybe_usc_sig_usc_sub_usc_value.val(nxt_v[foo[1]])
  foo_line = ( "%20s %5s @ %12s -> %5s @ %12s" %
	           ( foo[0],
		         str(simplify(x.sig_sub_value.value(foo_prev))),
		         z3numstr(x.sig_sub_value.time(foo_prev)),
		         str(simplify(x.sig_sub_value.value(foo_nxt))),
		         z3numstr(x.sig_sub_value.time(foo_nxt))))
  return(foo_line)

def cex_str(m):  # m is a model for a counter-example
  tr = m[x.tr]
  prev = x.gtrace.car(tr)
  prev_t = x.gstate_sub_t.statet(prev)
  prev_v = x.gstate_sub_t.statev(prev)
  nxt = x.gtrace.car(x.gtrace.cdr(tr))
  nxt_t = x.gstate_sub_t.statet(nxt)
  nxt_v = x.gstate_sub_t.statev(nxt)
  time_line = "%20s %20s -> %20s" % ('time', z3numstr(prev_t), z3numstr(nxt_t))
  sigs = [ ( 'left-internal', x.lenv.left_sub_internal(m[x.el]) ),
           ( 'go-full', x.asp_sub_stage.go_sub_full(m[x.a]) ),
           ( 'empty', x.asp_sub_stage.empty(m[x.a]) ),
           ( 'full-internal', x.asp_sub_stage.full_sub_internal(m[x.a]) ),
           ( 'full', x.asp_sub_stage.full(m[x.a]) ),
           ( 'go-empty', x.asp_sub_stage.go_sub_empty(m[x.a]) ),
           ( 'right-internal', x.renv.right_sub_internal(m[x.er]) ) ]
  v_lines = [ sig_line(foo, prev_v, nxt_v) for foo in sigs ]
  return [time_line] + v_lines


def gen_sigs(sig):
  if simplify(sig) == x.sig_sub_path.nil:
    return False

  return (simplify(x.Symbol_z3.z3Sym.ival(x.sig.module(x.sig_sub_path.car(sig)))),
          simplify(x.sig.index(x.sig_sub_path.car(sig))))

def gen_sigvals(sig, curr):
  value = simplify(x.sig_sub_value.value(x.maybe_usc_sig_usc_sub_usc_value.val(curr[sig])))
  time = simplify(x.sig_sub_value.time(x.maybe_usc_sig_usc_sub_usc_value.val(curr[sig])))
  return (value, time)

def acl2(m):
  tr = m[x.tr]
  prev = x.gtrace.car(tr)
  prev_t = x.gstate_sub_t.statet(prev)
  prev_v = x.gstate_sub_t.statev(prev)
  nxt = x.gtrace.car(x.gtrace.cdr(tr))
  nxt_t = x.gstate_sub_t.statet(nxt)
  nxt_v = x.gstate_sub_t.statev(nxt)
  sigs = [ x.asp_sub_stage.go_sub_full(m[x.a]),
           x.asp_sub_stage.go_sub_empty(m[x.a]),
	       x.asp_sub_stage.full(m[x.a]),
	       x.asp_sub_stage.empty(m[x.a]),
	       x.asp_sub_stage.full_sub_internal(m[x.a]),
	       x.lenv.left_sub_internal(m[x.el]),
	       x.renv.right_sub_internal(m[x.er])]
  flat_sigs = [ gen_sigs(foo) for foo in sigs ]
  lo = simplify(x.interval.lo(x.lenv.delta(m[x.el])))
  hi = simplify(x.interval.hi(x.lenv.delta(m[x.el])))
  delta = [ (lo, hi) for i in range(0,3)]
  sig_curr = [ gen_sigvals(foo, nxt_v) for foo in sigs]
  tcurr = simplify(nxt_t)
  return [flat_sigs, delta, sig_curr, tcurr]

def translate(term):
  step1 = str(term).replace(",", "").replace("[", "(").replace("]", ")")
  step2 = re.sub(r"([a-zA-Z0-9_]+?)\(", r"\(\1 ", step1)
  step3 = step2.replace(".0", "").replace("False", "nil").replace("True","t")
  return step3

def lenv_to_acl2(el):
  return('(make-lenv ' + ':ack-in ' + sigPath_to_acl2(x.lenv.ack_sub_in(el)) + '\n'
         + ':req-out ' + sigPath_to_acl2(x.lenv.req_sub_out(el)) + '\n'
         + ':left-internal ' + sigPath_to_acl2(x.lenv.left_sub_internal(el)) + '\n'
         + ':delta ' + interval_to_acl2(x.lenv.delta(el)) + ')\n')

def renv_to_acl2(er):
  return('(make-renv ' + ':req-in ' + sigPath_to_acl2(x.renv.req_sub_in(er)) + '\n'
         + ':ack-out ' + sigPath_to_acl2(x.renv.ack_sub_out(er)) + '\n'
         + ':right-internal ' + sigPath_to_acl2(x.renv.right_sub_internal(er)) + '\n'
         + ':delta ' + interval_to_acl2(x.renv.delta(er)) + ')\n')

def asp_stage_to_acl2(a):
  return('(make-asp-stage '
         + ':go-full ' + sigPath_to_acl2(x.asp_sub_stage.go_sub_full(a)) + '\n'
         + ':empty ' + sigPath_to_acl2(x.asp_sub_stage.empty(a)) + '\n'
         + ':go-empty ' + sigPath_to_acl2(x.asp_sub_stage.go_sub_empty(a)) + '\n'
         + ':full ' + sigPath_to_acl2(x.asp_sub_stage.full(a)) + '\n'
         + ':full-internal ' + sigPath_to_acl2(x.asp_sub_stage.full_sub_internal(a)) + '\n'
         + ':left ' + renv_to_acl2(x.asp_sub_stage.left(a)) + '\n'
         + ':right ' + lenv_to_acl2(x.asp_sub_stage.right(a)) + '\n'
         + ':delta ' + interval_to_acl2(x.asp_sub_stage.delta(a)) + ')\n')

def acl2m(m):
  a = m[x.a]
  el = m[x.el]
  er = m[x.er]
  tr = m[x.tr]
  inf = m[x.inf]
  sigs = [ x.lenv.left_sub_internal(el),
           x.asp_sub_stage.go_sub_full(a),
           x.asp_sub_stage.empty(a),
           x.asp_sub_stage.full_sub_internal(a),
           x.asp_sub_stage.full(a),
           x.asp_sub_stage.go_sub_empty(a),
           x.renv.right_sub_internal(er) ]
  return("(defun cex ()\n" +
          "(list" + "(cons 'asp " + asp_stage_to_acl2(a) + ")     \n"
                  + "(cons 'lenv " + lenv_to_acl2(el) + ")     \n"
                  + "(cons 'renv " + renv_to_acl2(er) + ")     \n"
                  + "(cons 'tr " + gtrace_to_acl2(tr, m, sigs) + ")\n"
                  + "(cons 'inf " + rational_to_acl2(inf) + ")))\n")


  # fetch the counter-example from x and print it in a human readable form
def main():
  thm = x.theorem
  mySolver = Solver()
  mySolver.add(Not(thm))
  status = mySolver.check()
  if(status == unsat):
    print("It's a theorem!\n")
  elif(status == unknown):
    print("z3 can't figure it out\n")
  else:
    m = mySolver.model()
    lines = cex_str(m)
    [print(line) for line in lines]
    print("\nUse the form below to test the next state invariants:")
    print(acl2m(m))
