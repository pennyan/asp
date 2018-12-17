import x
from z3 import simplify, Solver, Not, sat, unsat, unknown
import re

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
           ( 'req', x.lenv.req_sub_out(m[x.el]) ),
           ( 'ack', x.renv.ack_sub_out(m[x.er]) ),
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
  sigs = [ x.lenv.left_sub_internal(m[x.el]),
	       x.lenv.req_sub_out(m[x.el]),
           x.renv.ack_sub_out(m[x.er]),
	       x.renv.right_sub_internal(m[x.er])]
  flat_sigs = [ gen_sigs(foo) for foo in sigs ]
  lo = simplify(x.interval.lo(x.lenv.delta(m[x.el])))
  hi = simplify(x.interval.hi(x.lenv.delta(m[x.el])))
  delta = (lo, hi)
  sig_curr = [ gen_sigvals(foo, nxt_v) for foo in sigs]
  tcurr = simplify(nxt_t)
  return [flat_sigs, delta, sig_curr, tcurr]

def translate(term):
  step1 = str(term).replace(",", "").replace("[", "(").replace("]", ")")
  step2 = re.sub(r"([a-zA-Z0-9_]+?)\(", r"\(\1 ", step1)
  step3 = step2.replace(".0", "").replace("False", "nil").replace("True","t")
  return step3

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
    term = acl2(m)
    print("\nUse below form to test next state invariants:")
    print("(test-invariant-macro ")
    [print(translate(line)) for line in term]
    print(")")
