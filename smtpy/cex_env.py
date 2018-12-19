import x
from z3 import IntSort, RealSort, Select, simplify, Solver, Not, sat, unsat, unknown
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
  time_line = "%20s %20s -> %20s  (infinity = %s)" % ('time', z3numstr(prev_t), z3numstr(nxt_t), m[x.inf])
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

def acl2(m, whichState=1):
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
  if(whichState==0):
    sig_curr = [ gen_sigvals(foo, prev_v) for foo in sigs]
    tcurr = simplify(prev_t)
  else:
    sig_curr = [ gen_sigvals(foo, nxt_v) for foo in sigs]
    tcurr = simplify(nxt_t)
  return [flat_sigs, delta, sig_curr, tcurr]

def bool_to_acl2(b):
  if(simplify(b)):
    return 't'
  else:
    return 'nil'

def integer_to_acl2(i):
  return simplify(i).as_string()

def rational_to_acl2(r):
  r = simplify(r)
  if(r.sort() == IntSort()):
    return(integer_to_acl2(r))
  elif((r.sort() == RealSort()) and (r.decl().name() == 'Real')):
    if(r.denominator_as_long() == 1):
      return r.numerator().as_string()
    else:
      return('(/ ' + r.numerator().as_string() + ' ' + r.denominator().as_string() + ')')
  else:
    raise Exception('rational_to_acl2, badarg: ' + str(r))

def interval_to_acl2(iv):
  return('(make-interval' + ' :lo ' + rational_to_acl2(x.interval.lo(iv))
                          + ' :hi ' + rational_to_acl2(x.interval.hi(iv)) + ')')

def symbol_to_acl2(sym):
  sym = simplify(sym)
  return ("'sym" + simplify(x.Symbol_z3.z3Sym.ival(sym)).as_string())
  
def sig_to_acl2(s):
  mod = symbol_to_acl2(x.sig.module(s))
  idx = integer_to_acl2(x.sig.index(s))
  return('(make-sig :module ' + mod + ' :index ' + idx + ')')

def sigPath_to_acl2(p):
  if(simplify(p == x.sig_sub_path.nil)):
    return('nil')
  else:
    hd = sig_to_acl2(x.sig_sub_path.car(p))
    tl = sigPath_to_acl2(x.sig_sub_path.cdr(p))
    return('(cons ' + hd + ' ' + tl + ')')

def sigValue_to_acl2(sv):
  return('(make-sig-value' + ' :value ' + bool_to_acl2(x.sig_sub_value.value(sv))
                           + ' :time ' +  rational_to_acl2(x.sig_sub_value.time(sv)) + ')')

def maybeSigValue_to_acl2(msv):
  if(simplify(msv == x.maybe_usc_sig_usc_sub_usc_value.nil)):
   return 'nil'
  else:
   return sigValue_to_acl2(x.maybe_usc_sig_usc_sub_usc_value.val(msv))

def gstate_to_acl2(g, m, paths):
  s = '(list'
  for p in paths:
    s = s + '(cons' + sigPath_to_acl2(p) + ' ' + maybeSigValue_to_acl2(m.eval(Select(g, p))) + ')\n '
  return s + ')'

def gstate_t_to_acl2(gt, m, paths):
  return('(make-gstate-t :statet ' + rational_to_acl2(x.gstate_sub_t.statet(gt))  + '\n  '
                        ':statev ' + gstate_to_acl2(x.gstate_sub_t.statev(gt), m, paths) + ')\n')

def gtrace_to_acl2(tr, m, paths):
  if(simplify(tr == x.gtrace.nil)):
    return('nil')
  else:
    hd = gstate_t_to_acl2(x.gtrace.car(tr), m, paths)
    tl = gtrace_to_acl2(x.gtrace.cdr(tr), m, paths)
    return('(cons ' + hd + ' ' + tl + ')')

def lenv_to_acl2(el):
  return('(make-lenv ' + ':ack-in ' + sigPath_to_acl2(x.lenv.ack_sub_in(el)) + '\n'
                       + ':req-out ' + sigPath_to_acl2(x.lenv.req_sub_out(el)) + '\n'
                       + ':left-internal ' + sigPath_to_acl2(x.lenv.left_sub_internal(el)) + '\n'
                       + ':delta ' + interval_to_acl2(x.lenv.delta(el)) + ')\n')

def renv_to_acl2(el):
  return('(make-renv ' + ':req-in ' + sigPath_to_acl2(x.renv.req_sub_in(el)) + '\n'
                       + ':ack-out ' + sigPath_to_acl2(x.renv.ack_sub_out(el)) + '\n'
                       + ':right-internal ' + sigPath_to_acl2(x.renv.right_sub_internal(el)) + '\n'
                       + ':delta ' + interval_to_acl2(x.renv.delta(el)) + ')\n')


def acl2m(m):
  el = m[x.el]
  er = m[x.er]
  tr = m[x.tr]
  inf = m[x.inf]
  sigs = [ x.lenv.left_sub_internal(el),
           x.lenv.req_sub_out(el),
           x.renv.ack_sub_out(er),
           x.renv.right_sub_internal(er) ]
  return("(defun cex ()\n" +
          "(list" + "(cons 'lenv " + lenv_to_acl2(el) + ")     \n"
                  + "(cons 'renv " + renv_to_acl2(er) + ")     \n"
                  + "(cons 'tr " + gtrace_to_acl2(tr, m, sigs) + ")\n"
          + "(cons 'inf " + rational_to_acl2(inf) + ")))\n")

def translate(term):
  step1 = str(term).replace(",", "").replace("[", "(").replace("]", ")")
  step2 = re.sub(r"([a-zA-Z0-9_]+?)\(", r"\(\1 ", step1)
  step3 = step2.replace(".0", "").replace("False", "nil").replace("True","t")
  return step3

  # fetch the counter-example from x and print it in a human readable form
def main(whichState=1):
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
    term = acl2(m, whichState)
    print("\nUse the form below to test the next state invariants:")
    print(acl2m(m))
    # print("(test-invariant-macro ")
    # [print(translate(line)) for line in term]
    # print(")")
