import x
from z3 import IntSort, RealSort, Select, simplify, Solver, Not, sat, unsat, unknown
import re

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
  return('(make-delay-interval' + ' :lo ' + rational_to_acl2(x.delay_sub_interval.lo(iv))
                          + ' :hi ' + rational_to_acl2(x.delay_sub_interval.hi(iv)) + ')')

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
    s = s + '(cons ' + sigPath_to_acl2(p) + ' ' + maybeSigValue_to_acl2(m.eval(Select(g, p))) + ')\n '
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
