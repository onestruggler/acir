"""Lean text for case analyses on relation instances with indices in `Fin m`."""
import itertools

def fin_arm(g, res, rel, vars_, idx, m, valid, ind=4):
    """An arm `| rel vars => …` of `cases r with`: `fin_cases` on the index variables `idx`
    (in `Fin m`), the derivation named `valid[tuple]` for each admissible tuple, and the other
    tuples closed by deciding the hypotheses."""
    sp = ' ' * ind
    out = ['%s| %s %s =>' % (sp, rel, vars_)]
    hs = [v for v in vars_.split() if v.startswith('h')]
    if idx:
        out.append('%s  %s' % (sp, ' <;> '.join('fin_cases %s' % v for v in idx)))
        tuples = list(itertools.product(range(m), repeat=len(idx)))
    else:
        tuples = [()]
    for tup in tuples:
        if tup in valid:
            n_, l, r, eqs, steps = res[valid[tup]]
            pf = g.proof(eqs, steps, ind + 6)
            if hs:
                # the hypotheses are proofs: decided with them reverted, so the goal is closed
                pf = pf.replace('(by decide +kernel)', '(by revert %s; decide +kernel)' % ' '.join(hs))
            out.append('%s  · exact\n%s      %s' % (sp, sp, pf))
        else:
            out.append('%s  · exfalso; revert %s; decide' % (sp, ' '.join(hs)))
    return '\n'.join(out)

def absurd_arm(rel, vars_, ind=4):
    sp = ' ' * ind
    idx = [v for v in vars_.split() if not v.startswith('h')]
    hs = [v for v in vars_.split() if v.startswith('h')]
    if len(idx) >= 4:
        return '%s| %s %s => exfalso; %s <;> simp_all' % (
            sp, rel, vars_, ' <;> '.join('fin_cases %s' % v for v in idx))
    return '%s| %s %s => exfalso; revert %s; revert %s; decide' % (sp, rel, vars_, ' '.join(hs), ' '.join(idx))
