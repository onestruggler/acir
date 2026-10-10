"""Generate NFs.agda, TreeNF341.agda, TreeNF38.agda and TreeTop.agda.

Usage: python gen.py [OUTDIR]   (default: the development's folder)
"""
import os, sys
sys.setrecursionlimit(50000)
from emit import *
import trees

DIR = os.path.join(sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'), '')
NL = '\n'

def nf_block():
    out = []
    for nf, mini in ((trees.NF38, True), (trees.NF341, False)):
        tags = ['(just %d)' % nf.tags[r] if r in nf.tags else 'nothing' for r in nf.roles]
        out.append('nfData %s = record' % nf.name)
        out.append('  { forms = %s' % vec([form(nf.fs[r], nf.vars) for r in nf.roles]))
        out.append('  ; tags = %s' % vec(tags))
        out.append('  ; ic = %s ; id = %s ; mini = %s }' % (fin(nf.roles.index('c')), fin(nf.roles.index('d')), boolean(mini)))
    return out

def write_nfs():
    doc = "The normal forms: Clément's (38) for Subcase 3.4.2, and the form of" + NL + "-- Subcase 3.4.1 (generated)."
    out = [HEADER % (doc, 'NFs'), PRIV]
    out.append('nfData : (nf : NF) → NFData nf')
    out += nf_block()
    open(DIR + 'NFs.agda', 'w', encoding='utf-8').write(NL.join(out) + NL)

def write_tree(modname, doc, tname, t, rows, vars_, fs, tags, mini, allow):
    out = [HEADER % (doc, modname), 'open import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.NFs using (nfData)', PRIV]
    term = emit(t, rows, vars_, [], tname)
    m, r = len(rows), len(vars_)
    out.append('%s : Tree %d %d' % (tname, m, r))
    out.append('%s = %s' % (tname, term))
    out.append('')
    out.append('%sForms : Vec (Form %d) %d' % (tname, r, m))
    out.append('%sForms = %s' % (tname, vec([form(fs[x], vars_) for x in rows])))
    out.append('')
    out.append('%sTags : Vec (Maybe ℕ) %d' % (tname, m))
    out.append('%sTags = %s' % (tname, vec(['(just %d)' % tags[x] if x in tags else 'nothing' for x in rows])))
    out.append('')
    out.append('open Checker nfData (λ _ → %s) using (checkT)' % allow)
    out.append('')
    out.append('%s-ok : checkT %s %sTags %s %s %s %sForms ≡ true' % (tname, tname, tname, boolean(mini), fin(rows.index('c')), fin(rows.index('d')), tname))
    out.append('%s-ok = refl' % tname)
    open(DIR + modname + '.agda', 'w', encoding='utf-8').write(NL.join(out) + NL)

if __name__ == '__main__':
    T = trees.build()
    write_nfs()
    for nf, mini in ((trees.NF341, False), (trees.NF38, True)):
        name = 'TreeNF' + nf.name[2:]
        write_tree(name, 'The tree of the normal form %s (generated).' % nf.name, 't' + nf.name[2:], T[nf.name],
                   nf.roles, nf.vars, nf.fs, nf.tags, mini, 'false')
    rt = trees.root()
    write_tree('TreeTop', 'The tree from a hard state to the normal forms (generated).', 'top', T['top'],
               rt.rows, rt.vars, rt.fs, {}, True, 'true')
    print('written')
