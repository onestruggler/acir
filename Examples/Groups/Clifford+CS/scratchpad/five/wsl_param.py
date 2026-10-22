#!/usr/bin/env python3
"""The placed windows take the literal ones as an argument.

    python3 wsl_param.py REPO

Five.Resps instantiated the respelling lemmas at `wsL c4`, the proofs of
the literal windows (Five.WinInstL, which imports Five/Wins/WL01-09), so
the placed-window libraries WP01-08 waited for all of WL01-09 and loaded
their interfaces: two stages of window libraries, one after the other,
on the critical path of a from-scratch run.  Here the tables and the
placed windows take those proofs as an argument (`L : WsL`) and only
Five.WinInst supplies `wsL c4`; the evaluations do not look at them.
Idempotent (a run after emit5.py/winlib5.py redo it).
"""
import os, re, sys

BASE = os.path.join(sys.argv[1], 'Examples/Groups/Clifford+CS/Five')


def edit(path, f):
    s = open(path, encoding='utf-8').read()
    s2 = f(s)
    if s2 != s:
        open(path, 'w', encoding='utf-8').write(s2)
        return True
    return False


def resps(s):
    s = s.replace('open import Examples.Groups.Clifford+CS.Five.WinInstL using (wsL)\n',
                  'open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL)\n')
    s = re.sub(r'^(resp\d) : Complete 4 → ', r'\1 : WsL → ', s, flags=re.M)
    s = re.sub(r'^(resp\d) c4 ', r'\1 L ', s, flags=re.M)
    s = s.replace('(wsL c4)', 'L')
    # the binder named: in `WsL → _` the result type could not mention it
    s = re.sub(r'^(pw\d) : \(c4 : Complete 4\) (?:→ WsL )?→ _$', r'\1 : (c4 : Complete 4) (L : WsL) → _', s, flags=re.M)
    s = re.sub(r'^(pw\d) c4 = (W\d)\.pwin \((resp\d) c4\) c4$', r'\1 c4 L = \2.pwin (\3 L) c4', s, flags=re.M)
    return s


def wp(s):
    s = re.sub(r'^(wp\d+) : Complete 4 → (?!WsL)', r'\1 : Complete 4 → WsL → ', s, flags=re.M)
    s = re.sub(r'^(wp\d+) c4 = (pw\d) c4 ', r'\1 c4 L = \2 c4 L ', s, flags=re.M)
    if 'Five.WinSig using (WsL)' not in s:
        s = s.replace('open import Examples.Groups.Clifford+CS.Completeness using (Complete)\n',
                      'open import Examples.Groups.Clifford+CS.Completeness using (Complete)\n'
                      'open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL)\n')
    return s


def wininst(s):
    s = re.sub(r'\((WP\d\d\.wp\d+) c4\)', r'(\1 c4 L)', s)
    if 'where L = wsL c4' not in s and ' c4 L)' in s:
        s = s.replace('  { lit = wsL c4\n', '  { lit = L\n')
        s = s.rstrip('\n') + '\n  where L = wsL c4\n'
    return s


print('Resps', edit(os.path.join(BASE, 'Resps.agda'), resps))
print('WP', sum(edit(os.path.join(BASE, 'Wins', f), wp)
                for f in sorted(os.listdir(os.path.join(BASE, 'Wins'))) if f.startswith('WP')))
print('WinInst', edit(os.path.join(BASE, 'WinInst.agda'), wininst))
