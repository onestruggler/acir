#!/usr/bin/env python3
"""The window libraries take what a window step needs as an argument.

    python3 winbase.py REPO

A window step (Windows.win) needs the swap rules, which Swaps proves by
completeness on two and three wires, and completeness at the width of
the window.  The libraries used the proofs (Completeness.complete₃, the
placements over Swaps), so all of Four/Wins and Five/Wins waited for
the chain under them -- TwoQubit/Decoding, ThreeQubit, Swaps,
TopWeakening, Place, Windows -- and could not start until some
400 s into a from-scratch run.  Here every window takes a `Windows.Base`
(the swap rules, SwapFacts, and completeness), the libraries depend on
the statements alone, and only the assemblies Four.WinInst, Five.WinInstL
and Five.WinInst supply the proofs.  Idempotent; run it after winlib4.py,
winmac4.py, winlib5.py and wsl_param.py.
"""
import os, re, sys

C = os.path.join(sys.argv[1], 'Examples/Groups/Clifford+CS')
P = 'Examples.Groups.Clifford+CS.'


def edit(path, f):
    p = os.path.join(C, path)
    s = open(p, encoding='utf-8', newline='').read()
    crlf = '\r\n' in s
    s = s.replace('\r\n', '\n')
    t = f(s)
    if t != s:
        if crlf:
            t = t.replace('\n', '\r\n')
        open(p, 'w', encoding='utf-8', newline='').write(t)
        return True
    return False


def four_lib(s):
    s = s.replace(f'open import {P}Windows using (win)\n', f'open import {P}Windows using (Base ; win)\n')
    s = s.replace(f'open import {P}Completeness using (complete₃)\n', '')
    s = re.sub(r'^(wn\d+) : (?!Base 3 → )', r'\1 : Base 3 → ', s, flags=re.M)
    s = re.sub(r'^(wn\d+) = win (\d+) (\d+) complete₃ ', r'\1 b = win \2 \3 b ', s, flags=re.M)
    return s


def four_inst(s):
    s = re.sub(r'(?<!\()\b(W\d\d\.wn\d+)\b(?! b\))', r'(\1 b)', s)
    if 'Windows using (Base)' not in s:
        s = s.replace(f'open import {P}Four.WinSig using (Ws ; leaf ; node)\n',
                      f'open import {P}Four.WinSig using (Ws ; leaf ; node)\n'
                      f'open import {P}Windows using (Base)\n'
                      f'open import {P}Swaps using (facts)\n'
                      f'open import {P}Completeness using (complete₃)\n')
        s = s.rstrip('\n') + ('\n  where\n  b : Base 3\n'
                              '  b = record { facts = facts ; complete = complete₃ }\n')
    return s


def five_lib(s):
    s = s.replace(f'open import {P}SemanticSteps using (Complete)\n', f'open import {P}Windows using (Base)\n')
    s = re.sub(r'^((?:wl|wp)\d+) : Complete 4 → ', r'\1 : Base 4 → ', s, flags=re.M)
    return s


def resps(s):
    s = s.replace(f'open import {P}SemanticSteps using (Complete)\n', f'open import {P}Windows using (Base)\n')
    s = re.sub(r'^(pw\d) : \(c4 : Complete 4\) ', r'\1 : (c4 : Base 4) ', s, flags=re.M)
    return s


BASE4 = ('  c4 : Base 4\n'
         '  c4 = record { facts = facts ; complete = c }\n')


def five_instL(s):
    if 'Windows using (Base)' in s:
        return s
    s = s.replace(f'open import {P}SemanticSteps using (Complete)\n',
                  f'open import {P}SemanticSteps using (Complete)\n'
                  f'open import {P}Windows using (Base)\n'
                  f'open import {P}Swaps using (facts)\n')
    s = s.replace('\nwsL c4 =\n', '\nwsL c =\n')
    return s.rstrip('\n') + '\n  where\n' + BASE4


def five_inst(s):
    if 'Windows using (Base)' in s:
        return s
    s = s.replace(f'open import {P}SemanticSteps using (Complete)\n',
                  f'open import {P}SemanticSteps using (Complete)\n'
                  f'open import {P}Windows using (Base)\n'
                  f'open import {P}Swaps using (facts)\n')
    s = s.replace('\nws c4 = record\n', '\nws c = record\n')
    s = s.replace('\n  where L = wsL c4\n', '\n  where\n' + BASE4 + '  L = wsL c\n')
    return s


n = 0
for d, f in [('Four/Wins', four_lib), ('Five/Wins', five_lib)]:
    for x in sorted(os.listdir(os.path.join(C, d))):
        if x.endswith('.agda'):
            n += edit(f'{d}/{x}', f)
for path, f in [('Four/WinInst.agda', four_inst), ('Five/Resps.agda', resps),
                ('Five/WinInstL.agda', five_instL), ('Five/WinInst.agda', five_inst)]:
    n += edit(path, f)
print('edited', n)
