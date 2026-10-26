"""Five.F1, F2 and F4 through the letters of λ¹ (Five.LamLetters).

    python3 lamletters.py REPO

Each clause of Five.F1 (f1₀, f1₁), Five.F2 and Five.F4 compared λ¹ of
generators or rules with the letters of its derivation by flattening
both sides (`by-flat Eq.refl` twice): tens of thousands of generators
for the rules with many CS, an S-box each.  This pass makes them
`via₀ RULE (LEM c4)` (`via₁` at offset 1), `lam2 g h (LEM c4)` and
`lam4 g h (LEM c4)`: λ¹ of a generator is the word of one letter
(`lamG`), proved once per generator, and the derivation's statement is
compared with those letters.  Run it after gen_lam.py and the passes that
follow it (di.py); idempotent.
"""
import os, re, sys

REPO = sys.argv[1]
FIVE = os.path.join(REPO, 'Examples/Groups/Clifford+CS/Five')
BF = r'trans \(by-flat Eq\.refl\) \(trans \((\S+) c4\) \(by-flat Eq\.refl\)\)'
FLAT = 'open import Examples.Groups.Clifford+CS.Five.Flat using (by-flat)\n'
LAM = 'open import Examples.Groups.Clifford+CS.Five.LamLetters using ({})\n'


def rewrite(name, rules, names, note):
    p = os.path.join(FIVE, name)
    s = open(p, encoding='utf-8').read()
    n = 0
    for pat, rep in rules:
        s, k = re.subn(pat, rep, s, flags=re.M)
        n += k
    imp = LAM.format(' ; '.join(names))
    if imp not in s:
        if FLAT in s:
            s = s.replace(FLAT, imp) if 'by-flat' not in s.replace(FLAT, '') else s.replace(FLAT, FLAT + imp)
        else:
            last = list(re.finditer(r'^open import .*\n', s, re.M))[-1]
            s = s[:last.end()] + imp + s[last.end():]
    if 'Five.LamLetters' not in s.split('-' * 72 + '\n\n')[0]:
        s = s.replace('-' * 72 + '\n\n', note + '-' * 72 + '\n\n', 1)
    old = open(p, encoding='utf-8').read()
    if s != old:
        open(p, 'w', encoding='utf-8', newline='\n').write(s)
    print(f'{name}: {n} clauses rewritten')


NOTE = ('-- Each side is compared with its derivation letter by letter\n'
        '-- (Five.LamLetters, scratchpad/five/lamletters.py).\n')
rewrite('F1.agda',
        [(r'^(f1₀ c4 (\S+)) = ' + BF + '$', r'\1 = via₀ \2 (\3 c4)'),
         (r'^(f1₁ c4 (\S+)) = ' + BF + '$', r'\1 = via₁ \2 (\3 c4)')],
        ['via₀', 'via₁'], NOTE)
rewrite('F4.agda',
        [(r'^(f4 c4 (\(.*?\)) (\(.*?\))) = ' + BF + '$', r'\1 = lam4 \2 \3 (\4 c4)')],
        ['lam4'], NOTE)
rewrite('F2.agda',
        [(r'^(f2 c4 (\(.*?\)) (\(.*?\)) _) = ' + BF + '$', r'\1 = lam2 \2 \3 (\4 c4)'),
         (r'^(f2 c4 (\(.*?\)) (\(.*?\)) _) = sym \(' + BF + r'\)$', r'\1 = sym (lam2 \3 \2 (\4 c4))')],
        ['lam2'], NOTE)
