# State each window of Four/Wins over the macro letters, as Four/D uses it:
#
#   python3 winmac4.py REPO
#
# Run after reflect4.py (which calls it): the spelling of window n is read
# off Four/D's tables (`qK = eqn SEG YS (wn n W)`).  A window's type was
# `(₁₊ (i +ℕ r)) ⊢ insʷ i u ≈ insʷ i v`; stated as `⟪ SEG ⟫ʷ ≈ ⟪ YS ⟫ʷ`
# the conversion between the two spellings is checked in the window
# library, in parallel with the others, where Four.WinInst used to check
# all 2,584 of them in one module (179 s), and WinInst's proofs have the
# tree's types on the nose.
import os, re, sys

REPO = sys.argv[1]
T = os.path.join(REPO, 'Examples/Groups/Clifford+CS/Four')
def term(s, i):
    """the list expression starting at s[i]: `[]` or a balanced `( … )`"""
    if s.startswith('[]', i):
        return s[i:i + 2], i + 2
    d = 0
    for k in range(i, len(s)):
        d += (s[k] == '(') - (s[k] == ')')
        if d == 0:
            return s[i:k + 1], k + 1
    raise ValueError(s[i:])


spell = {}
for f in sorted(os.listdir(os.path.join(T, 'D'))):
    if re.fullmatch(r'D\d+\.agda', f):
        for line in open(os.path.join(T, 'D', f), encoding='utf-8'):
            m = re.match(r'  q\d+ = eqn ', line)
            if not m or not line.rstrip().endswith(' W)') or '(wn ' not in line:
                continue
            seg, i = term(line, m.end())
            ys, i = term(line, i + 1)
            pm = re.fullmatch(r' \(wn (\d+) W\)', line[i:].rstrip())
            if pm:
                spell.setdefault(int(pm.group(1)), (seg, ys))
fixed = 0
for f in sorted(os.listdir(os.path.join(T, 'Wins'))):
    if not re.fullmatch(r'W\d+\.agda', f):
        continue
    p = os.path.join(T, 'Wins', f)
    s = open(p, encoding='utf-8').read()
    s = s.replace('-- (Windows.win, one evaluation).  Written by scratchpad/four/winlib4.py.\n',
                  '-- (Windows.win, one evaluation), stated over the macro letters as\n'
                  '-- Four/D uses it.  Written by scratchpad/four/winlib4.py and restated\n'
                  '-- by winmac4.py.\n')
    if 'Data.List using' not in s:
        s = s.replace('open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)\n',
                      'open import Data.List using ([] ; _∷_)\n'
                      'open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)\n')
    if 'Four.Chain using' not in s:
        s = s.replace('open import Examples.Groups.Clifford+CS.Windows using (win ; insʷ)\n',
                      'open import Examples.Groups.Clifford+CS.Windows using (win)\n'
                      'open import Examples.Groups.Clifford+CS.Four.Chain using (⟪_⟫ʷ ; _≈_)\n'
                      'open import Examples.Groups.Clifford+CS.Four.Letters\n')

    def sub(m):
        global fixed
        seg, ys = spell[int(m.group(1))]
        fixed += 1
        return f'wn{m.group(1)} : ⟪ {seg} ⟫ʷ ≈ ⟪ {ys} ⟫ʷ'
    s = re.sub(r'^wn(\d+) : .*$', sub, s, flags=re.M)
    open(p, 'w', encoding='utf-8', newline='\n').write(s)
print(f'{fixed} windows restated, {len(spell)} spellings')
