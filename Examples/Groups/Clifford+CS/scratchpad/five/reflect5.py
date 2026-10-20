# Turn Five/D's chains into derivations by reflection (Five.Reflect), as
# scratchpad/four/reflect4.py does for Four/D:
#
#   python3 reflect5.py REPO [TREE]      (TREE Five, the default, or FiveV)
#
# Run on the chain form (`bN : Chain … ; bN = at k n ys proof ▸ … ▸ done`),
# after emit5.py, repack.py and winlib5.py.  It writes Five/Reflect.agda
# (by ../four/reflect4_engine.py) and rewrites every module of Five/D: a
# lemma keeps its statement, `lem-X : Ws → ⟪ L ⟫ʷ ≈ ⟪ R ⟫ʷ` (or WsL), and
# becomes `lem-X c4 = derive L R steps Eq.refl`, its steps `rw k (qN c4)`,
# `rw⁻ k (qN c4)` — qN an entry of the module's table of its distinct
# equations, a function of the windows — or `re k n ys`, a re-bracketing
# (`by-assoc`) or a box fold (`refl`), both decided by comparing the
# generators the two sides spell.  Nothing outside Five/D changes.
import os, re, sys, subprocess

REPO = sys.argv[1]
TREE = sys.argv[2] if len(sys.argv) > 2 else 'Five'
HERE = os.path.dirname(os.path.abspath(__file__))
T = os.path.join(REPO, 'Examples/Groups/Clifford+CS')
D = os.path.join(T, TREE, 'D')
P = 'Examples.Groups.Clifford+CS.'
subprocess.run([sys.executable, os.path.join(HERE, '../four/reflect4_engine.py'), REPO, TREE], check=True)


def rd(p):
    return open(p, encoding='utf-8').read()


def wr(p, s):
    open(p, 'w', encoding='utf-8', newline='\n').write(s)


def balanced(s, i):
    d = 0
    for k in range(i, len(s)):
        c = s[k]
        if c == '(':
            d += 1
        elif c == ')':
            d -= 1
            if d == 0:
                return k + 1
    raise ValueError(s[i:i + 80])


def letters(t):
    t = t.strip()
    if t == '[]':
        return []
    assert t[0] == '(' and t.endswith('∷ [])'), t[:80]
    return [x.strip() for x in t[1:-len('∷ [])')].split(' ∷ ') if x.strip()]


def lst(xs):
    return '[]' if not xs else '(' + ' ∷ '.join(xs) + ' ∷ [])'


def chains(text):
    out = []
    for m in re.finditer(r'^  (b\d+) : Chain ', text, re.M):
        i = m.end()
        j = balanced(text, i) if text[i] == '(' else i + 2
        start = letters(text[i:j])
        dm = re.search(r'^  ' + m.group(1) + r' = ', text[j:], re.M)
        p = j + dm.end()
        steps = []
        while True:
            while text[p] in ' \n':
                p += 1
            if text.startswith('done', p):
                break
            mm = re.match(r'at (\d+) (\d+) ', text[p:])
            assert mm, text[p:p + 80]
            p += mm.end()
            if text.startswith('[]', p):
                ys, p = [], p + 2
            else:
                q = balanced(text, p)
                ys = letters(text[p:q])
                p = q
            while text[p] == ' ':
                p += 1
            q = balanced(text, p) if text[p] == '(' else p + len(re.match(r'\S+', text[p:]).group(0))
            steps.append((int(mm.group(1)), int(mm.group(2)), ys, text[p:q]))
            p = q
            while text[p] in ' \n':
                p += 1
            assert text.startswith('▸', p), text[p:p + 40]
            p += 1
        out.append((start, steps))
    return out


LEM = r'^(-- .*\n)?lem-\S+ : '
mods = sorted(f[:-5] for f in os.listdir(D) if re.fullmatch(r'[A-Z]\d+\.agda', f))
nst = nre = neq = 0
for m in mods:
    text = rd(os.path.join(D, m + '.agda'))
    assert f'{TREE}.Reflect' not in text, f'{TREE}/D is already reflected'
    first = re.search(LEM, text, re.M).start()
    header, body = text[:first], text[first:]
    starts = [mm.start() for mm in re.finditer(LEM, body, re.M)] + [len(body)]
    table, out = {}, []
    for a, b in zip(starts, starts[1:]):
        blk = body[a:b]
        mm = re.search(r'^(lem-\S+) : (\S+) → ⟪ (.*) ⟫ʷ ≈ ⟪ (.*) ⟫ʷ$', blk, re.M)
        name, ty, L, R = mm.groups()
        comment = blk[:mm.start()].rstrip('\n')
        dm = re.search(r'^' + re.escape(name) + r' (\S+) = (.*)$', blk, re.M)
        arg, rhs = dm.groups()
        stmt = ('\n' + comment if comment else '') + f'\n{name} : {ty} → ⟪ {L} ⟫ʷ ≈ ⟪ {R} ⟫ʷ'
        if rhs == 'refl':
            out.append(stmt + f'\n{name} {arg} = refl')
            continue
        cur = letters(L)
        steps, newq = [], []
        for start, ss in chains(blk):
            assert start == cur, name
            for k, n, ys, proof in ss:
                seg = cur[k:k + n]
                cur = cur[:k] + ys + cur[k + n:]
                nst += 1
                if proof in ('(by-assoc Eq.refl)', '(refl)'):
                    steps.append(f're {k} {n} {lst(ys)}')
                    nre += 1
                    continue
                if proof.startswith('(sym ') and proof.endswith(')'):
                    kind, key = 'rw⁻', (ty, tuple(ys), tuple(seg), proof[5:-1])
                else:
                    kind, key = 'rw', (ty, tuple(seg), tuple(ys), proof)
                if arg != 'c4':
                    key = (ty, key[1], key[2], re.sub(r'(?<![\w-])' + re.escape(arg) + r'(?![\w-])', 'c4', key[3]))
                if key not in table:
                    table[key] = f'q{len(table) + 1}'
                    newq.append(key)
                steps.append(f'{kind} {k} ({table[key]} {arg})')
        assert cur == letters(R), name
        blkout = []
        if newq:
            blkout.append('\nprivate')
            for key in newq:
                blkout.append(f'  {table[key]} : {key[0]} → Eqn')
                blkout.append(f'  {table[key]} c4 = eqn {lst(list(key[1]))} {lst(list(key[2]))} {key[3]}')
        blkout.append(stmt)
        blkout.append(f'{name} {arg} = derive {L} {R}')
        blkout.append('  (' + ' ∷\n   '.join(steps) + ' ∷ []) Eq.refl')
        out.append('\n'.join(blkout))
    neq += len(table)
    header = header.replace(
        f'open import {P}{TREE}.Chain\n',
        f'open import {P}{TREE}.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)\n'
        f'open import {P}{TREE}.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)\n')
    assert f'{TREE}.Reflect' in header, m
    wr(os.path.join(D, m + '.agda'), header.rstrip('\n') + '\n' + '\n'.join(out) + '\n')
print(f'{len(mods)} modules, {nst} steps ({nre} re-bracketings and folds), {neq} table equations')
