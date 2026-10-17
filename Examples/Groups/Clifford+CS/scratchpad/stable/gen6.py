"""Six-wire derivations over placed gates (Stable/Six/Engine.agda).

A placed gate is (k, lit, rho): the k-wire literal `lit` (an Agda
expression with a basic word) placed on six wires by the network rho
(swap positions, diagram order; LocalPlace.pl).  A derivation is a line
of placed gates and a list of steps:

  win(k, n, ys)        the n gates from position k replaced by ys, all of
                       them avoiding one wire w: checked on six wires and,
                       re-placed under the network tau that carries w to
                       the top, on five (what Agda evaluates);
  lemma(k, L, pi)      the lemma L (a derivation, between its first and
                       last lines) transported by the wire map pi;
  split(k) / merge(k)  a five-wire gate a . b as two, and back.

Every step is checked semantically (joint/cs.py fingerprints).
"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
SCR = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(SCR, 'joint'))
sys.path.insert(0, os.path.join(SCR, 'five'))
sys.path.insert(0, HERE)
import cs
import mac5
from nets import bubble, places

N = 6
SEM = {5: cs.Sem(5), 6: cs.Sem(6)}
LETTERS = os.path.join(os.path.dirname(SCR), 'Five', 'Letters.agda')

# ---------------------------------------------------------------- literals
class Lit:
    def __init__(self, name, expr, k, word):
        self.name, self.expr, self.k, self.word = name, expr, k, word

    def __repr__(self): return self.name


def mac(g): return mac5.word_of(mac5.mac_tree(g))


def letters_rhs(name):
    """the right-hand side of a definition in Five/Letters.agda."""
    with open(LETTERS, encoding='utf-8') as f:
        for line in f:
            if line.startswith(name + ' = '):
                return line[len(name) + 3:].strip()
    raise KeyError(name)


LIT = {}
def deflit(name, expr, k, word):
    LIT[name] = Lit(name, expr, k, word)
    return LIT[name]

Toff = deflit('Toff', 'Toff', 3, mac5.TOFF0)                  # target 0, controls 1 2
CCZ = deflit('CCZ', 'CCZ', 3, mac5.CCZ0)
CX10 = deflit('CX10', 'CX₁₀', 2, mac5._CX10)                  # control 1, target 0
CX01 = deflit('CX01', 'CX₀₁', 2, mac5._CX01)                  # control 0, target 1
CSl = deflit('CS', 'CS', 2, mac5.CS(0))
CS3 = deflit('CS3', '(CS • CS • CS)', 2, mac5.CS(0) * 3)
CK10 = deflit('CK10', 'CK₁₀', 2, mac5._CK10)


def box_lit(name, g):
    return deflit(name, 'b-' + name, 5, mac(g))

Sig0 = box_lit('Sb2-0-41-3', ('SBOX', 2, 0, (4, 1), 3))
SbA = box_lit('Sb0-1-42-3', ('SBOX', 0, 1, (4, 2), 3))
SbB = box_lit('Sb0-2-43-1', ('SBOX', 0, 2, (4, 3), 1))
Bx0 = box_lit('Bx2-0413', ('BOX', 2, 0, 4, 1, 3))
assert Sig0.word[:len(Bx0.word)] == Bx0.word
R0 = deflit('R0', '(' + letters_rhs('b-Sb2-0-41-3')[len('b-Bx2-0413 • '):] + ')', 5,
            Sig0.word[len(Bx0.word):])


def to_cs(word): return mac5.to_cs(word)


def swaps(rho):
    return [b for p in rho for b in mac5.SWAP(p)]


# ---------------------------------------------------------------- placed gates
class PG:
    def __init__(self, lit, rho):
        self.lit, self.rho = lit, list(rho)
        self.k = lit.k

    @property
    def f(self): return places(self.rho, N, self.k)

    def word(self):
        return swaps(self.rho) + self.lit.word + swaps(list(reversed(self.rho)))

    def wires(self): return set(self.f)

    def same(self, o): return self.lit is o.lit and self.f == o.f

    def agda(self):
        return f'g{self.k} {nl(self.rho)} {self.lit.expr}'

    def __repr__(self): return f'{self.lit.name}@{self.f}'


def at(lit, f):
    """the literal placed with its base wires on f."""
    assert len(f) == lit.k
    return PG(lit, bubble(list(f), N))


def nl(rho):
    return '(' + ' ∷ '.join(str(p) for p in rho) + (' ∷ []' if rho else '[]') + ')'


def word(gs): return to_cs([b for g in gs for b in g.word()])


def pword(gs, rhos):
    return to_cs([b for g, r in zip(gs, rhos)
                  for b in swaps(r) + g.lit.word + swaps(list(reversed(r)))])


def agda_list(gs):
    return '(' + ' ∷ '.join(g.agda() for g in gs) + (' ∷ []' if gs else '[]') + ')'


def frames(tau, gs, rhos):
    """Agda Frames tau gs gs' with gs' the gates placed by rhos."""
    fs = []
    for g, r in zip(gs, rhos):
        refls = ' '.join(['Eq.refl'] * g.k)
        fs.append(f'fr{g.k} {nl(tau)} {nl(g.rho)} {nl(r)} {g.lit.expr} {refls}')
    return '(' + ' ∷ '.join(fs) + (' ∷ []' if fs else '[]') + ')'


# ---------------------------------------------------------------- controlled lines
SEM[4] = cs.Sem(4)
# the S-boxes as λ¹-images of the four-wire domain's CS: (Agda generator, shift)
SBOX_GEN = {'Sb2-0-41-3': ('(gate₂ CS-gate)', 0), 'Sb0-1-42-3': ('(gate₂ CS-gate ↥)', 1),
            'Sb0-2-43-1': ('(gate₂ CS-gate ↥ ↥)', 2)}


def ctrl_line(gs, rhos):
    """Agda CtrlLine of gates placed on five wires by rhos (control on the
    top wire 4), and the domain word (four wires) it denotes."""
    facts, dom = [], []
    for g, r in zip(gs, rhos):
        if g.lit.name in SBOX_GEN:
            gen, sh = SBOX_GEN[g.lit.name]
            assert all(p <= 2 for p in r), (g, r)
            facts.append(f'sbox {nl(r)} {gen} Eq.refl')
            dom += swaps(r) + mac5.CS(sh) + swaps(list(reversed(r)))
        else:
            f = places(r, N - 1, g.k)
            if g.lit is CSl:
                i = [w for w in f if w != 4]; assert 4 in f and len(i) == 1; i = i[0]
                gen, d = '(gate₁ S-gate' + ' ↥' * i + ')', mac5.S(i)
            elif g.lit is CK10:
                assert f[1] == 4; i = f[0]
                gen, d = '(gate₁ K-gate' + ' ↥' * i + ')', mac5.K(i)
            else:
                raise ValueError(g)
            facts.append(f'small (g{g.k} {nl(r)} {g.lit.expr}) {gen} Eq.refl')
            dom += d
    return '(' + ' ∷ᶜ '.join(facts + ['[]ᶜ']) + ')', dom


# ---------------------------------------------------------------- derivations
class Deriv:
    def __init__(self, name, start):
        self.name = name
        self.start = list(start)
        self.cur = list(start)
        self.steps = []          # Agda expressions of Step values
        self.lines = [list(start)]
        self.heavy = []

    def check_line(self, new):
        assert SEM[6].eq(word(self.cur), word(new)), f'{self.name}: step {len(self.steps)} changes the operator'

    def win(self, k, n, ys, idle=None):
        seg = self.cur[k:k + n]
        used = set()
        for g in seg + ys:
            used |= g.wires()
        free = [w for w in range(N) if w not in used]
        assert free, f'{self.name}: step {len(self.steps)} is no window: {seg} -> {ys}'
        w = idle if idle is not None else free[-1]
        assert w in free
        assert SEM[6].eq(word(seg), word(ys)), f'{self.name}: window {len(self.steps)} {seg} -> {ys}'
        others = [x for x in range(N) if x != w]
        tau = bubble(others, N)
        def re(g):
            r = bubble([others.index(x) for x in g.f], N - 1)
            assert places(tau + r, N, g.k) == g.f
            return r
        rs, rt = [re(g) for g in seg], [re(g) for g in ys]
        assert SEM[5].eq(pword(seg, rs), pword(ys, rt))
        fx, fy = frames(tau, seg, rs), frames(tau, ys, rt)
        sbox = any(g.lit.name in SBOX_GEN for g in seg + ys)
        ctl = None
        if sbox:
            try:
                ctl = (ctrl_line(seg, rs), ctrl_line(ys, rt))
            except (ValueError, AssertionError):
                ctl = None
        if ctl is not None:
            (cx, dx), (cy, dy) = ctl
            assert SEM[4].eq(to_cs(dx), to_cs(dy))
            self.steps.append(f'at {k} {n} {agda_list(ys)}\n      (winC {nl(tau)} {fx}\n         {fy}\n'
                              f'         Eq.refl Eq.refl\n         {cx}\n         {cy}\n         Eq.refl)')
        else:
            self.steps.append(f'at {k} {n} {agda_list(ys)}\n      (win {nl(tau)} {fx}\n         {fy}\n         Eq.refl Eq.refl Eq.refl)')
        self.cur = self.cur[:k] + ys + self.cur[k + n:]
        self.lines.append(list(self.cur)); self.heavy.append(sbox and ctl is None)

    def lemma(self, k, L, pi, backwards=False):
        """L transported by the wire map pi (canonical wire -> wire)."""
        xs, ys = (L.cur, L.start) if backwards else (L.start, L.cur)
        n = len(xs)
        seg = self.cur[k:k + n]
        Nw = bubble(list(pi), N)
        def tr(g):
            return at(g.lit, [pi[x] for x in g.f])
        for a, c in zip(seg, xs):
            assert a.same(tr(c)), f'{self.name}: lemma {L.name} does not match at {k}: {a} vs {tr(c)}'
            assert places(Nw + c.rho, N, c.k) == a.f
        new = [tr(c) for c in ys]
        fx, fy = frames(Nw, seg, [c.rho for c in xs]), frames(Nw, new, [c.rho for c in ys])
        e = f'(PB.sym {L.name})' if backwards else L.name
        if not Nw and all(a.rho == c.rho for a, c in zip(seg, xs)):
            self.steps.append(f'at {k} {n} {agda_list(new)} {e}')
        else:
            self.steps.append(f'at {k} {n} {agda_list(new)}\n      (transport {nl(Nw)} {fx}\n         {fy}\n         {e})')
        self.check_line(self.cur[:k] + new + self.cur[k + n:])
        self.cur = self.cur[:k] + new + self.cur[k + n:]
        self.lines.append(list(self.cur)); self.heavy.append(False)

    def split(self, k, whole, a, b):
        g = self.cur[k]
        assert g.lit is whole and g.k == 5
        assert whole.word == a.word + b.word
        new = [PG(a, g.rho), PG(b, g.rho)]
        self.steps.append(f'at {k} 1 {agda_list(new)} (split5 {nl(g.rho)} {a.expr} {b.expr})')
        self.cur = self.cur[:k] + new + self.cur[k + 1:]
        self.lines.append(list(self.cur)); self.heavy.append(False)

    def merge(self, k, whole):
        a, b = self.cur[k], self.cur[k + 1]
        assert a.k == 5 and b.k == 5 and a.rho == b.rho and whole.word == a.lit.word + b.lit.word
        new = [PG(whole, a.rho)]
        self.steps.append(f'at {k} 2 {agda_list(new)} (PB.sym (split5 {nl(a.rho)} {a.lit.expr} {b.lit.expr}))')
        self.cur = self.cur[:k] + new + self.cur[k + 2:]
        self.lines.append(list(self.cur)); self.heavy.append(False)

    def parts(self, max_heavy=1):
        """cut the steps into parts with at most max_heavy heavy windows."""
        cuts, h = [0], 0
        for i, hv in enumerate(self.heavy):
            if hv and h == max_heavy:
                cuts.append(i); h = 0
            h += hv
        cuts.append(len(self.steps))
        out = []
        for j in range(len(cuts) - 1):
            p = Deriv.__new__(Deriv)
            p.name = f'{self.name}{j + 1}'
            p.start, p.cur = self.lines[cuts[j]], self.lines[cuts[j + 1]]
            p.steps = self.steps[cuts[j]:cuts[j + 1]]
            out.append(p)
        return out

    def agda(self, indent='  '):
        body = (f'\n{indent}▸ ').join(self.steps)
        return (f'{self.name} : 6 ⊢ᵧ ⟪ {agda_list(self.start)} ⟫₆ ≈ ⟪ {agda_list(self.cur)} ⟫₆\n'
                f'{self.name} = run {{{agda_list(self.start)}}} {{{agda_list(self.cur)}}}\n{indent}( {body}\n{indent}▸ done)\n')


# ---------------------------------------------------------------- modules
OUT = os.path.join(os.path.dirname(SCR), 'Stable', 'Six')
PARAM = '(c₅ : ∀ {u v : Circuit 5} → ⟦ u ⟧ ~ ⟦ v ⟧ → 5 ⊢ᵧ u ≈ v)'


def module(name, title, doc, derivs, imports=(), script='gen6.py'):
    lines = ['-' * 72, '-- Presentations of groups', '--', f'-- {title}', '--']
    lines += ['-- ' + l if l else '--' for l in doc.strip('\n').split('\n')]
    lines += ['--', f'-- Generated by scratchpad/stable/{script}; do not edit.', '-' * 72, '',
              '{-# OPTIONS --without-K --safe #-}', '',
              'open import Examples.Groups.Clifford+CS.Semantics using (_~_)',
              'open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)',
              'open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)',
              'open import Examples.Groups.Clifford+CS.Stable.Rules using (_⊢ᵧ_≈_)', '',
              f'module Examples.Groups.Clifford+CS.Stable.Six.{name}', f'  {PARAM} where', '',
              'open import Data.List using (List ; [] ; _∷_)',
              'open import Relation.Binary.PropositionalEquality as Eq using (_≡_)',
              'open import Word.Base using (_•_)', '',
              'import Presentation.Base as PB', '',
              'open import Examples.Groups.Clifford+CS.Syntactics',
              'FIVE-LETTERS',
              'open import Examples.Groups.Clifford+CS.Stable.Six.Engine']
    lines += list(imports)
    lines += ['', 'open Window c₅', '']
    for d in derivs:
        lines.append(d.agda())
    import re
    used = sorted(set(re.findall(r'b-[A-Za-z0-9⁻-]+', chr(10).join(lines[20:]))))
    fl = ('open import Examples.Groups.Clifford+CS.Five.Letters using (' + ' ; '.join(used) + ')') if used else ''
    lines = [fl if l == 'FIVE-LETTERS' else l for l in lines]
    with open(os.path.join(OUT, name + '.agda'), 'w', encoding='utf-8') as f:
        f.write('\n'.join(lines))
