"""The six-wire base facts of (F4) (Stable.Mixed.MixBase b₁, b₂, b₃ 0).

The white versions of Stable.Six.Comm1, Comm2 and Comm3: the letter
reaching the top domain wire is X on the control around its λ¹-image.
X is a separate one-wire gate on wire 5, so the commutation window,
which holds both X's and an S-box, is decided by evaluation (one
module per such window), and the moves of the S-boxes are the same as
in the black facts.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen6 import *
import six_su
from six_facts import cyc, CSup, CKup, ST, sig, pi_of, CSl, CK10

X4 = deflit('X4', '(Xᵗ 4)', 5, mac5.lift(mac5._X, 4))
Xl = deflit('X', 'X', 1, mac5._X)
Xg = at(Xl, [5])


class MixFact:
    """lhs (A • B • C) • D and rhs D • (A • B • C), as lines of four gates."""
    def __init__(self, name, a, b, d, d_lhs, b_up, d_up, deriv):
        self.name, self.a, self.b, self.d = name, a, b, d
        self.d_lhs, self.b_up, self.d_up = d_lhs, b_up, d_up
        self.deriv = deriv
        self.parts = None

    def lhs(self):
        return f'(Xᵗ 5 • {self.b} • Xᵗ 5) • {self.d_lhs}'

    def rhs(self):
        return f'{self.d_lhs} • (Xᵗ 5 • {self.b} • Xᵗ 5)'

    def agda(self):
        d = self.deriv
        if self.parts is None:
            chain = d.agda()
        else:
            comp = self.parts[-1].name
            for p in reversed(self.parts[:-1]):
                comp = f'PB.trans {p.name} ({comp})'
            chain = (f'{d.name} : 6 ⊢ᵧ ⟪ {agda_list(d.start)} ⟫₆ ≈ ⟪ {agda_list(d.cur)} ⟫₆{chr(10)}'
                     f'{d.name} = {comp}{chr(10)}')
        s0, s1, s2, s3 = d.start
        e0, e1, e2, e3 = d.cur

        def conv(nm, expr, g, up):
            if up:
                return (f'  {nm} : 6 ⊢ᵧ {expr} ↑ ≈ ⟦ {g.agda()} ⟧₆\n'
                        f'  {nm} = embed (PB.trans (↑≈ {expr}) (T₆.by-assoc Eq.refl))')
            return (f'  {nm} : 6 ⊢ᵧ {expr} ≈ ⟦ {g.agda()} ⟧₆\n'
                    f'  {nm} = embed (T₆.by-assoc Eq.refl)')
        b0 = self.b_up
        lines = [
            conv('cx', '(Xᵗ 4)', s0, True),
            conv('cb', b0, s1, True),
            conv('cd', self.d_lhs, s3, self.d_up),
            conv('cx′', '(Xᵗ 4)', e1, True),
            conv('cb′', b0, e2, True),
            conv('cd′', self.d_lhs, e0, self.d_up),
            f'  re : 6 ⊢ᵧ {self.lhs()} ≈ Xᵗ 5 • {self.b} • Xᵗ 5 • {self.d_lhs}\n'
            f'  re = embed (T₆.by-assoc Eq.refl)']
        body = '\n'.join(lines)
        return (chain + '\n' +
                f'{self.name} : 6 ⊢ᵧ {self.lhs()} ≈ {self.rhs()}\n'
                f'{self.name} = PB.trans re (PB.trans (PB.cong cx (PB.cong cb (PB.cong cx cd)))\n'
                f'  (PB.trans {d.name} (PB.sym (PB.cong cd′ (PB.cong cx′ (PB.cong cb′ cx′))))))\n'
                f'  where\n{body}\n')


def xs_in(d, positions):
    for p in positions:
        d.win(p, 1, [Xg], idle=0)


def xs_out(d, positions):
    for p in positions:
        d.win(p, 1, [PG(X4, cyc)], idle=0)


def b1(su, lit, name, gexpr):
    g = PG(lit, ST)
    assert g.f == [0, 5]
    d = Deriv(name + '-chain', [PG(X4, cyc), PG(SbB, cyc), PG(X4, cyc), g])
    xs_in(d, [0, 2])
    d.win(1, 1, [sig(3, 4, 1, 2, 5)], idle=0)                    # respelt
    p = pi_of(3, 4, 1, 2, 5, 0)
    d.lemma(1, su, p)
    d.win(0, 4, [g, Xg, d.cur[1], Xg], idle=1)                    # the commutation
    d.lemma(2, su, p, backwards=True)
    d.win(2, 1, [PG(SbB, cyc)], idle=0)
    xs_out(d, [1, 3])
    return MixFact(name, None, 'b-Sb0-2-43-1 ↑', None, gexpr, 'b-Sb0-2-43-1', False, d)


def b2(su, uplit, lit, name, upexpr):
    d = Deriv(name + '-chain', [PG(X4, cyc), PG(uplit, cyc), PG(X4, cyc), PG(Sig0, [4])])
    xs_in(d, [0, 2])
    g = at(lit, [4, 5])
    d.win(1, 1, [g], idle=0)
    p = pi_of(0, 1, 2, 3, 5, 4)
    d.lemma(3, su, p)
    d.win(0, 4, [d.cur[3], Xg, g, Xg], idle=2)                    # the commutation
    d.lemma(0, su, p, backwards=True)
    d.win(2, 1, [PG(uplit, cyc)], idle=0)
    xs_out(d, [1, 3])
    return MixFact(name, None, f'{upexpr} ↑', None, 'stretch b-Sb2-0-41-3', upexpr, False, d)


def b3(su):
    d = Deriv('mix₃-chain', [PG(X4, cyc), PG(SbB, cyc), PG(X4, cyc), PG(Sig0, [4])])
    xs_in(d, [0, 2])
    d.win(1, 1, [sig(3, 4, 1, 2, 5)], idle=0)                    # respelt
    pa = pi_of(3, 4, 1, 2, 5, 0)
    d.lemma(1, su, pa)
    d.win(1, 1, [sig(3, 4, 2, 0, 5)], idle=1)                    # F0
    pb = pi_of(3, 4, 2, 0, 5, 1)
    d.lemma(1, su, pb)
    pc = pi_of(0, 1, 2, 3, 5, 4)
    d.lemma(3, su, pc)
    d.win(0, 4, [d.cur[3], Xg, d.cur[1], Xg], idle=2)             # the commutation
    d.lemma(0, su, pc, backwards=True)
    d.lemma(2, su, pb, backwards=True)
    d.win(2, 1, [sig(3, 4, 0, 2, 5)], idle=1)                    # F0
    d.lemma(2, su, pa, backwards=True)
    d.win(2, 1, [PG(SbB, cyc)], idle=0)
    xs_out(d, [1, 3])
    return MixFact('mix₃', None, 'b-Sb0-2-43-1 ↑', None, 'stretch b-Sb2-0-41-3', 'b-Sb0-2-43-1', False, d)


def group(modname, title, doc, facts, imp):
    allimp = list(imp)
    mods = []
    for f in facts:
        f.parts = f.deriv.parts(1)
        if len(f.parts) == 1:
            f.parts = None
            continue
        for j, p in enumerate(f.parts):
            mn = f'{modname}{f.tag}{j + 1}'
            module(mn, f'{title}: part {j + 1} of {f.name}',
                   f'Steps of `{f.deriv.name}` (Stable.Six.{modname}), cut so that each{chr(10)}module evaluates at most one S-box window.',
                   [p], imports=imp, script='six_mix.py')
            allimp.append(f'open import Examples.Groups.Clifford+CS.Stable.Six.{mn} c₅ using ({p.name})')
            mods.append(mn)
    module(modname, title, doc, facts, imports=allimp, script='six_mix.py')
    return mods + [modname]


if __name__ == '__main__':
    _, su = six_su.build()
    imp = ['open import Examples.Groups.Clifford+CS.Lambda using (stretch ; CSᵗ ; CKᵗ ; Xᵗ)',
           'open import Examples.Groups.Clifford+CS.MultiControlled using (CK₁₀)',
           'open import Examples.Groups.Clifford+CS.Stable.Rules using (embed)',
           'open import Examples.Groups.Clifford+CS.Stable.Six.Su c₅ using (su)']
    f1s = b1(su, CSl, 'mix₁-S', 'CSᵗ 4'); f1s.tag = 'A'
    f1k = b1(su, CK10, 'mix₁-K', 'CKᵗ 4'); f1k.tag = 'B'
    f2s = b2(su, CSup, CSl, 'mix₂-S', '(CS ↑ ↑ ↑)'); f2s.tag = 'C'
    f2k = b2(su, CKup, CK10, 'mix₂-K', '(CK₁₀ ↑ ↑ ↑)'); f2k.tag = 'D'
    f3 = b3(su); f3.tag = 'E'
    doc = """{what} on six wires, a base fact of Stable.Mixed.MixBase: {comm}
with X on the control around the first letter.  The S-boxes move as
there (Stable.Six.Su, F0 and respelling windows); the commutation
window, which holds the two X's, is decided by evaluation."""
    mods = []
    for f, mn, what, comm in [
            (f1s, 'Mix1S', 'λ⁰ of the CS on the top two wires of a five-wire domain against S on wire 0', 'Stable.Six.Comm1'),
            (f1k, 'Mix1K', 'λ⁰ of the CS on the top two wires of a five-wire domain against K on wire 0', 'Stable.Six.Comm1'),
            (f2s, 'Mix2S', 'λ⁰ of S on the top wire of a five-wire domain against the CS on the wires 0 1', 'Stable.Six.Comm2'),
            (f2k, 'Mix2K', 'λ⁰ of K on the top wire of a five-wire domain against the CS on the wires 0 1', 'Stable.Six.Comm2'),
            (f3, 'Mix3', 'λ⁰ of the CS on the top two wires of a five-wire domain against the CS on the wires 0 1', 'Stable.Six.Comm3')]:
        module(mn, what[0].upper() + what[1:], doc.format(what=what[0].upper() + what[1:], comm=comm), [f], imports=imp, script='six_mix.py')
        mods.append(mn)
    print(' '.join(mods))
