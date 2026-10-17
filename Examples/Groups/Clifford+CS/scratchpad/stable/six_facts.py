"""The seven six-wire equations of Stable.HypFrom.Six, from the switch.

Each S-box is moved by the borrowed-wire switch `su` (Stable.Six.Su,
transported along a wire map) until the two gates of an equation share
five wires, where a window decides it; the F0 windows exchange the roles
of the box wire and the borrowed wire, and the respelling windows pass
between the letters b-Sb0-1-42-3, b-Sb0-2-43-1 and b-Sb2-0-41-3.

Wires of the canonical S-box of `su` (b-Sb2-0-41-3 one wire up):
x = 1, y = 2, u = 3, A = 4, t = 5, wire 0 idle.  A wire map pi sends the
canonical wires to the S-box's roles (pi[0] the wire the box wire moves
to).
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen6 import *
import six_su

cyc = [0, 1, 2, 3, 4]
CSup = deflit('CSup3', '(CS ↑ ↑ ↑)', 5, mac5.lift(mac5.CS(0), 3))
CKup = deflit('CKup3', '(CK₁₀ ↑ ↑ ↑)', 5, mac5.lift(mac5._CK10, 3))
ST = [4, 3, 2, 1]                       # stretch⁴: wire 1 of a two-wire gate to wire 5


def sig(x, y, u, A, t):
    """b-Sb2-0-41-3 (base x=0, y=1, u=2, A=3, t=4) on those wires."""
    return at(Sig0, [x, y, u, A, t])


def pi_of(x, y, u, A, t, z):
    """the wire map from the canonical S-box to Σ(x; t, y | u, A), the box
    wire moving to z."""
    pi = [None] * 6
    pi[0], pi[1], pi[2], pi[3], pi[4], pi[5] = z, x, y, u, A, t
    assert sorted(pi) == list(range(6))
    return pi


class Fact:
    def __init__(self, name, lhs, rhs, d, lconv, rconv):
        self.name, self.lhs, self.rhs, self.d = name, lhs, rhs, d
        self.lconv, self.rconv = lconv, rconv
        self.parts = None

    def chain(self):
        d = self.d
        if self.parts is None:
            return d.agda()
        comp = self.parts[-1].name
        for p in reversed(self.parts[:-1]):
            comp = f'PB.trans {p.name} ({comp})'
        nl_ = chr(10)
        return (f'{d.name} : 6 ⊢ᵧ ⟪ {agda_list(d.start)} ⟫₆ ≈ ⟪ {agda_list(d.cur)} ⟫₆{nl_}'
                f'{d.name} = {comp}{nl_}')

    def agda(self):
        d = self.d
        chain = self.chain()
        def conv(cs, gs, side):
            out = []
            names = []
            for i, (c, g) in enumerate(zip(cs, gs)):
                nm = f'{side}{i}'
                names.append(nm)
                if c[0] == 'up':
                    pf = f'embed (PB.trans (↑≈ {c[1]}) (T₆.by-assoc Eq.refl))'
                else:
                    pf = 'embed (T₆.by-assoc Eq.refl)'
                out.append(f'  {nm} : 6 ⊢ᵧ {c[1]}{" ↑" if c[0] == "up" else ""} ≈ ⟦ {g.agda()} ⟧₆\n  {nm} = {pf}')
            e = names[0] if len(names) == 1 else f'PB.cong {names[0]} {names[1]}'
            return e, out
        le, lo = conv(self.lconv, d.start, 'l')
        re_, ro = conv(self.rconv, d.cur, 'r')
        body = '\n'.join(lo + ro)
        return (chain + '\n' +
                f'{self.name} : 6 ⊢ᵧ {self.lhs} ≈ {self.rhs}\n'
                f'{self.name} = PB.trans ({le}) (PB.trans {d.name} (PB.sym ({re_})))\n'
                f'  where\n{body}\n')


def sw12(su):
    d = Deriv('sw₁₂-chain', [PG(Sig0, cyc)])
    d.win(0, 1, [sig(1, 2, 4, 3, 5)], idle=0)                       # F0
    d.lemma(0, su, pi_of(1, 2, 4, 3, 5, 0))
    d.win(0, 1, [PG(SbA, [4])], idle=4)
    return Fact('sw₁₂', 'b-Sb2-0-41-3 ↑', 'stretch b-Sb0-1-42-3', d,
                [('up', 'b-Sb2-0-41-3')], [('as', 'stretch b-Sb0-1-42-3')])


def sw23(su):
    d = Deriv('sw₂₃-chain', [PG(SbA, cyc)])
    d.win(0, 1, [sig(2, 3, 4, 1, 5)], idle=0)                       # respelt, F0
    d.lemma(0, su, pi_of(2, 3, 4, 1, 5, 0))
    d.win(0, 1, [PG(SbB, [4])], idle=4)
    return Fact('sw₂₃', 'b-Sb0-1-42-3 ↑', 'stretch b-Sb0-2-43-1', d,
                [('up', 'b-Sb0-1-42-3')], [('as', 'stretch b-Sb0-2-43-1')])


def comm1(su, lit, name, gexpr):
    g = PG(lit, ST)
    assert g.f == [0, 5]
    d = Deriv(name + '-chain', [PG(SbB, cyc), g])
    d.win(0, 1, [sig(3, 4, 1, 2, 5)], idle=0)                       # respelt
    p = pi_of(3, 4, 1, 2, 5, 0)
    d.lemma(0, su, p)
    d.win(0, 2, [g, d.cur[0]], idle=1)
    d.lemma(1, su, p, backwards=True)
    d.win(1, 1, [PG(SbB, cyc)], idle=0)
    return Fact(name, f'b-Sb0-2-43-1 ↑ • {gexpr}', f'{gexpr} • b-Sb0-2-43-1 ↑', d,
                [('up', 'b-Sb0-2-43-1'), ('as', gexpr)], [('as', gexpr), ('up', 'b-Sb0-2-43-1')])


def comm2(su, uplit, lit, name, gexpr):
    d = Deriv(name + '-chain', [PG(uplit, cyc), PG(Sig0, [4])])
    g = at(lit, [4, 5])
    d.win(0, 1, [g], idle=0)
    p = pi_of(0, 1, 2, 3, 5, 4)
    d.lemma(1, su, p)
    d.win(0, 2, [d.cur[1], g], idle=2)
    d.lemma(0, su, p, backwards=True)
    d.win(1, 1, [PG(uplit, cyc)], idle=0)
    return Fact(name, f'{gexpr} ↑ • stretch b-Sb2-0-41-3', f'stretch b-Sb2-0-41-3 • {gexpr} ↑', d,
                [('up', gexpr), ('as', 'stretch b-Sb2-0-41-3')],
                [('as', 'stretch b-Sb2-0-41-3'), ('up', gexpr)])


def comm3(su):
    d = Deriv('comm₂₂-chain', [PG(SbB, cyc), PG(Sig0, [4])])
    # A = Σ(3; 5, 4 | 1, 2) to Σ(3; 5, 4 | 1, 0)
    d.win(0, 1, [sig(3, 4, 1, 2, 5)], idle=0)                       # respelt
    pa = pi_of(3, 4, 1, 2, 5, 0)
    d.lemma(0, su, pa)                                              # u: 1 -> 0
    d.win(0, 1, [sig(3, 4, 2, 0, 5)], idle=1)                       # F0
    pb = pi_of(3, 4, 2, 0, 5, 1)
    d.lemma(0, su, pb)                                              # u: 2 -> 1
    # B = Σ(0; 5, 1 | 2, 3) to Σ(0; 5, 1 | 4, 3)
    pc = pi_of(0, 1, 2, 3, 5, 4)
    d.lemma(1, su, pc)
    d.win(0, 2, [d.cur[1], d.cur[0]], idle=2)
    d.lemma(0, su, pc, backwards=True)
    d.lemma(1, su, pb, backwards=True)
    d.win(1, 1, [sig(3, 4, 0, 2, 5)], idle=1)                       # F0
    d.lemma(1, su, pa, backwards=True)
    d.win(1, 1, [PG(SbB, cyc)], idle=0)
    return Fact('comm₂₂', 'b-Sb0-2-43-1 ↑ • stretch b-Sb2-0-41-3', 'stretch b-Sb2-0-41-3 • b-Sb0-2-43-1 ↑', d,
                [('up', 'b-Sb0-2-43-1'), ('as', 'stretch b-Sb2-0-41-3')],
                [('as', 'stretch b-Sb2-0-41-3'), ('up', 'b-Sb0-2-43-1')])


class Raw:
    def __init__(self, text): self.text = text
    def agda(self): return self.text


def group(modname, title, doc, facts, imp):
    """the facts in modname: their S-box windows are decided on the
    four-wire domain (Engine.winC), so one module holds them."""
    module(modname, title, doc, facts, imports=imp, script='six_facts.py')
    return [modname]


if __name__ == '__main__':
    _, su = six_su.build()
    imp = ['open import Examples.Groups.Clifford+CS.Lambda using (stretch ; CSᵗ ; CKᵗ)',
           'open import Examples.Groups.Clifford+CS.MultiControlled using (CK₁₀)',
           'open import Examples.Groups.Clifford+CS.Stable.Rules using (embed)',
           'open import Examples.Groups.Clifford+CS.Stable.Six.Su c₅ using (su)']
    f12, f23 = sw12(su), sw23(su); f12.tag, f23.tag = 'A', 'B'
    c1s, c1k = comm1(su, CSl, 'comm₁-S', 'CSᵗ 4'), comm1(su, CK10, 'comm₁-K', 'CKᵗ 4'); c1s.tag, c1k.tag = 'S', 'K'
    c2s = comm2(su, CSup, CSl, 'comm₂-S', '(CS ↑ ↑ ↑)'); c2k = comm2(su, CKup, CK10, 'comm₂-K', '(CK₁₀ ↑ ↑ ↑)')
    c2s.tag, c2k.tag = 'S', 'K'
    c3 = comm3(su); c3.tag = 'P'
    mods = []
    mods += group('Switch', 'The two borrowed-wire switches on six wires',
           """Stable.Coherence.Switch₆: Σ(1; 5, 2 | 3, 4) = Σ(1; 5, 2 | 0, 3) and
Σ(2; 5, 3 | 1, 4) = Σ(2; 5, 3 | 0, 1).  Each is the S-box with the roles
of its box wire and its borrowed wire exchanged (a window, wire 0
idle), its box wire moved to wire 0 (Stable.Six.Su, transported), and
respelt (a window, wire 4 idle).""", [f12, f23], imp)
    mods += group('Comm1', 'The CS on the top two wires of a five-wire domain against S or K on wire 0',
           """Under the control, Σ(3; 5, 4 | 1, 2) against CS(0, 5) or CK(5 → 0): the
S-box's box wire moves to wire 0 (Stable.Six.Su), where the two gates
leave wire 1 idle and commute by a window, and back.""", [c1s, c1k], imp)
    mods += group('Comm2', 'S or K on the top wire of a five-wire domain against the CS on the wires 0 1',
           """Under the control, CS(4, 5) or CK(5 → 4) against Σ(0; 5, 1 | 2, 3): the
S-box's box wire moves to wire 4 (Stable.Six.Su), where the two gates
leave wire 2 idle and commute by a window, and back.""", [c2s, c2k], imp)
    mods += group('Comm3', 'The CS on the top two wires of a five-wire domain against the CS on the wires 0 1',
           """Under the control, Σ(3; 5, 4 | 1, 2) against Σ(0; 5, 1 | 2, 3): each
S-box moves to borrow wires the other uses — the first to Σ(3; 5, 4 |
1, 0), by its box wire, an F0 window and its box wire again, the second
to Σ(0; 5, 1 | 4, 3), by its box wire (Stable.Six.Su) — so that the two
leave wire 2 idle and commute by a window, and back.""", [c3], imp)
    print(' '.join(mods))
