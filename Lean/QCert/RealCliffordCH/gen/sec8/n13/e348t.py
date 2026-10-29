"""(348) on three wires: the engine runs of `Sec8/D/N13/E348t.lean`.

The open instance: `hg[0,1](2:○)` (the `H` gate `A = X₂ CH(2→1) X₂`, idle box
wire 0) against `ZX[0](1:c₁, 2:●)` (`R = K0 · CZ₂₀ · K0 · CZ₂₀`, with `X₁`
around it when `c₁` is white).  The argument is (17) conjugated by `X₂`:

* `L17x`: `CZ₂₀` passes `K0 A K0` -- (17) says `CZ(2○,0)` passes `K0 K1 K0`;
  conjugate by `X₂` (which passes `K0`);
* `L132s`: `CZ₂₀` passes `A` -- (132) under the swap of the wires 0, 1;
* `LX1`: `X₁` passes `CZ₂₀` (through the swap, two-wire windows);
* `LKw`: `K0w A K0w = K0 A K0`, with `K0w = X₁ K0 X₁ = K0 H0` (Lemma 5.1 on the
  wires 0, 1) and `H0` passing `A` (disjoint) and `K0`.

Then, for `c₁` black, `A R = K0 (K0 A K0) CZ₂₀ K0 CZ₂₀ = K0 CZ₂₀ (K0 A K0) K0
CZ₂₀ = K0 CZ₂₀ K0 A CZ₂₀ = R A`, and for `c₁` white the same with `K0w` in
place of `K0` (moved there by `LX1`, and back by `LKw`).

Every step is checked by the model `eng3` of `Sec8/EngineN.lean` (each semantic
window numerically, on two wires) before the Lean is written, and (348) itself
is checked numerically in every colour: `python e348t.py [OUT.lean]` checks the
runs and writes `Sec8/D/N13/E348t.lean` (from this directory,
`python e348t.py ../../../Sec8/D/N13/E348t.lean`).
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))

import eng3  # noqa: E402
import letters as LT  # noqa: E402


def X(j):
    return [('H', j), ('Z', j), ('H', j)]


K0 = [('K', 0)]
K1 = [('K', 1)]
H0 = [('H', 0)]
S0 = [('S', 0)]
C1 = [('C', 1)]
CZ02 = S0 + C1 + S0
A = X(2) + K1 + X(2)
RB = K0 + CZ02 + K0 + CZ02
RW = X(1) + RB + X(1)
K0W = X(1) + K0 + X(1)

# the words agree with MC.lean's definitions (letters.mcw mirrors them)
assert A == LT.mcw(3, 'hg', [0, 1], lambda j: False if j == 2 else None)
assert RB == LT.mcw(3, 'zx', [0], lambda j: {1: True, 2: True}.get(j))
assert RW == LT.mcw(3, 'zx', [0], lambda j: {1: False, 2: True}.get(j))

T17 = (X(2) + CZ02 + X(2) + K0 + K1 + K0, K0 + K1 + K0 + X(2) + CZ02 + X(2))
T132 = (C1 + X(2) + S0 + K1 + S0 + X(2), X(2) + S0 + K1 + S0 + X(2) + C1)


class Run:
    """A run built step by step, each step applied (and so checked) at once."""

    def __init__(self, w, table):
        self.eng = eng3.Engine(2, [tuple(map(list, e)) for e in table])
        self.w = list(w)
        self.cur = list(w)
        self.steps = []

    def step(self, s):
        nxt = self.eng.apply_step(self.cur, s)
        assert nxt is not None, (s, self.cur)
        self.steps.append(s)
        self.cur = nxt

    def ins(self, i, r):
        self.step(('sem', i, 0, list(r)))

    def sem(self, i, n, r):
        self.step(('sem', i, n, list(r)))

    def cancel(self, i, n):
        self.step(('sem', i, n, []))

    def rw(self, i, k, d):
        self.step(('rw', i, k, d))

    def right(self, i, n, d):
        """Move the n letters at i right past the d letters after them."""
        for _ in range(d):
            for k in range(i + n - 1, i - 1, -1):
                self.step(('sw', k))
            i += 1

    def left(self, i, n, d):
        """Move the n letters at i left past the d letters before them."""
        for _ in range(d):
            for k in range(i - 1, i + n - 1):
                self.step(('sw', k))
            i -= 1

    def done(self, v):
        assert self.cur == list(v), (self.cur, v)
        # the whole run again, from the start
        out, bad = self.eng.run(self.w, self.steps)
        assert bad is None and out == list(v)
        return self.steps


def run_L17x():
    """`K0 A K0 · CZ₂₀ = CZ₂₀ · K0 A K0`, from (17)."""
    w = K0 + A + K0 + CZ02
    v = CZ02 + K0 + A + K0
    r = Run(w, [T17])
    r.left(1, 3, 1)            # X2 K0 K1 X2 K0 CZ02
    r.right(5, 3, 1)           # X2 K0 K1 K0 X2 CZ02
    r.ins(12, X(2) + X(2))     # X2 [K0 K1 K0 X2 CZ02 X2] X2
    r.rw(3, 0, True)           # X2 [X2 CZ02 X2 K0 K1 K0] X2
    r.cancel(0, 6)             # CZ02 X2 K0 K1 K0 X2
    r.right(3, 3, 1)           # CZ02 K0 X2 K1 K0 X2
    r.left(9, 3, 1)            # CZ02 K0 X2 K1 X2 K0
    return w, v, r.done(v)


def run_L132s():
    """`A · CZ₂₀ = CZ₂₀ · A`, from (132)."""
    w = A + CZ02
    v = CZ02 + A
    r = Run(w, [T132])
    r.ins(0, S0 + S0)          # S0 S0 X2 K1 X2 S0 C1 S0
    r.right(1, 1, 3)           # S0 X2 S0 K1 X2 S0 C1 S0
    r.ins(6, S0 + S0)          # S0 X2 S0 K1 S0 S0 X2 S0 C1 S0
    r.right(7, 1, 3)           # S0 X2 S0 K1 S0 X2 S0 S0 C1 S0
    r.cancel(10, 2)            # S0 X2 S0 K1 S0 X2 C1 S0
    r.rw(1, 0, True)           # S0 C1 X2 S0 K1 S0 X2 S0
    r.left(11, 1, 3)           # S0 C1 X2 S0 K1 S0 S0 X2
    r.cancel(7, 2)             # S0 C1 X2 S0 K1 X2
    r.left(5, 1, 3)            # S0 C1 S0 X2 K1 X2
    return w, v, r.done(v)


def run_LX1():
    """`X₁ · CZ₂₀ = CZ₂₀ · X₁`."""
    w = X(1) + CZ02
    v = CZ02 + X(1)
    r = Run(w, [])
    r.sem(0, 4, S0 + X(0))     # S0 X0 C1 S0
    r.right(1, 3, 1)           # S0 C1 X0 S0
    r.sem(2, 4, S0 + X(1))     # S0 C1 S0 X1
    return w, v, r.done(v)


def run_LKw():
    """`K0w A K0w = K0 A K0`."""
    w = K0W + A + K0W
    v = K0 + A + K0
    r = Run(w, [])
    r.sem(0, 3 + 1 + 3, K0 + H0)    # K0 H0 A K0w
    r.sem(9, 7, H0 + K0)            # K0 H0 A H0 K0
    r.right(1, 1, 7)                # K0 A H0 H0 K0
    r.cancel(8, 2)                  # K0 A K0
    return w, v, r.done(v)


def run_core(white):
    """`A R = R A` (table: L17x, L132s, LX1, LKw)."""
    if not white:
        w = A + RB
        v = RB + A
        r = Run(w, TABLE)
        r.ins(0, K0 + K0)          # K0 K0 A K0 CZ02 K0 CZ02
        r.rw(1, 0, False)          # K0 CZ02 K0 A K0 K0 CZ02
        r.cancel(12, 2)            # K0 CZ02 K0 A CZ02
        r.rw(5, 1, False)          # K0 CZ02 K0 CZ02 A
        return w, v, r.done(v)
    w = A + RW
    v = RW + A
    r = Run(w, TABLE)
    # A X1 K0 CZ02 K0 CZ02 X1
    r.rw(15, 2, True)              # A X1 K0 CZ02 K0 X1 CZ02
    r.ins(11, X(1) + X(1))         # A X1 K0 X1 X1 CZ02 K0 X1 CZ02
    r.rw(14, 2, False)             # A K0w CZ02 X1 K0 X1 CZ02  (A X1 K0 X1 CZ02 X1 K0 X1 CZ02)
    # A K0w CZ02 K0w CZ02, K0w at 7, 17
    r.ins(0, K0W + K0W)            # K0w K0w A K0w CZ02 K0w CZ02
    r.rw(7, 3, False)              # K0w [K0 A K0] CZ02 K0w CZ02
    r.rw(7, 0, False)              # K0w CZ02 [K0 A K0] K0w CZ02
    r.rw(10, 3, True)              # K0w CZ02 [K0w A K0w] K0w CZ02
    r.cancel(24, 14)               # K0w CZ02 K0w A CZ02
    r.rw(17, 1, False)             # K0w CZ02 K0w CZ02 A
    # back to RW: X1 K0 X1 CZ02 X1 K0 X1 CZ02 A
    r.rw(4, 2, False)              # X1 K0 CZ02 X1 X1 K0 X1 CZ02 A
    r.cancel(7, 6)                 # X1 K0 CZ02 K0 X1 CZ02 A
    r.rw(8, 2, False)              # X1 K0 CZ02 K0 CZ02 X1 A
    return w, v, r.done(v)


L17x = run_L17x()
L132s = run_L132s()
LX1 = run_LX1()
LKw = run_LKw()
TABLE = [(L17x[0], L17x[1]), (L132s[0], L132s[1]), (LX1[0], LX1[1]), (LKw[0], LKw[1])]
CORE_B = run_core(False)
CORE_W = run_core(True)




def lean_run(name, doc, table, w, v, steps, wexpr=None, vexpr=None):
    tbl = ', '.join(f'({LT.lean(a)}, {LT.lean(b)})' for a, b, _ in table)
    we = wexpr or LT.lean(w)
    ve = vexpr or LT.lean(v)
    lines = [f'/-- {doc} -/', f'theorem {name} (ih : IH 3) :',
             f'    Derivable (theory 3) (circW 3 {we})',
             f'      (circW 3 {ve}) :=']
    if table:
        lines.append(f'  check_sound ih (T := [{tbl}])')
        lines.append('    (by')
        lines.append('    intro e he')
        lines.append('    simp only [List.mem_cons, List.not_mem_nil, or_false] at he')
        lines.append('    rcases he with ' + ' | '.join(['rfl'] * len(table)))
        for _, _, pf in table:
            lines.append(f'    · exact {pf}')
        lines[-1] += ')'
    else:
        lines.append('  check_sound ih (T := []) (by intro e he; simp at he)')
    lines.append(f'    (w := {we})')
    lines.append(f'    (v := {ve})')
    lines.append(f'    (ss := [{", ".join(eng3.lean_steps(steps))}])')
    lines.append('    (by decide +kernel)')
    return '\n'.join(lines)


HEADER = '''/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Equation (348) on three wires

The `H` gate `hg[0,1](2:x)` against the rotation `(-1)ᵃZX[0](1:c₁, 2:y)`,
`x ≠ y` on wire `2`.  The paper's argument (page 234) needs a wire to spare;
on three wires the instance comes from Figure 4's (17) directly.  With the
colours `x = ○`, `y = ●` (the others by (81) on wire `2`, the sign by (317)),
the `H` gate is `A = X₂ · CH(2→1) · X₂` (its box wire `0` idle) and the
rotation is `R = K0 · CZ₂₀ · K0 · CZ₂₀` (`K0 = CH(1→0)`, with `X₁` around it
when `c₁` is white).  Where wire `2` is `0`, `R` is `K0 K0`; the derivation
makes that visible:

* `t17x`: `CZ₂₀` passes `K0 A K0` -- (17), `CZ(2○,0)` passes
  `K0 · CH(2→1) · K0`, conjugated by `X₂`;
* `t132s`: `CZ₂₀` passes `A` -- (132) under the swap of the wires `0, 1`;
* so `A R = K0 (K0 A K0) CZ₂₀ K0 CZ₂₀ = K0 CZ₂₀ (K0 A K0) K0 CZ₂₀ =
  K0 CZ₂₀ K0 A CZ₂₀ = R A` (`core_b`);
* for `c₁` white, `X₁` passes `CZ₂₀` (`tx1`), so `R = K0w CZ₂₀ K0w CZ₂₀` with
  `K0w = X₁ K0 X₁`, and `K0w A K0w = K0 A K0` (`tkw`: `K0w = K0 · H0` by
  Lemma 5.1, and `H0` passes `A` and `K0`); then the same argument
  (`core_w`).

Generated by `gen/sec8/n13/e348t.py`, which checks every step with the model
`gen/sec8/eng3.py` of the engine (each semantic window numerically) and
(348) itself numerically in every colour.
-/
import QCert.RealCliffordCH.Sec8.D.N13.E352t

set_option Elab.async false

namespace QCert.RealCliffordCH.Sec8.D.N13.R347

open Circuit Net E Eng

namespace T348

/-- `hg[0,1](2:○)`: `X₂ · CH(2→1) · X₂`. -/
def wA : List L := WA

/-- `ZX[0](1:●, 2:●)`: `CH(1→0) · CZ₂₀ · CH(1→0) · CZ₂₀`. -/
def wRB : List L := WRB

/-- `ZX[0](1:○, 2:●)`: the same with `X₁` on both sides. -/
def wRW : List L := WRW
'''

FOOTER = '''
end T348

open T348 in
/-- (348) on three wires, the colours `○` on the `H` gate's control and `●`
on the rotation's. -/
theorem c348 (ih : IH 3) (c₁ : Bool) :
    D.Comm 3 (mc 3 .hg [0, 1] (colOn 2 3 fun _ => false))
      (mc 3 .zx [0] (ctlOr (ctlAt 1 c₁) (colOn 2 3 fun _ => true))) := by
  have eA : mc 3 .hg [0, 1] (colOn 2 3 fun _ => false) = circW 3 wA := by
    set_option maxRecDepth 100000 in rfl
  have key : ∀ wR : List L, Derivable (theory 3) (circW 3 (wA ++ wR)) (circW 3 (wR ++ wA)) →
      mc 3 .zx [0] (ctlOr (ctlAt 1 c₁) (colOn 2 3 fun _ => true)) = circW 3 wR →
      D.Comm 3 (mc 3 .hg [0, 1] (colOn 2 3 fun _ => false))
        (mc 3 .zx [0] (ctlOr (ctlAt 1 c₁) (colOn 2 3 fun _ => true))) := by
    intro wR h e
    unfold D.Comm
    rw [eA, e, N13.drawn_two, N13.drawn_two, ← circW_append, ← circW_append]
    exact h
  cases c₁
  · exact key wRW (core_w ih) (by set_option maxRecDepth 100000 in rfl)
  · exact key wRB (core_b ih) (by set_option maxRecDepth 100000 in rfl)

/-- (348) on three wires. -/
theorem comm348_3 (ih : IH 3) (h317 : H317 3) (x y : ℕ → Bool) (hxy : DiffOn 2 3 x y)
    (a c₁ : Bool) :
    D.Comm 3 (mc 3 .hg [0, 1] (colOn 2 3 x))
      (mc 3 (Kind.sgnZX a) [0] (ctlOr (ctlAt 1 c₁) (colOn 2 3 y))) := by
  obtain ⟨j, hj2, hj3, hxyj⟩ := hxy
  have h2 : x 2 ≠ y 2 := by
    have : j = 2 := by omega
    subst this; exact hxyj
  refine Derivable.symm (sign0 h317 c₁ y (Derivable.symm ?_) a)
  have base : ∀ x y : ℕ → Bool, x 2 = false → y 2 = true →
      D.Comm 3 (mc 3 .hg [0, 1] (colOn 2 3 x))
        (mc 3 .zx [0] (ctlOr (ctlAt 1 c₁) (colOn 2 3 y))) := by
    intro x y hx hy
    have ex : mc 3 .hg [0, 1] (colOn 2 3 x) = mc 3 .hg [0, 1] (colOn 2 3 fun _ => false) :=
      Net.mc_congr _ _ _ (fun i hi => by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> simp [colOn, hx])
    have ey : mc 3 .zx [0] (ctlOr (ctlAt 1 c₁) (colOn 2 3 y)) =
        mc 3 .zx [0] (ctlOr (ctlAt 1 c₁) (colOn 2 3 fun _ => true)) :=
      Net.mc_congr _ _ _ (fun i hi => by
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
          simp [ctlOr, ctlAt, colOn, hy])
    rw [ex, ey]; exact c348 ih c₁
  cases hx : x 2
  · have hy : y 2 = true := by cases hy : y 2 <;> simp_all
    exact base x y hx hy
  · -- `X` on wire `2` flips both colours there
    have hy : y 2 = false := by cases hy : y 2 <;> simp_all
    have flA : ∀ z : ℕ → Bool, Derivable (theory 3)
        (xAt 3 2 * mc 3 .hg [0, 1] (colOn 2 3 z) * xAt 3 2)
        (mc 3 .hg [0, 1] (colOn 2 3 (MergeAll.flip1 z 2))) := by
      intro z
      refine (x81 .hg [0, 1] _ 2 (z 2) (by omega) (by simp) (by simp [colOn])).trans
        (der_of_eq (Net.mc_congr _ _ _ (fun i hi => ?_)))
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
        simp [setCtl, colOn, MergeAll.flip1]
    have flB : ∀ z : ℕ → Bool, Derivable (theory 3)
        (xAt 3 2 * mc 3 .zx [0] (ctlOr (ctlAt 1 c₁) (colOn 2 3 z)) * xAt 3 2)
        (mc 3 .zx [0] (ctlOr (ctlAt 1 c₁) (colOn 2 3 (MergeAll.flip1 z 2)))) := by
      intro z
      refine (x81 .zx [0] _ 2 (z 2) (by omega) (by simp) (by simp [ctlOr, ctlAt, colOn])).trans
        (der_of_eq (Net.mc_congr _ _ _ (fun i hi => ?_)))
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
        simp [setCtl, ctlOr, ctlAt, colOn, MergeAll.flip1]
    have k := base (MergeAll.flip1 x 2) (MergeAll.flip1 y 2) (by simp [MergeAll.flip1, hx])
      (by simp [MergeAll.flip1, hy])
    have e2 : ∀ z : ℕ → Bool, MergeAll.flip1 (MergeAll.flip1 z 2) 2 = z := fun z => by
      funext i; simp only [MergeAll.flip1]; split_ifs <;> simp
    have k2 := comm_flip k (D.xAt_inv 3 2 (by omega)) (flA (MergeAll.flip1 x 2))
      (flB (MergeAll.flip1 y 2))
    rwa [e2, e2] at k2

end QCert.RealCliffordCH.Sec8.D.N13.R347
'''


def lean_module():
    tab = [(L17x[0], L17x[1], 't17x ih'), (L132s[0], L132s[1], 't132s ih'),
           (LX1[0], LX1[1], 'tx1 ih'), (LKw[0], LKw[1], 'tkw ih')]
    runs = [
        lean_run('t17x', '(17) conjugated by `X₂`: `CZ₂₀` passes `K0 A K0`.',
                 [(T17[0], T17[1], 't_e17')], *L17x),
        lean_run('t132s', '(132) under the swap of the wires `0, 1`: `CZ₂₀` passes `A`.',
                 [(T132[0], T132[1], 'd132 ih')], *L132s),
        lean_run('tx1', '`X₁` passes `CZ₂₀`.', [], *LX1),
        lean_run('tkw', '`K0w A K0w = K0 A K0`.', [], *LKw),
        lean_run('core_b', '`A` and the rotation, `c₁` black.', tab[:2], *CORE_B,
                 wexpr='(wA ++ wRB)', vexpr='(wRB ++ wA)'),
        lean_run('core_w', '`A` and the rotation, `c₁` white.', tab, *CORE_W,
                 wexpr='(wA ++ wRW)', vexpr='(wRW ++ wA)'),
    ]
    head = (HEADER.replace('WA\n', LT.lean(A) + '\n').replace('WRB\n', LT.lean(RB) + '\n')
            .replace('WRW\n', LT.lean(RW) + '\n'))
    return head + '\n' + '\n\n'.join(runs) + '\n' + FOOTER


if __name__ == '__main__':
    print(f'L17x {len(L17x[2])} steps, L132s {len(L132s[2])}, LX1 {len(LX1[2])}, '
          f'LKw {len(LKw[2])}, core-black {len(CORE_B[2])}, core-white {len(CORE_W[2])}')
    # the cores' two sides are equal operators (the statement is sound)
    for w, v, _ in (CORE_B, CORE_W):
        assert LT.eq(3, w, v)
    # and (348) itself, numerically, in every colour
    for xb in (False, True):
        for yb in (False, True):
            if xb == yb:
                continue
            for c1 in (False, True):
                for K in ('zx', 'xz'):
                    a = LT.mcw(3, 'hg', [0, 1], lambda j: xb if j == 2 else None)
                    b = LT.mcw(3, K, [0], lambda j: {1: c1, 2: yb}.get(j))
                    assert LT.eq(3, a + b, b + a)
    if len(sys.argv) > 1:
        with open(sys.argv[1], 'w', encoding='utf-8', newline='\n') as f:
            f.write(lean_module())
        print('wrote', sys.argv[1])
