"""Write Stable/Base{W}.agda: comm2-base2 at m = W - 6 from completeness on W - 1.

Stable.Base7 explains the method.  Here every move of a borrowed wire is
an adjacent swap with an idle neighbour, each a window on V = W - 1
wires with some idle wire w; the window's two V-wire placements Y, Y'
have Y' = top S . Y . top S literally (S the swap, on V - 1 wires), and
the semantics of Y, ctrl [[c]], comes from a chain of the same
conjugations at width V from a lambda-image (Stable.Windows6.win-sem).

    python3 genbase.py 8 9
"""
import sys
from nets import bubble, places

def lst(xs):
    return '(' + ' ∷ '.join(str(x) for x in xs) + ' ∷ [])' if xs else '[]'

def ups(n): return ' ↑' * n

def swaps_needed(f, n):
    return bubble(f, n)


class Gen:
    def __init__(self, W):
        self.W = W; self.V = W - 1; self.t = W - 1
        self.lines = []          # private definitions
        self.sem = {}            # (box, net tuple) -> lemma name
        self.semdefs = []
        self.scfacts = {}        # (j, c) -> names of the two small facts
        self.scdefs = []
        self.cnt = 0

    def name(self, p):
        self.cnt += 1
        return f'{p}{self.cnt}'

    # ------------------------------------------------------------ width V
    def V_base(self, box):
        V = self.V
        if box == 'Σ₀':
            return list(range(V - 2, 3, -1))          # Σᵗ (V-5)
        net = []
        for j in range(V - 5):
            net += list(range(0, V - 1 - j))
        return net

    def V_place(self, box):
        """the placement (base wire -> wire) of the base network at width V"""
        return places(self.V_base(box), self.V, 5)

    def small(self, j, c):
        """facts about S = Swap ↑ʲ on V - 1 wires: S S ~ ε and S c S ~ c"""
        key = (j, c)
        S = '(Swap' + ups(j) + ')'
        if key not in self.scfacts:
            nm = self.name('sm')
            self.scdefs.append(f'''
  {nm}ˢ : ⟦ {S} • {S} ⟧ ~ ⟦ ε {{X = Gen {self.V - 1}}} ⟧
  {nm}ˢ = same-sem ({S} • {S}) ε Eq.refl

  {nm}ᶜ : ⟦ {S} • ({c} • {S}) ⟧ ~ ⟦ {c} ⟧
  {nm}ᶜ = same-sem ({S} • ({c} • {S})) {c} Eq.refl''')
            self.scfacts[key] = nm
        return self.scfacts[key], S

    def semantics(self, box, net):
        """name of a lemma: ⟦ PV (nsV net) box ⟧ ~ ctrl ⟦ c ⟧"""
        key = (box, tuple(net))
        if key in self.sem:
            return self.sem[key]
        V = self.V
        c = 'CSa' if box == 'Σ₀' else 'CSb'
        base = self.V_base(box)
        nm = self.name('e')
        Y = f'PV (nsV {lst(net)}) {box}'
        if net == base:
            if box == 'Σ₀':
                body = (f'~-trans {{s = ⟦ {Y} ⟧}} {{t = ⟦ Σᵗ {V - 5} ⟧}} {{u = ctrl ⟦ CSa ⟧}}\n'
                        f'          (sound {{w = {Y}}} {{v = Σᵗ {V - 5}}} (by-assoc Eq.refl)) (ctrl-gen (gate₂ CS-gate))\n'
                        f'    where open Tools ({V} VRel,_===_)')
            else:
                body = (f'~-trans {{s = ⟦ {Y} ⟧}} {{t = ⟦ Σ₂{ups(V - 5)} ⟧}} {{u = ctrl ⟦ CSb ⟧}}\n'
                        f'          (sound {{w = {Y}}} {{v = Σ₂{ups(V - 5)}}} (sym (trans up{V - 5} (by-assoc Eq.refl))))\n'
                        f'          (ctrl-gen (gate₂ CS-gate{" ↥" * (V - 3)}))\n'
                        f'    where open Tools ({V} VRel,_===_)')
        else:
            j, prev = net[0], net[1:]
            pn = self.semantics(box, prev)
            sm, S = self.small(j, c)
            Yp = f'PV (nsV {lst(prev)}) {box}'
            body = (f'~-trans {{s = ⟦ {Y} ⟧}} {{t = ⟦ top {S} • ({Yp} • top {S}) ⟧}} {{u = ctrl ⟦ {c} ⟧}}\n'
                    f'          (sound {{w = {Y}}} {{v = top {S} • ({Yp} • top {S})}} (by-assoc Eq.refl))\n'
                    f'          (win-sem {S} {c} ({Yp}) {sm}ˢ {sm}ᶜ {pn})\n'
                    f'    where open Tools ({V} VRel,_===_)')
        self.semdefs.append(f'''
  {nm} : ⟦ {Y} ⟧ ~ ctrl ⟦ {c} ⟧
  {nm} = {body}''')
        self.sem[key] = nm
        return nm

    def V_net(self, box, g):
        """a network at width V placing box at g, reachable from the base by
        adjacent swaps prepended (each a conjugation by top S)"""
        V = self.V
        cur = self.V_place(box); net = self.V_base(box)
        # move entries of cur to g one adjacent swap at a time; the swap
        # (p, p+1) prepended moves whatever sits on p or p+1
        x, y, tt = (0, 1, 4) if box == 'Σ₀' else (2, 3, 4)
        assert cur[x] == g[x] and cur[y] == g[y] and cur[tt] == g[tt], (cur, g)
        for idx in (2, 3) if box == 'Σ₀' else (0, 1):
            pass
        guard = 0
        while cur != g:
            guard += 1; assert guard < 100
            moved = False
            for i in range(5):
                if cur[i] == g[i]: continue
                d = 1 if g[i] > cur[i] else -1
                nxt = cur[i] + d
                if nxt in cur: continue
                p = min(cur[i], nxt)
                assert p + 1 <= V - 2
                net = [p] + net
                cur = places(net, V, 5)
                moved = True
                break
            assert moved, (cur, g)
        return net

    # ------------------------------------------------------------ width W
    def chain(self, box, f0, moves, final):
        """moves: list of (index, new wire); returns the Agda chain text"""
        W, V, t = self.W, self.V, self.t
        steps = []
        f = list(f0)
        start_net = None
        for (i, new) in moves:
            f2 = list(f); f2[i] = new
            used = set(f) | set(f2)
            w = min(x for x in range(W) if x not in used)
            others = [x for x in range(W) if x != w]
            tau = bubble(others, W)
            g = [others.index(x) for x in f]
            g2 = [others.index(x) for x in f2]
            rho = self.V_net(box, g)
            rho2 = self.V_net(box, g2)
            assert places(tau + rho, W, 5) == f and places(tau + rho2, W, 5) == f2
            e1 = self.semantics(box, rho)
            e2 = self.semantics(box, rho2)
            steps.append((tau, rho, rho2, e1, e2))
            f = f2
        assert f == final
        return steps


def emit(W):
    G = Gen(W)
    V, t = G.V, G.t
    P0 = [0, 1, 2, 3, t]
    Pmoves = [(3, a) for a in range(4, W - 1)] + [(2, u) for u in range(3, W - 2)]
    Pfin = [0, 1, W - 3, W - 2, t]
    Q0 = [W - 5, W - 4, W - 3, W - 2, t]
    Qmoves = [(0, u) for u in range(W - 6, -1, -1)] + [(1, a) for a in range(W - 5, 0, -1)]
    Qfin = [0, 1, W - 3, W - 2, t]
    Psteps = G.chain('Σ₀', P0, Pmoves, Pfin)
    Qsteps = G.chain('Σ₂', Q0, Qmoves, Qfin)
    N = bubble(Pfin, W)
    NP0 = list(range(W - 2, 3, -1))
    NQ = []
    for j in range(W - 5):
        NQ += list(range(0, W - 1 - j))
    assert places(NP0, W, 5) == P0 and places(NQ, W, 5) == Q0

    def frame(box, a, b):
        return (f'(frame {box} ({a}) ({b}) Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl)')

    def wchain(box, start_net, steps, start_expr, final_line):
        out = [f'    {start_expr}']
        out.append(f'      ≈⟨ {"by-assoc Eq.refl" if box == "Σ₀" else "embed Q-placed"} ⟩')
        cur = f'nsW {lst(start_net)}'
        out.append(f'    PW ({cur}) {box}')
        for (tau, rho, rho2, e1, e2) in steps:
            s_ = f'nsW {lst(tau)} • nsW {lst(rho)}'
            out.append(f'      ≈⟨ {frame(box, cur, s_)} ⟩')
            out.append(f'    PW ({s_}) {box}')
            s2 = f'nsW {lst(tau)} • nsW {lst(rho2)}'
            out.append(f'      ≈⟨ switch {box} ({s_}) (nsW {lst(tau)}) {lst(rho)} {lst(rho2)} ({s2})\n'
                       f'           PB.refl Eq.refl (same {{PV (nsV {lst(rho)}) {box}}} {{PV (nsV {lst(rho2)}) {box}}} {{{"CSa" if box == "Σ₀" else "CSb"}}} {e1} {e2}) Eq.refl PB.refl ⟩')
            out.append(f'    PW ({s2}) {box}')
            cur = s2
        out.append(f'      ≈⟨ {frame(box, cur, "N")} ⟩')
        out.append(f'    PW N {box} ∎')
        return '\n'.join(out)

    k = W - 5
    def nat(n): return 'zero' if n == 0 else f'suc ({nat(n - 1)})'
    sucm = nat(W - 6)
    lam = f'λ¹ {{suc ({sucm})}}'
    lam0 = f'λ⁰ {{suc ({sucm})}}'
    T4 = bubble([4], 5)
    assert places(N + T4, W, 1) == [W - 1]
    exprs = ['Σ₂']
    for j in range(1, k + 1):
        exprs.append(f'σ {4 + j} • top ({exprs[-1]}) • σ⁻¹ {4 + j}')
    ups_lemmas = ''
    for j in range(1, max(k, V - 5) + 1):
        if j == 1:
            body = '↑≈ Σ₂'
        else:
            body = f'trans (↑≈ (Σ₂{ups(j - 1)})) (back _ (front _ (top-cong up{j - 1})))'
        ups_lemmas += f'''
  up{j} : {5 + j} ⊢ Σ₂{ups(j)} ≈ {exprs[j] if j < len(exprs) else ''}
  up{j} = {body}
    where open Tools ({5 + j} VRel,_===_)
'''
    # semantics lemmas need up_{V-5}: make sure exprs is long enough
    while len(exprs) <= V - 5:
        j = len(exprs)
        exprs.append(f'σ {4 + j} • top ({exprs[-1]}) • σ⁻¹ {4 + j}')

    def swdefs(n):
        out = [f'sw{n} : ℕ → Word (S.Gen {n})']
        for p in range(n - 1):
            out.append(f'sw{n} {p} = [ S.gate₂ S.σ-gate' + ' S.↥' * p + ' ]ʷ')
        out.append(f'sw{n} _ = ε')
        out.append('')
        out.append(f'ns{n} : List ℕ → Word (S.Gen {n})')
        out.append(f'ns{n} []       = ε')
        out.append(f'ns{n} (p ∷ ps) = sw{n} p • ns{n} ps')
        return '\n'.join(out)

    # semantics first (they define e-names); force generation by chains above
    src = f'''------------------------------------------------------------------------
-- Presentations of groups
--
-- A {W}-wire equation of the transport from completeness on {V}
--
-- Generated by scratchpad/stable/genbase.py; Stable.Base7 explains the
-- method.  The controlled CS of the wires 0 1 and the four-wire domain's
-- CS on its top two wires, shifted to the wires {W - 3} {W - 2}, cover every
-- wire; each is moved, one borrowed wire at a time by an adjacent swap,
-- onto the wires 0 1 {W - 3} {W - 2} {t}, every move a window on {V} wires, and there
-- they commute by completeness on five.  Each window's equality of
-- semantics comes from conjugations by swaps the control does not see
-- (Stable.Windows6.win-sem), starting from a λ¹-image.
------------------------------------------------------------------------

{{-# OPTIONS --without-K --safe #-}}

open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Examples.Groups.Clifford+CS.Semantics using (_~_)
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_⊢ᵧ_≈_)

module Examples.Groups.Clifford+CS.Stable.Base{W}
  (c₅ : ∀ {{u v : Circuit 5}} → ⟦ u ⟧ ~ ⟦ v ⟧ → 5 ⊢ᵧ u ≈ v)
  (cV : ∀ {{u v : Circuit {V}}} → ⟦ u ⟧ ~ ⟦ v ⟧ → {V} ⊢ᵧ u ≈ v)
  where

open import Data.Fin using (Fin ; toℕ) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.List using (List ; [] ; _∷_)
open import Data.Nat using (ℕ ; zero ; suc ; _<_ ; s≤s)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

import Presentation.Base as PB
import Examples.Groups.Symmetric.Syntactics as S

open import Examples.Groups.Clifford+CS.Semantics.Control using (ctrl ; ctrl-~)
open import Examples.Groups.Clifford+CS.Semantics using (~-trans ; ~-sym)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧ᵍ)
open import Examples.Groups.Clifford+CS.Soundness using (sound)
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.MultiControlled using (top)
open import Examples.Groups.Clifford+CS.SemanticSteps using (same-sem)
open import Examples.Groups.Clifford+CS.TopWeakening using (σ ; σ⁻¹ ; σσ⁻¹ ; nat ; top-cong)
open import Examples.Groups.Clifford+CS.PermCalc using (net ; perm ; revS)
open import Examples.Groups.Clifford+CS.LocalPlace using (pl ; pl-• ; pl-pl ; place-eq)
open import Examples.Groups.Clifford+CS.Lambda using (Σᵗ ; λ¹ ; λ⁰ ; Xᵗ)
open import Examples.Groups.Clifford+CS.Lambda.Semantics using (λ¹-~ ; λ¹-gen ; ⟦gen⟧)
open import Examples.Groups.Clifford+CS.Stable.Rules
open import Examples.Groups.Clifford+CS.Stable.Soundness using (axiom-soundᵧ)
open import Examples.Groups.Clifford+CS.Stable.Weakening using (top-congᵧ)
open import Examples.Groups.Clifford+CS.Stable.Insert4 using (top2)
open import Examples.Groups.Clifford+CS.Stable.Nets7 using (Σ₀ ; Σ₂)
open import Examples.Groups.Clifford+CS.Stable.Windows6 using (win-sem)
open import Examples.Groups.Clifford+CS.Stable.CalcSem using (F4-sem)
open import Examples.Groups.Clifford+CS.Stable.XPlace using (Xᵗ-placed)

private
  variable
    n : ℕ

{swdefs(W).replace(f"sw{W}", "swW").replace(f"ns{W}", "nsW")}

{swdefs(V).replace(f"sw{V}", "swV").replace(f"ns{V}", "nsV")}

PW : Word (S.Gen {W}) → Circuit 5 → Circuit {W}
PW s u = pl s (u ↓ᵏ {W - 5})

PV : Word (S.Gen {V}) → Circuit 5 → Circuit {V}
PV s u = pl s (u ↓ᵏ {V - 5})

private
  refl≡ᵧ : ∀ {{n}} {{a b : Circuit n}} → a ≡ b → n ⊢ᵧ a ≈ b
  refl≡ᵧ Eq.refl = PB.refl

  frame : (u : Circuit 5) (s s′ : Word (S.Gen {W})) →
          perm s′ ⟨$⟩ʳ (perm (revS s) ⟨$⟩ʳ 0F) ≡ 0F →
          perm s′ ⟨$⟩ʳ (perm (revS s) ⟨$⟩ʳ sF 0F) ≡ sF 0F →
          perm s′ ⟨$⟩ʳ (perm (revS s) ⟨$⟩ʳ sF (sF 0F)) ≡ sF (sF 0F) →
          perm s′ ⟨$⟩ʳ (perm (revS s) ⟨$⟩ʳ sF (sF (sF 0F))) ≡ sF (sF (sF 0F)) →
          perm s′ ⟨$⟩ʳ (perm (revS s) ⟨$⟩ʳ sF (sF (sF (sF 0F)))) ≡ sF (sF (sF (sF 0F))) →
          {W} ⊢ᵧ PW s u ≈ PW s′ u
  frame u s s′ e0 e1 e2 e3 e4 = embed (place-eq u s s′ agree)
    where
    agree : ∀ (j : Fin {W}) → toℕ j < 5 → perm s′ ⟨$⟩ʳ (perm (revS s) ⟨$⟩ʳ j) ≡ j
    agree 0F                          _ = e0
    agree (sF 0F)                     _ = e1
    agree (sF (sF 0F))                _ = e2
    agree (sF (sF (sF 0F)))           _ = e3
    agree (sF (sF (sF (sF 0F))))      _ = e4
    agree (sF (sF (sF (sF (sF j))))) (s≤s (s≤s (s≤s (s≤s (s≤s ())))))

  win : (t : Word (S.Gen {W})) (Y Y′ : Circuit {V}) → ⟦ Y ⟧ ~ ⟦ Y′ ⟧ →
        {W} ⊢ᵧ pl t (top Y) ≈ pl t (top Y′)
  win t Y Y′ e = PB.cong PB.refl (PB.cong (top-congᵧ (cV {{Y}} {{Y′}} e)) PB.refl)

  switch : (u : Circuit 5) (s t : Word (S.Gen {W})) (ρ ρ′ : List ℕ) (s′ : Word (S.Gen {W})) →
           {W} ⊢ᵧ PW s u ≈ PW (t • nsW ρ) u →
           pl (nsW ρ) (u ↓ᵏ {W - 5}) ≡ top (PV (nsV ρ) u) →
           ⟦ PV (nsV ρ) u ⟧ ~ ⟦ PV (nsV ρ′) u ⟧ →
           pl (nsW ρ′) (u ↓ᵏ {W - 5}) ≡ top (PV (nsV ρ′) u) →
           {W} ⊢ᵧ PW (t • nsW ρ′) u ≈ PW s′ u →
           {W} ⊢ᵧ PW s u ≈ PW s′ u
  switch u s t ρ ρ′ s′ f₁ n₁ e n₂ f₂ = begin
    PW s u                              ≈⟨ f₁ ⟩
    PW (t • nsW ρ) u                    ≈⟨ sym (embed (pl-pl t (nsW ρ) (u ↓ᵏ {W - 5}))) ⟩
    pl t (pl (nsW ρ) (u ↓ᵏ {W - 5}))        ≈⟨ refl≡ᵧ (Eq.cong (pl t) n₁) ⟩
    pl t (top (PV (nsV ρ) u))           ≈⟨ win t (PV (nsV ρ) u) (PV (nsV ρ′) u) e ⟩
    pl t (top (PV (nsV ρ′) u))          ≈⟨ refl≡ᵧ (Eq.cong (pl t) (Eq.sym n₂)) ⟩
    pl t (pl (nsW ρ′) (u ↓ᵏ {W - 5}))       ≈⟨ embed (pl-pl t (nsW ρ′) (u ↓ᵏ {W - 5})) ⟩
    PW (t • nsW ρ′) u                   ≈⟨ f₂ ⟩
    PW s′ u ∎
    where open Tools ({W} YVRel,_===_)

  same : {{Y Y′ : Circuit {V}}} {{c : Circuit {V - 1}}} → ⟦ Y ⟧ ~ ctrl ⟦ c ⟧ → ⟦ Y′ ⟧ ~ ctrl ⟦ c ⟧ → ⟦ Y ⟧ ~ ⟦ Y′ ⟧
  same {{Y}} {{Y′}} {{c}} e e′ = ~-trans {{s = ⟦ Y ⟧}} {{t = ctrl ⟦ c ⟧}} {{u = ⟦ Y′ ⟧}} e (~-sym {{s = ⟦ Y′ ⟧}} {{t = ctrl ⟦ c ⟧}} e′)

  -- The controlled CS of the wires 0 1, and of the top two wires of the domain.
  CSa CSb : Circuit {V - 1}
  CSa = [ gate₂ CS-gate ]ʷ
  CSb = [ gate₂ CS-gate{" ↥" * (V - 3)} ]ʷ

  ctrl-gen : (g : Gen {V - 1}) → ⟦ λ¹ {{{V - 5}}} g ⟧ ~ ctrl ⟦ [ g ]ʷ ⟧
  ctrl-gen g = ~-trans {{s = ⟦ λ¹ {{{V - 5}}} g ⟧}} {{t = ctrl (1 , ⟦ g ⟧ᵍ)}} {{u = ctrl ⟦ [ g ]ʷ ⟧}}
                 (λ¹-gen g) (ctrl-~ {{s = 1 , ⟦ g ⟧ᵍ}} {{t = ⟦ [ g ]ʷ ⟧}} (~-sym {{s = ⟦ [ g ]ʷ ⟧}} {{t = 1 , ⟦ g ⟧ᵍ}} (⟦gen⟧ g)))

  ↑≈ : (w : Circuit n) → (₁₊ n) ⊢ w ↑ ≈ σ n • top w • σ⁻¹ n
  ↑≈ {{n}} w = begin
    w ↑                         ≈⟨ sym right-unit ⟩
    w ↑ • ε                     ≈⟨ back _ (sym (σσ⁻¹ n)) ⟩
    w ↑ • σ n • σ⁻¹ n           ≈⟨ sym assoc ⟩
    (w ↑ • σ n) • σ⁻¹ n         ≈⟨ front _ (nat w) ⟩
    (σ n • top w) • σ⁻¹ n       ≈⟨ assoc ⟩
    σ n • top w • σ⁻¹ n ∎
    where open Tools ((₁₊ n) VRel,_===_)
'''
    for j in range(1, max(k, V - 5) + 1):
        if j == 1:
            body = '↑≈ Σ₂'
        else:
            body = f'PB.trans (↑≈ (Σ₂{ups(j - 1)})) (PB.cong PB.refl (PB.cong (top-cong up{j - 1}) PB.refl))'
        src += f'''
  up{j} : {5 + j} ⊢ Σ₂{ups(j)} ≈ {exprs[j]}
  up{j} = {body}
'''
    src += ''.join(G.scdefs) + '\n' + ''.join(G.semdefs) + '\n'
    src += f'''
  N : Word (S.Gen {W})
  N = nsW {lst(N)}

  P-moved : {W} ⊢ᵧ Σᵗ {k} ≈ PW N Σ₀
  P-moved = begin
{wchain('Σ₀', NP0, Psteps, f'Σᵗ {k}', None)}
    where open Tools ({W} YVRel,_===_)

  Q-placed : {W} ⊢ Σ₂{ups(k)} ≈ PW (nsW {lst(NQ)}) Σ₂
  Q-placed = PB.trans up{k} (by-assoc Eq.refl)
    where open Tools ({W} VRel,_===_)

  Q-moved : {W} ⊢ᵧ Σ₂{ups(k)} ≈ PW N Σ₂
  Q-moved = begin
{wchain('Σ₂', NQ, Qsteps, f'Σ₂{ups(k)}', None)}
    where open Tools ({W} YVRel,_===_)

  comm₅ : 5 ⊢ᵧ Σ₂ • Σ₀ ≈ Σ₀ • Σ₂
  comm₅ = c₅ {{Σ₂ • Σ₀}} {{Σ₀ • Σ₂}}
            (λ¹-~ {{0}} {{[ gate₂ CS-gate ↥ ↥ ]ʷ • [ gate₂ CS-gate ]ʷ}} {{[ gate₂ CS-gate ]ʷ • [ gate₂ CS-gate ↥ ↥ ]ʷ}}
              (axiom-soundᵧ (comm₂ᵧ CS-gate (gate₂ CS-gate))))

  moved-comm : {W} ⊢ᵧ PW N Σ₂ • PW N Σ₀ ≈ PW N Σ₀ • PW N Σ₂
  moved-comm = begin
    PW N Σ₂ • PW N Σ₀            ≈⟨ sym (embed (pl-• N (Σ₂ ↓ᵏ {k}) (Σ₀ ↓ᵏ {k}))) ⟩
    pl N ((Σ₂ • Σ₀) ↓ᵏ {k})      ≈⟨ cong refl (cong ({'(top-congᵧ ' * k}comm₅{')' * k}) refl) ⟩
    pl N ((Σ₀ • Σ₂) ↓ᵏ {k})      ≈⟨ embed (pl-• N (Σ₀ ↓ᵏ {k}) (Σ₂ ↓ᵏ {k})) ⟩
    PW N Σ₀ • PW N Σ₂ ∎
    where open Tools ({W} YVRel,_===_)

comm₂-base₂-{W} : (₂₊ (₄₊ ({sucm}))) ⊢ᵧ {lam} (top2 (₃₊ ({sucm})) CS-gate) • {lam} (gate₂ CS-gate)
                                   ≈ {lam} (gate₂ CS-gate) • {lam} (top2 (₃₊ ({sucm})) CS-gate)
comm₂-base₂-{W} = begin
  Σ₂{ups(k)} • Σᵗ {k}        ≈⟨ cong Q-moved P-moved ⟩
  PW N Σ₂ • PW N Σ₀          ≈⟨ moved-comm ⟩
  PW N Σ₀ • PW N Σ₂          ≈⟨ sym (cong P-moved Q-moved) ⟩
  Σᵗ {k} • Σ₂{ups(k)} ∎
  where open Tools ({W} YVRel,_===_)

------------------------------------------------------------------------
-- The same with the first letter white (Stable.Mixed.MixBase): X on the
-- control is X on the moved S-box's control (Stable.XPlace), and on five
-- wires the white and the black S-box commute by (F4) there.

private
{chr(10).join('  ' + l if l else l for l in swdefs(5).split(chr(10)))}

  comm⁰₅ : 5 ⊢ᵧ (Xᵗ 4 • Σ₂ • Xᵗ 4) • Σ₀ ≈ Σ₀ • (Xᵗ 4 • Σ₂ • Xᵗ 4)
  comm⁰₅ = c₅ {{(Xᵗ 4 • Σ₂ • Xᵗ 4) • Σ₀}} {{Σ₀ • (Xᵗ 4 • Σ₂ • Xᵗ 4)}}
             (F4-sem {{0}} (gate₂ CS-gate ↥ ↥) (gate₂ CS-gate))

  X-moved : {W} ⊢ Xᵗ {W - 1} ≈ PW N (Xᵗ 4)
  X-moved = begin
    Xᵗ {W - 1}                                       ≈⟨ Xᵗ-placed {W - 1} (N • nsW {lst(T4)}) Eq.refl ⟩
    pl (N • nsW {lst(T4)}) (X {{0}} ↓ᵏ {W - 1})          ≈⟨ sym (pl-pl N (nsW {lst(T4)}) (X {{0}} ↓ᵏ {W - 1})) ⟩
    pl N (pl (nsW {lst(T4)}) (X {{0}} ↓ᵏ {W - 1}))       ≈⟨ sym (cong refl (cong ({'top-cong (' * k}Xᵗ-placed 4 (ns5 {lst(T4)}) Eq.refl{')' * k}) refl)) ⟩
    PW N (Xᵗ 4) ∎
    where open Tools ({W} VRel,_===_)

  moved-comm⁰ : {W} ⊢ᵧ (PW N (Xᵗ 4) • PW N Σ₂ • PW N (Xᵗ 4)) • PW N Σ₀
                    ≈ PW N Σ₀ • (PW N (Xᵗ 4) • PW N Σ₂ • PW N (Xᵗ 4))
  moved-comm⁰ = begin
    (PW N x • PW N Σ₂ • PW N x) • PW N Σ₀
      ≈⟨ cong (trans (back _ (sym (embed (pl-• N (Σ₂ ↓ᵏ {k}) (x ↓ᵏ {k})))))
                     (sym (embed (pl-• N (x ↓ᵏ {k}) ((Σ₂ • x) ↓ᵏ {k}))))) refl ⟩
    PW N (x • Σ₂ • x) • PW N Σ₀
      ≈⟨ sym (embed (pl-• N ((x • Σ₂ • x) ↓ᵏ {k}) (Σ₀ ↓ᵏ {k}))) ⟩
    pl N (((x • Σ₂ • x) • Σ₀) ↓ᵏ {k})
      ≈⟨ cong refl (cong ({'(top-congᵧ ' * k}comm⁰₅{')' * k}) refl) ⟩
    pl N ((Σ₀ • (x • Σ₂ • x)) ↓ᵏ {k})
      ≈⟨ embed (pl-• N (Σ₀ ↓ᵏ {k}) ((x • Σ₂ • x) ↓ᵏ {k})) ⟩
    PW N Σ₀ • PW N (x • Σ₂ • x)
      ≈⟨ cong refl (trans (embed (pl-• N (x ↓ᵏ {k}) ((Σ₂ • x) ↓ᵏ {k})))
                          (back _ (embed (pl-• N (Σ₂ ↓ᵏ {k}) (x ↓ᵏ {k}))))) ⟩
    PW N Σ₀ • (PW N x • PW N Σ₂ • PW N x) ∎
    where
    x = Xᵗ 4
    open Tools ({W} YVRel,_===_)

mix-base-{W} : (₂₊ (₄₊ ({sucm}))) ⊢ᵧ {lam0} (top2 (₃₊ ({sucm})) CS-gate) • {lam} (gate₂ CS-gate)
                                ≈ {lam} (gate₂ CS-gate) • {lam0} (top2 (₃₊ ({sucm})) CS-gate)
mix-base-{W} = begin
  (Xᵗ {W - 1} • Σ₂{ups(k)} • Xᵗ {W - 1}) • Σᵗ {k}       ≈⟨ cong (cong xm (cong Q-moved xm)) P-moved ⟩
  (PW N (Xᵗ 4) • PW N Σ₂ • PW N (Xᵗ 4)) • PW N Σ₀       ≈⟨ moved-comm⁰ ⟩
  PW N Σ₀ • (PW N (Xᵗ 4) • PW N Σ₂ • PW N (Xᵗ 4))       ≈⟨ sym (cong P-moved (cong xm (cong Q-moved xm))) ⟩
  Σᵗ {k} • (Xᵗ {W - 1} • Σ₂{ups(k)} • Xᵗ {W - 1}) ∎
  where
  xm = embed X-moved
  open Tools ({W} YVRel,_===_)
'''
    return src


if __name__ == '__main__':
    for W in map(int, sys.argv[1:]):
        import os; out = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'Stable', f'Base{W}.agda')
        src = emit(W)
        open(out, 'w', encoding='utf-8').write(src)
        print('wrote', out, len(src.splitlines()), 'lines')
