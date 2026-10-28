"""Generate CaseKMeet.lean: Subcases 3.2.2-3.2.5 dispatched."""
import os
HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.join(HERE, '..')
A = ['a₀', 'a₁', 'a₂', 'a₃']
H = ['h₁', 'h₂', 'h₃']
def lt(i, j):
    hs = [H[t] for t in range(i, j)]
    p = hs[-1]
    for h in reversed(hs[:-1]):
        p = f"({h}.trans {p})"
    return p
def ltc(i):
    if i == 3: return "h₄"
    return f"({lt(i, 3)}.trans h₄)"
OPT = {(0, 1): [(0, 2), (1, 3)], (0, 2): [(0, 1), (2, 3)], (0, 3): [(0, 3), (1, 2)],
       (1, 2): [(0, 3), (1, 2)], (1, 3): [(0, 1), (2, 3)], (2, 3): [(0, 2), (1, 3)]}
PAR = {(0, 1, 0, 2): 'false', (0, 1, 1, 3): 'true', (0, 2, 0, 1): 'false', (0, 2, 2, 3): 'true',
       (0, 3, 0, 3): 'false', (0, 3, 1, 2): 'true', (1, 2, 0, 3): 'true', (1, 2, 1, 2): 'false',
       (1, 3, 0, 1): 'true', (1, 3, 2, 3): 'false', (2, 3, 0, 2): 'true', (2, 3, 1, 3): 'false'}
def wexpr(t):
    return {0: "(w0 + w1 + w2 + w3) / 2", 1: "(w0 - w1 + w2 - w3) / 2",
            2: "(w0 + w1 - w2 - w3) / 2", 3: "(w0 - w1 - w2 + w3) / 2"}[t]
head = open(os.path.join(HERE, 'meet_head.lean'), encoding='utf-8').read()
out = [head, """theorem xor4_tau (z1 z2 z3 z4 : ℤ) (o1 : z1 % 2 = 1) (o2 : z2 % 2 = 1) (o3 : z3 % 2 = 1)
    (o4 : z4 % 2 = 1) :
    xor (xor (xor (tau z1) (tau z2)) (tau z3)) (tau z4) = decide ((z1 + z2 + z3 + z4) % 4 = 2) := by
  unfold tau
  by_cases h1 : z1 % 4 = 3 <;> by_cases h2 : z2 % 4 = 3 <;> by_cases h3 : z3 % 4 = 3 <;>
    by_cases h4 : z4 % 4 = 3 <;> simp [h1, h2, h3, h4] <;> omega

theorem ne_of_val {a b : Fin n} (h : a.val ≠ b.val) : a ≠ b := fun e => h (congrArg Fin.val e)
"""]
for (i, j), opts in sorted(OPT.items()):
    k, l = [t for t in range(4) if t not in (i, j)]
    def opt(al, be):
        no = [t for t in range(4) if t not in (al, be)]
        cst = 2 if PAR[(i, j, al, be)] == 'true' else 0
        return (f"({wexpr(al)} % 2 = 1 ∧ {wexpr(be)} % 2 = 1 ∧ {wexpr(no[0])} % 2 = 0 ∧ "
                f"{wexpr(no[1])} % 2 = 0 ∧\n      ({wexpr(al)} + {wexpr(be)} + w{i} + w{j}) % 4 = {cst})")
    (al1, be1), (al2, be2) = opts
    out.append(f"""/-- Lemma A.3 with `a, b = {i}, {j}`: the odd entries of `K s` and the parity of the signs. -/
theorem par_{i}{j} (w0 w1 w2 w3 : ℤ) (oi : w{i} % 2 = 1) (oj : w{j} % 2 = 1) (ek : w{k} % 2 = 0)
    (el : w{l} % 2 = 0) :
    {opt(al1, be1)} ∨
    {opt(al2, be2)} := by
  omega
""")
    def branch(al, be):
        cfg = f"{i}{j}{al}{be}"
        no = [t for t in range(4) if t not in (al, be)]
        return f"""  · rw [← hv{al}, ← hv{be}, ← hv{no[0]}, ← hv{no[1]}] at hp
    obtain ⟨pα, pβ, pk, pl, h4⟩ := hp
    have hpar := (xor4_tau _ _ _ _ pα pβ oi oj).trans (by rw [h4])
    exact finish323 hs hk h₁ h₂ h₃ h₄ h₅ hle (a := {A[i]}) (b := {A[j]}) (α := {A[al]})
      (β := {A[be]}) {lt(i, j)} {ltc(j)} {lt(al, be)} {ltc(be)} (Fin.le_def.2 (by omega))
      hc hd hsylls hcV (Int.odd_iff.2 pα) (Int.odd_iff.2 pβ) hout (fun r hr ho => by
        have ho' := Int.odd_iff.1 ho
        rcases low4 hr with rfl | rfl | rfl | rfl <;> first
          | (left; rfl) | (right; rfl)
          | (exfalso; rw [pk] at ho'; exact absurd ho' (by decide))
          | (exfalso; rw [pl] at ho'; exact absurd ho' (by decide))) hrest
      (rel323_{cfg} h₁ h₂ h₃ h₄ h₅ _ _ _ _ hpar)
"""
    nev = "(ne_of_val (by omega))"
    out.append(f"""/-- Subcase 3.2.3 with `a, b = {i}, {j}` (from `0`). -/
theorem two_{i}{j} {{s : O_ZHalf n}} (hs : s ≠ 1) {{a₀ a₁ a₂ a₃ c d : Fin n}} (h₁ : a₀ < a₁)
    (h₂ : a₁ < a₂) (h₃ : a₂ < a₃) (h₄ : a₃ < c) (h₅ : c < d)
    (hv : a₀.val = 0 ∧ a₁.val = 1 ∧ a₂.val = 2 ∧ a₃.val = 3)
    (hle : level (sem n (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃) * s) ≤ level s) (hk : 0 < lde s)
    (ha : {A[i]} ∈ oddS s) (hb : {A[j]} ∈ oddS s) (hc : c ∈ oddS s) (hd : d ∈ oddS s)
    (hrest : ∀ r ∈ oddS s, r = {A[i]} ∨ r = {A[j]} ∨ r = c ∨ r = d ∨ d < r) :
    ∃ (m : ℕ) (gs : List (Gen n)), PathBelow gs (next s) (level s) ∧
      Derivable (Table1 n) (FreeMonoid.ofList (npath m (sem n (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃) * s)) *
        FreeMonoid.of (Gen.k a₀ a₁ a₂ a₃ h₁ h₂ h₃))
        (FreeMonoid.ofList gs * FreeMonoid.ofList (syll s)) := by
  obtain ⟨e0, e1, e2, e3⟩ := hv
  have hU := pivot_pos hs
  have vc := Fin.lt_def.1 h₄; have vd := Fin.lt_def.1 h₅
  have oi := Int.odd_iff.1 ((mem_oddS_iff _).1 ha)
  have oj := Int.odd_iff.1 ((mem_oddS_iff _).1 hb)
  have ek : wint s {A[k]} % 2 = 0 := even_low hrest {nev} {nev} {nev} {nev}
    (Fin.le_def.2 (by omega))
  have el : wint s {A[l]} % 2 = 0 := even_low hrest {nev} {nev} {nev} {nev}
    (Fin.le_def.2 (by omega))
  have hsylls := syll_eq_pos s hU hk {lt(i, j)} {ltc(j)} h₅ ha hb hc hd hrest
  have hsum : 2 ∣ wint s a₀ + wint s a₁ + wint s a₂ + wint s a₃ := by omega
  obtain ⟨u', hcV, hv0, hv1, hv2, hv3, hout⟩ := kcol h₁ h₂ h₃ hsum
  have low4 : ∀ {{r : Fin n}}, r ≤ a₃ → r = a₀ ∨ r = a₁ ∨ r = a₂ ∨ r = a₃ := fun {{r}} hr => by
    have := Fin.le_def.1 hr
    simp only [Fin.ext_iff]; omega
  rcases par_{i}{j} _ _ _ _ oi oj ek el with hp | hp
{branch(al1, be1)}{branch(al2, be2)}""")
out.append(open(os.path.join(HERE, 'meet_tail.lean'), encoding='utf-8').read())
open(os.path.join(LEAN, 'CaseKMeet.lean'), 'w', encoding='utf-8', newline='\n').write("\n".join(out))
