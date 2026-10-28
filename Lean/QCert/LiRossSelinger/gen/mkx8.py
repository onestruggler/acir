"""Append eight_lev_e / eight_lev_h to CaseX8.lean."""
import os
HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.join(HERE, '..')
import re
IDX = list('abcdefgh')
def ne(x, y):
    """proof of x ≠ y for indices x, y in a..h"""
    return f"(ne' (by omega))" if IDX.index(x) < IDX.index(y) else f"(ne (by omega))"

def gen(tag, Z, haz, par, sumv):
    others = [x for x in 'efgh' if x != Z]
    # u5 values on b,c,d and e..h
    def w5(x):
        if x == Z:
            return 'w5z'
        return f"w5 {x} {ne(x, 'a')} {ne(x, Z)}"
    def w6(x):  # x in e..h
        return f"w6 {x} (by simp)"
    abcd_rw = f"w5a, {w5('b')}, {w5('c')}, {w5('d')}"
    efgh_rw = f"{w6('e')}, {w6('f')}, {w6('g')}, {w6('h')}, {w5('e')}, {w5('f')}, {w5('g')}, {w5('h')}"
    o7r = lambda x: f"o7 {x} {ne(x, 'e')} {ne(x, 'f')} {ne(x, 'g')} {ne(x, 'h')}"
    # j = 0 hsub branches
    br0 = []
    for x in 'abcd':
        br0.append(f"""        by_cases r{x} : r = {x}
        · rw [r{x}, {o7r(x)}, y6{x}, {abcd_rw}] at ho; exfalso; omega""")
    for x in 'efgh':
        br0.append(f"""        by_cases r{x} : r = {x}
        · rw [r{x}, y7{x}, {efgh_rw}] at ho; exfalso; omega""")
    rz = 'r' + Z
    br0.append(f"""        rw [o7 r re rf rg rh, o6 r ra rb rc rd, w5 r ra {rz},
          o2 r ra rb rc rd re rf rg rh] at hr
        exact hr""")
    br1 = []
    for x in 'abcd':
        br1.append(f"""        by_cases r{x} : r = {x}
        · rw [r{x}, y6{x}, {abcd_rw}] at ho; exfalso; omega""")
    br1.append(f"""        rw [o6 r ra rb rc rd] at ho hr
        by_cases {rz} : r = {Z}
        · rw [{rz}, w5z] at ho; exfalso; omega
        rw [w5 r ra {rz}] at ho hr""")
    for x in others:
        br1.append(f"""        by_cases r{x} : r = {x}
        · rw [r{x}] at ho; exfalso; omega""")
    br1.append(f"""        rwa [o2 r ra rb rc rd re rf rg rh] at hr""")
    t = f'''
/-- The states along `T = K_[e,f,g,h] K_[a,b,c,d] (−1)_[a] (−1)_[{Z}] X_[a,{Z}]` after
the two syllables lie below the level (sum `≡ {sumv} (mod 8)`). -/
theorem eight_lev_{tag} {{σ : O_ZHalf n}} (hσ : σ ≠ 1) (hk : 0 < lde σ) {{a b c d e f g h : Fin n}}
    (h1 : a < b) (h2 : b < c) (h3 : c < d) (h4 : d < e) (h5 : e < f) (h6 : f < g) (h7 : g < h)
    (ha : a ∈ oddS σ) (hb : b ∈ oddS σ) (hc : c ∈ oddS σ) (hd : d ∈ oddS σ)
    (he : e ∈ oddS σ) (hf : f ∈ oddS σ) (hg : g ∈ oddS σ) (hh : h ∈ oddS σ)
    (hrest : ∀ r ∈ oddS σ, r = a ∨ r = b ∨ r = c ∨ r = d ∨ r = e ∨ r = f ∨ r = g ∨ r = h ∨
      h < r)
    (hsum : (fix4 (wint σ a) + fix4 (wint σ b) + fix4 (wint σ c) + fix4 (wint σ d) +
      fix4 (wint σ e) + fix4 (wint σ f) + fix4 (wint σ g) + fix4 (wint σ h)) % 8 = {sumv}) :
    ∀ j ≤ 5, level (FreeMonoid.lift (sem n) (FreeMonoid.ofList
      ([Gen.k e f g h h5 h6 h7, Gen.k a b c d h1 h2 h3, Gen.neg a, Gen.neg {Z},
        Gen.x a {Z} {haz}].drop j)) * next (next σ)) < level σ := by
  have v1 := Fin.lt_def.1 h1; have v2 := Fin.lt_def.1 h2; have v3 := Fin.lt_def.1 h3
  have v4 := Fin.lt_def.1 h4; have v5 := Fin.lt_def.1 h5; have v6 := Fin.lt_def.1 h6
  have v7 := Fin.lt_def.1 h7
  have ne : ∀ {{x y : Fin n}}, x.val < y.val → y ≠ x := fun hxy e => by subst e; omega
  have ne' : ∀ {{x y : Fin n}}, x.val < y.val → x ≠ y := fun hxy e => by subst e; omega
  obtain ⟨hs1, hs2, hne1, u2, c2, va, vb, vc, vd, ve, vf, vg, vh, o2⟩ :=
    eight_syll hσ hk h1 h2 h3 h4 h5 h6 h7 ha hb hc hd he hf hg hh hrest
  have hF : ∀ x ∈ oddS σ, fix4 (wint σ x) % 4 = 1 := fun x hx => fix4_mod ((mem_oddS_iff x).1 hx)
  obtain ⟨ea, eb, ec, ed, ee, ef, eg, eh, k1, k1a, k1b, k1c, k1d, k2, k2e, k2f, k2g, k2h⟩ :=
    {par} _ _ _ _ _ _ _ _ (hF a ha) (hF b hb) (hF c hc) (hF d hd) (hF e he) (hF f hf)
      (hF g hg) (hF h hh) hsum _ _ _ _ _ _ _ _ va vb vc vd ve vf vg vh
  have hJ : h.val < pivotJ σ := le_pidx_of_odd hσ hh
  have hνF : FixCols (mat (next (next σ))) (pivotJ σ) := fixCols_iterN 2 σ (fixCols_pivotJ σ)
  have hνL : level (next (next σ)) < level σ :=
    lt_of_le_of_lt (level_next_le _) (level_next_lt σ hσ)
  obtain ⟨u3, c3, x3a, x3z, o3⟩ := step_x c2 {haz}
  obtain ⟨u4, c4, x4z, o4⟩ := step_neg c3 {Z}
  obtain ⟨u5, c5, x5a, o5⟩ := step_neg c4 a
  have w5a : u5 a = -u2 {Z} := by rw [x5a, o4 a (ne' (by omega)), x3a]
  have w5z : u5 {Z} = -u2 a := by rw [o5 {Z} (ne (by omega)), x4z, x3z]
  have w5 : ∀ r, r ≠ a → r ≠ {Z} → u5 r = u2 r := fun r ra rz => by
    rw [o5 r ra, o4 r rz, o3 r ra rz]
  have hstate : ∀ l : List (Gen n), FreeMonoid.lift (sem n) (FreeMonoid.ofList
      (l ++ (syll (next σ) ++ syll σ))) * σ =
      FreeMonoid.lift (sem n) (FreeMonoid.ofList l) * next (next σ) := by
    intro l
    simp only [FreeMonoid.ofList_append, map_mul, mul_assoc]
    rfl
  have hbelow : ∀ l : List (Gen n), (∀ x ∈ l, extent x ≤ h.val) →
      BelowJ (pivotJ σ) (l ++ (syll (next σ) ++ syll σ)) := by
    intro l hl x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact lt_of_le_of_lt (hl x hx) hJ
    rcases List.mem_append.1 hx with hx | hx
    · rw [hs2] at hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hJ
      · exact signs_extent (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl <;> omega) x hx
    · rw [hs1] at hx
      rcases List.mem_cons.1 hx with rfl | hx
      · show d.val < pivotJ σ; omega
      · exact signs_extent (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl <;> omega) x hx
  have hoa : Odd (wint σ a) := (mem_oddS_iff a).1 ha
  obtain ⟨u6, c6, y6a, y6b, y6c, y6d, o6⟩ := step_k c5 h1 h2 h3 (by
    rw [{abcd_rw}]; exact k1)
  have w6 : ∀ r, r = e ∨ r = f ∨ r = g ∨ r = h → u6 r = u5 r := fun r hr => by
    apply o6 <;> rcases hr with rfl | rfl | rfl | rfl <;> exact ne (by omega)
  intro j hj
  rcases (show j = 0 ∨ j = 1 ∨ 2 ≤ j by omega) with rfl | rfl | hj2
  · obtain ⟨u7, c7, y7e, y7f, y7g, y7h, o7⟩ := step_k c6 h5 h6 h7 (by
      rw [{efgh_rw}]
      exact k2)
    have hl := hbelow [Gen.k e f g h h5 h6 h7, Gen.k a b c d h1 h2 h3, Gen.neg a, Gen.neg {Z},
      Gen.x a {Z} {haz}] (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp [extent] <;> omega)
    have := level_lt_of_col hσ hk _ hl (u' := u7)
      (by rw [wact_append]; exact c7) (fun r hr => by
        have ho := Int.odd_iff.1 hr
{chr(10).join(br0)}) (r₀ := a) hoa (fun hr => by
          have ho := Int.odd_iff.1 hr
          rw [{o7r('a')}, y6a, {abcd_rw}] at ho; omega)
    rwa [hstate] at this
  · have hl := hbelow [Gen.k a b c d h1 h2 h3, Gen.neg a, Gen.neg {Z}, Gen.x a {Z} {haz}] (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> simp [extent] <;> omega)
    have := level_lt_of_col hσ hk _ hl (u' := u6)
      (by rw [wact_append]; exact c6) (fun r hr => by
        have ho := Int.odd_iff.1 hr
{chr(10).join(br1)}) (r₀ := a) hoa (fun hr => by
          have ho := Int.odd_iff.1 hr
          rw [y6a, {abcd_rw}] at ho; omega)
    rwa [hstate] at this
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
    have e2 : ([Gen.k e f g h h5 h6 h7, Gen.k a b c d h1 h2 h3, Gen.neg a, Gen.neg {Z},
        Gen.x a {Z} {haz}].drop (i + 2)) = [Gen.neg a, Gen.neg {Z}, Gen.x a {Z} {haz}].drop i := rfl
    rw [e2]
    refine (level_sp_word hσ hk _ (fun x hx => ?_) hνF hνL).2
    have hx' := List.mem_of_mem_drop hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
    rcases hx' with rfl | rfl | rfl <;> exact ⟨by simp [Gen.tag], by simp [extent]; omega⟩
'''
    return t
out = gen('e', 'e', '(h1.trans (h2.trans (h3.trans h4)))', 'par8_e', '4')
out += gen('h', 'h', '(h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7))))))', 'par8_h', '0')
p = os.path.join(LEAN, 'CaseX8.lean')
s = open(p, encoding='utf-8').read()
start = s.index('\n/-- The states along `T')
stop = s.index('\n/-! ## The derivation')
s = s[:start] + out + s[stop:]
open(p, 'w', encoding='utf-8', newline='\n').write(s)
