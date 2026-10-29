/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Hypothesis (b): through Clément's relations

`QCert.Clement2019` presents the same group by Clément's relations (1)–(21),
on generators with indices in either order, and proves Figure 6 equivalent
to them syntactically: a Figure 6 derivation is a derivation from Clément's
relations of the included words (`fig6_to_rel`), and `tr`, which writes a
Clément word over `𝒢ₙ`, undoes the inclusion (`tr_ι`).  So the congruence of
Claim B contains Figure 6 as soon as its pullback `GC n` along `tr` contains
Clément's relations.

Here: (1)–(19) are in `GC n` (`relK_gc`), by Clément's own tables of Figure 6
derivations on at most four indices (`ToFig6.lean`), which hold in `GB n`
now that it contains (d3) (`gb_good`); hence `GC n` is invariant under every
permutation of the indices (`gc_perm`, after `Clement2019.rel_perm`, from
conjugation by `X[i,j]`).
-/
import QCert.RealCliffordCH.Sec8.A.ItemBd3
import QCert.Clement2019.ToFig6
import QCert.Clement2019.Equivalence

namespace QCert.RealCliffordCH.Sec8

open FreeMonoid
open QCert.Clement2019 (RL trL Good exists_sort trL_map tr tr_eq RelK wmapC)

variable {n : ℕ}

/-- A scheme of Clément's on at most five indices, good for Figure 6, holds in `GB` at every
instance. -/
theorem gb_good (hn : 3 ≤ n) {a : ℕ} (ha : a ≤ 5) {L R : List (RL a)} (hG : Good L R)
    (x : Fin a → Fin (2 ^ n)) (hx : Function.Injective x) :
    GB n (ofList (trL (L.map (RL.map x)))) (ofList (trL (R.map (RL.map x)))) := by
  obtain ⟨g, hg, p, hp, hxp⟩ := exists_sort x hx
  have e : RL.map x = RL.map g ∘ RL.map p := by
    funext r; rw [Function.comp_apply, Clement2019.RL.map_comp]; congr 1; funext i; exact hxp i
  have hl : ∀ l : List (RL a), trL (l.map (RL.map x)) =
      (trL (l.map (RL.map p))).map (HadamardPi.Gen.map g hg) := by
    intro l; rw [e, ← List.map_map, trL_map g hg]
  rw [hl, hl, ← HadamardPi.wmap_ofList, ← HadamardPi.wmap_ofList]
  have hle : conGen (HadamardPi.Fig6 (n := a)) ≤ (GB n).comap (HadamardPi.wmap g hg) (map_mul _) :=
    Con.conGen_le fun u v huv => pull_fig6 hn ha g hg (d3At_all hn g hg) huv
  exact hle (hG p hp)

theorem gb_scheme (hn : 3 ≤ n) {a : ℕ} (ha : a ≤ 5) {L R : List (RL a)} (hG : Good L R)
    (x : Fin a → Fin (2 ^ n)) (hx : Function.Injective x) {w v : Word (Clement2019.Gen (2 ^ n))}
    (hw : w.toList.map Clement2019.Gen.raw = L.map (RL.map x))
    (hv : v.toList.map Clement2019.Gen.raw = R.map (RL.map x)) : GB n (tr w) (tr v) := by
  rw [tr_eq, tr_eq, hw, hv]; exact gb_good hn ha hG x hx

variable (n) in
/-- The pullback of `GB n` to Clément's words. -/
def GC : Con (Word (Clement2019.Gen (2 ^ n))) := (GB n).comap tr (map_mul tr)

open QCert.Clement2019 in
/-- Clément's relations (1)–(19) are in `GC n`. -/
theorem relK_gc (hn : 3 ≤ n) {w v : Word (Clement2019.Gen (2 ^ n))} (h : RelK false w v) :
    GC n w v := by
  show GB n (tr w) (tr v)
  cases h with
  | r1 j => exact gb_scheme hn (by norm_num) good1 ![j] (by vec_inj) rfl rfl
  | @r2 j k h => exact gb_scheme hn (by norm_num) good2 ![j, k] (by vec_inj) rfl rfl
  | @r3 j k h => exact gb_scheme hn (by norm_num) good3 ![j, k] (by vec_inj) rfl rfl
  | @r4 j k h => exact gb_scheme hn (by norm_num) good4 ![j, k] (by vec_inj) rfl rfl
  | @r5 j k l h1 h2 h3 => exact gb_scheme hn (by norm_num) good5 ![j, k, l] (by vec_inj) rfl rfl
  | @r6 j k l h1 h2 h3 => exact gb_scheme hn (by norm_num) good6 ![j, k, l] (by vec_inj) rfl rfl
  | @r7 j k l t h1 h2 h3 h4 h5 h6 =>
    exact gb_scheme hn (by norm_num) good7 ![j, k, l, t] (by vec_inj) rfl rfl
  | @r8 j k l t h1 h2 h3 h4 h5 h6 =>
    exact gb_scheme hn (by norm_num) good8 ![j, k, l, t] (by vec_inj) rfl rfl
  | @r9 j k l t h1 h2 h3 h4 h5 h6 =>
    exact gb_scheme hn (by norm_num) good9 ![j, k, l, t] (by vec_inj) rfl rfl
  | @r10 j k h => exact gb_scheme hn (by norm_num) good10 ![j, k] (by vec_inj) rfl rfl
  | @r11 j k h => exact gb_scheme hn (by norm_num) good11 ![j, k] (by vec_inj) rfl rfl
  | @r12 j k l h1 h2 h3 => exact gb_scheme hn (by norm_num) good12 ![j, k, l] (by vec_inj) rfl rfl
  | @r13 j k l h1 h2 h3 => exact gb_scheme hn (by norm_num) good13 ![j, k, l] (by vec_inj) rfl rfl
  | @r14 j k l h1 h2 h3 => exact gb_scheme hn (by norm_num) good14 ![j, k, l] (by vec_inj) rfl rfl
  | @r15 j k l h1 h2 h3 => exact gb_scheme hn (by norm_num) good15 ![j, k, l] (by vec_inj) rfl rfl
  | @r16 j k h => exact gb_scheme hn (by norm_num) good16 ![j, k] (by vec_inj) rfl rfl
  | @r17 j k h => exact gb_scheme hn (by norm_num) good17 ![j, k] (by vec_inj) rfl rfl
  | @r18 j k h => exact gb_scheme hn (by norm_num) good18 ![j, k] (by vec_inj) rfl rfl
  | @r19 j k l t h1 h2 h3 h4 h5 =>
    by_cases hkl : k = l
    · subst hkl; exact (GB n).refl _
    · exact gb_scheme hn (by norm_num) good19 ![j, k, l, t] (by vec_inj) rfl rfl
  | r20 hb => cases hb
  | r21 hb => cases hb

theorem relK_gc' (hn : 3 ≤ n) {w v : Word (Clement2019.Gen (2 ^ n))}
    (h : Derivable (RelK false) w v) : GC n w v :=
  (Con.conGen_le fun _ _ hxy => relK_gc hn hxy) h

/-- `GC n` is invariant under every permutation of the indices. -/
theorem gc_perm (hn : 3 ≤ n) (σ : Equiv.Perm (Fin (2 ^ n))) {w v : Word (Clement2019.Gen (2 ^ n))}
    (h : GC n w v) : GC n (wmapC σ σ.injective w) (wmapC σ σ.injective v) := by
  have h3 : 3 ≤ 2 ^ n := by have := h8_of hn; omega
  revert w v
  refine Equiv.Perm.swap_induction_on (motive := fun σ => ∀ {w v : Word (Clement2019.Gen (2 ^ n))},
    GC n w v → GC n (wmapC σ σ.injective w) (wmapC σ σ.injective v)) σ ?_ ?_
  · intro w v h
    rw [Clement2019.wmapC_congr (Equiv.Perm.coe_one) _ Function.injective_id,
      Clement2019.wmapC_congr (Equiv.Perm.coe_one) _ Function.injective_id,
      Clement2019.wmapC_id, Clement2019.wmapC_id]
    exact h
  · intro f x y hxy ih w v h
    obtain ⟨o, hox, hoy⟩ := Clement2019.exists_third h3 x y
    have e : ∀ u : Word (Clement2019.Gen (2 ^ n)),
        wmapC (Equiv.swap x y * f) (Equiv.swap x y * f).injective u =
        wmapC (Equiv.swap x y) (Equiv.swap x y).injective (wmapC f f.injective u) := by
      intro u
      rw [Clement2019.wmapC_comp]
      exact Clement2019.wmapC_congr (Equiv.Perm.coe_mul _ _) _ _ u
    rw [e, e]
    have hc := fun u => relK_gc' hn (Clement2019.conj_word hxy hox hoy u)
    exact (GC n).trans ((GC n).symm (hc _))
      ((GC n).trans ((GC n).mul ((GC n).mul ((GC n).refl _) (ih h)) ((GC n).refl _)) (hc _))

/-- A relation of `GC n` at one injective placement holds at every injective placement. -/
theorem gc_place (hn : 3 ≤ n) {k : ℕ} {f : Fin k → Fin (2 ^ n)} (hf : Function.Injective f)
    {w v : Word (Clement2019.Gen k)} (h : GC n (wmapC f hf w) (wmapC f hf v))
    (f' : Fin k → Fin (2 ^ n)) (hf' : Function.Injective f') :
    GC n (wmapC f' hf' w) (wmapC f' hf' v) := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f f' hf hf'
  have := gc_perm hn σ h
  rw [Clement2019.wmapC_comp, Clement2019.wmapC_comp,
    Clement2019.wmapC_congr (show ⇑σ ∘ f = f' from funext hσ) _ hf',
    Clement2019.wmapC_congr (show ⇑σ ∘ f = f' from funext hσ) _ hf'] at this
  exact this

end QCert.RealCliffordCH.Sec8
