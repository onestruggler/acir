/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Greylyn: the Main Lemma for the basic edges `X_[α,α+1]`

Cases 3, 4 and 5 of the proof of Lemma 31: `X_[a,b]`, `b = a + 1` (indices
from `0`), for all `a` at once.  The thesis details `X_[1,2]` (Case 3) and
`X_[2,3]` (Case 4), saying that the other cases are "directly analogous"
and that Case 5 is "entirely analogous to Case 4"; here every configuration
gets its own argument.

* Pivot `p < b` (Subcases 3.5.1, 4.1): `r` has pivot `b`, column `e_a`, and
  the edge is retrograde.  (The thesis computes `level r = (j + 1, 0, 0)`;
  it is `(b + 1, 0, 0)` in its numbering, `(3, 0, 0)` for `X_[2,3]`, and
  its matrix for `r` exchanges rows 3, 4 instead of 2, 3.)
* `k > 0`, first two odd entries `α < β` of the numerator:
  - `{α, β} ∩ {a, b} = ∅` (Subcases 3.4, …): `G' = X_[a,b]`;
  - `α = a`, `β = b` (Subcase 3.1): the residues exchange; (18), (28)–(30);
  - `α = a < b < β` (Subcase 3.2), `α = b` (Subcase 3.3), `β = b`, `α < a`
    (Subcase 4.2's mirror), and `β = a` with `b` even (Subcase 4.2):
    `G' = X_[a,b]` by (14), (21), (22), (15);
  - `β = a` with `b` odd: Subcases 4.3, 4.4 (`square_X_hard`).
* `k = 0`, pivot column `ωᵐ e_c` (Subcases 3.5.2–3.7): `G' = X_[a,b]` by
  (12) and (6), except when `b = p`: for `c = a` the syllable of `s` is
  `X_[a,b]` (`m = 8`) or the normal edge out of `r` is `N` after `X_[a,b]`;
  for `c < a` the square closes with `G' = X_[c,a]`, by (12) and (13) — a
  configuration that `X_[1,2]` (Case 3) does not have.
-/
import QCert.Greylyn.MainHard

namespace QCert.Greylyn

open Matrix Complex ZOmega

noncomputable section

variable {n : ℕ}

local notation "⟪" w "⟫" => FreeMonoid.lift (sem _) w

theorem FirstTwo.below {w : Fin n → ZOmega} {x y : Fin n} (hf : FirstTwo w x y) :
    ∀ i, i < y → i ≠ x → ¬ IsOdd (w i) := by
  intro i hi hix
  rcases lt_trichotomy i x with h | h | h
  · exact hf.2.2.2.1 i h
  · exact absurd h hix
  · exact hf.2.2.2.2 i h hi

theorem FirstTwo.mk' {w : Fin n → ZOmega} {x y : Fin n} (hxy : x < y) (hx : IsOdd (w x))
    (hy : IsOdd (w y)) (h : ∀ i, i < y → i ≠ x → ¬ IsOdd (w i)) : FirstTwo w x y :=
  ⟨hxy, hx, hy, fun i hi => h i (hi.trans hxy) (ne_of_lt hi),
    fun i h1 h2 => h i h2 (ne_of_gt h1)⟩

theorem hasNum_Xswap {v : Fin n → ℂ} {k : ℕ} {u : Fin n → ZOmega} (h : HasNum v k u)
    {a b : Fin n} (hab : a ≠ b) :
    HasNum (twoLevel a b Xmat *ᵥ v) k (fun i => u (Equiv.swap a b i)) := by
  intro i
  rw [twoLevel_X_mulVec hab, Equiv.symm_swap]
  exact h _

/-- `X_[a,b] X_[a,p] ≈ X_[b,p] X_[a,b]` read the other way. -/
theorem eXap (a b p : Fin n) (hab : a < b) (hbp : b < p) :
    gX a p (hab.trans hbp) * gX a b hab = gX a b hab * gX b p hbp :=
  conj_swap (e3 a b hab) (e12 a b p hab hbp)

/-- `X_[c,b] X_[a,b] ≈ X_[c,a] X_[c,b]` (`c < a < b`), from (12) and (13). -/
theorem eXcb (c a b : Fin n) (hca : c < a) (hab : a < b) :
    gX c b (hca.trans hab) * gX a b hab = gX c a hca * gX c b (hca.trans hab) :=
  ((e12 c a b hca hab).trans (e13 a b c hca hab)).symm

/-- Cases 3–5 of the proof of Lemma 31: the basic edge `X_[a,a+1]`. -/
theorem square_X (hn : n ≤ 4) {s : St n} (hs : s ≠ 1) (a b : Fin n) (hab : a < b)
    (hb : (b : ℕ) = a + 1) : Square s (Gen.X a b hab) := by
  obtain ⟨p, hp⟩ := exists_pivot hs
  have hlt_b : ∀ i : Fin n, i < b → i ≤ a := fun i hi => by
    rw [Fin.lt_def] at hi; rw [Fin.le_def]; omega
  have hgt_a : ∀ i : Fin n, a < i → b ≤ i := fun i hi => by
    rw [Fin.lt_def] at hi; rw [Fin.le_def]; omega
  by_cases hbp : b ≤ p
  swap
  · -- Subcases 3.5.1 and 4.1: the pivot is below `b`, retrograde
    have hpb : p < b := lt_of_not_ge hbp
    have hcol : col (sem n (Gen.X a b hab) * s) b = col (sem n (Gen.X a b hab)) b := by
      rw [col_mul, hp.2 b hpb, mulVec_ev]
    have hr : IsPivot (sem n (Gen.X a b hab) * s) b := by
      refine ⟨by rw [hcol]; exact (isPivot_X hab).1, fun q hq => ?_⟩
      rw [col_mul, hp.2 q (hpb.trans hq), sm_sem]
      apply mat_mulVec_ev_of_ne
      intro i hi
      simp only [gidx, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact ne_of_lt (hab.trans hq)
      · exact ne_of_lt hq
    have hsylr : syl (sem n (Gen.X a b hab) * s) = ω b ^ 0 * X a b hab := by
      rw [syl_eq hr, hcol, ← syl_eq (isPivot_X hab), syl_X hab]
    refine sq_retro hs hr.ne_one hsylr ?_
    rw [derivable_iff]
    simp only [map_mul, map_one, cl_X, pow_zero, one_mul]
    exact e3 a b hab
  have hap : a < p := hab.trans_le hbp
  have hgidx : ∀ i ∈ gidx (Gen.X a b hab), i ≤ p := by
    intro i hi
    simp only [gidx, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact hap.le
    · exact hbp
  obtain ⟨u, hu⟩ : ∃ u, HasNum (col s p) (lde (col s p)) u := ⟨_, hasNum_num s p⟩
  have hcolr : col (sem n (Gen.X a b hab) * s) p = twoLevel a b Xmat *ᵥ col s p := by
    rw [col_mul, sm_sem]; rfl
  have hur : HasNum (col (sem n (Gen.X a b hab) * s) p) (lde (col s p))
      (fun i => u (Equiv.swap a b i)) := by
    rw [hcolr]; exact hasNum_Xswap hu hab.ne
  have swa : Equiv.swap a b a = b := Equiv.swap_apply_left a b
  have swb : Equiv.swap a b b = a := Equiv.swap_apply_right a b
  have swo : ∀ i, i ≠ a → i ≠ b → Equiv.swap a b i = i :=
    fun i h1 h2 => Equiv.swap_apply_of_ne_of_ne h1 h2
  rcases Nat.eq_zero_or_pos (lde (col s p)) with hk | hk
  · -- `k = 0`: Subcases 3.5.2–3.7 and their analogues
    rw [hk] at hu hur
    obtain ⟨c, hcp, hc1, hc0⟩ := unit_data' hp hu
    have hcne : u c ≠ 0 := fun h' => by rw [h'] at hc1; simp [nrm0] at hc1
    have hvz : ∀ i, i ≠ c → col s p i = 0 := fun i hi => by
      have := hu i; rw [pow_zero, one_mul, hc0 i hi, map_zero] at this; exact this
    have hpiv : ∀ i, u (Equiv.swap a b i) ≠ (if i = p then 1 else 0) →
        IsPivot (sem n (Gen.X a b hab) * s) p := fun i hi =>
      isPivot_mul hp hgidx (fun he => hi (num_eq_ev hur (by rw [hcolr]; exact he) i))
    have hsame : col s p a = 0 → col s p b = 0 →
        col (sem n (Gen.X a b hab) * s) p = col s p := fun h1 h2 => by
      rw [hcolr]; exact twoLevel_mulVec_of_zero hab.ne _ h1 h2
    have hlett : ∀ {G : Gen n}, (∀ i ∈ gidx G, i < p) →
        AllBelow (level s) (⟪syl s⟫ * s) (FreeMonoid.of G) := fun hG =>
      allBelow_A hp (t_above hp hk) (AllL.of hG)
    have hXab : ∀ i ∈ gidx (Gen.X a b hab), i < p → i < p := fun _ _ h => h
    rcases hcp.lt_or_eq with hcp' | hcp'
    · -- `c < p`
      have hsyl := syl_unit_lt_of hp hu hcne hc0 hcp'
      by_cases hca : c = a
      · subst c
        by_cases hbp' : b = p
        · -- `c = a`, `b = p`: the syllable of `s` is `ωᵉ_[b] X_[a,b]`
          subst p
          by_cases h8 : uexp (u a) = 8
          · apply sq_triv hs
            rw [hsyl, h8]
            simpa using Derivable.refl (Γ := Rel n) (FreeMonoid.of (Gen.X a b hab))
          · have hub : u b = 0 := hc0 b hab.ne'
            have hr : IsPivot (sem n (Gen.X a b hab) * s) b := by
              refine hpiv b ?_
              rw [swb, if_pos rfl]
              intro h1
              apply h8
              rw [h1]; decide
            have h1 : u (Equiv.swap a b b) ≠ 0 := by rw [swb]; exact hcne
            have h2 : ∀ i, i ≠ b → u (Equiv.swap a b i) = 0 := by
              intro i hi
              by_cases hia : i = a
              · rw [hia, swa, hub]
              · rw [swo i hia hi]; exact hc0 i hia
            have hsylr := syl_unit_eq_of hr hur h1 h2
            rw [swb] at hsylr
            refine sq_gen hr.ne_one hsylr (G' := 1) ?_ (AllBelow.one' (level_syl_lt hs))
            rw [hsyl]
            simpa using Derivable.refl (Γ := Rel n)
              (ω b ^ (8 - uexp (u a)) * FreeMonoid.of (Gen.X a b hab))
        · -- `c = a < b < p`: `G' = X_[a,b]`, by (12)
          have hbp'' : b < p := lt_of_le_of_ne hbp hbp'
          have hub : u b = 0 := hc0 b hab.ne'
          have hr : IsPivot (sem n (Gen.X a b hab) * s) p := by
            refine hpiv b ?_
            rw [swb, if_neg hbp']; exact hcne
          have h1 : u (Equiv.swap a b b) ≠ 0 := by rw [swb]; exact hcne
          have h2 : ∀ i, i ≠ b → u (Equiv.swap a b i) = 0 := by
            intro i hi
            by_cases hia : i = a
            · rw [hia, swa, hub]
            · rw [swo i hia hi]; exact hc0 i hia
          have hsylr := syl_unit_lt_of hr hur h1 h2 hbp''
          rw [swb] at hsylr
          refine sq_gen hr.ne_one hsylr (G' := X a b hab) ?_ ?_
          · rw [hsyl, derivable_iff]
            simp only [map_mul, map_pow, cl_ω, cl_X]
            have hc : Commute (gX a b hab) (gω p ^ (8 - uexp (u a))) :=
              ((c_ωX hab (ne_of_gt hap) (ne_of_gt hbp'')).pow_left _).symm
            rw [mul_assoc, ← e12 a b p hab hbp'', ← mul_assoc, ← hc.eq, mul_assoc]
          · exact hlett (by
              intro i hi
              simp only [gidx, List.mem_cons, List.not_mem_nil, or_false] at hi
              rcases hi with rfl | rfl
              · exact hap
              · exact hbp'')
      · by_cases hcb : c = b
        · -- `c = b < p`: `G' = X_[a,b]`, by (12)
          subst c
          have hua : u a = 0 := hc0 a hab.ne
          have hr : IsPivot (sem n (Gen.X a b hab) * s) p := by
            refine hpiv a ?_
            rw [swa, if_neg (ne_of_lt hap)]; exact hcne
          have h1 : u (Equiv.swap a b a) ≠ 0 := by rw [swa]; exact hcne
          have h2 : ∀ i, i ≠ a → u (Equiv.swap a b i) = 0 := by
            intro i hi
            by_cases hib : i = b
            · rw [hib, swb, hua]
            · rw [swo i hi hib]; exact hc0 i hib
          have hsylr := syl_unit_lt_of hr hur h1 h2 hap
          rw [swa] at hsylr
          refine sq_gen hr.ne_one hsylr (G' := X a b hab) ?_ ?_
          · rw [hsyl, derivable_iff]
            simp only [map_mul, map_pow, cl_ω, cl_X]
            have hc : Commute (gX a b hab) (gω p ^ (8 - uexp (u b))) :=
              ((c_ωX hab (ne_of_gt hap) (ne_of_gt hcp')).pow_left _).symm
            rw [mul_assoc, eXap a b p hab hcp', ← mul_assoc, ← hc.eq, mul_assoc]
          · exact hlett (by
              intro i hi
              simp only [gidx, List.mem_cons, List.not_mem_nil, or_false] at hi
              rcases hi with rfl | rfl
              · exact hap
              · exact hcp')
        · have hva : col s p a = 0 := hvz a (Ne.symm hca)
          have hvb : col s p b = 0 := hvz b (Ne.symm hcb)
          have hcol := hsame hva hvb
          have hr : IsPivot (sem n (Gen.X a b hab) * s) p :=
            ⟨by rw [hcol]; exact hp.1, (isPivot_mul hp hgidx (by
              rw [← sm_sem, ← col_mul, hcol]; exact hp.1)).2⟩
          have hsylr : syl (sem n (Gen.X a b hab) * s) = syl s := by
            rw [syl_eq hr, syl_eq hp, hcol]
          by_cases hbp' : b = p
          · -- `c < a`, `b = p`: `G' = X_[c,a]`, by (12) and (13)
            subst p
            have hca' : c < a := lt_of_le_of_ne (hlt_b c hcp') hca
            refine sq_gen hr.ne_one hsylr (G' := X c a hca') ?_ ?_
            · rw [hsyl, derivable_iff]
              simp only [map_mul, map_pow, cl_ω, cl_X]
              have hc : Commute (gω b ^ (8 - uexp (u c))) (gX c a hca') :=
                (c_ωX hca' (ne_of_gt hcp') (ne_of_gt hab)).pow_left _
              rw [mul_assoc, eXcb c a b hca' hab, ← mul_assoc, hc.eq, mul_assoc]
            · exact hlett (by
                intro i hi
                simp only [gidx, List.mem_cons, List.not_mem_nil, or_false] at hi
                rcases hi with rfl | rfl
                · exact hcp'
                · exact hab)
          · -- `{c, p} ∩ {a, b} = ∅`: `G' = X_[a,b]`
            have hbp'' : b < p := lt_of_le_of_ne hbp hbp'
            refine sq_gen hr.ne_one hsylr (G' := X a b hab) ?_ ?_
            · rw [hsyl, derivable_iff]
              simp only [map_mul, map_pow, cl_ω, cl_X]
              have h1 : Commute (gX a b hab) (gω p ^ (8 - uexp (u c))) :=
                ((c_ωX hab (ne_of_gt hap) (ne_of_gt hbp'')).pow_left _).symm
              have h2 : Commute (gX a b hab) (gX c p hcp') :=
                e9 a b c p hab hcp' hca hcb (ne_of_gt hap) (ne_of_gt hbp'')
              exact (h1.mul_right h2).eq.symm
            · exact hlett (by
                intro i hi
                simp only [gidx, List.mem_cons, List.not_mem_nil, or_false] at hi
                rcases hi with rfl | rfl
                · exact hap
                · exact hbp'')
    · -- `c = p`: the pivot column is `ωᵐ e_p`
      subst c
      have hsyl := syl_unit_eq_of hp hu hcne hc0
      have hua : u a = 0 := hc0 a (ne_of_lt hap)
      by_cases hbp' : b = p
      · -- `b = p`: the normal edge out of `r` is `N` after `X_[a,b]`
        subst p
        have hr : IsPivot (sem n (Gen.X a b hab) * s) b := by
          refine hpiv a ?_
          rw [swa, if_neg hab.ne]; exact hcne
        have h1 : u (Equiv.swap a b a) ≠ 0 := by rw [swa]; exact hcne
        have h2 : ∀ i, i ≠ a → u (Equiv.swap a b i) = 0 := by
          intro i hi
          by_cases hib : i = b
          · rw [hib, swb, hua]
          · rw [swo i hi hib]; exact hc0 i hib
        have hsylr := syl_unit_lt_of hr hur h1 h2 hab
        rw [swa] at hsylr
        refine sq_gen hr.ne_one hsylr (G' := 1) ?_ (AllBelow.one' (level_syl_lt hs))
        rw [hsyl, derivable_iff]
        simp only [map_mul, map_pow, cl_ω, cl_X, one_mul]
        rw [mul_assoc, gX_sq, mul_one]
      · -- `b < p`: `G' = X_[a,b]`
        have hbp'' : b < p := lt_of_le_of_ne hbp hbp'
        have hcol := hsame (hvz a (ne_of_lt hap)) (hvz b hbp')
        have hr : IsPivot (sem n (Gen.X a b hab) * s) p :=
          ⟨by rw [hcol]; exact hp.1, (isPivot_mul hp hgidx (by
            rw [← sm_sem, ← col_mul, hcol]; exact hp.1)).2⟩
        have hsylr : syl (sem n (Gen.X a b hab) * s) = syl s := by
          rw [syl_eq hr, syl_eq hp, hcol]
        refine sq_gen hr.ne_one hsylr (G' := X a b hab) ?_ ?_
        · rw [hsyl, derivable_iff]
          simp only [map_mul, map_pow, cl_ω, cl_X]
          exact ((c_ωX hab (ne_of_gt hap) (ne_of_gt hbp'')).pow_left _).eq
        · exact hlett (by
            intro i hi
            simp only [gidx, List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl
            · exact hap
            · exact hbp'')
  · -- `k > 0`
    obtain ⟨α, β, hf, hβp⟩ := odd_data' hp hu hk rfl
    have hsyl := syl_H_of' hp hu hk hf hf.1
    obtain ⟨ht1, ht2⟩ := t_below hp hk
    have hpiv : ∀ i, IsOdd (u (Equiv.swap a b i)) → IsPivot (sem n (Gen.X a b hab) * s) p :=
      fun i hi => isPivot_mul hp hgidx (by
        rw [← sm_sem, ← col_mul]; exact ne_ev_of_hasNum hur hk ⟨i, hi⟩ p)
    have hBXab : AllBelow (level s) (⟪syl s⟫ * s) (X a b hab) :=
      allBelow_B hp ht1 ht2 (AllL.of ⟨trivial, by simp [gidx, hap.le, hbp]⟩)
    have hlt : ∀ i : Fin n, i < α → ¬ IsOdd (u i) := hf.2.2.2.1
    by_cases hαa : α = a
    · subst α
      by_cases hβb : β = b
      · -- Subcase 3.1: `α = a`, `β = b`; the residues exchange
        subst β
        have hf' : FirstTwo (fun i => u (Equiv.swap a b i)) a b := by
          refine FirstTwo.mk' hab (by rw [swa]; exact hf.2.2.1) (by rw [swb]; exact hf.2.1) ?_
          intro i hi hia
          have hia' : i < a := lt_of_le_of_ne (hlt_b i hi) hia
          rw [swo i hia (ne_of_lt hi)]
          exact hlt i hia'
        have hr := hpiv a (by rw [swa]; exact hf.2.2.1)
        have hsylr := syl_H_of' hr hur hk hf' hab
        rw [swa, swb, zexp_swap] at hsylr
        have hz := zexp_lt (u a) (u b)
        by_cases hz0 : zexp (u a) (u b) = 0
        · rw [hz0] at hsylr hsyl
          refine sq_gen hr.ne_one hsylr (G' := ω b ^ 4) ?_ ?_
          · rw [hsyl, derivable_iff]
            simp only [map_mul, map_pow, cl_ω, cl_X, cl_H, pow_zero, mul_one,
              show (4 - 0) % 4 = 0 from rfl]
            exact e18 a b hab
          · exact allBelow_B hp ht1 ht2 ((AllL.of ⟨trivial, by simp [gidx, hbp]⟩).pow 4)
        · have he : (4 - zexp (u a) (u b)) % 4 = 4 - zexp (u a) (u b) := by omega
          rw [he] at hsylr
          refine sq_gen hr.ne_one hsylr (G' := ω a ^ (4 + (4 - zexp (u a) (u b))) *
            ω b ^ (4 - zexp (u a) (u b)) * X a b hab) ?_ ?_
          · rw [hsyl, derivable_iff]
            simp only [map_mul, map_pow, cl_ω, cl_X, cl_H]
            rw [eHωX a b hab _ (by omega), show 4 - (4 - zexp (u a) (u b)) = zexp (u a) (u b)
              by omega]
            simp only [mul_assoc]
          · apply allBelow_B hp ht1 ht2
            refine ((AllL.of ?_).pow _ |>.mul ((AllL.of ?_).pow _)).mul (AllL.of ?_)
            · exact ⟨trivial, by simp [gidx, hap.le]⟩
            · exact ⟨trivial, by simp [gidx, hbp]⟩
            · exact ⟨trivial, by simp [gidx, hap.le, hbp]⟩
      · -- Subcase 3.2: `α = a < b < β`
        have hbβ : b < β := lt_of_le_of_ne (hgt_a β hf.1) (Ne.symm hβb)
        have hob : ¬ IsOdd (u b) := hf.2.2.2.2 b hab hbβ
        have hβa : β ≠ a := ne_of_gt hf.1
        have hf' : FirstTwo (fun i => u (Equiv.swap a b i)) b β := by
          refine FirstTwo.mk' hbβ (by rw [swb]; exact hf.2.1)
            (by rw [swo β hβa hβb]; exact hf.2.2.1) ?_
          intro i hi hib
          by_cases hia : i = a
          · rw [hia, swa]; exact hob
          · rw [swo i hia hib]; exact hf.below i hi hia
        have hr := hpiv b (by rw [swb]; exact hf.2.1)
        have hsylr := syl_H_of' hr hur hk hf' hbβ
        rw [swb, swo β hβa hβb] at hsylr
        refine sq_gen hr.ne_one hsylr (G' := X a b hab) ?_ hBXab
        rw [hsyl, derivable_iff]
        simp only [map_mul, map_pow, cl_ω, cl_X, cl_H]
        have h1 : gω b ^ zexp (u a) (u β) * gX a b hab = gX a b hab * gω a ^ zexp (u a) (u β) :=
          ((s_Xωj hab).pow_right _).eq.symm
        rw [mul_assoc, h1, ← mul_assoc, ← e14 a b β hab hbβ, mul_assoc]
    · by_cases hαb : α = b
      · -- Subcase 3.3: `α = b`
        subst α
        have hoa : ¬ IsOdd (u a) := hlt a hab
        have hβa : β ≠ a := ne_of_gt (hab.trans hf.1)
        have hβb : β ≠ b := ne_of_gt hf.1
        have hf' : FirstTwo (fun i => u (Equiv.swap a b i)) a β := by
          refine FirstTwo.mk' (hab.trans hf.1) (by rw [swa]; exact hf.2.1)
            (by rw [swo β hβa hβb]; exact hf.2.2.1) ?_
          intro i hi hia
          by_cases hib : i = b
          · rw [hib, swb]; exact hoa
          · rw [swo i hia hib]; exact hf.below i hi hib
        have hr := hpiv a (by rw [swa]; exact hf.2.1)
        have hsylr := syl_H_of' hr hur hk hf' (hab.trans hf.1)
        rw [swa, swo β hβa hβb] at hsylr
        refine sq_gen hr.ne_one hsylr (G' := X a b hab) ?_ hBXab
        rw [hsyl, derivable_iff]
        simp only [map_mul, map_pow, cl_ω, cl_X, cl_H]
        have h1 : gω a ^ zexp (u b) (u β) * gX a b hab = gX a b hab * gω b ^ zexp (u b) (u β) :=
          ((s_Xωk hab).pow_right _).eq.symm
        rw [mul_assoc, h1, ← mul_assoc, e21 a b β hab hf.1, mul_assoc]
      · by_cases hβa : β = a
        · subst β
          by_cases hob : IsOdd (u b)
          · -- Subcases 4.3 and 4.4
            exact square_X_hard hn hs hab hb hp hbp hu hk hf hob
          · -- Subcase 4.2: `β = a`, `b` even
            have hf' : FirstTwo (fun i => u (Equiv.swap a b i)) α b := by
              refine FirstTwo.mk' (hf.1.trans hab) (by rw [swo α hαa hαb]; exact hf.2.1)
                (by rw [swb]; exact hf.2.2.1) ?_
              intro i hi hiα
              by_cases hia : i = a
              · rw [hia, swa]; exact hob
              · have hia' : i < a := lt_of_le_of_ne (hlt_b i hi) hia
                rw [swo i hia (ne_of_lt hi)]; exact hf.below i hia' hiα
            have hr := hpiv α (by rw [swo α hαa hαb]; exact hf.2.1)
            have hsylr := syl_H_of' hr hur hk hf' (hf.1.trans hab)
            rw [swo α hαa hαb, swb] at hsylr
            refine sq_gen hr.ne_one hsylr (G' := X a b hab) ?_ hBXab
            rw [hsyl, derivable_iff]
            simp only [map_mul, map_pow, cl_ω, cl_X, cl_H]
            have h1 : gω α ^ zexp (u α) (u a) * gX a b hab =
                gX a b hab * gω α ^ zexp (u α) (u a) :=
              ((c_ωX hab hαa hαb).pow_left _).eq
            rw [mul_assoc, h1, ← mul_assoc, ← e15 a b α hf.1 hab, mul_assoc]
        · by_cases hβb : β = b
          · -- `β = b`, `α < a`: the mirror of Subcase 4.2
            subst β
            have hαa' : α < a := lt_of_le_of_ne (hlt_b α hf.1) hαa
            have hoa : ¬ IsOdd (u a) := hf.2.2.2.2 a hαa' hab
            have hf' : FirstTwo (fun i => u (Equiv.swap a b i)) α a := by
              refine FirstTwo.mk' hαa' (by rw [swo α hαa hαb]; exact hf.2.1)
                (by rw [swa]; exact hf.2.2.1) ?_
              intro i hi hiα
              rw [swo i (ne_of_lt hi) (ne_of_lt (hi.trans hab))]
              exact hf.below i (hi.trans hab) hiα
            have hr := hpiv α (by rw [swo α hαa hαb]; exact hf.2.1)
            have hsylr := syl_H_of' hr hur hk hf' hαa'
            rw [swo α hαa hαb, swa] at hsylr
            refine sq_gen hr.ne_one hsylr (G' := X a b hab) ?_ hBXab
            rw [hsyl, derivable_iff]
            simp only [map_mul, map_pow, cl_ω, cl_X, cl_H]
            have h1 : gω α ^ zexp (u α) (u b) * gX a b hab =
                gX a b hab * gω α ^ zexp (u α) (u b) :=
              ((c_ωX hab hαa hαb).pow_left _).eq
            rw [mul_assoc, h1, ← mul_assoc, e22 a b α hαa' hab, mul_assoc]
          · -- `{α, β} ∩ {a, b} = ∅`: `G' = X_[a,b]`
            have hf' : FirstTwo (fun i => u (Equiv.swap a b i)) α β := by
              refine FirstTwo.mk' hf.1 (by rw [swo α hαa hαb]; exact hf.2.1)
                (by rw [swo β hβa hβb]; exact hf.2.2.1) ?_
              intro i hi hiα
              by_cases hia : i = a
              · rw [hia, swa]
                have hbβ : b < β := lt_of_le_of_ne (hgt_a β (hia ▸ hi)) (Ne.symm hβb)
                exact hf.below b hbβ (Ne.symm hαb)
              · by_cases hib : i = b
                · rw [hib, swb]
                  exact hf.below a (hab.trans (hib ▸ hi)) (Ne.symm hαa)
                · rw [swo i hia hib]; exact hf.below i hi hiα
            have hr := hpiv α (by rw [swo α hαa hαb]; exact hf.2.1)
            have hsylr := syl_H_of' hr hur hk hf' hf.1
            rw [swo α hαa hαb, swo β hβa hβb, ← hsyl] at hsylr
            refine sq_gen hr.ne_one hsylr (G' := X a b hab) ?_ hBXab
            rw [hsyl, derivable_iff]
            simp only [map_mul, map_pow, cl_ω, cl_X, cl_H]
            have h1 : Commute (gX a b hab) (gH α β hf.1) :=
              (e8 α β a b hf.1 hab (Ne.symm hαa) (Ne.symm hβa) (Ne.symm hαb) (Ne.symm hβb)).symm
            have h2 : Commute (gX a b hab) (gω α ^ zexp (u α) (u β)) :=
              ((c_ωX hab hαa hαb).pow_left _).symm
            exact (h1.mul_right h2).eq.symm

end

end QCert.Greylyn
