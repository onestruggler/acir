/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024), after the Agda `CCX+H-3qubit-RS`: Theorem 6.3

Translation of `PresentationH.agda`.  Theorem 6.3 of Amy, Ross and Wesley,
with `r_K`: the circuits over `Σ₂ = Σ₁ ∪ {H₂}` modulo
`R₂⁺ = R₀ ∪ R₈₄ ∪ Figure 8 ∪ {r_K}` present `TofH(3) = L₈`.

Completeness as for `O(8, 𝔻)`, now through Li, Ross and Selinger's
presentation of `L₈` by Tables 1 and 2 (`LiRossSelinger.completeL`): a
circuit over `Σ₂` is the decoding of its encoding (`GoodH`, from `Good` one
level down, and `H₂` for `I ⊗ H`), and the decoding respects Tables 1 and 2
(`DecodeH`).  Surjectivity: the decoding of a generator of `𝓕₈` has its
value (`dec_sem`, and `H₂` for `I ⊗ H`).
-/
import QCert.ToffoliHadamardRS.DecodeH

namespace QCert.ToffoliHadamardRS

open LiRossSelinger (Gen GenL Table12 toL)

/-! ## Completeness -/

/-- Decoding the encoding gives the circuit back. -/
def GoodH (w : Word G₂) : Prop := Derivable R2plus (decLW (encLW w)) w

theorem encL_up (g : G₁) : encL g.up = toL (enc g) := by cases g <;> rfl

theorem goodH_up (g : G₁) : GoodH (FreeMonoid.of g.up) := by
  unfold GoodH
  rw [FreeMonoid.lift_eval_of, encL_up, decL_toL]
  have := lift12 (Complete.good derived (FreeMonoid.of g))
  rw [FreeMonoid.lift_eval_of] at this
  exact this

theorem good_gateH : ∀ g : G₂, GoodH (FreeMonoid.of g)
  | .X₀ => goodH_up .X₀
  | .X₁ => goodH_up .X₁
  | .X₂ => goodH_up .X₂
  | .Z₀ => goodH_up .Z₀
  | .Z₁ => goodH_up .Z₁
  | .Z₂ => goodH_up .Z₂
  | .CX₀₁ => goodH_up .CX₀₁
  | .CX₀₂ => goodH_up .CX₀₂
  | .CX₁₀ => goodH_up .CX₁₀
  | .CX₁₂ => goodH_up .CX₁₂
  | .CX₂₀ => goodH_up .CX₂₀
  | .CX₂₁ => goodH_up .CX₂₁
  | .CZ₀₁ => goodH_up .CZ₀₁
  | .CZ₀₂ => goodH_up .CZ₀₂
  | .CZ₁₂ => goodH_up .CZ₁₂
  | .CCX₀₁ => goodH_up .CCX₀₁
  | .CCX₀₂ => goodH_up .CCX₀₂
  | .CCX₁₂ => goodH_up .CCX₁₂
  | .K₀₁ => goodH_up .K₀₁
  | .K₁₂ => goodH_up .K₁₂
  | .SW₀₁ => goodH_up .SW₀₁
  | .SW₀₂ => goodH_up .SW₀₂
  | .SW₁₂ => goodH_up .SW₁₂
  | .NK => goodH_up .NK
  | .CCZ => goodH_up .CCZ
  | .H₂ => Derivable.refl _

theorem goodH (w : Word G₂) : GoodH w := by
  induction w using FreeMonoid.inductionOn' with
  | one => exact Derivable.refl _
  | mul_of g w ih =>
    unfold GoodH at *; rw [map_mul, map_mul]; exact (good_gateH g).mul ih

theorem complete2 {w v : Word G₂} (h : semH w = semH v) : Derivable R2plus w v :=
  (goodH w).symm.trans ((decL_cong (LiRossSelinger.completeL 4 (by norm_num) h)).trans (goodH v))

/-! ## The decoding of a generator has its value -/

theorem noH_up (w : Word G₁) : noH (upW w) = true := by
  induction w using FreeMonoid.inductionOn' with
  | one => rfl
  | mul_of g w ih =>
    simp only [noH, map_mul, FreeMonoid.toList_mul, List.all_append, Bool.and_eq_true] at ih ⊢
    exact ⟨by cases g <;> rfl, ih⟩

theorem enc_up {k : ℕ} (g : Gate k) : enc g.up = enc g := by cases g <;> rfl

theorem semO_upW {k : ℕ} (w : Word (Gate k)) : semO (upW w) = semO w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of g w ih =>
    rw [map_mul, map_mul, map_mul, ih, FreeMonoid.map_of]
    simp only [semO, MonoidHom.comp_apply, FreeMonoid.lift_eval_of, enc_up]

theorem decL_sem : ∀ x : GenL 4, semH (decL x) = LiRossSelinger.semL 4 x
  | .base g => by
    apply Subtype.ext
    rw [decL, semH_noH _ (noH_up _), semO_upW, dec_sem]; rfl
  | .ih => rfl

theorem decL_semW (u : Word (GenL 4)) :
    semH (decLW u) = FreeMonoid.lift (LiRossSelinger.semL 4) u := by
  induction u using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of x u ih =>
    rw [map_mul, map_mul, map_mul, FreeMonoid.lift_eval_of, FreeMonoid.lift_eval_of, decL_sem, ih]

/-! ## The presentation -/

theorem invol2_up (g : G₁) :
    Derivable R2plus (FreeMonoid.of g.up * FreeMonoid.of g.up) 1 := by
  have := lift12 (invol1 g)
  rwa [map_mul, map_one, FreeMonoid.map_of] at this

theorem grouplike2 : Grouplike R2plus
  | .X₀ => ⟨FreeMonoid.of .X₀, invol2_up .X₀⟩
  | .X₁ => ⟨FreeMonoid.of .X₁, invol2_up .X₁⟩
  | .X₂ => ⟨FreeMonoid.of .X₂, invol2_up .X₂⟩
  | .Z₀ => ⟨FreeMonoid.of .Z₀, invol2_up .Z₀⟩
  | .Z₁ => ⟨FreeMonoid.of .Z₁, invol2_up .Z₁⟩
  | .Z₂ => ⟨FreeMonoid.of .Z₂, invol2_up .Z₂⟩
  | .CX₀₁ => ⟨FreeMonoid.of .CX₀₁, invol2_up .CX₀₁⟩
  | .CX₀₂ => ⟨FreeMonoid.of .CX₀₂, invol2_up .CX₀₂⟩
  | .CX₁₀ => ⟨FreeMonoid.of .CX₁₀, invol2_up .CX₁₀⟩
  | .CX₁₂ => ⟨FreeMonoid.of .CX₁₂, invol2_up .CX₁₂⟩
  | .CX₂₀ => ⟨FreeMonoid.of .CX₂₀, invol2_up .CX₂₀⟩
  | .CX₂₁ => ⟨FreeMonoid.of .CX₂₁, invol2_up .CX₂₁⟩
  | .CZ₀₁ => ⟨FreeMonoid.of .CZ₀₁, invol2_up .CZ₀₁⟩
  | .CZ₀₂ => ⟨FreeMonoid.of .CZ₀₂, invol2_up .CZ₀₂⟩
  | .CZ₁₂ => ⟨FreeMonoid.of .CZ₁₂, invol2_up .CZ₁₂⟩
  | .CCX₀₁ => ⟨FreeMonoid.of .CCX₀₁, invol2_up .CCX₀₁⟩
  | .CCX₀₂ => ⟨FreeMonoid.of .CCX₀₂, invol2_up .CCX₀₂⟩
  | .CCX₁₂ => ⟨FreeMonoid.of .CCX₁₂, invol2_up .CCX₁₂⟩
  | .K₀₁ => ⟨FreeMonoid.of .K₀₁, invol2_up .K₀₁⟩
  | .K₁₂ => ⟨FreeMonoid.of .K₁₂, invol2_up .K₁₂⟩
  | .SW₀₁ => ⟨FreeMonoid.of .SW₀₁, invol2_up .SW₀₁⟩
  | .SW₀₂ => ⟨FreeMonoid.of .SW₀₂, invol2_up .SW₀₂⟩
  | .SW₁₂ => ⟨FreeMonoid.of .SW₁₂, invol2_up .SW₁₂⟩
  | .NK => ⟨FreeMonoid.of .NK, invol2_up .NK⟩
  | .CCZ => ⟨FreeMonoid.of .CCZ, invol2_up .CCZ⟩
  | .H₂ => ⟨FreeMonoid.of .H₂, Derivable.of (R2plus.fig8 Fig8.r108)⟩

/-- Theorem 6.3, with `r_K`: `R₂⁺` presents `TofH(3) = L₈`. -/
theorem presentationH : IsPresentationOf R2plus sem2 where
  grouplike := grouplike2
  sound w v h := by rw [lift_sem2, lift_sem2]; exact sound2plus_ax h
  complete w v h := complete2 (by rwa [lift_sem2, lift_sem2] at h)
  surjective A := by
    obtain ⟨u, hu⟩ := LiRossSelinger.surjectiveL 4 A
    exact ⟨decLW u, by rw [lift_sem2, decL_semW, hu]⟩

end QCert.ToffoliHadamardRS
