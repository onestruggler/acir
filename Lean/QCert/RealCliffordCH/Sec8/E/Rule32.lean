/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E.5: the rule (32)

`D((-1)_[a]X_[a,a+1])` and `D((-1)_[b]X_[b,b+1])`, `a + 1 < b`, are
multi-controlled `ZX`/`XZ` gates on the wires `t`, `t'` where the Gray code
changes at `a` and at `b`.  On one wire they commute by (351); on two wires
by (352), which needs the controls on the other wires to differ somewhere:
otherwise `G(a), G(a+1), G(b), G(b+1)` would not be four distinct states
(`gray_separated`).
-/
import QCert.RealCliffordCH.Sec8.E.Rule22

namespace QCert.RealCliffordCH.Sec8.E

open Circuit Net

theorem gray_inj {n x y : ℕ} (hx : x < 2 ^ n) (hy : y < 2 ^ n) (h : gray x = gray y) : x = y := by
  rw [← gInv_gray hx, ← gInv_gray hy, h]

theorem gray_succ_tOf {n a : ℕ} (ha : a + 1 < 2 ^ n) : gray (a + 1) = gray a ^^^ 2 ^ tOf n a := by
  obtain ⟨β, hβ, _⟩ := succ_spec a
  rw [tOf_eq hβ ha]; exact gray_succ_eq hβ

theorem bool_ne {x y : Bool} (h : x ≠ y) : y = !x := by cases x <;> cases y <;> simp_all

/-- Two Gray steps `a → a + 1` and `b → b + 1`, `a + 1 < b`, on different wires:
the states `G(a)` and `G(b)` differ on some other wire. -/
theorem gray_separated {n a b : ℕ} (hab : a + 1 < b) (hb : b + 1 < 2 ^ n)
    (htt : tOf n a ≠ tOf n b) :
    ∃ w, w < n ∧ w ≠ tOf n a ∧ w ≠ tOf n b ∧ (gray a).testBit w ≠ (gray b).testBit w := by
  set ta := tOf n a
  set tb := tOf n b
  by_contra hne
  push Not at hne
  have han : a < 2 ^ n := by omega
  have hbn : b < 2 ^ n := by omega
  have hall : ∀ w, w ≠ ta → w ≠ tb → (gray a).testBit w = (gray b).testBit w := by
    intro w h1 h2
    by_cases hw : w < n
    · exact hne w hw h1 h2
    · rw [testBit_of_lt (gray_lt han) (by omega), testBit_of_lt (gray_lt hbn) (by omega)]
  have ga := gray_succ_tOf (n := n) (a := a) (by omega)
  have gb := gray_succ_tOf (n := n) (a := b) hb
  have xx : ∀ (g : ℕ) (t : ℕ), g ^^^ 2 ^ t ^^^ 2 ^ t = g := fun g t => by
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  by_cases e1 : (gray a).testBit ta = (gray b).testBit ta <;>
    by_cases e2 : (gray a).testBit tb = (gray b).testBit tb
  · have : gray a = gray b := Nat.eq_of_testBit_eq fun q => by
      by_cases h1 : q = ta
      · subst h1; exact e1
      · by_cases h2 : q = tb
        · subst h2; exact e2
        · exact hall q h1 h2
    have := gray_inj han hbn this; omega
  · have hgb : gray b = gray a ^^^ 2 ^ tb := Nat.eq_of_testBit_eq fun q => by
      by_cases h2 : q = tb
      · subst h2; rw [testBit_xor_pow_self]; exact bool_ne e2
      · rw [testBit_xor_pow_ne h2]
        by_cases h1 : q = ta
        · subst h1; exact e1.symm
        · exact (hall q h1 h2).symm
    have : gray (b + 1) = gray a := by rw [gb, hgb, xx]
    have := gray_inj (by omega) han this; omega
  · have hgb : gray b = gray (a + 1) := by
      rw [ga]
      exact Nat.eq_of_testBit_eq fun q => by
        by_cases h1 : q = ta
        · subst h1; rw [testBit_xor_pow_self]; exact bool_ne e1
        · rw [testBit_xor_pow_ne h1]
          by_cases h2 : q = tb
          · subst h2; exact e2.symm
          · exact (hall q h1 h2).symm
    have := gray_inj hbn (by omega) hgb; omega
  · have hgb : gray b = gray a ^^^ 2 ^ ta ^^^ 2 ^ tb := Nat.eq_of_testBit_eq fun q => by
      by_cases h2 : q = tb
      · subst h2; rw [testBit_xor_pow_self, testBit_xor_pow_ne (Ne.symm htt), bool_ne e2]
      · rw [testBit_xor_pow_ne h2]
        by_cases h1 : q = ta
        · subst h1; rw [testBit_xor_pow_self]; exact bool_ne e1
        · rw [testBit_xor_pow_ne h1]; exact (hall q h1 h2).symm
    have : gray (b + 1) = gray (a + 1) := by rw [gb, hgb, xx, ga]
    have := gray_inj (by omega) (by omega) this; omega

/-- Two decoded multi-controlled `ZX`/`XZ` gates commute: on one wire by
(351), on two wires by (352) when their controls differ on another wire. -/
theorem rots_comm {M : ℕ} (ih : IH (M + 3)) (α β : Bool) {t t' s s' : ℕ} (ht : t < M + 3)
    (ht' : t' < M + 3)
    (hsep : t ≠ t' → ∃ w, w < M + 3 ∧ w ≠ t ∧ w ≠ t' ∧ s.testBit w ≠ s'.testBit w) :
    D.Comm (M + 3) (mc (M + 3) (Kind.sgnZX α) [t] (ctlOf s t))
      (mc (M + 3) (Kind.sgnZX β) [t'] (ctlOf s' t')) := by
  have hK : ∀ γ : Bool, kindSp (Kind.sgnZX γ) = 1 := fun γ => by cases γ <;> rfl
  by_cases htt : t = t'
  · subst htt
    have hnd : [t].Nodup := by simp
    have hps : ∀ p ∈ [t], p < M + 3 := by simp [ht]
    have f := fun γ s => frame1 ih (Kind.sgnZX γ) (hK γ) ht s
    exact via_frame hnd hps (List.Forall₂.cons (f α s) (List.Forall₂.cons (f β s') List.Forall₂.nil))
      (List.Forall₂.cons (f β s') (List.Forall₂.cons (f α s) List.Forall₂.nil))
      (D.eq351 (M + 3) (by omega) ih (pull1 t s) (pull1 t s') α β)
  · have hnd : [t, t'].Nodup := by simp [htt]
    have hps : ∀ p ∈ [t, t'], p < M + 3 := by simp [ht, ht']
    have f1 := (frame2_one ih (Kind.sgnZX α) (hK α) ht ht' htt s).1
    have f2 := (frame2_one ih (Kind.sgnZX β) (hK β) ht' ht (Ne.symm htt) s').2
    obtain ⟨w, hw, hwt, hwt', hdiff⟩ := hsep htt
    have hd : DiffOn 2 (M + 3) (pull2 t t' s) (pull2 t t' s') := by
      refine ⟨pos (netOf [t, t']) w, ?_, pos_lt _ (netOf_ok hnd hps) w hw, ?_⟩
      · have h0 : frm [t, t'] 0 = t := frm_getD hnd hps (by simp)
        have h1 : frm [t, t'] 1 = t' := frm_getD hnd hps (by simp)
        by_contra hlt
        have : pos (netOf [t, t']) w = 0 ∨ pos (netOf [t, t']) w = 1 := by omega
        rcases this with e | e
        · apply hwt; rw [← frm_pos [t, t'] w, e, h0]
        · apply hwt'; rw [← frm_pos [t, t'] w, e, h1]
      · simp only [pull2, frm_pos, bitOf_eq]
        intro e; apply hdiff
        revert e; cases s.testBit w <;> cases s'.testBit w <;> simp
    exact via_frame hnd hps (List.Forall₂.cons f1 (List.Forall₂.cons f2 List.Forall₂.nil))
      (List.Forall₂.cons f2 (List.Forall₂.cons f1 List.Forall₂.nil))
      (D.eq352 (M + 3) (by omega) ih _ _ hd α β _ _)

theorem kindZX_sgn {k a : ℕ} (which : ℕ) : ∃ γ : Bool, kindZX (k + 1) a which = Kind.sgnZX γ := by
  unfold kindZX
  split_ifs
  · exact ⟨true, rfl⟩
  · exact ⟨false, rfl⟩

/-- (32) decodes to (351) or (352). -/
theorem dec32 {M : ℕ} (ih : IH (M + 3)) (a b : ℕ) (hab : a + 1 < b) (hb : b + 1 < 2 ^ (M + 3)) :
    Derivable (theory (M + 3))
      (decW (M + 3) (wordOf [Zx (M + 3) a a (a + 1), Zx (M + 3) b b (b + 1)]))
      (decW (M + 3) (wordOf [Zx (M + 3) b b (b + 1), Zx (M + 3) a a (a + 1)])) := by
  simp only [decW_wordOf, List.map, List.prod_cons, List.prod_nil, mul_one,
    dec_Zx_lo (show a + 1 < 2 ^ (M + 3) by omega), dec_Zx_lo hb]
  rw [dZX1_mc (M + 2), dZX1_mc (M + 2)]
  obtain ⟨α, hα⟩ := kindZX_sgn (k := M + 2) (a := a) 0
  obtain ⟨β, hβ⟩ := kindZX_sgn (k := M + 2) (a := b) 0
  rw [hα, hβ]
  have := rots_comm ih β α (tOf_lt b (by omega)) (tOf_lt a (by omega)) (fun htt => by
    obtain ⟨w, hw, h1, h2, h3⟩ := gray_separated (n := M + 2 + 1) hab hb (Ne.symm htt)
    exact ⟨w, hw, h2, h1, Ne.symm h3⟩)
  unfold D.Comm at this
  rw [drawn_two, drawn_two] at this
  exact this

end QCert.RealCliffordCH.Sec8.E
