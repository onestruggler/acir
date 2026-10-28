/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E.5: the rule (22)

`D((-1)_[a](-1)_[b])` is the product of the boxes `B_k = D((-1)_[k](-1)_[k+1])`
for `k` between `a` and `b`.  The boxes commute ((335) on one wire, (336) on
two, `box_comm`) and are involutions ((311), `box_inv`), so a product of
them only depends on the parity of the multiplicity of each box: the
products for `[a, b)` and `[b, c)` give the product for `[a, c)` after
permuting (`drawn_perm`) and cancelling (`drawn_cancel`).
-/
import QCert.RealCliffordCH.Sec8.E.Rules1

namespace QCert.RealCliffordCH.Sec8.E

open Circuit Net

/-! ## Commuting involutions -/

section Algebra

variable {N : ℕ}

theorem drawn_perm {l l' : List (Circ N)} (hp : l.Perm l')
    (hc : ∀ x ∈ l, ∀ y ∈ l, D.Comm N x y) : Derivable (theory N) (drawn l) (drawn l') := by
  induction hp with
  | nil => exact Derivable.refl _
  | cons x _ ih =>
    rw [drawn_cons, drawn_cons]
    exact dright _ (ih fun a ha b hb => hc a (by simp [ha]) b (by simp [hb]))
  | swap x y l =>
    rw [drawn_cons, drawn_cons, drawn_cons, drawn_cons, mul_assoc, mul_assoc]
    have this : Derivable (theory N) (drawn [x, y]) (drawn [y, x]) := hc x (by simp) y (by simp)
    rw [drawn_two, drawn_two] at this
    exact dleft _ this.symm
  | trans h1 h2 ih1 ih2 =>
    exact (ih1 hc).trans (ih2 fun a ha b hb => hc a (h1.symm.subset ha) b (h1.symm.subset hb))

theorem drawn_pal : ∀ C : List (Circ N), (∀ x ∈ C, Derivable (theory N) (drawn [x, x]) 1) →
    Derivable (theory N) (drawn (C ++ C.reverse)) 1
  | [], _ => by simp [drawn]; exact Derivable.refl _
  | x :: C, h => by
    have ih := drawn_pal C (fun y hy => h y (by simp [hy]))
    have hx := h x (by simp)
    rw [drawn_two] at hx
    have e : drawn ((x :: C) ++ (x :: C).reverse) = x * drawn (C ++ C.reverse) * x := by
      rw [List.reverse_cons, List.cons_append, drawn_cons, ← List.append_assoc, drawn_append,
        drawn_single]
    rw [e]
    have := dright x (dleft x ih)
    rw [mul_one] at this
    exact this.trans hx

theorem drawn_cancel (A C : List (Circ N)) (h : ∀ x ∈ C, Derivable (theory N) (drawn [x, x]) 1) :
    Derivable (theory N) (drawn (A ++ C ++ C.reverse)) (drawn A) := by
  rw [List.append_assoc, drawn_append]
  have := dright (drawn A) (drawn_pal C h)
  rwa [one_mul] at this

end Algebra

/-! ## Gates on one of two wires, moved by the frame of both -/

/-- A gate on wire `t` coloured by `s`, as the canonical gate on wire `0`
(`i = 0`) or `1` (`i = 1`) of the frame of `[t, t']`. -/
theorem frame2_one {N : ℕ} (ih : IH N) (K : Kind) (hK : kindSp K = 1) {t t' : ℕ} (ht : t < N)
    (ht' : t' < N) (htt : t ≠ t') (s : ℕ) :
    Derivable (theory N) (placedBy N (netOf [t, t'])
        (mc N K [0] (ctlOr (ctlAt 1 (decide (bitOf s t' = 1))) (colOn 2 N (pull2 t t' s)))))
      (mc N K [t] (ctlOf s t)) ∧
    Derivable (theory N) (placedBy N (netOf [t', t])
        (mc N K [1] (ctlOr (ctlAt 0 (decide (bitOf s t' = 1))) (colOn 2 N (pull2 t' t s)))))
      (mc N K [t] (ctlOf s t)) := by
  have hnd : [t, t'].Nodup := by simp [htt]
  have hps : ∀ p ∈ [t, t'], p < N := by simp [ht, ht']
  have hnd' : [t', t].Nodup := by simp [Ne.symm htt]
  have hps' : ∀ p ∈ [t', t], p < N := by simp [ht, ht']
  have h0 : frm [t, t'] 0 = t := frm_getD hnd hps (by simp)
  have h1 : frm [t, t'] 1 = t' := frm_getD hnd hps (by simp)
  have h0' : frm [t', t] 0 = t' := frm_getD hnd' hps' (by simp)
  have h1' : frm [t', t] 1 = t := frm_getD hnd' hps' (by simp)
  constructor
  · have := frame (mcSwapAll ih) hnd hps K [0] (ctlOf s t) (by simp [hK]) (by simp) (by simp; omega)
    rw [show [0].map (frm [t, t']) = [t] by simp [h0]] at this
    refine Derivable.trans ?_ this
    rw [Net.mc_congr N K [0] (c' := ctlOf s t ∘ frm [t, t']) ?_]
    intro j hj
    rcases j with _ | _ | j
    · simp [ctlOr, ctlAt, colOn, ctlOf, h0]
    · simp [ctlOr, ctlAt, colOn, ctlOf, h1, Ne.symm htt]
    · have hne1 : frm [t, t'] (j + 2) ≠ t := by
        intro e; have := frm_injective _ (e.trans h0.symm); omega
      simp [ctlOr, ctlAt, colOn, ctlOf, hne1, pull2, hj]
  · have := frame (mcSwapAll ih) hnd' hps' K [1] (ctlOf s t) (by simp [hK]) (by simp) (by simp; omega)
    rw [show [1].map (frm [t', t]) = [t] by simp [h1']] at this
    refine Derivable.trans ?_ this
    rw [Net.mc_congr N K [1] (c' := ctlOf s t ∘ frm [t', t]) ?_]
    intro j hj
    rcases j with _ | _ | j
    · simp [ctlOr, ctlAt, colOn, ctlOf, h0', Ne.symm htt]
    · simp [ctlOr, ctlAt, colOn, ctlOf, h1']
    · have hne1 : frm [t', t] (j + 2) ≠ t := by
        intro e; have := frm_injective _ (e.trans h1'.symm); omega
      simp [ctlOr, ctlAt, colOn, ctlOf, hne1, pull2, hj]

/-! ## The decoded boxes commute and are involutions -/

/-- Two boxes, each on one wire with a control on every other wire, commute. -/
theorem boxes_comm {M : ℕ} (ih : IH (M + 3)) {t t' s s' : ℕ} (ht : t < M + 3) (ht' : t' < M + 3) :
    D.Comm (M + 3) (mc (M + 3) .box [t] (ctlOf s t)) (mc (M + 3) .box [t'] (ctlOf s' t')) := by
  by_cases htt : t = t'
  · subst htt
    have hnd : [t].Nodup := by simp
    have hps : ∀ p ∈ [t], p < M + 3 := by simp [ht]
    have f := fun s => frame1 ih .box rfl ht s
    exact via_frame hnd hps (List.Forall₂.cons (f s) (List.Forall₂.cons (f s') List.Forall₂.nil))
      (List.Forall₂.cons (f s') (List.Forall₂.cons (f s) List.Forall₂.nil))
      (D.eq335 (M + 3) (by omega) ih (pull1 t s) (pull1 t s'))
  · have hnd : [t, t'].Nodup := by simp [htt]
    have hps : ∀ p ∈ [t, t'], p < M + 3 := by simp [ht, ht']
    have f1 := (frame2_one ih .box rfl ht ht' htt s).1
    have f2 := (frame2_one ih .box rfl ht' ht (Ne.symm htt) s').2
    exact via_frame hnd hps (List.Forall₂.cons f1 (List.Forall₂.cons f2 List.Forall₂.nil))
      (List.Forall₂.cons f2 (List.Forall₂.cons f1 List.Forall₂.nil))
      (D.eq336 (M + 3) (by omega) ih _ _ _ _)

/-- A box on one wire with a control on every other wire is an involution. -/
theorem box_inv {M : ℕ} (ih : IH (M + 3)) {t s : ℕ} (ht : t < M + 3) :
    Derivable (theory (M + 3)) (drawn [mc (M + 3) .box [t] (ctlOf s t), mc (M + 3) .box [t] (ctlOf s t)]) 1 := by
  have hnd : [t].Nodup := by simp
  have hps : ∀ p ∈ [t], p < M + 3 := by simp [ht]
  have f := frame1 ih .box rfl ht s
  have := via_frame hnd hps (L := [mc (M + 3) .box [t] (ctlOf s t), mc (M + 3) .box [t] (ctlOf s t)])
    (R := []) (List.Forall₂.cons f (List.Forall₂.cons f List.Forall₂.nil)) List.Forall₂.nil
    (by simpa [drawn] using D.eq311 (M + 3) (by omega) ih (pull1 t s))
  simpa [drawn] using this

/-! ## The rule -/

/-- The boxes `B_a, …, B_{b-1}`. -/
def zzL (n a b : ℕ) : List (Circ n) := (List.range (b - a)).map fun i => dZZ1 n (a + i)

theorem dZZ_zzL {n a b : ℕ} (h : a ≤ b) : dZZ n a b = drawn (zzL n a b) := dZZ_le h

theorem dZZ_zzL' {n a b : ℕ} (h : b ≤ a) : dZZ n a b = drawn (zzL n b a) := by
  rw [dZZ_comm]; exact dZZ_le h

theorem zzL_split {n a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    zzL n a c = zzL n a b ++ zzL n b c := by
  unfold zzL
  rw [show c - a = (b - a) + (c - b) by omega, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp]
  congr 1; omega

theorem perm_xyx {α : Type*} (X Y : List α) : (X ++ Y ++ X).Perm (Y ++ X ++ X.reverse) := by
  have h1 : (X ++ Y ++ X).Perm (Y ++ X ++ X) := by
    rw [List.append_assoc, List.append_assoc]
    exact (List.perm_append_comm.trans (by rw [List.append_assoc])).trans
      (List.Perm.append_left Y List.perm_append_comm)
  exact h1.trans (List.Perm.append_left _ (List.reverse_perm X).symm)

theorem perm_xxy {α : Type*} (X Y : List α) : (X ++ X ++ Y).Perm (Y ++ X ++ X.reverse) := by
  have h1 : (X ++ X ++ Y).Perm (Y ++ X ++ X) := by
    rw [List.append_assoc Y]; exact List.perm_append_comm
  exact h1.trans (List.Perm.append_left _ (List.reverse_perm X).symm)

theorem perm_yxx {α : Type*} (X Y : List α) : (Y ++ X ++ X).Perm (Y ++ X ++ X.reverse) :=
  List.Perm.append_left _ (List.reverse_perm X).symm

/-- (22) decodes to a product of commuting involutions, permuted and cancelled. -/
theorem dec22 {M : ℕ} (ih : IH (M + 3)) (a b c : ℕ) (ha : a < 2 ^ (M + 3)) (hb : b < 2 ^ (M + 3))
    (hc : c < 2 ^ (M + 3)) :
    Derivable (theory (M + 3)) (decW (M + 3) (wordOf [Zz (M + 3) a b, Zz (M + 3) b c]))
      (decW (M + 3) (wordOf [Zz (M + 3) a c])) := by
  simp only [decW_wordOf, List.map, List.prod_cons, List.prod_nil, mul_one, dec_Zz ha hb,
    dec_Zz hb hc, dec_Zz ha hc]
  -- the boxes commute and are involutions
  have isB : ∀ {x y : ℕ} {L : List (Circ (M + 3))}, L = zzL (M + 3) x y →
      ∀ z ∈ L, ∃ k, z = dZZ1 (M + 3) k := by
    intro x y L hL z hz
    rw [hL] at hz
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hz
    exact ⟨_, rfl⟩
  have comm : ∀ z ∈ (∅ : List (Circ (M + 3))), True := fun _ _ => trivial
  have hcomm : ∀ (u v : ℕ), D.Comm (M + 3) (dZZ1 (M + 3) u) (dZZ1 (M + 3) v) := by
    intro u v
    rw [dZZ1_mc (M + 2), dZZ1_mc (M + 2)]
    exact boxes_comm ih (tOf_lt u (by omega)) (tOf_lt v (by omega))
  have hinv : ∀ u, Derivable (theory (M + 3)) (drawn [dZZ1 (M + 3) u, dZZ1 (M + 3) u]) 1 := by
    intro u
    rw [dZZ1_mc (M + 2)]
    exact box_inv ih (tOf_lt u (by omega))
  have hB : ∀ (l : List (Circ (M + 3))), (∀ z ∈ l, ∃ k, z = dZZ1 (M + 3) k) →
      ∀ x ∈ l, ∀ y ∈ l, D.Comm (M + 3) x y := by
    intro l hl x hx y hy
    obtain ⟨u, rfl⟩ := hl x hx
    obtain ⟨v, rfl⟩ := hl y hy
    exact hcomm u v
  have hI : ∀ (l : List (Circ (M + 3))), (∀ z ∈ l, ∃ k, z = dZZ1 (M + 3) k) →
      ∀ x ∈ l, Derivable (theory (M + 3)) (drawn [x, x]) 1 := by
    intro l hl x hx
    obtain ⟨u, rfl⟩ := hl x hx
    exact hinv u
  have memB : ∀ (x y : ℕ), ∀ z ∈ zzL (M + 3) x y, ∃ k, z = dZZ1 (M + 3) k :=
    fun x y => isB rfl
  -- the general step: a permutation of `A ++ C ++ C.reverse`
  have step : ∀ (A C L : List (Circ (M + 3))), L.Perm (A ++ C ++ C.reverse) →
      (∀ z ∈ L, ∃ k, z = dZZ1 (M + 3) k) → Derivable (theory (M + 3)) (drawn L) (drawn A) := by
    intro A C L hp hl
    refine (drawn_perm hp (hB L hl)).trans (drawn_cancel A C ?_)
    intro x hx
    exact hI L hl x (hp.symm.subset (by simp [hx]))
  have memApp : ∀ (L1 L2 : List (Circ (M + 3))), (∀ z ∈ L1, ∃ k, z = dZZ1 (M + 3) k) →
      (∀ z ∈ L2, ∃ k, z = dZZ1 (M + 3) k) → ∀ z ∈ L1 ++ L2, ∃ k, z = dZZ1 (M + 3) k := by
    intro L1 L2 h1 h2 z hz
    rcases List.mem_append.1 hz with h | h
    · exact h1 z h
    · exact h2 z h
  have hdeg : ∀ x, Derivable (theory (M + 3)) (dZZ (M + 3) x x * dZZ (M + 3) x x) (dZZ (M + 3) x x) := by
    intro x
    have e : dZZ (M + 3) x x = 1 := by simp [dZZ, drawn]
    rw [e, mul_one]
  rcases le_total a b with hab | hab <;> rcases le_total b c with hbc | hbc <;>
    rcases le_total a c with hac | hac
  · -- a ≤ b ≤ c
    rw [dZZ_zzL hab, dZZ_zzL hbc, dZZ_zzL hac, ← drawn_append, zzL_split hab hbc]
    exact step (zzL (M + 3) a b ++ zzL (M + 3) b c) [] _ (by simpa using List.perm_append_comm)
      (memApp _ _ (memB _ _) (memB _ _))
  · obtain rfl : b = a := by omega
    obtain rfl : c = b := by omega
    exact hdeg c
  · -- a ≤ c ≤ b
    rw [dZZ_zzL hab, dZZ_zzL' hbc, dZZ_zzL hac, ← drawn_append, zzL_split hac hbc]
    exact step (zzL (M + 3) a c) (zzL (M + 3) c b) _
      (by rw [← List.append_assoc]; exact perm_xyx _ _)
      (memApp _ _ (memB _ _) (memApp _ _ (memB _ _) (memB _ _)))
  · -- c ≤ a ≤ b
    rw [dZZ_zzL hab, dZZ_zzL' hbc, dZZ_zzL' hac, ← drawn_append, zzL_split hac hab]
    exact step (zzL (M + 3) c a) (zzL (M + 3) a b) _ (perm_yxx _ _)
      (memApp _ _ (memApp _ _ (memB _ _) (memB _ _)) (memB _ _))
  · -- b ≤ a ≤ c
    rw [dZZ_zzL' hab, dZZ_zzL hbc, dZZ_zzL hac, ← drawn_append, zzL_split hab hac]
    exact step (zzL (M + 3) a c) (zzL (M + 3) b a) _ (perm_xyx _ _)
      (memApp _ _ (memApp _ _ (memB _ _) (memB _ _)) (memB _ _))
  · -- b ≤ c ≤ a
    rw [dZZ_zzL' hab, dZZ_zzL hbc, dZZ_zzL' hac, ← drawn_append, zzL_split hbc hac]
    exact step (zzL (M + 3) c a) (zzL (M + 3) b c) _
      (by rw [← List.append_assoc]; exact perm_xxy _ _)
      (memApp _ _ (memB _ _) (memApp _ _ (memB _ _) (memB _ _)))
  · obtain rfl : b = a := by omega
    obtain rfl : c = b := by omega
    exact hdeg c
  · -- c ≤ b ≤ a
    rw [dZZ_zzL' hab, dZZ_zzL' hbc, dZZ_zzL' hac, ← drawn_append, zzL_split hbc hab]

end QCert.RealCliffordCH.Sec8.E
