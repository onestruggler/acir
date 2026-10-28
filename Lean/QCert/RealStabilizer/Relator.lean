/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Real stabilizer circuits: relators

Every generator `-1`, `H`, `Z`, `CZ` is an involution (R1, R3, R2, R5), so a
word followed by its reverse is the identity (`Holds.inv_cancel`), and an
equation `l = r` can be used in any of the forms the supplement uses: as
its relator `l ++ reverse r = 1`, rotated, reversed and split again into
two sides (`Holds.variant`, computed by `variantEq`).
-/
import QCert.RealStabilizer.Rewrite

namespace QCert.RealStabilizer

open Circuit

/-- A word on the bottom `k` wires. -/
def Bnd (k : ℕ) (l : List Lt) : Prop := ∀ a ∈ l, a.hi ≤ k

instance (k : ℕ) (l : List Lt) : Decidable (Bnd k l) := by unfold Bnd; infer_instance

theorem bnd_append {k : ℕ} {l l' : List Lt} (h : Bnd k l) (h' : Bnd k l') : Bnd k (l ++ l') := by
  intro a ha; rcases List.mem_append.1 ha with ha | ha; exacts [h a ha, h' a ha]

theorem bnd_reverse {k : ℕ} {l : List Lt} (h : Bnd k l) : Bnd k l.reverse :=
  fun a ha => h a (List.mem_reverse.1 ha)

/-- A letter `s` wires up. -/
def Lt.upBy (s : ℕ) : Lt → Lt
  | .neg => .neg
  | .H i => .H (s + i)
  | .Z i => .Z (s + i)
  | .CZ i => .CZ (s + i)

theorem upN_eq : ∀ (s : ℕ) (l : List Lt), upN s l = l.map (Lt.upBy s)
  | 0, l => by
    simp only [upN]
    conv_lhs => rw [← List.map_id l]
    congr 1; funext a; cases a <;> simp [Lt.upBy]
  | s + 1, l => by
    simp only [upN, upN_eq s l, List.map_map]
    congr 1; funext a; cases a <;> simp [Lt.upBy, Lt.up] <;> omega

/-- Each letter is an involution. -/
theorem Holds.sq {k : ℕ} : ∀ a : Lt, a.hi ≤ k → Holds k [a, a] []
  | .neg, _ => (Holds.of_rel Rel.R1 [.neg, .neg] [] rfl rfl (by decide) (by decide)).mono
      (Nat.zero_le _)
  | .H i, h => by
    have := holds_upN (Holds.of_rel Rel.R3 [.H 0, .H 0] [] rfl rfl (by decide) (by decide)) i
    simp only [upN_eq, List.map, Lt.upBy, Nat.add_zero] at this
    exact this.mono (by simp [Lt.hi] at h ⊢; omega)
  | .Z i, h => by
    have := holds_upN (Holds.of_rel Rel.R2 [.Z 0, .Z 0] [] rfl rfl (by decide) (by decide)) i
    simp only [upN_eq, List.map, Lt.upBy, Nat.add_zero] at this
    exact this.mono (by simp [Lt.hi] at h ⊢; omega)
  | .CZ i, h => by
    have := holds_upN (Holds.of_rel Rel.R5 [.CZ 0, .CZ 0] [] rfl rfl (by decide) (by decide)) i
    simp only [upN_eq, List.map, Lt.upBy, Nat.add_zero] at this
    exact this.mono (by simp [Lt.hi] at h ⊢; omega)

/-- A word followed by its reverse is the identity. -/
theorem Holds.inv_cancel {k : ℕ} : ∀ (l : List Lt), Bnd k l → Holds k (l ++ l.reverse) []
  | [], _ => Holds.refl k []
  | a :: l, h => by
    have h1 := Holds.congr [a] [a] (Holds.inv_cancel l (fun b hb => h b (by simp [hb])))
    have h2 := Holds.sq a (h a (by simp))
    simp only [List.reverse_cons, List.cons_append, List.nil_append, List.append_nil,
      List.append_assoc, List.singleton_append] at h1 ⊢
    exact h1.trans h2

theorem Holds.neg_pass {k : ℕ} (u : List Lt) : Holds k (.neg :: u) (u ++ [.neg]) :=
  (allDisj_move (by simp [allDisj, Lt.disj])).mono (Nat.zero_le _)

/-- The scalar moved past a word. -/
theorem Holds.neg_back {k : ℕ} (u : List Lt) : Holds k (u ++ [.neg]) (.neg :: u) :=
  (Holds.neg_pass u).symm

/-- The scalars of a word moved to its end, `(-1)² = 1`. -/
theorem Holds.negs {k : ℕ} : ∀ (w : List Lt),
    Holds k w (w.filter (· ≠ .neg) ++ List.replicate (w.count .neg % 2) .neg)
  | [] => Holds.refl k []
  | a :: w => by
    have ih := Holds.congr [a] [] (Holds.negs (k := k) w)
    simp only [List.nil_append, List.append_nil, List.singleton_append] at ih
    by_cases ha : a = .neg
    · subst ha
      refine ih.trans ((Holds.neg_pass _).trans ?_)
      simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, List.count_cons_self,
        List.append_assoc, cond_false]
      refine Holds.congr (w.filter (· ≠ .neg)) [] ?_ |> fun h => by simpa using h
      rcases Nat.mod_two_eq_zero_or_one (w.count .neg) with h | h
      · rw [h, show (w.count .neg + 1) % 2 = 1 by omega]; exact Holds.refl _ _
      · rw [h, show (w.count .neg + 1) % 2 = 0 by omega]
        exact Holds.sq .neg (Nat.zero_le _)
    · simpa [List.filter_cons, ha, List.count_cons, Ne.symm ha] using ih

/-- From `a ++ b = 1`, `a = reverse b`. -/
theorem Holds.split {k : ℕ} {a b : List Lt} (hb : Bnd k b) (h : Holds k (a ++ b) []) :
    Holds k a b.reverse := by
  have h1 : Holds k a (a ++ (b ++ b.reverse)) := by
    simpa using Holds.congr a [] (Holds.inv_cancel b hb).symm
  have h2 : Holds k (a ++ b ++ b.reverse) b.reverse := by
    simpa using Holds.congr [] b.reverse h
  exact h1.trans (by simpa [List.append_assoc] using h2)

/-- From `a ++ b = 1`, `b ++ a = 1`. -/
theorem Holds.rot {k : ℕ} {a b : List Lt} (ha : Bnd k a) (h : Holds k (a ++ b) []) :
    Holds k (b ++ a) [] := by
  have h1 : Holds k b (a.reverse ++ a ++ b) := by
    have := (Holds.inv_cancel a.reverse (bnd_reverse ha)).symm
    simpa using Holds.congr [] b this
  have h2 : Holds k (a.reverse ++ a ++ b) a.reverse := by
    simpa [List.append_assoc] using Holds.congr a.reverse [] h
  have h3 := (h1.trans h2)
  have h4 := Holds.congr [] a h3
  simp only [List.nil_append] at h4
  have h5 : Holds k (a.reverse ++ a) [] := by
    simpa using Holds.inv_cancel a.reverse (bnd_reverse ha)
  exact h4.trans h5

/-- An equation in the form the supplement uses: the relator `l ++ reverse r`
without its scalars, reversed if `flip = 1`, rotated by `i`, split after `j`
letters; the scalars go to the right. -/
def variantEq (l r : List Lt) (flip i j : ℕ) : List Lt × List Lt :=
  let w := l ++ r.reverse
  let ρ := w.filter (· ≠ .neg)
  let ρ' := if flip = 1 then ρ.reverse else ρ
  let rot := ρ'.drop i ++ ρ'.take i
  (rot.take j, (rot.drop j).reverse ++ List.replicate (w.count .neg % 2) .neg)

theorem bnd_filter {k : ℕ} {l : List Lt} (h : Bnd k l) (p : Lt → Bool) : Bnd k (l.filter p) :=
  fun a ha => h a (List.mem_filter.1 ha).1

theorem bnd_drop {k : ℕ} {l : List Lt} (h : Bnd k l) (i : ℕ) : Bnd k (l.drop i) :=
  fun a ha => h a (List.mem_of_mem_drop ha)

theorem bnd_take {k : ℕ} {l : List Lt} (h : Bnd k l) (i : ℕ) : Bnd k (l.take i) :=
  fun a ha => h a (List.mem_of_mem_take ha)

theorem bnd_rep (k n : ℕ) : Bnd k (List.replicate n Lt.neg) := by
  intro a ha; rw [List.eq_of_mem_replicate ha]; simp [Lt.hi]

/-- **An equation used in another form**: rotated, reversed, split. -/
theorem Holds.variant {k : ℕ} {l r : List Lt} (h : Holds k l r) (hl : Bnd k l) (hr : Bnd k r)
    (flip i j : ℕ) : Holds k (variantEq l r flip i j).1 (variantEq l r flip i j).2 := by
  set w := l ++ r.reverse
  have hw : Bnd k w := bnd_append hl (bnd_reverse hr)
  set p := w.count .neg % 2
  set ρ := w.filter (· ≠ .neg)
  set N := List.replicate p Lt.neg
  have hN : Bnd k N := bnd_rep k p
  have hρ : Bnd k ρ := bnd_filter hw _
  -- the relator is the identity
  have h0 : Holds k w [] := by
    have := Holds.congr [] r.reverse h
    simp only [List.nil_append] at this
    exact this.trans (Holds.inv_cancel r hr)
  have h1 : Holds k (ρ ++ N) [] := (Holds.negs w).symm.trans h0
  -- the scalars commute with everything
  have comm : ∀ u : List Lt, Holds k (N ++ u) (u ++ N) := by
    intro u
    have : ∀ n : ℕ, Holds k (List.replicate n .neg ++ u) (u ++ List.replicate n .neg) := by
      intro n
      induction n with
      | zero => simpa using Holds.refl k u
      | succ n ih =>
        rw [List.replicate_succ, List.cons_append]
        have a1 := Holds.congr [.neg] [] ih
        simp only [List.nil_append, List.append_nil, List.singleton_append] at a1
        refine a1.trans ?_
        have a2 := Holds.neg_pass (k := k) (u ++ List.replicate n .neg)
        refine a2.trans ?_
        simp only [List.append_assoc]
        have a3 := Holds.congr u [] (Holds.neg_pass (k := k) (List.replicate n .neg)).symm
        simp only [List.append_nil] at a3
        simpa [List.replicate_succ'] using a3
    exact this p
  -- reversed if flip = 1
  set ρ' := if flip = 1 then ρ.reverse else ρ
  have hρ' : Bnd k ρ' := by by_cases hf : flip = 1 <;> simp [ρ', hf, hρ, bnd_reverse hρ]
  have h2 : Holds k (ρ' ++ N) [] := by
    by_cases hf : flip = 1
    · simp only [ρ', hf, if_true]
      have r1 : Holds k (N ++ ρ.reverse) [] := by
        have := Holds.split (a := ρ ++ N) (b := []) (by simp [Bnd]) (by simpa using h1)
        have e : (ρ ++ N).reverse = N ++ ρ.reverse := by
          simp [N, List.reverse_replicate]
        have r := Holds.inv_cancel (ρ ++ N).reverse (bnd_reverse (bnd_append hρ hN))
        simp only [List.reverse_reverse] at r
        -- (ρ ++ N).reverse ≈ (ρ ++ N).reverse ++ (ρ ++ N) ≈ []
        have r2 : Holds k ((ρ ++ N).reverse) ((ρ ++ N).reverse ++ (ρ ++ N)) := by
          simpa using Holds.congr (ρ ++ N).reverse [] h1.symm
        rw [← e]; exact r2.trans r
      exact (comm ρ.reverse).symm.trans r1
    · simpa [ρ', hf] using h1
  -- rotated by i
  set rot := ρ'.drop i ++ ρ'.take i
  have h3 : Holds k (rot ++ N) [] := by
    have e : ρ'.take i ++ (ρ'.drop i ++ N) = ρ' ++ N := by
      rw [← List.append_assoc, List.take_append_drop]
    have a := Holds.rot (a := ρ'.take i) (b := ρ'.drop i ++ N) (bnd_take hρ' i) (e ▸ h2)
    have b := Holds.congr (ρ'.drop i) [] (comm (ρ'.take i))
    simp only [List.append_nil, List.append_assoc] at a b
    have e2 : rot ++ N = ρ'.drop i ++ (ρ'.take i ++ N) := by simp [rot, List.append_assoc]
    rw [e2]
    exact b.symm.trans a
  -- split after j
  have h4 := Holds.split (a := rot.take j) (b := rot.drop j ++ N)
    (bnd_append (bnd_drop (bnd_append (bnd_drop hρ' i) (bnd_take hρ' i)) j) hN)
    (by rw [← List.append_assoc, List.take_append_drop]; exact h3)
  have e : (rot.drop j ++ N).reverse = N ++ (rot.drop j).reverse := by
    simp [N, List.reverse_replicate]
  rw [e] at h4
  exact h4.trans (comm _)

/-- `Holds.variant`, with the variant written out (checked by evaluation). -/
theorem Holds.variant' {k : ℕ} {l r l' r' : List Lt} (h : Holds k l r) (hl : Bnd k l)
    (hr : Bnd k r) (flip i j : ℕ) (e : variantEq l r flip i j = (l', r')) : Holds k l' r' := by
  have := h.variant hl hr flip i j
  rw [e] at this
  exact this

/-- An equation from its relator: `l r⁻¹ = 1` (every letter an involution). -/
theorem Holds.of_relator {k : ℕ} {l r : List Lt} (hr : Bnd k r) (h : Holds k (l ++ r.reverse) []) :
    Holds k l r := by
  have := Holds.split (bnd_reverse hr) h
  rwa [List.reverse_reverse] at this

end QCert.RealStabilizer
