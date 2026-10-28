/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# CliffCS₂ on two wires: the decoding at the level of blocks

Bian and Selinger's two-level generators in dimension `4` are decoded as
conjugates of three atoms by permutations of the basis indices `s₀ + 2 s₁`:
`i_[a]` as a conjugate of `cs` (`CS`, which is `i_[3]`), `X_[a,b]` of `t2`
(the CNOT, which is `X_[2,3]`) and `K_[a,b]` of `ck` (the controlled `K`,
which is `K_[2,3]`), by words of the permutation blocks `t0`, `t1`, `t2`,
`x0`, `x1` carrying the indices `2, 3` (or `3`) to the generator's
(`dB`).  This file works with words of blocks modulo the block relations
`brels` (`BRel`), each of which `W2Lemmas` derives from Figure 6:

* two words of permutation blocks with the same permutation are equal
  (`perm_complete`), through the canonical words of `S₄` and the
  certificates of their multiplication table;
* a conjugate of an atom depends only on where the permutation sends the
  atom's indices (`frame`), the permutations fixing them being words in the
  atom's stabiliser letters, which commute with it;
* so the decoding of a generator renamed by a permutation is the decoding of
  the generator conjugated by that permutation (`dec_ok`), and every
  instance of a relation follows from one standard instance (`transport`).
-/
import QCert.Minimality.CliffordCS.W2Data
import QCert.BianSelingerUn.Syntax
import Mathlib.Tactic.FinCases

namespace QCert.Minimality.CliffordCS.W2

open Blk

/-- Words of blocks. -/
abbrev BW := FreeMonoid Blk

instance : DecidableEq BW := inferInstanceAs (DecidableEq (List Blk))

/-- The block relations as axioms. -/
def BRel : WRel Blk := fun a b => (FreeMonoid.toList a, FreeMonoid.toList b) ∈ brels

/-- The block relations as rewriting rules. -/
def rules : List (Rule BRel) := brels.attach.map fun p => ⟨p.1.1, p.1.2, Derivable.of p.2⟩

theorem brel {l r : List Blk} (h : (l, r) ∈ brels := by decide) :
    Derivable BRel (FreeMonoid.ofList l) (FreeMonoid.ofList r) := Derivable.of h

theorem derivable_congr {a a' b b' : BW} (ha : a = a') (hb : b = b')
    (h : Derivable BRel a' b') : Derivable BRel a b := ha ▸ hb ▸ h

/-! ### Permutations -/

/-- The images of `0, 1, 2, 3` under a permutation block. -/
def permOf : Blk → List (Fin 4)
  | t0 => [1, 0, 2, 3]
  | t1 => [0, 2, 1, 3]
  | t2 => [0, 1, 3, 2]
  | x0 => [1, 0, 3, 2]
  | x1 => [2, 3, 0, 1]
  | _ => [0, 1, 2, 3]

/-- The permutation of the basis indices a block realises. -/
def act (b : Blk) (x : Fin 4) : Fin 4 := (permOf b).getD x.val x

/-- The permutation blocks. -/
def isPerm : Blk → Bool
  | t0 | t1 | t2 | x0 | x1 => true
  | _ => false

/-- The permutation of a word of blocks in operator order (the last block
acts first). -/
def actW : List Blk → Fin 4 → Fin 4
  | [] => id
  | b :: u => act b ∘ actW u

/-- The images of `0, 1, 2, 3`. -/
def key (u : List Blk) : List (Fin 4) := [actW u 0, actW u 1, actW u 2, actW u 3]

theorem actW_append (u v : List Blk) : actW (u ++ v) = actW u ∘ actW v := by
  induction u with
  | nil => rfl
  | cons b u ih => simp only [List.cons_append, actW, ih, Function.comp_assoc]

theorem actW_eq_of_key {u v : List Blk} (h : key u = key v) : actW u = actW v := by
  simp only [key, List.cons.injEq, and_true] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  funext x
  fin_cases x
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem key_eq_of_actW {u v : List Blk} (h : actW u = actW v) : key u = key v := by
  simp only [key, h]

theorem act_invol {b : Blk} (hb : isPerm b = true) (x : Fin 4) : act b (act b x) = x := by
  revert x
  cases b <;> simp only [isPerm, Bool.false_eq_true] at hb <;> decide

theorem actW_rev_left : ∀ u : List Blk, u.all isPerm = true → actW u.reverse ∘ actW u = id
  | [], _ => rfl
  | b :: u, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [List.reverse_cons, actW_append]
    funext x
    simp only [Function.comp_apply, actW, id]
    rw [act_invol h.1]
    exact congrFun (actW_rev_left u h.2) x

theorem actW_rev_right (u : List Blk) (h : u.all isPerm = true) :
    actW u ∘ actW u.reverse = id := by
  have h' : u.reverse.all isPerm = true := by simpa [List.all_reverse] using h
  simpa using actW_rev_left u.reverse h'

theorem key_rev {u v : List Blk} (hu : u.all isPerm = true) (hv : v.all isPerm = true)
    (h : key u = key v) : key u.reverse = key v.reverse := by
  apply key_eq_of_actW
  have e := actW_eq_of_key h
  calc actW u.reverse = actW u.reverse ∘ (actW v ∘ actW v.reverse) := by
        rw [actW_rev_right v hv]; rfl
    _ = (actW u.reverse ∘ actW u) ∘ actW v.reverse := by rw [e]; rfl
    _ = actW v.reverse := by rw [actW_rev_left u hu]; rfl

/-! ### Canonical words -/

/-- The canonical word with the permutation of `u`. -/
def canon (u : List Blk) : List Blk := (canonL.find? fun c => key c == key u).getD []

/-- The permutation blocks, listed. -/
def permL : List Blk := [t0, t1, t2, x0, x1]

/-- The certificate for `c ++ [b]`. -/
def certOf (c : List Blk) (b : Blk) : List (ℕ × ℕ × Bool) := (certTable.lookup (c, b)).getD []

theorem canon_congr {u v : List Blk} (h : key u = key v) : canon u = canon v := by
  simp only [canon, h]

theorem canon_step : ∀ c ∈ canonL, ∀ b ∈ permL,
    runSteps rules (c ++ [b]) (certOf c b) = some (canon (c ++ [b])) ∧
      canon (c ++ [b]) ∈ canonL ∧ key (canon (c ++ [b])) = key (c ++ [b]) := by
  decide +kernel

theorem canon_nil : canon [] = [] ∧ ([] : List Blk) ∈ canonL := by decide +kernel

theorem canonL_perm : ∀ c ∈ canonL, c.all isPerm = true := by decide +kernel

theorem mem_permL {b : Blk} (h : isPerm b = true) : b ∈ permL := by
  cases b <;> simp_all [isPerm, permL]

/-- Every word of permutation blocks is equal to its canonical word. -/
theorem perm_canon (u : List Blk) (hu : u.all isPerm = true) :
    Derivable BRel (FreeMonoid.ofList u) (FreeMonoid.ofList (canon u)) ∧
      canon u ∈ canonL ∧ key (canon u) = key u := by
  induction u using List.reverseRecOn with
  | nil =>
    rw [canon_nil.1]
    exact ⟨Derivable.refl _, canon_nil.2, rfl⟩
  | append_singleton u b ih =>
    simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true] at hu
    obtain ⟨d, mem, hk⟩ := ih hu.1
    obtain ⟨h1, h2, h3⟩ := canon_step _ mem b (mem_permL hu.2)
    have hkey : key (canon u ++ [b]) = key (u ++ [b]) := by
      apply key_eq_of_actW
      rw [actW_append, actW_append, actW_eq_of_key hk]
    have hc : canon (canon u ++ [b]) = canon (u ++ [b]) := canon_congr hkey
    refine ⟨?_, hc ▸ h2, hc ▸ h3.trans hkey⟩
    have e1 : Derivable BRel (FreeMonoid.ofList (u ++ [b]))
        (FreeMonoid.ofList (canon u ++ [b])) := by
      rw [FreeMonoid.ofList_append, FreeMonoid.ofList_append]
      exact d.mul (Derivable.refl _)
    have e2 := derivable_of_runSteps' rules h1
    rw [hc] at e2
    exact e1.trans e2

/-- Two words of permutation blocks with the same permutation are equal. -/
theorem perm_complete {u v : List Blk} (hu : u.all isPerm = true) (hv : v.all isPerm = true)
    (h : key u = key v) : Derivable BRel (FreeMonoid.ofList u) (FreeMonoid.ofList v) := by
  have du := (perm_canon u hu).1
  have dv := (perm_canon v hv).1
  rw [canon_congr h] at du
  exact du.trans dv.symm

theorem inv_cancel {u : List Blk} (hu : u.all isPerm = true) :
    Derivable BRel (FreeMonoid.ofList u * FreeMonoid.ofList u.reverse) 1 := by
  rw [← FreeMonoid.ofList_append, ← FreeMonoid.ofList_nil]
  refine perm_complete (by simp [List.all_append, List.all_reverse, hu]) rfl ?_
  apply key_eq_of_actW
  rw [actW_append, actW_rev_right u hu]
  rfl

theorem inv_cancel' {u : List Blk} (hu : u.all isPerm = true) :
    Derivable BRel (FreeMonoid.ofList u.reverse * FreeMonoid.ofList u) 1 := by
  have h' : u.reverse.all isPerm = true := by simpa [List.all_reverse] using hu
  simpa using inv_cancel h'

/-! ### Conjugates of the atoms -/

/-- `R A R⁻¹`: the atom `A` conjugated by the permutation word `R`. -/
def conj (R : List Blk) (A : Blk) : BW :=
  FreeMonoid.ofList R * FreeMonoid.of A * FreeMonoid.ofList R.reverse

/-- Where the conjugating permutations must agree: on the index `3` for
`cs`, on `2` and `3` for `ck`, on the set `{2, 3}` for `t2`. -/
def baseOK : Blk → List (Fin 4) → List (Fin 4) → Bool
  | cs, k, k' => k.getD 3 0 == k'.getD 3 0
  | ck, k, k' => k.getD 2 0 == k'.getD 2 0 && k.getD 3 0 == k'.getD 3 0
  | t2, k, k' => (k.getD 2 0 == k'.getD 2 0 && k.getD 3 0 == k'.getD 3 0) ||
      (k.getD 2 0 == k'.getD 3 0 && k.getD 3 0 == k'.getD 2 0)
  | _, _, _ => false

/-- The stabiliser letters of an atom. -/
def stabL : Blk → List Blk
  | cs => [t0, t1]
  | ck => [t0]
  | t2 => [t0, t2]
  | _ => []

/-- A word in the stabiliser letters of `A` with the permutation `k`. -/
def stabW (A : Blk) (k : List (Fin 4)) : List Blk := ((stabTable A).lookup k).getD []

/-- The atoms. -/
def atoms : List Blk := [cs, ck, t2]

theorem frame_dec : ∀ A ∈ atoms, ∀ c ∈ canonL, ∀ c' ∈ canonL, baseOK A (key c) (key c') = true →
    (stabW A (key (c.reverse ++ c'))).all (stabL A).contains = true ∧
      key (c ++ stabW A (key (c.reverse ++ c'))) = key c' := by
  decide +kernel

theorem stabL_perm : ∀ A ∈ atoms, (stabL A).all isPerm = true := by decide +kernel

theorem stab_letter : ∀ A ∈ atoms, ∀ b ∈ stabL A,
    Derivable BRel (FreeMonoid.of b * FreeMonoid.of A) (FreeMonoid.of A * FreeMonoid.of b) := by
  intro A hA b hb
  simp only [atoms, List.mem_cons, List.not_mem_nil, or_false] at hA
  rcases hA with rfl | rfl | rfl <;> simp only [stabL, List.mem_cons, List.not_mem_nil,
    or_false] at hb
  · rcases hb with rfl | rfl
    · exact brel (l := [t0, cs]) (r := [cs, t0])
    · exact brel (l := [t1, cs]) (r := [cs, t1])
  · rcases hb with rfl
    exact brel (l := [t0, ck]) (r := [ck, t0])
  · rcases hb with rfl | rfl
    · exact brel (l := [t0, t2]) (r := [t2, t0])
    · exact Derivable.refl _

theorem stab_comm {A : Blk} (hA : A ∈ atoms) :
    ∀ V : List Blk, V.all (stabL A).contains = true →
      Derivable BRel (FreeMonoid.ofList V * FreeMonoid.of A)
        (FreeMonoid.of A * FreeMonoid.ofList V)
  | [], _ => by
    simp only [FreeMonoid.ofList_nil, one_mul, mul_one]
    exact Derivable.refl _
  | b :: V, h => by
    simp only [List.all_cons, Bool.and_eq_true, List.contains_iff_mem] at h
    have ih := stab_comm hA V h.2
    rw [FreeMonoid.ofList_cons, mul_assoc]
    refine ((Derivable.refl _).mul ih).trans ?_
    rw [← mul_assoc, ← mul_assoc]
    exact (stab_letter A hA b (by simpa using h.1)).mul (Derivable.refl _)

theorem all_perm_of_stab {A : Blk} (hA : A ∈ atoms) {V : List Blk}
    (h : V.all (stabL A).contains = true) : V.all isPerm = true := by
  rw [List.all_eq_true] at h ⊢
  intro b hb
  have hs := stabL_perm A hA
  rw [List.all_eq_true] at hs
  exact hs b (by simpa using h b hb)

/-- The conjugate of an atom by two permutation words with the same permutation. -/
theorem conj_perm {R R' : List Blk} (hR : R.all isPerm = true) (hR' : R'.all isPerm = true)
    (h : key R = key R') (A : Blk) : Derivable BRel (conj R A) (conj R' A) :=
  ((perm_complete hR hR' h).mul (Derivable.refl _)).mul
    (perm_complete (by simpa [List.all_reverse] using hR) (by simpa [List.all_reverse] using hR')
      (key_rev hR hR' h))

theorem conj_append (P Q : List Blk) (A : Blk) :
    FreeMonoid.ofList P * conj Q A * FreeMonoid.ofList P.reverse = conj (P ++ Q) A := by
  simp only [conj, List.reverse_append, FreeMonoid.ofList_append, mul_assoc]

theorem frame_canon {A : Blk} (hA : A ∈ atoms) {c c' : List Blk} (hc : c ∈ canonL)
    (hc' : c' ∈ canonL) (h : baseOK A (key c) (key c') = true) :
    Derivable BRel (conj c A) (conj c' A) := by
  obtain ⟨hV, hk⟩ := frame_dec A hA c hc c' hc' h
  set V := stabW A (key (c.reverse ++ c'))
  have pc := canonL_perm c hc
  have pV := all_perm_of_stab hA hV
  have pcV : (c ++ V).all isPerm = true := by simp [List.all_append, pc, pV]
  refine Derivable.trans ?_ (conj_perm pcV (canonL_perm c' hc') hk A)
  -- c A c⁻¹ ~ c V A V⁻¹ c⁻¹
  have e : conj (c ++ V) A = FreeMonoid.ofList c *
      ((FreeMonoid.ofList V * FreeMonoid.of A) * FreeMonoid.ofList V.reverse) *
        FreeMonoid.ofList c.reverse := by
    simp only [conj, List.reverse_append, FreeMonoid.ofList_append, mul_assoc]
  rw [e]
  have step : Derivable BRel
      ((FreeMonoid.ofList V * FreeMonoid.of A) * FreeMonoid.ofList V.reverse)
      (FreeMonoid.of A) := by
    refine ((stab_comm hA V hV).mul (Derivable.refl _)).trans ?_
    rw [mul_assoc]
    refine ((Derivable.refl _).mul (inv_cancel pV)).trans ?_
    rw [mul_one]
  exact (((Derivable.refl _).mul step).mul (Derivable.refl _)).symm

/-- A conjugate of an atom depends only on where the permutation sends the
atom's indices. -/
theorem frame {A : Blk} (hA : A ∈ atoms) {R R' : List Blk} (hR : R.all isPerm = true)
    (hR' : R'.all isPerm = true) (h : baseOK A (key R) (key R') = true) :
    Derivable BRel (conj R A) (conj R' A) := by
  obtain ⟨_, m, k⟩ := perm_canon R hR
  obtain ⟨_, m', k'⟩ := perm_canon R' hR'
  refine (conj_perm hR (canonL_perm _ m) k.symm A).trans ?_
  refine Derivable.trans ?_ (conj_perm (canonL_perm _ m') hR' k' A)
  exact frame_canon hA m m' (by rw [k, k']; exact h)

/-- A conjugate of an atom passes a permutation word, renamed by it. -/
theorem swap_conj {A : Blk} (hA : A ∈ atoms) {R W R' : List Blk} (hR : R.all isPerm = true)
    (hW : W.all isPerm = true) (hR' : R'.all isPerm = true)
    (h : baseOK A (key (W.reverse ++ R)) (key R') = true) :
    Derivable BRel (conj R A * FreeMonoid.ofList W) (FreeMonoid.ofList W * conj R' A) := by
  have pWR : (W.reverse ++ R).all isPerm = true := by
    simp [List.all_append, List.all_reverse, hR, hW]
  have e1 : Derivable BRel (conj R A * FreeMonoid.ofList W)
      (FreeMonoid.ofList W * FreeMonoid.ofList W.reverse * (conj R A * FreeMonoid.ofList W)) := by
    have := (inv_cancel hW).symm.mul (Derivable.refl (conj R A * FreeMonoid.ofList W))
    rw [one_mul] at this
    exact this
  have e2 : FreeMonoid.ofList W * FreeMonoid.ofList W.reverse * (conj R A * FreeMonoid.ofList W) =
      FreeMonoid.ofList W * conj (W.reverse ++ R) A := by
    rw [← conj_append, List.reverse_reverse]
    simp only [mul_assoc]
  rw [e2] at e1
  exact e1.trans ((Derivable.refl _).mul (frame hA pWR hR' h))

/-! ### The decoding -/

open QCert.BianSelingerUn in
/-- The permutation word carrying `3` to the index of `i_[a]`. -/
def Qi (a : Fin 4) : List Blk :=
  match a.val with
  | 0 => [x1, x0]
  | 1 => [x1]
  | 2 => [x0]
  | _ => []

/-- The permutation word carrying `2, 3` to `a, b` (for `a < b`). -/
def Qp (a b : Fin 4) : List Blk :=
  match a.val, b.val with
  | 0, 1 => [x1]
  | 0, 2 => [t1, x1]
  | 0, 3 => [t0, t1]
  | 1, 2 => [t2, t1]
  | 1, 3 => [t1]
  | _, _ => []

/-- The atom of a generator. -/
def atomOf : QCert.BianSelingerUn.Gen 4 → Blk
  | .X .. => t2
  | .K .. => ck
  | .i _ => cs

/-- The conjugating word of a generator. -/
def Qof : QCert.BianSelingerUn.Gen 4 → List Blk
  | .X a b _ => Qp a b
  | .K a b _ => Qp a b
  | .i a => Qi a

/-- The decoding of the refined generators as blocks: the new scalar as `ω`,
a generator as its atom conjugated by its word. -/
def dB : Option (QCert.BianSelingerUn.Gen 4) → BW
  | none => FreeMonoid.of w
  | some g => conj (Qof g) (atomOf g)

/-- The decoding of refined words. -/
def DB : FreeMonoid (Option (QCert.BianSelingerUn.Gen 4)) →* BW := FreeMonoid.lift dB

/-- The decoding of a list of generators. -/
def DBs (l : List (QCert.BianSelingerUn.Gen 4)) : BW := DB (FreeMonoid.ofList (l.map some))

theorem DBs_nil : DBs [] = 1 := rfl

theorem DBs_cons (g : QCert.BianSelingerUn.Gen 4) (l : List (QCert.BianSelingerUn.Gen 4)) :
    DBs (g :: l) = dB (some g) * DBs l := by
  simp only [DBs, List.map_cons, FreeMonoid.ofList_cons, map_mul, DB, FreeMonoid.lift_eval_of]

theorem Q_perm : (∀ a : Fin 4, (Qi a).all isPerm = true) ∧
    ∀ a b : Fin 4, (Qp a b).all isPerm = true := by decide +kernel

theorem Qof_perm (g : QCert.BianSelingerUn.Gen 4) : (Qof g).all isPerm = true := by
  cases g with
  | X a b _ => exact Q_perm.2 a b
  | K a b _ => exact Q_perm.2 a b
  | i a => exact Q_perm.1 a

theorem atomOf_mem (g : QCert.BianSelingerUn.Gen 4) : atomOf g ∈ atoms := by
  cases g <;> simp [atomOf, atoms]

/-- `g` is `g0` renamed by the permutation `P` (as far as the decoding sees). -/
def okG (P : List Blk) (g0 g : QCert.BianSelingerUn.Gen 4) : Bool :=
  atomOf g0 == atomOf g && baseOK (atomOf g0) (key (P ++ Qof g0)) (key (Qof g))

theorem dec_ok {P : List Blk} (hP : P.all isPerm = true) {g0 g : QCert.BianSelingerUn.Gen 4}
    (h : okG P g0 g = true) :
    Derivable BRel (dB (some g)) (FreeMonoid.ofList P * dB (some g0) * FreeMonoid.ofList P.reverse) := by
  simp only [okG, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨ha, hb⟩ := h
  simp only [dB]
  rw [conj_append, ← ha]
  have pP : (P ++ Qof g0).all isPerm = true := by simp [List.all_append, hP, Qof_perm]
  exact (frame (atomOf_mem g0) pP (Qof_perm g) hb).symm

/-- `l` is `l0` renamed by `P`, letter by letter. -/
def allOk (P : List Blk) : List (QCert.BianSelingerUn.Gen 4) → List (QCert.BianSelingerUn.Gen 4) → Bool
  | [], [] => true
  | g0 :: l0, g :: l => okG P g0 g && allOk P l0 l
  | _, _ => false

theorem DBs_ok {P : List Blk} (hP : P.all isPerm = true) :
    ∀ l0 l, allOk P l0 l = true →
      Derivable BRel (DBs l) (FreeMonoid.ofList P * DBs l0 * FreeMonoid.ofList P.reverse)
  | [], [], _ => by
    rw [DBs_nil, mul_one]
    exact (inv_cancel hP).symm
  | g0 :: l0, g :: l, h => by
    simp only [allOk, Bool.and_eq_true] at h
    rw [DBs_cons, DBs_cons]
    refine ((dec_ok hP h.1).mul (DBs_ok hP l0 l h.2)).trans ?_
    have e : FreeMonoid.ofList P * dB (some g0) * FreeMonoid.ofList P.reverse *
        (FreeMonoid.ofList P * DBs l0 * FreeMonoid.ofList P.reverse) =
        FreeMonoid.ofList P * dB (some g0) *
          (FreeMonoid.ofList P.reverse * FreeMonoid.ofList P) * DBs l0 *
            FreeMonoid.ofList P.reverse := by
      simp only [mul_assoc]
    rw [e]
    have := ((((Derivable.refl (FreeMonoid.ofList P * dB (some g0))).mul (inv_cancel' hP)).mul
      (Derivable.refl (DBs l0))).mul (Derivable.refl (FreeMonoid.ofList P.reverse)))
    simpa only [mul_one, mul_assoc] using this
  | [], _ :: _, h => by simp [allOk] at h
  | _ :: _, [], h => by simp [allOk] at h

/-- Every instance of a relation follows from its standard instance, when the
instance is the standard one renamed by a permutation. -/
theorem transport (P : List Blk) (hP : P.all isPerm = true) (l0 l r0 r : List (QCert.BianSelingerUn.Gen 4))
    (hl : allOk P l0 l = true) (hr : allOk P r0 r = true)
    (h : Derivable BRel (DBs l0) (DBs r0)) : Derivable BRel (DBs l) (DBs r) :=
  (DBs_ok hP l0 l hl).trans ((((Derivable.refl _).mul h).mul (Derivable.refl _)).trans
    (DBs_ok hP r0 r hr).symm)

/-- The canonical word carrying the indices `std` to `targets`. -/
def Pw (std targets : List (Fin 4)) : List Blk :=
  (canonL.find? fun c => (std.zip targets).all fun st => actW c st.1 == st.2).getD []

theorem Pw_perm (std targets : List (Fin 4)) : (Pw std targets).all isPerm = true := by
  unfold Pw
  cases h : canonL.find? (fun c => (std.zip targets).all fun st => actW c st.1 == st.2) with
  | none => rfl
  | some c => exact canonL_perm c (List.mem_of_find?_eq_some h)

/-- The scalar commutes with every word of blocks. -/
theorem w_comm : ∀ u : List Blk,
    Derivable BRel (FreeMonoid.of w * FreeMonoid.ofList u) (FreeMonoid.ofList u * FreeMonoid.of w)
  | [] => by
    simp only [FreeMonoid.ofList_nil, one_mul, mul_one]
    exact Derivable.refl _
  | b :: u => by
    rw [FreeMonoid.ofList_cons, ← mul_assoc]
    have hb : Derivable BRel (FreeMonoid.of w * FreeMonoid.of b) (FreeMonoid.of b * FreeMonoid.of w) := by
      cases b
      all_goals first
        | exact Derivable.refl _
        | exact brel (l := [w, _]) (r := [_, w])
    refine (hb.mul (Derivable.refl _)).trans ?_
    rw [mul_assoc, mul_assoc]
    exact (Derivable.refl _).mul (w_comm u)

end QCert.Minimality.CliffordCS.W2
