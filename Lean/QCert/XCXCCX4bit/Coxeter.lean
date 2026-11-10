/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Permutations of `N` basis states as circuits, and the frame lemma

Translation of `Coxeter.agda`: `Examples.Groups.Symmetric.CoxeterFrames` for
any number `N` of states.  A Coxeter word (`CW N`, a word of `S_N`'s
presentation, `Lib/Symmetric`) is read with `T d` for its letter `s_d` on
the states `d, d + 1` (`Circuits.Pc`), `T d` circuits over any alphabet.
Given the Coxeter relations for the circuits `T d` (`Coxeter`), the
relations of `S_N` hold for the circuits (`Pc_cong`), two Coxeter words with
the same permutation have equivalent circuits (`perm_complete`), and a
circuit that the `T i` with `i ≥ j` commute with, conjugated by a Coxeter
word, depends only on where the word sends the states below `j`
(`frame_eq`, the Agda's `frame≈`).  The width-independent part (actions,
inverses, lifts, frames) is the Agda `CoxeterFrames`' own, here
`Lib/Symmetric` and the first section below; `frame ts` sends the states
`0, 1, …` to the distinct states `ts` (`frame_act`).

**Deviation from the Agda.**  Coxeter words are words over the letters
`SG N = {d // 2 + d ≤ N}` of `Lib/Symmetric` rather than circuits of the
Agda's presentation of `S_N`; the Agda's `tr o g` is `o + g.1`.  The
completeness of that presentation, `stab` and the frame lemma come from the
general part of `QCert.ToffoliHadamardRS.CoxeterFrames` (Coxeter words as
`List ℕ`, through `Symmetric.toL`), read in the quotient monoid of the
theory; so the Agda's `stripN`, `strip-ok`, `liftW`, `⟦liftW⟧`, `cyc` and
`outs`, which only its proof of `stab` uses, are not reproduced.
`Distinct ts` is `ts.Nodup` and `Avoid t ts` is `t ∉ ts`; `frame ts` is
total (the Agda's takes the proof of distinctness), and only `frame_act`
asks for distinctness.  The Agda's `xs ‼ i` is `xs[i]?`.  Words are
multiplied left-associatively (`Fr T b p = Pc T 0 p * b * Pc T 0 (inv p)`,
where the Agda brackets to the right), which matters only up to
`mul_assoc`.  `Fr_conj` holds as an equation of words.
-/
import QCert.XCXCCX4bit.Lib.Symmetric
import Mathlib.GroupTheory.Perm.Sign

namespace QCert.XCXCCX4bit.Coxeter

open QCert.ToffoliHadamardRS
open Symmetric

export Symmetric (SG tr tr_ge tr_le inv inv_of inv_one inv_mul inv_inv act act_one act_of
  act_mul act_inv act_inv' perm perm_apply perm_symm_apply perm_of perm_mul perm_mul_apply
  l_to_r perm_eq_iff_act)

variable {n : ℕ}

/-- Words of `S_N`'s presentation. -/
abbrev CW (N : ℕ) := Word (SG N)

/-! ## Lifted permutations -/

/-- The function of `liftN j ρ`. -/
def liftNFun (j : ℕ) {m : ℕ} (ρ : Equiv.Perm (Fin m)) (i : Fin (j + m)) : Fin (j + m) :=
  if h : i.1 < j then i else Fin.natAdd j (ρ ⟨i.1 - j, by omega⟩)

theorem liftNFun_inv (j : ℕ) {m : ℕ} (ρ : Equiv.Perm (Fin m)) (i : Fin (j + m)) :
    liftNFun j ρ.symm (liftNFun j ρ i) = i := by
  unfold liftNFun
  by_cases h : i.1 < j
  · simp [h]
  · simp only [h, dite_false, Fin.natAdd, Fin.val_mk]
    ext; simp; omega

/-- A permutation of `m` states lifted over `j` fixed states below it (the
Agda's `liftN`, iterated `lift₀`). -/
def liftN (j : ℕ) {m : ℕ} (ρ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (j + m)) where
  toFun := liftNFun j ρ
  invFun := liftNFun j ρ.symm
  left_inv := liftNFun_inv j ρ
  right_inv i := by simpa using liftNFun_inv j ρ.symm i

theorem liftN_lo (j : ℕ) {m : ℕ} (ρ : Equiv.Perm (Fin m)) (i : Fin (j + m)) (h : i.1 < j) :
    liftN j ρ i = i := by
  show liftNFun j ρ i = i; simp [liftNFun, h]

theorem liftN_natAdd (j : ℕ) {m : ℕ} (ρ : Equiv.Perm (Fin m)) (k : Fin m) :
    liftN j ρ (Fin.natAdd j k) = Fin.natAdd j (ρ k) := by
  show liftNFun j ρ _ = _
  simp [liftNFun]

theorem liftN_cong (j : ℕ) {m : ℕ} (π ρ : Equiv.Perm (Fin m)) (h : ∀ i, π i = ρ i) :
    ∀ i, liftN j π i = liftN j ρ i := by
  rw [Equiv.ext h]; intro; rfl

/-- `liftN j ρ` is `ρ` extended to the states from `j` on. -/
theorem liftN_eq_extendDomain (j : ℕ) {m : ℕ} (ρ : Equiv.Perm (Fin m)) :
    liftN j ρ = ρ.extendDomain
      ({ toFun := fun k => ⟨Fin.natAdd j k, by simp⟩
         invFun := fun i => ⟨i.1.1 - j, by have := i.1.2; have := i.2; omega⟩
         left_inv := fun k => by ext; simp
         right_inv := fun i => by ext; simp; have := i.2; omega } :
        Fin m ≃ {i : Fin (j + m) // j ≤ i.1}) := by
  refine Equiv.ext fun i => ?_
  by_cases h : j ≤ i.1
  · rw [Equiv.Perm.extendDomain_apply_subtype (b := i) _ _ h]
    apply Fin.ext
    show (liftNFun j ρ i).1 = _
    simp [liftNFun, show ¬ i.1 < j by omega]
  · rw [Equiv.Perm.extendDomain_apply_not_subtype (b := i) _ _ h, liftN_lo j ρ i (by omega)]

/-! ## Frames -/

/-- Distinct states (the Agda's `Distinct`). -/
abbrev Distinct (xs : List (Fin n)) : Prop := xs.Nodup

/-- A list of states avoiding a state (the Agda's `Avoid`). -/
abbrev Avoid (t : Fin n) (xs : List (Fin n)) : Prop := t ∉ xs

theorem frame_bound (ts : List (Fin n)) (d : Distinct ts) :
    ∀ e ∈ CoxeterFrames.frame (ts.map Fin.val), 2 + e ≤ n := by
  intro e he
  rcases n with _ | n
  · cases ts with
    | nil => simp [CoxeterFrames.frame_nil] at he
    | cons t _ => exact t.elim0
  · have := CoxeterFrames.frame_valid n (ts.map Fin.val)
      (d.map_on fun x _ y _ h => Fin.ext h)
      (by intro t ht; obtain ⟨x, -, rfl⟩ := List.mem_map.1 ht; exact x.2) e he
    omega

/-- `frame ts` sends the state `i` to the `i`-th entry of `ts`: the frame
normal form of `CoxeterFrames` (`cyc` of the head, followed one wire up by
the frame of the rest punched out at the head). -/
def frame (ts : List (Fin n)) : Word (SG n) := ofL n (CoxeterFrames.frame (ts.map Fin.val))

theorem toL_frame (ts : List (Fin n)) (d : Distinct ts) :
    toL (frame ts) = CoxeterFrames.frame (ts.map Fin.val) :=
  toL_ofL _ (frame_bound ts d)

/-- The Agda's `frame-act`. -/
theorem frame_act (ts : List (Fin n)) (d : Distinct ts) (i x : Fin n) (h : ts[i.1]? = some x) :
    act (frame ts) i = x := by
  apply Fin.ext
  rw [act_val, toL_frame ts d]
  exact CoxeterFrames.frame_act' _ (d.map_on fun x _ y _ h => Fin.ext h) i.1 x.1
    (by rw [List.getElem?_map, h]; rfl)

/-! ## Coxeter words as circuits -/

namespace Circuits

variable {A : Type*} (T : ℕ → Word A)

/-- A Coxeter word read as a circuit, its states shifted up by `o`. -/
def Pc (o : ℕ) {n : ℕ} : Word (SG n) →* Word A := FreeMonoid.lift fun g => T (tr o g)

@[simp] theorem Pc_of (o : ℕ) (g : SG n) : Pc T o (FreeMonoid.of g) = T (o + g.1) := rfl

theorem Pc_zero_of (g : SG n) : Pc T 0 (FreeMonoid.of g) = T g.1 := by
  rw [Pc_of, Nat.zero_add]

theorem Pc_mul (o : ℕ) (u v : Word (SG n)) : Pc T o (u * v) = Pc T o u * Pc T o v := map_mul _ u v

theorem Pc_one (o : ℕ) : Pc T o (1 : Word (SG n)) = 1 := map_one _

/-- The Coxeter relations for the circuits `T d`, `d + 1 < N`. -/
structure Coxeter (N : ℕ) (T : ℕ → Word A) (Γ : WRel A) : Prop where
  order : ∀ i, 2 + i ≤ N → Derivable Γ (T i * T i) 1
  braid : ∀ i, 3 + i ≤ N → Derivable Γ (T i * T (i + 1) * T i) (T (i + 1) * T i * T (i + 1))
  far : ∀ i j, 2 + i ≤ j → 2 + j ≤ N → Derivable Γ (T i * T j) (T j * T i)

variable {T} {N : ℕ} {Γ : WRel A}

/-! ### Transfer of the relations of `S_N` -/

/-- The relations of `S_n` read `o` states up hold for the circuits (the
Agda's `Transfer.Pc-ax`). -/
theorem Pc_ax (cox : Coxeter N T Γ) {u v : Word (SG n)} (o : ℕ) (b : o + n ≤ N)
    (h : SymRel n u v) : Derivable Γ (Pc T o u) (Pc T o v) := by
  cases h with
  | order d q => exact cox.order (o + d) (by omega)
  | braid d q => exact cox.braid (o + d) (by omega)
  | far d e lo q => exact cox.far (o + d) (o + e) (by omega) (by omega)

/-- The congruence of the relations of `S_n` read `o` states up (the
Agda's `Pc-cong`). -/
theorem Pc_cong (cox : Coxeter N T Γ) {u v : Word (SG n)} (o : ℕ) (b : o + n ≤ N)
    (h : Derivable (SymRel n) u v) : Derivable Γ (Pc T o u) (Pc T o v) := by
  let c : Con (Word (SG n)) :=
    { r := fun u v => Derivable Γ (Pc T o u) (Pc T o v)
      iseqv := ⟨fun _ => Derivable.refl _, Derivable.symm, Derivable.trans⟩
      mul' := fun hu hv => by rw [Pc_mul, Pc_mul]; exact hu.mul hv }
  have : conGen (SymRel n) ≤ c := Con.conGen_le fun _ _ hab => Pc_ax cox o b hab
  exact this h

/-! ### Completeness for permutations, inverses, frames and stabilisers -/

/-- Two Coxeter words with the same permutation are equal circuits. -/
theorem perm_complete' (cox : Coxeter N T Γ) (hn : n ≤ N) (p q : Word (SG n))
    (h : ∀ i, perm p i = perm q i) : Derivable Γ (Pc T 0 p) (Pc T 0 q) :=
  Pc_cong cox 0 (by omega) (Symmetric.complete h)

theorem perm_complete (cox : Coxeter N T Γ) (p q : CW N) (h : ∀ x, act p x = act q x) :
    Derivable Γ (Pc T 0 p) (Pc T 0 q) :=
  perm_complete' cox le_rfl p q ((perm_eq_iff_act p q).2 h)

/-- A Coxeter word followed by its inverse. -/
theorem Pc_inv (cox : Coxeter N T Γ) (o : ℕ) (b : o + n ≤ N) (p : Word (SG n)) :
    Derivable Γ (Pc T o p * Pc T o (inv p)) 1 := by
  rw [← Pc_mul, ← Pc_one T o]
  exact Pc_cong cox o b (Symmetric.complete fun i => by
    rw [perm_mul_apply, perm_apply (inv p), inv_inv, perm_apply p, act_inv']; rfl)

theorem Pc_inv' (cox : Coxeter N T Γ) (o : ℕ) (b : o + n ≤ N) (p : Word (SG n)) :
    Derivable Γ (Pc T o (inv p) * Pc T o p) 1 := by
  have := Pc_inv cox o b (inv p); rwa [inv_inv] at this

variable (T) in
/-- A circuit conjugated by a Coxeter word. -/
def Fr (b : Word A) (p : CW N) : Word A := Pc T 0 p * b * Pc T 0 (inv p)

theorem Fr_conj (b : Word A) (r p : CW N) :
    Pc T 0 r * Fr T b p * Pc T 0 (inv r) = Fr T b (r * p) := by
  simp only [Fr, inv_mul, map_mul, mul_assoc]

/-- Circuits that every `T i` with `i ≥ j` commutes with (the Agda's
`Comm≥`). -/
def CommGe (N : ℕ) (T : ℕ → Word A) (Γ : WRel A) (j : ℕ) (b : Word A) : Prop :=
  ∀ i, j ≤ i → 2 + i ≤ N → Derivable Γ (T i * b) (b * T i)

theorem comm_word {j m : ℕ} (b : Word A) (cb : CommGe N T Γ j b) (bd : j + m ≤ N)
    (w : Word (SG m)) : Derivable Γ (Pc T j w * b) (b * Pc T j w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => rw [map_one, one_mul, mul_one]
  | mul_of g w ih =>
    have hg := cb (j + g.1) (by omega) (by have := g.2; omega)
    rw [map_mul, Pc_of, mul_assoc]
    refine ((Derivable.refl _).mul ih).trans ?_
    rw [← mul_assoc, ← mul_assoc]
    exact hg.mul (Derivable.refl _)

/-! ### Through the quotient monoid -/

theorem coxRel (cox : Coxeter N T Γ) :
    CoxeterFrames.CoxRel (fun i => CoxeterFrames.cl Γ (T i)) (N - 1) where
  order i hi := by
    rw [← CoxeterFrames.cl_mul, ← CoxeterFrames.cl_one]
    exact CoxeterFrames.cl_eq.2 (cox.order i (by omega))
  braid i hi := by
    simp only [← CoxeterFrames.cl_mul]
    exact CoxeterFrames.cl_eq.2 (cox.braid i (by omega))
  far i j hij hj := by
    simp only [← CoxeterFrames.cl_mul]
    exact CoxeterFrames.cl_eq.2 (cox.far i j (by omega) (by omega))

theorem cl_Pc (w : Word (SG n)) :
    CoxeterFrames.cl Γ (Pc T 0 w) = CoxeterFrames.ev (fun i => CoxeterFrames.cl Γ (T i)) (toL w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => exact CoxeterFrames.cl_one
  | mul_of g w ih =>
    rw [map_mul, CoxeterFrames.cl_mul, ih, toL_mul, toL_of, List.singleton_append,
      CoxeterFrames.ev_cons, Pc_zero_of]

/-- A Coxeter word fixing the states below `j` commutes with `b` (the Agda's
`stab`). -/
theorem stab (cox : Coxeter N T Γ) (j m : ℕ) (bd : j + m ≤ N) (b : Word A)
    (cb : CommGe N T Γ j b) (r : Word (SG (j + m)))
    (fix : ∀ x : Fin (j + m), x.1 < j → act r x = x) :
    Derivable Γ (Pc T 0 r * b) (b * Pc T 0 r) := by
  apply CoxeterFrames.cl_eq.1
  rw [CoxeterFrames.cl_mul, CoxeterFrames.cl_mul, cl_Pc]
  refine CoxeterFrames.stab (N := j + m - 1) (j := j) ((coxRel cox).mono (by omega)) (by omega)
    (fun i hi hi' => ?_) (valid_toL r) (fun x hx => ?_)
  · show CoxeterFrames.cl Γ (T i) * CoxeterFrames.cl Γ b = CoxeterFrames.cl Γ b * CoxeterFrames.cl Γ (T i)
    simp only [← CoxeterFrames.cl_mul]
    exact CoxeterFrames.cl_eq.2 (cb i hi (by omega))
  · have := congrArg Fin.val (fix ⟨x, by omega⟩ hx)
    rwa [act_val] at this

/-- Frames: `b` conjugated by two Coxeter words that agree below `j` (the
Agda's `frame≈`). -/
theorem frame_eq (cox : Coxeter N T Γ) (j m : ℕ) (bd : j + m ≤ N) (b : Word A)
    (cb : CommGe N T Γ j b) (p q : Word (SG (j + m)))
    (h : ∀ x : Fin (j + m), x.1 < j → act p x = act q x) :
    Derivable Γ (Pc T 0 p * b * Pc T 0 (inv p)) (Pc T 0 q * b * Pc T 0 (inv q)) := by
  apply CoxeterFrames.cl_eq.1
  simp only [CoxeterFrames.cl_mul, cl_Pc, toL_inv]
  refine CoxeterFrames.frame_eq (N := j + m - 1) (j := j) ((coxRel cox).mono (by omega)) (by omega)
    (fun i hi hi' => ?_) (valid_toL p) (valid_toL q) (fun x hx => ?_)
  · show CoxeterFrames.cl Γ (T i) * CoxeterFrames.cl Γ b = CoxeterFrames.cl Γ b * CoxeterFrames.cl Γ (T i)
    simp only [← CoxeterFrames.cl_mul]
    exact CoxeterFrames.cl_eq.2 (cb i hi (by omega))
  · have := congrArg Fin.val (h ⟨x, by omega⟩ hx)
    rwa [act_val, act_val] at this

end Circuits

end QCert.XCXCCX4bit.Coxeter
