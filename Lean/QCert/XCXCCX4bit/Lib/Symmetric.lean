/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The symmetric group `S_N` by its Coxeter presentation

Translation of what `Examples/Groups/XCXCCX-4bit` uses of the Agda library
`Examples/Groups/Symmetric` (`Syntactics`, `Semantics`, `Interpretation`,
`Soundness`, `Presentation`, `Surjectivity`): the words of `S_N` in the
adjacent transpositions, the permutations of the states `Fin N` they denote,
and the completeness of the Coxeter relations for them.

A letter `s_d` (`SG N`, with `2 + d ≤ N`) is the transposition of the states
`d` and `d + 1`.  A word acts on the states in operator order, its rightmost
letter first (`act`, the Agda's `CoxeterFrames.actₙ`), and denotes the
inverse permutation, read in diagram order (`perm`, the Agda's `SymI.⟦_⟧`
read with `⟨$⟩ʳ`): `perm (u * v) = (perm u).trans (perm v)`, and
`(perm w).symm x = act w x` holds by `rfl` (the Agda's
`actₙ w x = SymI.⟦ w ⟧ ⟨$⟩ˡ x`).  The relations `SymRel N` are the Coxeter
relations; they are sound for `perm` (`sound`, the Agda's
`Soundness.sound`) and complete (`complete`, the injectivity in
`Presentation.presentation`); every permutation is the permutation of a word
(`go`, `go_sem`: the Agda's `Surjectivity.go`); and so `SymRel N` presents
`S_N` (`presentation`).

**Deviation from the Agda.**  The Agda's words are circuits of
`Circuit.Base` over the one gate `σ-gate` (a letter is `gate₂ σ-gate`
shifted up `d` times), and its relations are `Lift-Relation` of order and
Yang–Baxter, whose structural rules give the far commutations and carry
each relation to every offset.  Here a letter is its index with its bound
(`SG N = {d // 2 + d ≤ N}`, the Agda's `letter N d q` with `tr 0` its index),
and `SymRel N` lists the order, braid and far relations at every index:
exactly the instances of the Agda's relation.  The Agda proves completeness
by a coset normal form; here it is
`QCert.ToffoliHadamardRS.CoxeterFrames.perm_complete` (the frame normal
form) in the quotient monoid, and `go` is that normal form.  Permutations
are Mathlib's `Equiv.Perm (Fin N)`: the Agda's `π ⟨$⟩ʳ i` is `π i`,
`π ⟨$⟩ˡ i` is `π.symm i`, `π ∘ₚ ρ` (diagram order) is `π.trans ρ`
(`= ρ * π`) and `flip π` is `π.symm`.
-/
import QCert.ToffoliHadamardRS.CoxeterFrames
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.Group.End

namespace QCert.XCXCCX4bit.Symmetric

open QCert.ToffoliHadamardRS

variable {n : ℕ}

/-! ## Letters and words -/

/-- The letters of `S_N`: `s_d`, the transposition of the states `d` and
`d + 1` (the Agda's `Sym.Gen N`, through `tr 0`). -/
abbrev SG (N : ℕ) := {d : ℕ // 2 + d ≤ N}

/-- The letter `s_d` as a word. -/
abbrev s (d : ℕ) (q : 2 + d ≤ n) : Word (SG n) := FreeMonoid.of ⟨d, q⟩

/-- The lower state of a letter, read from offset `o`. -/
def tr (o : ℕ) (g : SG n) : ℕ := o + g.1

theorem tr_ge (o : ℕ) (g : SG n) : o ≤ tr o g := Nat.le_add_right o g.1

theorem tr_le (o : ℕ) (g : SG n) : 2 + tr o g ≤ o + n := by
  have := g.2; unfold tr; omega

@[simp] theorem tr_zero (g : SG n) : tr 0 g = g.1 := Nat.zero_add _

/-- The inverse of a word: its letters reversed. -/
def inv (w : Word (SG n)) : Word (SG n) := FreeMonoid.reverse w

@[simp] theorem inv_of (g : SG n) : inv (FreeMonoid.of g) = FreeMonoid.of g := rfl

@[simp] theorem inv_one : inv (1 : Word (SG n)) = 1 := rfl

theorem inv_mul (u v : Word (SG n)) : inv (u * v) = inv v * inv u := FreeMonoid.reverse_mul

@[simp] theorem inv_inv (p : Word (SG n)) : inv (inv p) = p := FreeMonoid.reverse_reverse

/-- The letters of a word, as a Coxeter word of `CoxeterFrames`. -/
def toL (w : Word (SG n)) : List ℕ := (FreeMonoid.toList w).map Subtype.val

@[simp] theorem toL_one : toL (1 : Word (SG n)) = [] := rfl

@[simp] theorem toL_of (g : SG n) : toL (FreeMonoid.of g) = [g.1] := rfl

@[simp] theorem toL_mul (u v : Word (SG n)) : toL (u * v) = toL u ++ toL v := by
  simp [toL]

theorem toL_inv (w : Word (SG n)) : toL (inv w) = CoxeterFrames.inv (toL w) := by
  show ((FreeMonoid.toList w).reverse).map Subtype.val = ((FreeMonoid.toList w).map Subtype.val).reverse
  exact List.map_reverse ..

theorem toL_bound (w : Word (SG n)) : ∀ d ∈ toL w, 2 + d ≤ n := by
  intro d hd
  obtain ⟨g, -, rfl⟩ := List.mem_map.1 hd
  exact g.2

/-- A Coxeter word of `CoxeterFrames` as a word, its letters beyond the
bound left out. -/
def ofL (n : ℕ) (l : List ℕ) : Word (SG n) :=
  FreeMonoid.ofList (l.filterMap fun d => if h : 2 + d ≤ n then some ⟨d, h⟩ else none)

theorem toL_ofL (l : List ℕ) (h : ∀ d ∈ l, 2 + d ≤ n) : toL (ofL n l) = l := by
  induction l with
  | nil => rfl
  | cons d l ih =>
    have hd := h d (by simp)
    have ih := ih fun e he => h e (List.mem_cons_of_mem _ he)
    simp only [ofL, List.filterMap_cons, dif_pos hd] at ih ⊢
    simp only [toL, FreeMonoid.toList_ofList, List.map_cons] at ih ⊢
    rw [ih]

/-! ## The action on states -/

/-- A letter as a function on the states. -/
def swp (g : SG n) (x : Fin n) : Fin n :=
  ⟨CoxeterFrames.sw g.1 x.1, CoxeterFrames.sw_lt (by have := g.2; omega) x.2⟩

theorem swp_swp (g : SG n) (x : Fin n) : swp g (swp g x) = x :=
  Fin.ext (CoxeterFrames.sw_sw g.1 x.1)

/-- The circuit of `w` sends the state `x` to `act w x` (the Agda's
`actₙ`): the rightmost letter acts first. -/
def act (w : Word (SG n)) (x : Fin n) : Fin n := (FreeMonoid.toList w).foldr swp x

@[simp] theorem act_one (x : Fin n) : act 1 x = x := rfl

@[simp] theorem act_of (g : SG n) (x : Fin n) : act (FreeMonoid.of g) x = swp g x := rfl

/-- The Agda's `act-•`. -/
theorem act_mul (u v : Word (SG n)) (x : Fin n) : act (u * v) x = act u (act v x) := by
  simp [act, List.foldr_append]

theorem act_val (w : Word (SG n)) (x : Fin n) :
    (act w x).1 = CoxeterFrames.act (toL w) x.1 := by
  induction w using FreeMonoid.inductionOn' with
  | one => rfl
  | mul_of g w ih => rw [act_mul, toL_mul, CoxeterFrames.act_append, act_of]; simp [swp, ih, toL]

theorem act_inv (p : Word (SG n)) (x : Fin n) : act (inv p) (act p x) = x :=
  Fin.ext (by rw [act_val, act_val, toL_inv, CoxeterFrames.act_inv])

theorem act_inv' (p : Word (SG n)) (x : Fin n) : act p (act (inv p) x) = x := by
  have := act_inv (inv p) x; rwa [inv_inv] at this

/-- A Coxeter word with letters below `n - 1` fixes the states from `n` on. -/
theorem act_fix_ge (l : List ℕ) (hl : ∀ d ∈ l, 2 + d ≤ n) (x : ℕ) (hx : n ≤ x) :
    CoxeterFrames.act l x = x := by
  induction l with
  | nil => rfl
  | cons d l ih =>
    rw [CoxeterFrames.act_cons, ih fun e he => hl e (List.mem_cons_of_mem _ he)]
    have := hl d (by simp)
    unfold CoxeterFrames.sw; split_ifs <;> omega

/-! ## The permutation of a word -/

/-- The permutation of a word, read in diagram order (the Agda's
`SymI.⟦ w ⟧`): `perm w i` is the Agda's `SymI.⟦ w ⟧ ⟨$⟩ʳ i`, and
`(perm w).symm x = act w x` by `rfl`. -/
def perm (w : Word (SG n)) : Equiv.Perm (Fin n) where
  toFun := act (inv w)
  invFun := act w
  left_inv x := act_inv' w x
  right_inv x := act_inv w x

theorem perm_apply (w : Word (SG n)) (i : Fin n) : perm w i = act (inv w) i := rfl

@[simp] theorem perm_symm_apply (w : Word (SG n)) (x : Fin n) : (perm w).symm x = act w x := rfl

@[simp] theorem perm_of (g : SG n) (i : Fin n) : perm (FreeMonoid.of g) i = swp g i := rfl

@[simp] theorem perm_one : perm (1 : Word (SG n)) = Equiv.refl _ := rfl

theorem perm_mul (u v : Word (SG n)) : perm (u * v) = (perm u).trans (perm v) := by
  ext i; simp [perm_apply, inv_mul, act_mul]

theorem perm_mul_apply (u v : Word (SG n)) (i : Fin n) : perm (u * v) i = perm v (perm u i) := by
  rw [perm_mul]; rfl

/-- Two permutations whose inverses agree agree (the Agda's `ˡ⇒ʳ`). -/
theorem l_to_r (π ρ : Equiv.Perm (Fin n)) (h : ∀ x, π.symm x = ρ.symm x) : ∀ i, π i = ρ i := by
  have : π.symm = ρ.symm := Equiv.ext h
  intro i; rw [show π = ρ from Equiv.symm_bijective.injective this]

theorem perm_eq_iff_act (u v : Word (SG n)) :
    (∀ i, perm u i = perm v i) ↔ ∀ x, act u x = act v x := by
  constructor
  · intro h x
    have : perm u = perm v := Equiv.ext h
    rw [← perm_symm_apply, this, perm_symm_apply]
  · exact l_to_r (perm u) (perm v)

/-! ## The relations -/

/-- The Coxeter relations of `S_n` (the Agda's `n VRel,_===_` of
`Examples.Groups.Symmetric`, flattened: order, braid and far commutation at
every index). -/
inductive SymRel (n : ℕ) : WRel (SG n)
  | order (d : ℕ) (q : 2 + d ≤ n) : SymRel n (s d q * s d q) 1
  | braid (d : ℕ) (q : 3 + d ≤ n) :
      SymRel n (s d (by omega) * s (d + 1) (by omega) * s d (by omega))
        (s (d + 1) (by omega) * s d (by omega) * s (d + 1) (by omega))
  | far (d e : ℕ) (lo : 2 + d ≤ e) (q : 2 + e ≤ n) :
      SymRel n (s d (by omega) * s e q) (s e q * s d (by omega))

/-- The kernel of the action, a congruence. -/
def actCon (n : ℕ) : Con (Word (SG n)) where
  r u v := ∀ x, act u x = act v x
  iseqv := ⟨fun _ _ => rfl, fun h x => (h x).symm, fun h h' x => (h x).trans (h' x)⟩
  mul' {u u' v v'} hu hv x := by rw [act_mul, act_mul, hv, hu]

theorem sound_ax {u v : Word (SG n)} (h : SymRel n u v) : ∀ x, act u x = act v x := by
  intro x
  apply Fin.ext
  rw [act_val, act_val]
  cases h <;>
  · simp only [toL_mul, toL_of, toL_one, List.cons_append, List.nil_append,
      CoxeterFrames.act_cons, CoxeterFrames.act_nil]
    unfold CoxeterFrames.sw
    split_ifs <;> omega

/-- The relations are sound (the Agda's `Soundness.sound`). -/
theorem sound {u v : Word (SG n)} (h : Derivable (SymRel n) u v) : ∀ i, perm u i = perm v i := by
  have : conGen (SymRel n) ≤ actCon n := Con.conGen_le fun a b hab => sound_ax hab
  exact (perm_eq_iff_act u v).2 (this h)

/-! ## Completeness -/

section Complete

open CoxeterFrames in
/-- The letters as elements of the quotient monoid (`1` beyond the bound). -/
def τ (n : ℕ) (d : ℕ) : (conGen (SymRel n)).Quotient :=
  if h : 2 + d ≤ n then cl (SymRel n) (s d h) else 1

theorem τ_of (d : ℕ) (h : 2 + d ≤ n) : τ n d = CoxeterFrames.cl (SymRel n) (s d h) := dif_pos h

theorem ev_toL (w : Word (SG n)) :
    CoxeterFrames.ev (τ n) (toL w) = CoxeterFrames.cl (SymRel n) w := by
  induction w using FreeMonoid.inductionOn' with
  | one => exact CoxeterFrames.cl_one.symm
  | mul_of g w ih =>
    rw [toL_mul, toL_of, List.singleton_append, CoxeterFrames.ev_cons, ih, τ_of g.1 g.2,
      CoxeterFrames.cl_mul]

theorem coxRel : CoxeterFrames.CoxRel (τ n) (n - 1) where
  order i hi := by
    rw [τ_of i (by omega), ← CoxeterFrames.cl_mul, ← CoxeterFrames.cl_one]
    exact CoxeterFrames.cl_eq.2 (Derivable.of (SymRel.order i _))
  braid i hi := by
    rw [τ_of i (by omega), τ_of (i + 1) (by omega)]
    simp only [← CoxeterFrames.cl_mul]
    exact CoxeterFrames.cl_eq.2 (Derivable.of (SymRel.braid i (by omega)))
  far i j hij hj := by
    rw [τ_of i (by omega), τ_of j (by omega)]
    simp only [← CoxeterFrames.cl_mul]
    exact CoxeterFrames.cl_eq.2 (Derivable.of (SymRel.far i j (by omega) (by omega)))

theorem valid_toL (w : Word (SG n)) : CoxeterFrames.Valid (n - 1) (toL w) := by
  intro d hd; have := toL_bound w d hd; omega

/-- Two words with the same permutation are equal by the relations (the
completeness of the Agda's `Presentation.presentation`). -/
theorem complete {u v : Word (SG n)} (h : ∀ i, perm u i = perm v i) : Derivable (SymRel n) u v := by
  have ha := (perm_eq_iff_act u v).1 h
  apply CoxeterFrames.cl_eq.1
  rw [← ev_toL, ← ev_toL]
  apply CoxeterFrames.perm_complete coxRel (valid_toL u) (valid_toL v)
  intro x hx
  by_cases hxn : x < n
  · have := congrArg Fin.val (ha ⟨x, hxn⟩)
    rwa [act_val, act_val] at this
  · rw [act_fix_ge _ (toL_bound u) x (by omega), act_fix_ge _ (toL_bound v) x (by omega)]

end Complete

/-! ## Surjectivity -/

/-- The list of the images of the states under `π⁻¹`, whose frame is a word
for `π`. -/
def goList (n : ℕ) (π : Equiv.Perm (Fin n)) : List ℕ := List.ofFn fun i => (π.symm i).1

theorem goList_nodup (π : Equiv.Perm (Fin n)) : (goList n π).Nodup :=
  List.nodup_ofFn.2 fun _ _ h => π.symm.injective (Fin.ext h)

theorem frame_bound (π : Equiv.Perm (Fin n)) :
    ∀ d ∈ CoxeterFrames.frame (goList n π), 2 + d ≤ n := by
  intro d hd
  rcases n with _ | n
  · simp [goList, CoxeterFrames.frame_nil] at hd
  · have := CoxeterFrames.frame_valid n (goList (n + 1) π) (goList_nodup π) (by
      intro t ht
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ht
      exact (π.symm i).2) d hd
    omega

/-- A word for each permutation (the Agda's `Surjectivity.go`, its first
component; `go_sem` is its second): the frame normal form. -/
def go (n : ℕ) (π : Equiv.Perm (Fin n)) : Word (SG n) :=
  ofL n (CoxeterFrames.frame (goList n π))

theorem go_act (π : Equiv.Perm (Fin n)) (x : Fin n) : act (go n π) x = π.symm x := by
  apply Fin.ext
  rw [act_val, go, toL_ofL _ (frame_bound π),
    CoxeterFrames.frame_act _ (goList_nodup π) x.1 (by simp [goList])]
  simp [goList]

/-- The word `go n π` denotes `π`. -/
theorem go_sem (n : ℕ) (π : Equiv.Perm (Fin n)) : ∀ i, perm (go n π) i = π i :=
  l_to_r _ _ fun x => go_act π x

theorem perm_go (π : Equiv.Perm (Fin n)) : perm (go n π) = π := Equiv.ext (go_sem n π)

attribute [irreducible] go

/-! ## The presentation -/

/-- The semantics of a letter, in operator order: the transposition. -/
def sem (g : SG n) : Equiv.Perm (Fin n) := (perm (FreeMonoid.of g)).symm

theorem lift_sem (w : Word (SG n)) : FreeMonoid.lift sem w = (perm w).symm := by
  induction w using FreeMonoid.inductionOn' with
  | one => rfl
  | mul_of g w ih =>
    rw [map_mul, ih, FreeMonoid.lift_eval_of, perm_mul]; rfl

/-- The Coxeter relations present `S_n` (the Agda's
`Presentation.presentation`, with the words acting in operator order). -/
theorem presentation : IsPresentationOf (SymRel n) (sem (n := n)) where
  grouplike g := ⟨FreeMonoid.of g, Derivable.of (SymRel.order g.1 g.2)⟩
  sound u v h := by
    rw [lift_sem, lift_sem, Equiv.ext (sound (Derivable.of h))]
  complete u v h := by
    rw [lift_sem, lift_sem] at h
    exact complete fun i => by rw [Equiv.symm_bijective.injective h]
  surjective π := ⟨go n π.symm, by rw [lift_sem, perm_go, Equiv.symm_symm]⟩

end QCert.XCXCCX4bit.Symmetric
