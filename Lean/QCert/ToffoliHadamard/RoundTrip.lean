/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024): the round trip

Every letter `x` of `Σ₁` is derivably equal, modulo `R₁`, to the circuit of
its decoding into level matrices, `encW (decW x)` (`roundTrip'`).

Each letter has a *route* (`Micro.routeLit x`): a word equal to it modulo
`R₁`, made of letters `y` proved earlier (`rtRank y < rtRank x`) and of the
words `xAdj i`, `neg0`, `K_[0,1,2,3]` of the macro letters (`rtPieces x`):
a definition of Figure 4 (`CZ₀₁ = K₁₂ CX₀₁ K₁₂`, …), `(r_K)` for `K₁₂`, the
alias of `(−1)_[0]` for `CCZ`, or a short derivation for the generators
`X₀, X₁, X₂, CX₀₁, CX₀₂, CX₁₀, CCX₀₂, CCX₁₂` (`Micro.lean`).  Replacing each
`y` by its round trip gives the macro word `roundW x`, which equals the
encoding of the decoding of `x` over `ML` (`RoundTable.rtTable`).
-/
import QCert.ToffoliHadamard.RoundTable
import QCert.ToffoliHadamard.Translation

namespace QCert.ToffoliHadamard.Macro

open Engine LiRossSelinger

/-- The round trip of one letter. -/
def RT (x : Sym1) : Prop :=
  Derivable R1 (FreeMonoid.of x) (encW (decW (FreeMonoid.of x)))

/-- The encoding of the decoding of a letter, over `ML`. -/
def roundD (x : Sym1) : List ML := encL ((dec x).map toAG)

theorem encW_decW (x : Sym1) : encW (decW (FreeMonoid.of x)) = phi (FreeMonoid.ofList (roundD x)) := by
  rw [decW, FreeMonoid.lift_eval_of, ← phi_encMW, encMW_ofList]; rfl

/-- A piece of a route as a word over `Σ₁`. -/
def pieceW : Sym1 ⊕ ML → List Sym1
  | .inl y => [y]
  | .inr m => phiL m

/-- A piece of a route as a word over `ML`. -/
def pieceM : Sym1 ⊕ ML → List ML
  | .inl y => roundD y
  | .inr m => [m]

theorem pieces_sound (ps : List (Sym1 ⊕ ML)) (h : ∀ y, Sum.inl y ∈ ps → RT y) :
    Derivable R1 (FreeMonoid.ofList (ps.flatMap pieceW))
      (phi (FreeMonoid.ofList (ps.flatMap pieceM))) := by
  induction ps with
  | nil => simp; rfl
  | cons p ps ih =>
    have ih' := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    rw [List.flatMap_cons, List.flatMap_cons, FreeMonoid.ofList_append, FreeMonoid.ofList_append,
      map_mul]
    refine Derivable.mul ?_ ih'
    cases p with
    | inl y =>
      have := h y (by simp)
      rw [RT, encW_decW] at this
      simpa [pieceW, pieceM] using this
    | inr m =>
      rw [pieceM, phi_ofList]
      simp [pieceW]
      rfl

set_option maxRecDepth 100000 in
theorem route_pieces (x : Sym1) : Micro.routeLit x = (rtPieces x).flatMap pieceW := by
  cases x <;> decide +kernel

set_option maxRecDepth 100000 in
theorem rt_get (x : Sym1) : (E0 ++ instE ++ eqns rtTable)[rtIdx x]? =
    some ((rtPieces x).flatMap pieceM, roundD x) := by
  cases x <;> decide +kernel

/-- The round trip of a letter, from those of the letters of its route. -/
theorem rt_of (x : Sym1) (h : ∀ y, Sum.inl y ∈ rtPieces x → RT y) : RT x := by
  have h1 := Micro.route_micro x
  rw [route_pieces] at h1
  have h2 := pieces_sound _ h
  have h3 := toR1 (rt_valid.get (rt_get x))
  rw [RT, encW_decW]
  exact h1.trans (h2.trans h3)

set_option maxRecDepth 100000 in
theorem rank_lt (x : Sym1) :
    ((rtPieces x).all fun p => match p with
      | .inl y => decide (rtRank y < rtRank x)
      | .inr _ => true) = true := by
  cases x <;> decide +kernel

/-- Every letter's round trip. -/
theorem roundTrip' (x : Sym1) : RT x := by
  induction h : rtRank x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    apply rt_of
    intro y hy
    have := List.all_eq_true.1 (rank_lt x) _ hy
    simp only [decide_eq_true_eq] at this
    exact ih _ (h ▸ this) y rfl

end QCert.ToffoliHadamard.Macro
