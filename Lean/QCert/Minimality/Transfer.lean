/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Completeness by transfer (Section 4.2)

Definition 18, Lemmas 19, 20 and Theorem 21: if circuits of a target theory
are encoded into a source theory that is complete for the same semantics,
and decoded back so that decoding respects the source relations (Lemma 20)
and decoding an encoding derives the original circuit (Lemma 19), then the
target theory is complete (`complete_of_transfer`).

For two gate sets with the same gates under a renaming, `Gen.map` renames
generators and `lift_map` carries the structural rules across.
-/
import QCert.Minimality.Derive

namespace QCert.Minimality

open Circuit

/-- Theorem 21: completeness transferred from a complete source theory along
an encoding `E` and a decoding `D`. -/
theorem complete_of_transfer {X Y : Type*} {M : Type*} [Monoid M]
    (Γ : WRel X) (Γs : WRel Y) (sem : FreeMonoid X →* M) (semS : FreeMonoid Y →* M)
    (E : FreeMonoid X → FreeMonoid Y) (D : FreeMonoid Y → FreeMonoid X)
    (hE : ∀ w, semS (E w) = sem w)
    (hsrc : ∀ a b, semS a = semS b → Derivable Γs a b)
    (hD : ∀ a b, Derivable Γs a b → Derivable Γ (D a) (D b))
    (hDE : ∀ w, Derivable Γ (D (E w)) w) :
    ∀ w v, sem w = sem v → Derivable Γ w v := by
  intro w v h
  have h1 : Derivable Γs (E w) (E v) := hsrc _ _ (by rw [hE, hE, h])
  exact ((hDE w).symm.trans (hD _ _ h1)).trans (hDE v)

/-- Lemma 20: a decoding that is a monoid homomorphism and sends each source
relation to a derivable equation respects derivability. -/
theorem derivable_map_of {X Y : Type*} (Γ : WRel X) (Γs : WRel Y) (D : FreeMonoid Y →* FreeMonoid X)
    (hD : ∀ a b, Γs a b → Derivable Γ (D a) (D b)) {a b : FreeMonoid Y}
    (h : Derivable Γs a b) : Derivable Γ (D a) (D b) := by
  let c : Con (FreeMonoid Y) := (conGen Γ).comap D (map_mul D)
  have : conGen Γs ≤ c := Con.conGen_le fun x y r => hD x y r
  exact this h

/-! ### Renaming gates -/

section Rename

variable {G G' : ℕ → Type} (f : ∀ k, G k → G' k)

/-- A generator with its gate renamed. -/
def Gen.map : {n : ℕ} → Gen G n → Gen G' n
  | _, .gate0 g => .gate0 (f 0 g)
  | _, .gate1 g => .gate1 (f 1 g)
  | _, .gate2 g => .gate2 (f 2 g)
  | _, .gate3 g => .gate3 (f 3 g)
  | _, .up g => .up (Gen.map g)

/-- A circuit with its gates renamed. -/
def Circuit.rename (n : ℕ) : Circuit G n →* Circuit G' n := FreeMonoid.map (Gen.map f)

theorem rename_shift {n : ℕ} (w : Circuit G n) :
    Circuit.rename f (n + 1) (shift w) = shift (Circuit.rename f n w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of g w ih =>
    rw [map_mul, map_mul, map_mul, map_mul, ih]
    rfl

theorem Gen.map_pad (m : ℕ) {k : ℕ} (g : Gen G k) : Gen.map f (g.pad m) = (Gen.map f g).pad m := by
  induction g with
  | gate0 c => rfl
  | gate1 c => rfl
  | gate2 c => rfl
  | gate3 c => rfl
  | up g ih => exact congrArg Gen.up ih

theorem rename_pad (m : ℕ) {k : ℕ} (w : Circuit G k) :
    Circuit.rename f (m + k) (Circuit.pad m w) = Circuit.pad m (Circuit.rename f k w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of g w ih =>
    rw [map_mul, map_mul, map_mul, map_mul, ih]
    congr 1
    show FreeMonoid.of (Gen.map f (g.pad m)) = FreeMonoid.of ((Gen.map f g).pad m)
    rw [Gen.map_pad]

/-- Renaming carries the structural rules to structural rules, and rules of
`R` to whatever they are sent to. -/
theorem lift_rename {R : CRel G} {R' : CRel G'}
    (hR : ∀ k w v, R k w v → Derivable (Lift R' k) (Circuit.rename f k w) (Circuit.rename f k v)) :
    ∀ {n : ℕ} {w v : Circuit G n}, Lift R n w v →
      Derivable (Lift R' n) (Circuit.rename f n w) (Circuit.rename f n v)
  | _, _, _, .rule r => hR _ _ _ r
  | _, _, _, .shift r => by
    rw [rename_shift, rename_shift]
    exact derivable_shift (lift_rename hR r)
  | _, _, _, .comm1 c g => by
    simp only [map_mul, Circuit.rename, FreeMonoid.map_of]
    exact Derivable.of (Lift.comm1 (f 1 c) (Gen.map f g))
  | _, _, _, .comm2 c g => by
    simp only [map_mul, Circuit.rename, FreeMonoid.map_of]
    exact Derivable.of (Lift.comm2 (f 2 c) (Gen.map f g))
  | _, _, _, .comm3 c g => by
    simp only [map_mul, Circuit.rename, FreeMonoid.map_of]
    exact Derivable.of (Lift.comm3 (f 3 c) (Gen.map f g))
  | _, _, _, .scalar c => by
    simp only [Circuit.rename, FreeMonoid.map_of]
    exact Derivable.of (Lift.scalar (f 0 c))

/-- Renaming carries derivations of `Lift (Padded Base)` to derivations of
`Lift (Padded Base')` as soon as it carries each rule of `Base`, on its own
wires, to a derivable equation. -/
theorem derivable_rename {Base : CRel G} {Base' : CRel G'}
    (hB : ∀ k w v, Base k w v →
      Derivable (Lift (Padded Base') k) (Circuit.rename f k w) (Circuit.rename f k v))
    {n : ℕ} {w v : Circuit G n} (h : Derivable (Lift (Padded Base) n) w v) :
    Derivable (Lift (Padded Base') n) (Circuit.rename f n w) (Circuit.rename f n v) := by
  refine derivable_map_of _ _ (Circuit.rename f n) (fun a b r => ?_) h
  refine lift_rename f (fun k w v r => ?_) r
  cases r with
  | @pad j m w v b =>
    rw [rename_pad, rename_pad]
    exact derivable_pad m (hB _ _ _ b)

end Rename

end QCert.Minimality
