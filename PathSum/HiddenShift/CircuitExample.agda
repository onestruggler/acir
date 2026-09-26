------------------------------------------------------------------------
-- Presentations of groups
--
-- The hidden shift circuits at one instance, as cross-checks
--
-- The theorems of PathSum.HiddenShift.Circuit and
-- PathSum.HiddenShift.Symbolic hold for every m, every list of
-- monomials and every shift; nothing here is needed for them.  These
-- are cross-checks at M₀ = 0 (so M = 3, the Clifford+T precision), at
-- the instance of PathSum.HiddenShift.Example: m = 1, g(a) = a (one Z
-- gate), s = (1, 0).
--
-- * The circuits are the ones drawn in figure 3: the gate lists of
--   HSᶜ g s and SSᶜ g, read wire by wire, are computed and compared
--   with the lists written out by hand (HSᶜ-gates, SSᶜ-gates), as are
--   those of the gadgets CZᶜ and CCZᶜ (seven T gates) and of X.  Their
--   Hadamard counts are 3n + 4|s| = 10 and 3n = 6.
-- * The gadgets and the oracle of f(x, y) = x + xy are checked
--   against the oracle path-sums by brute force (PathSum.Brute:
--   every entry of both operators computed), independently of the
--   diagonal calculus that proves them in general, and X against
--   |x⟩ ↦ |1 - x⟩.
-- * The general theorems, instantiated: the circuit of figure 3(a)
--   sends |0⟩ to |s⟩, and that of figure 3(b) |0⟩|s⟩ to |s⟩|s⟩ for
--   every s.  They are stated through the records HiddenShiftSpec and
--   SymbolicShiftSpec, whose arguments are the circuit's data, so that
--   Agda compares the closed statements by their arguments rather than
--   by unfolding the circuits into amplitudes.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.HiddenShift.CircuitExample where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Fin.Base using (Fin; zero; suc; toℕ)
open import Data.Integer.Base using (1ℤ)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (True)

open import PathSum.Base using (PathSum; ⟨_,_⟩)
open import PathSum.Brute 0 using (≋?; ≋-by-eval)
open import PathSum.CRK.Circuit 3 using
  (Gate; H; CNOT; R; R†; Circuit; norm; ⟦_⟧)
open import PathSum.Denotation 0 using (_≋_)
open import PathSum.Polynomial using (Poly; x[_]; 0ᴾ; _+ᴾ_; _-ᴾ_; κ; μ)
open import PathSum.Polynomial.Product using (_*ᴾ_)

open import PathSum.HiddenShift 0 using (Oᴾ)
open import PathSum.HiddenShift.Circuit 0 public using
  (monoᴾ; sumᴾ; oracleᶠ; oracleᵈ; HSᶜ; HiddenShiftSpec;
   hidden-shift-circuit-spec)
open import PathSum.HiddenShift.Gates 0 public using
  (Term; Z; CZ; CCZ; CZᶜ; CCZᶜ)
open import PathSum.HiddenShift.Layers 0 public using (Xᶜ)
open import PathSum.HiddenShift.Symbolic 0 public using
  (SSᶜ; SymbolicShiftSpec; symbolic-shift-spec)

private
  variable
    n k m : ℕ


------------------------------------------------------------------------
-- The instance

g₁ : List (Term 1)
g₁ = Z zero ∷ []

s₁ : Fin 2 → Bool
s₁ zero       = true
s₁ (suc zero) = false


------------------------------------------------------------------------
-- The gate lists

-- A gate, read by its kind and its wires.

data Shape : Set where
  h       : ℕ → Shape
  cx      : ℕ → ℕ → Shape
  rot rot† : ℕ → ℕ → Shape

shape : Gate n → Shape
shape (H w)        = h (toℕ w)
shape (CNOT c t _) = cx (toℕ c) (toℕ t)
shape (R k w)      = rot k (toℕ w)
shape (R† k w)     = rot† k (toℕ w)

-- X = H R₁ H, CZ from three S gates, CCZ from seven T gates.

X-gates : map shape (Xᶜ {1} zero) ≡ h 0 ∷ rot 1 0 ∷ h 0 ∷ []
X-gates = refl

CZ-gates : map shape (CZᶜ {2} zero (suc zero) (λ ())) ≡
           rot 2 0 ∷ rot 2 1 ∷ cx 0 1 ∷ rot† 2 1 ∷ cx 0 1 ∷ []
CZ-gates = refl

CCZ-gates : map shape (CCZᶜ {3} zero (suc zero) (suc (suc zero))
                              (λ ()) (λ ()) (λ ())) ≡
            rot 3 0 ∷ rot 3 1 ∷ rot 3 2 ∷
            cx 1 2 ∷ rot† 3 2 ∷ cx 1 2 ∷
            cx 0 2 ∷ cx 1 2 ∷ rot 3 2 ∷ cx 1 2 ∷ cx 0 2 ∷
            cx 0 2 ∷ rot† 3 2 ∷ cx 0 2 ∷
            cx 0 1 ∷ rot† 3 1 ∷ cx 0 1 ∷ []
CCZ-gates = refl

-- Figure 3(a): H^{⊗2}; X on x (s = 10); O_f = Z(x) CZ(x, y); X on x;
-- H^{⊗2}; O_f̃ = CZ(x, y) Z(y); H^{⊗2}.

HSᶜ-gates : map shape (HSᶜ g₁ s₁) ≡
  h 0 ∷ h 1 ∷
  h 0 ∷ rot 1 0 ∷ h 0 ∷
  rot 1 0 ∷ rot 2 0 ∷ rot 2 1 ∷ cx 0 1 ∷ rot† 2 1 ∷ cx 0 1 ∷
  h 0 ∷ rot 1 0 ∷ h 0 ∷
  h 0 ∷ h 1 ∷
  rot 2 0 ∷ rot 2 1 ∷ cx 0 1 ∷ rot† 2 1 ∷ cx 0 1 ∷ rot 1 1 ∷
  h 0 ∷ h 1 ∷ []
HSᶜ-gates = refl

HSᶜ-norm : norm (HSᶜ g₁ s₁) ≡ 10
HSᶜ-norm = refl

-- Figure 3(b), the shift register on wires 2 and 3: the X gates become
-- CNOTs from wire 2 + i to wire i.

SSᶜ-gates : map shape (SSᶜ g₁) ≡
  h 0 ∷ h 1 ∷
  cx 2 0 ∷ cx 3 1 ∷
  rot 1 0 ∷ rot 2 0 ∷ rot 2 1 ∷ cx 0 1 ∷ rot† 2 1 ∷ cx 0 1 ∷
  cx 2 0 ∷ cx 3 1 ∷
  h 0 ∷ h 1 ∷
  rot 2 0 ∷ rot 2 1 ∷ cx 0 1 ∷ rot† 2 1 ∷ cx 0 1 ∷ rot 1 1 ∷
  h 0 ∷ h 1 ∷ []
SSᶜ-gates = refl

SSᶜ-norm : norm (SSᶜ g₁) ≡ 6
SSᶜ-norm = refl


------------------------------------------------------------------------
-- Brute force

-- A circuit's path-sum against a path-sum, every entry computed.
-- Stated for any circuit, so that the closed instances below are
-- matched by their arguments.

crk-by-eval : ∀ {k′ m′} (C : Circuit n) (ζ : PathSum n k′ m′) →
              {True (≋? ⟦ C ⟧ ζ)} → ⟦ C ⟧ ≋ ζ
crk-by-eval C ζ {t} = ≋-by-eval ⟦ C ⟧ ζ {t}

-- The gadgets are the diagonals (-1)^{ab} and (-1)^{abc}.

CZ-brute : ⟦ CZᶜ {2} zero (suc zero) (λ ()) ⟧ ≋
           Oᴾ (monoᴾ (CZ {2} zero (suc zero) (λ ())))
CZ-brute = crk-by-eval (CZᶜ zero (suc zero) (λ ()))
                       (Oᴾ (monoᴾ (CZ zero (suc zero) (λ ()))))

CCZ-brute : ⟦ CCZᶜ {3} zero (suc zero) (suc (suc zero)) (λ ()) (λ ()) (λ ()) ⟧ ≋
            Oᴾ (monoᴾ (CCZ {3} zero (suc zero) (suc (suc zero))
                               (λ ()) (λ ()) (λ ())))
CCZ-brute = crk-by-eval
  (CCZᶜ zero (suc zero) (suc (suc zero)) (λ ()) (λ ()) (λ ()))
  (Oᴾ (monoᴾ (CCZ zero (suc zero) (suc (suc zero)) (λ ()) (λ ()) (λ ()))))

-- The oracles of f(x, y) = x + xy and of its dual y + xy, against the
-- polynomials written out.  (PathSum.HiddenShift's mmᴾ and dualᴾ are
-- built by renaming, which is opaque and does not compute; that they
-- have these parities is proved in general, bool-mmᴾ and bool-dualᴾ.)

fᴾ₁ f̃ᴾ₁ : Poly 2 0
fᴾ₁ = μ x[ zero ] +ᴾ (μ x[ zero ] *ᴾ μ x[ suc zero ])
f̃ᴾ₁ = μ x[ suc zero ] +ᴾ (μ x[ zero ] *ᴾ μ x[ suc zero ])

oracleᶠ-brute : ⟦ oracleᶠ g₁ ⟧ ≋ Oᴾ fᴾ₁
oracleᶠ-brute = crk-by-eval (oracleᶠ g₁) (Oᴾ fᴾ₁)

oracleᵈ-brute : ⟦ oracleᵈ g₁ ⟧ ≋ Oᴾ f̃ᴾ₁
oracleᵈ-brute = crk-by-eval (oracleᵈ g₁) (Oᴾ f̃ᴾ₁)

-- X = H R₁ H is |x⟩ ↦ |1 - x⟩.

NOTᴾ : PathSum 1 0 0
NOTᴾ = ⟨ 0ᴾ , (λ _ → κ 1ℤ -ᴾ μ x[ zero ]) ⟩

X-brute : ⟦ Xᶜ {1} zero ⟧ ≋ NOTᴾ
X-brute = crk-by-eval (Xᶜ zero) NOTᴾ


------------------------------------------------------------------------
-- The theorems at the instance

hidden-shift-example : HiddenShiftSpec g₁ s₁
hidden-shift-example = hidden-shift-circuit-spec g₁ s₁

symbolic-shift-example : SymbolicShiftSpec g₁
symbolic-shift-example = symbolic-shift-spec g₁
