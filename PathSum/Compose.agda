------------------------------------------------------------------------
-- Presentations of groups
--
-- Sequential and parallel composition of path-sums (Amy, QPL 2018,
-- definition 2.6 and section 2.1)
--
-- Definition 2.6 composes
--
--    U_ξ  : |x⟩  ↦ 1/√2^m  Σ_y  e^{2πi P(x,y)}   |f(x,y)⟩
--    U_ξ′ : |x′⟩ ↦ 1/√2^m′ Σ_y′ e^{2πi P′(x′,y′)} |f′(x′,y′)⟩
--
-- into U_{ξ′∘ξ} : |x⟩ ↦ 1/√2^(m+m′) Σ_{y ∈ Z₂^(m+m′)}
-- e^{2πi (P + P′[yᵢ ← y_{i+m}][xᵢ ← f̄ᵢ])(x,y)} |f′[x′ᵢ ← fᵢ](x,y)⟩.
-- Here that is one simultaneous substitution, feed ξ, applied to both
-- the phase and the outputs of ξ′ (PathSum.Polynomial.Bind): ξ′'s
-- input variable x′ᵢ becomes the lift of ξ's i-th output, and ξ′'s
-- path variable y′ⱼ becomes the path variable y_{m+j}.  ξ's own
-- variables are kept, its path variables in the first block (inˡ).
-- The path variables are therefore in the paper's order, ξ's first,
-- and the normalisations add.  Nothing is proved here; the meaning of
-- the composite is in PathSum.Compose.Properties.
--
-- Two departures from the letter of definition 2.6.
--
-- * The paper renames y′ into y_{·+m} in the phase but not in the
--   output f′[x′ᵢ ← fᵢ].  Read literally the output would then mention
--   ξ's path variables where ξ′'s were meant; that is a typo, and the
--   outputs are renamed here too.
--
-- * The outputs substitute the lifted f̄ᵢ rather than fᵢ over Z₂, as
--   PathSum.Reduction's hh-reduct already does: output polynomials are
--   stored as integer polynomials read modulo 2, and substituting the
--   lift, which agrees with fᵢ modulo 2 coefficient by coefficient
--   (PathSum.Polynomial.Boolean.liftᴮ-≈), gives the same Boolean
--   polynomial.  Only the outputs' residues are ever read.
--
-- The paper also restricts composition to "compatible" signatures,
-- which matters only for constant inputs; here every input is a
-- variable, so every pair of path-sums on n wires is compatible.
--
-- Vertical composition, "concatenating the inputs and outputs then
-- adding the phase polynomials with appropriate renaming", is _⊗ᴾ_:
-- the variables of ξ₁ go to the first blocks of inputs and path
-- variables, those of ξ₂ to the second.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Compose where

open import Data.Fin.Base using (_↑ˡ_; _↑ʳ_; splitAt)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Sum.Base using ([_,_]′)

open import PathSum.Base using (PathSum; ⟨_,_⟩; phase; out)
open import PathSum.Polynomial using (Poly; Var; x[_]; y[_]; _+ᴾ_; μ)
open import PathSum.Polynomial.Bind using (bind; rename)
open import PathSum.Polynomial.Boolean using (liftᴮ)

private
  variable
    n n₁ n₂ k k′ k₁ k₂ m m′ m₁ m₂ : ℕ


------------------------------------------------------------------------
-- Sequential composition (definition 2.6)

-- ξ's variables in the composite: its inputs stay, its path variables
-- are the first m of m + m′.

inˡ : ∀ m′ → Var n m → Var n (m + m′)
inˡ m′ x[ i ] = x[ i ]
inˡ m′ y[ j ] = y[ j ↑ˡ m′ ]

-- What ξ′'s variables become: its input x′ᵢ the lift of ξ's i-th
-- output, its path variable y′ⱼ the path variable y_{m+j}.

feed : PathSum n k m → Var n m′ → Poly n (m + m′)
feed {m′ = m′} ξ x[ i ] = rename (inˡ m′) (liftᴮ (out ξ i))
feed {m = m}   ξ y[ j ] = μ y[ m ↑ʳ j ]

-- ξ′ ∘ ξ: first ξ, then ξ′.

infixr 9 _∘ᴾ_

_∘ᴾ_ : PathSum n k′ m′ → PathSum n k m → PathSum n (k + k′) (m + m′)
_∘ᴾ_ {m′ = m′} ξ′ ξ =
  ⟨ rename (inˡ m′) (phase ξ) +ᴾ bind (phase ξ′) (feed ξ)
  , (λ w → bind (out ξ′ w) (feed ξ)) ⟩


------------------------------------------------------------------------
-- Parallel composition

-- The variables of the upper and the lower path-sum in the composite.

⊗ˡ : ∀ n₂ m₂ → Var n₁ m₁ → Var (n₁ + n₂) (m₁ + m₂)
⊗ˡ n₂ m₂ x[ i ] = x[ i ↑ˡ n₂ ]
⊗ˡ n₂ m₂ y[ j ] = y[ j ↑ˡ m₂ ]

⊗ʳ : ∀ n₁ m₁ → Var n₂ m₂ → Var (n₁ + n₂) (m₁ + m₂)
⊗ʳ n₁ m₁ x[ i ] = x[ n₁ ↑ʳ i ]
⊗ʳ n₁ m₁ y[ j ] = y[ m₁ ↑ʳ j ]

infixr 8 _⊗ᴾ_

_⊗ᴾ_ : PathSum n₁ k₁ m₁ → PathSum n₂ k₂ m₂ →
       PathSum (n₁ + n₂) (k₁ + k₂) (m₁ + m₂)
_⊗ᴾ_ {n₁ = n₁} {m₁ = m₁} {n₂ = n₂} {m₂ = m₂} ξ₁ ξ₂ =
  ⟨ rename (⊗ˡ n₂ m₂) (phase ξ₁) +ᴾ rename (⊗ʳ n₁ m₁) (phase ξ₂)
  , (λ w → [ (λ i → rename (⊗ˡ n₂ m₂) (out ξ₁ i))
           , (λ i → rename (⊗ʳ n₁ m₁) (out ξ₂ i)) ]′ (splitAt n₁ w)) ⟩
