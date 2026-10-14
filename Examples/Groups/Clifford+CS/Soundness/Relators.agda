------------------------------------------------------------------------
-- Presentations of groups
--
-- The relators of Syntactics, checked as matrix identities
--
-- Each rule is stated at the width it is drawn on and checked there, as
-- an identity between stored Gaussian-integer matrices: the two sides
-- have different numbers of letters, hence different powers of γ⁻¹, so
-- each side is scaled by the other's power of γ before comparison
-- (Interpretation.by-matrix).  Every check is `refl` on one boolean
-- (`Same`), computed on the row-operation reading (Evaluation).
--
-- The relators are named rather than inlined so that these checks and
-- the soundness proof that uses them cannot drift apart.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford+CS.Soundness.Relators where

open import Data.Bool using (true)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Interpretation
open import Examples.Groups.Clifford+CS.Semantics.Decide using (eqM ; eqM-sound ; ≡-eqM)
open import Examples.Groups.Clifford+CS.Evaluation using (⟦_⟧R ; ⟦⟧R≡⟦⟧M)

------------------------------------------------------------------------
-- The relators, at the width each is written for

-- The scalar: no wires.
rIˡ rIʳ : Circuit 0
rIˡ = iI • iI • iI • iI
rIʳ = ε

-- One wire.
rSˡ rSʳ rKˡ rKʳ rSKˡ rSKʳ : Circuit 1
rSˡ  = S • S • S • S
rSʳ  = ε
rKˡ  = K • K
rKʳ  = iI • iI • iI
rSKˡ = S • K • S • K • S • K
rSKʳ = iI • iI • iI

-- Two wires.
rCSˡ rCSʳ rS₀ˡ rS₀ʳ rS₁ˡ rS₁ʳ rX₀ˡ rX₀ʳ rX₁ˡ rX₁ʳ rK₀ˡ rK₀ʳ rK₁ˡ rK₁ʳ : Circuit 2
rCSˡ = CS • CS • CS • CS
rCSʳ = ε
rS₀ˡ = CS • S
rS₀ʳ = S • CS
rS₁ˡ = CS • S ↑
rS₁ʳ = S ↑ • CS
rX₀ˡ = X • CS
rX₀ʳ = CS • CS • CS • X • S ↑
rX₁ˡ = X ↑ • CS
rX₁ʳ = CS • CS • CS • X ↑ • S
rK₀ˡ = CS • K • CS • K • S
rK₀ʳ = S • K • CS • K • CS
rK₁ˡ = CS • K ↑ • CS • K ↑ • S ↑
rK₁ʳ = S ↑ • K ↑ • CS • K ↑ • CS

-- Three wires.
rCCˡ rCCʳ r266ˡ r266ʳ r267ˡ r267ʳ r268ˡ r268ʳ r269ˡ r269ʳ r272ˡ r272ʳ : Circuit 3
rCCˡ  = CS ↑ • CS
rCCʳ  = CS • CS ↑
r266ˡ = CX₁₀ • CX₀₁ • CS ↑ • CX₀₁ • CX₁₀
r266ʳ = CX₁₂ • CX₂₁ • CS • CX₂₁ • CX₁₂
r267ˡ = CX₁₀ • CX₀₁ • CS ↑ • CS ↑ • CX₀₁ • CX₁₀
r267ʳ = CX₀₁ • CS ↑ • CS ↑ • CX₀₁ • CS ↑ • CS ↑
r268ˡ = CS ↑ • CX₀₁ • CS ↑ • CS ↑ • CS ↑ • CX₀₁
r268ʳ = CS • CX₂₁ • CS • CS • CS • CX₂₁
r269ˡ = CS ↑ • K ↑ • CS ↑ • K ↑ • CS • K ↑ • CS
r269ʳ = CS • K ↑ • CS • K ↑ • CS ↑ • K ↑ • CS ↑
r272ˡ = CS ↑ • K ↑ • CS ↑ • CS ↑ • CS ↑ • K ↑ • CS • K ↑ • CS ↑
r272ʳ = CS • K ↑ • CS • CS • CS • K ↑ • CS ↑ • K ↑ • CS

-- Four wires.
rΔˡ rΔʳ : Circuit 4
rΔˡ = CX₁₀ ↑ ↑ • CCZ • CX₁₀ ↑ ↑
rΔʳ = CCZ • Swap ↑ ↑ • CCZ • Swap ↑ ↑

rΛˡ rΛʳ : Circuit 4
rΛˡ = Toff • CCZ₀₁₃ • Toff
rΛʳ = CCZ₀₁₃ • CCZ ↑

------------------------------------------------------------------------
-- The identities

-- Both sides denote the same matrix over ℤ[½,i], decided by one boolean
-- (Semantics.Decide) on the row-operation reading (Evaluation).
Same : ∀ {k} → Circuit k → Circuit k → Set
Same u v = eqM (scaleM (γ^ len v) ⟦ u ⟧R) (scaleM (γ^ len u) ⟦ v ⟧R) ≡ true

-- The equation of stored matrices it decides, and back.  The words are
-- explicit: `Same` is a function, so they cannot be read back off its
-- type.
same-≡ : ∀ {k} (u v : Circuit k) → Same u v → scaleM (γ^ len v) ⟦ u ⟧M ≡ scaleM (γ^ len u) ⟦ v ⟧M
same-≡ u v e =
  Eq.subst₂ (λ A B → scaleM (γ^ len v) A ≡ scaleM (γ^ len u) B) (⟦⟧R≡⟦⟧M u) (⟦⟧R≡⟦⟧M v)
            (eqM-sound _ _ e)

≡-same : ∀ {k} (u v : Circuit k) → scaleM (γ^ len v) ⟦ u ⟧M ≡ scaleM (γ^ len u) ⟦ v ⟧M → Same u v
≡-same u v e =
  ≡-eqM (Eq.subst₂ (λ A B → scaleM (γ^ len v) A ≡ scaleM (γ^ len u) B)
                   (Eq.sym (⟦⟧R≡⟦⟧M u)) (Eq.sym (⟦⟧R≡⟦⟧M v)) e)

mI : Same rIˡ rIʳ
mI = Eq.refl

mS : Same rSˡ rSʳ
mS = Eq.refl

mK : Same rKˡ rKʳ
mK = Eq.refl

mSK : Same rSKˡ rSKʳ
mSK = Eq.refl

mCS : Same rCSˡ rCSʳ
mCS = Eq.refl

mS₀ : Same rS₀ˡ rS₀ʳ
mS₀ = Eq.refl

mS₁ : Same rS₁ˡ rS₁ʳ
mS₁ = Eq.refl

mX₀ : Same rX₀ˡ rX₀ʳ
mX₀ = Eq.refl

mX₁ : Same rX₁ˡ rX₁ʳ
mX₁ = Eq.refl

mK₀ : Same rK₀ˡ rK₀ʳ
mK₀ = Eq.refl

mK₁ : Same rK₁ˡ rK₁ʳ
mK₁ = Eq.refl

mCC : Same rCCˡ rCCʳ
mCC = Eq.refl

m266 : Same r266ˡ r266ʳ
m266 = Eq.refl

m267 : Same r267ˡ r267ʳ
m267 = Eq.refl

m268 : Same r268ˡ r268ʳ
m268 = Eq.refl

m269 : Same r269ˡ r269ʳ
m269 = Eq.refl

m272 : Same r272ˡ r272ʳ
m272 = Eq.refl

mΔ : Same rΔˡ rΔʳ
mΔ = Eq.refl

mΛ : Same rΛˡ rΛʳ
mΛ = Eq.refl

------------------------------------------------------------------------
-- The relators, padded to any width, are the axioms' words

private
  variable
    n : ℕ

pIˡ : rIˡ ↓ᵏ n ≡ iI • iI • iI • iI
pIˡ = Eq.refl
pIʳ : rIʳ ↓ᵏ n ≡ ε {Gen n}
pIʳ = Eq.refl

pSˡ : rSˡ ↓ᵏ n ≡ S • S • S • S
pSˡ = Eq.refl
p1ʳ : rSʳ ↓ᵏ n ≡ ε {Gen (₁₊ n)}
p1ʳ = Eq.refl
pKˡ : rKˡ ↓ᵏ n ≡ K • K
pKˡ = Eq.refl
pKʳ : rKʳ ↓ᵏ n ≡ iI • iI • iI
pKʳ = Eq.refl
pSKˡ : rSKˡ ↓ᵏ n ≡ S • K • S • K • S • K
pSKˡ = Eq.refl

pCSˡ : rCSˡ ↓ᵏ n ≡ CS • CS • CS • CS
pCSˡ = Eq.refl
p2ʳ : rCSʳ ↓ᵏ n ≡ ε {Gen (₂₊ n)}
p2ʳ = Eq.refl
pS₀ˡ : rS₀ˡ ↓ᵏ n ≡ CS • S
pS₀ˡ = Eq.refl
pS₀ʳ : rS₀ʳ ↓ᵏ n ≡ S • CS
pS₀ʳ = Eq.refl
pS₁ˡ : rS₁ˡ ↓ᵏ n ≡ CS • S ↑
pS₁ˡ = Eq.refl
pS₁ʳ : rS₁ʳ ↓ᵏ n ≡ S ↑ • CS
pS₁ʳ = Eq.refl
pX₀ˡ : rX₀ˡ ↓ᵏ n ≡ X • CS
pX₀ˡ = Eq.refl
pX₀ʳ : rX₀ʳ ↓ᵏ n ≡ CS • CS • CS • X • S ↑
pX₀ʳ = Eq.refl
pX₁ˡ : rX₁ˡ ↓ᵏ n ≡ X ↑ • CS
pX₁ˡ = Eq.refl
pX₁ʳ : rX₁ʳ ↓ᵏ n ≡ CS • CS • CS • X ↑ • S
pX₁ʳ = Eq.refl
pK₀ˡ : rK₀ˡ ↓ᵏ n ≡ CS • K • CS • K • S
pK₀ˡ = Eq.refl
pK₀ʳ : rK₀ʳ ↓ᵏ n ≡ S • K • CS • K • CS
pK₀ʳ = Eq.refl
pK₁ˡ : rK₁ˡ ↓ᵏ n ≡ CS • K ↑ • CS • K ↑ • S ↑
pK₁ˡ = Eq.refl
pK₁ʳ : rK₁ʳ ↓ᵏ n ≡ S ↑ • K ↑ • CS • K ↑ • CS
pK₁ʳ = Eq.refl

pCCˡ : rCCˡ ↓ᵏ n ≡ CS ↑ • CS
pCCˡ = Eq.refl
pCCʳ : rCCʳ ↓ᵏ n ≡ CS • CS ↑
pCCʳ = Eq.refl
p266ˡ : r266ˡ ↓ᵏ n ≡ CX₁₀ • CX₀₁ • CS ↑ • CX₀₁ • CX₁₀
p266ˡ = Eq.refl
p266ʳ : r266ʳ ↓ᵏ n ≡ CX₁₂ • CX₂₁ • CS • CX₂₁ • CX₁₂
p266ʳ = Eq.refl
p267ˡ : r267ˡ ↓ᵏ n ≡ CX₁₀ • CX₀₁ • CS ↑ • CS ↑ • CX₀₁ • CX₁₀
p267ˡ = Eq.refl
p267ʳ : r267ʳ ↓ᵏ n ≡ CX₀₁ • CS ↑ • CS ↑ • CX₀₁ • CS ↑ • CS ↑
p267ʳ = Eq.refl
p268ˡ : r268ˡ ↓ᵏ n ≡ CS ↑ • CX₀₁ • CS ↑ • CS ↑ • CS ↑ • CX₀₁
p268ˡ = Eq.refl
p268ʳ : r268ʳ ↓ᵏ n ≡ CS • CX₂₁ • CS • CS • CS • CX₂₁
p268ʳ = Eq.refl
p269ˡ : r269ˡ ↓ᵏ n ≡ CS ↑ • K ↑ • CS ↑ • K ↑ • CS • K ↑ • CS
p269ˡ = Eq.refl
p269ʳ : r269ʳ ↓ᵏ n ≡ CS • K ↑ • CS • K ↑ • CS ↑ • K ↑ • CS ↑
p269ʳ = Eq.refl
p272ˡ : r272ˡ ↓ᵏ n ≡ CS ↑ • K ↑ • CS ↑ • CS ↑ • CS ↑ • K ↑ • CS • K ↑ • CS ↑
p272ˡ = Eq.refl
p272ʳ : r272ʳ ↓ᵏ n ≡ CS • K ↑ • CS • CS • CS • K ↑ • CS ↑ • K ↑ • CS
p272ʳ = Eq.refl

pΔˡ : rΔˡ ↓ᵏ n ≡ CX₁₀ ↑ ↑ • CCZ • CX₁₀ ↑ ↑
pΔˡ = Eq.refl
pΔʳ : rΔʳ ↓ᵏ n ≡ CCZ • Swap ↑ ↑ • CCZ • Swap ↑ ↑
pΔʳ = Eq.refl

pΛˡ : rΛˡ ↓ᵏ n ≡ Toff • CCZ₀₁₃ • Toff
pΛˡ = Eq.refl
pΛʳ : rΛʳ ↓ᵏ n ≡ CCZ₀₁₃ • CCZ ↑
pΛʳ = Eq.refl
