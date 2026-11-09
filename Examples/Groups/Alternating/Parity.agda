------------------------------------------------------------------------
-- Presentations of groups
--
-- The sign of a permutation, through the circuit presentation of Sₙ.
--
-- Lafont calls a permutation even when it is a product of an even
-- number of transpositions.  The circuits of Examples.Groups.Symmetric
-- are products of adjacent transpositions, and each of their relations
-- relates two words whose lengths have the same parity (parity-sound).
-- So the parity of a circuit is an invariant of the permutation it
-- denotes, and the sign of a permutation is the parity of any circuit
-- realising it (sign-of): one exists by Symmetric's Surjectivity, and
-- any two are congruent by its completeness (Lafont's Theorem 1).
-- The usual laws follow from those of words: the sign of a composite
-- is the xor of the signs, the identity is even, and so on.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Alternating.Parity where

open import Data.Bool using (Bool ; true ; false ; _xor_)
open import Data.Bool.Properties using (xor-assoc ; xor-identityʳ)
open import Data.Fin.Permutation
  using ( Permutation′ ; _⟨$⟩ʳ_ ; _∘ₚ_ ; id ; flip ; lift₀ ; lift₀-cong
        ; inverseˡ )
  renaming (_≈_ to _≈ₚ_)
open import Data.Nat using (ℕ)
open import Data.Product using (proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong ; cong₂)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; wmap)

import Presentation.Base as PB

import Examples.Groups.Symmetric.Completeness as SComp
import Examples.Groups.Symmetric.Interpretation as SInt
import Examples.Groups.Symmetric.Surjectivity as SSurj
import Examples.Groups.Symmetric.Syntactics as S

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- The parity of a word

-- Whether the length of a word is odd.
parity : ∀ {A : Set} → Word A → Bool
parity [ _ ]ʷ  = true
parity ε       = false
parity (w • v) = parity w xor parity v

parity-wmap : ∀ {A B : Set} (f : A → B) (w : Word A) →
              parity (wmap f w) ≡ parity w
parity-wmap f [ _ ]ʷ  = refl
parity-wmap f ε       = refl
parity-wmap f (w • v) = cong₂ _xor_ (parity-wmap f w) (parity-wmap f v)

------------------------------------------------------------------------
-- Congruent circuits of transpositions have the same parity

parity-ax : ∀ {w v : S.Circuit n} → S._VRel,_===_ n w v →
            parity w ≡ parity v
parity-ax (S.srel S.order)                = refl
parity-ax (S.srel S.yang-baxter)          = refl
parity-ax (S.cong↑ {_} {w} {v} p)         =
  trans (parity-wmap _ w) (trans (parity-ax p) (sym (parity-wmap _ v)))
parity-ax (S.comm₂ S.σ-gate g)            = refl

parity-sound : ∀ {w v : S.Circuit n} → PB._≈_ (S._VRel,_===_ n) w v →
               parity w ≡ parity v
parity-sound PB.refl                    = refl
parity-sound (PB.sym p)                 = sym (parity-sound p)
parity-sound (PB.trans p q)             =
  trans (parity-sound p) (parity-sound q)
parity-sound (PB.cong p q)              =
  cong₂ _xor_ (parity-sound p) (parity-sound q)
parity-sound (PB.assoc {w} {v} {u})     =
  xor-assoc (parity w) (parity v) (parity u)
parity-sound PB.left-unit               = refl
parity-sound (PB.right-unit {w})        = xor-identityʳ (parity w)
parity-sound (PB.axiom a)               = parity-ax a

------------------------------------------------------------------------
-- The sign of a permutation

-- The parity of the circuit that Symmetric's Surjectivity builds.
sign : Permutation′ n → Bool
sign {n} π = parity (proj₁ (SSurj.go n π))

-- Every circuit realising π has the parity of its sign.
sign-of : (w : S.Circuit n) (π : Permutation′ n) →
          (∀ k → SInt.⟦ w ⟧ ⟨$⟩ʳ k ≡ π ⟨$⟩ʳ k) → sign π ≡ parity w
sign-of {n} w π w≈π =
  parity-sound (SComp.completeness {n} {proj₁ (SSurj.go n π)} {w} λ k →
    trans (proj₂ (SSurj.go n π) k) (sym (w≈π k)))

sign-cong : ∀ {π ρ : Permutation′ n} → π ≈ₚ ρ → sign π ≡ sign ρ
sign-cong {n} {π} {ρ} π≈ρ = sign-of wρ π λ k →
  trans (proj₂ (SSurj.go n ρ) k) (sym (π≈ρ k))
  where wρ = proj₁ (SSurj.go n ρ)

sign-∘ : (π ρ : Permutation′ n) → sign (π ∘ₚ ρ) ≡ sign π xor sign ρ
sign-∘ {n} π ρ = sign-of (wπ • wρ) (π ∘ₚ ρ) λ k →
  trans (proj₂ (SSurj.go n ρ) (SInt.⟦ wπ ⟧ ⟨$⟩ʳ k))
        (cong (ρ ⟨$⟩ʳ_) (proj₂ (SSurj.go n π) k))
  where
  wπ = proj₁ (SSurj.go n π)
  wρ = proj₁ (SSurj.go n ρ)

sign-id : sign (id {n}) ≡ false
sign-id {n} = sign-of {n} ε id λ _ → refl

private
  xor-false : ∀ x y → x xor y ≡ false → y ≡ x
  xor-false false false _ = refl
  xor-false true  true  _ = refl
  xor-false false true  ()
  xor-false true  false ()

sign-flip : (π : Permutation′ n) → sign (flip π) ≡ sign π
sign-flip {n} π = xor-false (sign π) (sign (flip π))
  (trans (sym (sign-∘ π (flip π)))
         (trans (sign-cong {π = π ∘ₚ flip π} {ρ = id} λ _ → inverseˡ π)
                (sign-id {n})))

sign-lift₀ : (π : Permutation′ n) → sign (lift₀ π) ≡ sign π
sign-lift₀ {n} π = trans (sign-of (wπ S.↑) (lift₀ π) λ k →
    trans (SInt.⟦↑⟧ wπ k)
          (lift₀-cong SInt.⟦ wπ ⟧ π (proj₂ (SSurj.go n π)) k))
  (parity-wmap (S._↥ᵏ 1) wπ)
  where wπ = proj₁ (SSurj.go n π)
