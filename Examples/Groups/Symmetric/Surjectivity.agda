------------------------------------------------------------------------
-- Presentations of groups
--
-- Surjectivity of the permutation semantics of Sₙ: every permutation of
-- Fin n is the denotation of some circuit.
--
-- This is the one input to the presentation theorem that normalization
-- does not supply.  Presentation assembles a SUB-presentation out of
-- soundness, grouplike, the coset normal form and its uniqueness; what
-- it then needs to promote that to a presentation is exactly this
-- module, which is why the two are separated (Symplectic splits its
-- Presentation / Surjectivity the same way).
--
-- The construction is by induction on the width.  Given π on ₁₊ m, read
-- off where it sends wire 0 and write that as a coset representative r;
-- dividing ρ_r out of π fixes wire 0, so that wire can be removed and
-- the remaining permutation handled by the recursive call.  The witness
-- is w' ↑ • [ r ]ᶜ -- the shape of the coset normal form, which is why
-- surjectivity of the semantics and surjectivity of the normal form are
-- the same construction here.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Symmetric.Surjectivity where

open import Algebra.Bundles using (Group)
open import Data.Fin using (Fin)
open import Data.Fin.Permutation
  using ( Permutation′ ; _⟨$⟩ʳ_ ; _⟨$⟩ˡ_ ; _∘ₚ_ ; flip
        ; inverseˡ ; inverseʳ ; lift₀-cong ; remove ; lift₀-remove )
open import Data.Nat using (zero ; suc)
open import Data.Product using (∃ ; _,_ ; proj₁ ; proj₂)
open import Function.Definitions using (Surjective)
open import Notations
open import Word.Base

import Data.Fin as F
import Presentation.Base as PB
import Relation.Binary.PropositionalEquality as Eq

open Eq using (_≡_ ; refl)

open import Examples.Groups.Symmetric.Cosets
open import Examples.Groups.Symmetric.Interpretation
open import Examples.Groups.Symmetric.Semantics
open import Examples.Groups.Symmetric.Soundness
open import Examples.Groups.Symmetric.Syntactics

------------------------------------------------------------------------
-- Coset representatives and the wire they send 0 to

-- A coset of Sₘ in Sₘ₊₁ is named by where it sends wire 0, so C m and
-- Fin (₁₊ m) are in bijection.  Both directions are needed: fin-to-C to
-- build the witness, depth to see that it was the right one.
fin-to-C : ∀ {m} → Fin (₁₊ m) → C m
fin-to-C        F.zero    = ε
fin-to-C {₁₊ m} (F.suc j) = σ• (fin-to-C j)

depth : ∀ {m} → C m → Fin (₁₊ m)
depth ε      = F.zero
depth (σ• c) = F.suc (depth c)

depth-fin-to-C : ∀ {m} (j : Fin (₁₊ m)) → depth (fin-to-C j) ≡ j
depth-fin-to-C        F.zero    = refl
depth-fin-to-C {₁₊ m} (F.suc j) = Eq.cong F.suc (depth-fin-to-C j)

-- The representative's circuit does send wire 0 where its name says.
⟦[r]ᶜ⟧-zero : ∀ {m} (r : C m) → ⟦ [ r ]ᶜ ⟧ ⟨$⟩ʳ F.zero ≡ depth r
⟦[r]ᶜ⟧-zero ε      = refl
⟦[r]ᶜ⟧-zero (σ• c) =
  Eq.trans (⟦↑⟧ ([ c ]ᶜ) (F.suc F.zero))
           (Eq.cong F.suc (⟦[r]ᶜ⟧-zero c))

------------------------------------------------------------------------
-- Every permutation is realised by a circuit

-- go m π gives a circuit denoting π pointwise.  At width ₁₊ m: r names
-- π's action on wire 0, χ = π ∘ₚ flip ρ_r therefore fixes wire 0, and
-- ρ' = remove F.zero χ is what the induction hypothesis applies to.
go : ∀ m (π : Permutation′ m) → ∃ λ w → ∀ k → ⟦ w ⟧ ⟨$⟩ʳ k ≡ π ⟨$⟩ʳ k
go 0       π = ε , λ ()
go (suc m) π = w' ↑ • [ r ]ᶜ , correct
  where
  j      = π ⟨$⟩ʳ F.zero
  r      = fin-to-C j
  ρ_r    = ⟦ [ r ]ᶜ ⟧
  χ      = π ∘ₚ flip ρ_r
  ρ_r-eq : ρ_r ⟨$⟩ʳ F.zero ≡ j
  ρ_r-eq = Eq.trans (⟦[r]ᶜ⟧-zero r) (depth-fin-to-C j)
  χ₀     : χ ⟨$⟩ʳ F.zero ≡ F.zero
  χ₀     = Eq.subst (λ x → ρ_r ⟨$⟩ˡ x ≡ F.zero) ρ_r-eq (inverseˡ ρ_r)
  ρ'     = remove F.zero χ
  rec    = go m ρ'
  w'     = rec .proj₁
  ih     = rec .proj₂
  correct : ∀ k → ⟦ (w' ↑) • [ r ]ᶜ ⟧ ⟨$⟩ʳ k ≡ π ⟨$⟩ʳ k
  correct k =
    Eq.trans
      (Eq.cong (ρ_r ⟨$⟩ʳ_)
        (Eq.trans (⟦↑⟧ w' k)
        (Eq.trans (lift₀-cong ⟦ w' ⟧ ρ' ih k)
                  (lift₀-remove χ χ₀ k))))
      (inverseʳ ρ_r)

------------------------------------------------------------------------
-- Surjectivity of ⟦_⟧

-- The realiser of go, packaged as the surjectivity of the semantics:
-- any word congruent to it has the same denotation, by soundness.
surjective : ∀ {n} → let open PB (n VRel,_===_) in
  Surjective _≈_ (Group._≈_ (Permutation′-group n)) ⟦_⟧
surjective {n} y = let w , ih = go n y
                   in w , λ {z} z≈w k → Eq.trans (sound z≈w k) (ih k)
