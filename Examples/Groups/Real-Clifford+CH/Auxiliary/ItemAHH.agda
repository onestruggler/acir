------------------------------------------------------------------------
-- Presentations of groups
--
-- Item (a) of the Reidemeister–Schreier method, in full
--
-- `ItemA` proves the condition for the three Hadamard-free letter
-- shapes and leaves the Hadamard one as a hypothesis.  That shape is
-- exactly Figure 10's (71) at the two distinguished indices: the
-- action sends H_[a,b] from the identity coset to H_[a,b] H_[0,1] and
-- then H_[c,d] from ⟨K⟩ to H_[0,1] H_[c,d], so what has to be shown is
--
--     H_[a,b] H_[c,d]  ≈  (H_[a,b] H_[0,1]) (H_[0,1] H_[c,d]),
--
-- with no side condition beyond the two the letter carries.  `Fuse`
-- proves (71) in that generality, so item (a) is complete here.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.ItemAHH (m : ℕ) where

open import Data.Empty using (⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat using () renaming (_^_ to _^ℕ_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Word.Base using (Word ; _•_ ; _ᵗ ; [_]ʷ)

open import Notations using (₃₊)

import Presentation.Base as PB

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Cosets
  using (Coset ; ⟨ε⟩ ; ⟨K⟩)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8 using (_P,_===_)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP ; HH ; asG)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.RS m
  using (act ; z₀ ; o₁ ; z₀≢o₁)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Theorem410 m as T410
  using (Item-a ; Item-b ; module RS)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.ItemA m
  using (Item-a-HH ; run₂) renaming (item-a to item-a-of)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.LowGens m using (gen-hh)
open import Examples.Groups.Real-Clifford+CH.Encoding using (hh)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure10 m using (Eq65)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Fuse m using (fuse)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)

import Examples.Groups.Real-Clifford+CH.Auxiliary.Syntactics as G
open G using (H[_,_])

open Tools (m P,_===_)

private
  N : ℕ
  N = 2 ^ℕ (₃₊ m)

  Wᴾ : Set
  Wᴾ = Word (GenP (₃₊ m))

  refl≡ : ∀ {u v : Wᴾ} → u ≡ v → u ≈ v
  refl≡ Eq.refl = refl

------------------------------------------------------------------------
-- The two steps of the traversal
--
-- Computed once, as in `ItemA`: a `with` in a proof does not reduce a
-- stuck call to the action.

act-ε-H : ∀ (a b : Fin N) (ne : a ≢ b) →
          act ⟨ε⟩ H[ a , b ] ≡ ([ HH {₃₊ m} a b z₀ o₁ ne z₀≢o₁ ]ʷ , ⟨K⟩)
act-ε-H a b ne with a ≟ b
... | yes e = ⊥-elim (ne e)
... | no  _ = Eq.refl

act-K-H : ∀ (c d : Fin N) (ne : c ≢ d) →
          act ⟨K⟩ H[ c , d ] ≡ ([ HH {₃₊ m} z₀ o₁ c d z₀≢o₁ ne ]ʷ , ⟨ε⟩)
act-K-H c d ne with c ≟ d
... | yes e = ⊥-elim (ne e)
... | no  _ = Eq.refl

------------------------------------------------------------------------
-- The Hadamard shape, and item (a)

module _ (e65 : Eq65) where

  item-a-hh : Item-a-HH
  item-a-hh a b c d ni ni′ = go (a ≟ b) (c ≟ d)
    where
    Goal : Set
    Goal = RS._~_ ([ HH {₃₊ m} a b c d ni ni′ ]ʷ , ⟨ε⟩)
                  ((act ᵗ) ⟨ε⟩ (asG {₃₊ m} (HH {₃₊ m} a b c d ni ni′)))

    go : Dec (a ≡ b) → Dec (c ≡ d) → Goal
    go (yes e) _        = ⊥-elim-irr (ni e)
    go (no _)  (yes e)  = ⊥-elim-irr (ni′ e)
    go (no ne) (no ne′) =
      Eq.subst (RS._~_ ([ HH {₃₊ m} a b c d ni ni′ ]ʷ , ⟨ε⟩))
               (Eq.sym (run₂ H[ a , b ] H[ c , d ]
                          ([ HH {₃₊ m} a b z₀ o₁ ne z₀≢o₁ ]ʷ)
                          ([ HH {₃₊ m} z₀ o₁ c d z₀≢o₁ ne′ ]ʷ) ⟨K⟩ ⟨ε⟩
                          (act-ε-H a b ne) (act-K-H c d ne′)))
               (goal , Eq.refl)
      where
      -- (71) at the two distinguished indices, with the letters
      -- decided back into the shape the action produced.
      goal : [ HH {₃₊ m} a b c d ni ni′ ]ʷ
             ≈ [ HH {₃₊ m} a b z₀ o₁ ne z₀≢o₁ ]ʷ
               • [ HH {₃₊ m} z₀ o₁ c d z₀≢o₁ ne′ ]ʷ
      goal =
        trans (refl≡ (gen-hh a b c d ni ni′))
        (trans (sym (fuse e65 a b z₀ o₁ c d ne z₀≢o₁ ne′))
               (refl≡ (Eq.cong₂ _•_ (Eq.sym (gen-hh a b z₀ o₁ ne z₀≢o₁))
                                    (Eq.sym (gen-hh z₀ o₁ c d z₀≢o₁ ne′)))))

  -- So item (a) holds outright.
  item-a : Item-a
  item-a = item-a-of item-a-hh

  -- And Theorem 4.10 is then item (b) away: `Complete` exports the
  -- Reidemeister–Schreier conclusion, `(f ʷ)` injective modulo the two
  -- presentations, which with Theorem 4.4 is completeness of Figure 8
  -- for the alphabet P (`Theorem410Proof`, where item (b) is given).
  module Complete (item-b : Item-b) = T410.Complete item-a item-b
