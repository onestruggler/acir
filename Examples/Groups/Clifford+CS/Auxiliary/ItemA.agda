------------------------------------------------------------------------
-- Presentations of groups
--
-- Item (a) of the Reidemeister–Schreier method
--
-- Item (a) asks, for each letter x of P′, that reading x into the
-- two-level generators and back through the coset action from ⟨0⟩
-- returns x, at ⟨0⟩.  For the K-free letters — the phase pair, the
-- sign-exchange and the double exchange — both sides are K-free words
-- over P′, the traversal's phased permutation is the spelling's
-- (`ActionFree.run`, the conjugations by i_[0]^0 being trivial), and
-- the spelling's is the letter's; so Corollary A.5's analogue
-- (`Unique.A5`) gives the equivalence, and the coset reached is ⟨0⟩
-- because every letter has degree 0 mod 4.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; suc ; _≤_)

module Examples.Groups.Clifford+CS.Auxiliary.ItemA
  (N′ : ℕ) (big : 16 ≤ suc N′) where

open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; _ᵗ)

open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP ; asG)
open import Examples.Groups.Clifford+CS.Auxiliary.Rules using (free⇒full-≈)
open import Examples.Groups.Clifford+CS.Auxiliary.Cosets using (⟨0⟩)
open import Examples.Groups.Clifford+CS.Auxiliary.CosetAction N′ big
  using (act ; cos ; run-cos)
open import Examples.Groups.Clifford+CS.Auxiliary.ActionFree N′ big
  using (spT ; KFreeT ; ρ ; ρ⁻ ; ρ⟨0⟩ ; ρ⁻⟨0⟩ ; run ; run-kf)
open import Examples.Groups.Clifford+CS.Auxiliary.PhasedPerm (suc N′)
  using (PP ; idPP ; _⊙_ ; _≐_ ; ≐-refl ; ≐-sym ; ≐-trans ; ⊙-cong ; ⊙-idˡ
       ; ⊙-idʳ ; ⊙-assoc ; ≡⇒≐ ; PH ; SWP ; PH-fuse ; p1 ; p2 ; spg ; sp)
open import Examples.Groups.Clifford+CS.Auxiliary.NF N′
  using (KFree ; kf-pp ; kf-px ; kf-dx ; gen)
open import Examples.Groups.Clifford+CS.Auxiliary.Unique N′ using (A5)
open import Examples.Groups.Clifford+CS.Auxiliary.RS N′ big using (module RSF)

private
  N : ℕ
  N = suc N′

------------------------------------------------------------------------
-- The spelling of a K-free letter

-- It reads as the letter.
asG-sem : ∀ {x : GenP N} → KFree x → spT (asG x) ≐ spg x
asG-sem (kf-pp a b) =
  ⊙-cong (≐-refl {PH a p1})
         (≐-trans (⊙-cong (≐-refl {PH b p1}) (PH-fuse b p1 p1))
                  (PH-fuse b p1 p2))
asG-sem (kf-px c a b lt) =
  ≐-trans (≐-sym (⊙-assoc (PH c p1) (PH c p1) (SWP a b)))
          (⊙-cong (PH-fuse c p1 p1) (≐-refl {SWP a b}))
asG-sem (kf-dx a b c d ab cd) = ≐-refl

-- It has no K.
asG-kf : ∀ {x : GenP N} → KFree x → KFreeT (asG x)
asG-kf (kf-pp a b)           = tt , tt , tt , tt
asG-kf (kf-px c a b lt)      = tt , tt , tt
asG-kf (kf-dx a b c d ab cd) = tt , tt

-- It has degree 0.
asG-cos : ∀ {x : GenP N} → KFree x → cos ⟨0⟩ (asG x) ≡ ⟨0⟩
asG-cos (kf-pp a b)           = Eq.refl
asG-cos (kf-px c a b lt)      = Eq.refl
asG-cos (kf-dx a b c d ab cd) = Eq.refl

------------------------------------------------------------------------
-- Item (a) for the K-free letters

item-a-free : ∀ {x : GenP N} → KFree x →
              RSF._~_ ([ x ]ʷ , ⟨0⟩) ((act ᵗ) ⟨0⟩ (asG x))
item-a-free {x} k = word , coset
  where
  c′ = proj₂ ((act ᵗ) ⟨0⟩ (asG x))
  w′ = proj₁ ((act ᵗ) ⟨0⟩ (asG x))

  coset : ⟨0⟩ ≡ c′
  coset = Eq.sym (Eq.trans (run-cos ⟨0⟩ (asG x)) (asG-cos k))

  -- Conjugating by i_[0]^0 does nothing.
  mid : spT (asG x) ≐ ρ ⟨0⟩ ⊙ (spT (asG x) ⊙ ρ⁻ c′)
  mid = ≐-sym (≐-trans (⊙-cong ρ⟨0⟩
                         (⊙-cong (≐-refl {spT (asG x)})
                                 (≐-trans (≡⇒≐ (Eq.cong ρ⁻ (Eq.sym coset))) ρ⁻⟨0⟩)))
                       (≐-trans (⊙-idˡ (spT (asG x) ⊙ idPP)) (⊙-idʳ (spT (asG x)))))

  sem : spg x ≐ sp w′
  sem = ≐-trans (≐-sym (asG-sem k))
                (≐-trans mid (≐-sym (run ⟨0⟩ (asG x) (asG-kf k))))

  word = free⇒full-≈ (A5 (gen k) (run-kf ⟨0⟩ (asG x) (asG-kf k)) sem)
