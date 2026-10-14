------------------------------------------------------------------------
-- Presentations of groups
--
-- Item (b) of the Reidemeister–Schreier method, the K-free rules
--
-- Item (b) asks that the coset action respect every rule of the
-- two-level presentation at every coset: the two sides, traversed
-- from the same coset, emit equivalent words and land in the same
-- coset.  The cosets agree for every rule, its two sides having the
-- same degree mod 4 (`cos-rule`).  For the eight K-free rules — the
-- orders of i and X, the commutations among phases and exchanges, and
-- the swap relations of X — the words agree too: each rule holds for
-- phased permutations (`spT-sound`), the traversals read as the sides
-- conjugated by the same powers of i_[0] (`ActionFree.run`), and
-- Corollary A.5's analogue does the rest, uniformly in the coset and
-- in where the indices meet 0.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; suc ; _≤_)

module Examples.Groups.Clifford+CS.Auxiliary.ItemBFree
  (N′ : ℕ) (big : 16 ≤ suc N′) where

open import Data.Fin using (Fin)
open import Data.Fin.Properties using (<⇒≢)
open import Data.Nat.Properties using (<-trans)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; _ᵗ)

import Examples.Groups.Clifford+CS-TwoLevel.Syntactics as TL
open TL using (_===_)
open _===_

open import Examples.Groups.Clifford+CS.Auxiliary.Rules using (free⇒full-≈)
open import Examples.Groups.Clifford+CS.Auxiliary.Cosets using (Coset ; ⟨0⟩ ; ⟨1⟩ ; ⟨2⟩ ; ⟨3⟩ ; inc)
open import Examples.Groups.Clifford+CS.Auxiliary.CosetAction N′ big
  using (act ; cos ; run-cos)
open import Examples.Groups.Clifford+CS.Auxiliary.ActionFree N′ big
  using (spT ; KFreeT ; ρ ; ρ⁻ ; run ; run-kf)
open import Examples.Groups.Clifford+CS.Auxiliary.PhasedPerm (suc N′)
  using (PP ; idPP ; _⊙_ ; _≐_ ; ≐-refl ; ≐-sym ; ≐-trans ; ⊙-cong ; ⊙-idˡ
       ; ⊙-assoc ; ≡⇒≐ ; ph≡≐ ; swp≡ ; PH ; SWP ; PH-id ; PH-fuse ; PH-comm
       ; PH-SWP ; SWP-invol ; SWP-conj ; SWP-comm ; swapF-b ; swapF-o
       ; p0 ; p1 ; p2 ; p3 ; sp)
open import Examples.Groups.Clifford+CS.Auxiliary.Unique N′ using (A5)
open import Examples.Groups.Clifford+CS.Auxiliary.RS N′ big using (module RSF)

private
  N : ℕ
  N = suc N′

  ≢sym : ∀ {x y : Fin N} → x ≢ y → y ≢ x
  ≢sym ne e = ne (Eq.sym e)

------------------------------------------------------------------------
-- The cosets agree

inc⁴ : ∀ (c : Coset) → inc (inc (inc (inc c))) ≡ c
inc⁴ ⟨0⟩ = Eq.refl
inc⁴ ⟨1⟩ = Eq.refl
inc⁴ ⟨2⟩ = Eq.refl
inc⁴ ⟨3⟩ = Eq.refl

-- Both sides of a rule have the same degree mod 4.
cos-rule : ∀ (c : Coset) {u t : Word (TL.Gen N)} → u === t → cos c u ≡ cos c t
cos-rule c order-i              = inc⁴ c
cos-rule c (order-X _)          = inc⁴ c
cos-rule c (order-K _)          = Eq.trans (inc⁴ (inc (inc (inc (inc c))))) (inc⁴ c)
cos-rule c (comm-ii _)          = Eq.refl
cos-rule c (comm-iX _ _ _)      = Eq.refl
cos-rule c (comm-iK _ _ _)      = Eq.refl
cos-rule c (comm-XX _ _ _ _ _ _) = Eq.refl
cos-rule c (comm-XK _ _ _ _ _ _) = Eq.refl
cos-rule c (comm-KK _ _ _ _ _ _) = Eq.refl
cos-rule c (swap-iX _)          = Eq.refl
cos-rule c (swap-XX _ _)        = Eq.refl
cos-rule c (swap-XX′ _ _)       = Eq.refl
cos-rule c (swap-KX _ _)        = Eq.refl
cos-rule c (swap-KX′ _ _)       = Eq.refl
cos-rule c (rel-13 _)           = Eq.refl
cos-rule c (rel-14 _)           = Eq.refl
cos-rule c (rel-15 _)           = Eq.refl
cos-rule c (rel-16 _)           = inc⁴ c
cos-rule c (rel-17 _ _ _ _ _)   = Eq.refl

------------------------------------------------------------------------
-- The K-free rules hold for phased permutations

spT-sound : ∀ {u t : Word (TL.Gen N)} → u === t → KFreeT u → spT u ≐ spT t
spT-sound (order-i {j = j}) _ =
  ≐-trans (⊙-cong (≐-refl {PH j p1})
                  (≐-trans (⊙-cong (≐-refl {PH j p1}) (PH-fuse j p1 p1))
                           (PH-fuse j p1 p2)))
          (≐-trans (PH-fuse j p1 p3) (PH-id j))
spT-sound (order-X {j = j} {k = k} _) _ = SWP-invol j k
spT-sound (comm-ii {j = j} {k = k} _) _ = PH-comm j k p1 p1
spT-sound (comm-iX {k = k} {l = l} {j = j} _ jk jl) _ =
  ≐-trans (PH-SWP j p1 k l)
          (⊙-cong (≐-refl {SWP k l}) (ph≡≐ (swapF-o k l j jk jl)))
spT-sound (comm-XX {j = j} {k = k} {l = l} {m = m} _ _ jl jm kl km) _ =
  SWP-comm j k l m (≢sym jl) (≢sym kl) (≢sym jm) (≢sym km)
spT-sound (swap-iX {j = j} {k = k} _) _ =
  ≐-trans (PH-SWP k p1 j k)
          (⊙-cong (≐-refl {SWP j k}) (ph≡≐ (swapF-b j k)))
spT-sound (swap-XX {j = j} {k = k} {l = l} p q) _ = begin′
  where
  lj : l ≢ j
  lj = ≢sym (<⇒≢ (<-trans p q))

  lk : l ≢ k
  lk = ≢sym (<⇒≢ q)

  begin′ : SWP k l ⊙ SWP j k ≐ SWP j k ⊙ SWP j l
  begin′ =
    ≐-trans (≐-sym (⊙-idˡ (SWP k l ⊙ SWP j k)))
    (≐-trans (⊙-cong (≐-sym (SWP-invol j k)) (≐-refl {SWP k l ⊙ SWP j k}))
    (≐-trans (⊙-assoc (SWP j k) (SWP j k) (SWP k l ⊙ SWP j k))
    (⊙-cong (≐-refl {SWP j k})
            (≐-trans (SWP-conj j k k l)
                     (swp≡ (swapF-b j k) (swapF-o j k l lj lk))))))
spT-sound (swap-XX′ {j = j} {k = k} {l = l} p q) _ = begin′
  where
  jk : j ≢ k
  jk = <⇒≢ p

  jl : j ≢ l
  jl = <⇒≢ (<-trans p q)

  begin′ : SWP j l ⊙ SWP k l ≐ SWP k l ⊙ SWP j k
  begin′ =
    ≐-trans (≐-sym (⊙-idˡ (SWP j l ⊙ SWP k l)))
    (≐-trans (⊙-cong (≐-sym (SWP-invol k l)) (≐-refl {SWP j l ⊙ SWP k l}))
    (≐-trans (⊙-assoc (SWP k l) (SWP k l) (SWP j l ⊙ SWP k l))
    (⊙-cong (≐-refl {SWP k l})
            (≐-trans (SWP-conj k l j l)
                     (swp≡ (swapF-o k l j jk jl) (swapF-b k l))))))
spT-sound (order-K _)            (() , _)
spT-sound (comm-iK _ _ _)        (_ , ())
spT-sound (comm-XK _ _ _ _ _ _)  (_ , ())
spT-sound (comm-KK _ _ _ _ _ _)  (() , _)
spT-sound (swap-KX _ _)          (() , _)
spT-sound (swap-KX′ _ _)         (() , _)
spT-sound (rel-13 _)             (() , _)
spT-sound (rel-14 _)             (() , _)
spT-sound (rel-15 _)             (() , _)
spT-sound (rel-16 _)             ((() , _) , _)
spT-sound (rel-17 _ _ _ _ _)     (() , _)

------------------------------------------------------------------------
-- Item (b) for the K-free rules

item-b-free : ∀ (c : Coset) {u t : Word (TL.Gen N)} → u === t →
              KFreeT u → KFreeT t →
              RSF._~_ ((act ᵗ) c u) ((act ᵗ) c t)
item-b-free c {u} {t} r ku kt = word , coset
  where
  coset : proj₂ ((act ᵗ) c u) ≡ proj₂ ((act ᵗ) c t)
  coset = Eq.trans (run-cos c u) (Eq.trans (cos-rule c r) (Eq.sym (run-cos c t)))

  sem : sp (proj₁ ((act ᵗ) c u)) ≐ sp (proj₁ ((act ᵗ) c t))
  sem = ≐-trans (run c u ku)
        (≐-trans (⊙-cong (≐-refl {ρ c})
                         (⊙-cong (spT-sound r ku) (≡⇒≐ (Eq.cong ρ⁻ coset))))
                 (≐-sym (run c t kt)))

  word = free⇒full-≈ (A5 (run-kf c u ku) (run-kf c t kt) sem)
