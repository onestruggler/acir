------------------------------------------------------------------------
-- Presentations of groups
--
-- The letters of the controlled functor as placed canonical letters
--
-- Every letter of λ¹ on 5 + n wires is one of six canonical letters —
-- S on one wire, CS or CK on two, or one of the three S-boxes of
-- Five.Letters on five — placed by any network that sends the letter's
-- wires to the canonical ones (`placed`): the functor builds its letters
-- by `stretch` (an idle wire inserted below the top: a placement by the
-- exchange of the top two wires, `stretch-pl`) and `_↑` (a placement by
-- the cycle of TopWeakening, `up-pl`), and a placement depends only on
-- where the network sends the significant wires (LocalPlace.place-eq).
-- This is what reduces an equation between letters at any width to one
-- between canonical letters on a few wires.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Lambda.Placed where

open import Data.Fin using (Fin ; toℕ ; inject₁ ; fromℕ) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Nat using (ℕ ; zero ; suc ; _<_ ; s≤s ; z≤n)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

import Presentation.Base as PB
import Examples.Groups.Symmetric.Syntactics as S

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.MultiControlled using (top)
open import Examples.Groups.Clifford+CS.TopWeakening using (σ ; σ⁻¹ ; σσ⁻¹ ; nat ; top-cong)
open import Examples.Groups.Clifford+CS.PermCalc using (net ; net-↑ ; perm ; revS ; revS-↑ ; perm-inv)
open import Examples.Groups.Clifford+CS.LocalPlace using (pl ; pl-pl ; place-eq)
open import Examples.Groups.Clifford+CS.Networks using (perm-↑0 ; perm-↑s)
open import Examples.Groups.Clifford+CS.NetTop using (topS ; perm-top ; pl-top)
open import Examples.Groups.Clifford+CS.Lambda using (Swᵗ ; stretch)

private
  variable
    n k : ℕ

------------------------------------------------------------------------
-- The cycle: w ↑ is top w placed

cycS : (n : ℕ) → Word (S.Gen (₁₊ n))
cycS zero    = ε
cycS (suc n) = S.σ • cycS n S.↑

net-cyc : ∀ n → net (cycS n) ≡ σ n
net-cyc zero    = Eq.refl
net-cyc (suc n) = Eq.cong (Swap •_) (Eq.trans (net-↑ (cycS n)) (Eq.cong _↑ (net-cyc n)))

net-cyc⁻ : ∀ n → net (revS (cycS n)) ≡ σ⁻¹ n
net-cyc⁻ zero    = Eq.refl
net-cyc⁻ (suc n) =
  Eq.cong (_• Swap) (Eq.trans (Eq.cong net (revS-↑ (cycS n)))
                              (Eq.trans (net-↑ (revS (cycS n))) (Eq.cong _↑ (net-cyc⁻ n))))

up-pl : ∀ (w : Circuit n) → (₁₊ n) ⊢ w ↑ ≈ pl (cycS n) (top w)
up-pl {n} w = begin
  w ↑                           ≈⟨ sym right-unit ⟩
  w ↑ • ε                       ≈⟨ back _ (sym (σσ⁻¹ n)) ⟩
  w ↑ • (σ n • σ⁻¹ n)           ≈⟨ sym assoc ⟩
  (w ↑ • σ n) • σ⁻¹ n           ≈⟨ front _ (nat w) ⟩
  (σ n • top w) • σ⁻¹ n         ≈⟨ assoc ⟩
  σ n • top w • σ⁻¹ n           ≈⟨ ≡→≈ (Eq.sym (Eq.cong₂ (λ a b → a • top w • b) (net-cyc n) (net-cyc⁻ n))) ⟩
  pl (cycS n) (top w) ∎
  where
  open Tools ((₁₊ n) VRel,_===_)
  ≡→≈ : ∀ {a b : Circuit (₁₊ n)} → a ≡ b → a ≈ b
  ≡→≈ Eq.refl = refl

perm-cyc : ∀ n (j : Fin n) → perm (cycS n) ⟨$⟩ʳ sF j ≡ inject₁ j
perm-cyc (suc n) 0F     = perm-↑0 (cycS n)
perm-cyc (suc n) (sF j) = Eq.trans (perm-↑s (cycS n) (sF j)) (Eq.cong sF (perm-cyc n j))

------------------------------------------------------------------------
-- The exchange of the top two wires: stretch c is top c placed

swT : (k : ℕ) → Word (S.Gen (₂₊ k))
swT zero    = S.σ
swT (suc k) = swT k S.↑

net-swT : ∀ k → net (swT k) ≡ Swᵗ k
net-swT zero    = Eq.refl
net-swT (suc k) = Eq.trans (net-↑ (swT k)) (Eq.cong _↑ (net-swT k))

revS-swT : ∀ k → revS (swT k) ≡ swT k
revS-swT zero    = Eq.refl
revS-swT (suc k) = Eq.trans (revS-↑ (swT k)) (Eq.cong S._↑ (revS-swT k))

stretch-pl : ∀ (c : Circuit (₂₊ k)) → stretch c ≡ pl (swT (suc k)) (top c)
stretch-pl {k} c =
  Eq.sym (Eq.cong₂ (λ a b → a • top c • b) (net-swT (suc k))
                   (Eq.trans (Eq.cong net (revS-swT (suc k))) (net-swT (suc k))))

perm-swT-top : ∀ k → perm (swT k) ⟨$⟩ʳ fromℕ (₁₊ k) ≡ inject₁ (fromℕ k)
perm-swT-top zero    = Eq.refl
perm-swT-top (suc k) = Eq.trans (perm-↑s (swT k) (fromℕ (₁₊ k))) (Eq.cong sF (perm-swT-top k))

perm-swT-low : ∀ k (w : Fin k) → perm (swT k) ⟨$⟩ʳ inject₁ (inject₁ w) ≡ inject₁ (inject₁ w)
perm-swT-low (suc k) 0F     = perm-↑0 (swT k)
perm-swT-low (suc k) (sF w) = Eq.trans (perm-↑s (swT k) (inject₁ (inject₁ w))) (Eq.cong sF (perm-swT-low k w))

------------------------------------------------------------------------
-- A placement survives ↑ and stretch

module _ {m : ℕ} where
  private
    module T₁ = Tools ((₁₊ m) VRel,_===_)

  up-step : ∀ (g X : Circuit m) (τ′ : Word (S.Gen m)) → m ⊢ g ≈ pl τ′ X →
            (₁₊ m) ⊢ g ↑ ≈ pl (cycS m • topS τ′) (top X)
  up-step g X τ′ e = T₁.begin
    g ↑                              T₁.≈⟨ up-pl g ⟩
    pl (cycS m) (top g)              T₁.≈⟨ T₁.cong T₁.refl (T₁.cong (top-cong e) T₁.refl) ⟩
    pl (cycS m) (top (pl τ′ X))      T₁.≈⟨ ≡→≈ (Eq.cong (pl (cycS m)) (pl-top τ′ X)) ⟩
    pl (cycS m) (pl (topS τ′) (top X)) T₁.≈⟨ pl-pl (cycS m) (topS τ′) (top X) ⟩
    pl (cycS m • topS τ′) (top X) T₁.∎
    where
    ≡→≈ : ∀ {a b : Circuit (₁₊ m)} → a ≡ b → (₁₊ m) ⊢ a ≈ b
    ≡→≈ Eq.refl = T₁.refl

  perm-up : ∀ (τ′ : Word (S.Gen m)) (w : Fin m) → perm (cycS m • topS τ′) ⟨$⟩ʳ sF w ≡ inject₁ (perm τ′ ⟨$⟩ʳ w)
  perm-up τ′ w = Eq.trans (Eq.cong (perm (topS τ′) ⟨$⟩ʳ_) (perm-cyc m w)) (perm-top τ′ w)

stretch-step : ∀ (g X : Circuit (₂₊ k)) (τ′ : Word (S.Gen (₂₊ k))) → (₂₊ k) ⊢ g ≈ pl τ′ X →
               (₃₊ k) ⊢ stretch g ≈ pl (swT (suc k) • topS τ′) (top X)
stretch-step {k} g X τ′ e = T₃.begin
  stretch g                                T₃.≈⟨ ≡→≈ (stretch-pl g) ⟩
  pl (swT (suc k)) (top g)                 T₃.≈⟨ T₃.cong T₃.refl (T₃.cong (top-cong e) T₃.refl) ⟩
  pl (swT (suc k)) (top (pl τ′ X))         T₃.≈⟨ ≡→≈ (Eq.cong (pl (swT (suc k))) (pl-top τ′ X)) ⟩
  pl (swT (suc k)) (pl (topS τ′) (top X))  T₃.≈⟨ pl-pl (swT (suc k)) (topS τ′) (top X) ⟩
  pl (swT (suc k) • topS τ′) (top X) T₃.∎
  where
  module T₃ = Tools ((₃₊ k) VRel,_===_)
  ≡→≈ : ∀ {a b : Circuit (₃₊ k)} → a ≡ b → (₃₊ k) ⊢ a ≈ b
  ≡→≈ Eq.refl = T₃.refl

perm-stretch-top : ∀ k (τ′ : Word (S.Gen (₂₊ k))) →
                   perm (swT (suc k) • topS τ′) ⟨$⟩ʳ fromℕ (₂₊ k) ≡ inject₁ (perm τ′ ⟨$⟩ʳ fromℕ (₁₊ k))
perm-stretch-top k τ′ = Eq.trans (Eq.cong (perm (topS τ′) ⟨$⟩ʳ_) (perm-swT-top (suc k))) (perm-top τ′ (fromℕ (₁₊ k)))

perm-stretch-low : ∀ k (τ′ : Word (S.Gen (₂₊ k))) (w : Fin (₁₊ k)) →
                   perm (swT (suc k) • topS τ′) ⟨$⟩ʳ inject₁ (inject₁ w) ≡ inject₁ (perm τ′ ⟨$⟩ʳ inject₁ w)
perm-stretch-low k τ′ w = Eq.trans (Eq.cong (perm (topS τ′) ⟨$⟩ʳ_) (perm-swT-low (suc k) w)) (perm-top τ′ (inject₁ w))
