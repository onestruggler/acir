------------------------------------------------------------------------
-- Presentations of groups
--
-- A rotation merged over every colouring of its controls (Clément,
-- Appendix E.3, the product in the proof of Lemma 8.5)
--
-- (354) on the top wire at every width from five on (`rmerge-top`):
-- ZX354's merge on wire 3, carried up along the swaps of the controls,
-- which the rotation passes (Canon32.rot-rigid), by MergeGen.merge-up′.
-- Below five wires it is decided (BaseRotMerge).  So MergeGen.MergeTop
-- applies to the families ΛZX and ΛXZ: the rotation on 4 + k wires over
-- every colouring of its 3 + k controls is ZX, resp. XZ, on wire 0
-- (`merge-rot`), given completeness below 5 + k.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.RotMerge
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false)
open import Data.Nat using (ℕ ; zero ; suc ; _≤_ ; _<_ ; s≤s ; z≤n)
open import Data.Nat.Properties using (≤-refl ; ≤-trans ; n≤1+n)
open import Data.Vec using (_∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
import Examples.Groups.Real-Clifford+CH.SemanticSteps as SS
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (Xat ; swapAt)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (allBits)
open import Examples.Groups.Real-Clifford+CH.Encoding using (∏)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (net)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (negsB ; σAt ; net-σAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceAt using (placeAt ; placeAt-place)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below ; Comp)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (rot)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon32 complete₂ complete₃ using (rot-rigid)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZX354 complete₂ complete₃ using (eq354)
open import Examples.Groups.Real-Clifford+CH.GeneralN.MergeGen using (merge-up′ ; module MergeTop)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BaseRotMerge
  using (e-zx1 ; e-zx2 ; e-zx3 ; e-xz1 ; e-xz2 ; e-xz3)

-- The family of rotations with no control on wire 0 left out: ZX for
-- true, XZ for false (rot β is F β (2 + m)).
F : Bool → (K : ℕ) → Circuit (₁₊ K)
F true  = ΛZX
F false = ΛXZ

-- (354) on the top wire of 1 + K wires.
TopMerge : Bool → ℕ → Set
TopMerge β K = (₂₊ K) ⊢ (Xat (suc K) • F β (suc K) • Xat (suc K)) • F β (suc K) ≈ placeAt (suc K) (F β K)

------------------------------------------------------------------------
-- From wire 3 to the top wire, at width 5 + k

module _ (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  private
    N : ℕ
    N = ₁₊ (₄₊ k)

  open Tools (N VRel,_===_)

  private
    ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
    ≡→≈ Eq.refl = refl

    -- The swap of the wires 3 + i, 4 + i passes the rotation.
    swap-rot : ∀ β i → swapAt (₃₊ i) • rot β ≈ rot β • swapAt (₃₊ i)
    swap-rot β i = Eq.subst (λ w → w ↑ • rot β ≈ rot β • w ↑) (net-σAt (₂₊ i)) (rot-rigid k below β (σAt (₂₊ i)))

    go : ∀ β i → i ≤ ₁₊ k → (Xat (₃₊ i) • rot β • Xat (₃₊ i)) • rot β ≈ placeAt (₃₊ i) (rot {₁₊ k} β)
    go β zero    _       = trans (eq354 k below β) (≡→≈ (Eq.sym (placeAt-place 3 (rot {₁₊ k} β))))
    go β (suc i) (s≤s b) = merge-up′ (₃₊ i) (s≤s (s≤s (s≤s (s≤s b)))) (swap-rot β i)
                                     (go β i (≤-trans b (n≤1+n k)))

  rmerge-top : ∀ β → (Xat (₄₊ k) • rot β • Xat (₄₊ k)) • rot β ≈ placeAt (₄₊ k) (rot {₁₊ k} β)
  rmerge-top β = go β (₁₊ k) ≤-refl

------------------------------------------------------------------------
-- At every width below 5 + k

module _ (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  private
    c₂ : Comp 2
    c₂ = complete₂
    c₃ : Comp 3
    c₃ = complete₃
    c₄ : Comp 4
    c₄ = below (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))

    -- Completeness below 5 + k′ for k′ < k.
    below′ : ∀ k′ → k′ < k → Below (₁₊ (₄₊ k′))
    below′ k′ k′<k i< = below (≤-trans i< (s≤s (s≤s (s≤s (s≤s (s≤s (≤-trans (n≤1+n k′) k′<k)))))))

  top-merge : ∀ β K → K < ₃₊ k → TopMerge β K
  top-merge true  zero                _ =
    SS.Below.by-sem₀ 2 (s≤s (s≤s z≤n)) c₂ ((Xat 1 • ΛZX 1 • Xat 1) • ΛZX 1) (placeAt 1 (ΛZX 0)) (Evaluated.same e-zx1)
  top-merge true  (suc zero)          _ =
    SS.Below.by-sem₀ 3 (s≤s (s≤s (s≤s z≤n))) c₃ ((Xat 2 • ΛZX 2 • Xat 2) • ΛZX 2) (placeAt 2 (ΛZX 1)) (Evaluated.same e-zx2)
  top-merge true  (suc (suc zero))    _ =
    SS.Below.by-sem₀ 4 (s≤s (s≤s (s≤s (s≤s z≤n)))) c₄ ((Xat 3 • ΛZX 3 • Xat 3) • ΛZX 3) (placeAt 3 (ΛZX 2)) (Evaluated.same e-zx3)
  top-merge false zero                _ =
    SS.Below.by-sem₀ 2 (s≤s (s≤s z≤n)) c₂ ((Xat 1 • ΛXZ 1 • Xat 1) • ΛXZ 1) (placeAt 1 (ΛXZ 0)) (Evaluated.same e-xz1)
  top-merge false (suc zero)          _ =
    SS.Below.by-sem₀ 3 (s≤s (s≤s (s≤s z≤n))) c₃ ((Xat 2 • ΛXZ 2 • Xat 2) • ΛXZ 2) (placeAt 2 (ΛXZ 1)) (Evaluated.same e-xz2)
  top-merge false (suc (suc zero))    _ =
    SS.Below.by-sem₀ 4 (s≤s (s≤s (s≤s (s≤s z≤n)))) c₄ ((Xat 3 • ΛXZ 3 • Xat 3) • ΛXZ 3) (placeAt 3 (ΛXZ 2)) (Evaluated.same e-xz3)
  top-merge true  (suc (suc (suc k′))) (s≤s (s≤s (s≤s k′<k))) = rmerge-top k′ (below′ k′ k′<k) true
  top-merge false (suc (suc (suc k′))) (s≤s (s≤s (s≤s k′<k))) = rmerge-top k′ (below′ k′ k′<k) false

  -- The rotation on 4 + k wires over every colouring of its controls.
  merge-rot : ∀ β → (₄₊ k) ⊢ ∏ (allBits (₃₊ k)) (λ c → negsB (true ∷ c) • F β (₃₊ k) • negsB (true ∷ c))
                             ≈ F β 0 ↓ᵏ (₃₊ k)
  merge-rot true  = MergeTop.merge-top₀ (F true) (₃₊ k) (top-merge true) Eq.refl (λ j → Eq.refl) (₃₊ k) ≤-refl
  merge-rot false = MergeTop.merge-top₀ (F false) (₃₊ k) (top-merge false) Eq.refl (λ j → Eq.refl) (₃₊ k) ≤-refl
