------------------------------------------------------------------------
-- Presentations of groups
--
-- Two placed rotations commute when their colourings differ off both
-- targets (Clément, Appendix E.5, (351) and (352) with x ≠ y placed)
--
-- A rotation `rot β` is rigid on wire 0 (Canon32.rot-rigid), so its
-- placement by a network depends only on where the network sends its
-- target (Placed.frame₁).  Two placed rotations with the same target t
-- and a witness j — a wire off the target where their colourings
-- differ — are conjugated by a network bringing t, j to the wires 0, 1
-- (Placed.bring₂): they become the canonical rotation in two colourings,
-- black on wire 0 and relatively white on wire 1, which is C351g.  With
-- different targets t, t′ the network brings t, t′, j to 0, 1, 2
-- (bring₃), and the second rotation is the canonical one under the swap
-- of the wires 0 1: C352g.  The colourings are only ever read at those
-- wires, through the network (`swW-lookup`).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.RotAnywhere
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false)
open import Data.Fin using (Fin ; toℕ) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (yes ; no)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₄₊)

import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (lookupℕ)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (perm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (revS)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetColours using (swW ; _⇔_)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (pl ; perm-σ₁)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed
  using (Rigid ; frame₁ ; place ; place-pl ; reflect ; swW-lookup ; ⇔-diff ; revS² ; perm-back ; bring₂ ; bring₃)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (rot ; RotComm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Ancilla complete₂ complete₃ using (Below)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Canon32 complete₂ complete₃ using (rot-rigid ; C351g ; C352g)

module _ (k : ℕ) (below : Below (₁₊ (₄₊ k))) where

  private
    N : ℕ
    N = ₁₊ (₄₊ k)

  open Tools (N VRel,_===_)

  private
    rig : ∀ β → Rigid 1 (rot {₂₊ k} β)
    rig β v = rot-rigid k below β v

    -- A placed rotation, in the frame of σ, where σ sends its target to
    -- wire 0 …
    frame-0 : ∀ β (σ u : Word (S.Gen N)) (t : Fin N) → perm u ⟨$⟩ʳ t ≡ 0F → perm σ ⟨$⟩ʳ t ≡ 0F →
              (s : Bits N) → pl (revS σ) (place u s (rot β)) ≈ col (swW (revS σ) s) (rot β)
    frame-0 β σ u t pu σt s =
      trans (place-pl (revS σ) u s (rot β))
            (mid _ _ (trans (frame₁ (rig β) (revS σ • u) ε cond) (trans left-unit right-unit)))
      where
      cond : perm ε ⟨$⟩ʳ (perm (revS (revS σ • u)) ⟨$⟩ʳ 0F) ≡ 0F
      cond = Eq.trans (Eq.cong (perm (revS (revS σ)) ⟨$⟩ʳ_) (perm-back u pu))
                      (Eq.trans (Eq.cong (λ w → perm w ⟨$⟩ʳ t) (revS² σ)) σt)

    -- … or to wire 1.
    frame-1 : ∀ β (σ u : Word (S.Gen N)) (t : Fin N) → perm u ⟨$⟩ʳ t ≡ 0F → perm σ ⟨$⟩ʳ t ≡ sF 0F →
              (s : Bits N) → pl (revS σ) (place u s (rot β)) ≈ col (swW (revS σ) s) (Ex • rot β • Ex)
    frame-1 β σ u t pu σt s =
      trans (place-pl (revS σ) u s (rot β)) (mid _ _ (frame₁ (rig β) (revS σ • u) S.σ cond))
      where
      cond : perm S.σ ⟨$⟩ʳ (perm (revS (revS σ • u)) ⟨$⟩ʳ 0F) ≡ 0F
      cond = Eq.trans (Eq.cong (perm S.σ ⟨$⟩ʳ_)
                        (Eq.trans (Eq.cong (perm (revS (revS σ)) ⟨$⟩ʳ_) (perm-back u pu))
                                  (Eq.trans (Eq.cong (λ w → perm w ⟨$⟩ʳ t) (revS² σ)) σt)))
                      perm-σ₁

    -- The bit of a colouring in the frame of σ, at a wire σ sends there.
    bit : ∀ (σ : Word (S.Gen N)) (s : Bits N) (t i : Fin N) → perm σ ⟨$⟩ʳ t ≡ i →
          lookupℕ (toℕ i) (swW (revS σ) s) ≡ lookupℕ (toℕ t) s
    bit σ s t i e = Eq.trans (swW-lookup (revS σ) s i) (Eq.cong (λ x → lookupℕ (toℕ x) s) (perm-back σ e))

    -- The same target.
    same : ∀ α β (u u′ : Word (S.Gen N)) (t : Fin N) → perm u ⟨$⟩ʳ t ≡ 0F → perm u′ ⟨$⟩ʳ t ≡ 0F →
           (s s′ : Bits N) → lookupℕ (toℕ t) s ≡ true → lookupℕ (toℕ t) s′ ≡ true →
           (j : Fin N) → j ≢ t → lookupℕ (toℕ j) s ≢ lookupℕ (toℕ j) s′ →
           place u s (rot α) • place u′ s′ (rot β) ≈ place u′ s′ (rot β) • place u s (rot α)
    same α β u u′ t pu pu′ s s′ st st′ j jt sj with bring₂ t j jt
    ... | σ , σt , σj = reflect σ (begin
      pl (revS σ) (place u s (rot α)) • pl (revS σ) (place u′ s′ (rot β))
        ≈⟨ cong (frame-0 α σ u t pu σt s) (frame-0 β σ u′ t pu′ σt s′) ⟩
      col x (rot α) • col y (rot β)
        ≈⟨ C351g k below α β x y (Eq.trans (bit σ s t 0F σt) st) (Eq.trans (bit σ s′ t 0F σt) st′)
                   (⇔-diff _ _ (λ e → sj (Eq.trans (Eq.sym (bit σ s j (sF 0F) σj)) (Eq.trans e (bit σ s′ j (sF 0F) σj))))) ⟩
      col y (rot β) • col x (rot α)
        ≈⟨ sym (cong (frame-0 β σ u′ t pu′ σt s′) (frame-0 α σ u t pu σt s)) ⟩
      pl (revS σ) (place u′ s′ (rot β)) • pl (revS σ) (place u s (rot α)) ∎)
      where
      x y : Bits N
      x = swW (revS σ) s
      y = swW (revS σ) s′

    -- Crossed targets.
    crossed : ∀ α β (u u′ : Word (S.Gen N)) (t t′ : Fin N) → t′ ≢ t → perm u ⟨$⟩ʳ t ≡ 0F → perm u′ ⟨$⟩ʳ t′ ≡ 0F →
              (s s′ : Bits N) → lookupℕ (toℕ t) s ≡ true → lookupℕ (toℕ t′) s′ ≡ true →
              (j : Fin N) → j ≢ t → j ≢ t′ → lookupℕ (toℕ j) s ≢ lookupℕ (toℕ j) s′ →
              place u s (rot α) • place u′ s′ (rot β) ≈ place u′ s′ (rot β) • place u s (rot α)
    crossed α β u u′ t t′ t′t pu pu′ s s′ st st′ j jt jt′ sj with bring₃ t t′ j t′t jt jt′
    ... | σ , σt , σt′ , σj = reflect σ (begin
      pl (revS σ) (place u s (rot α)) • pl (revS σ) (place u′ s′ (rot β))
        ≈⟨ cong (frame-0 α σ u t pu σt s) (frame-1 β σ u′ t′ pu′ σt′ s′) ⟩
      col x (rot α) • col y (Ex • rot β • Ex)
        ≈⟨ C352g k below α β x y (Eq.trans (bit σ s t 0F σt) st) (Eq.trans (bit σ s′ t′ (sF 0F) σt′) st′)
                   (⇔-diff _ _ (λ e → sj (Eq.trans (Eq.sym (bit σ s j (sF (sF 0F)) σj))
                                                   (Eq.trans e (bit σ s′ j (sF (sF 0F)) σj))))) ⟩
      col y (Ex • rot β • Ex) • col x (rot α)
        ≈⟨ sym (cong (frame-1 β σ u′ t′ pu′ σt′ s′) (frame-0 α σ u t pu σt s)) ⟩
      pl (revS σ) (place u′ s′ (rot β)) • pl (revS σ) (place u s (rot α)) ∎)
      where
      x y : Bits N
      x = swW (revS σ) s
      y = swW (revS σ) s′

  rot-comm : RotComm (₂₊ k)
  rot-comm α β u u′ t t′ pu pu′ s s′ st st′ j jt jt′ sj with t′ ≟ t
  ... | yes Eq.refl = same α β u u′ t pu pu′ s s′ st st′ j jt sj
  ... | no t′t      = crossed α β u u′ t t′ t′t pu pu′ s s′ st st′ j jt jt′ sj
