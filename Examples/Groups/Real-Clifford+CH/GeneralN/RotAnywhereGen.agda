------------------------------------------------------------------------
-- Presentations of groups
--
-- Two placed rotations commute when their colourings differ off both
-- targets, at any width with the canonical cases given (Clément,
-- Appendix E.5, (351) and (352) with x ≠ y placed)
--
-- A rotation `rot β` rigid on wire 0 (`rig`) is placed by a network
-- depending only on where the network sends its target
-- (Placed.frame₁).  Two placed rotations with the same target t and a
-- witness j — a wire off the target where their colourings differ —
-- are conjugated by a network bringing t, j to the wires 0, 1
-- (Placed.bring₂): they become the canonical rotation in two
-- colourings, black on wire 0 and relatively white on wire 1, which is
-- `c351`.  With different targets t, t′ the network brings t, t′, j to
-- 0, 1, 2 (bring₃), and the second rotation is the canonical one under
-- the swap of the wires 0 1: `c352`.  The colourings are only ever read
-- at those wires, through the network (`swW-lookup`).  RotAnywhere
-- supplies the three parameters from five wires on.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed using (Rigid)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (rot ; C351 ; C352)

module Examples.Groups.Real-Clifford+CH.GeneralN.RotAnywhereGen
  {m : ℕ} (rig : ∀ β → Rigid 1 (rot {m} β)) (c351 : C351 m) (c352 : C352 m)
  where

open import Data.Bool using (Bool ; true ; false)
open import Data.Fin using (Fin ; toℕ) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Fin.Properties using (_≟_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (yes ; no)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₃₊)

import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (lookupℕ)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (perm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (revS)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetColours using (swW ; _⇔_)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (pl)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed
  using (place ; reflect ; ⇔-diff ; bring₂ ; bring₃)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceFrames using (bit)
import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceFrames as PF
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (RotComm)

private
  N : ℕ
  N = ₃₊ m

open Tools (N VRel,_===_)

private
  -- A placed rotation, in the frame of σ, where σ sends its target to
  -- wire 0 …
  frame-0 : ∀ β (σ u : Word (S.Gen N)) (t : Fin N) → perm u ⟨$⟩ʳ t ≡ 0F → perm σ ⟨$⟩ʳ t ≡ 0F →
            (s : Bits N) → pl (revS σ) (place u s (rot β)) ≈ col (swW (revS σ) s) (rot β)
  frame-0 β = PF.frame-0 (rig β)

  -- … or to wire 1.
  frame-1 : ∀ β (σ u : Word (S.Gen N)) (t : Fin N) → perm u ⟨$⟩ʳ t ≡ 0F → perm σ ⟨$⟩ʳ t ≡ sF 0F →
            (s : Bits N) → pl (revS σ) (place u s (rot β)) ≈ col (swW (revS σ) s) (Ex • rot β • Ex)
  frame-1 β = PF.frame-1 (rig β)

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
      ≈⟨ c351 α β x y (Eq.trans (bit σ s t 0F σt) st) (Eq.trans (bit σ s′ t 0F σt) st′)
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
      ≈⟨ c352 α β x y (Eq.trans (bit σ s t 0F σt) st) (Eq.trans (bit σ s′ t′ (sF 0F) σt′) st′)
                 (⇔-diff _ _ (λ e → sj (Eq.trans (Eq.sym (bit σ s j (sF (sF 0F)) σj))
                                                 (Eq.trans e (bit σ s′ j (sF (sF 0F)) σj))))) ⟩
    col y (Ex • rot β • Ex) • col x (rot α)
      ≈⟨ sym (cong (frame-1 β σ u′ t′ pu′ σt′ s′) (frame-0 α σ u t pu σt s)) ⟩
    pl (revS σ) (place u′ s′ (rot β)) • pl (revS σ) (place u s (rot α)) ∎)
    where
    x y : Bits N
    x = swW (revS σ) s
    y = swW (revS σ) s′

rot-comm : RotComm m
rot-comm α β u u′ t t′ pu pu′ s s′ st st′ j jt jt′ sj with t′ ≟ t
... | yes Eq.refl = same α β u u′ t pu pu′ s s′ st st′ j jt sj
... | no t′t      = crossed α β u u′ t t′ t′t pu pu′ s s′ st st′ j jt jt′ sj
