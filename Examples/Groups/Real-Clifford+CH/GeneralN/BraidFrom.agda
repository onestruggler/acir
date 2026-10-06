------------------------------------------------------------------------
-- Presentations of groups
--
-- Two crossed rotations braid, in every colour and placed anywhere, at
-- any width with the canonical facts given (Clément, Appendix E.5,
-- (358) as rule (24) uses it)
--
-- Two placed rotations P, Q with targets t ≠ t′, whose colourings agree
-- off the two targets, where P's type is decided by Q's colour on P's
-- target and Q's by P's colour on Q's target (as for two consecutive
-- Gray-code steps), satisfy P • Q • P ≈ Q • P • Q (`braid`).  A network
-- bringing t, t′ to the wires 0, 1 (Placed.bring₂) makes them the
-- canonical rotations on wires 0 and 1, and the colourings, relative to
-- each other, differ only on those two wires (PlaceFrames.col-rel₃ and
-- frame-agree).  What is left is `C24 γ δ`, the canonical braid in the
-- four colourings of the wires 0 1.  A white control on B's target is X
-- there, which turns B over (`e356`); white on A's target is X on wire
-- 0 around the canonical braid (`e358`), which turns A over.  So all
-- four are (358).  The parameters are the rotation's rigidity on wire 0,
-- (356) and (358); BraidAnywhere supplies them from five wires on.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed using (Rigid)
open import Examples.Groups.Real-Clifford+CH.GeneralN.RotCol using (rot)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BraidCol using (Braid ; E356 ; E358)

module Examples.Groups.Real-Clifford+CH.GeneralN.BraidFrom
  {m : ℕ} (rig : ∀ β → Rigid 1 (rot {m} β)) (e356 : E356 m) (e358 : E358 m)
  where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Fin using (Fin ; toℕ ; fromℕ<) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Nat using (zero ; suc ; _<_ ; s≤s ; z≤n)
open import Data.Product using (_,_)
open import Data.Vec using ([] ; _∷_ ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; X² ; Ex² ; S-X↓)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (lookupℕ)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (perm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (negsB ; revS ; allT)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetColours using (swW ; _⇔_ ; combine)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (pl ; pl-•)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Placed
  using (place ; combine-lookup ; bring₂)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (col)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (X-↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.PlaceFrames
  using (reflect′ ; col-rel₃ ; frame-0 ; frame-1 ; bit ; frame-agree)

private
  N : ℕ
  N = ₃₊ m

open Tools (N VRel,_===_)

private
  ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
  ≡→≈ Eq.refl = refl

  ⇔-true : ∀ b → (b ⇔ true) ≡ b
  ⇔-true true  = Eq.refl
  ⇔-true false = Eq.refl

  ones₃ : Bits (₁₊ m)
  ones₃ = replicate (₁₊ m) true

  module NX = Conj {N} X X²
  module S₀₁ = Conj {N} (Ex ↓) Ex²

  -- The rotation on wire 1, and its colourings of the wires 0 1.
  B : Bool → Circuit N
  B δ = Ex ↓ • rot δ • Ex ↓

  cl : Bool → Bool → Circuit N
  cl γ δ = col (γ ∷ δ ∷ ones₃) (B δ)

  col-11 : ∀ (w : Circuit N) → col (true ∷ true ∷ ones₃) w ≈ w
  col-11 w = trans (≡→≈ (Eq.cong (λ z → z • w • z) (allT N))) (trans left-unit right-unit)

  col-01 : ∀ (w : Circuit N) → col (false ∷ true ∷ ones₃) w ≈ X • w • X
  col-01 w = trans (≡→≈ (Eq.cong (λ z → (X • z ↑) • w • (X • z ↑)) (allT (₂₊ m))))
                   (cong right-unit (back _ right-unit))

  col-10 : ∀ (w : Circuit N) → col (true ∷ false ∷ ones₃) w ≈ X ↑ • w • X ↑
  col-10 w = trans (≡→≈ (Eq.cong (λ z → (X • z ↑) ↑ • w • (X • z ↑) ↑) (allT (₁₊ m))))
                   (cong right-unit (back _ right-unit))

  col-00 : ∀ (w : Circuit N) → col (false ∷ false ∷ ones₃) w ≈ X • (X ↑ • w • X ↑) • X
  col-00 w = begin
    (X • (X • z ↑) ↑) • w • (X • (X • z ↑) ↑)
      ≈⟨ ≡→≈ (Eq.cong (λ u → (X • (X • u ↑) ↑) • w • (X • (X • u ↑) ↑)) (allT (₁₊ m))) ⟩
    (X • (X ↑ • ε)) • w • (X • (X ↑ • ε))
      ≈⟨ cong (back _ right-unit) (back _ (back _ right-unit)) ⟩
    (X • X ↑) • w • (X • X ↑)
      ≈⟨ back _ (back _ (X-↑ X)) ⟩
    (X • X ↑) • w • (X ↑ • X)
      ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
    X • (X ↑ • w • X ↑) • X ∎
    where
    z : Circuit (₁₊ m)
    z = negsB ones₃

  -- X on B's target turns it over ((356) under the swap).
  X-B : X ↑ • B false • X ↑ ≈ B true
  X-B = trans (sym (S₀₁.⟪⟫-•₃ S-X↓ refl S-X↓)) (S₀₁.⟪⟫-cong e356)

  cl-0 : ∀ γ → cl γ false ≈ cl γ true
  cl-0 true  = trans (col-10 (B false)) (trans X-B (sym (col-11 (B true))))
  cl-0 false = trans (col-00 (B false)) (trans (back _ (front _ X-B)) (sym (col-01 (B true))))

------------------------------------------------------------------------
-- The canonical braid in the four colourings of the wires 0 1

private
  C24-tt : rot false • (cl true true • rot false) ≈ cl true true • (rot false • cl true true)
  C24-tt = trans (back _ (front _ (col-11 (B true))))
             (trans e358 (sym (cong (col-11 (B true)) (back _ (col-11 (B true))))))

  C24-ft : rot true • (cl false true • rot true) ≈ cl false true • (rot true • cl false true)
  C24-ft = trans (back _ (front _ (col-01 (B true))))
             (trans (NX.⟪⟫-≈ e358 (NX.⟪⟫-•₃ e356 refl e356)
                                             (NX.⟪⟫-•₃ refl e356 refl))
                    (sym (cong (col-01 (B true)) (back _ (col-01 (B true))))))

  -- A white control on B's target changes nothing.
  via-0 : ∀ γ → rot (not γ) • (cl γ true • rot (not γ)) ≈ cl γ true • (rot (not γ) • cl γ true) →
          rot (not γ) • (cl γ false • rot (not γ)) ≈ cl γ false • (rot (not γ) • cl γ false)
  via-0 γ e = trans (back _ (front _ (cl-0 γ))) (trans e (sym (cong (cl-0 γ) (back _ (cl-0 γ)))))

C24 : ∀ γ δ → rot (not γ) • (cl γ δ • rot (not γ)) ≈ cl γ δ • (rot (not γ) • cl γ δ)
C24 true  true  = C24-tt
C24 false true  = C24-ft
C24 true  false = via-0 true C24-tt
C24 false false = via-0 false C24-ft

private
  C24′ : ∀ α β → rot α • (col (not α ∷ β ∷ ones₃) (B β) • rot α) ≈
                 col (not α ∷ β ∷ ones₃) (B β) • (rot α • col (not α ∷ β ∷ ones₃) (B β))
  C24′ true  β = C24 false β
  C24′ false β = C24 true β

  frame-0′ : ∀ β (σ u : Word (S.Gen N)) (t : Fin N) → perm u ⟨$⟩ʳ t ≡ 0F → perm σ ⟨$⟩ʳ t ≡ 0F →
             (s : Bits N) → pl (revS σ) (place u s (rot β)) ≈ col (swW (revS σ) s) (rot β)
  frame-0′ β = frame-0 (rig β)

  frame-1′ : ∀ β (σ u : Word (S.Gen N)) (t : Fin N) → perm u ⟨$⟩ʳ t ≡ 0F → perm σ ⟨$⟩ʳ t ≡ sF 0F →
             (s : Bits N) → pl (revS σ) (place u s (rot β)) ≈ col (swW (revS σ) s) (Ex • rot β • Ex)
  frame-1′ β = frame-1 (rig β)

------------------------------------------------------------------------
-- The braid, placed

braid : Braid m
braid α β u u′ t t′ t′t pu pu′ s s′ st st′ agree αe βe with bring₂ t t′ t′t
... | σ , σt , σt′ = reflect′ σ (begin
  pl (revS σ) P • pl (revS σ) (Q • P)
    ≈⟨ back _ (pl-• (revS σ) Q P) ⟩
  pl (revS σ) P • (pl (revS σ) Q • pl (revS σ) P)
    ≈⟨ cong fP (cong fQ fP) ⟩
  col x (rot α) • (col y (B β) • col x (rot α))
    ≈⟨ col-rel₃ x y (Eq.subst (λ w → rot α • (col w (B β) • rot α) ≈ col w (B β) • (rot α • col w (B β)))
                              (Eq.sym zs) (C24′ α β)) ⟩
  col y (B β) • (col x (rot α) • col y (B β))
    ≈⟨ sym (cong fQ (cong fP fQ)) ⟩
  pl (revS σ) Q • (pl (revS σ) P • pl (revS σ) Q)
    ≈⟨ sym (back _ (pl-• (revS σ) P Q)) ⟩
  pl (revS σ) Q • pl (revS σ) (P • Q) ∎)
  where
  P Q : Circuit N
  P = place u s (rot α)
  Q = place u′ s′ (rot β)
  x y z : Bits N
  x = swW (revS σ) s
  y = swW (revS σ) s′
  z = combine x y
  fP : pl (revS σ) P ≈ col x (rot α)
  fP = frame-0′ α σ u t pu σt s
  fQ : pl (revS σ) Q ≈ col y (B β)
  fQ = frame-1′ β σ u′ t′ pu′ σt′ s′
  -- On the wires 0 1: P's colour on Q's target, Q's colour on P's target.
  z0 : lookupℕ 0 z ≡ not α
  z0 = Eq.trans (combine-lookup 0 x y (s≤s z≤n))
         (Eq.trans (Eq.cong (λ b → b ⇔ lookupℕ 0 y) (Eq.trans (bit σ s t 0F σt) st))
                   (Eq.trans (bit σ s′ t 0F σt) (Eq.sym αe)))
  z1 : lookupℕ 1 z ≡ β
  z1 = Eq.trans (combine-lookup 1 x y (s≤s (s≤s z≤n)))
         (Eq.trans (Eq.cong₂ _⇔_ (bit σ s t′ (sF 0F) σt′) (Eq.trans (bit σ s′ t′ (sF 0F) σt′) st′))
                   (Eq.trans (⇔-true (lookupℕ (toℕ t′) s)) (Eq.sym βe)))
  zs : z ≡ not α ∷ β ∷ ones₃
  zs = Eq.trans (frame-agree σ t t′ σt σt′ s s′ agree) (Eq.cong₂ (λ a b → a ∷ b ∷ ones₃) z0 z1)
