------------------------------------------------------------------------
-- Presentations of groups
--
-- A controlled gate one wire higher is the same gadget with the wires
-- above the spare moved up.
--
-- CTRL₁ (g ↥) conjugates CTRL₁ g ↑ by the swaps of wires 0 1 2, which
-- bring the control and the spare back down.  Equally, it is CTRL₁ g
-- with an idle wire on top, conjugated by a cycle Y of the wires from 2
-- up, which moves the gate up one wire and leaves the control and the
-- spare where they are (`move`).  For a gate at the bottom that is a
-- closed equation (`base`): Cycle.nat turns CTRL₁ g ↑ into CTRL₁ g ⇓
-- placed by a cycle of all the wires, and Frame.frame-perm replaces
-- that placement by Y's, the two networks sending every wire to the
-- same place (decided on the closed words, by `refl`).  One wire higher
-- the cycle moves up with the gate and passes the swaps of wires 0 1 2
-- (Placement.apart).  So a controlled gate far up is a controlled gate
-- low down, conjugated by a network away from the bottom wires — which
-- is what the commutation cases of the ctrl lemma need.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.CtrlMove where

open import Data.Fin.Base using (Fin ; zero ; suc ; inject+)
open import Data.Fin.Permutation using (_⟨$⟩ˡ_)
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)
import Presentation.Base as PB

open import Examples.Groups.CCX+HH.NaturalP.Syntactics
open import Examples.Groups.CCX+HH.NaturalP.Ctrl
open import Examples.Groups.CCX+HH.NaturalP.Pad using (widen)
import Examples.Groups.Symmetric.Syntactics as S
import Examples.Groups.Symmetric.Interpretation as SI
import Examples.Groups.Symmetric-Prop.Networks as Networks
import Examples.Groups.Symmetric-Prop.Placement as Placement
import Examples.Groups.Symmetric-Prop.Frame as Frame
import Examples.Groups.Symmetric-Prop.Cycle as Cycle

private
  variable
    n : ℕ

  no-scalar : ∀ {n} (h h′ : Gate 0) →
    n ⊢ [ gate₀ h′ ]ʷ • [ gate₀ h ]ʷ ≈ [ gate₀ h ]ʷ • [ gate₀ h′ ]ʷ
  no-scalar ()

  module NW = Networks Gate SW-gate _NP,_===_
  module PL = Placement Gate SW-gate _NP,_===_
  module FR = Frame Gate SW-gate _NP,_===_
  module CY = Cycle Gate SW-gate _NP,_===_

------------------------------------------------------------------------
-- Networks

-- The cycle carrying wire 0 to the top, as a network.
cycS : (n : ℕ) → Word (S.Gen (suc n))
cycS zero    = ε
cycS (suc n) = S.σ • cycS n S.↑

-- The swaps of wires 0 1 2, as a network.
LS : Word (S.Gen (₃₊ n))
LS = S.σ S.↑ • S.σ

------------------------------------------------------------------------
-- The closed base, for X

private
  KX : Circuit 3
  KX = CTRL₁ (gate₁ {0} X-gate)

  -- The cycle of all the wires, then the swaps; and the cycle of the
  -- wires from 2 up.
  NX NX′ : Word (S.Gen 4)
  NX  = LS • cycS 3
  NX′ = cycS 1 S.↑ S.↑

  agreeX : ∀ (j : Fin 4) → SI.⟦ NX ⟧ ⟨$⟩ˡ inject+ 0 j ≡ SI.⟦ NX′ ⟧ ⟨$⟩ˡ inject+ 0 j
  agreeX zero                   = refl
  agreeX (suc zero)             = refl
  agreeX (suc (suc zero))       = refl
  agreeX (suc (suc (suc zero))) = refl

------------------------------------------------------------------------
-- Generic steps

private
  -- A circuit one wire up is the circuit with an idle wire on top,
  -- placed by the cycle.
  up-place : (w : Circuit n) → (₁₊ n) ⊢ w ↑ ≈ CY.cyc n • (w ⇓ • CY.cyc⁻ n)
  up-place {n} w =
    PB.trans (PB.sym PB.right-unit)
    (PB.trans (PB.cong PB.refl (PB.sym (CY.cyc-cyc⁻ n)))
    (PB.trans (PB.sym PB.assoc)
    (PB.trans (PB.cong (CY.nat no-scalar w) PB.refl)
      PB.assoc)))

  reassoc : ∀ {A C W D E : Circuit n} →
    n ⊢ A • ((C • (W • D)) • E) ≈ (A • C) • (W • (D • E))
  reassoc = PB.trans (PB.cong PB.refl PB.assoc)
    (PB.trans (PB.cong PB.refl (PB.cong PB.refl PB.assoc)) (PB.sym PB.assoc))

  -- CTRL₁ (g ↥) as the cycle of all the wires and the swaps of wires
  -- 0 1 2 placing CTRL₁ g with an idle wire on top.
  step : (g : Gen n) → (₃₊ n) ⊢ CTRL₁ (g ↥) ≈
    ((σ ↑ • σ) • CY.cyc (₂₊ n)) • (CTRL₁ g ⇓ • (CY.cyc⁻ (₂₊ n) • (σ • σ ↑)))
  step g = PB.trans (PB.cong PB.refl (PB.cong (up-place (CTRL₁ g)) PB.refl)) reassoc

------------------------------------------------------------------------
-- The closed bases

private
  N₁ : Word (S.Gen 4)
  N₁ = LS • cycS 3
  N₁′ : Word (S.Gen 4)
  N₁′ = cycS 1 S.↑ S.↑

  N₂ : Word (S.Gen 5)
  N₂ = LS • cycS 4
  N₂′ : Word (S.Gen 5)
  N₂′ = cycS 2 S.↑ S.↑

  N₃ : Word (S.Gen 6)
  N₃ = LS • cycS 5
  N₃′ : Word (S.Gen 6)
  N₃′ = cycS 3 S.↑ S.↑

  agree₁ : ∀ (j : Fin 4) → SI.⟦ N₁ ⟧ ⟨$⟩ˡ inject+ 0 j ≡ SI.⟦ N₁′ ⟧ ⟨$⟩ˡ inject+ 0 j
  agree₁ zero                   = refl
  agree₁ (suc zero)             = refl
  agree₁ (suc (suc zero))       = refl
  agree₁ (suc (suc (suc zero))) = refl

  agree₂ : ∀ (j : Fin 5) → SI.⟦ N₂ ⟧ ⟨$⟩ˡ inject+ 0 j ≡ SI.⟦ N₂′ ⟧ ⟨$⟩ˡ inject+ 0 j
  agree₂ zero                         = refl
  agree₂ (suc zero)                   = refl
  agree₂ (suc (suc zero))             = refl
  agree₂ (suc (suc (suc zero)))       = refl
  agree₂ (suc (suc (suc (suc zero)))) = refl

  agree₃ : ∀ (j : Fin 6) → SI.⟦ N₃ ⟧ ⟨$⟩ˡ inject+ 0 j ≡ SI.⟦ N₃′ ⟧ ⟨$⟩ˡ inject+ 0 j
  agree₃ zero                               = refl
  agree₃ (suc zero)                         = refl
  agree₃ (suc (suc zero))                   = refl
  agree₃ (suc (suc (suc zero)))             = refl
  agree₃ (suc (suc (suc (suc zero))))       = refl
  agree₃ (suc (suc (suc (suc (suc zero))))) = refl

-- The gates at the bottom of their own wires (closed words, so that
-- frame-perm's idle wires above, none here, reduce away).
baseX : 4 ⊢ CTRL₁ (gate₁ {0} X-gate ↥) ≈
  CY.cyc 1 ↑ ↑ • (CTRL₁ (gate₁ {0} X-gate) ⇓ • CY.cyc⁻ 1 ↑ ↑)
baseX = PB.trans (step (gate₁ X-gate))
  (FR.frame-perm no-scalar {k = 4} {m = 0} N₁ N₁′ agree₁ (CTRL₁ (gate₁ {0} X-gate) ⇓))

base₂ : (h : Gate 2) → 5 ⊢ CTRL₁ (gate₂ {0} h ↥) ≈
  CY.cyc 2 ↑ ↑ • (CTRL₁ (gate₂ {0} h) ⇓ • CY.cyc⁻ 2 ↑ ↑)
base₂ CX-gate = PB.trans (step (gate₂ CX-gate))
  (FR.frame-perm no-scalar {k = 5} {m = 0} N₂ N₂′ agree₂ (CTRL₁ (gate₂ {0} CX-gate) ⇓))
base₂ HH-gate = PB.trans (step (gate₂ HH-gate))
  (FR.frame-perm no-scalar {k = 5} {m = 0} N₂ N₂′ agree₂ (CTRL₁ (gate₂ {0} HH-gate) ⇓))
base₂ SW-gate = PB.trans (step (gate₂ SW-gate))
  (FR.frame-perm no-scalar {k = 5} {m = 0} N₂ N₂′ agree₂ (CTRL₁ (gate₂ {0} SW-gate) ⇓))

baseCCX : 6 ⊢ CTRL₁ (gate₃ {0} CCX-gate ↥) ≈
  CY.cyc 3 ↑ ↑ • (CTRL₁ (gate₃ {0} CCX-gate) ⇓ • CY.cyc⁻ 3 ↑ ↑)
baseCCX = PB.trans (step (gate₃ CCX-gate))
  (FR.frame-perm no-scalar {k = 6} {m = 0} N₃ N₃′ agree₃ (CTRL₁ (gate₃ {0} CCX-gate) ⇓))

------------------------------------------------------------------------
-- At every height

-- The cycle of the wires from 2 up that moves g up one wire, below the
-- spare's wire (Y g = Z g ↑ ↑), and its inverse.
Z Z⁻ : Gen n → Circuit (₁₊ n)
Z (gate₀ ())
Z (gate₁ {k} X-gate)   = CY.cyc 1 ↓ᵏ k
Z (gate₂ {k} h)        = CY.cyc 2 ↓ᵏ k
Z (gate₃ {k} CCX-gate) = CY.cyc 3 ↓ᵏ k
Z (g ↥)                = Z g ↑
Z⁻ (gate₀ ())
Z⁻ (gate₁ {k} X-gate)   = CY.cyc⁻ 1 ↓ᵏ k
Z⁻ (gate₂ {k} h)        = CY.cyc⁻ 2 ↓ᵏ k
Z⁻ (gate₃ {k} CCX-gate) = CY.cyc⁻ 3 ↓ᵏ k
Z⁻ (g ↥)                = Z⁻ g ↑

private
  ⇓↑ : (w : Circuit n) → (w ↑) ⇓ ≡ (w ⇓) ↑
  ⇓↑ [ g ]ʷ  = refl
  ⇓↑ ε       = refl
  ⇓↑ (u • v) = Eq.cong₂ _•_ (⇓↑ u) (⇓↑ v)

  -- The swaps of wires 0 1 2, either way round, pass anything three
  -- wires up.
  comm-L : (X : Circuit n) → (₃₊ n) ⊢ (σ ↑ • σ) • X ↑ ↑ ↑ ≈ X ↑ ↑ ↑ • (σ ↑ • σ)
  comm-L X =
    PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl (PB.sym (comm-gate₂-w↑↑ SW-gate (X ↑))))
    (PB.trans (PB.sym PB.assoc)
    (PB.trans (PB.cong (lemma-cong↑ (σ • X ↑ ↑) (X ↑ ↑ • σ)
                         (PB.sym (comm-gate₂-w↑↑ SW-gate X))) PB.refl)
      PB.assoc)))

  comm-L⁻ : (X : Circuit n) → (₃₊ n) ⊢ (σ • σ ↑) • X ↑ ↑ ↑ ≈ X ↑ ↑ ↑ • (σ • σ ↑)
  comm-L⁻ X =
    PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl (lemma-cong↑ (σ • X ↑ ↑) (X ↑ ↑ • σ)
                                 (PB.sym (comm-gate₂-w↑↑ SW-gate X))))
    (PB.trans (PB.sym PB.assoc)
    (PB.trans (PB.cong (PB.sym (comm-gate₂-w↑↑ SW-gate (X ↑))) PB.refl)
      PB.assoc)))

-- A controlled gate one wire higher is the controlled gate with an
-- idle wire on top, its gate moved up by a cycle of the wires above
-- the spare.
move : (g : Gen n) → (₃₊ n) ⊢ CTRL₁ (g ↥) ≈ Z g ↑ ↑ • (CTRL₁ g ⇓ • Z⁻ g ↑ ↑)
move (gate₀ ())
move (gate₁ {k} X-gate)   = widen k baseX
move (gate₂ {k} CX-gate)  = widen k (base₂ CX-gate)
move (gate₂ {k} HH-gate)  = widen k (base₂ HH-gate)
move (gate₂ {k} SW-gate)  = widen k (base₂ SW-gate)
move (gate₃ {k} CCX-gate) = widen k baseCCX
move (g ↥) = PB.trans e₁ (PB.trans e₂ e₃)
  where
  C = CTRL₁ g
  L L⁻ : Circuit _
  L  = σ ↑ • σ
  L⁻ = σ • σ ↑
  A = Z g ↑ ↑ ↑
  A⁻ = Z⁻ g ↑ ↑ ↑
  B = C ⇓ ↑

  e₁ : _ ⊢ L • (CTRL₁ (g ↥) ↑ • L⁻) ≈ L • ((A • (B • A⁻)) • L⁻)
  e₁ = PB.cong PB.refl (PB.cong
         (lemma-cong↑ (CTRL₁ (g ↥)) (Z g ↑ ↑ • (C ⇓ • Z⁻ g ↑ ↑)) (move g)) PB.refl)

  e₂ : _ ⊢ L • ((A • (B • A⁻)) • L⁻) ≈ A • ((L • (B • L⁻)) • A⁻)
  e₂ =
    PB.trans (PB.cong PB.refl PB.assoc)
    (PB.trans (PB.sym PB.assoc)
    (PB.trans (PB.cong (comm-L (Z g)) PB.refl)
    (PB.trans PB.assoc
    (PB.cong PB.refl
      (PB.trans (PB.cong PB.refl PB.assoc)
      (PB.trans (PB.cong PB.refl (PB.cong PB.refl (PB.sym (comm-L⁻ (Z⁻ g)))))
      (PB.trans (PB.cong PB.refl (PB.sym PB.assoc))
        (PB.sym PB.assoc))))))))

  e₃ : _ ⊢ A • ((L • (B • L⁻)) • A⁻) ≈ A • ((L • ((C ↑) ⇓ • L⁻)) • A⁻)
  e₃ = Eq.subst (λ x → _ ⊢ A • ((L • (B • L⁻)) • A⁻) ≈ A • ((L • (x • L⁻)) • A⁻))
         (Eq.sym (⇓↑ C)) PB.refl
