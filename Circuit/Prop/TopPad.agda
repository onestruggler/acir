------------------------------------------------------------------------
-- Presentations of groups
--
-- Circuit.TopPad.Equivalence for a PROP: a family's relation lifted by
-- Lift-To-Prop, and the same rules with the swap rules, all on their
-- own wires and padded by Top-Pad, generate the same congruence
--
-- The swap rules are stated once here on their own wires (_SymB,_===_:
-- σ σ = ε on two wires, σ-nat_k on k + 1), and a family adds its own
-- rules on their own wires (_PBase,_===_ puts the two side by side).
-- The swap rules have the same rules on both sides whatever the family
-- (their words are closed, so ⇓'d they are the same words one wire
-- wider), so a family owes SameRules for its own rules only
-- (FamilyRules), and `same` completes it with the swap rules'.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Circuit.Prop.TopPad (Gate : ℕ → Set) (Ex-gate : Gate 2) where

open import Notations
open import Word.Base using ([_]ʷ ; ε ; _•_)

open import Circuit.Prop Gate Ex-gate
open import Circuit.TopPad Gate using (_⇓ ; module Top-Pad)
import Circuit.TopPad.Equivalence Gate as Equivalence
import Presentation.Base as PB

private
  variable
    n : ℕ
    w v : Circuit n

------------------------------------------------------------------------
-- The swap rules on their own wires

infix 4 _SymB,_===_
data _SymB,_===_ : (n : ℕ) → CRel n where
  σ-invᴮ  : 2 SymB, σ • σ === ε
  σ-nat₁ᴮ : (h : Gate 1) → 2 SymB,
            [ gate₁ h ]ʷ • σ[ 1 ] === σ[ 1 ] • [ gate₁ h ]ʷ ↑
  σ-nat₂ᴮ : (h : Gate 2) → 3 SymB,
            [ gate₂ h ]ʷ • σ[ 2 ] === σ[ 2 ] • [ gate₂ h ]ʷ ↑
  σ-nat₃ᴮ : (h : Gate 3) → 4 SymB,
            [ gate₃ h ]ʷ • σ[ 3 ] === σ[ 3 ] • [ gate₃ h ]ʷ ↑

------------------------------------------------------------------------
-- A family's rules with the swap rules

module Lift≅Top-Pad-Prop
  -- The family's rules at every width, lifted by Lift-To-Prop ...
  (_SRel,_===_ : (n : ℕ) → CRel n)
  -- ... and on their own wires.
  (_Base,_===_ : (n : ℕ) → CRel n)
  where

  private module LP = Lift-To-Prop _SRel,_===_

  infix 4 _PBase,_===_
  data _PBase,_===_ : (n : ℕ) → CRel n where
    σbase : n SymB, w === v → n PBase, w === v
    sbase : n Base, w === v → n PBase, w === v

  module TP = Top-Pad _PBase,_===_
  module E  = Equivalence.Lift≅Top-Pad LP._Prop,_===_ _PBase,_===_

  open E public using (_LRel,_===_ ; _TRel,_===_ ; _⊢ᴸ_≈_ ; _⊢ᵀ_≈_)

  -- The swap rules on the bottom wires of every wider circuit.
  σ-inv↓ : (₂₊ n) TRel, σ • σ === ε
  σ-inv↓ {0}    = TP.srel (σbase σ-invᴮ)
  σ-inv↓ {₁₊ n} = TP.cong↓ σ-inv↓

  σ-nat₁↓ : (h : Gate 1) → (₂₊ n) TRel,
            [ gate₁ h ]ʷ • σ[ 1 ] === σ[ 1 ] • [ gate₁ h ]ʷ ↑
  σ-nat₁↓ {0}    h = TP.srel (σbase (σ-nat₁ᴮ h))
  σ-nat₁↓ {₁₊ n} h = TP.cong↓ (σ-nat₁↓ h)

  σ-nat₂↓ : (h : Gate 2) → (₃₊ n) TRel,
            [ gate₂ h ]ʷ • σ[ 2 ] === σ[ 2 ] • [ gate₂ h ]ʷ ↑
  σ-nat₂↓ {0}    h = TP.srel (σbase (σ-nat₂ᴮ h))
  σ-nat₂↓ {₁₊ n} h = TP.cong↓ (σ-nat₂↓ h)

  σ-nat₃↓ : (h : Gate 3) → (₄₊ n) TRel,
            [ gate₃ h ]ʷ • σ[ 3 ] === σ[ 3 ] • [ gate₃ h ]ʷ ↑
  σ-nat₃↓ {0}    h = TP.srel (σbase (σ-nat₃ᴮ h))
  σ-nat₃↓ {₁₊ n} h = TP.cong↓ (σ-nat₃↓ h)

  -- What the family owes: SameRules for its own rules.
  record FamilyRules : Set where
    field
      pad    : n SRel, w === v → n ⊢ᵀ w ≈ v
      unpad  : n Base, w === v → n ⊢ᴸ w ≈ v
      srel-⇓ : n SRel, w === v → (₁₊ n) ⊢ᴸ w ⇓ ≈ v ⇓

  same : FamilyRules → E.SameRules
  same fam = record { pad = pad ; unpad = unpad ; srel-⇓ = srel-⇓ }
    where
    module F = FamilyRules fam

    pad : LP._Prop,_===_ n w v → n ⊢ᵀ w ≈ v
    pad (LP.σrel σ-inv)      = PB.axiom σ-inv↓
    pad (LP.σrel (σ-nat₁ h)) = PB.axiom (σ-nat₁↓ h)
    pad (LP.σrel (σ-nat₂ h)) = PB.axiom (σ-nat₂↓ h)
    pad (LP.σrel (σ-nat₃ h)) = PB.axiom (σ-nat₃↓ h)
    pad (LP.srel s)          = F.pad s

    unpad : n PBase, w === v → n ⊢ᴸ w ≈ v
    unpad (σbase σ-invᴮ)       = PB.axiom (LP.srel (LP.σrel σ-inv))
    unpad (σbase (σ-nat₁ᴮ h))  = PB.axiom (LP.srel (LP.σrel (σ-nat₁ h)))
    unpad (σbase (σ-nat₂ᴮ h))  = PB.axiom (LP.srel (LP.σrel (σ-nat₂ h)))
    unpad (σbase (σ-nat₃ᴮ h))  = PB.axiom (LP.srel (LP.σrel (σ-nat₃ h)))
    unpad (sbase b)            = F.unpad b

    -- A swap rule's words are closed: ⇓'d, the same rule one wire wider.
    srel-⇓ : LP._Prop,_===_ n w v → (₁₊ n) ⊢ᴸ w ⇓ ≈ v ⇓
    srel-⇓ (LP.σrel σ-inv)      = PB.axiom (LP.srel (LP.σrel σ-inv))
    srel-⇓ (LP.σrel (σ-nat₁ h)) = PB.axiom (LP.srel (LP.σrel (σ-nat₁ h)))
    srel-⇓ (LP.σrel (σ-nat₂ h)) = PB.axiom (LP.srel (LP.σrel (σ-nat₂ h)))
    srel-⇓ (LP.σrel (σ-nat₃ h)) = PB.axiom (LP.srel (LP.σrel (σ-nat₃ h)))
    srel-⇓ (LP.srel s)          = F.srel-⇓ s
