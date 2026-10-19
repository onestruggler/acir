------------------------------------------------------------------------
-- Presentations of groups
--
-- Each three-wire generator is the decoding of its encoding.
--
-- A generator is a list of elements (`Lg`: a classical gate is a
-- theta-word, H on wire 1 is H₀ HH, H on wire 2 is H₀ times the HH of the
-- wires 0 and 2, `conv`), and that list against the decoding of its
-- encoding is a loop (Inst/Recovery).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.NaturalP.ThreeWire.Recovery where

open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; map)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_)
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open import Examples.Groups.CCX+H.NaturalP.ThreeWire.Kit
open import Examples.Groups.CCX+H.NaturalP.ThreeWire.Chain using (⦅_⦆)
open import Examples.Groups.CCX+H.NaturalP.ThreeWire.Elements
open import Examples.Groups.CCX+H.NaturalP.ThreeWire.Decoder
import Examples.Groups.CCX+H.NaturalP.ThreeWire.Inst.Recovery as RI
open import Examples.Groups.CCX+H.NaturalP.Transfer using (θ-cong)
import Examples.Groups.CCX+H.Syntactics as C
import Examples.Groups.CCX+H.Encoding as Enc
import Examples.Groups.CCX+H.NaturalP.Bridge as Br
import Examples.Groups.CCX+HH.Natural.Syntactics as N
open import Examples.Groups.CCX+HH.Natural.Axioms using (x₀ ; x₁ ; x₂ ; cx₀ ; cx₁ ; hh₀ ; hh₁ ; ccx₀)
open import Examples.Groups.CCX+HH.Natural.Engine using (⟪_⟫)
import Examples.Groups.CCX+HH.NaturalP.Syntactics as P
import Examples.Groups.CCX+HH.NaturalP.Converse as Conv
import Examples.Groups.CCX+HH.NaturalP.Schema as PS
import Examples.Groups.CCX+HH.NaturalP.Bridge as PBr

private
  module R3 = SR (PP.word-setoid (3 VRel,_===_))
  open R3

------------------------------------------------------------------------
-- The generators as elements

-- HH on the wires 0 and 2: the swap of the wires 1, 2 around HH.
hh02 : N.Circuit 3
hh02 = ⟪ cx₁ ∷ hh₁ ∷ cx₁ ∷ hh₁ ∷ cx₁ ∷ hh₀ ∷ cx₁ ∷ hh₁ ∷ cx₁ ∷ hh₁ ∷ cx₁ ∷ [] ⟫

Lg : C.Gen 3 → List El
Lg (C.gate₀ ())
Lg (C.gate₀ () C.↥)
Lg (C.gate₀ () C.↥ C.↥)
Lg (C.gate₀ () C.↥ C.↥ C.↥)
Lg (C.gate₁ C.X-gate)             = th ⟪ x₀ ∷ [] ⟫ ∷ []
Lg (C.gate₁ C.X-gate C.↥)         = th ⟪ x₁ ∷ [] ⟫ ∷ []
Lg (C.gate₁ C.X-gate C.↥ C.↥)     = th ⟪ x₂ ∷ [] ⟫ ∷ []
Lg (C.gate₂ C.CX-gate)            = th ⟪ cx₀ ∷ [] ⟫ ∷ []
Lg (C.gate₂ C.CX-gate C.↥)        = th ⟪ cx₁ ∷ [] ⟫ ∷ []
Lg (C.gate₃ C.CCX-gate)           = th ⟪ ccx₀ ∷ [] ⟫ ∷ []
Lg (C.gate₁ C.H-gate)             = hE ∷ []
Lg (C.gate₁ C.H-gate C.↥)         = hE ∷ th ⟪ hh₀ ∷ [] ⟫ ∷ []
Lg (C.gate₁ C.H-gate C.↥ C.↥)     = hE ∷ th hh02 ∷ []

private
  -- The swap word of Natural on the wires 1, 2 is the swap gate.
  Ex↑ : 3 ⊢ Θ (N.Ex N.↑) ≈ σ ↑
  Ex↑ = θ-cong (PS.emb (P.lemma-cong↑ (PBr.ι N.Ex) P.σ Conv.ex))

  -- H on wire 1 crosses the swap of the wires 1, 2.
  H↑-σ↑ : 3 ⊢ H ↑ • σ ↑ ≈ σ ↑ • H ↑ ↑
  H↑-σ↑ = lemma-cong↑ (H • σ) (σ • H ↑) (sym-rule (σ-nat₁ H-gate))

  σ↑² : 3 ⊢ σ ↑ • σ ↑ ≈ ε
  σ↑² = lemma-cong↑ (σ • σ) ε σ-invol

  σ↑-H : 3 ⊢ σ ↑ • H ≈ H • σ ↑
  σ↑-H = comm-gate₁-w↑ H-gate σ

  h2 : 3 ⊢ H • Θ hh02 ≈ H ↑ ↑
  h2 = begin
    H • Θ hh02
      ≈⟨ cong refl (Θstep hh02 (N.Ex N.↑ • ([ hh₀ ]ʷ • N.Ex N.↑)) Eq.refl) ⟩
    H • (Θ (N.Ex N.↑) • ((H • H ↑) • Θ (N.Ex N.↑)))
      ≈⟨ cong refl (cong Ex↑ (cong refl Ex↑)) ⟩
    H • (σ ↑ • ((H • H ↑) • σ ↑))
      ≈⟨ sym assoc ⟩
    (H • σ ↑) • ((H • H ↑) • σ ↑)
      ≈⟨ cong (sym σ↑-H) refl ⟩
    (σ ↑ • H) • ((H • H ↑) • σ ↑)
      ≈⟨ assoc ⟩
    σ ↑ • (H • ((H • H ↑) • σ ↑))
      ≈⟨ cong refl (cong refl assoc) ⟩
    σ ↑ • (H • (H • (H ↑ • σ ↑)))
      ≈⟨ cong refl (cancel H² _) ⟩
    σ ↑ • (H ↑ • σ ↑)
      ≈⟨ cong refl H↑-σ↑ ⟩
    σ ↑ • (σ ↑ • H ↑ ↑)
      ≈⟨ cancel σ↑² _ ⟩
    H ↑ ↑
      ∎

conv : ∀ x → 3 ⊢ Br.ι [ x ]ʷ ≈ ⦅ map ⟦_⟧ₑ (Lg x) ⦆
conv (C.gate₀ ())
conv (C.gate₀ () C.↥)
conv (C.gate₀ () C.↥ C.↥)
conv (C.gate₀ () C.↥ C.↥ C.↥)
conv (C.gate₁ C.X-gate)         = sym right-unit
conv (C.gate₁ C.X-gate C.↥)     = sym right-unit
conv (C.gate₁ C.X-gate C.↥ C.↥) = sym right-unit
conv (C.gate₂ C.CX-gate)        = sym right-unit
conv (C.gate₂ C.CX-gate C.↥)    = sym right-unit
conv (C.gate₃ C.CCX-gate)       = sym right-unit
conv (C.gate₁ C.H-gate)         = refl
conv (C.gate₁ C.H-gate C.↥)     = sym (trans (cong refl right-unit) (cancel H² (H ↑)))
conv (C.gate₁ C.H-gate C.↥ C.↥) = sym h2

------------------------------------------------------------------------
-- The recovery equations

loop : ∀ x → 3 ⊢ ⦅ map ⟦_⟧ₑ (Lg x ++ invL (Lw (Enc.e x))) ⦆ ≈ ε
loop (C.gate₀ ())
loop (C.gate₀ () C.↥)
loop (C.gate₀ () C.↥ C.↥)
loop (C.gate₀ () C.↥ C.↥ C.↥)
loop (C.gate₁ C.X-gate)         = RI.i0
loop (C.gate₁ C.X-gate C.↥)     = RI.i1
loop (C.gate₁ C.X-gate C.↥ C.↥) = RI.i2
loop (C.gate₂ C.CX-gate)        = RI.i3
loop (C.gate₂ C.CX-gate C.↥)    = RI.i4
loop (C.gate₃ C.CCX-gate)       = RI.i5
loop (C.gate₁ C.H-gate)         = RI.i6
loop (C.gate₁ C.H-gate C.↥)     = RI.i7
loop (C.gate₁ C.H-gate C.↥ C.↥) = RI.i8

recover : ∀ x → 3 ⊢ Br.ι [ x ]ʷ ≈ Br.ι (D′ (Enc.e x))
recover x = trans (conv x) (trans (from-loop (Lg x) (Lw (Enc.e x)) (loop x)) (sym (D-flat (Enc.e x))))
