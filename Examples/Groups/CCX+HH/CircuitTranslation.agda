------------------------------------------------------------------------
-- Presentations of groups
--
-- The two stages of Clément's translation at every width >= 4.
-- First encode a physical circuit into the complete four-state
-- auxiliary presentation.  A correct physical decoder then gives the
-- explicit finite circuit relation: decoded auxiliary equations plus
-- one encode/decode equation per physical generator.
--
-- The decoder is an explicit parameter, not a postulate.  This module
-- isolates the remaining constructive obligation from the already
-- proved all-width encoding and completeness transfer.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _+_)

module Examples.Groups.CCX+HH.CircuitTranslation (n : ℕ) where

open import Data.Fin.Base using (Fin ; fromℕ< ; toℕ)
import Data.Fin.Properties as FP
open import Data.Nat.Base using (_<_ ; s≤s ; z≤n) renaming (_^_ to _^ℕ_)
import Data.Nat.Properties as NP
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)
import Presentation.Base as PB

open import Examples.Groups.CCX+HH.Syntactics
import Examples.Groups.CCX+HH.StructuralEncoding as E
import Examples.Groups.CCX+HH.Semantics as C
import Examples.Groups.CCX+HH.Translation as Translation
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Semantics as S
import Examples.Groups.CCX+HH-TwoLevel.Reduction as Red
import Examples.Groups.CCX+HH.Subgroup.PresentationAt as Subgroup
open import Examples.Groups.CCX+HH.Subgroup.Action using (c00)
open import Examples.Groups.CCX+HH.Subgroup.CircuitCharge using (gen-closed)

private
  N = 2 ^ℕ (4 + n)
  p₀ : 0 < N
  p₀ = NP.m^n>0 2 (4 + n)
  p₁ : 1 < N
  p₁ = NP.^-monoʳ-≤ 2 {1} {4 + n} (s≤s z≤n)
  a b : Fin N
  a = fromℕ< p₀
  b = fromℕ< p₁
  a<b : toℕ a < toℕ b
  a<b = Eq.subst₂ _<_ (Eq.sym (FP.toℕ-fromℕ< p₀))
    (Eq.sym (FP.toℕ-fromℕ< p₁)) (s≤s z≤n)

module Auxiliary = Subgroup N a b a<b
private module A = PB (T._===_ {N})

e : Gen (4 + n) → Word Auxiliary.Edge
e g = Auxiliary.decode c00 (E.e g)

encode : Circuit (4 + n) → Word Auxiliary.Edge
encode = e ʷ

-- Re-encoding the Schreier word recovers the original auxiliary word.
source-back : ∀ w → Auxiliary.encode (encode w) A.≈ E.encode w
source-back [ g ]ʷ = Auxiliary.decode-loop (gen-closed c00 g)
source-back ε = A.refl
source-back (u • v) = A.cong (source-back u) (source-back v)

encoding-correct : ∀ w → S.⟦ Auxiliary.encode (encode w) ⟧ᵐ ≡ C.interpret w
encoding-correct w = Eq.trans (Red.sound-act (source-back w) S.𝕀)
  (C.encoding-correct w)

-- Equality of ordinary circuit matrices is now equality in the
-- complete auxiliary subgroup presentation, at symbolic width.
encode-complete : ∀ {u v} → C.interpret u ≡ C.interpret v →
  encode u Auxiliary.≈ encode v
encode-complete {u} {v} eq = Auxiliary.completeness
  (Eq.trans (encoding-correct u) (Eq.trans eq (Eq.sym (encoding-correct v))))

encode-sound : ∀ {u v} → encode u Auxiliary.≈ encode v →
  C.interpret u ≡ C.interpret v
encode-sound {u} {v} eq = Eq.trans (Eq.sym (encoding-correct u))
  (Eq.trans (Auxiliary.soundness eq) (encoding-correct v))

-- A decoder must produce genuine circuits with the stated matrices.
-- Neither a source word nor a semantic equality is a circuit axiom.
record Decoder : Set where
  field
    d : Auxiliary.Edge → Circuit (4 + n)
    correct : ∀ y → C.interpret (d y) ≡ S.⟦ Auxiliary.e y ⟧ᵐ

module Complete (decoder : Decoder) where
  open Decoder decoder
  module Relations = Translation Auxiliary._===_ e d
  open Relations public using (_===_ ; decoded ; recover)
  open Relations.Circuit public using (_≈_)

  private
    section : ∀ y → Relations.E (d y) Auxiliary.≈ [ y ]ʷ
    section y = Auxiliary.completeness
      (Eq.trans (encoding-correct (d y)) (correct y))
    module Sound = Relations.Section section

  complete : ∀ {u v} → C.interpret u ≡ C.interpret v → u ≈ v
  complete eq = Relations.encode-injective (encode-complete eq)

  sound : ∀ {u v} → u ≈ v → C.interpret u ≡ C.interpret v
  sound eq = encode-sound (Sound.encode-cong eq)
