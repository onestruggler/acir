------------------------------------------------------------------------
-- Presentations of groups
--
-- Clément's two translations for physical CCX+H circuits at width >= 4.
-- The structural encoder has independent tensor semantics and lands
-- in the complete four-state scaled auxiliary subgroup presentation.
-- A physical decoder gives the circuit equations and both directions
-- of their matrix correctness.  Its construction remains explicit in
-- the Decoder parameter; no semantic equality is made into an axiom.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _+_)

module Examples.Groups.CCX+H.CircuitTranslation (n : ℕ) where

open import Data.Fin.Base using (Fin ; fromℕ< ; toℕ)
import Data.Fin.Properties as FP
open import Data.Nat.Base using (_*_ ; _<_ ; s≤s ; z≤n) renaming (_^_ to _^ℕ_)
import Data.Nat.Properties as NP
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)
import Presentation.Base as PB

open import Examples.Groups.CCX+H.Syntactics
import Examples.Groups.CCX+H.GeneralN.Semantics as Sem
import Examples.Groups.CCX+H.GeneralN.Action as Action
import Examples.Groups.CCX+H.GeneralN.CircuitCharge as Charge
import Examples.Groups.CCX+H.GeneralN.PresentationAt as Subgroup
import Examples.Groups.CCX+HH.Translation as Translation
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as S

open Action using (c00)
module C = Sem.At (3 + n)

private
  k = 2 ^ℕ (3 + n)
  N = k * 2
  dimension : 2 ^ℕ (4 + n) ≡ N
  dimension = NP.*-comm 2 k
  positive : 0 < k
  positive = NP.m^n>0 2 (3 + n)
  p₀ : 0 < N
  p₀ = Eq.subst (0 <_) dimension (NP.m^n>0 2 (4 + n))
  p₁ : 1 < N
  p₁ = Eq.subst (1 <_) dimension
    (NP.^-monoʳ-≤ 2 {1} {4 + n} (s≤s z≤n))
  a b : Fin N
  a = fromℕ< p₀
  b = fromℕ< p₁
  a<b : toℕ a < toℕ b
  a<b = Eq.subst₂ _<_ (Eq.sym (FP.toℕ-fromℕ< p₀))
    (Eq.sym (FP.toℕ-fromℕ< p₁)) (s≤s z≤n)
  module M = S.Dim k
  module A = PB (T._===ᴸ_ {N})

module Auxiliary = Subgroup k positive a b a<b

private
  cast-state : ∀ {j l} (p : j ≡ l) c w →
    Action.At.state l c (Sem.cast-word p w) ≡ Action.At.state j c w
  cast-state Eq.refl c w = Eq.refl

  compile-closed : ∀ g → Auxiliary.state c00 (C.compile-gen g) ≡ c00
  compile-closed g = Eq.trans (cast-state dimension c00 _)
    (Charge.At.gen-closed n g)

e : Gen (4 + n) → Word Auxiliary.Edge
e g = Auxiliary.decode c00 (C.compile-gen g)

encode : Circuit (4 + n) → Word Auxiliary.Edge
encode = e ʷ

source-back : ∀ w → Auxiliary.encode (encode w) A.≈ C.compile w
source-back [ g ]ʷ = Auxiliary.decode-loop (compile-closed g)
source-back ε = A.refl
source-back (u • v) = A.cong (source-back u) (source-back v)

encoding-correct : ∀ w → M.⟦ Auxiliary.encode (encode w) ⟧ᴸ ≡ C.interpret w
encoding-correct w = Eq.trans (S.soundness k (source-back w))
  (C.encoding-correct w)

encode-complete : ∀ {u v} → C.interpret u ≡ C.interpret v →
  encode u Auxiliary.≈ encode v
encode-complete {u} {v} eq = Auxiliary.completeness
  (Eq.trans (encoding-correct u) (Eq.trans eq (Eq.sym (encoding-correct v))))

encode-sound : ∀ {u v} → encode u Auxiliary.≈ encode v →
  C.interpret u ≡ C.interpret v
encode-sound {u} {v} eq = Eq.trans (Eq.sym (encoding-correct u))
  (Eq.trans (Auxiliary.soundness eq) (encoding-correct v))

record Decoder : Set where
  field
    d : Auxiliary.Edge → Circuit (4 + n)
    correct : ∀ y → C.interpret (d y) ≡ M.⟦ Auxiliary.e y ⟧ᴸ

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
