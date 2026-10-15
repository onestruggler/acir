------------------------------------------------------------------------
-- Presentations of groups
--
-- The controlled Toffolis C3Xa and C3Xb on their own five wires.
--
-- Both are words in the swap and the Toffoli, so they are classical
-- circuits (GeneralN.Classical).  Encoded by transpositions
-- (NaturalP.ClassicalWords) each is a word of X letters, as is the
-- Toffoli on the odd coordinates, and the two are compared by their
-- permutations of the 32 indices (NaturalP.PermCheck).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.CtrlBase5 where

open import Data.Bool.Base using (T)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _^_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality
open import Word.Base using ([_]ʷ ; ε ; _•_)
open import Notations using (₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.CCX+HH-TwoLevel.Ring using (isCommutativeRing-D ; adj-D ; ½ᴰ)
open import Examples.Groups.CCX+HH.EncodingSemantics.Blocks isCommutativeRing-D adj-D ½ᴰ
  using (encode-parallel)
open import Examples.Groups.CCX+HH.EncodingSemantics.Binary using (alternating)
import Examples.Groups.CCX+HH.Natural.Syntactics as N
import Examples.Groups.CCX+HH.StructuralEncoding as E
import Examples.Groups.CCX+HH.GeneralN.Classical as C
open import Examples.Groups.CCX+HH.GeneralN.ClassicalSemantics
  using (quantum ; physical-correct)
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (τ)
open import Examples.Groups.CCX+HH.NaturalP.Ctrl using (C3Xa ; C3Xb)
open import Examples.Groups.CCX+HH.NaturalP.Blocks2 using (ctrlA)
open import Examples.Groups.CCX+HH.NaturalP.Columns using (ctrl-word)
open import Examples.Groups.CCX+HH.NaturalP.ClassicalWords using (encodeᶜ ; encodeᶜ-action)
open import Examples.Groups.CCX+HH.NaturalP.PermCheck using (same-perm ; same-perm-sound)

private
  variable
    n : ℕ

  σ : C.Circuit (₂₊ n)
  σ = [ C.gate₂ C.SWAP-gate ]ʷ

  ccx : C.Circuit (₃₊ n)
  ccx = [ C.gate₃ C.CCX-gate ]ʷ

  -- NaturalP.Ctrl's T₁ and T₂ on five wires.
  t₁ t₂ c3xa c3xb : C.Circuit 5
  t₁ = σ • σ C.↑ • σ • σ C.↑ C.↑ C.↑ • ccx C.↑ • σ C.↑ C.↑ C.↑ • σ • σ C.↑ • σ
  t₂ = σ C.↑ C.↑ • σ C.↑ C.↑ C.↑ • σ C.↑ C.↑ • ccx C.↑ C.↑
     • σ C.↑ C.↑ • σ C.↑ C.↑ C.↑ • σ C.↑ C.↑
  c3xa = t₁ • t₂ • t₁ • t₂
  c3xb = σ C.↑ • σ C.↑ C.↑ • σ C.↑ C.↑ C.↑ • c3xa • σ C.↑ C.↑ C.↑ • σ C.↑ C.↑ • σ C.↑

  -- The same words as the translations of the gadgets.
  eqa : τ (C3Xa {zero}) ≡ C.physical c3xa
  eqa = refl

  eqb : τ (C3Xb {zero}) ≡ C.physical c3xb
  eqb = refl

  -- The Toffolis on the odd coordinates.
  Wa Wb : E.Levels 5
  Wa = encode-parallel (alternating (2 ^ ₄₊ zero)) ε (E.encode (N.CCX {suc zero}))
  Wb = encode-parallel (alternating (2 ^ ₄₊ zero)) ε (E.encode (N.CCX {zero} N.↑))

  chk-a : T (same-perm (encodeᶜ c3xa) Wa)
  chk-a = tt

  chk-b : T (same-perm (encodeᶜ c3xb) Wb)
  chk-b = tt

C3Xa-base : ∀ v → quantum (τ (C3Xa {zero})) v ≡ ctrlA (2 ^ ₄₊ zero) (quantum (N.CCX {suc zero})) v
C3Xa-base v = trans (cong (λ w → quantum w v) {x = τ (C3Xa {zero})} {y = C.physical c3xa} eqa)
  (trans (physical-correct c3xa v)
  (trans (sym (encodeᶜ-action c3xa v))
  (trans (same-perm-sound (encodeᶜ c3xa) Wa chk-a v) (ctrl-word (N.CCX {suc zero}) v))))

C3Xb-base : ∀ v → quantum (τ (C3Xb {zero})) v ≡ ctrlA (2 ^ ₄₊ zero) (quantum (N.CCX {zero} N.↑)) v
C3Xb-base v = trans (cong (λ w → quantum w v) {x = τ (C3Xb {zero})} {y = C.physical c3xb} eqb)
  (trans (physical-correct c3xb v)
  (trans (sym (encodeᶜ-action c3xb v))
  (trans (same-perm-sound (encodeᶜ c3xb) Wb chk-b v) (ctrl-word (N.CCX {zero} N.↑) v))))
