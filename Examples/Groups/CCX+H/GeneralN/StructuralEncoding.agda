------------------------------------------------------------------------
-- Presentations of groups
--
-- A structural scaled encoder.  Classical gates use the recursive
-- dyadic encoder.  A Hadamard at wire p is expressed by the telescoping
-- chain HH_(p-1,p) ... HH_(0,1) H_0.  Thus no enumeration of basis
-- indices or wire-permutation circuit is needed by this encoding.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.GeneralN.StructuralEncoding where

open import Data.Nat.Base using (ℕ ; zero ; suc) renaming (_^_ to _^ℕ_)
import Data.Fin.Base as Fin
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Word.Base using (Word ; ε ; _•_ ; _ʷ)
open import Examples.Groups.CCX+H.Syntactics
import Examples.Groups.CCX+HH.Syntactics as D
import Examples.Groups.CCX+HH.StructuralEncoding as DE
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as T

private variable n : ℕ

-- Preserve the indexed wire placement rather than discarding its bound.
classify : Gen n → D.Gen n ⊎ Fin.Fin n
classify (gate₀ ())
classify (gate₁ X-gate) = inj₁ D.X-gen
classify (gate₁ H-gate) = inj₂ Fin.zero
classify (gate₂ CX-gate) = inj₁ D.CX-gen
classify (gate₃ CCX-gate) = inj₁ D.CCX-gen
classify (g ↥) with classify g
... | inj₁ dg = inj₁ (dg D.↥)
... | inj₂ p = inj₂ (Fin.suc p)

prefix : Fin.Fin n → D.Circuit n
prefix Fin.zero = ε
prefix {suc zero} (Fin.suc ())
prefix {suc (suc n)} (Fin.suc p) = (prefix p D.↑) • D.HH

Levels : ℕ → Set
Levels n = Word (T.Genᴸ (2 ^ℕ n))

e : Gen n → Levels n
e g with classify g
... | inj₁ dg = T.⌊ DE.e dg ⌋ʷ
... | inj₂ p = T.⌊ DE.encode (prefix p) ⌋ʷ • T.H

encode : Circuit n → Levels n
encode = e ʷ
