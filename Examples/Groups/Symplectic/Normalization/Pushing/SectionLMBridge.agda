------------------------------------------------------------------------
-- Presentations of groups
--
-- Section's box interpretations ([_]ᵐ, [_]ᵛᵇ, [_]ˡ', [_]ᵐˡ') are defined
-- by the same clauses as LM-Sym's, but are distinct functions; these
-- bridges lift the atomic ML'-Top equalities (abox-eq / bbox-eq /
-- dbox-eq, and the definitional E-box agreement) to the composite boxes
-- by structural induction, so LM-Sym-stated pushes can be reused against
-- Section's coset boxes.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Symplectic.Normalization.Pushing.SectionLMBridge (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Notations
open import Data.Product using (_,_)
open import Data.Vec using (Vec ; _∷_ ; [])
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; refl ; cong ; cong₂)

open import ForStdlib.Data.Fin.Mod
open PrimeModulus p-2 p-prime
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic using (_↑)
open import Word.Base using (_•_)
open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime
import Examples.Groups.Symplectic.Lemmas.LM-Sym p-2 p-prime as LM
open import Examples.Groups.Symplectic.BR.Two.ML'-Top p-2 p-prime using (abox-eq ; bbox-eq ; dbox-eq)

private variable
  n : ℕ

-- (E box needs no bridge: definitionally S^ (- ·) in both, so the base
-- cases below discharge by refl.)

vbbox-eq : ∀ (vb : Vec B n) → [ vb ]ᵛᵇ ≡ LM.[ vb ]ᵛᵇ
vbbox-eq []       = refl
vbbox-eq (x ∷ v)  = cong₂ _•_ (cong (_↑) (vbbox-eq v)) (bbox-eq x)

vdbox-eq : ∀ (vd : Vec D n) → [ vd ]ᵛᵈ ≡ LM.[ vd ]ᵛᵈ
vdbox-eq []       = refl
vdbox-eq (x ∷ v)  = cong₂ _•_ (dbox-eq x) (cong (_↑) (vdbox-eq v))

mbox-eq : ∀ (m : M n) → [ m ]ᵐ ≡ LM.[ m ]ᵐ
mbox-eq {0}      _            = refl
mbox-eq {₁₊ n} ([] , e)       = refl
mbox-eq {₁₊ n} (x ∷ vd , e)   = cong₂ _•_ (dbox-eq x) (cong (_↑) (mbox-eq (vd , e)))

l'box-eq : ∀ (l : L' n) → [ l ]ˡ' ≡ LM.[ l ]ˡ'
l'box-eq {0}      _         = refl
l'box-eq {₁₊ n} (vb , a)    = cong₂ _•_ (vbbox-eq vb) (abox-eq a)
