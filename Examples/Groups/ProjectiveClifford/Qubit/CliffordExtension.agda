------------------------------------------------------------------------
-- Presentations of groups
--
-- The projection CMS-group ↠ Sp(2n,2) of the qubit Clifford
-- extension (p = 2).
--
-- The extension itself is now built in
-- Examples.Groups.ProjectiveClifford.Qubit.CliffordGroup, which packages the
-- Clifford group together with incl / proj and the exactness proofs as a
-- ForStdlib.Algebra.Construct.Extension record.  This module only
-- re-exports the projection side under its former names, so that
--
--     proj [w] = ⟦ w ⟧ (the symplectic map of w)
--
-- and its well-definedness / homomorphism properties stay available
-- without duplicating the proofs.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.ProjectiveClifford.Qubit.CliffordExtension where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations
open import Word.Base using (Word ; ε ; _•_)

open import ForStdlib.Data.Fin.Mod.Prime.Two using (p-2 ; p-prime)

import Examples.Groups.Symplectic.Syntactics p-2 p-prime as Syn
open Syn.Symplectic using (Gen)
open import Examples.Groups.Symplectic.Semantics p-2 p-prime as Sem
  using (Symplectic ; _≈ˢ_ ; _∘ˢ_ ; εˢ ; Sp-group)

open import Examples.Groups.ProjectiveClifford.Qubit.CliffordGroup
  using (CMS-extension ; CMS-group ; _≈ᶜ_ ; proj ; proj-cong ; cact-proj₂)
  public

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The homomorphism laws, which hold definitionally

-- act (w • v) = act w ∘ act v.
proj-∙ : (w v : Word (Gen n)) → proj (w • v) ≈ˢ (proj w ∘ˢ proj v)
proj-∙ w v P = Eq.refl

proj-ε : proj {n} ε ≈ˢ εˢ
proj-ε P = Eq.refl
