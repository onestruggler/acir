------------------------------------------------------------------------
-- Presentations of groups
--
-- At width zero there are no gates, hence only the identity circuit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.Zero where

open import Word.Base using (WRel ; [_]ʷ ; ε ; _•_)
import Presentation.Base as PB
open import Examples.Groups.CCX+H.Syntactics

data Empty : WRel (Gen 0) where

module P = PB Empty

identity : ∀ (w : Circuit 0) → w P.≈ ε
identity [ gate₀ () ]ʷ
identity ε = P.refl
identity (w • v) =
  P.trans (P.cong (identity w) (identity v)) P.left-unit

complete : ∀ (w v : Circuit 0) → w P.≈ v
complete w v = P.trans (identity w) (P.sym (identity v))
