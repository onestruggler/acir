------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the five-wire derivations (placed)
--
-- Each distinct window of the derivations of Five.D, evaluated once
-- (Five.Win).  Written by `scratchpad/five/winlib5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Wins.WP07 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)

wp1270 : Base 4 → WsL → ⟪ (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ
wp1270 c4 L = pw3 c4 L (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) tt tt Eq.refl

wp1271 : Base 4 → WsL → ⟪ (CK42 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ S1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ CS12 ∷ CS12 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CK42 ∷ CCZ234 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι1 ∷ S3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι1 ∷ CS23 ∷ CS23 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CCZ234 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι1 ∷ S3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι1 ∷ CS23 ∷ CS23 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CK42 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ S1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ CS12 ∷ CS12 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) ⟫ʷ
wp1271 c4 L = pw0 c4 L (CK42 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ S1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ CS12 ∷ CS12 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CK42 ∷ CCZ234 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι1 ∷ S3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι1 ∷ CS23 ∷ CS23 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (CK42 ∷ CCZ234 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι1 ∷ S3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι1 ∷ CS23 ∷ CS23 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CK42 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ S1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ CS12 ∷ CS12 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) tt tt Eq.refl

wp1272 : Base 4 → WsL → ⟪ (CK41 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ
wp1272 c4 L = pw3 c4 L (CK41 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) tt tt Eq.refl

wp1273 : Base 4 → WsL → ⟪ (CK42 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ S1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CK42 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι1 ∷ S3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι1 ∷ S3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CK42 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ S1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) ⟫ʷ
wp1273 c4 L = pw0 c4 L (CK42 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ S1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CK42 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι1 ∷ S3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (CK42 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι1 ∷ S3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CK42 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ S1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) tt tt Eq.refl

wp1274 : Base 4 → WsL → ⟪ (X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp1274 c4 L = pw1 c4 L (X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CK40 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ []) [] tt tt Eq.refl

wp1275 : Base 4 → WsL → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ014 ∷ Toff201 ∷ []) ⟫ʷ
wp1275 c4 L = pw3 c4 L (CCZ014 ∷ []) (Toff201 ∷ CCZ014 ∷ Toff201 ∷ []) tt tt Eq.refl

wp1276 : Base 4 → WsL → ⟪ (CCZ014 ∷ Toff301 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CS34 ∷ CCZ014 ∷ []) ⟫ʷ
wp1276 c4 L = pw2 c4 L (CCZ014 ∷ Toff301 ∷ CS34 ∷ []) (Toff301 ∷ CS34 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1277 : Base 4 → WsL → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) ⟫ʷ
wp1277 c4 L = pw2 c4 L (CCZ014 ∷ []) (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wp1278 : Base 4 → WsL → ⟪ (CCZ024 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ X0 ∷ CCZ024 ∷ []) ⟫ʷ
wp1278 c4 L = pw1 c4 L (CCZ024 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1279 : Base 4 → WsL → ⟪ (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ X0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) ⟫ʷ
wp1279 c4 L = pw2 c4 L (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wp1280 : Base 4 → WsL → ⟪ (CCZ024 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS04 ∷ X0 ∷ CCZ024 ∷ []) ⟫ʷ
wp1280 c4 L = pw1 c4 L (CCZ024 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1281 : Base 4 → WsL → ⟪ (S4 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ
wp1281 c4 L = pw1 c4 L (S4 ∷ CS04⁻ ∷ []) (X0 ∷ CS04 ∷ X0 ∷ []) tt tt Eq.refl

wp1282 : Base 4 → WsL → ⟪ (CCZ024 ∷ S4 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ CS04⁻ ∷ CCZ024 ∷ []) ⟫ʷ
wp1282 c4 L = pw1 c4 L (CCZ024 ∷ S4 ∷ CS04⁻ ∷ []) (S4 ∷ CS04⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1283 : Base 4 → WsL → ⟪ (S4 ∷ CS04⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ S4 ∷ CS04⁻ ∷ []) ⟫ʷ
wp1283 c4 L = pw2 c4 L (S4 ∷ CS04⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ S4 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp1284 : Base 4 → WsL → ⟪ (CCZ024 ∷ X0 ∷ CZ24 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CCZ024 ∷ []) ⟫ʷ
wp1284 c4 L = pw1 c4 L (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (X0 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1285 : Base 4 → WsL → ⟪ (CCZ024 ∷ CZ24 ∷ []) ⟫ʷ ≈ ⟪ (CZ24 ∷ CCZ024 ∷ []) ⟫ʷ
wp1285 c4 L = pw1 c4 L (CCZ024 ∷ CZ24 ∷ []) (CZ24 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1286 : Base 4 → WsL → ⟪ (CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ []) ⟫ʷ
wp1286 c4 L = pw2 c4 L (CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ []) tt tt Eq.refl

wp1287 : Base 4 → WsL → ⟪ (CX13 ∷ Toff301 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CX13 ∷ Toff301 ∷ []) ⟫ʷ
wp1287 c4 L = pw2 c4 L (CX13 ∷ Toff301 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CX13 ∷ Toff301 ∷ []) tt tt Eq.refl

wp1288 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ014 ∷ CCZ024 ∷ []) ⟫ʷ
wp1288 c4 L = pw3 c4 L (CCZ024 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ014 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1289 : Base 4 → WsL → ⟪ (CCZ014 ∷ CX13 ∷ CCZ014 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ Toff301 ∷ []) ⟫ʷ
wp1289 c4 L = pw2 c4 L (CCZ014 ∷ CX13 ∷ CCZ014 ∷ Toff301 ∷ []) (CX13 ∷ Toff301 ∷ []) tt tt Eq.refl

wp1290 : Base 4 → WsL → ⟪ (CS34 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CS34 ∷ []) ⟫ʷ
wp1290 c4 L = pw2 c4 L (CS34 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CS34 ∷ []) tt tt Eq.refl

wp1291 : Base 4 → WsL → ⟪ (CS34⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CS34⁻ ∷ []) ⟫ʷ
wp1291 c4 L = pw2 c4 L (CS34⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CS34⁻ ∷ []) tt tt Eq.refl

wp1292 : Base 4 → WsL → ⟪ (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ X0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) ⟫ʷ
wp1292 c4 L = pw2 c4 L (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wp1293 : Base 4 → WsL → ⟪ (CK01 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS04 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ
wp1293 c4 L = pw2 c4 L (CK01 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ CK01 ∷ []) tt tt Eq.refl

wp1294 : Base 4 → WsL → ⟪ (K1 ∷ CK01 ∷ S0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ K1 ∷ CK01 ∷ S0 ∷ []) ⟫ʷ
wp1294 c4 L = pw2 c4 L (K1 ∷ CK01 ∷ S0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ K1 ∷ CK01 ∷ S0 ∷ []) tt tt Eq.refl

wp1295 : Base 4 → WsL → ⟪ (CS04 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S0 ∷ X0 ∷ CS04 ∷ []) ⟫ʷ
wp1295 c4 L = pw1 c4 L (CS04 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ CS04 ∷ []) tt tt Eq.refl

wp1296 : Base 4 → WsL → ⟪ (CS04 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ []) ⟫ʷ
wp1296 c4 L = pw1 c4 L (CS04 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ []) tt tt Eq.refl

wp1297 : Base 4 → WsL → ⟪ (S4 ∷ CS04⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS04 ∷ []) ⟫ʷ
wp1297 c4 L = pw1 c4 L (S4 ∷ CS04⁻ ∷ X0 ∷ []) (X0 ∷ CS04 ∷ []) tt tt Eq.refl

wp1298 : Base 4 → WsL → ⟪ (CS04 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S4 ∷ CS04⁻ ∷ []) ⟫ʷ
wp1298 c4 L = pw1 c4 L (CS04 ∷ X0 ∷ []) (X0 ∷ S4 ∷ CS04⁻ ∷ []) tt tt Eq.refl

wp1299 : Base 4 → WsL → ⟪ (CS04 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ X0 ∷ CS04 ∷ []) ⟫ʷ
wp1299 c4 L = pw2 c4 L (CS04 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ CS04 ∷ []) tt tt Eq.refl

wp1300 : Base 4 → WsL → ⟪ (S0 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS04 ∷ X0 ∷ S0 ∷ []) ⟫ʷ
wp1300 c4 L = pw1 c4 L (S0 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ S0 ∷ []) tt tt Eq.refl

wp1301 : Base 4 → WsL → ⟪ (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ ι ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S0⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) ⟫ʷ
wp1301 c4 L = pw2 c4 L (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ ι ∷ S0⁻ ∷ []) (ι ∷ S0⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wp1302 : Base 4 → WsL → ⟪ (CCZ024 ∷ ι ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S0⁻ ∷ CCZ024 ∷ []) ⟫ʷ
wp1302 c4 L = pw1 c4 L (CCZ024 ∷ ι ∷ S0⁻ ∷ []) (ι ∷ S0⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1303 : Base 4 → WsL → ⟪ (CS01 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS04 ∷ X0 ∷ CS01 ∷ []) ⟫ʷ
wp1303 c4 L = pw2 c4 L (CS01 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ CS01 ∷ []) tt tt Eq.refl

wp1304 : Base 4 → WsL → ⟪ (S1 ∷ CS01⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ S1 ∷ CS01⁻ ∷ []) ⟫ʷ
wp1304 c4 L = pw2 c4 L (S1 ∷ CS01⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ S1 ∷ CS01⁻ ∷ []) tt tt Eq.refl

wp1305 : Base 4 → WsL → ⟪ (CCZ024 ∷ S1 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ CS01⁻ ∷ CCZ024 ∷ []) ⟫ʷ
wp1305 c4 L = pw3 c4 L (CCZ024 ∷ S1 ∷ CS01⁻ ∷ []) (S1 ∷ CS01⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1306 : Base 4 → WsL → ⟪ (S4 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ []) ⟫ʷ
wp1306 c4 L = pw1 c4 L (S4 ∷ []) (X0 ∷ CS04 ∷ X0 ∷ CS04 ∷ []) tt tt Eq.refl

wp1307 : Base 4 → WsL → ⟪ (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ
wp1307 c4 L = pw2 c4 L (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp1308 : Base 4 → WsL → ⟪ (CK41 ∷ CS14 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CCZ014 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ CS01 ∷ X0 ∷ []) ⟫ʷ
wp1308 c4 L = pw2 c4 L (CK41 ∷ CS14 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (X0 ∷ CCZ014 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ CS01 ∷ X0 ∷ []) tt tt Eq.refl

wp1309 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ024 ∷ CZ02 ∷ []) ⟫ʷ
wp1309 c4 L = pw3 c4 L (CCZ024 ∷ Toff402 ∷ []) (Toff402 ∷ CCZ024 ∷ CZ02 ∷ []) tt tt Eq.refl

wp1310 : Base 4 → WsL → ⟪ (CCZ024 ∷ CZ02 ∷ Toff402 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ []) ⟫ʷ
wp1310 c4 L = pw3 c4 L (CCZ024 ∷ CZ02 ∷ Toff402 ∷ CCZ024 ∷ []) (Toff402 ∷ []) tt tt Eq.refl

wp1311 : Base 4 → WsL → ⟪ (CX03 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CX03 ∷ []) ⟫ʷ
wp1311 c4 L = pw1 c4 L (CX03 ∷ Toff402 ∷ []) (Toff402 ∷ CX03 ∷ []) tt tt Eq.refl

wp1312 : Base 4 → WsL → ⟪ (CCZ134 ∷ CX03 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ CCZ134 ∷ []) ⟫ʷ
wp1312 c4 L = pw2 c4 L (CCZ134 ∷ CX03 ∷ CCZ014 ∷ []) (CX03 ∷ CCZ134 ∷ []) tt tt Eq.refl

wp1313 : Base 4 → WsL → ⟪ (CCZ014 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ014 ∷ CCZ012 ∷ []) ⟫ʷ
wp1313 c4 L = pw3 c4 L (CCZ014 ∷ Toff402 ∷ []) (Toff402 ∷ CCZ014 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp1314 : Base 4 → WsL → ⟪ (CX03 ∷ CCZ014 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ []) ⟫ʷ
wp1314 c4 L = pw2 c4 L (CX03 ∷ CCZ014 ∷ CCZ014 ∷ []) (CX03 ∷ []) tt tt Eq.refl

wp1315 : Base 4 → WsL → ⟪ (CX30 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CX30 ∷ Toff423 ∷ []) ⟫ʷ
wp1315 c4 L = pw1 c4 L (CX30 ∷ Toff402 ∷ []) (Toff402 ∷ CX30 ∷ Toff423 ∷ []) tt tt Eq.refl

wp1316 : Base 4 → WsL → ⟪ (CS12 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CS12 ∷ []) ⟫ʷ
wp1316 c4 L = pw3 c4 L (CS12 ∷ Toff402 ∷ []) (Toff402 ∷ CS12 ∷ []) tt tt Eq.refl

wp1317 : Base 4 → WsL → ⟪ (CX23 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CX23 ∷ []) ⟫ʷ
wp1317 c4 L = pw1 c4 L (CX23 ∷ Toff402 ∷ []) (Toff402 ∷ CX23 ∷ []) tt tt Eq.refl

wp1318 : Base 4 → WsL → ⟪ (Toff402 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Toff402 ∷ []) ⟫ʷ
wp1318 c4 L = pw1 c4 L (Toff402 ∷ Toff423 ∷ []) (Toff423 ∷ Toff402 ∷ []) tt tt Eq.refl

wp1319 : Base 4 → WsL → ⟪ (CX30 ∷ Toff423 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ []) ⟫ʷ
wp1319 c4 L = pw1 c4 L (CX30 ∷ Toff423 ∷ Toff423 ∷ []) (CX30 ∷ []) tt tt Eq.refl

wp1320 : Base 4 → WsL → ⟪ (K1 ∷ CK01 ∷ S0 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ K1 ∷ CK01 ∷ S0 ∷ []) ⟫ʷ
wp1320 c4 L = pw2 c4 L (K1 ∷ CK01 ∷ S0 ∷ Toff401 ∷ []) (Toff401 ∷ K1 ∷ CK01 ∷ S0 ∷ []) tt tt Eq.refl

wp1321 : Base 4 → WsL → ⟪ (K4 ∷ CCZ024 ∷ K4⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ []) ⟫ʷ
wp1321 c4 L = pw1 c4 L (K4 ∷ CCZ024 ∷ K4⁻ ∷ []) (Toff402 ∷ []) tt tt Eq.refl

wp1322 : Base 4 → WsL → ⟪ (CS02⁻ ∷ S4 ∷ Toff402 ∷ S4⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ024 ∷ []) ⟫ʷ
wp1322 c4 L = pw3 c4 L (CS02⁻ ∷ S4 ∷ Toff402 ∷ S4⁻ ∷ []) (Toff402 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1323 : Base 4 → WsL → ⟪ (Toff402 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp1323 c4 L = pw1 c4 L (Toff402 ∷ Toff402 ∷ []) [] tt tt Eq.refl

wp1324 : Base 4 → WsL → ⟪ (CCZ024 ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK02 ∷ X0 ∷ CCZ024 ∷ []) ⟫ʷ
wp1324 c4 L = pw3 c4 L (CCZ024 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp1325 : Base 4 → WsL → ⟪ (CCZ134 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CCZ134 ∷ CCZ013 ∷ []) ⟫ʷ
wp1325 c4 L = pw2 c4 L (CCZ134 ∷ Toff401 ∷ []) (Toff401 ∷ CCZ134 ∷ CCZ013 ∷ []) tt tt Eq.refl

wp1326 : Base 4 → WsL → ⟪ (CX21 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CX21 ∷ Toff402 ∷ []) ⟫ʷ
wp1326 c4 L = pw3 c4 L (CX21 ∷ Toff401 ∷ []) (Toff401 ∷ CX21 ∷ Toff402 ∷ []) tt tt Eq.refl

wp1327 : Base 4 → WsL → ⟪ (CCZ234 ∷ Toff402 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ234 ∷ []) ⟫ʷ
wp1327 c4 L = pw1 c4 L (CCZ234 ∷ Toff402 ∷ CCZ023 ∷ []) (Toff402 ∷ CCZ234 ∷ []) tt tt Eq.refl

wp1328 : Base 4 → WsL → ⟪ (CS03 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CS03 ∷ []) ⟫ʷ
wp1328 c4 L = pw2 c4 L (CS03 ∷ Toff401 ∷ []) (Toff401 ∷ CS03 ∷ []) tt tt Eq.refl

wp1329 : Base 4 → WsL → ⟪ (Toff401 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ Toff401 ∷ []) ⟫ʷ
wp1329 c4 L = pw3 c4 L (Toff401 ∷ Toff402 ∷ []) (Toff402 ∷ Toff401 ∷ []) tt tt Eq.refl

wp1330 : Base 4 → WsL → ⟪ (CX21 ∷ Toff402 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ []) ⟫ʷ
wp1330 c4 L = pw3 c4 L (CX21 ∷ Toff402 ∷ Toff402 ∷ []) (CX21 ∷ []) tt tt Eq.refl

wp1331 : Base 4 → WsL → ⟪ (CCZ014 ∷ Toff014 ∷ CZ03 ∷ Toff014 ∷ CCZ014 ∷ CZ03 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ []) ⟫ʷ
wp1331 c4 L = pw2 c4 L (CCZ014 ∷ Toff014 ∷ CZ03 ∷ Toff014 ∷ CCZ014 ∷ CZ03 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl

wp1332 : Base 4 → WsL → ⟪ (K2 ∷ CK02 ∷ S0 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ K2 ∷ CK02 ∷ S0 ∷ []) ⟫ʷ
wp1332 c4 L = pw3 c4 L (K2 ∷ CK02 ∷ S0 ∷ Toff402 ∷ []) (Toff402 ∷ K2 ∷ CK02 ∷ S0 ∷ []) tt tt Eq.refl

wp1333 : Base 4 → WsL → ⟪ (CX30 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CX30 ∷ []) ⟫ʷ
wp1333 c4 L = pw1 c4 L (CX30 ∷ Toff423 ∷ []) (Toff423 ∷ CX30 ∷ []) tt tt Eq.refl

wp1334 : Base 4 → WsL → ⟪ (CX03 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CX03 ∷ Toff402 ∷ []) ⟫ʷ
wp1334 c4 L = pw1 c4 L (CX03 ∷ Toff423 ∷ []) (Toff423 ∷ CX03 ∷ Toff402 ∷ []) tt tt Eq.refl

wp1335 : Base 4 → WsL → ⟪ (CCZ014 ∷ Toff402 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ014 ∷ []) ⟫ʷ
wp1335 c4 L = pw3 c4 L (CCZ014 ∷ Toff402 ∷ CCZ012 ∷ []) (Toff402 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1336 : Base 4 → WsL → ⟪ (CX20 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CX20 ∷ []) ⟫ʷ
wp1336 c4 L = pw1 c4 L (CX20 ∷ Toff423 ∷ []) (Toff423 ∷ CX20 ∷ []) tt tt Eq.refl

wp1337 : Base 4 → WsL → ⟪ (CX03 ∷ Toff402 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ []) ⟫ʷ
wp1337 c4 L = pw1 c4 L (CX03 ∷ Toff402 ∷ Toff402 ∷ []) (CX03 ∷ []) tt tt Eq.refl

wp1338 : Base 4 → WsL → ⟪ (CCZ014 ∷ CZ01 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CCZ014 ∷ []) ⟫ʷ
wp1338 c4 L = pw2 c4 L (CCZ014 ∷ CZ01 ∷ Toff401 ∷ []) (Toff401 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1339 : Base 4 → WsL → ⟪ (CCZ014 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CCZ014 ∷ Toff401 ∷ []) ⟫ʷ
wp1339 c4 L = pw2 c4 L (CCZ014 ∷ CZ01 ∷ []) (Toff401 ∷ CCZ014 ∷ Toff401 ∷ []) tt tt Eq.refl

wp1340 : Base 4 → WsL → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ CCZ014 ∷ CZ01 ∷ []) ⟫ʷ
wp1340 c4 L = pw2 c4 L (CCZ014 ∷ []) (CZ01 ∷ CCZ014 ∷ CZ01 ∷ []) tt tt Eq.refl

wp1341 : Base 4 → WsL → ⟪ (CCZ024 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CCZ024 ∷ CCZ012 ∷ []) ⟫ʷ
wp1341 c4 L = pw3 c4 L (CCZ024 ∷ Toff401 ∷ []) (Toff401 ∷ CCZ024 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp1342 : Base 4 → WsL → ⟪ (K3⁻ ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ K3⁻ ∷ []) ⟫ʷ
wp1342 c4 L = pw2 c4 L (K3⁻ ∷ Toff401 ∷ []) (Toff401 ∷ K3⁻ ∷ []) tt tt Eq.refl

wp1343 : Base 4 → WsL → ⟪ (CS02 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CS02 ∷ []) ⟫ʷ
wp1343 c4 L = pw3 c4 L (CS02 ∷ Toff401 ∷ []) (Toff401 ∷ CS02 ∷ []) tt tt Eq.refl

wp1344 : Base 4 → WsL → ⟪ (CS03⁻ ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CS03⁻ ∷ []) ⟫ʷ
wp1344 c4 L = pw2 c4 L (CS03⁻ ∷ Toff401 ∷ []) (Toff401 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp1345 : Base 4 → WsL → ⟪ (K3 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ K3 ∷ []) ⟫ʷ
wp1345 c4 L = pw2 c4 L (K3 ∷ Toff401 ∷ []) (Toff401 ∷ K3 ∷ []) tt tt Eq.refl

wp1346 : Base 4 → WsL → ⟪ (Toff302 ∷ CCZ024 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ []) ⟫ʷ
wp1346 c4 L = pw1 c4 L (Toff302 ∷ CCZ024 ∷ CCZ024 ∷ []) (Toff302 ∷ []) tt tt Eq.refl

wp1347 : Base 4 → WsL → ⟪ (CS03 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CS03 ∷ []) ⟫ʷ
wp1347 c4 L = pw1 c4 L (CS03 ∷ Toff423 ∷ []) (Toff423 ∷ CS03 ∷ []) tt tt Eq.refl

wp1348 : Base 4 → WsL → ⟪ (CS03⁻ ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CS03⁻ ∷ []) ⟫ʷ
wp1348 c4 L = pw1 c4 L (CS03⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp1349 : Base 4 → WsL → ⟪ (CCZ014 ∷ CX31 ∷ Toff103 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ Toff103 ∷ CCZ014 ∷ []) ⟫ʷ
wp1349 c4 L = pw2 c4 L (CCZ014 ∷ CX31 ∷ Toff103 ∷ []) (CX31 ∷ Toff103 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1350 : Base 4 → WsL → ⟪ (CCZ014 ∷ K1 ∷ CK01 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ CK01 ∷ S0 ∷ CCZ014 ∷ []) ⟫ʷ
wp1350 c4 L = pw2 c4 L (CCZ014 ∷ K1 ∷ CK01 ∷ S0 ∷ []) (K1 ∷ CK01 ∷ S0 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1351 : Base 4 → WsL → ⟪ (CCZ014 ∷ X0 ∷ CZ14 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CCZ014 ∷ []) ⟫ʷ
wp1351 c4 L = pw2 c4 L (CCZ014 ∷ X0 ∷ CZ14 ∷ []) (X0 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp1352 : Base 4 → WsL → ⟪ (CCZ014 ∷ CZ14 ∷ []) ⟫ʷ ≈ ⟪ (CZ14 ∷ CCZ014 ∷ []) ⟫ʷ
wp1352 c4 L = pw2 c4 L (CCZ014 ∷ CZ14 ∷ []) (CZ14 ∷ CCZ014 ∷ []) tt tt Eq.refl
