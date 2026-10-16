------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the five-wire derivations (placed)
--
-- Each distinct window of the derivations of Five.D, evaluated once
-- (Five.Win).  Written by `scratchpad/five/winlib5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Wins.WP04 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)

wp0442 : Complete 4 → ⟪ (K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ []) ⟫ʷ
wp0442 c4 = pw1 c4 (K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ []) (X4 ∷ CS02 ∷ X4 ∷ X4 ∷ Toff034 ∷ X4 ∷ X4 ∷ CS02⁻ ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ []) tt tt Eq.refl

wp0443 : Complete 4 → ⟪ (K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff034 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff034 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ []) ⟫ʷ
wp0443 c4 = pw1 c4 (K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff034 ∷ X4 ∷ []) (X4 ∷ Toff034 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ []) tt tt Eq.refl

wp0444 : Complete 4 → ⟪ (CX04 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ013 ∷ X4 ∷ CX04 ∷ []) ⟫ʷ
wp0444 c4 = pw2 c4 (CX04 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ X4 ∷ CX04 ∷ []) tt tt Eq.refl

wp0445 : Complete 4 → ⟪ (CS24⁻ ∷ X4 ∷ CX30 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CX30 ∷ X4 ∷ CS24⁻ ∷ []) ⟫ʷ
wp0445 c4 = pw1 c4 (CS24⁻ ∷ X4 ∷ CX30 ∷ X4 ∷ []) (X4 ∷ CX30 ∷ X4 ∷ CS24⁻ ∷ []) tt tt Eq.refl

wp0446 : Complete 4 → ⟪ (CS24⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS01⁻ ∷ X4 ∷ CS24⁻ ∷ []) ⟫ʷ
wp0446 c4 = pw3 c4 (CS24⁻ ∷ X4 ∷ CS01⁻ ∷ X4 ∷ []) (X4 ∷ CS01⁻ ∷ X4 ∷ CS24⁻ ∷ []) tt tt Eq.refl

wp0447 : Complete 4 → ⟪ (K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ []) ⟫ʷ
wp0447 c4 = pw3 c4 (K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ X4 ∷ Toff124 ∷ X4 ∷ []) (X4 ∷ Toff124 ∷ X4 ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS24⁻ ∷ K2⁻ ∷ K2 ∷ CX04 ∷ K2⁻ ∷ K2 ∷ CS02 ∷ K2⁻ ∷ []) tt tt Eq.refl

wp0448 : Complete 4 → ⟪ (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) ⟫ʷ
wp0448 c4 = pw1 c4 (K3 ∷ CS34 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) (X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CS34 ∷ K3⁻ ∷ []) tt tt Eq.refl

wp0449 : Complete 4 → ⟪ (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ []) ⟫ʷ
wp0449 c4 = pw2 c4 (K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) (X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX14 ∷ K3⁻ ∷ K3 ∷ CS13 ∷ K3⁻ ∷ []) tt tt Eq.refl

wp0450 : Complete 4 → ⟪ (CX14 ∷ X4 ∷ Toff012 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff012 ∷ X4 ∷ CX14 ∷ []) ⟫ʷ
wp0450 c4 = pw3 c4 (CX14 ∷ X4 ∷ Toff012 ∷ X4 ∷ []) (X4 ∷ Toff012 ∷ X4 ∷ CX14 ∷ []) tt tt Eq.refl

wp0451 : Complete 4 → ⟪ (CS34⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS02 ∷ X4 ∷ CS34⁻ ∷ []) ⟫ʷ
wp0451 c4 = pw1 c4 (CS34⁻ ∷ X4 ∷ CS02 ∷ X4 ∷ []) (X4 ∷ CS02 ∷ X4 ∷ CS34⁻ ∷ []) tt tt Eq.refl

wp0452 : Complete 4 → ⟪ (CS03 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS03 ∷ []) ⟫ʷ
wp0452 c4 = pw1 c4 (CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ []) tt tt Eq.refl

wp0453 : Complete 4 → ⟪ (CS03⁻ ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS03⁻ ∷ []) ⟫ʷ
wp0453 c4 = pw1 c4 (CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ []) tt tt Eq.refl

wp0454 : Complete 4 → ⟪ (CS12⁻ ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CS12⁻ ∷ []) ⟫ʷ
wp0454 c4 = pw3 c4 (CS12⁻ ∷ Toff024 ∷ []) (Toff024 ∷ CS12⁻ ∷ []) tt tt Eq.refl

wp0455 : Complete 4 → ⟪ (CS12 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CS12 ∷ []) ⟫ʷ
wp0455 c4 = pw3 c4 (CS12 ∷ Toff024 ∷ []) (Toff024 ∷ CS12 ∷ []) tt tt Eq.refl

wp0456 : Complete 4 → ⟪ (CCZ012 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CS01 ∷ Toff024 ∷ CCZ012 ∷ []) ⟫ʷ
wp0456 c4 = pw3 c4 (CCZ012 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ []) (Toff024 ∷ CS01 ∷ Toff024 ∷ CCZ012 ∷ []) tt tt Eq.refl

wp0457 : Complete 4 → ⟪ (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ []) ⟫ʷ
wp0457 c4 = pw1 c4 (K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ X4 ∷ CCZ034 ∷ X4 ∷ []) (X4 ∷ CCZ034 ∷ X4 ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS34⁻ ∷ K3⁻ ∷ K3 ∷ CX24 ∷ K3⁻ ∷ K3 ∷ CS23 ∷ K3⁻ ∷ []) tt tt Eq.refl

wp0458 : Complete 4 → ⟪ (CX24 ∷ X4 ∷ Toff012 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Toff012 ∷ X4 ∷ CX24 ∷ []) ⟫ʷ
wp0458 c4 = pw3 c4 (CX24 ∷ X4 ∷ Toff012 ∷ X4 ∷ []) (X4 ∷ Toff012 ∷ X4 ∷ CX24 ∷ []) tt tt Eq.refl

wp0459 : Complete 4 → ⟪ (CCZ024 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (CX43 ∷ CCZ024 ∷ []) ⟫ʷ
wp0459 c4 = pw1 c4 (CCZ024 ∷ CX43 ∷ []) (CX43 ∷ CCZ024 ∷ []) tt tt Eq.refl

wp0460 : Complete 4 → ⟪ (CX43 ∷ CS13⁻ ∷ CX43 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ []) ⟫ʷ
wp0460 c4 = pw2 c4 (CX43 ∷ CS13⁻ ∷ CX43 ∷ Toff013 ∷ []) (Toff013 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ []) tt tt Eq.refl

wp0461 : Complete 4 → ⟪ (S0 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0461 c4 = pw1 c4 (S0 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0462 : Complete 4 → ⟪ (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0462 c4 = pw1 c4 (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0463 : Complete 4 → ⟪ (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
wp0463 c4 = pw1 c4 (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl

wp0464 : Complete 4 → ⟪ (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0464 c4 = pw1 c4 (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0465 : Complete 4 → ⟪ (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0465 c4 = pw2 c4 (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0466 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wp0466 c4 = pw2 c4 (CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wp0467 : Complete 4 → ⟪ (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ
wp0467 c4 = pw2 c4 (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) tt tt Eq.refl

wp0468 : Complete 4 → ⟪ (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ
wp0468 c4 = pw3 c4 (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) tt tt Eq.refl

wp0469 : Complete 4 → ⟪ (CK41 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ
wp0469 c4 = pw3 c4 (CK41 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) tt tt Eq.refl

wp0470 : Complete 4 → ⟪ (CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0470 c4 = pw1 c4 (CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) [] tt tt Eq.refl

wp0471 : Complete 4 → ⟪ (CK40 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
wp0471 c4 = pw1 c4 (CK40 ∷ CK40 ∷ []) (S4 ∷ S4 ∷ S4 ∷ []) tt tt Eq.refl

wp0472 : Complete 4 → ⟪ (CS04 ∷ CK40 ∷ CS04 ∷ CK40 ∷ CS04 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
wp0472 c4 = pw1 c4 (CS04 ∷ CK40 ∷ CS04 ∷ CK40 ∷ CS04 ∷ CK40 ∷ []) (S4 ∷ S4 ∷ S4 ∷ []) tt tt Eq.refl

wp0473 : Complete 4 → ⟪ (CS04 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ CS04 ∷ []) ⟫ʷ
wp0473 c4 = pw1 c4 (CS04 ∷ S4 ∷ []) (S4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0474 : Complete 4 → ⟪ (CS04 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CS04 ∷ []) ⟫ʷ
wp0474 c4 = pw2 c4 (CS04 ∷ CS14 ∷ []) (CS14 ∷ CS04 ∷ []) tt tt Eq.refl

wp0475 : Complete 4 → ⟪ (CK41 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CK41 ∷ []) ⟫ʷ
wp0475 c4 = pw2 c4 (CK41 ∷ CS04 ∷ []) (CS04 ∷ CK41 ∷ []) tt tt Eq.refl

wp0476 : Complete 4 → ⟪ (CS04 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CS04 ∷ []) ⟫ʷ
wp0476 c4 = pw1 c4 (CS04 ∷ CS24 ∷ []) (CS24 ∷ CS04 ∷ []) tt tt Eq.refl

wp0477 : Complete 4 → ⟪ (CK42 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CK42 ∷ []) ⟫ʷ
wp0477 c4 = pw1 c4 (CK42 ∷ CS04 ∷ []) (CS04 ∷ CK42 ∷ []) tt tt Eq.refl

wp0478 : Complete 4 → ⟪ (CS04 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CS04 ∷ []) ⟫ʷ
wp0478 c4 = pw1 c4 (CS04 ∷ CS34 ∷ []) (CS34 ∷ CS04 ∷ []) tt tt Eq.refl

wp0479 : Complete 4 → ⟪ (CK43 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CK43 ∷ []) ⟫ʷ
wp0479 c4 = pw1 c4 (CK43 ∷ CS04 ∷ []) (CS04 ∷ CK43 ∷ []) tt tt Eq.refl

wp0480 : Complete 4 → ⟪ (CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ CK40 ∷ []) ⟫ʷ
wp0480 c4 = pw1 c4 (CK40 ∷ S4 ∷ []) (S4 ∷ CK40 ∷ []) tt tt Eq.refl

wp0481 : Complete 4 → ⟪ (CK40 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CK40 ∷ []) ⟫ʷ
wp0481 c4 = pw2 c4 (CK40 ∷ CS14 ∷ []) (CS14 ∷ CK40 ∷ []) tt tt Eq.refl

wp0482 : Complete 4 → ⟪ (CK40 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CK40 ∷ []) ⟫ʷ
wp0482 c4 = pw2 c4 (CK40 ∷ CK41 ∷ []) (CK41 ∷ CK40 ∷ []) tt tt Eq.refl

wp0483 : Complete 4 → ⟪ (CK40 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CK40 ∷ []) ⟫ʷ
wp0483 c4 = pw1 c4 (CK40 ∷ CS24 ∷ []) (CS24 ∷ CK40 ∷ []) tt tt Eq.refl

wp0484 : Complete 4 → ⟪ (CK40 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CK40 ∷ []) ⟫ʷ
wp0484 c4 = pw1 c4 (CK40 ∷ CK42 ∷ []) (CK42 ∷ CK40 ∷ []) tt tt Eq.refl

wp0485 : Complete 4 → ⟪ (CK40 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CK40 ∷ []) ⟫ʷ
wp0485 c4 = pw1 c4 (CK40 ∷ CS34 ∷ []) (CS34 ∷ CK40 ∷ []) tt tt Eq.refl

wp0486 : Complete 4 → ⟪ (CK40 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CK40 ∷ []) ⟫ʷ
wp0486 c4 = pw1 c4 (CK40 ∷ CK43 ∷ []) (CK43 ∷ CK40 ∷ []) tt tt Eq.refl

wp0487 : Complete 4 → ⟪ (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ
wp0487 c4 = pw1 c4 (CK40 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CK40 ∷ []) tt tt Eq.refl

wp0488 : Complete 4 → ⟪ (CK40 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ
wp0488 c4 = pw1 c4 (CK40 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CK40 ∷ []) tt tt Eq.refl

wp0489 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wp0489 c4 = pw1 c4 (CS24 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wp0490 : Complete 4 → ⟪ (CK42 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ
wp0490 c4 = pw1 c4 (CK42 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CK42 ∷ []) tt tt Eq.refl

wp0491 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wp0491 c4 = pw1 c4 (CS34 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wp0492 : Complete 4 → ⟪ (CK43 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ
wp0492 c4 = pw1 c4 (CK43 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CK43 ∷ []) tt tt Eq.refl

wp0493 : Complete 4 → ⟪ (S4 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ S4 ∷ []) ⟫ʷ
wp0493 c4 = pw1 c4 (S4 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ S4 ∷ []) tt tt Eq.refl

wp0494 : Complete 4 → ⟪ (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0494 c4 = pw1 c4 (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0495 : Complete 4 → ⟪ (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ
wp0495 c4 = pw1 c4 (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) tt tt Eq.refl

wp0496 : Complete 4 → ⟪ (CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ
wp0496 c4 = pw2 c4 (CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS14 ∷ []) tt tt Eq.refl

wp0497 : Complete 4 → ⟪ (CK41 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ
wp0497 c4 = pw2 c4 (CK41 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CK41 ∷ []) tt tt Eq.refl

wp0498 : Complete 4 → ⟪ (CS24 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ
wp0498 c4 = pw1 c4 (CS24 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS24 ∷ []) tt tt Eq.refl

wp0499 : Complete 4 → ⟪ (CK42 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ
wp0499 c4 = pw1 c4 (CK42 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CK42 ∷ []) tt tt Eq.refl

wp0500 : Complete 4 → ⟪ (CS34 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ
wp0500 c4 = pw1 c4 (CS34 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CS34 ∷ []) tt tt Eq.refl

wp0501 : Complete 4 → ⟪ (CK43 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ
wp0501 c4 = pw1 c4 (CK43 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CK43 ∷ []) tt tt Eq.refl

wp0502 : Complete 4 → ⟪ (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0502 c4 = pw2 c4 (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0503 : Complete 4 → ⟪ (CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ
wp0503 c4 = pw2 c4 (CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) tt tt Eq.refl

wp0504 : Complete 4 → ⟪ (CK40 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ
wp0504 c4 = pw2 c4 (CK40 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK40 ∷ []) tt tt Eq.refl

wp0505 : Complete 4 → ⟪ (CS04 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0505 c4 = pw1 c4 (CS04 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0506 : Complete 4 → ⟪ (CK40 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ
wp0506 c4 = pw1 c4 (CK40 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CK40 ∷ []) tt tt Eq.refl

wp0507 : Complete 4 → ⟪ (CS04 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0507 c4 = pw1 c4 (CS04 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0508 : Complete 4 → ⟪ (CK40 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK42 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ
wp0508 c4 = pw1 c4 (CK40 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CK40 ∷ []) tt tt Eq.refl

wp0509 : Complete 4 → ⟪ (CS04 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0509 c4 = pw1 c4 (CS04 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0510 : Complete 4 → ⟪ (CK40 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS34 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ
wp0510 c4 = pw1 c4 (CK40 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (X4 ∷ CS34 ∷ X4 ∷ CK40 ∷ []) tt tt Eq.refl

wp0511 : Complete 4 → ⟪ (CS04 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ
wp0511 c4 = pw1 c4 (CS04 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CS04 ∷ []) tt tt Eq.refl

wp0512 : Complete 4 → ⟪ (CK40 ∷ X4 ∷ CK43 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK43 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ
wp0512 c4 = pw1 c4 (CK40 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (X4 ∷ CK43 ∷ X4 ∷ CK40 ∷ []) tt tt Eq.refl

wp0513 : Complete 4 → ⟪ (K0 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ
wp0513 c4 = pw1 c4 (K0 ∷ []) (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) tt tt Eq.refl

wp0514 : Complete 4 → ⟪ (CX14 ∷ []) ⟫ʷ ≈ ⟪ (K4 ∷ CS14 ∷ CS14 ∷ K4 ∷ ι1 ∷ []) ⟫ʷ
wp0514 c4 = pw0 c4 (CX14 ∷ []) (K4 ∷ CS14 ∷ CS14 ∷ K4 ∷ ι1 ∷ []) tt tt Eq.refl

wp0515 : Complete 4 → ⟪ (CS01⁻ ∷ CCZ014 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ X4 ∷ CS04 ∷ X4 ∷ CX14 ∷ []) ⟫ʷ
wp0515 c4 = pw2 c4 (CS01⁻ ∷ CCZ014 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (CX14 ∷ X4 ∷ CS04 ∷ X4 ∷ CX14 ∷ []) tt tt Eq.refl

wp0516 : Complete 4 → ⟪ (CX14 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS01 ∷ CCZ014 ∷ []) ⟫ʷ
wp0516 c4 = pw2 c4 (CX14 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CX14 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS01 ∷ CCZ014 ∷ []) tt tt Eq.refl

wp0517 : Complete 4 → ⟪ (CS01 ∷ CCZ014 ∷ CS01⁻ ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
wp0517 c4 = pw2 c4 (CS01 ∷ CCZ014 ∷ CS01⁻ ∷ CCZ014 ∷ []) [] tt tt Eq.refl
