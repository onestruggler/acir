------------------------------------------------------------------------
-- Presentations of groups
--
-- The macro letters of the four-wire derivations and their spellings
--
-- A gate on adjacent wires is the lifted basic word; a gate on wires
-- further apart is the gate one wire closer conjugated by the adjacent
-- swap at its top (stacked swaps); a three-wire gate on wires 0 1 2 or
-- 1 2 3 is literal, the other two are conjugates by one swap.  Every
-- spelling is checked against the gate it names by
-- `scratchpad/four/mac.py`; `emit.py` writes this module.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.Letters where

open import Word.Base using (_•_)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)

data Mac : Set where
  ι ι1 ι2 ι3 ι⁻ ι1⁻ ι2⁻ ι3⁻ S0 S0⁻ K0 K0⁻ X0 Z0 S1 S1⁻ K1 K1⁻ X1 Z1 S2 S2⁻ K2 K2⁻ X2 Z2 S3 S3⁻ K3 K3⁻ X3 Z3 CS01 CS01⁻ CZ01 CX01 CK01 CK01⁻ Sw01 CS02 CS02⁻ CZ02 CX02 CK02 CK02⁻ CS03 CS03⁻ CZ03 CX03 CK03 CK03⁻ CX10 CK10 CK10⁻ CS12 CS12⁻ CZ12 CX12 CK12 CK12⁻ Sw12 CS13 CS13⁻ CZ13 CX13 CK13 CK13⁻ CX20 CK20 CK20⁻ CX21 CK21 CK21⁻ CS23 CS23⁻ CZ23 CX23 CK23 CK23⁻ Sw23 CX30 CK30 CK30⁻ CX31 CK31 CK31⁻ CX32 CK32 CK32⁻ CCZ012 CCZ013 CCZ023 CCZ123 Toff012 Toff013 Toff023 Toff102 Toff103 Toff123 Toff201 Toff203 Toff213 Toff301 Toff302 Toff312 : Mac

⟪_⟫ : Mac → Circuit 4
⟪ ι ⟫ = iI
⟪ ι1 ⟫ = iI ↑
⟪ ι2 ⟫ = iI ↑ ↑
⟪ ι3 ⟫ = iI ↑ ↑ ↑
⟪ ι⁻ ⟫ = iI • iI • iI
⟪ ι1⁻ ⟫ = (iI • iI • iI) ↑
⟪ ι2⁻ ⟫ = (iI • iI • iI) ↑ ↑
⟪ ι3⁻ ⟫ = (iI • iI • iI) ↑ ↑ ↑
⟪ S0 ⟫ = S
⟪ S0⁻ ⟫ = S • S • S
⟪ K0 ⟫ = K
⟪ K0⁻ ⟫ = K • iI
⟪ X0 ⟫ = X
⟪ Z0 ⟫ = Z
⟪ S1 ⟫ = S ↑
⟪ S1⁻ ⟫ = (S • S • S) ↑
⟪ K1 ⟫ = K ↑
⟪ K1⁻ ⟫ = (K • iI) ↑
⟪ X1 ⟫ = X ↑
⟪ Z1 ⟫ = Z ↑
⟪ S2 ⟫ = S ↑ ↑
⟪ S2⁻ ⟫ = (S • S • S) ↑ ↑
⟪ K2 ⟫ = K ↑ ↑
⟪ K2⁻ ⟫ = (K • iI) ↑ ↑
⟪ X2 ⟫ = X ↑ ↑
⟪ Z2 ⟫ = Z ↑ ↑
⟪ S3 ⟫ = S ↑ ↑ ↑
⟪ S3⁻ ⟫ = (S • S • S) ↑ ↑ ↑
⟪ K3 ⟫ = K ↑ ↑ ↑
⟪ K3⁻ ⟫ = (K • iI) ↑ ↑ ↑
⟪ X3 ⟫ = X ↑ ↑ ↑
⟪ Z3 ⟫ = Z ↑ ↑ ↑
⟪ CS01 ⟫ = CS
⟪ CS01⁻ ⟫ = CS • CS • CS
⟪ CZ01 ⟫ = CZ
⟪ CX01 ⟫ = CX₀₁
⟪ CK01 ⟫ = CK₀₁
⟪ CK01⁻ ⟫ = S • CK₀₁
⟪ Sw01 ⟫ = Swap
⟪ CS02 ⟫ = Swap ↑ • CS • Swap ↑
⟪ CS02⁻ ⟫ = Swap ↑ • (CS • CS • CS) • Swap ↑
⟪ CZ02 ⟫ = Swap ↑ • CZ • Swap ↑
⟪ CX02 ⟫ = Swap ↑ • CX₀₁ • Swap ↑
⟪ CK02 ⟫ = Swap ↑ • CK₀₁ • Swap ↑
⟪ CK02⁻ ⟫ = Swap ↑ • (S • CK₀₁) • Swap ↑
⟪ CS03 ⟫ = Swap ↑ ↑ • (Swap ↑ • CS • Swap ↑) • Swap ↑ ↑
⟪ CS03⁻ ⟫ = Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑
⟪ CZ03 ⟫ = Swap ↑ ↑ • (Swap ↑ • CZ • Swap ↑) • Swap ↑ ↑
⟪ CX03 ⟫ = Swap ↑ ↑ • (Swap ↑ • CX₀₁ • Swap ↑) • Swap ↑ ↑
⟪ CK03 ⟫ = Swap ↑ ↑ • (Swap ↑ • CK₀₁ • Swap ↑) • Swap ↑ ↑
⟪ CK03⁻ ⟫ = Swap ↑ ↑ • (Swap ↑ • (S • CK₀₁) • Swap ↑) • Swap ↑ ↑
⟪ CX10 ⟫ = CX₁₀
⟪ CK10 ⟫ = CK₁₀
⟪ CK10⁻ ⟫ = S ↑ • CK₁₀
⟪ CS12 ⟫ = CS ↑
⟪ CS12⁻ ⟫ = (CS • CS • CS) ↑
⟪ CZ12 ⟫ = CZ ↑
⟪ CX12 ⟫ = CX₀₁ ↑
⟪ CK12 ⟫ = CK₀₁ ↑
⟪ CK12⁻ ⟫ = (S • CK₀₁) ↑
⟪ Sw12 ⟫ = Swap ↑
⟪ CS13 ⟫ = Swap ↑ ↑ • CS ↑ • Swap ↑ ↑
⟪ CS13⁻ ⟫ = Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑
⟪ CZ13 ⟫ = Swap ↑ ↑ • CZ ↑ • Swap ↑ ↑
⟪ CX13 ⟫ = Swap ↑ ↑ • CX₀₁ ↑ • Swap ↑ ↑
⟪ CK13 ⟫ = Swap ↑ ↑ • CK₀₁ ↑ • Swap ↑ ↑
⟪ CK13⁻ ⟫ = Swap ↑ ↑ • ((S • CK₀₁) ↑) • Swap ↑ ↑
⟪ CX20 ⟫ = Swap ↑ • CX₁₀ • Swap ↑
⟪ CK20 ⟫ = Swap ↑ • CK₁₀ • Swap ↑
⟪ CK20⁻ ⟫ = Swap ↑ • (S ↑ • CK₁₀) • Swap ↑
⟪ CX21 ⟫ = CX₁₀ ↑
⟪ CK21 ⟫ = CK₁₀ ↑
⟪ CK21⁻ ⟫ = (S ↑ • CK₁₀) ↑
⟪ CS23 ⟫ = CS ↑ ↑
⟪ CS23⁻ ⟫ = (CS • CS • CS) ↑ ↑
⟪ CZ23 ⟫ = CZ ↑ ↑
⟪ CX23 ⟫ = CX₀₁ ↑ ↑
⟪ CK23 ⟫ = CK₀₁ ↑ ↑
⟪ CK23⁻ ⟫ = (S • CK₀₁) ↑ ↑
⟪ Sw23 ⟫ = Swap ↑ ↑
⟪ CX30 ⟫ = Swap ↑ ↑ • (Swap ↑ • CX₁₀ • Swap ↑) • Swap ↑ ↑
⟪ CK30 ⟫ = Swap ↑ ↑ • (Swap ↑ • CK₁₀ • Swap ↑) • Swap ↑ ↑
⟪ CK30⁻ ⟫ = Swap ↑ ↑ • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap ↑ ↑
⟪ CX31 ⟫ = Swap ↑ ↑ • CX₁₀ ↑ • Swap ↑ ↑
⟪ CK31 ⟫ = Swap ↑ ↑ • CK₁₀ ↑ • Swap ↑ ↑
⟪ CK31⁻ ⟫ = Swap ↑ ↑ • ((S ↑ • CK₁₀) ↑) • Swap ↑ ↑
⟪ CX32 ⟫ = CX₁₀ ↑ ↑
⟪ CK32 ⟫ = CK₁₀ ↑ ↑
⟪ CK32⁻ ⟫ = (S ↑ • CK₁₀) ↑ ↑
⟪ CCZ012 ⟫ = CCZ
⟪ CCZ013 ⟫ = Swap ↑ ↑ • CCZ • Swap ↑ ↑
⟪ CCZ023 ⟫ = Swap • CCZ ↑ • Swap
⟪ CCZ123 ⟫ = CCZ ↑
⟪ Toff012 ⟫ = Toff
⟪ Toff013 ⟫ = Swap ↑ ↑ • Toff • Swap ↑ ↑
⟪ Toff023 ⟫ = Swap • Toff ↑ • Swap
⟪ Toff102 ⟫ = K ↑ • CCZ • K ↑ • iI
⟪ Toff103 ⟫ = Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑
⟪ Toff123 ⟫ = Toff ↑
⟪ Toff201 ⟫ = Toffᵗ
⟪ Toff203 ⟫ = Swap • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap
⟪ Toff213 ⟫ = (K ↑ • CCZ • K ↑ • iI) ↑
⟪ Toff301 ⟫ = Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑
⟪ Toff302 ⟫ = Swap • Toffᵗ ↑ • Swap
⟪ Toff312 ⟫ = Toffᵗ ↑
