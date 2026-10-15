------------------------------------------------------------------------
-- Presentations of groups
--
-- The macro letters of the five-wire derivations and their spellings
--
-- A gate on wires w₁ < … < wₖ is its literal on the k adjacent wires from
-- w₁, whose upper wires are carried up by conjugation with adjacent
-- swaps, the highest first; a box (Clément's box, the S-box and the
-- K-box of the joint paper, and their inverses) is the concatenation of
-- the letters of its one-level unfolding, so that unfolding and folding
-- are definitional.  Every spelling is checked against the gate it
-- names by `scratchpad/five/mac5.py`; `emit5.py` writes this module.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Letters where

open import Word.Base using (_•_)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)

data Mac : Set where
  ι ι⁻ ι1 ι1⁻ ι2 ι2⁻ ι3 ι3⁻ ι4 ι4⁻ S0 S0⁻ : Mac
  K0 K0⁻ X0 Z0 S1 S1⁻ K1 K1⁻ X1 Z1 S2 S2⁻ : Mac
  K2 K2⁻ X2 Z2 S3 S3⁻ K3 K3⁻ X3 Z3 S4 S4⁻ : Mac
  K4 K4⁻ X4 Z4 CS01 CS01⁻ CZ01 Sw01 CX01 CK01 CK01⁻ CS02 : Mac
  CS02⁻ CZ02 Sw02 CX02 CK02 CK02⁻ CS03 CS03⁻ CZ03 Sw03 CX03 CK03 : Mac
  CK03⁻ CS04 CS04⁻ CZ04 Sw04 CX04 CK04 CK04⁻ CX10 CK10 CK10⁻ CS12 : Mac
  CS12⁻ CZ12 Sw12 CX12 CK12 CK12⁻ CS13 CS13⁻ CZ13 Sw13 CX13 CK13 : Mac
  CK13⁻ CS14 CS14⁻ CZ14 Sw14 CX14 CK14 CK14⁻ CX20 CK20 CK20⁻ CX21 : Mac
  CK21 CK21⁻ CS23 CS23⁻ CZ23 Sw23 CX23 CK23 CK23⁻ CS24 CS24⁻ CZ24 : Mac
  Sw24 CX24 CK24 CK24⁻ CX30 CK30 CK30⁻ CX31 CK31 CK31⁻ CX32 CK32 : Mac
  CK32⁻ CS34 CS34⁻ CZ34 Sw34 CX34 CK34 CK34⁻ CX40 CK40 CK40⁻ CX41 : Mac
  CK41 CK41⁻ CX42 CK42 CK42⁻ CX43 CK43 CK43⁻ CCZ012 Toff012 Toff102 Toff201 : Mac
  CCZ013 Toff013 Toff103 Toff301 CCZ014 Toff014 Toff104 Toff401 CCZ023 Toff023 Toff203 Toff302 : Mac
  CCZ024 Toff024 Toff204 Toff402 CCZ034 Toff034 Toff304 Toff403 CCZ123 Toff123 Toff213 Toff312 : Mac
  CCZ124 Toff124 Toff214 Toff412 CCZ134 Toff134 Toff314 Toff413 CCZ234 Toff234 Toff324 Toff423 : Mac
  Bx0-14 Bx1-034 Bx0-1234 Bx0-13 Bx1-023 Bx0-1423 Bx0-21 Bx2-03 Bx0-213 Bx2-031 Bx0-2431 Bx2-0413 : Mac
  Sb0-1-3-2 Sb⁻0-1-3-2 Sb0-1-42-3 Sb0-2-1-3 Sb⁻0-2-1-3 Sb0-2-43-1 Sb2-0-3-1 Sb⁻2-0-3-1 Sb2-0-41-3 : Mac

-- The boxes, each the concatenation of its one-level unfolding.

b-Bx0-14 : Circuit 5
b-Bx0-14 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (CZ ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx1-034 : Circuit 5
b-Bx1-034 = (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • b-Bx0-14 • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • b-Bx0-14
b-Bx0-1234 : Circuit 5
b-Bx0-1234 = CCZ • Toff • b-Bx1-034 • Toff • CCZ • b-Bx1-034
b-Bx0-13 : Circuit 5
b-Bx0-13 = (Swap ↑ ↑ • (CZ ↑) • Swap ↑ ↑)
b-Bx1-023 : Circuit 5
b-Bx1-023 = CCZ • (K ↑ • CCZ • K ↑ • iI) • b-Bx0-13 • (K ↑ • CCZ • K ↑ • iI) • CCZ • b-Bx0-13
b-Bx0-1423 : Circuit 5
b-Bx0-1423 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx1-023 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx1-023
b-Bx0-21 : Circuit 5
b-Bx0-21 = (CZ ↑)
b-Bx2-03 : Circuit 5
b-Bx2-03 = (Swap ↑ ↑ • (Swap ↑ • CZ • Swap ↑) • Swap ↑ ↑)
b-Bx0-213 : Circuit 5
b-Bx0-213 = CCZ • Toff • b-Bx2-03 • Toff • CCZ • b-Bx2-03
b-Bx2-031 : Circuit 5
b-Bx2-031 = (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) • b-Bx0-21 • (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • b-Bx0-21
b-Bx0-2431 : Circuit 5
b-Bx0-2431 = (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx2-031 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx2-031
b-Bx2-0413 : Circuit 5
b-Bx2-0413 = (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx0-213 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx0-213
b-Sb0-1-3-2 : Circuit 5
b-Sb0-1-3-2 = (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑)
b-Sb⁻0-1-3-2 : Circuit 5
b-Sb⁻0-1-3-2 = (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑)
b-Sb0-1-42-3 : Circuit 5
b-Sb0-1-42-3 = b-Bx0-1423 • ((K ↑ • CCZ • K ↑ • iI) ↑ ↑) • b-Sb0-1-3-2 • ((K ↑ • CCZ • K ↑ • iI) ↑ ↑) • b-Sb⁻0-1-3-2
b-Sb0-2-1-3 : Circuit 5
b-Sb0-2-1-3 = (CS ↑)
b-Sb⁻0-2-1-3 : Circuit 5
b-Sb⁻0-2-1-3 = ((CS • CS • CS) ↑)
b-Sb0-2-43-1 : Circuit 5
b-Sb0-2-43-1 = b-Bx0-2431 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Sb0-2-1-3 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Sb⁻0-2-1-3
b-Sb2-0-3-1 : Circuit 5
b-Sb2-0-3-1 = (Swap ↑ ↑ • (Swap ↑ • CS • Swap ↑) • Swap ↑ ↑)
b-Sb⁻2-0-3-1 : Circuit 5
b-Sb⁻2-0-3-1 = (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑)
b-Sb2-0-41-3 : Circuit 5
b-Sb2-0-41-3 = b-Bx2-0413 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Sb2-0-3-1 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Sb⁻2-0-3-1

⟪_⟫ : Mac → Circuit 5
⟪ ι ⟫ = iI
⟪ ι⁻ ⟫ = iI • iI • iI
⟪ ι1 ⟫ = iI ↑
⟪ ι1⁻ ⟫ = (iI • iI • iI) ↑
⟪ ι2 ⟫ = iI ↑ ↑
⟪ ι2⁻ ⟫ = (iI • iI • iI) ↑ ↑
⟪ ι3 ⟫ = iI ↑ ↑ ↑
⟪ ι3⁻ ⟫ = (iI • iI • iI) ↑ ↑ ↑
⟪ ι4 ⟫ = iI ↑ ↑ ↑ ↑
⟪ ι4⁻ ⟫ = (iI • iI • iI) ↑ ↑ ↑ ↑
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
⟪ S4 ⟫ = S ↑ ↑ ↑ ↑
⟪ S4⁻ ⟫ = (S • S • S) ↑ ↑ ↑ ↑
⟪ K4 ⟫ = K ↑ ↑ ↑ ↑
⟪ K4⁻ ⟫ = (K • iI) ↑ ↑ ↑ ↑
⟪ X4 ⟫ = X ↑ ↑ ↑ ↑
⟪ Z4 ⟫ = Z ↑ ↑ ↑ ↑
⟪ CS01 ⟫ = CS
⟪ CS01⁻ ⟫ = CS • CS • CS
⟪ CZ01 ⟫ = CZ
⟪ Sw01 ⟫ = Swap
⟪ CX01 ⟫ = CX₀₁
⟪ CK01 ⟫ = CK₀₁
⟪ CK01⁻ ⟫ = S • CK₀₁
⟪ CS02 ⟫ = Swap ↑ • CS • Swap ↑
⟪ CS02⁻ ⟫ = Swap ↑ • (CS • CS • CS) • Swap ↑
⟪ CZ02 ⟫ = Swap ↑ • CZ • Swap ↑
⟪ Sw02 ⟫ = Swap ↑ • Swap • Swap ↑
⟪ CX02 ⟫ = Swap ↑ • CX₀₁ • Swap ↑
⟪ CK02 ⟫ = Swap ↑ • CK₀₁ • Swap ↑
⟪ CK02⁻ ⟫ = Swap ↑ • (S • CK₀₁) • Swap ↑
⟪ CS03 ⟫ = Swap ↑ ↑ • (Swap ↑ • CS • Swap ↑) • Swap ↑ ↑
⟪ CS03⁻ ⟫ = Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑
⟪ CZ03 ⟫ = Swap ↑ ↑ • (Swap ↑ • CZ • Swap ↑) • Swap ↑ ↑
⟪ Sw03 ⟫ = Swap ↑ ↑ • (Swap ↑ • Swap • Swap ↑) • Swap ↑ ↑
⟪ CX03 ⟫ = Swap ↑ ↑ • (Swap ↑ • CX₀₁ • Swap ↑) • Swap ↑ ↑
⟪ CK03 ⟫ = Swap ↑ ↑ • (Swap ↑ • CK₀₁ • Swap ↑) • Swap ↑ ↑
⟪ CK03⁻ ⟫ = Swap ↑ ↑ • (Swap ↑ • (S • CK₀₁) • Swap ↑) • Swap ↑ ↑
⟪ CS04 ⟫ = Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • CS • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑
⟪ CS04⁻ ⟫ = Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑
⟪ CZ04 ⟫ = Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • CZ • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑
⟪ Sw04 ⟫ = Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • Swap • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑
⟪ CX04 ⟫ = Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • CX₀₁ • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑
⟪ CK04 ⟫ = Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • CK₀₁ • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑
⟪ CK04⁻ ⟫ = Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • (S • CK₀₁) • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑
⟪ CX10 ⟫ = CX₁₀
⟪ CK10 ⟫ = CK₁₀
⟪ CK10⁻ ⟫ = S ↑ • CK₁₀
⟪ CS12 ⟫ = CS ↑
⟪ CS12⁻ ⟫ = (CS • CS • CS) ↑
⟪ CZ12 ⟫ = CZ ↑
⟪ Sw12 ⟫ = Swap ↑
⟪ CX12 ⟫ = CX₀₁ ↑
⟪ CK12 ⟫ = CK₀₁ ↑
⟪ CK12⁻ ⟫ = (S • CK₀₁) ↑
⟪ CS13 ⟫ = Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑
⟪ CS13⁻ ⟫ = Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑
⟪ CZ13 ⟫ = Swap ↑ ↑ • (CZ ↑) • Swap ↑ ↑
⟪ Sw13 ⟫ = Swap ↑ ↑ • (Swap ↑) • Swap ↑ ↑
⟪ CX13 ⟫ = Swap ↑ ↑ • (CX₀₁ ↑) • Swap ↑ ↑
⟪ CK13 ⟫ = Swap ↑ ↑ • (CK₀₁ ↑) • Swap ↑ ↑
⟪ CK13⁻ ⟫ = Swap ↑ ↑ • ((S • CK₀₁) ↑) • Swap ↑ ↑
⟪ CS14 ⟫ = Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑
⟪ CS14⁻ ⟫ = Swap ↑ ↑ ↑ • (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑
⟪ CZ14 ⟫ = Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (CZ ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑
⟪ Sw14 ⟫ = Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑
⟪ CX14 ⟫ = Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (CX₀₁ ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑
⟪ CK14 ⟫ = Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (CK₀₁ ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑
⟪ CK14⁻ ⟫ = Swap ↑ ↑ ↑ • (Swap ↑ ↑ • ((S • CK₀₁) ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑
⟪ CX20 ⟫ = Swap ↑ • CX₁₀ • Swap ↑
⟪ CK20 ⟫ = Swap ↑ • CK₁₀ • Swap ↑
⟪ CK20⁻ ⟫ = Swap ↑ • (S ↑ • CK₁₀) • Swap ↑
⟪ CX21 ⟫ = CX₁₀ ↑
⟪ CK21 ⟫ = CK₁₀ ↑
⟪ CK21⁻ ⟫ = (S ↑ • CK₁₀) ↑
⟪ CS23 ⟫ = CS ↑ ↑
⟪ CS23⁻ ⟫ = (CS • CS • CS) ↑ ↑
⟪ CZ23 ⟫ = CZ ↑ ↑
⟪ Sw23 ⟫ = Swap ↑ ↑
⟪ CX23 ⟫ = CX₀₁ ↑ ↑
⟪ CK23 ⟫ = CK₀₁ ↑ ↑
⟪ CK23⁻ ⟫ = (S • CK₀₁) ↑ ↑
⟪ CS24 ⟫ = Swap ↑ ↑ ↑ • (CS ↑ ↑) • Swap ↑ ↑ ↑
⟪ CS24⁻ ⟫ = Swap ↑ ↑ ↑ • ((CS • CS • CS) ↑ ↑) • Swap ↑ ↑ ↑
⟪ CZ24 ⟫ = Swap ↑ ↑ ↑ • (CZ ↑ ↑) • Swap ↑ ↑ ↑
⟪ Sw24 ⟫ = Swap ↑ ↑ ↑ • (Swap ↑ ↑) • Swap ↑ ↑ ↑
⟪ CX24 ⟫ = Swap ↑ ↑ ↑ • (CX₀₁ ↑ ↑) • Swap ↑ ↑ ↑
⟪ CK24 ⟫ = Swap ↑ ↑ ↑ • (CK₀₁ ↑ ↑) • Swap ↑ ↑ ↑
⟪ CK24⁻ ⟫ = Swap ↑ ↑ ↑ • ((S • CK₀₁) ↑ ↑) • Swap ↑ ↑ ↑
⟪ CX30 ⟫ = Swap ↑ ↑ • (Swap ↑ • CX₁₀ • Swap ↑) • Swap ↑ ↑
⟪ CK30 ⟫ = Swap ↑ ↑ • (Swap ↑ • CK₁₀ • Swap ↑) • Swap ↑ ↑
⟪ CK30⁻ ⟫ = Swap ↑ ↑ • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap ↑ ↑
⟪ CX31 ⟫ = Swap ↑ ↑ • (CX₁₀ ↑) • Swap ↑ ↑
⟪ CK31 ⟫ = Swap ↑ ↑ • (CK₁₀ ↑) • Swap ↑ ↑
⟪ CK31⁻ ⟫ = Swap ↑ ↑ • ((S ↑ • CK₁₀) ↑) • Swap ↑ ↑
⟪ CX32 ⟫ = CX₁₀ ↑ ↑
⟪ CK32 ⟫ = CK₁₀ ↑ ↑
⟪ CK32⁻ ⟫ = (S ↑ • CK₁₀) ↑ ↑
⟪ CS34 ⟫ = CS ↑ ↑ ↑
⟪ CS34⁻ ⟫ = (CS • CS • CS) ↑ ↑ ↑
⟪ CZ34 ⟫ = CZ ↑ ↑ ↑
⟪ Sw34 ⟫ = Swap ↑ ↑ ↑
⟪ CX34 ⟫ = CX₀₁ ↑ ↑ ↑
⟪ CK34 ⟫ = CK₀₁ ↑ ↑ ↑
⟪ CK34⁻ ⟫ = (S • CK₀₁) ↑ ↑ ↑
⟪ CX40 ⟫ = Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • CX₁₀ • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑
⟪ CK40 ⟫ = Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • CK₁₀ • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑
⟪ CK40⁻ ⟫ = Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑
⟪ CX41 ⟫ = Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (CX₁₀ ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑
⟪ CK41 ⟫ = Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (CK₁₀ ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑
⟪ CK41⁻ ⟫ = Swap ↑ ↑ ↑ • (Swap ↑ ↑ • ((S ↑ • CK₁₀) ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑
⟪ CX42 ⟫ = Swap ↑ ↑ ↑ • (CX₁₀ ↑ ↑) • Swap ↑ ↑ ↑
⟪ CK42 ⟫ = Swap ↑ ↑ ↑ • (CK₁₀ ↑ ↑) • Swap ↑ ↑ ↑
⟪ CK42⁻ ⟫ = Swap ↑ ↑ ↑ • ((S ↑ • CK₁₀) ↑ ↑) • Swap ↑ ↑ ↑
⟪ CX43 ⟫ = CX₁₀ ↑ ↑ ↑
⟪ CK43 ⟫ = CK₁₀ ↑ ↑ ↑
⟪ CK43⁻ ⟫ = (S ↑ • CK₁₀) ↑ ↑ ↑
⟪ CCZ012 ⟫ = CCZ
⟪ Toff012 ⟫ = Toff
⟪ Toff102 ⟫ = K ↑ • CCZ • K ↑ • iI
⟪ Toff201 ⟫ = Toffᵗ
⟪ CCZ013 ⟫ = Swap ↑ ↑ • CCZ • Swap ↑ ↑
⟪ Toff013 ⟫ = Swap ↑ ↑ • Toff • Swap ↑ ↑
⟪ Toff103 ⟫ = Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑
⟪ Toff301 ⟫ = Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑
⟪ CCZ014 ⟫ = Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑
⟪ Toff014 ⟫ = Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑
⟪ Toff104 ⟫ = Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑
⟪ Toff401 ⟫ = Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑
⟪ CCZ023 ⟫ = Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑
⟪ Toff023 ⟫ = Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑
⟪ Toff203 ⟫ = Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑
⟪ Toff302 ⟫ = Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑
⟪ CCZ024 ⟫ = Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑
⟪ Toff024 ⟫ = Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑
⟪ Toff204 ⟫ = Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑
⟪ Toff402 ⟫ = Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑
⟪ CCZ034 ⟫ = Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑
⟪ Toff034 ⟫ = Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑
⟪ Toff304 ⟫ = Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑
⟪ Toff403 ⟫ = Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑
⟪ CCZ123 ⟫ = CCZ ↑
⟪ Toff123 ⟫ = Toff ↑
⟪ Toff213 ⟫ = (K ↑ • CCZ • K ↑ • iI) ↑
⟪ Toff312 ⟫ = Toffᵗ ↑
⟪ CCZ124 ⟫ = Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑
⟪ Toff124 ⟫ = Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑
⟪ Toff214 ⟫ = Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑
⟪ Toff412 ⟫ = Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑
⟪ CCZ134 ⟫ = Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑
⟪ Toff134 ⟫ = Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑
⟪ Toff314 ⟫ = Swap ↑ ↑ • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑
⟪ Toff413 ⟫ = Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑
⟪ CCZ234 ⟫ = CCZ ↑ ↑
⟪ Toff234 ⟫ = Toff ↑ ↑
⟪ Toff324 ⟫ = (K ↑ • CCZ • K ↑ • iI) ↑ ↑
⟪ Toff423 ⟫ = Toffᵗ ↑ ↑
⟪ Bx0-14 ⟫ = b-Bx0-14
⟪ Bx1-034 ⟫ = b-Bx1-034
⟪ Bx0-1234 ⟫ = b-Bx0-1234
⟪ Bx0-13 ⟫ = b-Bx0-13
⟪ Bx1-023 ⟫ = b-Bx1-023
⟪ Bx0-1423 ⟫ = b-Bx0-1423
⟪ Bx0-21 ⟫ = b-Bx0-21
⟪ Bx2-03 ⟫ = b-Bx2-03
⟪ Bx0-213 ⟫ = b-Bx0-213
⟪ Bx2-031 ⟫ = b-Bx2-031
⟪ Bx0-2431 ⟫ = b-Bx0-2431
⟪ Bx2-0413 ⟫ = b-Bx2-0413
⟪ Sb0-1-3-2 ⟫ = b-Sb0-1-3-2
⟪ Sb⁻0-1-3-2 ⟫ = b-Sb⁻0-1-3-2
⟪ Sb0-1-42-3 ⟫ = b-Sb0-1-42-3
⟪ Sb0-2-1-3 ⟫ = b-Sb0-2-1-3
⟪ Sb⁻0-2-1-3 ⟫ = b-Sb⁻0-2-1-3
⟪ Sb0-2-43-1 ⟫ = b-Sb0-2-43-1
⟪ Sb2-0-3-1 ⟫ = b-Sb2-0-3-1
⟪ Sb⁻2-0-3-1 ⟫ = b-Sb⁻2-0-3-1
⟪ Sb2-0-41-3 ⟫ = b-Sb2-0-41-3
