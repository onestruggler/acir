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
  Bx0-12 Bx0-14 Bx1-034 Bx0-1234 Bx0-13 Bx1-043 Bx0-1243 Bx1-024 Bx0-1324 Bx1-04 Bx0-134 Bx1-042 : Mac
  Bx0-1342 Bx1-023 Bx0-1423 Bx1-032 Bx0-1432 Bx0-21 Bx2-03 Bx0-213 Bx0-24 Bx2-034 Bx0-2134 Bx0-23 : Mac
  Bx2-043 Bx0-2143 Bx2-014 Bx0-2314 Bx2-04 Bx0-234 Bx2-041 Bx0-2341 Bx2-01 Bx0-241 Bx2-013 Bx0-2413 : Mac
  Bx0-243 Bx2-031 Bx0-2431 Bx0-31 Bx3-02 Bx0-312 Bx0-34 Bx3-024 Bx0-3124 Bx0-32 Bx3-042 Bx0-3142 : Mac
  Bx3-014 Bx0-3214 Bx3-04 Bx0-324 Bx3-041 Bx0-3241 Bx3-012 Bx0-3412 Bx3-021 Bx0-3421 Bx0-41 Bx0-43 : Mac
  Bx4-023 Bx0-4123 Bx0-42 Bx4-032 Bx0-4132 Bx4-013 Bx0-4213 Bx4-03 Bx0-423 Bx4-031 Bx0-4231 Bx4-012 : Mac
  Bx0-4312 Bx4-021 Bx0-4321 Bx1-0234 Bx2-14 Bx1-204 Bx1-234 Bx2-10 Bx1-240 Bx3-14 Bx1-304 Bx1-324 : Mac
  Bx3-10 Bx1-340 Bx4-13 Bx1-403 Bx1-423 Bx2-0134 Bx2-0143 Bx2-0341 Bx2-0413 Bx2-1034 Bx2-1304 Bx2-1340 : Mac
  Bx2-30 Bx2-31 Bx3-241 Bx2-3041 Bx3-20 Bx2-310 Bx3-240 Bx2-3140 Bx2-340 Bx3-210 Bx2-3410 Bx2-43 : Mac
  Bx4-213 Bx2-4013 Bx4-203 Bx2-4103 Bx3-0124 Bx3-0412 Bx3-1024 Bx3-1204 Bx3-1240 Bx3-2140 Bx3-2410 Bx3-42 : Mac
  Bx4-312 Bx3-4012 Bx4-302 Bx3-4102 Bx4-0123 Bx4-1023 Bx4-1203 Bx⁻2-03 Bx⁻0-213 Bx⁻2-0413 Sb0-1-3-2 Sb⁻0-1-3-2 : Mac
  Sb0-1-42-3 Sb0-2-1-3 Sb⁻0-2-1-3 Sb0-2-43-1 Sb2-0-3-1 Sb⁻2-0-3-1 Sb2-0-41-3 Sb3-0-4-2 Sb⁻3-0-4-2 Sb3-0-12-4 Sb3-0-2-1 Sb⁻3-0-2-1 : Mac
  Sb3-0-41-2 Sb4-0-3-2 Sb⁻4-0-3-2 Sb4-0-12-3 Sb⁻2-0-41-3 : Mac

-- The boxes, each the concatenation of its one-level unfolding.

b-Bx0-12 : Circuit 5
b-Bx0-12 = (CZ ↑)
b-Bx0-14 : Circuit 5
b-Bx0-14 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (CZ ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx1-034 : Circuit 5
b-Bx1-034 = (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • b-Bx0-14 • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • b-Bx0-14
b-Bx0-1234 : Circuit 5
b-Bx0-1234 = CCZ • Toff • b-Bx1-034 • Toff • CCZ • b-Bx1-034
b-Bx0-13 : Circuit 5
b-Bx0-13 = (Swap ↑ ↑ • (CZ ↑) • Swap ↑ ↑)
b-Bx1-043 : Circuit 5
b-Bx1-043 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx0-13 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx0-13
b-Bx0-1243 : Circuit 5
b-Bx0-1243 = CCZ • Toff • b-Bx1-043 • Toff • CCZ • b-Bx1-043
b-Bx1-024 : Circuit 5
b-Bx1-024 = CCZ • (K ↑ • CCZ • K ↑ • iI) • b-Bx0-14 • (K ↑ • CCZ • K ↑ • iI) • CCZ • b-Bx0-14
b-Bx0-1324 : Circuit 5
b-Bx0-1324 = (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • b-Bx1-024 • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • b-Bx1-024
b-Bx1-04 : Circuit 5
b-Bx1-04 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • CZ • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx0-134 : Circuit 5
b-Bx0-134 = (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • b-Bx1-04 • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • b-Bx1-04
b-Bx1-042 : Circuit 5
b-Bx1-042 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx0-12 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx0-12
b-Bx0-1342 : Circuit 5
b-Bx0-1342 = (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • b-Bx1-042 • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • b-Bx1-042
b-Bx1-023 : Circuit 5
b-Bx1-023 = CCZ • (K ↑ • CCZ • K ↑ • iI) • b-Bx0-13 • (K ↑ • CCZ • K ↑ • iI) • CCZ • b-Bx0-13
b-Bx0-1423 : Circuit 5
b-Bx0-1423 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx1-023 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx1-023
b-Bx1-032 : Circuit 5
b-Bx1-032 = (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • b-Bx0-12 • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • b-Bx0-12
b-Bx0-1432 : Circuit 5
b-Bx0-1432 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx1-032 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx1-032
b-Bx0-21 : Circuit 5
b-Bx0-21 = (CZ ↑)
b-Bx2-03 : Circuit 5
b-Bx2-03 = (Swap ↑ ↑ • (Swap ↑ • CZ • Swap ↑) • Swap ↑ ↑)
b-Bx0-213 : Circuit 5
b-Bx0-213 = CCZ • Toff • b-Bx2-03 • Toff • CCZ • b-Bx2-03
b-Bx0-24 : Circuit 5
b-Bx0-24 = (Swap ↑ ↑ ↑ • (CZ ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx2-034 : Circuit 5
b-Bx2-034 = (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) • b-Bx0-24 • (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • b-Bx0-24
b-Bx0-2134 : Circuit 5
b-Bx0-2134 = CCZ • Toff • b-Bx2-034 • Toff • CCZ • b-Bx2-034
b-Bx0-23 : Circuit 5
b-Bx0-23 = (CZ ↑ ↑)
b-Bx2-043 : Circuit 5
b-Bx2-043 = (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx0-23 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx0-23
b-Bx0-2143 : Circuit 5
b-Bx0-2143 = CCZ • Toff • b-Bx2-043 • Toff • CCZ • b-Bx2-043
b-Bx2-014 : Circuit 5
b-Bx2-014 = CCZ • Toffᵗ • b-Bx0-24 • Toffᵗ • CCZ • b-Bx0-24
b-Bx0-2314 : Circuit 5
b-Bx0-2314 = (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • b-Bx2-014 • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • b-Bx2-014
b-Bx2-04 : Circuit 5
b-Bx2-04 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • CZ • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx0-234 : Circuit 5
b-Bx0-234 = (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • b-Bx2-04 • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • b-Bx2-04
b-Bx2-041 : Circuit 5
b-Bx2-041 = (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx0-21 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx0-21
b-Bx0-2341 : Circuit 5
b-Bx0-2341 = (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • b-Bx2-041 • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • b-Bx2-041
b-Bx2-01 : Circuit 5
b-Bx2-01 = CZ
b-Bx0-241 : Circuit 5
b-Bx0-241 = (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx2-01 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx2-01
b-Bx2-013 : Circuit 5
b-Bx2-013 = CCZ • Toffᵗ • b-Bx0-23 • Toffᵗ • CCZ • b-Bx0-23
b-Bx0-2413 : Circuit 5
b-Bx0-2413 = (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx2-013 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx2-013
b-Bx0-243 : Circuit 5
b-Bx0-243 = (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx2-03 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx2-03
b-Bx2-031 : Circuit 5
b-Bx2-031 = (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) • b-Bx0-21 • (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • b-Bx0-21
b-Bx0-2431 : Circuit 5
b-Bx0-2431 = (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx2-031 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx2-031
b-Bx0-31 : Circuit 5
b-Bx0-31 = (Swap ↑ ↑ • (CZ ↑) • Swap ↑ ↑)
b-Bx3-02 : Circuit 5
b-Bx3-02 = (Swap ↑ • CZ • Swap ↑)
b-Bx0-312 : Circuit 5
b-Bx0-312 = (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • b-Bx3-02 • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • b-Bx3-02
b-Bx0-34 : Circuit 5
b-Bx0-34 = (CZ ↑ ↑ ↑)
b-Bx3-024 : Circuit 5
b-Bx3-024 = (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) • b-Bx0-34 • (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • b-Bx0-34
b-Bx0-3124 : Circuit 5
b-Bx0-3124 = (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • b-Bx3-024 • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • b-Bx3-024
b-Bx0-32 : Circuit 5
b-Bx0-32 = (CZ ↑ ↑)
b-Bx3-042 : Circuit 5
b-Bx3-042 = (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx0-32 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx0-32
b-Bx0-3142 : Circuit 5
b-Bx0-3142 = (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • b-Bx3-042 • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • b-Bx3-042
b-Bx3-014 : Circuit 5
b-Bx3-014 = (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • b-Bx0-34 • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • b-Bx0-34
b-Bx0-3214 : Circuit 5
b-Bx0-3214 = (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • b-Bx3-014 • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • b-Bx3-014
b-Bx3-04 : Circuit 5
b-Bx3-04 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • CZ • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx0-324 : Circuit 5
b-Bx0-324 = (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • b-Bx3-04 • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • b-Bx3-04
b-Bx3-041 : Circuit 5
b-Bx3-041 = (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx0-31 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx0-31
b-Bx0-3241 : Circuit 5
b-Bx0-3241 = (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • b-Bx3-041 • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • b-Bx3-041
b-Bx3-012 : Circuit 5
b-Bx3-012 = (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • b-Bx0-32 • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • b-Bx0-32
b-Bx0-3412 : Circuit 5
b-Bx0-3412 = (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx3-012 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx3-012
b-Bx3-021 : Circuit 5
b-Bx3-021 = (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) • b-Bx0-31 • (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • b-Bx0-31
b-Bx0-3421 : Circuit 5
b-Bx0-3421 = (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx3-021 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx3-021
b-Bx0-41 : Circuit 5
b-Bx0-41 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (CZ ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx0-43 : Circuit 5
b-Bx0-43 = (CZ ↑ ↑ ↑)
b-Bx4-023 : Circuit 5
b-Bx4-023 = (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx0-43 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx0-43
b-Bx0-4123 : Circuit 5
b-Bx0-4123 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx4-023 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx4-023
b-Bx0-42 : Circuit 5
b-Bx0-42 = (Swap ↑ ↑ ↑ • (CZ ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx4-032 : Circuit 5
b-Bx4-032 = (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx0-42 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx0-42
b-Bx0-4132 : Circuit 5
b-Bx0-4132 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx4-032 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx4-032
b-Bx4-013 : Circuit 5
b-Bx4-013 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx0-43 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx0-43
b-Bx0-4213 : Circuit 5
b-Bx0-4213 = (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx4-013 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx4-013
b-Bx4-03 : Circuit 5
b-Bx4-03 = (Swap ↑ ↑ • (Swap ↑ • CZ • Swap ↑) • Swap ↑ ↑)
b-Bx0-423 : Circuit 5
b-Bx0-423 = (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx4-03 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx4-03
b-Bx4-031 : Circuit 5
b-Bx4-031 = (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx0-41 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx0-41
b-Bx0-4231 : Circuit 5
b-Bx0-4231 = (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx4-031 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx4-031
b-Bx4-012 : Circuit 5
b-Bx4-012 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx0-42 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx0-42
b-Bx0-4312 : Circuit 5
b-Bx0-4312 = (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx4-012 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx4-012
b-Bx4-021 : Circuit 5
b-Bx4-021 = (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx0-41 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx0-41
b-Bx0-4321 : Circuit 5
b-Bx0-4321 = (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx4-021 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx4-021
b-Bx1-0234 : Circuit 5
b-Bx1-0234 = CCZ • (K ↑ • CCZ • K ↑ • iI) • b-Bx0-134 • (K ↑ • CCZ • K ↑ • iI) • CCZ • b-Bx0-134
b-Bx2-14 : Circuit 5
b-Bx2-14 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (CZ ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx1-204 : Circuit 5
b-Bx1-204 = CCZ • (K ↑ • CCZ • K ↑ • iI) • b-Bx2-14 • (K ↑ • CCZ • K ↑ • iI) • CCZ • b-Bx2-14
b-Bx1-234 : Circuit 5
b-Bx1-234 = (CCZ ↑) • (Toff ↑) • b-Bx2-14 • (Toff ↑) • (CCZ ↑) • b-Bx2-14
b-Bx2-10 : Circuit 5
b-Bx2-10 = CZ
b-Bx1-240 : Circuit 5
b-Bx1-240 = (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • b-Bx2-10 • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • b-Bx2-10
b-Bx3-14 : Circuit 5
b-Bx3-14 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (CZ ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx1-304 : Circuit 5
b-Bx1-304 = (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • b-Bx3-14 • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • b-Bx3-14
b-Bx1-324 : Circuit 5
b-Bx1-324 = (CCZ ↑) • (Toff ↑) • b-Bx3-14 • (Toff ↑) • (CCZ ↑) • b-Bx3-14
b-Bx3-10 : Circuit 5
b-Bx3-10 = CZ
b-Bx1-340 : Circuit 5
b-Bx1-340 = (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx3-10 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx3-10
b-Bx4-13 : Circuit 5
b-Bx4-13 = (Swap ↑ ↑ • (CZ ↑) • Swap ↑ ↑)
b-Bx1-403 : Circuit 5
b-Bx1-403 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx4-13 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx4-13
b-Bx1-423 : Circuit 5
b-Bx1-423 = (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • b-Bx4-13 • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • b-Bx4-13
b-Bx2-0134 : Circuit 5
b-Bx2-0134 = CCZ • Toffᵗ • b-Bx0-234 • Toffᵗ • CCZ • b-Bx0-234
b-Bx2-0143 : Circuit 5
b-Bx2-0143 = CCZ • Toffᵗ • b-Bx0-243 • Toffᵗ • CCZ • b-Bx0-243
b-Bx2-0341 : Circuit 5
b-Bx2-0341 = (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) • b-Bx0-241 • (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • b-Bx0-241
b-Bx2-0413 : Circuit 5
b-Bx2-0413 = (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx0-213 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx0-213
b-Bx2-1034 : Circuit 5
b-Bx2-1034 = CCZ • Toffᵗ • b-Bx1-234 • Toffᵗ • CCZ • b-Bx1-234
b-Bx2-1304 : Circuit 5
b-Bx2-1304 = (CCZ ↑) • ((K ↑ • CCZ • K ↑ • iI) ↑) • b-Bx1-204 • ((K ↑ • CCZ • K ↑ • iI) ↑) • (CCZ ↑) • b-Bx1-204
b-Bx2-1340 : Circuit 5
b-Bx2-1340 = (CCZ ↑) • ((K ↑ • CCZ • K ↑ • iI) ↑) • b-Bx1-240 • ((K ↑ • CCZ • K ↑ • iI) ↑) • (CCZ ↑) • b-Bx1-240
b-Bx2-30 : Circuit 5
b-Bx2-30 = (Swap ↑ ↑ • (Swap ↑ • CZ • Swap ↑) • Swap ↑ ↑)
b-Bx2-31 : Circuit 5
b-Bx2-31 = (Swap ↑ ↑ • (CZ ↑) • Swap ↑ ↑)
b-Bx3-241 : Circuit 5
b-Bx3-241 = (CCZ ↑ ↑) • ((K ↑ • CCZ • K ↑ • iI) ↑ ↑) • b-Bx2-31 • ((K ↑ • CCZ • K ↑ • iI) ↑ ↑) • (CCZ ↑ ↑) • b-Bx2-31
b-Bx2-3041 : Circuit 5
b-Bx2-3041 = (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) • b-Bx3-241 • (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • b-Bx3-241
b-Bx3-20 : Circuit 5
b-Bx3-20 = (Swap ↑ • CZ • Swap ↑)
b-Bx2-310 : Circuit 5
b-Bx2-310 = (CCZ ↑) • ((K ↑ • CCZ • K ↑ • iI) ↑) • b-Bx3-20 • ((K ↑ • CCZ • K ↑ • iI) ↑) • (CCZ ↑) • b-Bx3-20
b-Bx3-240 : Circuit 5
b-Bx3-240 = (CCZ ↑ ↑) • ((K ↑ • CCZ • K ↑ • iI) ↑ ↑) • b-Bx2-30 • ((K ↑ • CCZ • K ↑ • iI) ↑ ↑) • (CCZ ↑ ↑) • b-Bx2-30
b-Bx2-3140 : Circuit 5
b-Bx2-3140 = (CCZ ↑) • ((K ↑ • CCZ • K ↑ • iI) ↑) • b-Bx3-240 • ((K ↑ • CCZ • K ↑ • iI) ↑) • (CCZ ↑) • b-Bx3-240
b-Bx2-340 : Circuit 5
b-Bx2-340 = (CCZ ↑ ↑) • (Toff ↑ ↑) • b-Bx3-20 • (Toff ↑ ↑) • (CCZ ↑ ↑) • b-Bx3-20
b-Bx3-210 : Circuit 5
b-Bx3-210 = (CCZ ↑) • (Toffᵗ ↑) • b-Bx2-30 • (Toffᵗ ↑) • (CCZ ↑) • b-Bx2-30
b-Bx2-3410 : Circuit 5
b-Bx2-3410 = (CCZ ↑ ↑) • (Toff ↑ ↑) • b-Bx3-210 • (Toff ↑ ↑) • (CCZ ↑ ↑) • b-Bx3-210
b-Bx2-43 : Circuit 5
b-Bx2-43 = (CZ ↑ ↑ ↑)
b-Bx4-213 : Circuit 5
b-Bx4-213 = (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • b-Bx2-43 • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • b-Bx2-43
b-Bx2-4013 : Circuit 5
b-Bx2-4013 = (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx4-213 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx4-213
b-Bx4-203 : Circuit 5
b-Bx4-203 = (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx2-43 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx2-43
b-Bx2-4103 : Circuit 5
b-Bx2-4103 = (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • b-Bx4-203 • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • b-Bx4-203
b-Bx3-0124 : Circuit 5
b-Bx3-0124 = (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • b-Bx0-324 • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • b-Bx0-324
b-Bx3-0412 : Circuit 5
b-Bx3-0412 = (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx0-312 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx0-312
b-Bx3-1024 : Circuit 5
b-Bx3-1024 = (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • b-Bx1-324 • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • b-Bx1-324
b-Bx3-1204 : Circuit 5
b-Bx3-1204 = (CCZ ↑) • (Toffᵗ ↑) • b-Bx1-304 • (Toffᵗ ↑) • (CCZ ↑) • b-Bx1-304
b-Bx3-1240 : Circuit 5
b-Bx3-1240 = (CCZ ↑) • (Toffᵗ ↑) • b-Bx1-340 • (Toffᵗ ↑) • (CCZ ↑) • b-Bx1-340
b-Bx3-2140 : Circuit 5
b-Bx3-2140 = (CCZ ↑) • (Toffᵗ ↑) • b-Bx2-340 • (Toffᵗ ↑) • (CCZ ↑) • b-Bx2-340
b-Bx3-2410 : Circuit 5
b-Bx3-2410 = (CCZ ↑ ↑) • ((K ↑ • CCZ • K ↑ • iI) ↑ ↑) • b-Bx2-310 • ((K ↑ • CCZ • K ↑ • iI) ↑ ↑) • (CCZ ↑ ↑) • b-Bx2-310
b-Bx3-42 : Circuit 5
b-Bx3-42 = (Swap ↑ ↑ ↑ • (CZ ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx4-312 : Circuit 5
b-Bx4-312 = (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx3-42 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx3-42
b-Bx3-4012 : Circuit 5
b-Bx3-4012 = (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx4-312 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx4-312
b-Bx4-302 : Circuit 5
b-Bx4-302 = (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx3-42 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx3-42
b-Bx3-4102 : Circuit 5
b-Bx3-4102 = (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx4-302 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx4-302
b-Bx4-0123 : Circuit 5
b-Bx4-0123 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx0-423 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx0-423
b-Bx4-1023 : Circuit 5
b-Bx4-1023 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx1-423 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx1-423
b-Bx4-1203 : Circuit 5
b-Bx4-1203 = (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • b-Bx1-403 • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • b-Bx1-403
b-Bx⁻2-03 : Circuit 5
b-Bx⁻2-03 = (Swap ↑ ↑ • (Swap ↑ • CZ • Swap ↑) • Swap ↑ ↑)
b-Bx⁻0-213 : Circuit 5
b-Bx⁻0-213 = b-Bx⁻2-03 • CCZ • Toff • b-Bx⁻2-03 • Toff • CCZ
b-Bx⁻2-0413 : Circuit 5
b-Bx⁻2-0413 = b-Bx⁻0-213 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx⁻0-213 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑)
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
b-Sb3-0-4-2 : Circuit 5
b-Sb3-0-4-2 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • CS • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb⁻3-0-4-2 : Circuit 5
b-Sb⁻3-0-4-2 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb3-0-12-4 : Circuit 5
b-Sb3-0-12-4 = b-Bx3-0124 • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • b-Sb3-0-4-2 • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • b-Sb⁻3-0-4-2
b-Sb3-0-2-1 : Circuit 5
b-Sb3-0-2-1 = (Swap ↑ • CS • Swap ↑)
b-Sb⁻3-0-2-1 : Circuit 5
b-Sb⁻3-0-2-1 = (Swap ↑ • (CS • CS • CS) • Swap ↑)
b-Sb3-0-41-2 : Circuit 5
b-Sb3-0-41-2 = b-Bx3-0412 • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • b-Sb3-0-2-1 • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • b-Sb⁻3-0-2-1
b-Sb4-0-3-2 : Circuit 5
b-Sb4-0-3-2 = (Swap ↑ ↑ • (Swap ↑ • CS • Swap ↑) • Swap ↑ ↑)
b-Sb⁻4-0-3-2 : Circuit 5
b-Sb⁻4-0-3-2 = (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑)
b-Sb4-0-12-3 : Circuit 5
b-Sb4-0-12-3 = b-Bx4-0123 • (Toffᵗ ↑) • b-Sb4-0-3-2 • (Toffᵗ ↑) • b-Sb⁻4-0-3-2
b-Sb⁻2-0-41-3 : Circuit 5
b-Sb⁻2-0-41-3 = b-Sb2-0-3-1 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Sb⁻2-0-3-1 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx⁻2-0413

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
⟪ Bx0-12 ⟫ = b-Bx0-12
⟪ Bx0-14 ⟫ = b-Bx0-14
⟪ Bx1-034 ⟫ = b-Bx1-034
⟪ Bx0-1234 ⟫ = b-Bx0-1234
⟪ Bx0-13 ⟫ = b-Bx0-13
⟪ Bx1-043 ⟫ = b-Bx1-043
⟪ Bx0-1243 ⟫ = b-Bx0-1243
⟪ Bx1-024 ⟫ = b-Bx1-024
⟪ Bx0-1324 ⟫ = b-Bx0-1324
⟪ Bx1-04 ⟫ = b-Bx1-04
⟪ Bx0-134 ⟫ = b-Bx0-134
⟪ Bx1-042 ⟫ = b-Bx1-042
⟪ Bx0-1342 ⟫ = b-Bx0-1342
⟪ Bx1-023 ⟫ = b-Bx1-023
⟪ Bx0-1423 ⟫ = b-Bx0-1423
⟪ Bx1-032 ⟫ = b-Bx1-032
⟪ Bx0-1432 ⟫ = b-Bx0-1432
⟪ Bx0-21 ⟫ = b-Bx0-21
⟪ Bx2-03 ⟫ = b-Bx2-03
⟪ Bx0-213 ⟫ = b-Bx0-213
⟪ Bx0-24 ⟫ = b-Bx0-24
⟪ Bx2-034 ⟫ = b-Bx2-034
⟪ Bx0-2134 ⟫ = b-Bx0-2134
⟪ Bx0-23 ⟫ = b-Bx0-23
⟪ Bx2-043 ⟫ = b-Bx2-043
⟪ Bx0-2143 ⟫ = b-Bx0-2143
⟪ Bx2-014 ⟫ = b-Bx2-014
⟪ Bx0-2314 ⟫ = b-Bx0-2314
⟪ Bx2-04 ⟫ = b-Bx2-04
⟪ Bx0-234 ⟫ = b-Bx0-234
⟪ Bx2-041 ⟫ = b-Bx2-041
⟪ Bx0-2341 ⟫ = b-Bx0-2341
⟪ Bx2-01 ⟫ = b-Bx2-01
⟪ Bx0-241 ⟫ = b-Bx0-241
⟪ Bx2-013 ⟫ = b-Bx2-013
⟪ Bx0-2413 ⟫ = b-Bx0-2413
⟪ Bx0-243 ⟫ = b-Bx0-243
⟪ Bx2-031 ⟫ = b-Bx2-031
⟪ Bx0-2431 ⟫ = b-Bx0-2431
⟪ Bx0-31 ⟫ = b-Bx0-31
⟪ Bx3-02 ⟫ = b-Bx3-02
⟪ Bx0-312 ⟫ = b-Bx0-312
⟪ Bx0-34 ⟫ = b-Bx0-34
⟪ Bx3-024 ⟫ = b-Bx3-024
⟪ Bx0-3124 ⟫ = b-Bx0-3124
⟪ Bx0-32 ⟫ = b-Bx0-32
⟪ Bx3-042 ⟫ = b-Bx3-042
⟪ Bx0-3142 ⟫ = b-Bx0-3142
⟪ Bx3-014 ⟫ = b-Bx3-014
⟪ Bx0-3214 ⟫ = b-Bx0-3214
⟪ Bx3-04 ⟫ = b-Bx3-04
⟪ Bx0-324 ⟫ = b-Bx0-324
⟪ Bx3-041 ⟫ = b-Bx3-041
⟪ Bx0-3241 ⟫ = b-Bx0-3241
⟪ Bx3-012 ⟫ = b-Bx3-012
⟪ Bx0-3412 ⟫ = b-Bx0-3412
⟪ Bx3-021 ⟫ = b-Bx3-021
⟪ Bx0-3421 ⟫ = b-Bx0-3421
⟪ Bx0-41 ⟫ = b-Bx0-41
⟪ Bx0-43 ⟫ = b-Bx0-43
⟪ Bx4-023 ⟫ = b-Bx4-023
⟪ Bx0-4123 ⟫ = b-Bx0-4123
⟪ Bx0-42 ⟫ = b-Bx0-42
⟪ Bx4-032 ⟫ = b-Bx4-032
⟪ Bx0-4132 ⟫ = b-Bx0-4132
⟪ Bx4-013 ⟫ = b-Bx4-013
⟪ Bx0-4213 ⟫ = b-Bx0-4213
⟪ Bx4-03 ⟫ = b-Bx4-03
⟪ Bx0-423 ⟫ = b-Bx0-423
⟪ Bx4-031 ⟫ = b-Bx4-031
⟪ Bx0-4231 ⟫ = b-Bx0-4231
⟪ Bx4-012 ⟫ = b-Bx4-012
⟪ Bx0-4312 ⟫ = b-Bx0-4312
⟪ Bx4-021 ⟫ = b-Bx4-021
⟪ Bx0-4321 ⟫ = b-Bx0-4321
⟪ Bx1-0234 ⟫ = b-Bx1-0234
⟪ Bx2-14 ⟫ = b-Bx2-14
⟪ Bx1-204 ⟫ = b-Bx1-204
⟪ Bx1-234 ⟫ = b-Bx1-234
⟪ Bx2-10 ⟫ = b-Bx2-10
⟪ Bx1-240 ⟫ = b-Bx1-240
⟪ Bx3-14 ⟫ = b-Bx3-14
⟪ Bx1-304 ⟫ = b-Bx1-304
⟪ Bx1-324 ⟫ = b-Bx1-324
⟪ Bx3-10 ⟫ = b-Bx3-10
⟪ Bx1-340 ⟫ = b-Bx1-340
⟪ Bx4-13 ⟫ = b-Bx4-13
⟪ Bx1-403 ⟫ = b-Bx1-403
⟪ Bx1-423 ⟫ = b-Bx1-423
⟪ Bx2-0134 ⟫ = b-Bx2-0134
⟪ Bx2-0143 ⟫ = b-Bx2-0143
⟪ Bx2-0341 ⟫ = b-Bx2-0341
⟪ Bx2-0413 ⟫ = b-Bx2-0413
⟪ Bx2-1034 ⟫ = b-Bx2-1034
⟪ Bx2-1304 ⟫ = b-Bx2-1304
⟪ Bx2-1340 ⟫ = b-Bx2-1340
⟪ Bx2-30 ⟫ = b-Bx2-30
⟪ Bx2-31 ⟫ = b-Bx2-31
⟪ Bx3-241 ⟫ = b-Bx3-241
⟪ Bx2-3041 ⟫ = b-Bx2-3041
⟪ Bx3-20 ⟫ = b-Bx3-20
⟪ Bx2-310 ⟫ = b-Bx2-310
⟪ Bx3-240 ⟫ = b-Bx3-240
⟪ Bx2-3140 ⟫ = b-Bx2-3140
⟪ Bx2-340 ⟫ = b-Bx2-340
⟪ Bx3-210 ⟫ = b-Bx3-210
⟪ Bx2-3410 ⟫ = b-Bx2-3410
⟪ Bx2-43 ⟫ = b-Bx2-43
⟪ Bx4-213 ⟫ = b-Bx4-213
⟪ Bx2-4013 ⟫ = b-Bx2-4013
⟪ Bx4-203 ⟫ = b-Bx4-203
⟪ Bx2-4103 ⟫ = b-Bx2-4103
⟪ Bx3-0124 ⟫ = b-Bx3-0124
⟪ Bx3-0412 ⟫ = b-Bx3-0412
⟪ Bx3-1024 ⟫ = b-Bx3-1024
⟪ Bx3-1204 ⟫ = b-Bx3-1204
⟪ Bx3-1240 ⟫ = b-Bx3-1240
⟪ Bx3-2140 ⟫ = b-Bx3-2140
⟪ Bx3-2410 ⟫ = b-Bx3-2410
⟪ Bx3-42 ⟫ = b-Bx3-42
⟪ Bx4-312 ⟫ = b-Bx4-312
⟪ Bx3-4012 ⟫ = b-Bx3-4012
⟪ Bx4-302 ⟫ = b-Bx4-302
⟪ Bx3-4102 ⟫ = b-Bx3-4102
⟪ Bx4-0123 ⟫ = b-Bx4-0123
⟪ Bx4-1023 ⟫ = b-Bx4-1023
⟪ Bx4-1203 ⟫ = b-Bx4-1203
⟪ Bx⁻2-03 ⟫ = b-Bx⁻2-03
⟪ Bx⁻0-213 ⟫ = b-Bx⁻0-213
⟪ Bx⁻2-0413 ⟫ = b-Bx⁻2-0413
⟪ Sb0-1-3-2 ⟫ = b-Sb0-1-3-2
⟪ Sb⁻0-1-3-2 ⟫ = b-Sb⁻0-1-3-2
⟪ Sb0-1-42-3 ⟫ = b-Sb0-1-42-3
⟪ Sb0-2-1-3 ⟫ = b-Sb0-2-1-3
⟪ Sb⁻0-2-1-3 ⟫ = b-Sb⁻0-2-1-3
⟪ Sb0-2-43-1 ⟫ = b-Sb0-2-43-1
⟪ Sb2-0-3-1 ⟫ = b-Sb2-0-3-1
⟪ Sb⁻2-0-3-1 ⟫ = b-Sb⁻2-0-3-1
⟪ Sb2-0-41-3 ⟫ = b-Sb2-0-41-3
⟪ Sb3-0-4-2 ⟫ = b-Sb3-0-4-2
⟪ Sb⁻3-0-4-2 ⟫ = b-Sb⁻3-0-4-2
⟪ Sb3-0-12-4 ⟫ = b-Sb3-0-12-4
⟪ Sb3-0-2-1 ⟫ = b-Sb3-0-2-1
⟪ Sb⁻3-0-2-1 ⟫ = b-Sb⁻3-0-2-1
⟪ Sb3-0-41-2 ⟫ = b-Sb3-0-41-2
⟪ Sb4-0-3-2 ⟫ = b-Sb4-0-3-2
⟪ Sb⁻4-0-3-2 ⟫ = b-Sb⁻4-0-3-2
⟪ Sb4-0-12-3 ⟫ = b-Sb4-0-12-3
⟪ Sb⁻2-0-41-3 ⟫ = b-Sb⁻2-0-41-3
