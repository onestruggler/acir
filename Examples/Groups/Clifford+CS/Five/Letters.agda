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
  Bx0-12 Bx1-03 Bx0-123 Bx0-14 Bx1-034 Bx0-1234 Bx1-04 Bx0-124 Bx0-13 Bx1-043 Bx0-1243 Bx1-02 : Mac
  Bx0-132 Bx1-024 Bx0-1324 Bx0-134 Bx1-042 Bx0-1342 Bx0-142 Bx1-023 Bx0-1423 Bx0-143 Bx1-032 Bx0-1432 : Mac
  Bx0-21 Bx2-03 Bx0-213 Bx0-24 Bx2-034 Bx0-2134 Bx2-04 Bx0-214 Bx0-23 Bx2-043 Bx0-2143 Bx2-01 : Mac
  Bx0-231 Bx2-014 Bx0-2314 Bx0-234 Bx2-041 Bx0-2341 Bx0-241 Bx2-013 Bx0-2413 Bx0-243 Bx2-031 Bx0-2431 : Mac
  Bx0-31 Bx3-02 Bx0-312 Bx0-34 Bx3-024 Bx0-3124 Bx3-04 Bx0-314 Bx0-32 Bx3-042 Bx0-3142 Bx3-01 : Mac
  Bx0-321 Bx3-014 Bx0-3214 Bx0-324 Bx3-041 Bx0-3241 Bx0-341 Bx3-012 Bx0-3412 Bx0-342 Bx3-021 Bx0-3421 : Mac
  Bx0-41 Bx4-02 Bx0-412 Bx0-43 Bx4-023 Bx0-4123 Bx4-03 Bx0-413 Bx0-42 Bx4-032 Bx0-4132 Bx4-01 : Mac
  Bx0-421 Bx4-013 Bx0-4213 Bx0-423 Bx4-031 Bx0-4231 Bx0-431 Bx4-012 Bx0-4312 Bx0-432 Bx4-021 Bx0-4321 : Mac
  Bx1-0234 Bx1-0243 Bx1-0324 Bx1-0342 Bx1-0423 Bx1-0432 Bx1-20 Bx2-13 Bx1-203 Bx1-24 Bx2-134 Bx1-2034 : Mac
  Bx2-14 Bx1-204 Bx1-23 Bx2-143 Bx1-2043 Bx2-10 Bx1-230 Bx2-104 Bx1-2304 Bx1-234 Bx2-140 Bx1-2340 : Mac
  Bx1-240 Bx2-103 Bx1-2403 Bx1-243 Bx2-130 Bx1-2430 Bx1-30 Bx3-12 Bx1-302 Bx1-34 Bx3-124 Bx1-3024 : Mac
  Bx3-14 Bx1-304 Bx1-32 Bx3-142 Bx1-3042 Bx3-10 Bx1-320 Bx3-104 Bx1-3204 Bx1-324 Bx3-140 Bx1-3240 : Mac
  Bx1-340 Bx3-102 Bx1-3402 Bx1-342 Bx3-120 Bx1-3420 Bx1-40 Bx4-12 Bx1-402 Bx1-43 Bx4-123 Bx1-4023 : Mac
  Bx4-13 Bx1-403 Bx1-42 Bx4-132 Bx1-4032 Bx4-10 Bx1-420 Bx4-103 Bx1-4203 Bx1-423 Bx4-130 Bx1-4230 : Mac
  Bx1-430 Bx4-102 Bx1-4302 Bx1-432 Bx4-120 Bx1-4320 Bx2-0134 Bx2-0143 Bx2-0314 Bx2-0341 Bx2-0413 Bx2-0431 : Mac
  Bx2-1034 Bx2-1043 Bx2-1304 Bx2-1340 Bx2-1403 Bx2-1430 Bx2-30 Bx3-21 Bx2-301 Bx2-34 Bx3-214 Bx2-3014 : Mac
  Bx3-24 Bx2-304 Bx2-31 Bx3-241 Bx2-3041 Bx3-20 Bx2-310 Bx3-204 Bx2-3104 Bx2-314 Bx3-240 Bx2-3140 : Mac
  Bx2-340 Bx3-201 Bx2-3401 Bx2-341 Bx3-210 Bx2-3410 Bx2-40 Bx4-21 Bx2-401 Bx2-43 Bx4-213 Bx2-4013 : Mac
  Bx4-23 Bx2-403 Bx2-41 Bx4-231 Bx2-4031 Bx4-20 Bx2-410 Bx4-203 Bx2-4103 Bx2-413 Bx4-230 Bx2-4130 : Mac
  Bx2-430 Bx4-201 Bx2-4301 Bx2-431 Bx4-210 Bx2-4310 Bx3-0124 Bx3-0142 Bx3-0214 Bx3-0241 Bx3-0412 Bx3-0421 : Mac
  Bx3-1024 Bx3-1042 Bx3-1204 Bx3-1240 Bx3-1402 Bx3-1420 Bx3-2014 Bx3-2041 Bx3-2104 Bx3-2140 Bx3-2401 Bx3-2410 : Mac
  Bx3-40 Bx3-42 Bx4-312 Bx3-4012 Bx4-32 Bx3-402 Bx3-41 Bx4-321 Bx3-4021 Bx4-302 Bx3-4102 Bx3-412 : Mac
  Bx4-320 Bx3-4120 Bx4-30 Bx3-420 Bx4-301 Bx3-4201 Bx4-31 Bx3-421 Bx4-310 Bx3-4210 Bx4-0123 Bx4-0132 : Mac
  Bx4-0213 Bx4-0231 Bx4-0312 Bx4-0321 Bx4-1023 Bx4-1032 Bx4-1203 Bx4-1230 Bx4-1302 Bx4-1320 Bx4-2013 Bx4-2031 : Mac
  Bx4-2103 Bx4-2130 Bx4-2301 Bx4-2310 Bx4-3012 Bx4-3021 Bx4-3102 Bx4-3120 Bx⁻0-12 Bx⁻1-03 Bx⁻0-123 Bx⁻0-14 : Mac
  Bx⁻1-034 Bx⁻0-1234 Bx⁻1-04 Bx⁻0-124 Bx⁻0-13 Bx⁻1-043 Bx⁻0-1243 Bx⁻1-02 Bx⁻0-132 Bx⁻1-024 Bx⁻0-1324 Bx⁻0-134 : Mac
  Bx⁻1-042 Bx⁻0-1342 Bx⁻0-142 Bx⁻1-023 Bx⁻0-1423 Bx⁻0-143 Bx⁻1-032 Bx⁻0-1432 Bx⁻0-21 Bx⁻2-03 Bx⁻0-213 Bx⁻0-24 : Mac
  Bx⁻2-034 Bx⁻0-2134 Bx⁻2-04 Bx⁻0-214 Bx⁻2-01 Bx⁻0-231 Bx⁻0-234 Bx⁻2-041 Bx⁻0-2341 Bx⁻0-241 Bx⁻0-243 Bx⁻2-031 : Mac
  Bx⁻0-2431 Bx⁻3-02 Bx⁻0-312 Bx⁻0-34 Bx⁻3-024 Bx⁻0-3124 Bx⁻3-01 Bx⁻0-321 Bx⁻3-04 Bx⁻0-324 Bx⁻4-02 Bx⁻0-412 : Mac
  Bx⁻0-43 Bx⁻4-023 Bx⁻0-4123 Bx⁻4-03 Bx⁻0-413 Bx⁻4-01 Bx⁻0-421 Bx⁻0-423 Bx⁻0-431 Bx⁻0-432 Bx⁻1-0234 Bx⁻1-0243 : Mac
  Bx⁻1-0324 Bx⁻1-0342 Bx⁻1-0423 Bx⁻1-0432 Bx⁻1-20 Bx⁻2-13 Bx⁻1-203 Bx⁻1-24 Bx⁻2-134 Bx⁻1-2034 Bx⁻1-23 Bx⁻2-140 : Mac
  Bx⁻1-2340 Bx⁻2-10 Bx⁻1-240 Bx⁻2-103 Bx⁻1-2403 Bx⁻1-34 Bx⁻3-124 Bx⁻1-3024 Bx⁻1-32 Bx⁻3-102 Bx⁻1-3402 Bx⁻1-43 : Mac
  Bx⁻4-123 Bx⁻1-4023 Bx⁻1-42 Bx⁻4-10 Bx⁻1-420 Bx⁻4-103 Bx⁻1-4203 Bx⁻1-430 Bx⁻4-102 Bx⁻1-4302 Bx⁻2-0134 Bx⁻2-0143 : Mac
  Bx⁻2-0314 Bx⁻2-0341 Bx⁻2-0413 Bx⁻2-0431 Bx⁻2-1340 Bx⁻2-1403 Bx⁻2-34 Bx⁻3-214 Bx⁻2-3014 Bx⁻2-43 Bx⁻4-213 Bx⁻2-4013 : Mac
  Bx⁻4-203 Bx⁻2-4103 Bx⁻3-0124 Bx⁻3-0412 Bx⁻3-0421 Bx⁻4-0123 Bx⁻4-0132 Bx⁻4-0213 Bx⁻4-0231 Bx⁻4-0312 Bx⁻4-0321 Bx⁻4-1230 : Mac
  Bx⁻4-1320 Sb0-1-2-3 Sb0-1-2-4 Sb0-1-4-3 Sb⁻0-1-4-3 Sb0-1-23-4 Sb0-1-3-2 Sb0-1-3-4 Sb0-1-4-2 Sb⁻0-1-4-2 Sb0-1-32-4 Sb⁻0-1-2-4 : Mac
  Sb0-1-34-2 Sb⁻0-1-3-2 Sb0-1-42-3 Sb⁻0-1-2-3 Sb0-1-43-2 Sb0-2-1-3 Sb0-2-1-4 Sb0-2-4-3 Sb⁻0-2-4-3 Sb0-2-13-4 Sb0-2-3-1 Sb0-2-4-1 : Mac
  Sb⁻0-2-4-1 Sb0-2-31-4 Sb⁻0-2-1-4 Sb0-2-34-1 Sb⁻0-2-3-1 Sb0-2-41-3 Sb⁻0-2-1-3 Sb0-2-43-1 Sb0-3-1-2 Sb0-3-1-4 Sb0-3-4-2 Sb⁻0-3-4-2 : Mac
  Sb0-3-12-4 Sb0-3-2-4 Sb⁻0-3-2-4 Sb0-3-14-2 Sb0-3-2-1 Sb0-3-4-1 Sb⁻0-3-4-1 Sb0-3-21-4 Sb⁻0-3-1-4 Sb0-3-24-1 Sb0-4-1-2 Sb0-4-1-3 : Mac
  Sb0-4-3-2 Sb⁻0-4-3-2 Sb0-4-12-3 Sb0-4-2-1 Sb0-4-3-1 Sb⁻0-4-3-1 Sb0-4-21-3 Sb1-0-2-3 Sb1-0-2-4 Sb1-0-4-3 Sb⁻1-0-4-3 Sb1-0-23-4 : Mac
  Sb1-0-3-4 Sb⁻1-0-3-4 Sb1-0-24-3 Sb1-0-3-2 Sb1-0-4-2 Sb⁻1-0-4-2 Sb1-0-32-4 Sb⁻1-0-2-4 Sb1-0-34-2 Sb⁻1-0-3-2 Sb1-0-42-3 Sb⁻1-0-2-3 : Mac
  Sb1-0-43-2 Sb1-2-0-3 Sb1-2-0-4 Sb1-2-4-3 Sb⁻1-2-4-3 Sb1-2-03-4 Sb1-2-3-4 Sb⁻1-2-3-4 Sb1-2-04-3 Sb1-2-3-0 Sb⁻1-2-0-4 Sb1-2-34-0 : Mac
  Sb1-2-4-0 Sb⁻1-2-3-0 Sb1-2-40-3 Sb⁻1-2-0-3 Sb1-2-43-0 Sb1-3-0-4 Sb1-3-2-4 Sb⁻1-3-2-4 Sb1-3-04-2 Sb1-3-2-0 Sb⁻1-3-0-4 Sb1-3-24-0 : Mac
  Sb1-3-4-0 Sb⁻1-3-2-0 Sb1-3-40-2 Sb1-4-2-0 Sb1-4-3-0 Sb⁻1-4-3-0 Sb1-4-20-3 Sb⁻1-4-2-0 Sb1-4-30-2 Sb2-0-1-3 Sb2-0-1-4 Sb2-0-4-3 : Mac
  Sb⁻2-0-4-3 Sb2-0-13-4 Sb2-0-3-4 Sb⁻2-0-3-4 Sb2-0-14-3 Sb2-0-3-1 Sb2-0-4-1 Sb⁻2-0-4-1 Sb2-0-31-4 Sb⁻2-0-1-4 Sb2-0-34-1 Sb⁻2-0-3-1 : Mac
  Sb2-0-41-3 Sb⁻2-0-1-3 Sb2-0-43-1 Sb2-1-0-3 Sb2-1-0-4 Sb2-1-3-0 Sb⁻2-1-0-4 Sb2-1-34-0 Sb2-1-4-0 Sb⁻2-1-3-0 Sb2-1-40-3 Sb⁻2-1-0-3 : Mac
  Sb2-1-43-0 Sb2-3-0-1 Sb2-3-0-4 Sb2-3-1-4 Sb⁻2-3-1-4 Sb2-3-04-1 Sb2-3-1-0 Sb⁻2-3-0-4 Sb2-3-14-0 Sb⁻2-3-1-0 Sb2-3-40-1 Sb⁻2-3-0-1 : Mac
  Sb2-3-41-0 Sb2-4-0-1 Sb2-4-3-1 Sb⁻2-4-3-1 Sb2-4-01-3 Sb2-4-1-0 Sb2-4-3-0 Sb⁻2-4-3-0 Sb2-4-10-3 Sb⁻2-4-1-0 Sb2-4-30-1 Sb⁻2-4-0-1 : Mac
  Sb2-4-31-0 Sb3-0-1-2 Sb3-0-1-4 Sb3-0-2-4 Sb⁻3-0-2-4 Sb3-0-14-2 Sb3-0-2-1 Sb3-0-4-1 Sb⁻3-0-4-1 Sb3-0-21-4 Sb⁻3-0-1-4 Sb3-0-24-1 : Mac
  Sb⁻3-0-2-1 Sb3-0-41-2 Sb⁻3-0-1-2 Sb3-0-42-1 Sb3-1-0-2 Sb3-1-0-4 Sb3-1-2-0 Sb3-1-4-0 Sb⁻3-1-2-0 Sb3-1-40-2 Sb⁻3-1-0-2 Sb3-1-42-0 : Mac
  Sb3-2-0-1 Sb3-2-1-0 Sb⁻3-2-1-0 Sb3-2-40-1 Sb⁻3-2-0-1 Sb3-2-41-0 Sb3-4-0-1 Sb3-4-0-2 Sb3-4-2-1 Sb⁻3-4-2-1 Sb3-4-01-2 Sb3-4-1-0 : Mac
  Sb3-4-2-0 Sb⁻3-4-2-0 Sb3-4-10-2 Sb⁻3-4-0-2 Sb3-4-12-0 Sb⁻3-4-1-0 Sb3-4-20-1 Sb⁻3-4-0-1 Sb3-4-21-0 Sb4-0-1-2 Sb4-0-1-3 Sb4-0-2-1 : Mac
  Sb4-0-3-1 Sb⁻4-0-3-1 Sb4-0-21-3 Sb⁻4-0-1-3 Sb4-0-23-1 Sb⁻4-0-2-1 Sb4-0-31-2 Sb⁻4-0-1-2 Sb4-0-32-1 Sb4-1-0-2 Sb4-1-0-3 Sb4-1-2-0 : Mac
  Sb⁻4-1-0-3 Sb4-1-23-0 Sb4-1-3-0 Sb⁻4-1-0-2 Sb4-1-32-0 Sb4-2-3-0 Sb4-3-1-0 Sb4-3-2-0 Sb⁻0-1-23-4 Sb⁻0-1-3-4 Sb⁻0-1-32-4 Sb⁻0-1-34-2 : Mac
  Sb⁻0-1-42-3 Sb⁻0-1-43-2 Sb⁻0-2-34-1 Sb⁻0-2-43-1 Sb⁻0-3-1-2 Sb⁻0-3-2-1 Sb⁻0-4-1-2 Sb⁻0-4-1-3 Sb⁻0-4-2-1 Sb⁻1-0-23-4 Sb⁻1-0-24-3 Sb⁻1-0-32-4 : Mac
  Sb⁻1-0-34-2 Sb⁻1-0-42-3 Sb⁻1-0-43-2 Sb⁻1-2-34-0 Sb⁻1-2-4-0 Sb⁻1-2-40-3 Sb⁻1-3-4-0 Sb⁻1-3-4-2 Sb⁻1-3-40-2 Sb⁻1-4-20-3 Sb⁻1-4-30-2 Sb⁻2-0-13-4 : Mac
  Sb⁻2-0-14-3 Sb⁻2-0-31-4 Sb⁻2-0-34-1 Sb⁻2-0-41-3 Sb⁻2-0-43-1 Sb⁻2-1-34-0 Sb⁻2-1-4-0 Sb⁻2-1-40-3 Sb⁻2-3-4-0 Sb⁻2-3-4-1 Sb⁻2-4-01-3 Sb⁻2-4-10-3 : Mac
  Sb⁻3-0-41-2 Sb⁻3-0-42-1 Sb⁻3-1-0-4 Sb⁻3-1-4-0 Sb⁻4-0-23-1 Sb⁻4-0-31-2 Sb⁻4-0-32-1 Sb⁻4-1-2-0 Sb⁻4-1-23-0 Sb⁻4-1-3-0 Sb⁻4-1-32-0 : Mac

-- The boxes, each the concatenation of its one-level unfolding.

b-Bx0-12 : Circuit 5
b-Bx0-12 = (CZ ↑)
b-Bx1-03 : Circuit 5
b-Bx1-03 = (Swap ↑ ↑ • (Swap ↑ • CZ • Swap ↑) • Swap ↑ ↑)
b-Bx0-123 : Circuit 5
b-Bx0-123 = CCZ • Toff • b-Bx1-03 • Toff • CCZ • b-Bx1-03
b-Bx0-14 : Circuit 5
b-Bx0-14 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (CZ ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx1-034 : Circuit 5
b-Bx1-034 = (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • b-Bx0-14 • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • b-Bx0-14
b-Bx0-1234 : Circuit 5
b-Bx0-1234 = CCZ • Toff • b-Bx1-034 • Toff • CCZ • b-Bx1-034
b-Bx1-04 : Circuit 5
b-Bx1-04 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • CZ • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx0-124 : Circuit 5
b-Bx0-124 = CCZ • Toff • b-Bx1-04 • Toff • CCZ • b-Bx1-04
b-Bx0-13 : Circuit 5
b-Bx0-13 = (Swap ↑ ↑ • (CZ ↑) • Swap ↑ ↑)
b-Bx1-043 : Circuit 5
b-Bx1-043 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx0-13 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx0-13
b-Bx0-1243 : Circuit 5
b-Bx0-1243 = CCZ • Toff • b-Bx1-043 • Toff • CCZ • b-Bx1-043
b-Bx1-02 : Circuit 5
b-Bx1-02 = (Swap ↑ • CZ • Swap ↑)
b-Bx0-132 : Circuit 5
b-Bx0-132 = (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • b-Bx1-02 • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • b-Bx1-02
b-Bx1-024 : Circuit 5
b-Bx1-024 = CCZ • (K ↑ • CCZ • K ↑ • iI) • b-Bx0-14 • (K ↑ • CCZ • K ↑ • iI) • CCZ • b-Bx0-14
b-Bx0-1324 : Circuit 5
b-Bx0-1324 = (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • b-Bx1-024 • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • b-Bx1-024
b-Bx0-134 : Circuit 5
b-Bx0-134 = (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • b-Bx1-04 • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • b-Bx1-04
b-Bx1-042 : Circuit 5
b-Bx1-042 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx0-12 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx0-12
b-Bx0-1342 : Circuit 5
b-Bx0-1342 = (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • b-Bx1-042 • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • b-Bx1-042
b-Bx0-142 : Circuit 5
b-Bx0-142 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx1-02 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx1-02
b-Bx1-023 : Circuit 5
b-Bx1-023 = CCZ • (K ↑ • CCZ • K ↑ • iI) • b-Bx0-13 • (K ↑ • CCZ • K ↑ • iI) • CCZ • b-Bx0-13
b-Bx0-1423 : Circuit 5
b-Bx0-1423 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx1-023 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx1-023
b-Bx0-143 : Circuit 5
b-Bx0-143 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx1-03 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx1-03
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
b-Bx2-04 : Circuit 5
b-Bx2-04 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • CZ • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx0-214 : Circuit 5
b-Bx0-214 = CCZ • Toff • b-Bx2-04 • Toff • CCZ • b-Bx2-04
b-Bx0-23 : Circuit 5
b-Bx0-23 = (CZ ↑ ↑)
b-Bx2-043 : Circuit 5
b-Bx2-043 = (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx0-23 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx0-23
b-Bx0-2143 : Circuit 5
b-Bx0-2143 = CCZ • Toff • b-Bx2-043 • Toff • CCZ • b-Bx2-043
b-Bx2-01 : Circuit 5
b-Bx2-01 = CZ
b-Bx0-231 : Circuit 5
b-Bx0-231 = (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • b-Bx2-01 • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • b-Bx2-01
b-Bx2-014 : Circuit 5
b-Bx2-014 = CCZ • Toffᵗ • b-Bx0-24 • Toffᵗ • CCZ • b-Bx0-24
b-Bx0-2314 : Circuit 5
b-Bx0-2314 = (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • b-Bx2-014 • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • b-Bx2-014
b-Bx0-234 : Circuit 5
b-Bx0-234 = (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • b-Bx2-04 • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • b-Bx2-04
b-Bx2-041 : Circuit 5
b-Bx2-041 = (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx0-21 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx0-21
b-Bx0-2341 : Circuit 5
b-Bx0-2341 = (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • b-Bx2-041 • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • b-Bx2-041
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
b-Bx3-04 : Circuit 5
b-Bx3-04 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • CZ • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx0-314 : Circuit 5
b-Bx0-314 = (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • b-Bx3-04 • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • b-Bx3-04
b-Bx0-32 : Circuit 5
b-Bx0-32 = (CZ ↑ ↑)
b-Bx3-042 : Circuit 5
b-Bx3-042 = (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx0-32 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx0-32
b-Bx0-3142 : Circuit 5
b-Bx0-3142 = (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • b-Bx3-042 • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • b-Bx3-042
b-Bx3-01 : Circuit 5
b-Bx3-01 = CZ
b-Bx0-321 : Circuit 5
b-Bx0-321 = (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • b-Bx3-01 • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • b-Bx3-01
b-Bx3-014 : Circuit 5
b-Bx3-014 = (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • b-Bx0-34 • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • b-Bx0-34
b-Bx0-3214 : Circuit 5
b-Bx0-3214 = (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • b-Bx3-014 • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • b-Bx3-014
b-Bx0-324 : Circuit 5
b-Bx0-324 = (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • b-Bx3-04 • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • b-Bx3-04
b-Bx3-041 : Circuit 5
b-Bx3-041 = (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx0-31 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx0-31
b-Bx0-3241 : Circuit 5
b-Bx0-3241 = (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • b-Bx3-041 • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • b-Bx3-041
b-Bx0-341 : Circuit 5
b-Bx0-341 = (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx3-01 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx3-01
b-Bx3-012 : Circuit 5
b-Bx3-012 = (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • b-Bx0-32 • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • b-Bx0-32
b-Bx0-3412 : Circuit 5
b-Bx0-3412 = (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx3-012 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx3-012
b-Bx0-342 : Circuit 5
b-Bx0-342 = (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx3-02 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx3-02
b-Bx3-021 : Circuit 5
b-Bx3-021 = (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) • b-Bx0-31 • (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • b-Bx0-31
b-Bx0-3421 : Circuit 5
b-Bx0-3421 = (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx3-021 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx3-021
b-Bx0-41 : Circuit 5
b-Bx0-41 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (CZ ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx4-02 : Circuit 5
b-Bx4-02 = (Swap ↑ • CZ • Swap ↑)
b-Bx0-412 : Circuit 5
b-Bx0-412 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx4-02 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx4-02
b-Bx0-43 : Circuit 5
b-Bx0-43 = (CZ ↑ ↑ ↑)
b-Bx4-023 : Circuit 5
b-Bx4-023 = (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx0-43 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx0-43
b-Bx0-4123 : Circuit 5
b-Bx0-4123 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx4-023 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx4-023
b-Bx4-03 : Circuit 5
b-Bx4-03 = (Swap ↑ ↑ • (Swap ↑ • CZ • Swap ↑) • Swap ↑ ↑)
b-Bx0-413 : Circuit 5
b-Bx0-413 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx4-03 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx4-03
b-Bx0-42 : Circuit 5
b-Bx0-42 = (Swap ↑ ↑ ↑ • (CZ ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx4-032 : Circuit 5
b-Bx4-032 = (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx0-42 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx0-42
b-Bx0-4132 : Circuit 5
b-Bx0-4132 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx4-032 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx4-032
b-Bx4-01 : Circuit 5
b-Bx4-01 = CZ
b-Bx0-421 : Circuit 5
b-Bx0-421 = (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx4-01 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx4-01
b-Bx4-013 : Circuit 5
b-Bx4-013 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx0-43 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx0-43
b-Bx0-4213 : Circuit 5
b-Bx0-4213 = (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx4-013 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx4-013
b-Bx0-423 : Circuit 5
b-Bx0-423 = (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx4-03 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx4-03
b-Bx4-031 : Circuit 5
b-Bx4-031 = (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx0-41 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx0-41
b-Bx0-4231 : Circuit 5
b-Bx0-4231 = (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx4-031 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx4-031
b-Bx0-431 : Circuit 5
b-Bx0-431 = (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx4-01 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx4-01
b-Bx4-012 : Circuit 5
b-Bx4-012 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx0-42 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx0-42
b-Bx0-4312 : Circuit 5
b-Bx0-4312 = (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx4-012 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx4-012
b-Bx0-432 : Circuit 5
b-Bx0-432 = (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx4-02 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx4-02
b-Bx4-021 : Circuit 5
b-Bx4-021 = (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx0-41 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx0-41
b-Bx0-4321 : Circuit 5
b-Bx0-4321 = (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx4-021 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx4-021
b-Bx1-0234 : Circuit 5
b-Bx1-0234 = CCZ • (K ↑ • CCZ • K ↑ • iI) • b-Bx0-134 • (K ↑ • CCZ • K ↑ • iI) • CCZ • b-Bx0-134
b-Bx1-0243 : Circuit 5
b-Bx1-0243 = CCZ • (K ↑ • CCZ • K ↑ • iI) • b-Bx0-143 • (K ↑ • CCZ • K ↑ • iI) • CCZ • b-Bx0-143
b-Bx1-0324 : Circuit 5
b-Bx1-0324 = (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • b-Bx0-124 • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • b-Bx0-124
b-Bx1-0342 : Circuit 5
b-Bx1-0342 = (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • b-Bx0-142 • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • b-Bx0-142
b-Bx1-0423 : Circuit 5
b-Bx1-0423 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx0-123 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx0-123
b-Bx1-0432 : Circuit 5
b-Bx1-0432 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx0-132 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx0-132
b-Bx1-20 : Circuit 5
b-Bx1-20 = (Swap ↑ • CZ • Swap ↑)
b-Bx2-13 : Circuit 5
b-Bx2-13 = (Swap ↑ ↑ • (CZ ↑) • Swap ↑ ↑)
b-Bx1-203 : Circuit 5
b-Bx1-203 = CCZ • (K ↑ • CCZ • K ↑ • iI) • b-Bx2-13 • (K ↑ • CCZ • K ↑ • iI) • CCZ • b-Bx2-13
b-Bx1-24 : Circuit 5
b-Bx1-24 = (Swap ↑ ↑ ↑ • (CZ ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx2-134 : Circuit 5
b-Bx2-134 = (CCZ ↑) • ((K ↑ • CCZ • K ↑ • iI) ↑) • b-Bx1-24 • ((K ↑ • CCZ • K ↑ • iI) ↑) • (CCZ ↑) • b-Bx1-24
b-Bx1-2034 : Circuit 5
b-Bx1-2034 = CCZ • (K ↑ • CCZ • K ↑ • iI) • b-Bx2-134 • (K ↑ • CCZ • K ↑ • iI) • CCZ • b-Bx2-134
b-Bx2-14 : Circuit 5
b-Bx2-14 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (CZ ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx1-204 : Circuit 5
b-Bx1-204 = CCZ • (K ↑ • CCZ • K ↑ • iI) • b-Bx2-14 • (K ↑ • CCZ • K ↑ • iI) • CCZ • b-Bx2-14
b-Bx1-23 : Circuit 5
b-Bx1-23 = (CZ ↑ ↑)
b-Bx2-143 : Circuit 5
b-Bx2-143 = (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • b-Bx1-23 • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • b-Bx1-23
b-Bx1-2043 : Circuit 5
b-Bx1-2043 = CCZ • (K ↑ • CCZ • K ↑ • iI) • b-Bx2-143 • (K ↑ • CCZ • K ↑ • iI) • CCZ • b-Bx2-143
b-Bx2-10 : Circuit 5
b-Bx2-10 = CZ
b-Bx1-230 : Circuit 5
b-Bx1-230 = (CCZ ↑) • (Toff ↑) • b-Bx2-10 • (Toff ↑) • (CCZ ↑) • b-Bx2-10
b-Bx2-104 : Circuit 5
b-Bx2-104 = CCZ • Toffᵗ • b-Bx1-24 • Toffᵗ • CCZ • b-Bx1-24
b-Bx1-2304 : Circuit 5
b-Bx1-2304 = (CCZ ↑) • (Toff ↑) • b-Bx2-104 • (Toff ↑) • (CCZ ↑) • b-Bx2-104
b-Bx1-234 : Circuit 5
b-Bx1-234 = (CCZ ↑) • (Toff ↑) • b-Bx2-14 • (Toff ↑) • (CCZ ↑) • b-Bx2-14
b-Bx2-140 : Circuit 5
b-Bx2-140 = (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • b-Bx1-20 • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • b-Bx1-20
b-Bx1-2340 : Circuit 5
b-Bx1-2340 = (CCZ ↑) • (Toff ↑) • b-Bx2-140 • (Toff ↑) • (CCZ ↑) • b-Bx2-140
b-Bx1-240 : Circuit 5
b-Bx1-240 = (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • b-Bx2-10 • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • b-Bx2-10
b-Bx2-103 : Circuit 5
b-Bx2-103 = CCZ • Toffᵗ • b-Bx1-23 • Toffᵗ • CCZ • b-Bx1-23
b-Bx1-2403 : Circuit 5
b-Bx1-2403 = (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • b-Bx2-103 • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • b-Bx2-103
b-Bx1-243 : Circuit 5
b-Bx1-243 = (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • b-Bx2-13 • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • b-Bx2-13
b-Bx2-130 : Circuit 5
b-Bx2-130 = (CCZ ↑) • ((K ↑ • CCZ • K ↑ • iI) ↑) • b-Bx1-20 • ((K ↑ • CCZ • K ↑ • iI) ↑) • (CCZ ↑) • b-Bx1-20
b-Bx1-2430 : Circuit 5
b-Bx1-2430 = (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • b-Bx2-130 • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • b-Bx2-130
b-Bx1-30 : Circuit 5
b-Bx1-30 = (Swap ↑ ↑ • (Swap ↑ • CZ • Swap ↑) • Swap ↑ ↑)
b-Bx3-12 : Circuit 5
b-Bx3-12 = (CZ ↑)
b-Bx1-302 : Circuit 5
b-Bx1-302 = (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • b-Bx3-12 • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • b-Bx3-12
b-Bx1-34 : Circuit 5
b-Bx1-34 = (CZ ↑ ↑ ↑)
b-Bx3-124 : Circuit 5
b-Bx3-124 = (CCZ ↑) • (Toffᵗ ↑) • b-Bx1-34 • (Toffᵗ ↑) • (CCZ ↑) • b-Bx1-34
b-Bx1-3024 : Circuit 5
b-Bx1-3024 = (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • b-Bx3-124 • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • b-Bx3-124
b-Bx3-14 : Circuit 5
b-Bx3-14 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (CZ ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx1-304 : Circuit 5
b-Bx1-304 = (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • b-Bx3-14 • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • b-Bx3-14
b-Bx1-32 : Circuit 5
b-Bx1-32 = (CZ ↑ ↑)
b-Bx3-142 : Circuit 5
b-Bx3-142 = (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx1-32 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx1-32
b-Bx1-3042 : Circuit 5
b-Bx1-3042 = (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • b-Bx3-142 • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • b-Bx3-142
b-Bx3-10 : Circuit 5
b-Bx3-10 = CZ
b-Bx1-320 : Circuit 5
b-Bx1-320 = (CCZ ↑) • (Toff ↑) • b-Bx3-10 • (Toff ↑) • (CCZ ↑) • b-Bx3-10
b-Bx3-104 : Circuit 5
b-Bx3-104 = (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • b-Bx1-34 • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • b-Bx1-34
b-Bx1-3204 : Circuit 5
b-Bx1-3204 = (CCZ ↑) • (Toff ↑) • b-Bx3-104 • (Toff ↑) • (CCZ ↑) • b-Bx3-104
b-Bx1-324 : Circuit 5
b-Bx1-324 = (CCZ ↑) • (Toff ↑) • b-Bx3-14 • (Toff ↑) • (CCZ ↑) • b-Bx3-14
b-Bx3-140 : Circuit 5
b-Bx3-140 = (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx1-30 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx1-30
b-Bx1-3240 : Circuit 5
b-Bx1-3240 = (CCZ ↑) • (Toff ↑) • b-Bx3-140 • (Toff ↑) • (CCZ ↑) • b-Bx3-140
b-Bx1-340 : Circuit 5
b-Bx1-340 = (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx3-10 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx3-10
b-Bx3-102 : Circuit 5
b-Bx3-102 = (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • b-Bx1-32 • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • b-Bx1-32
b-Bx1-3402 : Circuit 5
b-Bx1-3402 = (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx3-102 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx3-102
b-Bx1-342 : Circuit 5
b-Bx1-342 = (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx3-12 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx3-12
b-Bx3-120 : Circuit 5
b-Bx3-120 = (CCZ ↑) • (Toffᵗ ↑) • b-Bx1-30 • (Toffᵗ ↑) • (CCZ ↑) • b-Bx1-30
b-Bx1-3420 : Circuit 5
b-Bx1-3420 = (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx3-120 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx3-120
b-Bx1-40 : Circuit 5
b-Bx1-40 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • CZ • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx4-12 : Circuit 5
b-Bx4-12 = (CZ ↑)
b-Bx1-402 : Circuit 5
b-Bx1-402 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx4-12 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx4-12
b-Bx1-43 : Circuit 5
b-Bx1-43 = (CZ ↑ ↑ ↑)
b-Bx4-123 : Circuit 5
b-Bx4-123 = (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • b-Bx1-43 • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • b-Bx1-43
b-Bx1-4023 : Circuit 5
b-Bx1-4023 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx4-123 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx4-123
b-Bx4-13 : Circuit 5
b-Bx4-13 = (Swap ↑ ↑ • (CZ ↑) • Swap ↑ ↑)
b-Bx1-403 : Circuit 5
b-Bx1-403 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx4-13 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx4-13
b-Bx1-42 : Circuit 5
b-Bx1-42 = (Swap ↑ ↑ ↑ • (CZ ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx4-132 : Circuit 5
b-Bx4-132 = (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx1-42 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx1-42
b-Bx1-4032 : Circuit 5
b-Bx1-4032 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx4-132 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx4-132
b-Bx4-10 : Circuit 5
b-Bx4-10 = CZ
b-Bx1-420 : Circuit 5
b-Bx1-420 = (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • b-Bx4-10 • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • b-Bx4-10
b-Bx4-103 : Circuit 5
b-Bx4-103 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx1-43 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx1-43
b-Bx1-4203 : Circuit 5
b-Bx1-4203 = (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • b-Bx4-103 • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • b-Bx4-103
b-Bx1-423 : Circuit 5
b-Bx1-423 = (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • b-Bx4-13 • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • b-Bx4-13
b-Bx4-130 : Circuit 5
b-Bx4-130 = (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx1-40 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx1-40
b-Bx1-4230 : Circuit 5
b-Bx1-4230 = (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • b-Bx4-130 • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • b-Bx4-130
b-Bx1-430 : Circuit 5
b-Bx1-430 = (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx4-10 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx4-10
b-Bx4-102 : Circuit 5
b-Bx4-102 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx1-42 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx1-42
b-Bx1-4302 : Circuit 5
b-Bx1-4302 = (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx4-102 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx4-102
b-Bx1-432 : Circuit 5
b-Bx1-432 = (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx4-12 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx4-12
b-Bx4-120 : Circuit 5
b-Bx4-120 = (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • b-Bx1-40 • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • b-Bx1-40
b-Bx1-4320 : Circuit 5
b-Bx1-4320 = (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx4-120 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx4-120
b-Bx2-0134 : Circuit 5
b-Bx2-0134 = CCZ • Toffᵗ • b-Bx0-234 • Toffᵗ • CCZ • b-Bx0-234
b-Bx2-0143 : Circuit 5
b-Bx2-0143 = CCZ • Toffᵗ • b-Bx0-243 • Toffᵗ • CCZ • b-Bx0-243
b-Bx2-0314 : Circuit 5
b-Bx2-0314 = (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) • b-Bx0-214 • (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • b-Bx0-214
b-Bx2-0341 : Circuit 5
b-Bx2-0341 = (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) • b-Bx0-241 • (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • b-Bx0-241
b-Bx2-0413 : Circuit 5
b-Bx2-0413 = (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx0-213 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx0-213
b-Bx2-0431 : Circuit 5
b-Bx2-0431 = (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx0-231 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx0-231
b-Bx2-1034 : Circuit 5
b-Bx2-1034 = CCZ • Toffᵗ • b-Bx1-234 • Toffᵗ • CCZ • b-Bx1-234
b-Bx2-1043 : Circuit 5
b-Bx2-1043 = CCZ • Toffᵗ • b-Bx1-243 • Toffᵗ • CCZ • b-Bx1-243
b-Bx2-1304 : Circuit 5
b-Bx2-1304 = (CCZ ↑) • ((K ↑ • CCZ • K ↑ • iI) ↑) • b-Bx1-204 • ((K ↑ • CCZ • K ↑ • iI) ↑) • (CCZ ↑) • b-Bx1-204
b-Bx2-1340 : Circuit 5
b-Bx2-1340 = (CCZ ↑) • ((K ↑ • CCZ • K ↑ • iI) ↑) • b-Bx1-240 • ((K ↑ • CCZ • K ↑ • iI) ↑) • (CCZ ↑) • b-Bx1-240
b-Bx2-1403 : Circuit 5
b-Bx2-1403 = (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • b-Bx1-203 • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • b-Bx1-203
b-Bx2-1430 : Circuit 5
b-Bx2-1430 = (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • b-Bx1-230 • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • b-Bx1-230
b-Bx2-30 : Circuit 5
b-Bx2-30 = (Swap ↑ ↑ • (Swap ↑ • CZ • Swap ↑) • Swap ↑ ↑)
b-Bx3-21 : Circuit 5
b-Bx3-21 = (CZ ↑)
b-Bx2-301 : Circuit 5
b-Bx2-301 = (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) • b-Bx3-21 • (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • b-Bx3-21
b-Bx2-34 : Circuit 5
b-Bx2-34 = (CZ ↑ ↑ ↑)
b-Bx3-214 : Circuit 5
b-Bx3-214 = (CCZ ↑) • (Toffᵗ ↑) • b-Bx2-34 • (Toffᵗ ↑) • (CCZ ↑) • b-Bx2-34
b-Bx2-3014 : Circuit 5
b-Bx2-3014 = (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) • b-Bx3-214 • (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • b-Bx3-214
b-Bx3-24 : Circuit 5
b-Bx3-24 = (Swap ↑ ↑ ↑ • (CZ ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx2-304 : Circuit 5
b-Bx2-304 = (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) • b-Bx3-24 • (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • b-Bx3-24
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
b-Bx3-204 : Circuit 5
b-Bx3-204 = (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) • b-Bx2-34 • (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • b-Bx2-34
b-Bx2-3104 : Circuit 5
b-Bx2-3104 = (CCZ ↑) • ((K ↑ • CCZ • K ↑ • iI) ↑) • b-Bx3-204 • ((K ↑ • CCZ • K ↑ • iI) ↑) • (CCZ ↑) • b-Bx3-204
b-Bx2-314 : Circuit 5
b-Bx2-314 = (CCZ ↑) • ((K ↑ • CCZ • K ↑ • iI) ↑) • b-Bx3-24 • ((K ↑ • CCZ • K ↑ • iI) ↑) • (CCZ ↑) • b-Bx3-24
b-Bx3-240 : Circuit 5
b-Bx3-240 = (CCZ ↑ ↑) • ((K ↑ • CCZ • K ↑ • iI) ↑ ↑) • b-Bx2-30 • ((K ↑ • CCZ • K ↑ • iI) ↑ ↑) • (CCZ ↑ ↑) • b-Bx2-30
b-Bx2-3140 : Circuit 5
b-Bx2-3140 = (CCZ ↑) • ((K ↑ • CCZ • K ↑ • iI) ↑) • b-Bx3-240 • ((K ↑ • CCZ • K ↑ • iI) ↑) • (CCZ ↑) • b-Bx3-240
b-Bx2-340 : Circuit 5
b-Bx2-340 = (CCZ ↑ ↑) • (Toff ↑ ↑) • b-Bx3-20 • (Toff ↑ ↑) • (CCZ ↑ ↑) • b-Bx3-20
b-Bx3-201 : Circuit 5
b-Bx3-201 = (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) • b-Bx2-31 • (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • b-Bx2-31
b-Bx2-3401 : Circuit 5
b-Bx2-3401 = (CCZ ↑ ↑) • (Toff ↑ ↑) • b-Bx3-201 • (Toff ↑ ↑) • (CCZ ↑ ↑) • b-Bx3-201
b-Bx2-341 : Circuit 5
b-Bx2-341 = (CCZ ↑ ↑) • (Toff ↑ ↑) • b-Bx3-21 • (Toff ↑ ↑) • (CCZ ↑ ↑) • b-Bx3-21
b-Bx3-210 : Circuit 5
b-Bx3-210 = (CCZ ↑) • (Toffᵗ ↑) • b-Bx2-30 • (Toffᵗ ↑) • (CCZ ↑) • b-Bx2-30
b-Bx2-3410 : Circuit 5
b-Bx2-3410 = (CCZ ↑ ↑) • (Toff ↑ ↑) • b-Bx3-210 • (Toff ↑ ↑) • (CCZ ↑ ↑) • b-Bx3-210
b-Bx2-40 : Circuit 5
b-Bx2-40 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • CZ • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx4-21 : Circuit 5
b-Bx4-21 = (CZ ↑)
b-Bx2-401 : Circuit 5
b-Bx2-401 = (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx4-21 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx4-21
b-Bx2-43 : Circuit 5
b-Bx2-43 = (CZ ↑ ↑ ↑)
b-Bx4-213 : Circuit 5
b-Bx4-213 = (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • b-Bx2-43 • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • b-Bx2-43
b-Bx2-4013 : Circuit 5
b-Bx2-4013 = (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx4-213 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx4-213
b-Bx4-23 : Circuit 5
b-Bx4-23 = (CZ ↑ ↑)
b-Bx2-403 : Circuit 5
b-Bx2-403 = (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx4-23 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx4-23
b-Bx2-41 : Circuit 5
b-Bx2-41 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (CZ ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx4-231 : Circuit 5
b-Bx4-231 = (CCZ ↑ ↑) • (Toffᵗ ↑ ↑) • b-Bx2-41 • (Toffᵗ ↑ ↑) • (CCZ ↑ ↑) • b-Bx2-41
b-Bx2-4031 : Circuit 5
b-Bx2-4031 = (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx4-231 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx4-231
b-Bx4-20 : Circuit 5
b-Bx4-20 = (Swap ↑ • CZ • Swap ↑)
b-Bx2-410 : Circuit 5
b-Bx2-410 = (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • b-Bx4-20 • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • b-Bx4-20
b-Bx4-203 : Circuit 5
b-Bx4-203 = (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx2-43 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx2-43
b-Bx2-4103 : Circuit 5
b-Bx2-4103 = (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • b-Bx4-203 • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • b-Bx4-203
b-Bx2-413 : Circuit 5
b-Bx2-413 = (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • b-Bx4-23 • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • b-Bx4-23
b-Bx4-230 : Circuit 5
b-Bx4-230 = (CCZ ↑ ↑) • (Toffᵗ ↑ ↑) • b-Bx2-40 • (Toffᵗ ↑ ↑) • (CCZ ↑ ↑) • b-Bx2-40
b-Bx2-4130 : Circuit 5
b-Bx2-4130 = (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • b-Bx4-230 • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • b-Bx4-230
b-Bx2-430 : Circuit 5
b-Bx2-430 = (CCZ ↑ ↑) • (Toff ↑ ↑) • b-Bx4-20 • (Toff ↑ ↑) • (CCZ ↑ ↑) • b-Bx4-20
b-Bx4-201 : Circuit 5
b-Bx4-201 = (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx2-41 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx2-41
b-Bx2-4301 : Circuit 5
b-Bx2-4301 = (CCZ ↑ ↑) • (Toff ↑ ↑) • b-Bx4-201 • (Toff ↑ ↑) • (CCZ ↑ ↑) • b-Bx4-201
b-Bx2-431 : Circuit 5
b-Bx2-431 = (CCZ ↑ ↑) • (Toff ↑ ↑) • b-Bx4-21 • (Toff ↑ ↑) • (CCZ ↑ ↑) • b-Bx4-21
b-Bx4-210 : Circuit 5
b-Bx4-210 = (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • b-Bx2-40 • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • b-Bx2-40
b-Bx2-4310 : Circuit 5
b-Bx2-4310 = (CCZ ↑ ↑) • (Toff ↑ ↑) • b-Bx4-210 • (Toff ↑ ↑) • (CCZ ↑ ↑) • b-Bx4-210
b-Bx3-0124 : Circuit 5
b-Bx3-0124 = (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • b-Bx0-324 • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • b-Bx0-324
b-Bx3-0142 : Circuit 5
b-Bx3-0142 = (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • b-Bx0-342 • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • b-Bx0-342
b-Bx3-0214 : Circuit 5
b-Bx3-0214 = (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) • b-Bx0-314 • (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • b-Bx0-314
b-Bx3-0241 : Circuit 5
b-Bx3-0241 = (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) • b-Bx0-341 • (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • b-Bx0-341
b-Bx3-0412 : Circuit 5
b-Bx3-0412 = (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx0-312 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx0-312
b-Bx3-0421 : Circuit 5
b-Bx3-0421 = (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx0-321 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx0-321
b-Bx3-1024 : Circuit 5
b-Bx3-1024 = (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • b-Bx1-324 • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • b-Bx1-324
b-Bx3-1042 : Circuit 5
b-Bx3-1042 = (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • b-Bx1-342 • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • b-Bx1-342
b-Bx3-1204 : Circuit 5
b-Bx3-1204 = (CCZ ↑) • (Toffᵗ ↑) • b-Bx1-304 • (Toffᵗ ↑) • (CCZ ↑) • b-Bx1-304
b-Bx3-1240 : Circuit 5
b-Bx3-1240 = (CCZ ↑) • (Toffᵗ ↑) • b-Bx1-340 • (Toffᵗ ↑) • (CCZ ↑) • b-Bx1-340
b-Bx3-1402 : Circuit 5
b-Bx3-1402 = (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx1-302 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx1-302
b-Bx3-1420 : Circuit 5
b-Bx3-1420 = (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx1-320 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx1-320
b-Bx3-2014 : Circuit 5
b-Bx3-2014 = (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) • b-Bx2-314 • (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • b-Bx2-314
b-Bx3-2041 : Circuit 5
b-Bx3-2041 = (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) • b-Bx2-341 • (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • b-Bx2-341
b-Bx3-2104 : Circuit 5
b-Bx3-2104 = (CCZ ↑) • (Toffᵗ ↑) • b-Bx2-304 • (Toffᵗ ↑) • (CCZ ↑) • b-Bx2-304
b-Bx3-2140 : Circuit 5
b-Bx3-2140 = (CCZ ↑) • (Toffᵗ ↑) • b-Bx2-340 • (Toffᵗ ↑) • (CCZ ↑) • b-Bx2-340
b-Bx3-2401 : Circuit 5
b-Bx3-2401 = (CCZ ↑ ↑) • ((K ↑ • CCZ • K ↑ • iI) ↑ ↑) • b-Bx2-301 • ((K ↑ • CCZ • K ↑ • iI) ↑ ↑) • (CCZ ↑ ↑) • b-Bx2-301
b-Bx3-2410 : Circuit 5
b-Bx3-2410 = (CCZ ↑ ↑) • ((K ↑ • CCZ • K ↑ • iI) ↑ ↑) • b-Bx2-310 • ((K ↑ • CCZ • K ↑ • iI) ↑ ↑) • (CCZ ↑ ↑) • b-Bx2-310
b-Bx3-40 : Circuit 5
b-Bx3-40 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • CZ • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx3-42 : Circuit 5
b-Bx3-42 = (Swap ↑ ↑ ↑ • (CZ ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx4-312 : Circuit 5
b-Bx4-312 = (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx3-42 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx3-42
b-Bx3-4012 : Circuit 5
b-Bx3-4012 = (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx4-312 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx4-312
b-Bx4-32 : Circuit 5
b-Bx4-32 = (CZ ↑ ↑)
b-Bx3-402 : Circuit 5
b-Bx3-402 = (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx4-32 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx4-32
b-Bx3-41 : Circuit 5
b-Bx3-41 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (CZ ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx4-321 : Circuit 5
b-Bx4-321 = (CCZ ↑ ↑) • (Toffᵗ ↑ ↑) • b-Bx3-41 • (Toffᵗ ↑ ↑) • (CCZ ↑ ↑) • b-Bx3-41
b-Bx3-4021 : Circuit 5
b-Bx3-4021 = (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx4-321 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx4-321
b-Bx4-302 : Circuit 5
b-Bx4-302 = (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx3-42 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx3-42
b-Bx3-4102 : Circuit 5
b-Bx3-4102 = (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx4-302 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx4-302
b-Bx3-412 : Circuit 5
b-Bx3-412 = (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx4-32 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx4-32
b-Bx4-320 : Circuit 5
b-Bx4-320 = (CCZ ↑ ↑) • (Toffᵗ ↑ ↑) • b-Bx3-40 • (Toffᵗ ↑ ↑) • (CCZ ↑ ↑) • b-Bx3-40
b-Bx3-4120 : Circuit 5
b-Bx3-4120 = (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx4-320 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx4-320
b-Bx4-30 : Circuit 5
b-Bx4-30 = (Swap ↑ ↑ • (Swap ↑ • CZ • Swap ↑) • Swap ↑ ↑)
b-Bx3-420 : Circuit 5
b-Bx3-420 = (CCZ ↑ ↑) • ((K ↑ • CCZ • K ↑ • iI) ↑ ↑) • b-Bx4-30 • ((K ↑ • CCZ • K ↑ • iI) ↑ ↑) • (CCZ ↑ ↑) • b-Bx4-30
b-Bx4-301 : Circuit 5
b-Bx4-301 = (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx3-41 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx3-41
b-Bx3-4201 : Circuit 5
b-Bx3-4201 = (CCZ ↑ ↑) • ((K ↑ • CCZ • K ↑ • iI) ↑ ↑) • b-Bx4-301 • ((K ↑ • CCZ • K ↑ • iI) ↑ ↑) • (CCZ ↑ ↑) • b-Bx4-301
b-Bx4-31 : Circuit 5
b-Bx4-31 = (Swap ↑ ↑ • (CZ ↑) • Swap ↑ ↑)
b-Bx3-421 : Circuit 5
b-Bx3-421 = (CCZ ↑ ↑) • ((K ↑ • CCZ • K ↑ • iI) ↑ ↑) • b-Bx4-31 • ((K ↑ • CCZ • K ↑ • iI) ↑ ↑) • (CCZ ↑ ↑) • b-Bx4-31
b-Bx4-310 : Circuit 5
b-Bx4-310 = (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx3-40 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx3-40
b-Bx3-4210 : Circuit 5
b-Bx3-4210 = (CCZ ↑ ↑) • ((K ↑ • CCZ • K ↑ • iI) ↑ ↑) • b-Bx4-310 • ((K ↑ • CCZ • K ↑ • iI) ↑ ↑) • (CCZ ↑ ↑) • b-Bx4-310
b-Bx4-0123 : Circuit 5
b-Bx4-0123 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx0-423 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx0-423
b-Bx4-0132 : Circuit 5
b-Bx4-0132 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx0-432 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx0-432
b-Bx4-0213 : Circuit 5
b-Bx4-0213 = (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx0-413 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx0-413
b-Bx4-0231 : Circuit 5
b-Bx4-0231 = (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx0-431 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx0-431
b-Bx4-0312 : Circuit 5
b-Bx4-0312 = (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx0-412 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx0-412
b-Bx4-0321 : Circuit 5
b-Bx4-0321 = (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx0-421 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx0-421
b-Bx4-1023 : Circuit 5
b-Bx4-1023 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx1-423 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx1-423
b-Bx4-1032 : Circuit 5
b-Bx4-1032 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx1-432 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx1-432
b-Bx4-1203 : Circuit 5
b-Bx4-1203 = (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • b-Bx1-403 • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • b-Bx1-403
b-Bx4-1230 : Circuit 5
b-Bx4-1230 = (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • b-Bx1-430 • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • b-Bx1-430
b-Bx4-1302 : Circuit 5
b-Bx4-1302 = (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx1-402 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx1-402
b-Bx4-1320 : Circuit 5
b-Bx4-1320 = (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx1-420 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx1-420
b-Bx4-2013 : Circuit 5
b-Bx4-2013 = (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx2-413 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx2-413
b-Bx4-2031 : Circuit 5
b-Bx4-2031 = (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx2-431 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx2-431
b-Bx4-2103 : Circuit 5
b-Bx4-2103 = (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • b-Bx2-403 • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • b-Bx2-403
b-Bx4-2130 : Circuit 5
b-Bx4-2130 = (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • b-Bx2-430 • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • b-Bx2-430
b-Bx4-2301 : Circuit 5
b-Bx4-2301 = (CCZ ↑ ↑) • (Toffᵗ ↑ ↑) • b-Bx2-401 • (Toffᵗ ↑ ↑) • (CCZ ↑ ↑) • b-Bx2-401
b-Bx4-2310 : Circuit 5
b-Bx4-2310 = (CCZ ↑ ↑) • (Toffᵗ ↑ ↑) • b-Bx2-410 • (Toffᵗ ↑ ↑) • (CCZ ↑ ↑) • b-Bx2-410
b-Bx4-3012 : Circuit 5
b-Bx4-3012 = (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx3-412 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx3-412
b-Bx4-3021 : Circuit 5
b-Bx4-3021 = (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx3-421 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx3-421
b-Bx4-3102 : Circuit 5
b-Bx4-3102 = (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx3-402 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx3-402
b-Bx4-3120 : Circuit 5
b-Bx4-3120 = (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx3-420 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx3-420
b-Bx⁻0-12 : Circuit 5
b-Bx⁻0-12 = (CZ ↑)
b-Bx⁻1-03 : Circuit 5
b-Bx⁻1-03 = (Swap ↑ ↑ • (Swap ↑ • CZ • Swap ↑) • Swap ↑ ↑)
b-Bx⁻0-123 : Circuit 5
b-Bx⁻0-123 = b-Bx⁻1-03 • CCZ • Toff • b-Bx⁻1-03 • Toff • CCZ
b-Bx⁻0-14 : Circuit 5
b-Bx⁻0-14 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (CZ ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx⁻1-034 : Circuit 5
b-Bx⁻1-034 = b-Bx⁻0-14 • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • b-Bx⁻0-14 • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑)
b-Bx⁻0-1234 : Circuit 5
b-Bx⁻0-1234 = b-Bx⁻1-034 • CCZ • Toff • b-Bx⁻1-034 • Toff • CCZ
b-Bx⁻1-04 : Circuit 5
b-Bx⁻1-04 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • CZ • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx⁻0-124 : Circuit 5
b-Bx⁻0-124 = b-Bx⁻1-04 • CCZ • Toff • b-Bx⁻1-04 • Toff • CCZ
b-Bx⁻0-13 : Circuit 5
b-Bx⁻0-13 = (Swap ↑ ↑ • (CZ ↑) • Swap ↑ ↑)
b-Bx⁻1-043 : Circuit 5
b-Bx⁻1-043 = b-Bx⁻0-13 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx⁻0-13 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx⁻0-1243 : Circuit 5
b-Bx⁻0-1243 = b-Bx⁻1-043 • CCZ • Toff • b-Bx⁻1-043 • Toff • CCZ
b-Bx⁻1-02 : Circuit 5
b-Bx⁻1-02 = (Swap ↑ • CZ • Swap ↑)
b-Bx⁻0-132 : Circuit 5
b-Bx⁻0-132 = b-Bx⁻1-02 • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • b-Bx⁻1-02 • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑)
b-Bx⁻1-024 : Circuit 5
b-Bx⁻1-024 = b-Bx⁻0-14 • CCZ • (K ↑ • CCZ • K ↑ • iI) • b-Bx⁻0-14 • (K ↑ • CCZ • K ↑ • iI) • CCZ
b-Bx⁻0-1324 : Circuit 5
b-Bx⁻0-1324 = b-Bx⁻1-024 • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • b-Bx⁻1-024 • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑)
b-Bx⁻0-134 : Circuit 5
b-Bx⁻0-134 = b-Bx⁻1-04 • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • b-Bx⁻1-04 • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑)
b-Bx⁻1-042 : Circuit 5
b-Bx⁻1-042 = b-Bx⁻0-12 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx⁻0-12 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx⁻0-1342 : Circuit 5
b-Bx⁻0-1342 = b-Bx⁻1-042 • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • b-Bx⁻1-042 • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑)
b-Bx⁻0-142 : Circuit 5
b-Bx⁻0-142 = b-Bx⁻1-02 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx⁻1-02 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx⁻1-023 : Circuit 5
b-Bx⁻1-023 = b-Bx⁻0-13 • CCZ • (K ↑ • CCZ • K ↑ • iI) • b-Bx⁻0-13 • (K ↑ • CCZ • K ↑ • iI) • CCZ
b-Bx⁻0-1423 : Circuit 5
b-Bx⁻0-1423 = b-Bx⁻1-023 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx⁻1-023 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx⁻0-143 : Circuit 5
b-Bx⁻0-143 = b-Bx⁻1-03 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx⁻1-03 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx⁻1-032 : Circuit 5
b-Bx⁻1-032 = b-Bx⁻0-12 • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • b-Bx⁻0-12 • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑)
b-Bx⁻0-1432 : Circuit 5
b-Bx⁻0-1432 = b-Bx⁻1-032 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx⁻1-032 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx⁻0-21 : Circuit 5
b-Bx⁻0-21 = (CZ ↑)
b-Bx⁻2-03 : Circuit 5
b-Bx⁻2-03 = (Swap ↑ ↑ • (Swap ↑ • CZ • Swap ↑) • Swap ↑ ↑)
b-Bx⁻0-213 : Circuit 5
b-Bx⁻0-213 = b-Bx⁻2-03 • CCZ • Toff • b-Bx⁻2-03 • Toff • CCZ
b-Bx⁻0-24 : Circuit 5
b-Bx⁻0-24 = (Swap ↑ ↑ ↑ • (CZ ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx⁻2-034 : Circuit 5
b-Bx⁻2-034 = b-Bx⁻0-24 • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) • b-Bx⁻0-24 • (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)
b-Bx⁻0-2134 : Circuit 5
b-Bx⁻0-2134 = b-Bx⁻2-034 • CCZ • Toff • b-Bx⁻2-034 • Toff • CCZ
b-Bx⁻2-04 : Circuit 5
b-Bx⁻2-04 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • CZ • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx⁻0-214 : Circuit 5
b-Bx⁻0-214 = b-Bx⁻2-04 • CCZ • Toff • b-Bx⁻2-04 • Toff • CCZ
b-Bx⁻2-01 : Circuit 5
b-Bx⁻2-01 = CZ
b-Bx⁻0-231 : Circuit 5
b-Bx⁻0-231 = b-Bx⁻2-01 • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • b-Bx⁻2-01 • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)
b-Bx⁻0-234 : Circuit 5
b-Bx⁻0-234 = b-Bx⁻2-04 • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • b-Bx⁻2-04 • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)
b-Bx⁻2-041 : Circuit 5
b-Bx⁻2-041 = b-Bx⁻0-21 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx⁻0-21 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑)
b-Bx⁻0-2341 : Circuit 5
b-Bx⁻0-2341 = b-Bx⁻2-041 • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • b-Bx⁻2-041 • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)
b-Bx⁻0-241 : Circuit 5
b-Bx⁻0-241 = b-Bx⁻2-01 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx⁻2-01 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑)
b-Bx⁻0-243 : Circuit 5
b-Bx⁻0-243 = b-Bx⁻2-03 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx⁻2-03 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑)
b-Bx⁻2-031 : Circuit 5
b-Bx⁻2-031 = b-Bx⁻0-21 • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) • b-Bx⁻0-21 • (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)
b-Bx⁻0-2431 : Circuit 5
b-Bx⁻0-2431 = b-Bx⁻2-031 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx⁻2-031 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑)
b-Bx⁻3-02 : Circuit 5
b-Bx⁻3-02 = (Swap ↑ • CZ • Swap ↑)
b-Bx⁻0-312 : Circuit 5
b-Bx⁻0-312 = b-Bx⁻3-02 • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • b-Bx⁻3-02 • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑)
b-Bx⁻0-34 : Circuit 5
b-Bx⁻0-34 = (CZ ↑ ↑ ↑)
b-Bx⁻3-024 : Circuit 5
b-Bx⁻3-024 = b-Bx⁻0-34 • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) • b-Bx⁻0-34 • (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)
b-Bx⁻0-3124 : Circuit 5
b-Bx⁻0-3124 = b-Bx⁻3-024 • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • b-Bx⁻3-024 • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑)
b-Bx⁻3-01 : Circuit 5
b-Bx⁻3-01 = CZ
b-Bx⁻0-321 : Circuit 5
b-Bx⁻0-321 = b-Bx⁻3-01 • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • b-Bx⁻3-01 • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)
b-Bx⁻3-04 : Circuit 5
b-Bx⁻3-04 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • CZ • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx⁻0-324 : Circuit 5
b-Bx⁻0-324 = b-Bx⁻3-04 • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • b-Bx⁻3-04 • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)
b-Bx⁻4-02 : Circuit 5
b-Bx⁻4-02 = (Swap ↑ • CZ • Swap ↑)
b-Bx⁻0-412 : Circuit 5
b-Bx⁻0-412 = b-Bx⁻4-02 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx⁻4-02 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx⁻0-43 : Circuit 5
b-Bx⁻0-43 = (CZ ↑ ↑ ↑)
b-Bx⁻4-023 : Circuit 5
b-Bx⁻4-023 = b-Bx⁻0-43 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx⁻0-43 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑)
b-Bx⁻0-4123 : Circuit 5
b-Bx⁻0-4123 = b-Bx⁻4-023 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx⁻4-023 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx⁻4-03 : Circuit 5
b-Bx⁻4-03 = (Swap ↑ ↑ • (Swap ↑ • CZ • Swap ↑) • Swap ↑ ↑)
b-Bx⁻0-413 : Circuit 5
b-Bx⁻0-413 = b-Bx⁻4-03 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx⁻4-03 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx⁻4-01 : Circuit 5
b-Bx⁻4-01 = CZ
b-Bx⁻0-421 : Circuit 5
b-Bx⁻0-421 = b-Bx⁻4-01 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx⁻4-01 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑)
b-Bx⁻0-423 : Circuit 5
b-Bx⁻0-423 = b-Bx⁻4-03 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx⁻4-03 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑)
b-Bx⁻0-431 : Circuit 5
b-Bx⁻0-431 = b-Bx⁻4-01 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx⁻4-01 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑)
b-Bx⁻0-432 : Circuit 5
b-Bx⁻0-432 = b-Bx⁻4-02 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx⁻4-02 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑)
b-Bx⁻1-0234 : Circuit 5
b-Bx⁻1-0234 = b-Bx⁻0-134 • CCZ • (K ↑ • CCZ • K ↑ • iI) • b-Bx⁻0-134 • (K ↑ • CCZ • K ↑ • iI) • CCZ
b-Bx⁻1-0243 : Circuit 5
b-Bx⁻1-0243 = b-Bx⁻0-143 • CCZ • (K ↑ • CCZ • K ↑ • iI) • b-Bx⁻0-143 • (K ↑ • CCZ • K ↑ • iI) • CCZ
b-Bx⁻1-0324 : Circuit 5
b-Bx⁻1-0324 = b-Bx⁻0-124 • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • b-Bx⁻0-124 • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑)
b-Bx⁻1-0342 : Circuit 5
b-Bx⁻1-0342 = b-Bx⁻0-142 • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • b-Bx⁻0-142 • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑)
b-Bx⁻1-0423 : Circuit 5
b-Bx⁻1-0423 = b-Bx⁻0-123 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx⁻0-123 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx⁻1-0432 : Circuit 5
b-Bx⁻1-0432 = b-Bx⁻0-132 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx⁻0-132 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx⁻1-20 : Circuit 5
b-Bx⁻1-20 = (Swap ↑ • CZ • Swap ↑)
b-Bx⁻2-13 : Circuit 5
b-Bx⁻2-13 = (Swap ↑ ↑ • (CZ ↑) • Swap ↑ ↑)
b-Bx⁻1-203 : Circuit 5
b-Bx⁻1-203 = b-Bx⁻2-13 • CCZ • (K ↑ • CCZ • K ↑ • iI) • b-Bx⁻2-13 • (K ↑ • CCZ • K ↑ • iI) • CCZ
b-Bx⁻1-24 : Circuit 5
b-Bx⁻1-24 = (Swap ↑ ↑ ↑ • (CZ ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx⁻2-134 : Circuit 5
b-Bx⁻2-134 = b-Bx⁻1-24 • (CCZ ↑) • ((K ↑ • CCZ • K ↑ • iI) ↑) • b-Bx⁻1-24 • ((K ↑ • CCZ • K ↑ • iI) ↑) • (CCZ ↑)
b-Bx⁻1-2034 : Circuit 5
b-Bx⁻1-2034 = b-Bx⁻2-134 • CCZ • (K ↑ • CCZ • K ↑ • iI) • b-Bx⁻2-134 • (K ↑ • CCZ • K ↑ • iI) • CCZ
b-Bx⁻1-23 : Circuit 5
b-Bx⁻1-23 = (CZ ↑ ↑)
b-Bx⁻2-140 : Circuit 5
b-Bx⁻2-140 = b-Bx⁻1-20 • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • b-Bx⁻1-20 • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑)
b-Bx⁻1-2340 : Circuit 5
b-Bx⁻1-2340 = b-Bx⁻2-140 • (CCZ ↑) • (Toff ↑) • b-Bx⁻2-140 • (Toff ↑) • (CCZ ↑)
b-Bx⁻2-10 : Circuit 5
b-Bx⁻2-10 = CZ
b-Bx⁻1-240 : Circuit 5
b-Bx⁻1-240 = b-Bx⁻2-10 • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • b-Bx⁻2-10 • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑)
b-Bx⁻2-103 : Circuit 5
b-Bx⁻2-103 = b-Bx⁻1-23 • CCZ • Toffᵗ • b-Bx⁻1-23 • Toffᵗ • CCZ
b-Bx⁻1-2403 : Circuit 5
b-Bx⁻1-2403 = b-Bx⁻2-103 • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • b-Bx⁻2-103 • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑)
b-Bx⁻1-34 : Circuit 5
b-Bx⁻1-34 = (CZ ↑ ↑ ↑)
b-Bx⁻3-124 : Circuit 5
b-Bx⁻3-124 = b-Bx⁻1-34 • (CCZ ↑) • (Toffᵗ ↑) • b-Bx⁻1-34 • (Toffᵗ ↑) • (CCZ ↑)
b-Bx⁻1-3024 : Circuit 5
b-Bx⁻1-3024 = b-Bx⁻3-124 • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • b-Bx⁻3-124 • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑)
b-Bx⁻1-32 : Circuit 5
b-Bx⁻1-32 = (CZ ↑ ↑)
b-Bx⁻3-102 : Circuit 5
b-Bx⁻3-102 = b-Bx⁻1-32 • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • b-Bx⁻1-32 • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑)
b-Bx⁻1-3402 : Circuit 5
b-Bx⁻1-3402 = b-Bx⁻3-102 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx⁻3-102 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑)
b-Bx⁻1-43 : Circuit 5
b-Bx⁻1-43 = (CZ ↑ ↑ ↑)
b-Bx⁻4-123 : Circuit 5
b-Bx⁻4-123 = b-Bx⁻1-43 • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • b-Bx⁻1-43 • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑)
b-Bx⁻1-4023 : Circuit 5
b-Bx⁻1-4023 = b-Bx⁻4-123 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx⁻4-123 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx⁻1-42 : Circuit 5
b-Bx⁻1-42 = (Swap ↑ ↑ ↑ • (CZ ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx⁻4-10 : Circuit 5
b-Bx⁻4-10 = CZ
b-Bx⁻1-420 : Circuit 5
b-Bx⁻1-420 = b-Bx⁻4-10 • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • b-Bx⁻4-10 • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑)
b-Bx⁻4-103 : Circuit 5
b-Bx⁻4-103 = b-Bx⁻1-43 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx⁻1-43 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx⁻1-4203 : Circuit 5
b-Bx⁻1-4203 = b-Bx⁻4-103 • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • b-Bx⁻4-103 • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑)
b-Bx⁻1-430 : Circuit 5
b-Bx⁻1-430 = b-Bx⁻4-10 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx⁻4-10 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑)
b-Bx⁻4-102 : Circuit 5
b-Bx⁻4-102 = b-Bx⁻1-42 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx⁻1-42 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx⁻1-4302 : Circuit 5
b-Bx⁻1-4302 = b-Bx⁻4-102 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx⁻4-102 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑)
b-Bx⁻2-0134 : Circuit 5
b-Bx⁻2-0134 = b-Bx⁻0-234 • CCZ • Toffᵗ • b-Bx⁻0-234 • Toffᵗ • CCZ
b-Bx⁻2-0143 : Circuit 5
b-Bx⁻2-0143 = b-Bx⁻0-243 • CCZ • Toffᵗ • b-Bx⁻0-243 • Toffᵗ • CCZ
b-Bx⁻2-0314 : Circuit 5
b-Bx⁻2-0314 = b-Bx⁻0-214 • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) • b-Bx⁻0-214 • (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)
b-Bx⁻2-0341 : Circuit 5
b-Bx⁻2-0341 = b-Bx⁻0-241 • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) • b-Bx⁻0-241 • (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)
b-Bx⁻2-0413 : Circuit 5
b-Bx⁻2-0413 = b-Bx⁻0-213 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx⁻0-213 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑)
b-Bx⁻2-0431 : Circuit 5
b-Bx⁻2-0431 = b-Bx⁻0-231 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx⁻0-231 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑)
b-Bx⁻2-1340 : Circuit 5
b-Bx⁻2-1340 = b-Bx⁻1-240 • (CCZ ↑) • ((K ↑ • CCZ • K ↑ • iI) ↑) • b-Bx⁻1-240 • ((K ↑ • CCZ • K ↑ • iI) ↑) • (CCZ ↑)
b-Bx⁻2-1403 : Circuit 5
b-Bx⁻2-1403 = b-Bx⁻1-203 • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • b-Bx⁻1-203 • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑)
b-Bx⁻2-34 : Circuit 5
b-Bx⁻2-34 = (CZ ↑ ↑ ↑)
b-Bx⁻3-214 : Circuit 5
b-Bx⁻3-214 = b-Bx⁻2-34 • (CCZ ↑) • (Toffᵗ ↑) • b-Bx⁻2-34 • (Toffᵗ ↑) • (CCZ ↑)
b-Bx⁻2-3014 : Circuit 5
b-Bx⁻2-3014 = b-Bx⁻3-214 • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) • b-Bx⁻3-214 • (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)
b-Bx⁻2-43 : Circuit 5
b-Bx⁻2-43 = (CZ ↑ ↑ ↑)
b-Bx⁻4-213 : Circuit 5
b-Bx⁻4-213 = b-Bx⁻2-43 • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • b-Bx⁻2-43 • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑)
b-Bx⁻2-4013 : Circuit 5
b-Bx⁻2-4013 = b-Bx⁻4-213 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx⁻4-213 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑)
b-Bx⁻4-203 : Circuit 5
b-Bx⁻4-203 = b-Bx⁻2-43 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx⁻2-43 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑)
b-Bx⁻2-4103 : Circuit 5
b-Bx⁻2-4103 = b-Bx⁻4-203 • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • b-Bx⁻4-203 • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑)
b-Bx⁻3-0124 : Circuit 5
b-Bx⁻3-0124 = b-Bx⁻0-324 • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • b-Bx⁻0-324 • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • (Swap ↑ ↑ • CCZ • Swap ↑ ↑)
b-Bx⁻3-0412 : Circuit 5
b-Bx⁻3-0412 = b-Bx⁻0-312 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx⁻0-312 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑)
b-Bx⁻3-0421 : Circuit 5
b-Bx⁻3-0421 = b-Bx⁻0-321 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx⁻0-321 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑)
b-Bx⁻4-0123 : Circuit 5
b-Bx⁻4-0123 = b-Bx⁻0-423 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx⁻0-423 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx⁻4-0132 : Circuit 5
b-Bx⁻4-0132 = b-Bx⁻0-432 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Bx⁻0-432 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Bx⁻4-0213 : Circuit 5
b-Bx⁻4-0213 = b-Bx⁻0-413 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx⁻0-413 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑)
b-Bx⁻4-0231 : Circuit 5
b-Bx⁻4-0231 = b-Bx⁻0-431 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx⁻0-431 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑)
b-Bx⁻4-0312 : Circuit 5
b-Bx⁻4-0312 = b-Bx⁻0-412 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx⁻0-412 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑)
b-Bx⁻4-0321 : Circuit 5
b-Bx⁻4-0321 = b-Bx⁻0-421 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx⁻0-421 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑)
b-Bx⁻4-1230 : Circuit 5
b-Bx⁻4-1230 = b-Bx⁻1-430 • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • b-Bx⁻1-430 • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑)
b-Bx⁻4-1320 : Circuit 5
b-Bx⁻4-1320 = b-Bx⁻1-420 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx⁻1-420 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (CCZ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑)
b-Sb0-1-2-3 : Circuit 5
b-Sb0-1-2-3 = (CS ↑)
b-Sb0-1-2-4 : Circuit 5
b-Sb0-1-2-4 = (CS ↑)
b-Sb0-1-4-3 : Circuit 5
b-Sb0-1-4-3 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb⁻0-1-4-3 : Circuit 5
b-Sb⁻0-1-4-3 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb0-1-23-4 : Circuit 5
b-Sb0-1-23-4 = b-Bx0-1234 • (Toffᵗ ↑ ↑) • b-Sb0-1-4-3 • (Toffᵗ ↑ ↑) • b-Sb⁻0-1-4-3
b-Sb0-1-3-2 : Circuit 5
b-Sb0-1-3-2 = (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑)
b-Sb0-1-3-4 : Circuit 5
b-Sb0-1-3-4 = (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑)
b-Sb0-1-4-2 : Circuit 5
b-Sb0-1-4-2 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb⁻0-1-4-2 : Circuit 5
b-Sb⁻0-1-4-2 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb0-1-32-4 : Circuit 5
b-Sb0-1-32-4 = b-Bx0-1324 • (Toffᵗ ↑ ↑) • b-Sb0-1-4-2 • (Toffᵗ ↑ ↑) • b-Sb⁻0-1-4-2
b-Sb⁻0-1-2-4 : Circuit 5
b-Sb⁻0-1-2-4 = ((CS • CS • CS) ↑)
b-Sb0-1-34-2 : Circuit 5
b-Sb0-1-34-2 = b-Bx0-1342 • (Toff ↑ ↑) • b-Sb0-1-2-4 • (Toff ↑ ↑) • b-Sb⁻0-1-2-4
b-Sb⁻0-1-3-2 : Circuit 5
b-Sb⁻0-1-3-2 = (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑)
b-Sb0-1-42-3 : Circuit 5
b-Sb0-1-42-3 = b-Bx0-1423 • ((K ↑ • CCZ • K ↑ • iI) ↑ ↑) • b-Sb0-1-3-2 • ((K ↑ • CCZ • K ↑ • iI) ↑ ↑) • b-Sb⁻0-1-3-2
b-Sb⁻0-1-2-3 : Circuit 5
b-Sb⁻0-1-2-3 = ((CS • CS • CS) ↑)
b-Sb0-1-43-2 : Circuit 5
b-Sb0-1-43-2 = b-Bx0-1432 • (Toff ↑ ↑) • b-Sb0-1-2-3 • (Toff ↑ ↑) • b-Sb⁻0-1-2-3
b-Sb0-2-1-3 : Circuit 5
b-Sb0-2-1-3 = (CS ↑)
b-Sb0-2-1-4 : Circuit 5
b-Sb0-2-1-4 = (CS ↑)
b-Sb0-2-4-3 : Circuit 5
b-Sb0-2-4-3 = (Swap ↑ ↑ ↑ • (CS ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb⁻0-2-4-3 : Circuit 5
b-Sb⁻0-2-4-3 = (Swap ↑ ↑ ↑ • ((CS • CS • CS) ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb0-2-13-4 : Circuit 5
b-Sb0-2-13-4 = b-Bx0-2134 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Sb0-2-4-3 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Sb⁻0-2-4-3
b-Sb0-2-3-1 : Circuit 5
b-Sb0-2-3-1 = (CS ↑ ↑)
b-Sb0-2-4-1 : Circuit 5
b-Sb0-2-4-1 = (Swap ↑ ↑ ↑ • (CS ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb⁻0-2-4-1 : Circuit 5
b-Sb⁻0-2-4-1 = (Swap ↑ ↑ ↑ • ((CS • CS • CS) ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb0-2-31-4 : Circuit 5
b-Sb0-2-31-4 = b-Bx0-2314 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Sb0-2-4-1 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Sb⁻0-2-4-1
b-Sb⁻0-2-1-4 : Circuit 5
b-Sb⁻0-2-1-4 = ((CS • CS • CS) ↑)
b-Sb0-2-34-1 : Circuit 5
b-Sb0-2-34-1 = b-Bx0-2341 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Sb0-2-1-4 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Sb⁻0-2-1-4
b-Sb⁻0-2-3-1 : Circuit 5
b-Sb⁻0-2-3-1 = ((CS • CS • CS) ↑ ↑)
b-Sb0-2-41-3 : Circuit 5
b-Sb0-2-41-3 = b-Bx0-2413 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Sb0-2-3-1 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Sb⁻0-2-3-1
b-Sb⁻0-2-1-3 : Circuit 5
b-Sb⁻0-2-1-3 = ((CS • CS • CS) ↑)
b-Sb0-2-43-1 : Circuit 5
b-Sb0-2-43-1 = b-Bx0-2431 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Sb0-2-1-3 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Sb⁻0-2-1-3
b-Sb0-3-1-2 : Circuit 5
b-Sb0-3-1-2 = (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑)
b-Sb0-3-1-4 : Circuit 5
b-Sb0-3-1-4 = (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑)
b-Sb0-3-4-2 : Circuit 5
b-Sb0-3-4-2 = (CS ↑ ↑ ↑)
b-Sb⁻0-3-4-2 : Circuit 5
b-Sb⁻0-3-4-2 = ((CS • CS • CS) ↑ ↑ ↑)
b-Sb0-3-12-4 : Circuit 5
b-Sb0-3-12-4 = b-Bx0-3124 • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • b-Sb0-3-4-2 • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • b-Sb⁻0-3-4-2
b-Sb0-3-2-4 : Circuit 5
b-Sb0-3-2-4 = (CS ↑ ↑)
b-Sb⁻0-3-2-4 : Circuit 5
b-Sb⁻0-3-2-4 = ((CS • CS • CS) ↑ ↑)
b-Sb0-3-14-2 : Circuit 5
b-Sb0-3-14-2 = b-Bx0-3142 • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • b-Sb0-3-2-4 • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • b-Sb⁻0-3-2-4
b-Sb0-3-2-1 : Circuit 5
b-Sb0-3-2-1 = (CS ↑ ↑)
b-Sb0-3-4-1 : Circuit 5
b-Sb0-3-4-1 = (CS ↑ ↑ ↑)
b-Sb⁻0-3-4-1 : Circuit 5
b-Sb⁻0-3-4-1 = ((CS • CS • CS) ↑ ↑ ↑)
b-Sb0-3-21-4 : Circuit 5
b-Sb0-3-21-4 = b-Bx0-3214 • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • b-Sb0-3-4-1 • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • b-Sb⁻0-3-4-1
b-Sb⁻0-3-1-4 : Circuit 5
b-Sb⁻0-3-1-4 = (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑)
b-Sb0-3-24-1 : Circuit 5
b-Sb0-3-24-1 = b-Bx0-3241 • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • b-Sb0-3-1-4 • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • b-Sb⁻0-3-1-4
b-Sb0-4-1-2 : Circuit 5
b-Sb0-4-1-2 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb0-4-1-3 : Circuit 5
b-Sb0-4-1-3 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb0-4-3-2 : Circuit 5
b-Sb0-4-3-2 = (CS ↑ ↑ ↑)
b-Sb⁻0-4-3-2 : Circuit 5
b-Sb⁻0-4-3-2 = ((CS • CS • CS) ↑ ↑ ↑)
b-Sb0-4-12-3 : Circuit 5
b-Sb0-4-12-3 = b-Bx0-4123 • (Toffᵗ ↑) • b-Sb0-4-3-2 • (Toffᵗ ↑) • b-Sb⁻0-4-3-2
b-Sb0-4-2-1 : Circuit 5
b-Sb0-4-2-1 = (Swap ↑ ↑ ↑ • (CS ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb0-4-3-1 : Circuit 5
b-Sb0-4-3-1 = (CS ↑ ↑ ↑)
b-Sb⁻0-4-3-1 : Circuit 5
b-Sb⁻0-4-3-1 = ((CS • CS • CS) ↑ ↑ ↑)
b-Sb0-4-21-3 : Circuit 5
b-Sb0-4-21-3 = b-Bx0-4213 • (Toffᵗ ↑) • b-Sb0-4-3-1 • (Toffᵗ ↑) • b-Sb⁻0-4-3-1
b-Sb1-0-2-3 : Circuit 5
b-Sb1-0-2-3 = (Swap ↑ • CS • Swap ↑)
b-Sb1-0-2-4 : Circuit 5
b-Sb1-0-2-4 = (Swap ↑ • CS • Swap ↑)
b-Sb1-0-4-3 : Circuit 5
b-Sb1-0-4-3 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • CS • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb⁻1-0-4-3 : Circuit 5
b-Sb⁻1-0-4-3 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb1-0-23-4 : Circuit 5
b-Sb1-0-23-4 = b-Bx1-0234 • (Toffᵗ ↑ ↑) • b-Sb1-0-4-3 • (Toffᵗ ↑ ↑) • b-Sb⁻1-0-4-3
b-Sb1-0-3-4 : Circuit 5
b-Sb1-0-3-4 = (Swap ↑ ↑ • (Swap ↑ • CS • Swap ↑) • Swap ↑ ↑)
b-Sb⁻1-0-3-4 : Circuit 5
b-Sb⁻1-0-3-4 = (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑)
b-Sb1-0-24-3 : Circuit 5
b-Sb1-0-24-3 = b-Bx1-0243 • ((K ↑ • CCZ • K ↑ • iI) ↑ ↑) • b-Sb1-0-3-4 • ((K ↑ • CCZ • K ↑ • iI) ↑ ↑) • b-Sb⁻1-0-3-4
b-Sb1-0-3-2 : Circuit 5
b-Sb1-0-3-2 = (Swap ↑ ↑ • (Swap ↑ • CS • Swap ↑) • Swap ↑ ↑)
b-Sb1-0-4-2 : Circuit 5
b-Sb1-0-4-2 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • CS • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb⁻1-0-4-2 : Circuit 5
b-Sb⁻1-0-4-2 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb1-0-32-4 : Circuit 5
b-Sb1-0-32-4 = b-Bx1-0324 • (Toffᵗ ↑ ↑) • b-Sb1-0-4-2 • (Toffᵗ ↑ ↑) • b-Sb⁻1-0-4-2
b-Sb⁻1-0-2-4 : Circuit 5
b-Sb⁻1-0-2-4 = (Swap ↑ • (CS • CS • CS) • Swap ↑)
b-Sb1-0-34-2 : Circuit 5
b-Sb1-0-34-2 = b-Bx1-0342 • (Toff ↑ ↑) • b-Sb1-0-2-4 • (Toff ↑ ↑) • b-Sb⁻1-0-2-4
b-Sb⁻1-0-3-2 : Circuit 5
b-Sb⁻1-0-3-2 = (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑)
b-Sb1-0-42-3 : Circuit 5
b-Sb1-0-42-3 = b-Bx1-0423 • ((K ↑ • CCZ • K ↑ • iI) ↑ ↑) • b-Sb1-0-3-2 • ((K ↑ • CCZ • K ↑ • iI) ↑ ↑) • b-Sb⁻1-0-3-2
b-Sb⁻1-0-2-3 : Circuit 5
b-Sb⁻1-0-2-3 = (Swap ↑ • (CS • CS • CS) • Swap ↑)
b-Sb1-0-43-2 : Circuit 5
b-Sb1-0-43-2 = b-Bx1-0432 • (Toff ↑ ↑) • b-Sb1-0-2-3 • (Toff ↑ ↑) • b-Sb⁻1-0-2-3
b-Sb1-2-0-3 : Circuit 5
b-Sb1-2-0-3 = (Swap ↑ • CS • Swap ↑)
b-Sb1-2-0-4 : Circuit 5
b-Sb1-2-0-4 = (Swap ↑ • CS • Swap ↑)
b-Sb1-2-4-3 : Circuit 5
b-Sb1-2-4-3 = (Swap ↑ ↑ ↑ • (CS ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb⁻1-2-4-3 : Circuit 5
b-Sb⁻1-2-4-3 = (Swap ↑ ↑ ↑ • ((CS • CS • CS) ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb1-2-03-4 : Circuit 5
b-Sb1-2-03-4 = b-Bx1-2034 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Sb1-2-4-3 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Sb⁻1-2-4-3
b-Sb1-2-3-4 : Circuit 5
b-Sb1-2-3-4 = (CS ↑ ↑)
b-Sb⁻1-2-3-4 : Circuit 5
b-Sb⁻1-2-3-4 = ((CS • CS • CS) ↑ ↑)
b-Sb1-2-04-3 : Circuit 5
b-Sb1-2-04-3 = b-Bx1-2043 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Sb1-2-3-4 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Sb⁻1-2-3-4
b-Sb1-2-3-0 : Circuit 5
b-Sb1-2-3-0 = (CS ↑ ↑)
b-Sb⁻1-2-0-4 : Circuit 5
b-Sb⁻1-2-0-4 = (Swap ↑ • (CS • CS • CS) • Swap ↑)
b-Sb1-2-34-0 : Circuit 5
b-Sb1-2-34-0 = b-Bx1-2340 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Sb1-2-0-4 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Sb⁻1-2-0-4
b-Sb1-2-4-0 : Circuit 5
b-Sb1-2-4-0 = (Swap ↑ ↑ ↑ • (CS ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb⁻1-2-3-0 : Circuit 5
b-Sb⁻1-2-3-0 = ((CS • CS • CS) ↑ ↑)
b-Sb1-2-40-3 : Circuit 5
b-Sb1-2-40-3 = b-Bx1-2403 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Sb1-2-3-0 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Sb⁻1-2-3-0
b-Sb⁻1-2-0-3 : Circuit 5
b-Sb⁻1-2-0-3 = (Swap ↑ • (CS • CS • CS) • Swap ↑)
b-Sb1-2-43-0 : Circuit 5
b-Sb1-2-43-0 = b-Bx1-2430 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Sb1-2-0-3 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Sb⁻1-2-0-3
b-Sb1-3-0-4 : Circuit 5
b-Sb1-3-0-4 = (Swap ↑ ↑ • (Swap ↑ • CS • Swap ↑) • Swap ↑ ↑)
b-Sb1-3-2-4 : Circuit 5
b-Sb1-3-2-4 = (CS ↑ ↑)
b-Sb⁻1-3-2-4 : Circuit 5
b-Sb⁻1-3-2-4 = ((CS • CS • CS) ↑ ↑)
b-Sb1-3-04-2 : Circuit 5
b-Sb1-3-04-2 = b-Bx1-3042 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Sb1-3-2-4 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Sb⁻1-3-2-4
b-Sb1-3-2-0 : Circuit 5
b-Sb1-3-2-0 = (CS ↑ ↑)
b-Sb⁻1-3-0-4 : Circuit 5
b-Sb⁻1-3-0-4 = (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑)
b-Sb1-3-24-0 : Circuit 5
b-Sb1-3-24-0 = b-Bx1-3240 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Sb1-3-0-4 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Sb⁻1-3-0-4
b-Sb1-3-4-0 : Circuit 5
b-Sb1-3-4-0 = (CS ↑ ↑ ↑)
b-Sb⁻1-3-2-0 : Circuit 5
b-Sb⁻1-3-2-0 = ((CS • CS • CS) ↑ ↑)
b-Sb1-3-40-2 : Circuit 5
b-Sb1-3-40-2 = b-Bx1-3402 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Sb1-3-2-0 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Sb⁻1-3-2-0
b-Sb1-4-2-0 : Circuit 5
b-Sb1-4-2-0 = (Swap ↑ ↑ ↑ • (CS ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb1-4-3-0 : Circuit 5
b-Sb1-4-3-0 = (CS ↑ ↑ ↑)
b-Sb⁻1-4-3-0 : Circuit 5
b-Sb⁻1-4-3-0 = ((CS • CS • CS) ↑ ↑ ↑)
b-Sb1-4-20-3 : Circuit 5
b-Sb1-4-20-3 = b-Bx1-4203 • (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) • b-Sb1-4-3-0 • (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) • b-Sb⁻1-4-3-0
b-Sb⁻1-4-2-0 : Circuit 5
b-Sb⁻1-4-2-0 = (Swap ↑ ↑ ↑ • ((CS • CS • CS) ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb1-4-30-2 : Circuit 5
b-Sb1-4-30-2 = b-Bx1-4302 • (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) • b-Sb1-4-2-0 • (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) • b-Sb⁻1-4-2-0
b-Sb2-0-1-3 : Circuit 5
b-Sb2-0-1-3 = CS
b-Sb2-0-1-4 : Circuit 5
b-Sb2-0-1-4 = CS
b-Sb2-0-4-3 : Circuit 5
b-Sb2-0-4-3 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • CS • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb⁻2-0-4-3 : Circuit 5
b-Sb⁻2-0-4-3 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb2-0-13-4 : Circuit 5
b-Sb2-0-13-4 = b-Bx2-0134 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Sb2-0-4-3 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Sb⁻2-0-4-3
b-Sb2-0-3-4 : Circuit 5
b-Sb2-0-3-4 = (Swap ↑ ↑ • (Swap ↑ • CS • Swap ↑) • Swap ↑ ↑)
b-Sb⁻2-0-3-4 : Circuit 5
b-Sb⁻2-0-3-4 = (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑)
b-Sb2-0-14-3 : Circuit 5
b-Sb2-0-14-3 = b-Bx2-0143 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Sb2-0-3-4 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Sb⁻2-0-3-4
b-Sb2-0-3-1 : Circuit 5
b-Sb2-0-3-1 = (Swap ↑ ↑ • (Swap ↑ • CS • Swap ↑) • Swap ↑ ↑)
b-Sb2-0-4-1 : Circuit 5
b-Sb2-0-4-1 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • CS • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb⁻2-0-4-1 : Circuit 5
b-Sb⁻2-0-4-1 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb2-0-31-4 : Circuit 5
b-Sb2-0-31-4 = b-Bx2-0314 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Sb2-0-4-1 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Sb⁻2-0-4-1
b-Sb⁻2-0-1-4 : Circuit 5
b-Sb⁻2-0-1-4 = (CS • CS • CS)
b-Sb2-0-34-1 : Circuit 5
b-Sb2-0-34-1 = b-Bx2-0341 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Sb2-0-1-4 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Sb⁻2-0-1-4
b-Sb⁻2-0-3-1 : Circuit 5
b-Sb⁻2-0-3-1 = (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑)
b-Sb2-0-41-3 : Circuit 5
b-Sb2-0-41-3 = b-Bx2-0413 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Sb2-0-3-1 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Sb⁻2-0-3-1
b-Sb⁻2-0-1-3 : Circuit 5
b-Sb⁻2-0-1-3 = (CS • CS • CS)
b-Sb2-0-43-1 : Circuit 5
b-Sb2-0-43-1 = b-Bx2-0431 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Sb2-0-1-3 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Sb⁻2-0-1-3
b-Sb2-1-0-3 : Circuit 5
b-Sb2-1-0-3 = CS
b-Sb2-1-0-4 : Circuit 5
b-Sb2-1-0-4 = CS
b-Sb2-1-3-0 : Circuit 5
b-Sb2-1-3-0 = (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑)
b-Sb⁻2-1-0-4 : Circuit 5
b-Sb⁻2-1-0-4 = (CS • CS • CS)
b-Sb2-1-34-0 : Circuit 5
b-Sb2-1-34-0 = b-Bx2-1340 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Sb2-1-0-4 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Sb⁻2-1-0-4
b-Sb2-1-4-0 : Circuit 5
b-Sb2-1-4-0 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb⁻2-1-3-0 : Circuit 5
b-Sb⁻2-1-3-0 = (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑)
b-Sb2-1-40-3 : Circuit 5
b-Sb2-1-40-3 = b-Bx2-1403 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Sb2-1-3-0 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Sb⁻2-1-3-0
b-Sb⁻2-1-0-3 : Circuit 5
b-Sb⁻2-1-0-3 = (CS • CS • CS)
b-Sb2-1-43-0 : Circuit 5
b-Sb2-1-43-0 = b-Bx2-1430 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Sb2-1-0-3 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Sb⁻2-1-0-3
b-Sb2-3-0-1 : Circuit 5
b-Sb2-3-0-1 = (Swap ↑ ↑ • (Swap ↑ • CS • Swap ↑) • Swap ↑ ↑)
b-Sb2-3-0-4 : Circuit 5
b-Sb2-3-0-4 = (Swap ↑ ↑ • (Swap ↑ • CS • Swap ↑) • Swap ↑ ↑)
b-Sb2-3-1-4 : Circuit 5
b-Sb2-3-1-4 = (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑)
b-Sb⁻2-3-1-4 : Circuit 5
b-Sb⁻2-3-1-4 = (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑)
b-Sb2-3-04-1 : Circuit 5
b-Sb2-3-04-1 = b-Bx2-3041 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Sb2-3-1-4 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Sb⁻2-3-1-4
b-Sb2-3-1-0 : Circuit 5
b-Sb2-3-1-0 = (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑)
b-Sb⁻2-3-0-4 : Circuit 5
b-Sb⁻2-3-0-4 = (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑)
b-Sb2-3-14-0 : Circuit 5
b-Sb2-3-14-0 = b-Bx2-3140 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Sb2-3-0-4 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Sb⁻2-3-0-4
b-Sb⁻2-3-1-0 : Circuit 5
b-Sb⁻2-3-1-0 = (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑)
b-Sb2-3-40-1 : Circuit 5
b-Sb2-3-40-1 = b-Bx2-3401 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Sb2-3-1-0 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Sb⁻2-3-1-0
b-Sb⁻2-3-0-1 : Circuit 5
b-Sb⁻2-3-0-1 = (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑)
b-Sb2-3-41-0 : Circuit 5
b-Sb2-3-41-0 = b-Bx2-3410 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Sb2-3-0-1 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Sb⁻2-3-0-1
b-Sb2-4-0-1 : Circuit 5
b-Sb2-4-0-1 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • CS • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb2-4-3-1 : Circuit 5
b-Sb2-4-3-1 = (CS ↑ ↑ ↑)
b-Sb⁻2-4-3-1 : Circuit 5
b-Sb⁻2-4-3-1 = ((CS • CS • CS) ↑ ↑ ↑)
b-Sb2-4-01-3 : Circuit 5
b-Sb2-4-01-3 = b-Bx2-4013 • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • b-Sb2-4-3-1 • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • b-Sb⁻2-4-3-1
b-Sb2-4-1-0 : Circuit 5
b-Sb2-4-1-0 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb2-4-3-0 : Circuit 5
b-Sb2-4-3-0 = (CS ↑ ↑ ↑)
b-Sb⁻2-4-3-0 : Circuit 5
b-Sb⁻2-4-3-0 = ((CS • CS • CS) ↑ ↑ ↑)
b-Sb2-4-10-3 : Circuit 5
b-Sb2-4-10-3 = b-Bx2-4103 • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • b-Sb2-4-3-0 • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • b-Sb⁻2-4-3-0
b-Sb⁻2-4-1-0 : Circuit 5
b-Sb⁻2-4-1-0 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb2-4-30-1 : Circuit 5
b-Sb2-4-30-1 = b-Bx2-4301 • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • b-Sb2-4-1-0 • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • b-Sb⁻2-4-1-0
b-Sb⁻2-4-0-1 : Circuit 5
b-Sb⁻2-4-0-1 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb2-4-31-0 : Circuit 5
b-Sb2-4-31-0 = b-Bx2-4310 • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • b-Sb2-4-0-1 • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • b-Sb⁻2-4-0-1
b-Sb3-0-1-2 : Circuit 5
b-Sb3-0-1-2 = CS
b-Sb3-0-1-4 : Circuit 5
b-Sb3-0-1-4 = CS
b-Sb3-0-2-4 : Circuit 5
b-Sb3-0-2-4 = (Swap ↑ • CS • Swap ↑)
b-Sb⁻3-0-2-4 : Circuit 5
b-Sb⁻3-0-2-4 = (Swap ↑ • (CS • CS • CS) • Swap ↑)
b-Sb3-0-14-2 : Circuit 5
b-Sb3-0-14-2 = b-Bx3-0142 • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • b-Sb3-0-2-4 • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • b-Sb⁻3-0-2-4
b-Sb3-0-2-1 : Circuit 5
b-Sb3-0-2-1 = (Swap ↑ • CS • Swap ↑)
b-Sb3-0-4-1 : Circuit 5
b-Sb3-0-4-1 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • CS • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb⁻3-0-4-1 : Circuit 5
b-Sb⁻3-0-4-1 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb3-0-21-4 : Circuit 5
b-Sb3-0-21-4 = b-Bx3-0214 • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • b-Sb3-0-4-1 • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • b-Sb⁻3-0-4-1
b-Sb⁻3-0-1-4 : Circuit 5
b-Sb⁻3-0-1-4 = (CS • CS • CS)
b-Sb3-0-24-1 : Circuit 5
b-Sb3-0-24-1 = b-Bx3-0241 • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • b-Sb3-0-1-4 • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • b-Sb⁻3-0-1-4
b-Sb⁻3-0-2-1 : Circuit 5
b-Sb⁻3-0-2-1 = (Swap ↑ • (CS • CS • CS) • Swap ↑)
b-Sb3-0-41-2 : Circuit 5
b-Sb3-0-41-2 = b-Bx3-0412 • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • b-Sb3-0-2-1 • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • b-Sb⁻3-0-2-1
b-Sb⁻3-0-1-2 : Circuit 5
b-Sb⁻3-0-1-2 = (CS • CS • CS)
b-Sb3-0-42-1 : Circuit 5
b-Sb3-0-42-1 = b-Bx3-0421 • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • b-Sb3-0-1-2 • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • b-Sb⁻3-0-1-2
b-Sb3-1-0-2 : Circuit 5
b-Sb3-1-0-2 = CS
b-Sb3-1-0-4 : Circuit 5
b-Sb3-1-0-4 = CS
b-Sb3-1-2-0 : Circuit 5
b-Sb3-1-2-0 = (CS ↑)
b-Sb3-1-4-0 : Circuit 5
b-Sb3-1-4-0 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb⁻3-1-2-0 : Circuit 5
b-Sb⁻3-1-2-0 = ((CS • CS • CS) ↑)
b-Sb3-1-40-2 : Circuit 5
b-Sb3-1-40-2 = b-Bx3-1402 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Sb3-1-2-0 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Sb⁻3-1-2-0
b-Sb⁻3-1-0-2 : Circuit 5
b-Sb⁻3-1-0-2 = (CS • CS • CS)
b-Sb3-1-42-0 : Circuit 5
b-Sb3-1-42-0 = b-Bx3-1420 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Sb3-1-0-2 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Sb⁻3-1-0-2
b-Sb3-2-0-1 : Circuit 5
b-Sb3-2-0-1 = (Swap ↑ • CS • Swap ↑)
b-Sb3-2-1-0 : Circuit 5
b-Sb3-2-1-0 = (CS ↑)
b-Sb⁻3-2-1-0 : Circuit 5
b-Sb⁻3-2-1-0 = ((CS • CS • CS) ↑)
b-Sb3-2-40-1 : Circuit 5
b-Sb3-2-40-1 = b-Bx3-2401 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Sb3-2-1-0 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Sb⁻3-2-1-0
b-Sb⁻3-2-0-1 : Circuit 5
b-Sb⁻3-2-0-1 = (Swap ↑ • (CS • CS • CS) • Swap ↑)
b-Sb3-2-41-0 : Circuit 5
b-Sb3-2-41-0 = b-Bx3-2410 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Sb3-2-0-1 • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • b-Sb⁻3-2-0-1
b-Sb3-4-0-1 : Circuit 5
b-Sb3-4-0-1 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • CS • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb3-4-0-2 : Circuit 5
b-Sb3-4-0-2 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • CS • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb3-4-2-1 : Circuit 5
b-Sb3-4-2-1 = (Swap ↑ ↑ ↑ • (CS ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb⁻3-4-2-1 : Circuit 5
b-Sb⁻3-4-2-1 = (Swap ↑ ↑ ↑ • ((CS • CS • CS) ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb3-4-01-2 : Circuit 5
b-Sb3-4-01-2 = b-Bx3-4012 • Toffᵗ • b-Sb3-4-2-1 • Toffᵗ • b-Sb⁻3-4-2-1
b-Sb3-4-1-0 : Circuit 5
b-Sb3-4-1-0 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb3-4-2-0 : Circuit 5
b-Sb3-4-2-0 = (Swap ↑ ↑ ↑ • (CS ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb⁻3-4-2-0 : Circuit 5
b-Sb⁻3-4-2-0 = (Swap ↑ ↑ ↑ • ((CS • CS • CS) ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb3-4-10-2 : Circuit 5
b-Sb3-4-10-2 = b-Bx3-4102 • Toffᵗ • b-Sb3-4-2-0 • Toffᵗ • b-Sb⁻3-4-2-0
b-Sb⁻3-4-0-2 : Circuit 5
b-Sb⁻3-4-0-2 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb3-4-12-0 : Circuit 5
b-Sb3-4-12-0 = b-Bx3-4120 • Toff • b-Sb3-4-0-2 • Toff • b-Sb⁻3-4-0-2
b-Sb⁻3-4-1-0 : Circuit 5
b-Sb⁻3-4-1-0 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb3-4-20-1 : Circuit 5
b-Sb3-4-20-1 = b-Bx3-4201 • (K ↑ • CCZ • K ↑ • iI) • b-Sb3-4-1-0 • (K ↑ • CCZ • K ↑ • iI) • b-Sb⁻3-4-1-0
b-Sb⁻3-4-0-1 : Circuit 5
b-Sb⁻3-4-0-1 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb3-4-21-0 : Circuit 5
b-Sb3-4-21-0 = b-Bx3-4210 • Toff • b-Sb3-4-0-1 • Toff • b-Sb⁻3-4-0-1
b-Sb4-0-1-2 : Circuit 5
b-Sb4-0-1-2 = CS
b-Sb4-0-1-3 : Circuit 5
b-Sb4-0-1-3 = CS
b-Sb4-0-2-1 : Circuit 5
b-Sb4-0-2-1 = (Swap ↑ • CS • Swap ↑)
b-Sb4-0-3-1 : Circuit 5
b-Sb4-0-3-1 = (Swap ↑ ↑ • (Swap ↑ • CS • Swap ↑) • Swap ↑ ↑)
b-Sb⁻4-0-3-1 : Circuit 5
b-Sb⁻4-0-3-1 = (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑)
b-Sb4-0-21-3 : Circuit 5
b-Sb4-0-21-3 = b-Bx4-0213 • (Toffᵗ ↑) • b-Sb4-0-3-1 • (Toffᵗ ↑) • b-Sb⁻4-0-3-1
b-Sb⁻4-0-1-3 : Circuit 5
b-Sb⁻4-0-1-3 = (CS • CS • CS)
b-Sb4-0-23-1 : Circuit 5
b-Sb4-0-23-1 = b-Bx4-0231 • (Toff ↑) • b-Sb4-0-1-3 • (Toff ↑) • b-Sb⁻4-0-1-3
b-Sb⁻4-0-2-1 : Circuit 5
b-Sb⁻4-0-2-1 = (Swap ↑ • (CS • CS • CS) • Swap ↑)
b-Sb4-0-31-2 : Circuit 5
b-Sb4-0-31-2 = b-Bx4-0312 • ((K ↑ • CCZ • K ↑ • iI) ↑) • b-Sb4-0-2-1 • ((K ↑ • CCZ • K ↑ • iI) ↑) • b-Sb⁻4-0-2-1
b-Sb⁻4-0-1-2 : Circuit 5
b-Sb⁻4-0-1-2 = (CS • CS • CS)
b-Sb4-0-32-1 : Circuit 5
b-Sb4-0-32-1 = b-Bx4-0321 • (Toff ↑) • b-Sb4-0-1-2 • (Toff ↑) • b-Sb⁻4-0-1-2
b-Sb4-1-0-2 : Circuit 5
b-Sb4-1-0-2 = CS
b-Sb4-1-0-3 : Circuit 5
b-Sb4-1-0-3 = CS
b-Sb4-1-2-0 : Circuit 5
b-Sb4-1-2-0 = (CS ↑)
b-Sb⁻4-1-0-3 : Circuit 5
b-Sb⁻4-1-0-3 = (CS • CS • CS)
b-Sb4-1-23-0 : Circuit 5
b-Sb4-1-23-0 = b-Bx4-1230 • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • b-Sb4-1-0-3 • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • b-Sb⁻4-1-0-3
b-Sb4-1-3-0 : Circuit 5
b-Sb4-1-3-0 = (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑)
b-Sb⁻4-1-0-2 : Circuit 5
b-Sb⁻4-1-0-2 = (CS • CS • CS)
b-Sb4-1-32-0 : Circuit 5
b-Sb4-1-32-0 = b-Bx4-1320 • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • b-Sb4-1-0-2 • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • b-Sb⁻4-1-0-2
b-Sb4-2-3-0 : Circuit 5
b-Sb4-2-3-0 = (CS ↑ ↑)
b-Sb4-3-1-0 : Circuit 5
b-Sb4-3-1-0 = (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑)
b-Sb4-3-2-0 : Circuit 5
b-Sb4-3-2-0 = (CS ↑ ↑)
b-Sb⁻0-1-23-4 : Circuit 5
b-Sb⁻0-1-23-4 = b-Sb0-1-4-3 • (Toffᵗ ↑ ↑) • b-Sb⁻0-1-4-3 • (Toffᵗ ↑ ↑) • b-Bx⁻0-1234
b-Sb⁻0-1-3-4 : Circuit 5
b-Sb⁻0-1-3-4 = (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑)
b-Sb⁻0-1-32-4 : Circuit 5
b-Sb⁻0-1-32-4 = b-Sb0-1-4-2 • (Toffᵗ ↑ ↑) • b-Sb⁻0-1-4-2 • (Toffᵗ ↑ ↑) • b-Bx⁻0-1324
b-Sb⁻0-1-34-2 : Circuit 5
b-Sb⁻0-1-34-2 = b-Sb0-1-2-4 • (Toff ↑ ↑) • b-Sb⁻0-1-2-4 • (Toff ↑ ↑) • b-Bx⁻0-1342
b-Sb⁻0-1-42-3 : Circuit 5
b-Sb⁻0-1-42-3 = b-Sb0-1-3-2 • ((K ↑ • CCZ • K ↑ • iI) ↑ ↑) • b-Sb⁻0-1-3-2 • ((K ↑ • CCZ • K ↑ • iI) ↑ ↑) • b-Bx⁻0-1423
b-Sb⁻0-1-43-2 : Circuit 5
b-Sb⁻0-1-43-2 = b-Sb0-1-2-3 • (Toff ↑ ↑) • b-Sb⁻0-1-2-3 • (Toff ↑ ↑) • b-Bx⁻0-1432
b-Sb⁻0-2-34-1 : Circuit 5
b-Sb⁻0-2-34-1 = b-Sb0-2-1-4 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Sb⁻0-2-1-4 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx⁻0-2341
b-Sb⁻0-2-43-1 : Circuit 5
b-Sb⁻0-2-43-1 = b-Sb0-2-1-3 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Sb⁻0-2-1-3 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx⁻0-2431
b-Sb⁻0-3-1-2 : Circuit 5
b-Sb⁻0-3-1-2 = (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑)
b-Sb⁻0-3-2-1 : Circuit 5
b-Sb⁻0-3-2-1 = ((CS • CS • CS) ↑ ↑)
b-Sb⁻0-4-1-2 : Circuit 5
b-Sb⁻0-4-1-2 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb⁻0-4-1-3 : Circuit 5
b-Sb⁻0-4-1-3 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb⁻0-4-2-1 : Circuit 5
b-Sb⁻0-4-2-1 = (Swap ↑ ↑ ↑ • ((CS • CS • CS) ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb⁻1-0-23-4 : Circuit 5
b-Sb⁻1-0-23-4 = b-Sb1-0-4-3 • (Toffᵗ ↑ ↑) • b-Sb⁻1-0-4-3 • (Toffᵗ ↑ ↑) • b-Bx⁻1-0234
b-Sb⁻1-0-24-3 : Circuit 5
b-Sb⁻1-0-24-3 = b-Sb1-0-3-4 • ((K ↑ • CCZ • K ↑ • iI) ↑ ↑) • b-Sb⁻1-0-3-4 • ((K ↑ • CCZ • K ↑ • iI) ↑ ↑) • b-Bx⁻1-0243
b-Sb⁻1-0-32-4 : Circuit 5
b-Sb⁻1-0-32-4 = b-Sb1-0-4-2 • (Toffᵗ ↑ ↑) • b-Sb⁻1-0-4-2 • (Toffᵗ ↑ ↑) • b-Bx⁻1-0324
b-Sb⁻1-0-34-2 : Circuit 5
b-Sb⁻1-0-34-2 = b-Sb1-0-2-4 • (Toff ↑ ↑) • b-Sb⁻1-0-2-4 • (Toff ↑ ↑) • b-Bx⁻1-0342
b-Sb⁻1-0-42-3 : Circuit 5
b-Sb⁻1-0-42-3 = b-Sb1-0-3-2 • ((K ↑ • CCZ • K ↑ • iI) ↑ ↑) • b-Sb⁻1-0-3-2 • ((K ↑ • CCZ • K ↑ • iI) ↑ ↑) • b-Bx⁻1-0423
b-Sb⁻1-0-43-2 : Circuit 5
b-Sb⁻1-0-43-2 = b-Sb1-0-2-3 • (Toff ↑ ↑) • b-Sb⁻1-0-2-3 • (Toff ↑ ↑) • b-Bx⁻1-0432
b-Sb⁻1-2-34-0 : Circuit 5
b-Sb⁻1-2-34-0 = b-Sb1-2-0-4 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Sb⁻1-2-0-4 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx⁻1-2340
b-Sb⁻1-2-4-0 : Circuit 5
b-Sb⁻1-2-4-0 = (Swap ↑ ↑ ↑ • ((CS • CS • CS) ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb⁻1-2-40-3 : Circuit 5
b-Sb⁻1-2-40-3 = b-Sb1-2-3-0 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Sb⁻1-2-3-0 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx⁻1-2403
b-Sb⁻1-3-4-0 : Circuit 5
b-Sb⁻1-3-4-0 = ((CS • CS • CS) ↑ ↑ ↑)
b-Sb⁻1-3-4-2 : Circuit 5
b-Sb⁻1-3-4-2 = ((CS • CS • CS) ↑ ↑ ↑)
b-Sb⁻1-3-40-2 : Circuit 5
b-Sb⁻1-3-40-2 = b-Sb1-3-2-0 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Sb⁻1-3-2-0 • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • b-Bx⁻1-3402
b-Sb⁻1-4-20-3 : Circuit 5
b-Sb⁻1-4-20-3 = b-Sb1-4-3-0 • (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) • b-Sb⁻1-4-3-0 • (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) • b-Bx⁻1-4203
b-Sb⁻1-4-30-2 : Circuit 5
b-Sb⁻1-4-30-2 = b-Sb1-4-2-0 • (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) • b-Sb⁻1-4-2-0 • (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) • b-Bx⁻1-4302
b-Sb⁻2-0-13-4 : Circuit 5
b-Sb⁻2-0-13-4 = b-Sb2-0-4-3 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Sb⁻2-0-4-3 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx⁻2-0134
b-Sb⁻2-0-14-3 : Circuit 5
b-Sb⁻2-0-14-3 = b-Sb2-0-3-4 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Sb⁻2-0-3-4 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx⁻2-0143
b-Sb⁻2-0-31-4 : Circuit 5
b-Sb⁻2-0-31-4 = b-Sb2-0-4-1 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Sb⁻2-0-4-1 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toffᵗ ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx⁻2-0314
b-Sb⁻2-0-34-1 : Circuit 5
b-Sb⁻2-0-34-1 = b-Sb2-0-1-4 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Sb⁻2-0-1-4 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx⁻2-0341
b-Sb⁻2-0-41-3 : Circuit 5
b-Sb⁻2-0-41-3 = b-Sb2-0-3-1 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Sb⁻2-0-3-1 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx⁻2-0413
b-Sb⁻2-0-43-1 : Circuit 5
b-Sb⁻2-0-43-1 = b-Sb2-0-1-3 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Sb⁻2-0-1-3 • (Swap ↑ ↑ • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • Swap ↑ ↑) • b-Bx⁻2-0431
b-Sb⁻2-1-34-0 : Circuit 5
b-Sb⁻2-1-34-0 = b-Sb2-1-0-4 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Sb⁻2-1-0-4 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx⁻2-1340
b-Sb⁻2-1-4-0 : Circuit 5
b-Sb⁻2-1-4-0 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb⁻2-1-40-3 : Circuit 5
b-Sb⁻2-1-40-3 = b-Sb2-1-3-0 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Sb⁻2-1-3-0 • (Swap ↑ ↑ • (Swap ↑ • (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑ ↑ ↑) • Swap ↑) • Swap ↑ ↑) • b-Bx⁻2-1403
b-Sb⁻2-3-4-0 : Circuit 5
b-Sb⁻2-3-4-0 = ((CS • CS • CS) ↑ ↑ ↑)
b-Sb⁻2-3-4-1 : Circuit 5
b-Sb⁻2-3-4-1 = ((CS • CS • CS) ↑ ↑ ↑)
b-Sb⁻2-4-01-3 : Circuit 5
b-Sb⁻2-4-01-3 = b-Sb2-4-3-1 • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • b-Sb⁻2-4-3-1 • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • b-Bx⁻2-4013
b-Sb⁻2-4-10-3 : Circuit 5
b-Sb⁻2-4-10-3 = b-Sb2-4-3-0 • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • b-Sb⁻2-4-3-0 • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • b-Bx⁻2-4103
b-Sb⁻3-0-41-2 : Circuit 5
b-Sb⁻3-0-41-2 = b-Sb3-0-2-1 • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • b-Sb⁻3-0-2-1 • (Swap ↑ ↑ ↑ • ((K ↑ • CCZ • K ↑ • iI) ↑) • Swap ↑ ↑ ↑) • b-Bx⁻3-0412
b-Sb⁻3-0-42-1 : Circuit 5
b-Sb⁻3-0-42-1 = b-Sb3-0-1-2 • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • b-Sb⁻3-0-1-2 • (Swap ↑ ↑ ↑ • (Toff ↑) • Swap ↑ ↑ ↑) • b-Bx⁻3-0421
b-Sb⁻3-1-0-4 : Circuit 5
b-Sb⁻3-1-0-4 = (CS • CS • CS)
b-Sb⁻3-1-4-0 : Circuit 5
b-Sb⁻3-1-4-0 = (Swap ↑ ↑ ↑ • (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑) • Swap ↑ ↑ ↑)
b-Sb⁻4-0-23-1 : Circuit 5
b-Sb⁻4-0-23-1 = b-Sb4-0-1-3 • (Toff ↑) • b-Sb⁻4-0-1-3 • (Toff ↑) • b-Bx⁻4-0231
b-Sb⁻4-0-31-2 : Circuit 5
b-Sb⁻4-0-31-2 = b-Sb4-0-2-1 • ((K ↑ • CCZ • K ↑ • iI) ↑) • b-Sb⁻4-0-2-1 • ((K ↑ • CCZ • K ↑ • iI) ↑) • b-Bx⁻4-0312
b-Sb⁻4-0-32-1 : Circuit 5
b-Sb⁻4-0-32-1 = b-Sb4-0-1-2 • (Toff ↑) • b-Sb⁻4-0-1-2 • (Toff ↑) • b-Bx⁻4-0321
b-Sb⁻4-1-2-0 : Circuit 5
b-Sb⁻4-1-2-0 = ((CS • CS • CS) ↑)
b-Sb⁻4-1-23-0 : Circuit 5
b-Sb⁻4-1-23-0 = b-Sb4-1-0-3 • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • b-Sb⁻4-1-0-3 • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • b-Bx⁻4-1230
b-Sb⁻4-1-3-0 : Circuit 5
b-Sb⁻4-1-3-0 = (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑)
b-Sb⁻4-1-32-0 : Circuit 5
b-Sb⁻4-1-32-0 = b-Sb4-1-0-2 • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • b-Sb⁻4-1-0-2 • (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) • b-Bx⁻4-1320

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
⟪ Bx1-03 ⟫ = b-Bx1-03
⟪ Bx0-123 ⟫ = b-Bx0-123
⟪ Bx0-14 ⟫ = b-Bx0-14
⟪ Bx1-034 ⟫ = b-Bx1-034
⟪ Bx0-1234 ⟫ = b-Bx0-1234
⟪ Bx1-04 ⟫ = b-Bx1-04
⟪ Bx0-124 ⟫ = b-Bx0-124
⟪ Bx0-13 ⟫ = b-Bx0-13
⟪ Bx1-043 ⟫ = b-Bx1-043
⟪ Bx0-1243 ⟫ = b-Bx0-1243
⟪ Bx1-02 ⟫ = b-Bx1-02
⟪ Bx0-132 ⟫ = b-Bx0-132
⟪ Bx1-024 ⟫ = b-Bx1-024
⟪ Bx0-1324 ⟫ = b-Bx0-1324
⟪ Bx0-134 ⟫ = b-Bx0-134
⟪ Bx1-042 ⟫ = b-Bx1-042
⟪ Bx0-1342 ⟫ = b-Bx0-1342
⟪ Bx0-142 ⟫ = b-Bx0-142
⟪ Bx1-023 ⟫ = b-Bx1-023
⟪ Bx0-1423 ⟫ = b-Bx0-1423
⟪ Bx0-143 ⟫ = b-Bx0-143
⟪ Bx1-032 ⟫ = b-Bx1-032
⟪ Bx0-1432 ⟫ = b-Bx0-1432
⟪ Bx0-21 ⟫ = b-Bx0-21
⟪ Bx2-03 ⟫ = b-Bx2-03
⟪ Bx0-213 ⟫ = b-Bx0-213
⟪ Bx0-24 ⟫ = b-Bx0-24
⟪ Bx2-034 ⟫ = b-Bx2-034
⟪ Bx0-2134 ⟫ = b-Bx0-2134
⟪ Bx2-04 ⟫ = b-Bx2-04
⟪ Bx0-214 ⟫ = b-Bx0-214
⟪ Bx0-23 ⟫ = b-Bx0-23
⟪ Bx2-043 ⟫ = b-Bx2-043
⟪ Bx0-2143 ⟫ = b-Bx0-2143
⟪ Bx2-01 ⟫ = b-Bx2-01
⟪ Bx0-231 ⟫ = b-Bx0-231
⟪ Bx2-014 ⟫ = b-Bx2-014
⟪ Bx0-2314 ⟫ = b-Bx0-2314
⟪ Bx0-234 ⟫ = b-Bx0-234
⟪ Bx2-041 ⟫ = b-Bx2-041
⟪ Bx0-2341 ⟫ = b-Bx0-2341
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
⟪ Bx3-04 ⟫ = b-Bx3-04
⟪ Bx0-314 ⟫ = b-Bx0-314
⟪ Bx0-32 ⟫ = b-Bx0-32
⟪ Bx3-042 ⟫ = b-Bx3-042
⟪ Bx0-3142 ⟫ = b-Bx0-3142
⟪ Bx3-01 ⟫ = b-Bx3-01
⟪ Bx0-321 ⟫ = b-Bx0-321
⟪ Bx3-014 ⟫ = b-Bx3-014
⟪ Bx0-3214 ⟫ = b-Bx0-3214
⟪ Bx0-324 ⟫ = b-Bx0-324
⟪ Bx3-041 ⟫ = b-Bx3-041
⟪ Bx0-3241 ⟫ = b-Bx0-3241
⟪ Bx0-341 ⟫ = b-Bx0-341
⟪ Bx3-012 ⟫ = b-Bx3-012
⟪ Bx0-3412 ⟫ = b-Bx0-3412
⟪ Bx0-342 ⟫ = b-Bx0-342
⟪ Bx3-021 ⟫ = b-Bx3-021
⟪ Bx0-3421 ⟫ = b-Bx0-3421
⟪ Bx0-41 ⟫ = b-Bx0-41
⟪ Bx4-02 ⟫ = b-Bx4-02
⟪ Bx0-412 ⟫ = b-Bx0-412
⟪ Bx0-43 ⟫ = b-Bx0-43
⟪ Bx4-023 ⟫ = b-Bx4-023
⟪ Bx0-4123 ⟫ = b-Bx0-4123
⟪ Bx4-03 ⟫ = b-Bx4-03
⟪ Bx0-413 ⟫ = b-Bx0-413
⟪ Bx0-42 ⟫ = b-Bx0-42
⟪ Bx4-032 ⟫ = b-Bx4-032
⟪ Bx0-4132 ⟫ = b-Bx0-4132
⟪ Bx4-01 ⟫ = b-Bx4-01
⟪ Bx0-421 ⟫ = b-Bx0-421
⟪ Bx4-013 ⟫ = b-Bx4-013
⟪ Bx0-4213 ⟫ = b-Bx0-4213
⟪ Bx0-423 ⟫ = b-Bx0-423
⟪ Bx4-031 ⟫ = b-Bx4-031
⟪ Bx0-4231 ⟫ = b-Bx0-4231
⟪ Bx0-431 ⟫ = b-Bx0-431
⟪ Bx4-012 ⟫ = b-Bx4-012
⟪ Bx0-4312 ⟫ = b-Bx0-4312
⟪ Bx0-432 ⟫ = b-Bx0-432
⟪ Bx4-021 ⟫ = b-Bx4-021
⟪ Bx0-4321 ⟫ = b-Bx0-4321
⟪ Bx1-0234 ⟫ = b-Bx1-0234
⟪ Bx1-0243 ⟫ = b-Bx1-0243
⟪ Bx1-0324 ⟫ = b-Bx1-0324
⟪ Bx1-0342 ⟫ = b-Bx1-0342
⟪ Bx1-0423 ⟫ = b-Bx1-0423
⟪ Bx1-0432 ⟫ = b-Bx1-0432
⟪ Bx1-20 ⟫ = b-Bx1-20
⟪ Bx2-13 ⟫ = b-Bx2-13
⟪ Bx1-203 ⟫ = b-Bx1-203
⟪ Bx1-24 ⟫ = b-Bx1-24
⟪ Bx2-134 ⟫ = b-Bx2-134
⟪ Bx1-2034 ⟫ = b-Bx1-2034
⟪ Bx2-14 ⟫ = b-Bx2-14
⟪ Bx1-204 ⟫ = b-Bx1-204
⟪ Bx1-23 ⟫ = b-Bx1-23
⟪ Bx2-143 ⟫ = b-Bx2-143
⟪ Bx1-2043 ⟫ = b-Bx1-2043
⟪ Bx2-10 ⟫ = b-Bx2-10
⟪ Bx1-230 ⟫ = b-Bx1-230
⟪ Bx2-104 ⟫ = b-Bx2-104
⟪ Bx1-2304 ⟫ = b-Bx1-2304
⟪ Bx1-234 ⟫ = b-Bx1-234
⟪ Bx2-140 ⟫ = b-Bx2-140
⟪ Bx1-2340 ⟫ = b-Bx1-2340
⟪ Bx1-240 ⟫ = b-Bx1-240
⟪ Bx2-103 ⟫ = b-Bx2-103
⟪ Bx1-2403 ⟫ = b-Bx1-2403
⟪ Bx1-243 ⟫ = b-Bx1-243
⟪ Bx2-130 ⟫ = b-Bx2-130
⟪ Bx1-2430 ⟫ = b-Bx1-2430
⟪ Bx1-30 ⟫ = b-Bx1-30
⟪ Bx3-12 ⟫ = b-Bx3-12
⟪ Bx1-302 ⟫ = b-Bx1-302
⟪ Bx1-34 ⟫ = b-Bx1-34
⟪ Bx3-124 ⟫ = b-Bx3-124
⟪ Bx1-3024 ⟫ = b-Bx1-3024
⟪ Bx3-14 ⟫ = b-Bx3-14
⟪ Bx1-304 ⟫ = b-Bx1-304
⟪ Bx1-32 ⟫ = b-Bx1-32
⟪ Bx3-142 ⟫ = b-Bx3-142
⟪ Bx1-3042 ⟫ = b-Bx1-3042
⟪ Bx3-10 ⟫ = b-Bx3-10
⟪ Bx1-320 ⟫ = b-Bx1-320
⟪ Bx3-104 ⟫ = b-Bx3-104
⟪ Bx1-3204 ⟫ = b-Bx1-3204
⟪ Bx1-324 ⟫ = b-Bx1-324
⟪ Bx3-140 ⟫ = b-Bx3-140
⟪ Bx1-3240 ⟫ = b-Bx1-3240
⟪ Bx1-340 ⟫ = b-Bx1-340
⟪ Bx3-102 ⟫ = b-Bx3-102
⟪ Bx1-3402 ⟫ = b-Bx1-3402
⟪ Bx1-342 ⟫ = b-Bx1-342
⟪ Bx3-120 ⟫ = b-Bx3-120
⟪ Bx1-3420 ⟫ = b-Bx1-3420
⟪ Bx1-40 ⟫ = b-Bx1-40
⟪ Bx4-12 ⟫ = b-Bx4-12
⟪ Bx1-402 ⟫ = b-Bx1-402
⟪ Bx1-43 ⟫ = b-Bx1-43
⟪ Bx4-123 ⟫ = b-Bx4-123
⟪ Bx1-4023 ⟫ = b-Bx1-4023
⟪ Bx4-13 ⟫ = b-Bx4-13
⟪ Bx1-403 ⟫ = b-Bx1-403
⟪ Bx1-42 ⟫ = b-Bx1-42
⟪ Bx4-132 ⟫ = b-Bx4-132
⟪ Bx1-4032 ⟫ = b-Bx1-4032
⟪ Bx4-10 ⟫ = b-Bx4-10
⟪ Bx1-420 ⟫ = b-Bx1-420
⟪ Bx4-103 ⟫ = b-Bx4-103
⟪ Bx1-4203 ⟫ = b-Bx1-4203
⟪ Bx1-423 ⟫ = b-Bx1-423
⟪ Bx4-130 ⟫ = b-Bx4-130
⟪ Bx1-4230 ⟫ = b-Bx1-4230
⟪ Bx1-430 ⟫ = b-Bx1-430
⟪ Bx4-102 ⟫ = b-Bx4-102
⟪ Bx1-4302 ⟫ = b-Bx1-4302
⟪ Bx1-432 ⟫ = b-Bx1-432
⟪ Bx4-120 ⟫ = b-Bx4-120
⟪ Bx1-4320 ⟫ = b-Bx1-4320
⟪ Bx2-0134 ⟫ = b-Bx2-0134
⟪ Bx2-0143 ⟫ = b-Bx2-0143
⟪ Bx2-0314 ⟫ = b-Bx2-0314
⟪ Bx2-0341 ⟫ = b-Bx2-0341
⟪ Bx2-0413 ⟫ = b-Bx2-0413
⟪ Bx2-0431 ⟫ = b-Bx2-0431
⟪ Bx2-1034 ⟫ = b-Bx2-1034
⟪ Bx2-1043 ⟫ = b-Bx2-1043
⟪ Bx2-1304 ⟫ = b-Bx2-1304
⟪ Bx2-1340 ⟫ = b-Bx2-1340
⟪ Bx2-1403 ⟫ = b-Bx2-1403
⟪ Bx2-1430 ⟫ = b-Bx2-1430
⟪ Bx2-30 ⟫ = b-Bx2-30
⟪ Bx3-21 ⟫ = b-Bx3-21
⟪ Bx2-301 ⟫ = b-Bx2-301
⟪ Bx2-34 ⟫ = b-Bx2-34
⟪ Bx3-214 ⟫ = b-Bx3-214
⟪ Bx2-3014 ⟫ = b-Bx2-3014
⟪ Bx3-24 ⟫ = b-Bx3-24
⟪ Bx2-304 ⟫ = b-Bx2-304
⟪ Bx2-31 ⟫ = b-Bx2-31
⟪ Bx3-241 ⟫ = b-Bx3-241
⟪ Bx2-3041 ⟫ = b-Bx2-3041
⟪ Bx3-20 ⟫ = b-Bx3-20
⟪ Bx2-310 ⟫ = b-Bx2-310
⟪ Bx3-204 ⟫ = b-Bx3-204
⟪ Bx2-3104 ⟫ = b-Bx2-3104
⟪ Bx2-314 ⟫ = b-Bx2-314
⟪ Bx3-240 ⟫ = b-Bx3-240
⟪ Bx2-3140 ⟫ = b-Bx2-3140
⟪ Bx2-340 ⟫ = b-Bx2-340
⟪ Bx3-201 ⟫ = b-Bx3-201
⟪ Bx2-3401 ⟫ = b-Bx2-3401
⟪ Bx2-341 ⟫ = b-Bx2-341
⟪ Bx3-210 ⟫ = b-Bx3-210
⟪ Bx2-3410 ⟫ = b-Bx2-3410
⟪ Bx2-40 ⟫ = b-Bx2-40
⟪ Bx4-21 ⟫ = b-Bx4-21
⟪ Bx2-401 ⟫ = b-Bx2-401
⟪ Bx2-43 ⟫ = b-Bx2-43
⟪ Bx4-213 ⟫ = b-Bx4-213
⟪ Bx2-4013 ⟫ = b-Bx2-4013
⟪ Bx4-23 ⟫ = b-Bx4-23
⟪ Bx2-403 ⟫ = b-Bx2-403
⟪ Bx2-41 ⟫ = b-Bx2-41
⟪ Bx4-231 ⟫ = b-Bx4-231
⟪ Bx2-4031 ⟫ = b-Bx2-4031
⟪ Bx4-20 ⟫ = b-Bx4-20
⟪ Bx2-410 ⟫ = b-Bx2-410
⟪ Bx4-203 ⟫ = b-Bx4-203
⟪ Bx2-4103 ⟫ = b-Bx2-4103
⟪ Bx2-413 ⟫ = b-Bx2-413
⟪ Bx4-230 ⟫ = b-Bx4-230
⟪ Bx2-4130 ⟫ = b-Bx2-4130
⟪ Bx2-430 ⟫ = b-Bx2-430
⟪ Bx4-201 ⟫ = b-Bx4-201
⟪ Bx2-4301 ⟫ = b-Bx2-4301
⟪ Bx2-431 ⟫ = b-Bx2-431
⟪ Bx4-210 ⟫ = b-Bx4-210
⟪ Bx2-4310 ⟫ = b-Bx2-4310
⟪ Bx3-0124 ⟫ = b-Bx3-0124
⟪ Bx3-0142 ⟫ = b-Bx3-0142
⟪ Bx3-0214 ⟫ = b-Bx3-0214
⟪ Bx3-0241 ⟫ = b-Bx3-0241
⟪ Bx3-0412 ⟫ = b-Bx3-0412
⟪ Bx3-0421 ⟫ = b-Bx3-0421
⟪ Bx3-1024 ⟫ = b-Bx3-1024
⟪ Bx3-1042 ⟫ = b-Bx3-1042
⟪ Bx3-1204 ⟫ = b-Bx3-1204
⟪ Bx3-1240 ⟫ = b-Bx3-1240
⟪ Bx3-1402 ⟫ = b-Bx3-1402
⟪ Bx3-1420 ⟫ = b-Bx3-1420
⟪ Bx3-2014 ⟫ = b-Bx3-2014
⟪ Bx3-2041 ⟫ = b-Bx3-2041
⟪ Bx3-2104 ⟫ = b-Bx3-2104
⟪ Bx3-2140 ⟫ = b-Bx3-2140
⟪ Bx3-2401 ⟫ = b-Bx3-2401
⟪ Bx3-2410 ⟫ = b-Bx3-2410
⟪ Bx3-40 ⟫ = b-Bx3-40
⟪ Bx3-42 ⟫ = b-Bx3-42
⟪ Bx4-312 ⟫ = b-Bx4-312
⟪ Bx3-4012 ⟫ = b-Bx3-4012
⟪ Bx4-32 ⟫ = b-Bx4-32
⟪ Bx3-402 ⟫ = b-Bx3-402
⟪ Bx3-41 ⟫ = b-Bx3-41
⟪ Bx4-321 ⟫ = b-Bx4-321
⟪ Bx3-4021 ⟫ = b-Bx3-4021
⟪ Bx4-302 ⟫ = b-Bx4-302
⟪ Bx3-4102 ⟫ = b-Bx3-4102
⟪ Bx3-412 ⟫ = b-Bx3-412
⟪ Bx4-320 ⟫ = b-Bx4-320
⟪ Bx3-4120 ⟫ = b-Bx3-4120
⟪ Bx4-30 ⟫ = b-Bx4-30
⟪ Bx3-420 ⟫ = b-Bx3-420
⟪ Bx4-301 ⟫ = b-Bx4-301
⟪ Bx3-4201 ⟫ = b-Bx3-4201
⟪ Bx4-31 ⟫ = b-Bx4-31
⟪ Bx3-421 ⟫ = b-Bx3-421
⟪ Bx4-310 ⟫ = b-Bx4-310
⟪ Bx3-4210 ⟫ = b-Bx3-4210
⟪ Bx4-0123 ⟫ = b-Bx4-0123
⟪ Bx4-0132 ⟫ = b-Bx4-0132
⟪ Bx4-0213 ⟫ = b-Bx4-0213
⟪ Bx4-0231 ⟫ = b-Bx4-0231
⟪ Bx4-0312 ⟫ = b-Bx4-0312
⟪ Bx4-0321 ⟫ = b-Bx4-0321
⟪ Bx4-1023 ⟫ = b-Bx4-1023
⟪ Bx4-1032 ⟫ = b-Bx4-1032
⟪ Bx4-1203 ⟫ = b-Bx4-1203
⟪ Bx4-1230 ⟫ = b-Bx4-1230
⟪ Bx4-1302 ⟫ = b-Bx4-1302
⟪ Bx4-1320 ⟫ = b-Bx4-1320
⟪ Bx4-2013 ⟫ = b-Bx4-2013
⟪ Bx4-2031 ⟫ = b-Bx4-2031
⟪ Bx4-2103 ⟫ = b-Bx4-2103
⟪ Bx4-2130 ⟫ = b-Bx4-2130
⟪ Bx4-2301 ⟫ = b-Bx4-2301
⟪ Bx4-2310 ⟫ = b-Bx4-2310
⟪ Bx4-3012 ⟫ = b-Bx4-3012
⟪ Bx4-3021 ⟫ = b-Bx4-3021
⟪ Bx4-3102 ⟫ = b-Bx4-3102
⟪ Bx4-3120 ⟫ = b-Bx4-3120
⟪ Bx⁻0-12 ⟫ = b-Bx⁻0-12
⟪ Bx⁻1-03 ⟫ = b-Bx⁻1-03
⟪ Bx⁻0-123 ⟫ = b-Bx⁻0-123
⟪ Bx⁻0-14 ⟫ = b-Bx⁻0-14
⟪ Bx⁻1-034 ⟫ = b-Bx⁻1-034
⟪ Bx⁻0-1234 ⟫ = b-Bx⁻0-1234
⟪ Bx⁻1-04 ⟫ = b-Bx⁻1-04
⟪ Bx⁻0-124 ⟫ = b-Bx⁻0-124
⟪ Bx⁻0-13 ⟫ = b-Bx⁻0-13
⟪ Bx⁻1-043 ⟫ = b-Bx⁻1-043
⟪ Bx⁻0-1243 ⟫ = b-Bx⁻0-1243
⟪ Bx⁻1-02 ⟫ = b-Bx⁻1-02
⟪ Bx⁻0-132 ⟫ = b-Bx⁻0-132
⟪ Bx⁻1-024 ⟫ = b-Bx⁻1-024
⟪ Bx⁻0-1324 ⟫ = b-Bx⁻0-1324
⟪ Bx⁻0-134 ⟫ = b-Bx⁻0-134
⟪ Bx⁻1-042 ⟫ = b-Bx⁻1-042
⟪ Bx⁻0-1342 ⟫ = b-Bx⁻0-1342
⟪ Bx⁻0-142 ⟫ = b-Bx⁻0-142
⟪ Bx⁻1-023 ⟫ = b-Bx⁻1-023
⟪ Bx⁻0-1423 ⟫ = b-Bx⁻0-1423
⟪ Bx⁻0-143 ⟫ = b-Bx⁻0-143
⟪ Bx⁻1-032 ⟫ = b-Bx⁻1-032
⟪ Bx⁻0-1432 ⟫ = b-Bx⁻0-1432
⟪ Bx⁻0-21 ⟫ = b-Bx⁻0-21
⟪ Bx⁻2-03 ⟫ = b-Bx⁻2-03
⟪ Bx⁻0-213 ⟫ = b-Bx⁻0-213
⟪ Bx⁻0-24 ⟫ = b-Bx⁻0-24
⟪ Bx⁻2-034 ⟫ = b-Bx⁻2-034
⟪ Bx⁻0-2134 ⟫ = b-Bx⁻0-2134
⟪ Bx⁻2-04 ⟫ = b-Bx⁻2-04
⟪ Bx⁻0-214 ⟫ = b-Bx⁻0-214
⟪ Bx⁻2-01 ⟫ = b-Bx⁻2-01
⟪ Bx⁻0-231 ⟫ = b-Bx⁻0-231
⟪ Bx⁻0-234 ⟫ = b-Bx⁻0-234
⟪ Bx⁻2-041 ⟫ = b-Bx⁻2-041
⟪ Bx⁻0-2341 ⟫ = b-Bx⁻0-2341
⟪ Bx⁻0-241 ⟫ = b-Bx⁻0-241
⟪ Bx⁻0-243 ⟫ = b-Bx⁻0-243
⟪ Bx⁻2-031 ⟫ = b-Bx⁻2-031
⟪ Bx⁻0-2431 ⟫ = b-Bx⁻0-2431
⟪ Bx⁻3-02 ⟫ = b-Bx⁻3-02
⟪ Bx⁻0-312 ⟫ = b-Bx⁻0-312
⟪ Bx⁻0-34 ⟫ = b-Bx⁻0-34
⟪ Bx⁻3-024 ⟫ = b-Bx⁻3-024
⟪ Bx⁻0-3124 ⟫ = b-Bx⁻0-3124
⟪ Bx⁻3-01 ⟫ = b-Bx⁻3-01
⟪ Bx⁻0-321 ⟫ = b-Bx⁻0-321
⟪ Bx⁻3-04 ⟫ = b-Bx⁻3-04
⟪ Bx⁻0-324 ⟫ = b-Bx⁻0-324
⟪ Bx⁻4-02 ⟫ = b-Bx⁻4-02
⟪ Bx⁻0-412 ⟫ = b-Bx⁻0-412
⟪ Bx⁻0-43 ⟫ = b-Bx⁻0-43
⟪ Bx⁻4-023 ⟫ = b-Bx⁻4-023
⟪ Bx⁻0-4123 ⟫ = b-Bx⁻0-4123
⟪ Bx⁻4-03 ⟫ = b-Bx⁻4-03
⟪ Bx⁻0-413 ⟫ = b-Bx⁻0-413
⟪ Bx⁻4-01 ⟫ = b-Bx⁻4-01
⟪ Bx⁻0-421 ⟫ = b-Bx⁻0-421
⟪ Bx⁻0-423 ⟫ = b-Bx⁻0-423
⟪ Bx⁻0-431 ⟫ = b-Bx⁻0-431
⟪ Bx⁻0-432 ⟫ = b-Bx⁻0-432
⟪ Bx⁻1-0234 ⟫ = b-Bx⁻1-0234
⟪ Bx⁻1-0243 ⟫ = b-Bx⁻1-0243
⟪ Bx⁻1-0324 ⟫ = b-Bx⁻1-0324
⟪ Bx⁻1-0342 ⟫ = b-Bx⁻1-0342
⟪ Bx⁻1-0423 ⟫ = b-Bx⁻1-0423
⟪ Bx⁻1-0432 ⟫ = b-Bx⁻1-0432
⟪ Bx⁻1-20 ⟫ = b-Bx⁻1-20
⟪ Bx⁻2-13 ⟫ = b-Bx⁻2-13
⟪ Bx⁻1-203 ⟫ = b-Bx⁻1-203
⟪ Bx⁻1-24 ⟫ = b-Bx⁻1-24
⟪ Bx⁻2-134 ⟫ = b-Bx⁻2-134
⟪ Bx⁻1-2034 ⟫ = b-Bx⁻1-2034
⟪ Bx⁻1-23 ⟫ = b-Bx⁻1-23
⟪ Bx⁻2-140 ⟫ = b-Bx⁻2-140
⟪ Bx⁻1-2340 ⟫ = b-Bx⁻1-2340
⟪ Bx⁻2-10 ⟫ = b-Bx⁻2-10
⟪ Bx⁻1-240 ⟫ = b-Bx⁻1-240
⟪ Bx⁻2-103 ⟫ = b-Bx⁻2-103
⟪ Bx⁻1-2403 ⟫ = b-Bx⁻1-2403
⟪ Bx⁻1-34 ⟫ = b-Bx⁻1-34
⟪ Bx⁻3-124 ⟫ = b-Bx⁻3-124
⟪ Bx⁻1-3024 ⟫ = b-Bx⁻1-3024
⟪ Bx⁻1-32 ⟫ = b-Bx⁻1-32
⟪ Bx⁻3-102 ⟫ = b-Bx⁻3-102
⟪ Bx⁻1-3402 ⟫ = b-Bx⁻1-3402
⟪ Bx⁻1-43 ⟫ = b-Bx⁻1-43
⟪ Bx⁻4-123 ⟫ = b-Bx⁻4-123
⟪ Bx⁻1-4023 ⟫ = b-Bx⁻1-4023
⟪ Bx⁻1-42 ⟫ = b-Bx⁻1-42
⟪ Bx⁻4-10 ⟫ = b-Bx⁻4-10
⟪ Bx⁻1-420 ⟫ = b-Bx⁻1-420
⟪ Bx⁻4-103 ⟫ = b-Bx⁻4-103
⟪ Bx⁻1-4203 ⟫ = b-Bx⁻1-4203
⟪ Bx⁻1-430 ⟫ = b-Bx⁻1-430
⟪ Bx⁻4-102 ⟫ = b-Bx⁻4-102
⟪ Bx⁻1-4302 ⟫ = b-Bx⁻1-4302
⟪ Bx⁻2-0134 ⟫ = b-Bx⁻2-0134
⟪ Bx⁻2-0143 ⟫ = b-Bx⁻2-0143
⟪ Bx⁻2-0314 ⟫ = b-Bx⁻2-0314
⟪ Bx⁻2-0341 ⟫ = b-Bx⁻2-0341
⟪ Bx⁻2-0413 ⟫ = b-Bx⁻2-0413
⟪ Bx⁻2-0431 ⟫ = b-Bx⁻2-0431
⟪ Bx⁻2-1340 ⟫ = b-Bx⁻2-1340
⟪ Bx⁻2-1403 ⟫ = b-Bx⁻2-1403
⟪ Bx⁻2-34 ⟫ = b-Bx⁻2-34
⟪ Bx⁻3-214 ⟫ = b-Bx⁻3-214
⟪ Bx⁻2-3014 ⟫ = b-Bx⁻2-3014
⟪ Bx⁻2-43 ⟫ = b-Bx⁻2-43
⟪ Bx⁻4-213 ⟫ = b-Bx⁻4-213
⟪ Bx⁻2-4013 ⟫ = b-Bx⁻2-4013
⟪ Bx⁻4-203 ⟫ = b-Bx⁻4-203
⟪ Bx⁻2-4103 ⟫ = b-Bx⁻2-4103
⟪ Bx⁻3-0124 ⟫ = b-Bx⁻3-0124
⟪ Bx⁻3-0412 ⟫ = b-Bx⁻3-0412
⟪ Bx⁻3-0421 ⟫ = b-Bx⁻3-0421
⟪ Bx⁻4-0123 ⟫ = b-Bx⁻4-0123
⟪ Bx⁻4-0132 ⟫ = b-Bx⁻4-0132
⟪ Bx⁻4-0213 ⟫ = b-Bx⁻4-0213
⟪ Bx⁻4-0231 ⟫ = b-Bx⁻4-0231
⟪ Bx⁻4-0312 ⟫ = b-Bx⁻4-0312
⟪ Bx⁻4-0321 ⟫ = b-Bx⁻4-0321
⟪ Bx⁻4-1230 ⟫ = b-Bx⁻4-1230
⟪ Bx⁻4-1320 ⟫ = b-Bx⁻4-1320
⟪ Sb0-1-2-3 ⟫ = b-Sb0-1-2-3
⟪ Sb0-1-2-4 ⟫ = b-Sb0-1-2-4
⟪ Sb0-1-4-3 ⟫ = b-Sb0-1-4-3
⟪ Sb⁻0-1-4-3 ⟫ = b-Sb⁻0-1-4-3
⟪ Sb0-1-23-4 ⟫ = b-Sb0-1-23-4
⟪ Sb0-1-3-2 ⟫ = b-Sb0-1-3-2
⟪ Sb0-1-3-4 ⟫ = b-Sb0-1-3-4
⟪ Sb0-1-4-2 ⟫ = b-Sb0-1-4-2
⟪ Sb⁻0-1-4-2 ⟫ = b-Sb⁻0-1-4-2
⟪ Sb0-1-32-4 ⟫ = b-Sb0-1-32-4
⟪ Sb⁻0-1-2-4 ⟫ = b-Sb⁻0-1-2-4
⟪ Sb0-1-34-2 ⟫ = b-Sb0-1-34-2
⟪ Sb⁻0-1-3-2 ⟫ = b-Sb⁻0-1-3-2
⟪ Sb0-1-42-3 ⟫ = b-Sb0-1-42-3
⟪ Sb⁻0-1-2-3 ⟫ = b-Sb⁻0-1-2-3
⟪ Sb0-1-43-2 ⟫ = b-Sb0-1-43-2
⟪ Sb0-2-1-3 ⟫ = b-Sb0-2-1-3
⟪ Sb0-2-1-4 ⟫ = b-Sb0-2-1-4
⟪ Sb0-2-4-3 ⟫ = b-Sb0-2-4-3
⟪ Sb⁻0-2-4-3 ⟫ = b-Sb⁻0-2-4-3
⟪ Sb0-2-13-4 ⟫ = b-Sb0-2-13-4
⟪ Sb0-2-3-1 ⟫ = b-Sb0-2-3-1
⟪ Sb0-2-4-1 ⟫ = b-Sb0-2-4-1
⟪ Sb⁻0-2-4-1 ⟫ = b-Sb⁻0-2-4-1
⟪ Sb0-2-31-4 ⟫ = b-Sb0-2-31-4
⟪ Sb⁻0-2-1-4 ⟫ = b-Sb⁻0-2-1-4
⟪ Sb0-2-34-1 ⟫ = b-Sb0-2-34-1
⟪ Sb⁻0-2-3-1 ⟫ = b-Sb⁻0-2-3-1
⟪ Sb0-2-41-3 ⟫ = b-Sb0-2-41-3
⟪ Sb⁻0-2-1-3 ⟫ = b-Sb⁻0-2-1-3
⟪ Sb0-2-43-1 ⟫ = b-Sb0-2-43-1
⟪ Sb0-3-1-2 ⟫ = b-Sb0-3-1-2
⟪ Sb0-3-1-4 ⟫ = b-Sb0-3-1-4
⟪ Sb0-3-4-2 ⟫ = b-Sb0-3-4-2
⟪ Sb⁻0-3-4-2 ⟫ = b-Sb⁻0-3-4-2
⟪ Sb0-3-12-4 ⟫ = b-Sb0-3-12-4
⟪ Sb0-3-2-4 ⟫ = b-Sb0-3-2-4
⟪ Sb⁻0-3-2-4 ⟫ = b-Sb⁻0-3-2-4
⟪ Sb0-3-14-2 ⟫ = b-Sb0-3-14-2
⟪ Sb0-3-2-1 ⟫ = b-Sb0-3-2-1
⟪ Sb0-3-4-1 ⟫ = b-Sb0-3-4-1
⟪ Sb⁻0-3-4-1 ⟫ = b-Sb⁻0-3-4-1
⟪ Sb0-3-21-4 ⟫ = b-Sb0-3-21-4
⟪ Sb⁻0-3-1-4 ⟫ = b-Sb⁻0-3-1-4
⟪ Sb0-3-24-1 ⟫ = b-Sb0-3-24-1
⟪ Sb0-4-1-2 ⟫ = b-Sb0-4-1-2
⟪ Sb0-4-1-3 ⟫ = b-Sb0-4-1-3
⟪ Sb0-4-3-2 ⟫ = b-Sb0-4-3-2
⟪ Sb⁻0-4-3-2 ⟫ = b-Sb⁻0-4-3-2
⟪ Sb0-4-12-3 ⟫ = b-Sb0-4-12-3
⟪ Sb0-4-2-1 ⟫ = b-Sb0-4-2-1
⟪ Sb0-4-3-1 ⟫ = b-Sb0-4-3-1
⟪ Sb⁻0-4-3-1 ⟫ = b-Sb⁻0-4-3-1
⟪ Sb0-4-21-3 ⟫ = b-Sb0-4-21-3
⟪ Sb1-0-2-3 ⟫ = b-Sb1-0-2-3
⟪ Sb1-0-2-4 ⟫ = b-Sb1-0-2-4
⟪ Sb1-0-4-3 ⟫ = b-Sb1-0-4-3
⟪ Sb⁻1-0-4-3 ⟫ = b-Sb⁻1-0-4-3
⟪ Sb1-0-23-4 ⟫ = b-Sb1-0-23-4
⟪ Sb1-0-3-4 ⟫ = b-Sb1-0-3-4
⟪ Sb⁻1-0-3-4 ⟫ = b-Sb⁻1-0-3-4
⟪ Sb1-0-24-3 ⟫ = b-Sb1-0-24-3
⟪ Sb1-0-3-2 ⟫ = b-Sb1-0-3-2
⟪ Sb1-0-4-2 ⟫ = b-Sb1-0-4-2
⟪ Sb⁻1-0-4-2 ⟫ = b-Sb⁻1-0-4-2
⟪ Sb1-0-32-4 ⟫ = b-Sb1-0-32-4
⟪ Sb⁻1-0-2-4 ⟫ = b-Sb⁻1-0-2-4
⟪ Sb1-0-34-2 ⟫ = b-Sb1-0-34-2
⟪ Sb⁻1-0-3-2 ⟫ = b-Sb⁻1-0-3-2
⟪ Sb1-0-42-3 ⟫ = b-Sb1-0-42-3
⟪ Sb⁻1-0-2-3 ⟫ = b-Sb⁻1-0-2-3
⟪ Sb1-0-43-2 ⟫ = b-Sb1-0-43-2
⟪ Sb1-2-0-3 ⟫ = b-Sb1-2-0-3
⟪ Sb1-2-0-4 ⟫ = b-Sb1-2-0-4
⟪ Sb1-2-4-3 ⟫ = b-Sb1-2-4-3
⟪ Sb⁻1-2-4-3 ⟫ = b-Sb⁻1-2-4-3
⟪ Sb1-2-03-4 ⟫ = b-Sb1-2-03-4
⟪ Sb1-2-3-4 ⟫ = b-Sb1-2-3-4
⟪ Sb⁻1-2-3-4 ⟫ = b-Sb⁻1-2-3-4
⟪ Sb1-2-04-3 ⟫ = b-Sb1-2-04-3
⟪ Sb1-2-3-0 ⟫ = b-Sb1-2-3-0
⟪ Sb⁻1-2-0-4 ⟫ = b-Sb⁻1-2-0-4
⟪ Sb1-2-34-0 ⟫ = b-Sb1-2-34-0
⟪ Sb1-2-4-0 ⟫ = b-Sb1-2-4-0
⟪ Sb⁻1-2-3-0 ⟫ = b-Sb⁻1-2-3-0
⟪ Sb1-2-40-3 ⟫ = b-Sb1-2-40-3
⟪ Sb⁻1-2-0-3 ⟫ = b-Sb⁻1-2-0-3
⟪ Sb1-2-43-0 ⟫ = b-Sb1-2-43-0
⟪ Sb1-3-0-4 ⟫ = b-Sb1-3-0-4
⟪ Sb1-3-2-4 ⟫ = b-Sb1-3-2-4
⟪ Sb⁻1-3-2-4 ⟫ = b-Sb⁻1-3-2-4
⟪ Sb1-3-04-2 ⟫ = b-Sb1-3-04-2
⟪ Sb1-3-2-0 ⟫ = b-Sb1-3-2-0
⟪ Sb⁻1-3-0-4 ⟫ = b-Sb⁻1-3-0-4
⟪ Sb1-3-24-0 ⟫ = b-Sb1-3-24-0
⟪ Sb1-3-4-0 ⟫ = b-Sb1-3-4-0
⟪ Sb⁻1-3-2-0 ⟫ = b-Sb⁻1-3-2-0
⟪ Sb1-3-40-2 ⟫ = b-Sb1-3-40-2
⟪ Sb1-4-2-0 ⟫ = b-Sb1-4-2-0
⟪ Sb1-4-3-0 ⟫ = b-Sb1-4-3-0
⟪ Sb⁻1-4-3-0 ⟫ = b-Sb⁻1-4-3-0
⟪ Sb1-4-20-3 ⟫ = b-Sb1-4-20-3
⟪ Sb⁻1-4-2-0 ⟫ = b-Sb⁻1-4-2-0
⟪ Sb1-4-30-2 ⟫ = b-Sb1-4-30-2
⟪ Sb2-0-1-3 ⟫ = b-Sb2-0-1-3
⟪ Sb2-0-1-4 ⟫ = b-Sb2-0-1-4
⟪ Sb2-0-4-3 ⟫ = b-Sb2-0-4-3
⟪ Sb⁻2-0-4-3 ⟫ = b-Sb⁻2-0-4-3
⟪ Sb2-0-13-4 ⟫ = b-Sb2-0-13-4
⟪ Sb2-0-3-4 ⟫ = b-Sb2-0-3-4
⟪ Sb⁻2-0-3-4 ⟫ = b-Sb⁻2-0-3-4
⟪ Sb2-0-14-3 ⟫ = b-Sb2-0-14-3
⟪ Sb2-0-3-1 ⟫ = b-Sb2-0-3-1
⟪ Sb2-0-4-1 ⟫ = b-Sb2-0-4-1
⟪ Sb⁻2-0-4-1 ⟫ = b-Sb⁻2-0-4-1
⟪ Sb2-0-31-4 ⟫ = b-Sb2-0-31-4
⟪ Sb⁻2-0-1-4 ⟫ = b-Sb⁻2-0-1-4
⟪ Sb2-0-34-1 ⟫ = b-Sb2-0-34-1
⟪ Sb⁻2-0-3-1 ⟫ = b-Sb⁻2-0-3-1
⟪ Sb2-0-41-3 ⟫ = b-Sb2-0-41-3
⟪ Sb⁻2-0-1-3 ⟫ = b-Sb⁻2-0-1-3
⟪ Sb2-0-43-1 ⟫ = b-Sb2-0-43-1
⟪ Sb2-1-0-3 ⟫ = b-Sb2-1-0-3
⟪ Sb2-1-0-4 ⟫ = b-Sb2-1-0-4
⟪ Sb2-1-3-0 ⟫ = b-Sb2-1-3-0
⟪ Sb⁻2-1-0-4 ⟫ = b-Sb⁻2-1-0-4
⟪ Sb2-1-34-0 ⟫ = b-Sb2-1-34-0
⟪ Sb2-1-4-0 ⟫ = b-Sb2-1-4-0
⟪ Sb⁻2-1-3-0 ⟫ = b-Sb⁻2-1-3-0
⟪ Sb2-1-40-3 ⟫ = b-Sb2-1-40-3
⟪ Sb⁻2-1-0-3 ⟫ = b-Sb⁻2-1-0-3
⟪ Sb2-1-43-0 ⟫ = b-Sb2-1-43-0
⟪ Sb2-3-0-1 ⟫ = b-Sb2-3-0-1
⟪ Sb2-3-0-4 ⟫ = b-Sb2-3-0-4
⟪ Sb2-3-1-4 ⟫ = b-Sb2-3-1-4
⟪ Sb⁻2-3-1-4 ⟫ = b-Sb⁻2-3-1-4
⟪ Sb2-3-04-1 ⟫ = b-Sb2-3-04-1
⟪ Sb2-3-1-0 ⟫ = b-Sb2-3-1-0
⟪ Sb⁻2-3-0-4 ⟫ = b-Sb⁻2-3-0-4
⟪ Sb2-3-14-0 ⟫ = b-Sb2-3-14-0
⟪ Sb⁻2-3-1-0 ⟫ = b-Sb⁻2-3-1-0
⟪ Sb2-3-40-1 ⟫ = b-Sb2-3-40-1
⟪ Sb⁻2-3-0-1 ⟫ = b-Sb⁻2-3-0-1
⟪ Sb2-3-41-0 ⟫ = b-Sb2-3-41-0
⟪ Sb2-4-0-1 ⟫ = b-Sb2-4-0-1
⟪ Sb2-4-3-1 ⟫ = b-Sb2-4-3-1
⟪ Sb⁻2-4-3-1 ⟫ = b-Sb⁻2-4-3-1
⟪ Sb2-4-01-3 ⟫ = b-Sb2-4-01-3
⟪ Sb2-4-1-0 ⟫ = b-Sb2-4-1-0
⟪ Sb2-4-3-0 ⟫ = b-Sb2-4-3-0
⟪ Sb⁻2-4-3-0 ⟫ = b-Sb⁻2-4-3-0
⟪ Sb2-4-10-3 ⟫ = b-Sb2-4-10-3
⟪ Sb⁻2-4-1-0 ⟫ = b-Sb⁻2-4-1-0
⟪ Sb2-4-30-1 ⟫ = b-Sb2-4-30-1
⟪ Sb⁻2-4-0-1 ⟫ = b-Sb⁻2-4-0-1
⟪ Sb2-4-31-0 ⟫ = b-Sb2-4-31-0
⟪ Sb3-0-1-2 ⟫ = b-Sb3-0-1-2
⟪ Sb3-0-1-4 ⟫ = b-Sb3-0-1-4
⟪ Sb3-0-2-4 ⟫ = b-Sb3-0-2-4
⟪ Sb⁻3-0-2-4 ⟫ = b-Sb⁻3-0-2-4
⟪ Sb3-0-14-2 ⟫ = b-Sb3-0-14-2
⟪ Sb3-0-2-1 ⟫ = b-Sb3-0-2-1
⟪ Sb3-0-4-1 ⟫ = b-Sb3-0-4-1
⟪ Sb⁻3-0-4-1 ⟫ = b-Sb⁻3-0-4-1
⟪ Sb3-0-21-4 ⟫ = b-Sb3-0-21-4
⟪ Sb⁻3-0-1-4 ⟫ = b-Sb⁻3-0-1-4
⟪ Sb3-0-24-1 ⟫ = b-Sb3-0-24-1
⟪ Sb⁻3-0-2-1 ⟫ = b-Sb⁻3-0-2-1
⟪ Sb3-0-41-2 ⟫ = b-Sb3-0-41-2
⟪ Sb⁻3-0-1-2 ⟫ = b-Sb⁻3-0-1-2
⟪ Sb3-0-42-1 ⟫ = b-Sb3-0-42-1
⟪ Sb3-1-0-2 ⟫ = b-Sb3-1-0-2
⟪ Sb3-1-0-4 ⟫ = b-Sb3-1-0-4
⟪ Sb3-1-2-0 ⟫ = b-Sb3-1-2-0
⟪ Sb3-1-4-0 ⟫ = b-Sb3-1-4-0
⟪ Sb⁻3-1-2-0 ⟫ = b-Sb⁻3-1-2-0
⟪ Sb3-1-40-2 ⟫ = b-Sb3-1-40-2
⟪ Sb⁻3-1-0-2 ⟫ = b-Sb⁻3-1-0-2
⟪ Sb3-1-42-0 ⟫ = b-Sb3-1-42-0
⟪ Sb3-2-0-1 ⟫ = b-Sb3-2-0-1
⟪ Sb3-2-1-0 ⟫ = b-Sb3-2-1-0
⟪ Sb⁻3-2-1-0 ⟫ = b-Sb⁻3-2-1-0
⟪ Sb3-2-40-1 ⟫ = b-Sb3-2-40-1
⟪ Sb⁻3-2-0-1 ⟫ = b-Sb⁻3-2-0-1
⟪ Sb3-2-41-0 ⟫ = b-Sb3-2-41-0
⟪ Sb3-4-0-1 ⟫ = b-Sb3-4-0-1
⟪ Sb3-4-0-2 ⟫ = b-Sb3-4-0-2
⟪ Sb3-4-2-1 ⟫ = b-Sb3-4-2-1
⟪ Sb⁻3-4-2-1 ⟫ = b-Sb⁻3-4-2-1
⟪ Sb3-4-01-2 ⟫ = b-Sb3-4-01-2
⟪ Sb3-4-1-0 ⟫ = b-Sb3-4-1-0
⟪ Sb3-4-2-0 ⟫ = b-Sb3-4-2-0
⟪ Sb⁻3-4-2-0 ⟫ = b-Sb⁻3-4-2-0
⟪ Sb3-4-10-2 ⟫ = b-Sb3-4-10-2
⟪ Sb⁻3-4-0-2 ⟫ = b-Sb⁻3-4-0-2
⟪ Sb3-4-12-0 ⟫ = b-Sb3-4-12-0
⟪ Sb⁻3-4-1-0 ⟫ = b-Sb⁻3-4-1-0
⟪ Sb3-4-20-1 ⟫ = b-Sb3-4-20-1
⟪ Sb⁻3-4-0-1 ⟫ = b-Sb⁻3-4-0-1
⟪ Sb3-4-21-0 ⟫ = b-Sb3-4-21-0
⟪ Sb4-0-1-2 ⟫ = b-Sb4-0-1-2
⟪ Sb4-0-1-3 ⟫ = b-Sb4-0-1-3
⟪ Sb4-0-2-1 ⟫ = b-Sb4-0-2-1
⟪ Sb4-0-3-1 ⟫ = b-Sb4-0-3-1
⟪ Sb⁻4-0-3-1 ⟫ = b-Sb⁻4-0-3-1
⟪ Sb4-0-21-3 ⟫ = b-Sb4-0-21-3
⟪ Sb⁻4-0-1-3 ⟫ = b-Sb⁻4-0-1-3
⟪ Sb4-0-23-1 ⟫ = b-Sb4-0-23-1
⟪ Sb⁻4-0-2-1 ⟫ = b-Sb⁻4-0-2-1
⟪ Sb4-0-31-2 ⟫ = b-Sb4-0-31-2
⟪ Sb⁻4-0-1-2 ⟫ = b-Sb⁻4-0-1-2
⟪ Sb4-0-32-1 ⟫ = b-Sb4-0-32-1
⟪ Sb4-1-0-2 ⟫ = b-Sb4-1-0-2
⟪ Sb4-1-0-3 ⟫ = b-Sb4-1-0-3
⟪ Sb4-1-2-0 ⟫ = b-Sb4-1-2-0
⟪ Sb⁻4-1-0-3 ⟫ = b-Sb⁻4-1-0-3
⟪ Sb4-1-23-0 ⟫ = b-Sb4-1-23-0
⟪ Sb4-1-3-0 ⟫ = b-Sb4-1-3-0
⟪ Sb⁻4-1-0-2 ⟫ = b-Sb⁻4-1-0-2
⟪ Sb4-1-32-0 ⟫ = b-Sb4-1-32-0
⟪ Sb4-2-3-0 ⟫ = b-Sb4-2-3-0
⟪ Sb4-3-1-0 ⟫ = b-Sb4-3-1-0
⟪ Sb4-3-2-0 ⟫ = b-Sb4-3-2-0
⟪ Sb⁻0-1-23-4 ⟫ = b-Sb⁻0-1-23-4
⟪ Sb⁻0-1-3-4 ⟫ = b-Sb⁻0-1-3-4
⟪ Sb⁻0-1-32-4 ⟫ = b-Sb⁻0-1-32-4
⟪ Sb⁻0-1-34-2 ⟫ = b-Sb⁻0-1-34-2
⟪ Sb⁻0-1-42-3 ⟫ = b-Sb⁻0-1-42-3
⟪ Sb⁻0-1-43-2 ⟫ = b-Sb⁻0-1-43-2
⟪ Sb⁻0-2-34-1 ⟫ = b-Sb⁻0-2-34-1
⟪ Sb⁻0-2-43-1 ⟫ = b-Sb⁻0-2-43-1
⟪ Sb⁻0-3-1-2 ⟫ = b-Sb⁻0-3-1-2
⟪ Sb⁻0-3-2-1 ⟫ = b-Sb⁻0-3-2-1
⟪ Sb⁻0-4-1-2 ⟫ = b-Sb⁻0-4-1-2
⟪ Sb⁻0-4-1-3 ⟫ = b-Sb⁻0-4-1-3
⟪ Sb⁻0-4-2-1 ⟫ = b-Sb⁻0-4-2-1
⟪ Sb⁻1-0-23-4 ⟫ = b-Sb⁻1-0-23-4
⟪ Sb⁻1-0-24-3 ⟫ = b-Sb⁻1-0-24-3
⟪ Sb⁻1-0-32-4 ⟫ = b-Sb⁻1-0-32-4
⟪ Sb⁻1-0-34-2 ⟫ = b-Sb⁻1-0-34-2
⟪ Sb⁻1-0-42-3 ⟫ = b-Sb⁻1-0-42-3
⟪ Sb⁻1-0-43-2 ⟫ = b-Sb⁻1-0-43-2
⟪ Sb⁻1-2-34-0 ⟫ = b-Sb⁻1-2-34-0
⟪ Sb⁻1-2-4-0 ⟫ = b-Sb⁻1-2-4-0
⟪ Sb⁻1-2-40-3 ⟫ = b-Sb⁻1-2-40-3
⟪ Sb⁻1-3-4-0 ⟫ = b-Sb⁻1-3-4-0
⟪ Sb⁻1-3-4-2 ⟫ = b-Sb⁻1-3-4-2
⟪ Sb⁻1-3-40-2 ⟫ = b-Sb⁻1-3-40-2
⟪ Sb⁻1-4-20-3 ⟫ = b-Sb⁻1-4-20-3
⟪ Sb⁻1-4-30-2 ⟫ = b-Sb⁻1-4-30-2
⟪ Sb⁻2-0-13-4 ⟫ = b-Sb⁻2-0-13-4
⟪ Sb⁻2-0-14-3 ⟫ = b-Sb⁻2-0-14-3
⟪ Sb⁻2-0-31-4 ⟫ = b-Sb⁻2-0-31-4
⟪ Sb⁻2-0-34-1 ⟫ = b-Sb⁻2-0-34-1
⟪ Sb⁻2-0-41-3 ⟫ = b-Sb⁻2-0-41-3
⟪ Sb⁻2-0-43-1 ⟫ = b-Sb⁻2-0-43-1
⟪ Sb⁻2-1-34-0 ⟫ = b-Sb⁻2-1-34-0
⟪ Sb⁻2-1-4-0 ⟫ = b-Sb⁻2-1-4-0
⟪ Sb⁻2-1-40-3 ⟫ = b-Sb⁻2-1-40-3
⟪ Sb⁻2-3-4-0 ⟫ = b-Sb⁻2-3-4-0
⟪ Sb⁻2-3-4-1 ⟫ = b-Sb⁻2-3-4-1
⟪ Sb⁻2-4-01-3 ⟫ = b-Sb⁻2-4-01-3
⟪ Sb⁻2-4-10-3 ⟫ = b-Sb⁻2-4-10-3
⟪ Sb⁻3-0-41-2 ⟫ = b-Sb⁻3-0-41-2
⟪ Sb⁻3-0-42-1 ⟫ = b-Sb⁻3-0-42-1
⟪ Sb⁻3-1-0-4 ⟫ = b-Sb⁻3-1-0-4
⟪ Sb⁻3-1-4-0 ⟫ = b-Sb⁻3-1-4-0
⟪ Sb⁻4-0-23-1 ⟫ = b-Sb⁻4-0-23-1
⟪ Sb⁻4-0-31-2 ⟫ = b-Sb⁻4-0-31-2
⟪ Sb⁻4-0-32-1 ⟫ = b-Sb⁻4-0-32-1
⟪ Sb⁻4-1-2-0 ⟫ = b-Sb⁻4-1-2-0
⟪ Sb⁻4-1-23-0 ⟫ = b-Sb⁻4-1-23-0
⟪ Sb⁻4-1-3-0 ⟫ = b-Sb⁻4-1-3-0
⟪ Sb⁻4-1-32-0 ⟫ = b-Sb⁻4-1-32-0
