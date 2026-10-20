{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D002 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0006 ; wl0018 ; wl0518 ; wl0788 ; wp0135 ; wp0153 ; wp0154 ; wl0288 ; wl0293 ; wl0294 ; wl0415 ; wl0928 ; wl0929 ; wp0130 ; wp0140 ; wp0141 ; wp0162 ; wp0279 ; wp0280 ; wp0765 ; wp0766 ; wp0767 ; wl0004 ; wl0205 ; wp0131 ; wp0216 ; wp0527 ; wp0529 ; wp0812 ; wp0813 ; wl0184 ; wl1044 ; wl1045 ; wl1046 ; wl1047 ; wl1048 ; wl1049 ; wp0847 ; wp0848 ; wl0432 ; wl0433 ; wl1052 ; wl1053 ; wl1054 ; wl1055 ; wl1057 ; wl1058 ; wl1059 ; wl1060 ; wl1061 ; wl1063 ; wl1064 ; wl1067 ; wl1077 ; wl1078 ; wl1079 ; wl1080 ; wl1102 ; wl1103 ; wl1104 ; wl1105 ; wl1106 ; wl1107 ; wl1108 ; wl1109 ; wl1110 ; wl1111 ; wp0019 ; wp0294 ; wp0850 ; wp0851 ; wp0852 ; wp0853 ; wp0854 ; wp0855 ; wp0861 ; wp0862 ; wp0865 ; wp0867 ; wp0868 ; wp0869 ; wp0902 ; wp0903 ; wp0904 ; wl1122 ; wl1123 ; wl1124 ; wl1125 ; wl1126 ; wl1137 ; wl1138 ; wl0231 ; wl1155 ; wp0214 ; wp0528 ; wp0530 ; wp0398 ; wp0551 ; wp0553 ; wp0957 ; wp0958 ; wp0959 ; wp0965 ; wp0966 ; wp0972 ; wp0973 ; wp0992 ; wl0322 ; wl1210 ; wl1211 ; wl1212 ; wl1216 ; wl1217 ; wl1218 ; wl1219 ; wl1231 ; wl1232 ; wp1014 ; wp1015 ; wp1016 ; wp0175 ; wp0176 ; wp0177 ; wp0178 ; wp0273 ; wp0274 ; wl1303 ; wp0262 ; wl0330 ; wl0331 ; wl1319 ; wl0030 ; wl0031 ; wl0063 ; wl0135 ; wl0136 ; wl1340 ; wp0111 ; wp0008)
open import Examples.Groups.Clifford+CS.Five.Chain

-- sym-ab @1331: 18 steps
lem-sym-ab-at1331 : Ws → ⟪ (Bx0-3214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ []) ⟫ʷ
lem-sym-ab-at1331 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-3214 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ Toff023 ∷ CCZ023 ∷ Bx3-014 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff023 ∷ Bx3-014 ∷ Toff023 ∷ CCZ023 ∷ Bx3-014 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ014 ∷ []) (wp0154 c4) ▸
       at 2 1 (CCZ012 ∷ Toff201 ∷ CZ24 ∷ Toff201 ∷ CCZ012 ∷ CZ24 ∷ []) (sym (wp0153 c4)) ▸
       at 4 1 (Bx0-24 ∷ []) (refl) ▸
       at 7 1 (Bx0-24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ Toff023 ∷ CCZ023 ∷ Bx3-014 ∷ []) (CCZ023 ∷ Toff023 ∷ Bx2-014 ∷ Toff023 ∷ CCZ023 ∷ CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ [])
  b1 = at 2 6 (Bx2-014 ∷ []) (refl) ▸
       at 5 1 (CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸
       at 5 6 (CCZ014 ∷ []) (wp0154 c4) ▸
       at 5 1 (CCZ012 ∷ Toff201 ∷ CZ24 ∷ Toff201 ∷ CCZ012 ∷ CZ24 ∷ []) (sym (wp0153 c4)) ▸
       at 7 1 (Bx0-24 ∷ []) (refl) ▸
       at 10 1 (Bx0-24 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ023 ∷ Toff023 ∷ Bx2-014 ∷ Toff023 ∷ CCZ023 ∷ CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) (Bx0-2314 ∷ [])
  b2 = at 5 6 (Bx2-014 ∷ []) (refl) ▸
       at 0 6 (Bx0-2314 ∷ []) (refl) ▸ done

-- sym-ab @0220: 18 steps
lem-sym-ab-at0220 : Ws → ⟪ (Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-sym-ab-at0220 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-1034 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ Toff201 ∷ CCZ012 ∷ Bx1-234 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff201 ∷ Bx1-234 ∷ Toff201 ∷ CCZ012 ∷ Bx1-234 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wl0518 (lit c4)) ▸
       at 2 1 (CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (sym (wp0280 c4)) ▸
       at 4 1 (Bx2-04 ∷ []) (refl) ▸
       at 7 1 (Bx2-04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff201 ∷ CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ Toff201 ∷ CCZ012 ∷ Bx1-234 ∷ []) (CCZ012 ∷ Toff201 ∷ Bx0-234 ∷ Toff201 ∷ CCZ012 ∷ CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ [])
  b1 = at 2 6 (Bx0-234 ∷ []) (refl) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸
       at 5 6 (CCZ234 ∷ []) (wl0518 (lit c4)) ▸
       at 5 1 (CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (sym (wp0280 c4)) ▸
       at 7 1 (Bx2-04 ∷ []) (refl) ▸
       at 10 1 (Bx2-04 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ012 ∷ Toff201 ∷ Bx0-234 ∷ Toff201 ∷ CCZ012 ∷ CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ []) (Bx2-0134 ∷ [])
  b2 = at 5 6 (Bx0-234 ∷ []) (refl) ▸
       at 0 6 (Bx2-0134 ∷ []) (refl) ▸ done

-- sym-ab @14233241: 18 steps
lem-sym-ab-at14233241 : Ws → ⟪ (Bx0-4321 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ []) ⟫ʷ
lem-sym-ab-at14233241 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-4321 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ Toff034 ∷ CCZ034 ∷ Bx4-021 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx4-021 ∷ Toff034 ∷ CCZ034 ∷ Bx4-021 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wp0162 c4)) ▸
       at 2 1 (CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ []) (wl0288 (lit c4)) ▸
       at 4 1 (Bx0-31 ∷ []) (refl) ▸
       at 7 1 (Bx0-31 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ Toff034 ∷ CCZ034 ∷ Bx4-021 ∷ []) (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ CCZ034 ∷ CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ [])
  b1 = at 2 6 (Bx3-021 ∷ []) (refl) ▸
       at 5 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸
       at 5 6 (CCZ012 ∷ []) (sym (wp0162 c4)) ▸
       at 5 1 (CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ []) (wl0288 (lit c4)) ▸
       at 7 1 (Bx0-31 ∷ []) (refl) ▸
       at 10 1 (Bx0-31 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ CCZ034 ∷ CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) (Bx0-3421 ∷ [])
  b2 = at 5 6 (Bx3-021 ∷ []) (refl) ▸
       at 0 6 (Bx0-3421 ∷ []) (refl) ▸ done

-- sym-ab @021021: 18 steps
lem-sym-ab-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ []) ⟫ʷ
lem-sym-ab-at021021 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-0134 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ Toff201 ∷ CCZ012 ∷ Bx0-234 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff201 ∷ Bx0-234 ∷ Toff201 ∷ CCZ012 ∷ Bx0-234 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wp0280 c4) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (sym (wl0518 (lit c4))) ▸
       at 4 1 (Bx2-14 ∷ []) (refl) ▸
       at 7 1 (Bx2-14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff201 ∷ CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ Toff201 ∷ CCZ012 ∷ Bx0-234 ∷ []) (CCZ012 ∷ Toff201 ∷ Bx1-234 ∷ Toff201 ∷ CCZ012 ∷ CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ [])
  b1 = at 2 6 (Bx1-234 ∷ []) (refl) ▸
       at 5 1 (CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸
       at 5 6 (CCZ234 ∷ []) (wp0280 c4) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (sym (wl0518 (lit c4))) ▸
       at 7 1 (Bx2-14 ∷ []) (refl) ▸
       at 10 1 (Bx2-14 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ012 ∷ Toff201 ∷ Bx1-234 ∷ Toff201 ∷ CCZ012 ∷ CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) (Bx2-1034 ∷ [])
  b2 = at 5 6 (Bx1-234 ∷ []) (refl) ▸
       at 0 6 (Bx2-1034 ∷ []) (refl) ▸ done

-- cQ @0220: 7 steps
lem-cQ-at0220 : Ws → ⟪ (CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ
lem-cQ-at0220 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4)) ▸
       at 4 2 (CCZ234 ∷ CS12 ∷ []) (sym (wl0415 (lit c4))) ▸
       at 3 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CS02⁻ ∷ []) (sym (wp0765 c4)) ▸
       at 1 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 0 2 (CCZ234 ∷ CS02 ∷ []) (sym (wp0279 c4)) ▸
       at 1 5 (CCZ012 ∷ []) (sym (wl0929 (lit c4))) ▸ done

-- cQ @0213243140: 7 steps
lem-cQ-at0213243140 : Ws → ⟪ (CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ
lem-cQ-at0213243140 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ234 ∷ [])
  b0 = at 0 1 (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) (wl0293 (lit c4)) ▸
       at 4 2 (CCZ012 ∷ CS23 ∷ []) (sym (wl0294 (lit c4))) ▸
       at 3 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 2 2 (CCZ012 ∷ CS24⁻ ∷ []) (sym (wp0140 c4)) ▸
       at 1 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 0 2 (CCZ012 ∷ CS24 ∷ []) (sym (wp0141 c4)) ▸
       at 1 5 (CCZ234 ∷ []) (sym (wl0293 (lit c4))) ▸ done

-- sym-ab @0213213440: 18 steps
lem-sym-ab-at0213213440 : Ws → ⟪ (Bx2-3140 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ []) ⟫ʷ
lem-sym-ab-at0213213440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-3140 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ Toff213 ∷ CCZ123 ∷ Bx3-240 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff213 ∷ Bx3-240 ∷ Toff213 ∷ CCZ123 ∷ Bx3-240 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (sym (wp0766 c4)) ▸
       at 2 1 (CCZ124 ∷ Toff124 ∷ CZ01 ∷ Toff124 ∷ CCZ124 ∷ CZ01 ∷ []) (wp0767 c4) ▸
       at 4 1 (Bx2-10 ∷ []) (refl) ▸
       at 7 1 (Bx2-10 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff213 ∷ CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ Toff213 ∷ CCZ123 ∷ Bx3-240 ∷ []) (CCZ123 ∷ Toff213 ∷ Bx1-240 ∷ Toff213 ∷ CCZ123 ∷ CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ [])
  b1 = at 2 6 (Bx1-240 ∷ []) (refl) ▸
       at 5 1 (CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸
       at 5 6 (CCZ024 ∷ []) (sym (wp0766 c4)) ▸
       at 5 1 (CCZ124 ∷ Toff124 ∷ CZ01 ∷ Toff124 ∷ CCZ124 ∷ CZ01 ∷ []) (wp0767 c4) ▸
       at 7 1 (Bx2-10 ∷ []) (refl) ▸
       at 10 1 (Bx2-10 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ123 ∷ Toff213 ∷ Bx1-240 ∷ Toff213 ∷ CCZ123 ∷ CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ []) (Bx2-1340 ∷ [])
  b2 = at 5 6 (Bx1-240 ∷ []) (refl) ▸
       at 0 6 (Bx2-1340 ∷ []) (refl) ▸ done

-- sym-ab @02233440: 18 steps
lem-sym-ab-at02233440 : Ws → ⟪ (Bx2-1340 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ []) ⟫ʷ
lem-sym-ab-at02233440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-1340 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ Toff213 ∷ CCZ123 ∷ Bx1-240 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff213 ∷ Bx1-240 ∷ Toff213 ∷ CCZ123 ∷ Bx1-240 ∷ []) (refl) ▸
       at 2 1 (CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (sym (wp0767 c4)) ▸
       at 2 1 (CCZ234 ∷ Toff324 ∷ CZ03 ∷ Toff324 ∷ CCZ234 ∷ CZ03 ∷ []) (wp0766 c4) ▸
       at 4 1 (Bx2-30 ∷ []) (refl) ▸
       at 7 1 (Bx2-30 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff213 ∷ CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ Toff213 ∷ CCZ123 ∷ Bx1-240 ∷ []) (CCZ123 ∷ Toff213 ∷ Bx3-240 ∷ Toff213 ∷ CCZ123 ∷ CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ [])
  b1 = at 2 6 (Bx3-240 ∷ []) (refl) ▸
       at 5 1 (CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸
       at 5 6 (CCZ024 ∷ []) (sym (wp0767 c4)) ▸
       at 5 1 (CCZ234 ∷ Toff324 ∷ CZ03 ∷ Toff324 ∷ CCZ234 ∷ CZ03 ∷ []) (wp0766 c4) ▸
       at 7 1 (Bx2-30 ∷ []) (refl) ▸
       at 10 1 (Bx2-30 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ123 ∷ Toff213 ∷ Bx3-240 ∷ Toff213 ∷ CCZ123 ∷ CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ []) (Bx2-3140 ∷ [])
  b2 = at 5 6 (Bx3-240 ∷ []) (refl) ▸
       at 0 6 (Bx2-3140 ∷ []) (refl) ▸ done

-- nat-SWbc @12233441: 23 steps
lem-nat-SWbc-at12233441 : Ws → ⟪ (Sw34 ∷ Bx0-2341 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-nat-SWbc-at12233441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw34 ∷ Bx0-2341 ∷ Sw34 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ Sw34 ∷ CCZ024 ∷ Bx0-21 ∷ Toff023 ∷ CCZ023 ∷ Bx2-041 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-041 ∷ Toff023 ∷ CCZ023 ∷ Bx2-041 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw34 ∷ []) (sym (wp0529 c4)) ▸
       at 1 2 (Toff024 ∷ Sw34 ∷ []) (wp0812 c4) ▸
       at 3 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) (refl) ▸
       at 2 2 (CCZ023 ∷ Sw34 ∷ []) (sym (wp0527 c4)) ▸
       at 3 2 (Toff203 ∷ Sw34 ∷ []) (wp0813 c4) ▸
       at 4 2 (Bx0-21 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 5 2 (Toff203 ∷ Sw34 ∷ []) (wp0813 c4) ▸ done

  b1 : Chain (CCZ024 ∷ Toff024 ∷ CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ Sw34 ∷ CCZ024 ∷ Bx0-21 ∷ Toff023 ∷ CCZ023 ∷ Bx2-041 ∷ Sw34 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ Toff024 ∷ CCZ024 ∷ CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Sw34 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ Sw34 ∷ [])
  b1 = at 6 2 (CCZ023 ∷ Sw34 ∷ []) (sym (wp0527 c4)) ▸
       at 7 2 (Bx0-21 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 8 2 (Toff024 ∷ Sw34 ∷ []) (wp0812 c4) ▸
       at 9 2 (CCZ024 ∷ Sw34 ∷ []) (sym (wp0529 c4)) ▸
       at 11 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) (refl) ▸
       at 10 2 (CCZ023 ∷ Sw34 ∷ []) (sym (wp0527 c4)) ▸
       at 11 2 (Toff203 ∷ Sw34 ∷ []) (wp0813 c4) ▸
       at 12 2 (Bx0-21 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸ done

  b2 : Chain (CCZ024 ∷ Toff024 ∷ CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ Toff024 ∷ CCZ024 ∷ CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Sw34 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ Sw34 ∷ []) (Bx0-2431 ∷ [])
  b2 = at 13 2 (Toff203 ∷ Sw34 ∷ []) (wp0813 c4) ▸
       at 14 2 (CCZ023 ∷ Sw34 ∷ []) (sym (wp0527 c4)) ▸
       at 15 2 (Bx0-21 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 16 2 [] (wl0004 (lit c4)) ▸
       at 2 6 (Bx2-031 ∷ []) (refl) ▸
       at 5 6 (Bx2-031 ∷ []) (refl) ▸
       at 0 6 (Bx0-2431 ∷ []) (refl) ▸ done

-- sym-ab @14213243: 18 steps
lem-sym-ab-at14213243 : Ws → ⟪ (Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-sym-ab-at14213243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-4123 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ Toff014 ∷ CCZ014 ∷ Bx4-023 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff014 ∷ Bx4-023 ∷ Toff014 ∷ CCZ014 ∷ Bx4-023 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wp0216 c4)) ▸
       at 2 1 (CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (sym (wl0205 (lit c4))) ▸
       at 4 1 (Bx0-13 ∷ []) (refl) ▸
       at 7 1 (Bx0-13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ Toff014 ∷ CCZ014 ∷ Bx4-023 ∷ []) (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ [])
  b1 = at 2 6 (Bx1-023 ∷ []) (refl) ▸
       at 5 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸
       at 5 6 (CCZ023 ∷ []) (sym (wp0216 c4)) ▸
       at 5 1 (CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (sym (wl0205 (lit c4))) ▸
       at 7 1 (Bx0-13 ∷ []) (refl) ▸
       at 10 1 (Bx0-13 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (Bx0-1423 ∷ [])
  b2 = at 5 6 (Bx1-023 ∷ []) (refl) ▸
       at 0 6 (Bx0-1423 ∷ []) (refl) ▸ done

-- sym-ab @132132: 18 steps
lem-sym-ab-at132132 : Ws → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ []) ⟫ʷ
lem-sym-ab-at132132 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-3124 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ Toff013 ∷ CCZ013 ∷ Bx3-024 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff013 ∷ Bx3-024 ∷ Toff013 ∷ CCZ013 ∷ Bx3-024 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (wp0131 c4) ▸
       at 2 1 (CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) (sym (wp0130 c4)) ▸
       at 4 1 (Bx0-14 ∷ []) (refl) ▸
       at 7 1 (Bx0-14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ Toff013 ∷ CCZ013 ∷ Bx3-024 ∷ []) (CCZ013 ∷ Toff013 ∷ Bx1-024 ∷ Toff013 ∷ CCZ013 ∷ CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ [])
  b1 = at 2 6 (Bx1-024 ∷ []) (refl) ▸
       at 5 1 (CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸
       at 5 6 (CCZ024 ∷ []) (wp0131 c4) ▸
       at 5 1 (CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) (sym (wp0130 c4)) ▸
       at 7 1 (Bx0-14 ∷ []) (refl) ▸
       at 10 1 (Bx0-14 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ013 ∷ Toff013 ∷ Bx1-024 ∷ Toff013 ∷ CCZ013 ∷ CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) (Bx0-1324 ∷ [])
  b2 = at 5 6 (Bx1-024 ∷ []) (refl) ▸
       at 0 6 (Bx0-1324 ∷ []) (refl) ▸ done

-- F2-I-S0: 1 steps
lem-F2-I-S0 : Ws → ⟪ (S4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-S0 c4 = run b0
  where
  b0 : Chain (S4 ∷ CS04 ∷ []) (CS04 ∷ S4 ∷ [])
  b0 = at 0 2 (CS04 ∷ S4 ∷ []) (sym (wp0847 c4)) ▸ done

-- F2-I-S1: 1 steps
lem-F2-I-S1 : Ws → ⟪ (S4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-S1 c4 = run b0
  where
  b0 : Chain (S4 ∷ CS14 ∷ []) (CS14 ∷ S4 ∷ [])
  b0 = at 0 2 (CS14 ∷ S4 ∷ []) (sym (wl1044 (lit c4))) ▸ done

-- F2-I-S2: 1 steps
lem-F2-I-S2 : Ws → ⟪ (S4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-S2 c4 = run b0
  where
  b0 : Chain (S4 ∷ CS24 ∷ []) (CS24 ∷ S4 ∷ [])
  b0 = at 0 2 (CS24 ∷ S4 ∷ []) (sym (wl1045 (lit c4))) ▸ done

-- F2-I-S3: 1 steps
lem-F2-I-S3 : Ws → ⟪ (S4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-S3 c4 = run b0
  where
  b0 : Chain (S4 ∷ CS34 ∷ []) (CS34 ∷ S4 ∷ [])
  b0 = at 0 2 (CS34 ∷ S4 ∷ []) (sym (wl1046 (lit c4))) ▸ done

-- F2-I-K0: 1 steps
lem-F2-I-K0 : Ws → ⟪ (S4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-K0 c4 = run b0
  where
  b0 : Chain (S4 ∷ CK40 ∷ []) (CK40 ∷ S4 ∷ [])
  b0 = at 0 2 (CK40 ∷ S4 ∷ []) (sym (wp0848 c4)) ▸ done

-- F2-I-K1: 1 steps
lem-F2-I-K1 : Ws → ⟪ (S4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-K1 c4 = run b0
  where
  b0 : Chain (S4 ∷ CK41 ∷ []) (CK41 ∷ S4 ∷ [])
  b0 = at 0 2 (CK41 ∷ S4 ∷ []) (sym (wl1047 (lit c4))) ▸ done

-- F2-I-K2: 1 steps
lem-F2-I-K2 : Ws → ⟪ (S4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-K2 c4 = run b0
  where
  b0 : Chain (S4 ∷ CK42 ∷ []) (CK42 ∷ S4 ∷ [])
  b0 = at 0 2 (CK42 ∷ S4 ∷ []) (sym (wl1048 (lit c4))) ▸ done

-- F2-I-K3: 1 steps
lem-F2-I-K3 : Ws → ⟪ (S4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-K3 c4 = run b0
  where
  b0 : Chain (S4 ∷ CK43 ∷ []) (CK43 ∷ S4 ∷ [])
  b0 = at 0 2 (CK43 ∷ S4 ∷ []) (sym (wl1049 (lit c4))) ▸ done

-- F2-S0-S1: 1 steps
lem-F2-S0-S1 : Ws → ⟪ (CS04 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0-S1 c4 = run b0
  where
  b0 : Chain (CS04 ∷ CS14 ∷ []) (CS14 ∷ CS04 ∷ [])
  b0 = at 0 2 (CS14 ∷ CS04 ∷ []) (wp0850 c4) ▸ done

-- F2-S0-S2: 1 steps
lem-F2-S0-S2 : Ws → ⟪ (CS04 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0-S2 c4 = run b0
  where
  b0 : Chain (CS04 ∷ CS24 ∷ []) (CS24 ∷ CS04 ∷ [])
  b0 = at 0 2 (CS24 ∷ CS04 ∷ []) (wp0851 c4) ▸ done

-- F2-S0-S3: 1 steps
lem-F2-S0-S3 : Ws → ⟪ (CS04 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0-S3 c4 = run b0
  where
  b0 : Chain (CS04 ∷ CS34 ∷ []) (CS34 ∷ CS04 ∷ [])
  b0 = at 0 2 (CS34 ∷ CS04 ∷ []) (wp0852 c4) ▸ done

-- F2-S0-K1: 1 steps
lem-F2-S0-K1 : Ws → ⟪ (CS04 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0-K1 c4 = run b0
  where
  b0 : Chain (CS04 ∷ CK41 ∷ []) (CK41 ∷ CS04 ∷ [])
  b0 = at 0 2 (CK41 ∷ CS04 ∷ []) (sym (wp0853 c4)) ▸ done

-- F2-S0-K2: 1 steps
lem-F2-S0-K2 : Ws → ⟪ (CS04 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0-K2 c4 = run b0
  where
  b0 : Chain (CS04 ∷ CK42 ∷ []) (CK42 ∷ CS04 ∷ [])
  b0 = at 0 2 (CK42 ∷ CS04 ∷ []) (sym (wp0854 c4)) ▸ done

-- F2-S0-K3: 1 steps
lem-F2-S0-K3 : Ws → ⟪ (CS04 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0-K3 c4 = run b0
  where
  b0 : Chain (CS04 ∷ CK43 ∷ []) (CK43 ∷ CS04 ∷ [])
  b0 = at 0 2 (CK43 ∷ CS04 ∷ []) (sym (wp0855 c4)) ▸ done

-- F2-S1-S2: 1 steps
lem-F2-S1-S2 : Ws → ⟪ (CS14 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CS14 ∷ []) ⟫ʷ
lem-F2-S1-S2 c4 = run b0
  where
  b0 : Chain (CS14 ∷ CS24 ∷ []) (CS24 ∷ CS14 ∷ [])
  b0 = at 0 2 (CS24 ∷ CS14 ∷ []) (wl1052 (lit c4)) ▸ done

-- F2-S1-S3: 1 steps
lem-F2-S1-S3 : Ws → ⟪ (CS14 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CS14 ∷ []) ⟫ʷ
lem-F2-S1-S3 c4 = run b0
  where
  b0 : Chain (CS14 ∷ CS34 ∷ []) (CS34 ∷ CS14 ∷ [])
  b0 = at 0 2 (CS34 ∷ CS14 ∷ []) (wl1053 (lit c4)) ▸ done

-- F2-S1-K0: 1 steps
lem-F2-S1-K0 : Ws → ⟪ (CS14 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CS14 ∷ []) ⟫ʷ
lem-F2-S1-K0 c4 = run b0
  where
  b0 : Chain (CS14 ∷ CK40 ∷ []) (CK40 ∷ CS14 ∷ [])
  b0 = at 0 2 (CK40 ∷ CS14 ∷ []) (sym (wp0861 c4)) ▸ done

-- F2-S1-K2: 1 steps
lem-F2-S1-K2 : Ws → ⟪ (CS14 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CS14 ∷ []) ⟫ʷ
lem-F2-S1-K2 c4 = run b0
  where
  b0 : Chain (CS14 ∷ CK42 ∷ []) (CK42 ∷ CS14 ∷ [])
  b0 = at 0 2 (CK42 ∷ CS14 ∷ []) (sym (wl1054 (lit c4))) ▸ done

-- F2-S1-K3: 1 steps
lem-F2-S1-K3 : Ws → ⟪ (CS14 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CS14 ∷ []) ⟫ʷ
lem-F2-S1-K3 c4 = run b0
  where
  b0 : Chain (CS14 ∷ CK43 ∷ []) (CK43 ∷ CS14 ∷ [])
  b0 = at 0 2 (CK43 ∷ CS14 ∷ []) (sym (wl1055 (lit c4))) ▸ done

-- F2-S2-S3: 1 steps
lem-F2-S2-S3 : Ws → ⟪ (CS24 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CS24 ∷ []) ⟫ʷ
lem-F2-S2-S3 c4 = run b0
  where
  b0 : Chain (CS24 ∷ CS34 ∷ []) (CS34 ∷ CS24 ∷ [])
  b0 = at 0 2 (CS34 ∷ CS24 ∷ []) (wl1057 (lit c4)) ▸ done

-- F2-S2-K0: 1 steps
lem-F2-S2-K0 : Ws → ⟪ (CS24 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CS24 ∷ []) ⟫ʷ
lem-F2-S2-K0 c4 = run b0
  where
  b0 : Chain (CS24 ∷ CK40 ∷ []) (CK40 ∷ CS24 ∷ [])
  b0 = at 0 2 (CK40 ∷ CS24 ∷ []) (sym (wp0862 c4)) ▸ done

-- F2-S2-K1: 1 steps
lem-F2-S2-K1 : Ws → ⟪ (CS24 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CS24 ∷ []) ⟫ʷ
lem-F2-S2-K1 c4 = run b0
  where
  b0 : Chain (CS24 ∷ CK41 ∷ []) (CK41 ∷ CS24 ∷ [])
  b0 = at 0 2 (CK41 ∷ CS24 ∷ []) (sym (wl1058 (lit c4))) ▸ done

-- F2-S2-K3: 1 steps
lem-F2-S2-K3 : Ws → ⟪ (CS24 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CS24 ∷ []) ⟫ʷ
lem-F2-S2-K3 c4 = run b0
  where
  b0 : Chain (CS24 ∷ CK43 ∷ []) (CK43 ∷ CS24 ∷ [])
  b0 = at 0 2 (CK43 ∷ CS24 ∷ []) (sym (wl1059 (lit c4))) ▸ done

-- F2-S3-K0: 1 steps
lem-F2-S3-K0 : Ws → ⟪ (CS34 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CS34 ∷ []) ⟫ʷ
lem-F2-S3-K0 c4 = run b0
  where
  b0 : Chain (CS34 ∷ CK40 ∷ []) (CK40 ∷ CS34 ∷ [])
  b0 = at 0 2 (CK40 ∷ CS34 ∷ []) (sym (wp0865 c4)) ▸ done

-- F2-S3-K1: 1 steps
lem-F2-S3-K1 : Ws → ⟪ (CS34 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CS34 ∷ []) ⟫ʷ
lem-F2-S3-K1 c4 = run b0
  where
  b0 : Chain (CS34 ∷ CK41 ∷ []) (CK41 ∷ CS34 ∷ [])
  b0 = at 0 2 (CK41 ∷ CS34 ∷ []) (sym (wl1060 (lit c4))) ▸ done

-- F2-S3-K2: 1 steps
lem-F2-S3-K2 : Ws → ⟪ (CS34 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CS34 ∷ []) ⟫ʷ
lem-F2-S3-K2 c4 = run b0
  where
  b0 : Chain (CS34 ∷ CK42 ∷ []) (CK42 ∷ CS34 ∷ [])
  b0 = at 0 2 (CK42 ∷ CS34 ∷ []) (sym (wl1061 (lit c4))) ▸ done

-- F2-K0-K1: 1 steps
lem-F2-K0-K1 : Ws → ⟪ (CK40 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CK40 ∷ []) ⟫ʷ
lem-F2-K0-K1 c4 = run b0
  where
  b0 : Chain (CK40 ∷ CK41 ∷ []) (CK41 ∷ CK40 ∷ [])
  b0 = at 0 2 (CK41 ∷ CK40 ∷ []) (wp0867 c4) ▸ done

-- F2-K0-K2: 1 steps
lem-F2-K0-K2 : Ws → ⟪ (CK40 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CK40 ∷ []) ⟫ʷ
lem-F2-K0-K2 c4 = run b0
  where
  b0 : Chain (CK40 ∷ CK42 ∷ []) (CK42 ∷ CK40 ∷ [])
  b0 = at 0 2 (CK42 ∷ CK40 ∷ []) (wp0868 c4) ▸ done

-- F2-K0-K3: 1 steps
lem-F2-K0-K3 : Ws → ⟪ (CK40 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CK40 ∷ []) ⟫ʷ
lem-F2-K0-K3 c4 = run b0
  where
  b0 : Chain (CK40 ∷ CK43 ∷ []) (CK43 ∷ CK40 ∷ [])
  b0 = at 0 2 (CK43 ∷ CK40 ∷ []) (wp0869 c4) ▸ done

-- F2-K1-K2: 1 steps
lem-F2-K1-K2 : Ws → ⟪ (CK41 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CK41 ∷ []) ⟫ʷ
lem-F2-K1-K2 c4 = run b0
  where
  b0 : Chain (CK41 ∷ CK42 ∷ []) (CK42 ∷ CK41 ∷ [])
  b0 = at 0 2 (CK42 ∷ CK41 ∷ []) (wl1063 (lit c4)) ▸ done

-- F2-K1-K3: 1 steps
lem-F2-K1-K3 : Ws → ⟪ (CK41 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CK41 ∷ []) ⟫ʷ
lem-F2-K1-K3 c4 = run b0
  where
  b0 : Chain (CK41 ∷ CK43 ∷ []) (CK43 ∷ CK41 ∷ [])
  b0 = at 0 2 (CK43 ∷ CK41 ∷ []) (wl1064 (lit c4)) ▸ done

-- F2-K2-K3: 1 steps
lem-F2-K2-K3 : Ws → ⟪ (CK42 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CK42 ∷ []) ⟫ʷ
lem-F2-K2-K3 c4 = run b0
  where
  b0 : Chain (CK42 ∷ CK43 ∷ []) (CK43 ∷ CK42 ∷ [])
  b0 = at 0 2 (CK43 ∷ CK42 ∷ []) (wl1067 (lit c4)) ▸ done

-- inv-SBOX(2;0;41;3): 30 steps
lem-inv-SBOX⟨2·0·41·3⟩ : Ws → ⟪ (Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-inv-SBOX⟨2·0·41·3⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ CS03⁻ ∷ Toff314 ∷ Bx⁻2-0413 ∷ [])
  b0 = at 0 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 4 1 (CS03⁻ ∷ []) (refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 4 2 [] (wl1077 (lit c4)) ▸
       at 3 2 [] (wl0788 (lit c4)) ▸
       at 2 1 (CS03 ∷ []) (refl) ▸
       at 3 1 (CS03⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ CS03⁻ ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ [])
  b1 = at 2 2 [] (wl1078 (lit c4)) ▸
       at 1 2 [] (wl0788 (lit c4)) ▸
       at 0 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (refl) ▸
       at 6 1 (Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) (refl) ▸
       at 5 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸
       at 11 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ [])
  b2 = at 11 1 (CZ03 ∷ []) (refl) ▸
       at 14 1 (CZ03 ∷ []) (refl) ▸
       at 5 12 [] (wl1079 (lit c4)) ▸
       at 4 2 [] (wp0135 c4) ▸
       at 3 2 [] (wp0019 c4) ▸
       at 2 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸ done

  b3 : Chain (CCZ024 ∷ Toff204 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) []
  b3 = at 8 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 8 1 (CZ03 ∷ []) (refl) ▸
       at 11 1 (CZ03 ∷ []) (refl) ▸
       at 2 12 [] (wl1079 (lit c4)) ▸
       at 1 2 [] (wp0019 c4) ▸
       at 0 2 [] (wp0135 c4) ▸ done

-- invr-SBOX(2;0;41;3): 30 steps
lem-invr-SBOX⟨2·0·41·3⟩ : Ws → ⟪ (Sb⁻2-0-41-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-invr-SBOX⟨2·0·41·3⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb⁻2-0-41-3 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b0 = at 0 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 5 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) (refl) ▸
       at 10 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (refl) ▸
       at 9 2 [] (wp0135 c4) ▸
       at 8 2 [] (wp0019 c4) ▸
       at 7 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸ done

  b1 : Chain (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b1 = at 10 1 (CZ03 ∷ []) (refl) ▸
       at 13 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 15 1 (CZ03 ∷ []) (refl) ▸
       at 18 1 (CZ03 ∷ []) (refl) ▸
       at 7 12 [] (wl1080 (lit c4)) ▸
       at 6 2 [] (wp0019 c4) ▸
       at 5 2 [] (wp0135 c4) ▸
       at 4 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸ done

  b2 : Chain (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b2 = at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 12 1 (CZ03 ∷ []) (refl) ▸
       at 15 1 (CZ03 ∷ []) (refl) ▸
       at 4 12 [] (wl1080 (lit c4)) ▸
       at 3 2 [] (wl0788 (lit c4)) ▸
       at 2 1 (CS03⁻ ∷ []) (refl) ▸ done

  b3 : Chain (Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) []
  b3 = at 3 1 (CS03 ∷ []) (refl) ▸
       at 2 2 [] (wl1077 (lit c4)) ▸
       at 1 2 [] (wl0788 (lit c4)) ▸
       at 0 1 (CS03 ∷ []) (refl) ▸
       at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 [] (wl1078 (lit c4)) ▸ done

-- F1-order-I@0: 1 steps
lem-F1-order-Iat0 : Ws → ⟪ (S4 ∷ S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-Iat0 c4 = run b0
  where
  b0 : Chain (S4 ∷ S4 ∷ S4 ∷ S4 ∷ []) []
  b0 = at 0 4 [] (wl1102 (lit c4)) ▸ done

-- F1-order-S@0: 1 steps
lem-F1-order-Sat0 : Ws → ⟪ (CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-Sat0 c4 = run b0
  where
  b0 : Chain (CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) []
  b0 = at 0 4 [] (wp0902 c4) ▸ done

-- F1-order-S@1: 1 steps
lem-F1-order-Sat1 : Ws → ⟪ (CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-Sat1 c4 = run b0
  where
  b0 : Chain (CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) []
  b0 = at 0 4 [] (wl1103 (lit c4)) ▸ done

-- F1-order-S@2: 1 steps
lem-F1-order-Sat2 : Ws → ⟪ (CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-Sat2 c4 = run b0
  where
  b0 : Chain (CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) []
  b0 = at 0 4 [] (wl1104 (lit c4)) ▸ done

-- F1-order-S@3: 1 steps
lem-F1-order-Sat3 : Ws → ⟪ (CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-Sat3 c4 = run b0
  where
  b0 : Chain (CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) []
  b0 = at 0 4 [] (wl1105 (lit c4)) ▸ done

-- F1-order-K@0: 1 steps
lem-F1-order-Kat0 : Ws → ⟪ (CK40 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
lem-F1-order-Kat0 c4 = run b0
  where
  b0 : Chain (CK40 ∷ CK40 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
  b0 = at 0 2 (S4 ∷ S4 ∷ S4 ∷ []) (wp0903 c4) ▸ done

-- F1-order-K@1: 1 steps
lem-F1-order-Kat1 : Ws → ⟪ (CK41 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
lem-F1-order-Kat1 c4 = run b0
  where
  b0 : Chain (CK41 ∷ CK41 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
  b0 = at 0 2 (S4 ∷ S4 ∷ S4 ∷ []) (wl1106 (lit c4)) ▸ done

-- F1-order-K@2: 1 steps
lem-F1-order-Kat2 : Ws → ⟪ (CK42 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
lem-F1-order-Kat2 c4 = run b0
  where
  b0 : Chain (CK42 ∷ CK42 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
  b0 = at 0 2 (S4 ∷ S4 ∷ S4 ∷ []) (wl1107 (lit c4)) ▸ done

-- F1-order-K@3: 1 steps
lem-F1-order-Kat3 : Ws → ⟪ (CK43 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
lem-F1-order-Kat3 c4 = run b0
  where
  b0 : Chain (CK43 ∷ CK43 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
  b0 = at 0 2 (S4 ∷ S4 ∷ S4 ∷ []) (wl1108 (lit c4)) ▸ done

-- F1-order-SK@0: 1 steps
lem-F1-order-SKat0 : Ws → ⟪ (CS04 ∷ CK40 ∷ CS04 ∷ CK40 ∷ CS04 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
lem-F1-order-SKat0 c4 = run b0
  where
  b0 : Chain (CS04 ∷ CK40 ∷ CS04 ∷ CK40 ∷ CS04 ∷ CK40 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
  b0 = at 0 6 (S4 ∷ S4 ∷ S4 ∷ []) (wp0904 c4) ▸ done

-- F1-order-SK@1: 1 steps
lem-F1-order-SKat1 : Ws → ⟪ (CS14 ∷ CK41 ∷ CS14 ∷ CK41 ∷ CS14 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
lem-F1-order-SKat1 c4 = run b0
  where
  b0 : Chain (CS14 ∷ CK41 ∷ CS14 ∷ CK41 ∷ CS14 ∷ CK41 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
  b0 = at 0 6 (S4 ∷ S4 ∷ S4 ∷ []) (wl1109 (lit c4)) ▸ done

-- F1-order-SK@2: 1 steps
lem-F1-order-SKat2 : Ws → ⟪ (CS24 ∷ CK42 ∷ CS24 ∷ CK42 ∷ CS24 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
lem-F1-order-SKat2 c4 = run b0
  where
  b0 : Chain (CS24 ∷ CK42 ∷ CS24 ∷ CK42 ∷ CS24 ∷ CK42 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
  b0 = at 0 6 (S4 ∷ S4 ∷ S4 ∷ []) (wl1110 (lit c4)) ▸ done

-- F1-order-SK@3: 1 steps
lem-F1-order-SKat3 : Ws → ⟪ (CS34 ∷ CK43 ∷ CS34 ∷ CK43 ∷ CS34 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
lem-F1-order-SKat3 c4 = run b0
  where
  b0 : Chain (CS34 ∷ CK43 ∷ CS34 ∷ CK43 ∷ CS34 ∷ CK43 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
  b0 = at 0 6 (S4 ∷ S4 ∷ S4 ∷ []) (wl1111 (lit c4)) ▸ done

-- nf-order-CS@0: 0 steps
lem-nf-order-CSat0 : Ws → ⟪ [] ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-nf-order-CSat0 c4 = refl

-- nf-order-CS@1: 0 steps
lem-nf-order-CSat1 : Ws → ⟪ [] ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-nf-order-CSat1 c4 = refl

-- nf-order-CS@2: 0 steps
lem-nf-order-CSat2 : Ws → ⟪ [] ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-nf-order-CSat2 c4 = refl

-- nat-SWbc @02233440: 23 steps
lem-nat-SWbc-at02233440 : Ws → ⟪ (Sw34 ∷ Bx2-1340 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ []) ⟫ʷ
lem-nat-SWbc-at02233440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw34 ∷ Bx2-1340 ∷ Sw34 ∷ []) (CCZ124 ∷ Toff214 ∷ CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ Sw34 ∷ CCZ124 ∷ Bx2-10 ∷ Toff213 ∷ CCZ123 ∷ Bx1-240 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx1-240 ∷ Toff213 ∷ CCZ123 ∷ Bx1-240 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw34 ∷ []) (sym (wl1122 (lit c4))) ▸
       at 1 2 (Toff214 ∷ Sw34 ∷ []) (wl1123 (lit c4)) ▸
       at 3 1 (CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ []) (refl) ▸
       at 2 2 (CCZ123 ∷ Sw34 ∷ []) (sym (wl1124 (lit c4))) ▸
       at 3 2 (Toff123 ∷ Sw34 ∷ []) (wl1125 (lit c4)) ▸
       at 4 2 (Bx2-10 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 5 2 (Toff123 ∷ Sw34 ∷ []) (wl1125 (lit c4)) ▸ done

  b1 : Chain (CCZ124 ∷ Toff214 ∷ CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ Sw34 ∷ CCZ124 ∷ Bx2-10 ∷ Toff213 ∷ CCZ123 ∷ Bx1-240 ∷ Sw34 ∷ []) (CCZ124 ∷ Toff214 ∷ CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ Toff214 ∷ CCZ124 ∷ CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Sw34 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ Sw34 ∷ [])
  b1 = at 6 2 (CCZ123 ∷ Sw34 ∷ []) (sym (wl1124 (lit c4))) ▸
       at 7 2 (Bx2-10 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 8 2 (Toff214 ∷ Sw34 ∷ []) (wl1123 (lit c4)) ▸
       at 9 2 (CCZ124 ∷ Sw34 ∷ []) (sym (wl1122 (lit c4))) ▸
       at 11 1 (CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ []) (refl) ▸
       at 10 2 (CCZ123 ∷ Sw34 ∷ []) (sym (wl1124 (lit c4))) ▸
       at 11 2 (Toff123 ∷ Sw34 ∷ []) (wl1125 (lit c4)) ▸
       at 12 2 (Bx2-10 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸ done

  b2 : Chain (CCZ124 ∷ Toff214 ∷ CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ Toff214 ∷ CCZ124 ∷ CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Sw34 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ Sw34 ∷ []) (Bx2-1430 ∷ [])
  b2 = at 13 2 (Toff123 ∷ Sw34 ∷ []) (wl1125 (lit c4)) ▸
       at 14 2 (CCZ123 ∷ Sw34 ∷ []) (sym (wl1124 (lit c4))) ▸
       at 15 2 (Bx2-10 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 16 2 [] (wl0004 (lit c4)) ▸
       at 2 6 (Bx1-230 ∷ []) (refl) ▸
       at 5 6 (Bx1-230 ∷ []) (refl) ▸
       at 0 6 (Bx2-1430 ∷ []) (refl) ▸ done

-- nat-SWbc @022440: 23 steps
lem-nat-SWbc-at022440 : Ws → ⟪ (Sw34 ∷ Bx2-1430 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ []) ⟫ʷ
lem-nat-SWbc-at022440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw34 ∷ Bx2-1430 ∷ Sw34 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ Sw34 ∷ CCZ123 ∷ Bx2-10 ∷ Toff214 ∷ CCZ124 ∷ Bx1-230 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff214 ∷ Bx1-230 ∷ Toff214 ∷ CCZ124 ∷ Bx1-230 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw34 ∷ []) (sym (wl1124 (lit c4))) ▸
       at 1 2 (Toff213 ∷ Sw34 ∷ []) (wl1137 (lit c4)) ▸
       at 3 1 (CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ []) (refl) ▸
       at 2 2 (CCZ124 ∷ Sw34 ∷ []) (sym (wl1122 (lit c4))) ▸
       at 3 2 (Toff124 ∷ Sw34 ∷ []) (wl1138 (lit c4)) ▸
       at 4 2 (Bx2-10 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 5 2 (Toff124 ∷ Sw34 ∷ []) (wl1138 (lit c4)) ▸ done

  b1 : Chain (CCZ123 ∷ Toff213 ∷ CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ Sw34 ∷ CCZ123 ∷ Bx2-10 ∷ Toff214 ∷ CCZ124 ∷ Bx1-230 ∷ Sw34 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ Toff213 ∷ CCZ123 ∷ CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Sw34 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ Sw34 ∷ [])
  b1 = at 6 2 (CCZ124 ∷ Sw34 ∷ []) (sym (wl1122 (lit c4))) ▸
       at 7 2 (Bx2-10 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 8 2 (Toff213 ∷ Sw34 ∷ []) (wl1137 (lit c4)) ▸
       at 9 2 (CCZ123 ∷ Sw34 ∷ []) (sym (wl1124 (lit c4))) ▸
       at 11 1 (CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ []) (refl) ▸
       at 10 2 (CCZ124 ∷ Sw34 ∷ []) (sym (wl1122 (lit c4))) ▸
       at 11 2 (Toff124 ∷ Sw34 ∷ []) (wl1138 (lit c4)) ▸
       at 12 2 (Bx2-10 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸ done

  b2 : Chain (CCZ123 ∷ Toff213 ∷ CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ Toff213 ∷ CCZ123 ∷ CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Sw34 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ Sw34 ∷ []) (Bx2-1340 ∷ [])
  b2 = at 13 2 (Toff124 ∷ Sw34 ∷ []) (wl1138 (lit c4)) ▸
       at 14 2 (CCZ124 ∷ Sw34 ∷ []) (sym (wl1122 (lit c4))) ▸
       at 15 2 (Bx2-10 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 16 2 [] (wl0004 (lit c4)) ▸
       at 2 6 (Bx1-240 ∷ []) (refl) ▸
       at 5 6 (Bx1-240 ∷ []) (refl) ▸
       at 0 6 (Bx2-1340 ∷ []) (refl) ▸ done

-- sym-ab @1441: 18 steps
lem-sym-ab-at1441 : Ws → ⟪ (Bx0-4231 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-sym-ab-at1441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-4231 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ Toff024 ∷ CCZ024 ∷ Bx4-031 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff024 ∷ Bx4-031 ∷ Toff024 ∷ CCZ024 ∷ Bx4-031 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (sym (wp0214 c4)) ▸
       at 2 1 (CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ []) (wl0231 (lit c4)) ▸
       at 4 1 (Bx0-21 ∷ []) (refl) ▸
       at 7 1 (Bx0-21 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff024 ∷ CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ Toff024 ∷ CCZ024 ∷ Bx4-031 ∷ []) (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ [])
  b1 = at 2 6 (Bx2-031 ∷ []) (refl) ▸
       at 5 1 (CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸
       at 5 6 (CCZ013 ∷ []) (sym (wp0214 c4)) ▸
       at 5 1 (CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ []) (wl0231 (lit c4)) ▸
       at 7 1 (Bx0-21 ∷ []) (refl) ▸
       at 10 1 (Bx0-21 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) (Bx0-2431 ∷ [])
  b2 = at 5 6 (Bx2-031 ∷ []) (refl) ▸
       at 0 6 (Bx0-2431 ∷ []) (refl) ▸ done

-- nat-SWbc @0210233441: 23 steps
lem-nat-SWbc-at0210233441 : Ws → ⟪ (Sw34 ∷ Bx2-0341 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ []) ⟫ʷ
lem-nat-SWbc-at0210233441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw34 ∷ Bx2-0341 ∷ Sw34 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ Sw34 ∷ CCZ024 ∷ Bx2-01 ∷ Toff203 ∷ CCZ023 ∷ Bx0-241 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-241 ∷ Toff203 ∷ CCZ023 ∷ Bx0-241 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw34 ∷ []) (sym (wp0529 c4)) ▸
       at 1 2 (Toff204 ∷ Sw34 ∷ []) (wp0530 c4) ▸
       at 3 1 (CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ []) (refl) ▸
       at 2 2 (CCZ023 ∷ Sw34 ∷ []) (sym (wp0527 c4)) ▸
       at 3 2 (Toff023 ∷ Sw34 ∷ []) (wp0528 c4) ▸
       at 4 2 (Bx2-01 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 5 2 (Toff023 ∷ Sw34 ∷ []) (wp0528 c4) ▸ done

  b1 : Chain (CCZ024 ∷ Toff204 ∷ CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ Sw34 ∷ CCZ024 ∷ Bx2-01 ∷ Toff203 ∷ CCZ023 ∷ Bx0-241 ∷ Sw34 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ Toff204 ∷ CCZ024 ∷ CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Sw34 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ Sw34 ∷ [])
  b1 = at 6 2 (CCZ023 ∷ Sw34 ∷ []) (sym (wp0527 c4)) ▸
       at 7 2 (Bx2-01 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 8 2 (Toff204 ∷ Sw34 ∷ []) (wp0530 c4) ▸
       at 9 2 (CCZ024 ∷ Sw34 ∷ []) (sym (wp0529 c4)) ▸
       at 11 1 (CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ []) (refl) ▸
       at 10 2 (CCZ023 ∷ Sw34 ∷ []) (sym (wp0527 c4)) ▸
       at 11 2 (Toff023 ∷ Sw34 ∷ []) (wp0528 c4) ▸
       at 12 2 (Bx2-01 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸ done

  b2 : Chain (CCZ024 ∷ Toff204 ∷ CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ Toff204 ∷ CCZ024 ∷ CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Sw34 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ Sw34 ∷ []) (Bx2-0431 ∷ [])
  b2 = at 13 2 (Toff023 ∷ Sw34 ∷ []) (wp0528 c4) ▸
       at 14 2 (CCZ023 ∷ Sw34 ∷ []) (sym (wp0527 c4)) ▸
       at 15 2 (Bx2-01 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 16 2 [] (wl0004 (lit c4)) ▸
       at 2 6 (Bx0-231 ∷ []) (refl) ▸
       at 5 6 (Bx0-231 ∷ []) (refl) ▸
       at 0 6 (Bx2-0431 ∷ []) (refl) ▸ done

-- nat-SWbc @02102441: 23 steps
lem-nat-SWbc-at02102441 : Ws → ⟪ (Sw34 ∷ Bx2-0431 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ []) ⟫ʷ
lem-nat-SWbc-at02102441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw34 ∷ Bx2-0431 ∷ Sw34 ∷ []) (CCZ023 ∷ Toff203 ∷ CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ Sw34 ∷ CCZ023 ∷ Bx2-01 ∷ Toff204 ∷ CCZ024 ∷ Bx0-231 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-231 ∷ Toff204 ∷ CCZ024 ∷ Bx0-231 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw34 ∷ []) (sym (wp0527 c4)) ▸
       at 1 2 (Toff203 ∷ Sw34 ∷ []) (wp0813 c4) ▸
       at 3 1 (CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ []) (refl) ▸
       at 2 2 (CCZ024 ∷ Sw34 ∷ []) (sym (wp0529 c4)) ▸
       at 3 2 (Toff024 ∷ Sw34 ∷ []) (wp0812 c4) ▸
       at 4 2 (Bx2-01 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 5 2 (Toff024 ∷ Sw34 ∷ []) (wp0812 c4) ▸ done

  b1 : Chain (CCZ023 ∷ Toff203 ∷ CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ Sw34 ∷ CCZ023 ∷ Bx2-01 ∷ Toff204 ∷ CCZ024 ∷ Bx0-231 ∷ Sw34 ∷ []) (CCZ023 ∷ Toff203 ∷ CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ Toff203 ∷ CCZ023 ∷ CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Sw34 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ Sw34 ∷ [])
  b1 = at 6 2 (CCZ024 ∷ Sw34 ∷ []) (sym (wp0529 c4)) ▸
       at 7 2 (Bx2-01 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 8 2 (Toff203 ∷ Sw34 ∷ []) (wp0813 c4) ▸
       at 9 2 (CCZ023 ∷ Sw34 ∷ []) (sym (wp0527 c4)) ▸
       at 11 1 (CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ []) (refl) ▸
       at 10 2 (CCZ024 ∷ Sw34 ∷ []) (sym (wp0529 c4)) ▸
       at 11 2 (Toff024 ∷ Sw34 ∷ []) (wp0812 c4) ▸
       at 12 2 (Bx2-01 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸ done

  b2 : Chain (CCZ023 ∷ Toff203 ∷ CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ Toff203 ∷ CCZ023 ∷ CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Sw34 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ Sw34 ∷ []) (Bx2-0341 ∷ [])
  b2 = at 13 2 (Toff024 ∷ Sw34 ∷ []) (wp0812 c4) ▸
       at 14 2 (CCZ024 ∷ Sw34 ∷ []) (sym (wp0529 c4)) ▸
       at 15 2 (Bx2-01 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 16 2 [] (wl0004 (lit c4)) ▸
       at 2 6 (Bx0-241 ∷ []) (refl) ▸
       at 5 6 (Bx0-241 ∷ []) (refl) ▸
       at 0 6 (Bx2-0341 ∷ []) (refl) ▸ done

-- nat-SWbc @233442: 23 steps
lem-nat-SWbc-at233442 : Ws → ⟪ (Sw34 ∷ Bx0-1342 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ []) ⟫ʷ
lem-nat-SWbc-at233442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw34 ∷ Bx0-1342 ∷ Sw34 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ Sw34 ∷ CCZ014 ∷ Bx0-12 ∷ Toff013 ∷ CCZ013 ∷ Bx1-042 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-042 ∷ Toff013 ∷ CCZ013 ∷ Bx1-042 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw34 ∷ []) (sym (wp0398 c4)) ▸
       at 1 2 (Toff014 ∷ Sw34 ∷ []) (wp0957 c4) ▸
       at 3 1 (CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) (refl) ▸
       at 2 2 (CCZ013 ∷ Sw34 ∷ []) (sym (wp0958 c4)) ▸
       at 3 2 (Toff103 ∷ Sw34 ∷ []) (wp0959 c4) ▸
       at 4 2 (Bx0-12 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 5 2 (Toff103 ∷ Sw34 ∷ []) (wp0959 c4) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ Sw34 ∷ CCZ014 ∷ Bx0-12 ∷ Toff013 ∷ CCZ013 ∷ Bx1-042 ∷ Sw34 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ Toff014 ∷ CCZ014 ∷ CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Sw34 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ Sw34 ∷ [])
  b1 = at 6 2 (CCZ013 ∷ Sw34 ∷ []) (sym (wp0958 c4)) ▸
       at 7 2 (Bx0-12 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 8 2 (Toff014 ∷ Sw34 ∷ []) (wp0957 c4) ▸
       at 9 2 (CCZ014 ∷ Sw34 ∷ []) (sym (wp0398 c4)) ▸
       at 11 1 (CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) (refl) ▸
       at 10 2 (CCZ013 ∷ Sw34 ∷ []) (sym (wp0958 c4)) ▸
       at 11 2 (Toff103 ∷ Sw34 ∷ []) (wp0959 c4) ▸
       at 12 2 (Bx0-12 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸ done

  b2 : Chain (CCZ014 ∷ Toff014 ∷ CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ Toff014 ∷ CCZ014 ∷ CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Sw34 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ Sw34 ∷ []) (Bx0-1432 ∷ [])
  b2 = at 13 2 (Toff103 ∷ Sw34 ∷ []) (wp0959 c4) ▸
       at 14 2 (CCZ013 ∷ Sw34 ∷ []) (sym (wp0958 c4)) ▸
       at 15 2 (Bx0-12 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 16 2 [] (wl0004 (lit c4)) ▸
       at 2 6 (Bx1-032 ∷ []) (refl) ▸
       at 5 6 (Bx1-032 ∷ []) (refl) ▸
       at 0 6 (Bx0-1432 ∷ []) (refl) ▸ done

-- nat-SWbc @2442: 23 steps
lem-nat-SWbc-at2442 : Ws → ⟪ (Sw34 ∷ Bx0-1432 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-nat-SWbc-at2442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw34 ∷ Bx0-1432 ∷ Sw34 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ Sw34 ∷ CCZ013 ∷ Bx0-12 ∷ Toff014 ∷ CCZ014 ∷ Bx1-032 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ CCZ014 ∷ Bx1-032 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw34 ∷ []) (sym (wp0958 c4)) ▸
       at 1 2 (Toff013 ∷ Sw34 ∷ []) (wp0965 c4) ▸
       at 3 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) (refl) ▸
       at 2 2 (CCZ014 ∷ Sw34 ∷ []) (sym (wp0398 c4)) ▸
       at 3 2 (Toff104 ∷ Sw34 ∷ []) (wp0966 c4) ▸
       at 4 2 (Bx0-12 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 5 2 (Toff104 ∷ Sw34 ∷ []) (wp0966 c4) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ Sw34 ∷ CCZ013 ∷ Bx0-12 ∷ Toff014 ∷ CCZ014 ∷ Bx1-032 ∷ Sw34 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ Toff013 ∷ CCZ013 ∷ CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Sw34 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ Sw34 ∷ [])
  b1 = at 6 2 (CCZ014 ∷ Sw34 ∷ []) (sym (wp0398 c4)) ▸
       at 7 2 (Bx0-12 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 8 2 (Toff013 ∷ Sw34 ∷ []) (wp0965 c4) ▸
       at 9 2 (CCZ013 ∷ Sw34 ∷ []) (sym (wp0958 c4)) ▸
       at 11 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) (refl) ▸
       at 10 2 (CCZ014 ∷ Sw34 ∷ []) (sym (wp0398 c4)) ▸
       at 11 2 (Toff104 ∷ Sw34 ∷ []) (wp0966 c4) ▸
       at 12 2 (Bx0-12 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸ done

  b2 : Chain (CCZ013 ∷ Toff013 ∷ CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ Toff013 ∷ CCZ013 ∷ CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Sw34 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ Sw34 ∷ []) (Bx0-1342 ∷ [])
  b2 = at 13 2 (Toff104 ∷ Sw34 ∷ []) (wp0966 c4) ▸
       at 14 2 (CCZ014 ∷ Sw34 ∷ []) (sym (wp0398 c4)) ▸
       at 15 2 (Bx0-12 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 16 2 [] (wl0004 (lit c4)) ▸
       at 2 6 (Bx1-042 ∷ []) (refl) ▸
       at 5 6 (Bx1-042 ∷ []) (refl) ▸
       at 0 6 (Bx0-1342 ∷ []) (refl) ▸ done

-- nat-SWbc @143143: 23 steps
lem-nat-SWbc-at143143 : Ws → ⟪ (Sw12 ∷ Bx0-4213 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ []) ⟫ʷ
lem-nat-SWbc-at143143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw12 ∷ Bx0-4213 ∷ Sw12 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ Sw12 ∷ CCZ014 ∷ Bx0-43 ∷ Toff024 ∷ CCZ024 ∷ Bx4-013 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-013 ∷ Toff024 ∷ CCZ024 ∷ Bx4-013 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (sym (wp0553 c4)) ▸
       at 1 2 (Toff014 ∷ Sw12 ∷ []) (wp0972 c4) ▸
       at 3 1 (CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) (refl) ▸
       at 2 2 (CCZ024 ∷ Sw12 ∷ []) (sym (wp0551 c4)) ▸
       at 3 2 (Toff402 ∷ Sw12 ∷ []) (wp0973 c4) ▸
       at 4 2 (Bx0-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 5 2 (Toff402 ∷ Sw12 ∷ []) (wp0973 c4) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ Sw12 ∷ CCZ014 ∷ Bx0-43 ∷ Toff024 ∷ CCZ024 ∷ Bx4-013 ∷ Sw12 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ Toff014 ∷ CCZ014 ∷ CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Sw12 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ Sw12 ∷ [])
  b1 = at 6 2 (CCZ024 ∷ Sw12 ∷ []) (sym (wp0551 c4)) ▸
       at 7 2 (Bx0-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 8 2 (Toff014 ∷ Sw12 ∷ []) (wp0972 c4) ▸
       at 9 2 (CCZ014 ∷ Sw12 ∷ []) (sym (wp0553 c4)) ▸
       at 11 1 (CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) (refl) ▸
       at 10 2 (CCZ024 ∷ Sw12 ∷ []) (sym (wp0551 c4)) ▸
       at 11 2 (Toff402 ∷ Sw12 ∷ []) (wp0973 c4) ▸
       at 12 2 (Bx0-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸ done

  b2 : Chain (CCZ014 ∷ Toff014 ∷ CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ Toff014 ∷ CCZ014 ∷ CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Sw12 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ Sw12 ∷ []) (Bx0-4123 ∷ [])
  b2 = at 13 2 (Toff402 ∷ Sw12 ∷ []) (wp0973 c4) ▸
       at 14 2 (CCZ024 ∷ Sw12 ∷ []) (sym (wp0551 c4)) ▸
       at 15 2 (Bx0-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 16 2 [] (wl0006 (lit c4)) ▸
       at 2 6 (Bx4-023 ∷ []) (refl) ▸
       at 5 6 (Bx4-023 ∷ []) (refl) ▸
       at 0 6 (Bx0-4123 ∷ []) (refl) ▸ done

-- sym-ab @0314213240: 18 steps
lem-sym-ab-at0314213240 : Ws → ⟪ (Bx3-4120 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-sym-ab-at0314213240 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-4120 ∷ []) (CCZ134 ∷ Toff314 ∷ CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ Toff314 ∷ CCZ134 ∷ Bx4-320 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff314 ∷ Bx4-320 ∷ Toff314 ∷ CCZ134 ∷ Bx4-320 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wp0992 c4)) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ CZ01 ∷ Toff123 ∷ CCZ123 ∷ CZ01 ∷ []) (wl1126 (lit c4)) ▸
       at 4 1 (Bx3-10 ∷ []) (refl) ▸
       at 7 1 (Bx3-10 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff314 ∷ CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ Toff314 ∷ CCZ134 ∷ Bx4-320 ∷ []) (CCZ134 ∷ Toff314 ∷ Bx1-320 ∷ Toff314 ∷ CCZ134 ∷ CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ [])
  b1 = at 2 6 (Bx1-320 ∷ []) (refl) ▸
       at 5 1 (CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸
       at 5 6 (CCZ023 ∷ []) (sym (wp0992 c4)) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ CZ01 ∷ Toff123 ∷ CCZ123 ∷ CZ01 ∷ []) (wl1126 (lit c4)) ▸
       at 7 1 (Bx3-10 ∷ []) (refl) ▸
       at 10 1 (Bx3-10 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ134 ∷ Toff314 ∷ Bx1-320 ∷ Toff314 ∷ CCZ134 ∷ CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ []) (Bx3-1420 ∷ [])
  b2 = at 5 6 (Bx1-320 ∷ []) (refl) ▸
       at 0 6 (Bx3-1420 ∷ []) (refl) ▸ done

-- sym-ab @03243240: 18 steps
lem-sym-ab-at03243240 : Ws → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ []) ⟫ʷ
lem-sym-ab-at03243240 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-1420 ∷ []) (CCZ134 ∷ Toff314 ∷ CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ Toff314 ∷ CCZ134 ∷ Bx1-320 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff314 ∷ Bx1-320 ∷ Toff314 ∷ CCZ134 ∷ Bx1-320 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wl1126 (lit c4))) ▸
       at 2 1 (CCZ234 ∷ Toff423 ∷ CZ04 ∷ Toff423 ∷ CCZ234 ∷ CZ04 ∷ []) (wp0992 c4) ▸
       at 4 1 (Bx3-40 ∷ []) (refl) ▸
       at 7 1 (Bx3-40 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff314 ∷ CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ Toff314 ∷ CCZ134 ∷ Bx1-320 ∷ []) (CCZ134 ∷ Toff314 ∷ Bx4-320 ∷ Toff314 ∷ CCZ134 ∷ CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ [])
  b1 = at 2 6 (Bx4-320 ∷ []) (refl) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸
       at 5 6 (CCZ023 ∷ []) (sym (wl1126 (lit c4))) ▸
       at 5 1 (CCZ234 ∷ Toff423 ∷ CZ04 ∷ Toff423 ∷ CCZ234 ∷ CZ04 ∷ []) (wp0992 c4) ▸
       at 7 1 (Bx3-40 ∷ []) (refl) ▸
       at 10 1 (Bx3-40 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ134 ∷ Toff314 ∷ Bx4-320 ∷ Toff314 ∷ CCZ134 ∷ CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ []) (Bx3-4120 ∷ [])
  b2 = at 5 6 (Bx4-320 ∷ []) (refl) ▸
       at 0 6 (Bx3-4120 ∷ []) (refl) ▸ done

-- nat-S @01143043: 31 steps
lem-nat-S-at01143043 : Ws → ⟪ (Sw03 ∷ Sb0-1-42-3 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-42-0 ∷ []) ⟫ʷ
lem-nat-S-at01143043 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sw03 ∷ Sb0-1-42-3 ∷ Sw03 ∷ []) (CCZ134 ∷ Toff314 ∷ Sw03 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Sw03 ∷ [])
  b0 = at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw03 ∷ []) (sym (wp1014 c4)) ▸
       at 1 2 (Toff314 ∷ Sw03 ∷ []) (wp1015 c4) ▸
       at 3 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (refl) ▸
       at 5 1 (CZ13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff314 ∷ Sw03 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Sw03 ∷ []) (CCZ134 ∷ Toff314 ∷ Bx1-320 ∷ Toff314 ∷ CCZ134 ∷ Sw03 ∷ CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Sw03 ∷ [])
  b1 = at 8 1 (CZ13 ∷ []) (refl) ▸
       at 2 7 (CCZ123 ∷ Toff123 ∷ CZ01 ∷ Toff123 ∷ CCZ123 ∷ CZ01 ∷ Sw03 ∷ []) (sym (wl1210 (lit c4))) ▸
       at 4 1 (Bx3-10 ∷ []) (refl) ▸
       at 7 1 (Bx3-10 ∷ []) (refl) ▸
       at 2 6 (Bx1-320 ∷ []) (refl) ▸
       at 3 2 (Toff314 ∷ Sw03 ∷ []) (wp1015 c4) ▸
       at 4 2 (CCZ134 ∷ Sw03 ∷ []) (sym (wp1014 c4)) ▸
       at 6 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ134 ∷ Toff314 ∷ Bx1-320 ∷ Toff314 ∷ CCZ134 ∷ Sw03 ∷ CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Sw03 ∷ []) (CCZ134 ∷ Toff314 ∷ Bx1-320 ∷ Toff314 ∷ CCZ134 ∷ Bx1-320 ∷ Toff024 ∷ CS01 ∷ Sw03 ∷ Toff324 ∷ CS13⁻ ∷ Sw03 ∷ [])
  b2 = at 8 1 (CZ13 ∷ []) (refl) ▸
       at 11 1 (CZ13 ∷ []) (refl) ▸
       at 5 7 (CCZ123 ∷ Toff123 ∷ CZ01 ∷ Toff123 ∷ CCZ123 ∷ CZ01 ∷ Sw03 ∷ []) (sym (wl1210 (lit c4))) ▸
       at 7 1 (Bx3-10 ∷ []) (refl) ▸
       at 10 1 (Bx3-10 ∷ []) (refl) ▸
       at 5 6 (Bx1-320 ∷ []) (refl) ▸
       at 6 2 (Toff024 ∷ Sw03 ∷ []) (wp1016 c4) ▸
       at 7 2 (CS01 ∷ Sw03 ∷ []) (sym (wl1211 (lit c4))) ▸ done

  b3 : Chain (CCZ134 ∷ Toff314 ∷ Bx1-320 ∷ Toff314 ∷ CCZ134 ∷ Bx1-320 ∷ Toff024 ∷ CS01 ∷ Sw03 ∷ Toff324 ∷ CS13⁻ ∷ Sw03 ∷ []) (Sb3-1-42-0 ∷ [])
  b3 = at 8 2 (Toff024 ∷ Sw03 ∷ []) (wp1016 c4) ▸
       at 9 2 (CS01⁻ ∷ Sw03 ∷ []) (sym (wl1212 (lit c4))) ▸
       at 10 2 [] (wl0928 (lit c4)) ▸
       at 0 6 (Bx3-1420 ∷ []) (refl) ▸
       at 2 1 (Sb3-1-0-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻3-1-0-2 ∷ []) (refl) ▸
       at 0 5 (Sb3-1-42-0 ∷ []) (refl) ▸ done

-- nat-SWbc @033440: 23 steps
lem-nat-SWbc-at033440 : Ws → ⟪ (Sw24 ∷ Bx3-1240 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-nat-SWbc-at033440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw24 ∷ Bx3-1240 ∷ Sw24 ∷ []) (CCZ134 ∷ Toff314 ∷ CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ Sw24 ∷ CCZ134 ∷ Bx3-10 ∷ Toff312 ∷ CCZ123 ∷ Bx1-340 ∷ Sw24 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx1-340 ∷ Toff312 ∷ CCZ123 ∷ Bx1-340 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw24 ∷ []) (sym (wl1216 (lit c4))) ▸
       at 1 2 (Toff314 ∷ Sw24 ∷ []) (wl1217 (lit c4)) ▸
       at 3 1 (CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ []) (refl) ▸
       at 2 2 (CCZ123 ∷ Sw24 ∷ []) (sym (wl1218 (lit c4))) ▸
       at 3 2 (Toff123 ∷ Sw24 ∷ []) (wl1219 (lit c4)) ▸
       at 4 2 (Bx3-10 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸
       at 5 2 (Toff123 ∷ Sw24 ∷ []) (wl1219 (lit c4)) ▸ done

  b1 : Chain (CCZ134 ∷ Toff314 ∷ CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ Sw24 ∷ CCZ134 ∷ Bx3-10 ∷ Toff312 ∷ CCZ123 ∷ Bx1-340 ∷ Sw24 ∷ []) (CCZ134 ∷ Toff314 ∷ CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ Toff314 ∷ CCZ134 ∷ CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Sw24 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ Sw24 ∷ [])
  b1 = at 6 2 (CCZ123 ∷ Sw24 ∷ []) (sym (wl1218 (lit c4))) ▸
       at 7 2 (Bx3-10 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸
       at 8 2 (Toff314 ∷ Sw24 ∷ []) (wl1217 (lit c4)) ▸
       at 9 2 (CCZ134 ∷ Sw24 ∷ []) (sym (wl1216 (lit c4))) ▸
       at 11 1 (CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ []) (refl) ▸
       at 10 2 (CCZ123 ∷ Sw24 ∷ []) (sym (wl1218 (lit c4))) ▸
       at 11 2 (Toff123 ∷ Sw24 ∷ []) (wl1219 (lit c4)) ▸
       at 12 2 (Bx3-10 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸ done

  b2 : Chain (CCZ134 ∷ Toff314 ∷ CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ Toff314 ∷ CCZ134 ∷ CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Sw24 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ Sw24 ∷ []) (Bx3-1420 ∷ [])
  b2 = at 13 2 (Toff123 ∷ Sw24 ∷ []) (wl1219 (lit c4)) ▸
       at 14 2 (CCZ123 ∷ Sw24 ∷ []) (sym (wl1218 (lit c4))) ▸
       at 15 2 (Bx3-10 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸
       at 16 2 [] (wl0322 (lit c4)) ▸
       at 2 6 (Bx1-320 ∷ []) (refl) ▸
       at 5 6 (Bx1-320 ∷ []) (refl) ▸
       at 0 6 (Bx3-1420 ∷ []) (refl) ▸ done

-- nat-SWbc @03243240: 23 steps
lem-nat-SWbc-at03243240 : Ws → ⟪ (Sw24 ∷ Bx3-1420 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1240 ∷ []) ⟫ʷ
lem-nat-SWbc-at03243240 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw24 ∷ Bx3-1420 ∷ Sw24 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ Sw24 ∷ CCZ123 ∷ Bx3-10 ∷ Toff314 ∷ CCZ134 ∷ Bx1-320 ∷ Sw24 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff314 ∷ Bx1-320 ∷ Toff314 ∷ CCZ134 ∷ Bx1-320 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw24 ∷ []) (sym (wl1218 (lit c4))) ▸
       at 1 2 (Toff312 ∷ Sw24 ∷ []) (wl1231 (lit c4)) ▸
       at 3 1 (CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ []) (refl) ▸
       at 2 2 (CCZ134 ∷ Sw24 ∷ []) (sym (wl1216 (lit c4))) ▸
       at 3 2 (Toff134 ∷ Sw24 ∷ []) (wl1232 (lit c4)) ▸
       at 4 2 (Bx3-10 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸
       at 5 2 (Toff134 ∷ Sw24 ∷ []) (wl1232 (lit c4)) ▸ done

  b1 : Chain (CCZ123 ∷ Toff312 ∷ CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ Sw24 ∷ CCZ123 ∷ Bx3-10 ∷ Toff314 ∷ CCZ134 ∷ Bx1-320 ∷ Sw24 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ Toff312 ∷ CCZ123 ∷ CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Sw24 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ Sw24 ∷ [])
  b1 = at 6 2 (CCZ134 ∷ Sw24 ∷ []) (sym (wl1216 (lit c4))) ▸
       at 7 2 (Bx3-10 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸
       at 8 2 (Toff312 ∷ Sw24 ∷ []) (wl1231 (lit c4)) ▸
       at 9 2 (CCZ123 ∷ Sw24 ∷ []) (sym (wl1218 (lit c4))) ▸
       at 11 1 (CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ []) (refl) ▸
       at 10 2 (CCZ134 ∷ Sw24 ∷ []) (sym (wl1216 (lit c4))) ▸
       at 11 2 (Toff134 ∷ Sw24 ∷ []) (wl1232 (lit c4)) ▸
       at 12 2 (Bx3-10 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸ done

  b2 : Chain (CCZ123 ∷ Toff312 ∷ CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ Toff312 ∷ CCZ123 ∷ CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Sw24 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ Sw24 ∷ []) (Bx3-1240 ∷ [])
  b2 = at 13 2 (Toff134 ∷ Sw24 ∷ []) (wl1232 (lit c4)) ▸
       at 14 2 (CCZ134 ∷ Sw24 ∷ []) (sym (wl1216 (lit c4))) ▸
       at 15 2 (Bx3-10 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸
       at 16 2 [] (wl0322 (lit c4)) ▸
       at 2 6 (Bx1-340 ∷ []) (refl) ▸
       at 5 6 (Bx1-340 ∷ []) (refl) ▸
       at 0 6 (Bx3-1240 ∷ []) (refl) ▸ done

-- nat-SWbc @03103441: 23 steps
lem-nat-SWbc-at03103441 : Ws → ⟪ (Sw24 ∷ Bx3-0241 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ []) ⟫ʷ
lem-nat-SWbc-at03103441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw24 ∷ Bx3-0241 ∷ Sw24 ∷ []) (CCZ034 ∷ Toff304 ∷ CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ Sw24 ∷ CCZ034 ∷ Bx3-01 ∷ Toff302 ∷ CCZ023 ∷ Bx0-341 ∷ Sw24 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-341 ∷ Toff302 ∷ CCZ023 ∷ Bx0-341 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw24 ∷ []) (sym (wp0177 c4)) ▸
       at 1 2 (Toff304 ∷ Sw24 ∷ []) (wp0178 c4) ▸
       at 3 1 (CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Toff034 ∷ CCZ034 ∷ Bx3-01 ∷ []) (refl) ▸
       at 2 2 (CCZ023 ∷ Sw24 ∷ []) (sym (wp0175 c4)) ▸
       at 3 2 (Toff023 ∷ Sw24 ∷ []) (wp0176 c4) ▸
       at 4 2 (Bx3-01 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸
       at 5 2 (Toff023 ∷ Sw24 ∷ []) (wp0176 c4) ▸ done

  b1 : Chain (CCZ034 ∷ Toff304 ∷ CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ Sw24 ∷ CCZ034 ∷ Bx3-01 ∷ Toff302 ∷ CCZ023 ∷ Bx0-341 ∷ Sw24 ∷ []) (CCZ034 ∷ Toff304 ∷ CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ Toff304 ∷ CCZ034 ∷ CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Sw24 ∷ Toff034 ∷ CCZ034 ∷ Bx3-01 ∷ Sw24 ∷ [])
  b1 = at 6 2 (CCZ023 ∷ Sw24 ∷ []) (sym (wp0175 c4)) ▸
       at 7 2 (Bx3-01 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸
       at 8 2 (Toff304 ∷ Sw24 ∷ []) (wp0178 c4) ▸
       at 9 2 (CCZ034 ∷ Sw24 ∷ []) (sym (wp0177 c4)) ▸
       at 11 1 (CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Toff034 ∷ CCZ034 ∷ Bx3-01 ∷ []) (refl) ▸
       at 10 2 (CCZ023 ∷ Sw24 ∷ []) (sym (wp0175 c4)) ▸
       at 11 2 (Toff023 ∷ Sw24 ∷ []) (wp0176 c4) ▸
       at 12 2 (Bx3-01 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸ done

  b2 : Chain (CCZ034 ∷ Toff304 ∷ CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ Toff304 ∷ CCZ034 ∷ CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Sw24 ∷ Toff034 ∷ CCZ034 ∷ Bx3-01 ∷ Sw24 ∷ []) (Bx3-0421 ∷ [])
  b2 = at 13 2 (Toff023 ∷ Sw24 ∷ []) (wp0176 c4) ▸
       at 14 2 (CCZ023 ∷ Sw24 ∷ []) (sym (wp0175 c4)) ▸
       at 15 2 (Bx3-01 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸
       at 16 2 [] (wl0322 (lit c4)) ▸
       at 2 6 (Bx0-321 ∷ []) (refl) ▸
       at 5 6 (Bx0-321 ∷ []) (refl) ▸
       at 0 6 (Bx3-0421 ∷ []) (refl) ▸ done

-- nat-SWbc @0310243241: 23 steps
lem-nat-SWbc-at0310243241 : Ws → ⟪ (Sw24 ∷ Bx3-0421 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ []) ⟫ʷ
lem-nat-SWbc-at0310243241 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw24 ∷ Bx3-0421 ∷ Sw24 ∷ []) (CCZ023 ∷ Toff302 ∷ CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Toff034 ∷ Sw24 ∷ CCZ023 ∷ Bx3-01 ∷ Toff304 ∷ CCZ034 ∷ Bx0-321 ∷ Sw24 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-321 ∷ Toff304 ∷ CCZ034 ∷ Bx0-321 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw24 ∷ []) (sym (wp0175 c4)) ▸
       at 1 2 (Toff302 ∷ Sw24 ∷ []) (wp0274 c4) ▸
       at 3 1 (CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ []) (refl) ▸
       at 2 2 (CCZ034 ∷ Sw24 ∷ []) (sym (wp0177 c4)) ▸
       at 3 2 (Toff034 ∷ Sw24 ∷ []) (wp0273 c4) ▸
       at 4 2 (Bx3-01 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸
       at 5 2 (Toff034 ∷ Sw24 ∷ []) (wp0273 c4) ▸ done

  b1 : Chain (CCZ023 ∷ Toff302 ∷ CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Toff034 ∷ Sw24 ∷ CCZ023 ∷ Bx3-01 ∷ Toff304 ∷ CCZ034 ∷ Bx0-321 ∷ Sw24 ∷ []) (CCZ023 ∷ Toff302 ∷ CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Toff034 ∷ CCZ034 ∷ Bx3-01 ∷ Toff302 ∷ CCZ023 ∷ CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Sw24 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ Sw24 ∷ [])
  b1 = at 6 2 (CCZ034 ∷ Sw24 ∷ []) (sym (wp0177 c4)) ▸
       at 7 2 (Bx3-01 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸
       at 8 2 (Toff302 ∷ Sw24 ∷ []) (wp0274 c4) ▸
       at 9 2 (CCZ023 ∷ Sw24 ∷ []) (sym (wp0175 c4)) ▸
       at 11 1 (CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ []) (refl) ▸
       at 10 2 (CCZ034 ∷ Sw24 ∷ []) (sym (wp0177 c4)) ▸
       at 11 2 (Toff034 ∷ Sw24 ∷ []) (wp0273 c4) ▸
       at 12 2 (Bx3-01 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸ done

  b2 : Chain (CCZ023 ∷ Toff302 ∷ CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Toff034 ∷ CCZ034 ∷ Bx3-01 ∷ Toff302 ∷ CCZ023 ∷ CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Sw24 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ Sw24 ∷ []) (Bx3-0241 ∷ [])
  b2 = at 13 2 (Toff034 ∷ Sw24 ∷ []) (wp0273 c4) ▸
       at 14 2 (CCZ034 ∷ Sw24 ∷ []) (sym (wp0177 c4)) ▸
       at 15 2 (Bx3-01 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸
       at 16 2 [] (wl0322 (lit c4)) ▸
       at 2 6 (Bx0-341 ∷ []) (refl) ▸
       at 5 6 (Bx0-341 ∷ []) (refl) ▸
       at 0 6 (Bx3-0241 ∷ []) (refl) ▸ done

-- cQ @0310213442: 7 steps
lem-cQ-at0310213442 : Ws → ⟪ (CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ
lem-cQ-at0310213442 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ013 ∷ [])
  b0 = at 0 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (wl0184 (lit c4)) ▸
       at 4 2 (CCZ234 ∷ CS03 ∷ []) (sym (wp0294 c4)) ▸
       at 3 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CS13⁻ ∷ []) (sym (wl0432 (lit c4))) ▸
       at 1 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 0 2 (CCZ234 ∷ CS13 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 1 5 (CCZ013 ∷ []) (sym (wl0184 (lit c4))) ▸ done

-- sym-ab @03122031: 18 steps
lem-sym-ab-at03122031 : Ws → ⟪ (Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ []) ⟫ʷ
lem-sym-ab-at03122031 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-2014 ∷ []) (CCZ023 ∷ Toff302 ∷ CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ Toff302 ∷ CCZ023 ∷ Bx2-314 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff302 ∷ Bx2-314 ∷ Toff302 ∷ CCZ023 ∷ Bx2-314 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ134 ∷ []) (wl1303 (lit c4)) ▸
       at 2 1 (CCZ013 ∷ Toff013 ∷ CZ04 ∷ Toff013 ∷ CCZ013 ∷ CZ04 ∷ []) (sym (wp0262 c4)) ▸
       at 4 1 (Bx3-04 ∷ []) (refl) ▸
       at 7 1 (Bx3-04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff302 ∷ CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ Toff302 ∷ CCZ023 ∷ Bx2-314 ∷ []) (CCZ023 ∷ Toff302 ∷ Bx0-314 ∷ Toff302 ∷ CCZ023 ∷ CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ [])
  b1 = at 2 6 (Bx0-314 ∷ []) (refl) ▸
       at 5 1 (CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸
       at 5 6 (CCZ134 ∷ []) (wl1303 (lit c4)) ▸
       at 5 1 (CCZ013 ∷ Toff013 ∷ CZ04 ∷ Toff013 ∷ CCZ013 ∷ CZ04 ∷ []) (sym (wp0262 c4)) ▸
       at 7 1 (Bx3-04 ∷ []) (refl) ▸
       at 10 1 (Bx3-04 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ023 ∷ Toff302 ∷ Bx0-314 ∷ Toff302 ∷ CCZ023 ∷ CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ []) (Bx3-0214 ∷ [])
  b2 = at 5 6 (Bx0-314 ∷ []) (refl) ▸
       at 0 6 (Bx3-0214 ∷ []) (refl) ▸ done

-- sym-ab @0312243041: 18 steps
lem-sym-ab-at0312243041 : Ws → ⟪ (Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ []) ⟫ʷ
lem-sym-ab-at0312243041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-2401 ∷ []) (CCZ234 ∷ Toff324 ∷ CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ Toff324 ∷ CCZ234 ∷ Bx2-301 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff324 ∷ Bx2-301 ∷ Toff324 ∷ CCZ234 ∷ Bx2-301 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (sym (wl0231 (lit c4))) ▸
       at 2 1 (CCZ034 ∷ Toff403 ∷ CZ14 ∷ Toff403 ∷ CCZ034 ∷ CZ14 ∷ []) (wp0214 c4) ▸
       at 4 1 (Bx3-41 ∷ []) (refl) ▸
       at 7 1 (Bx3-41 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff324 ∷ CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ Toff324 ∷ CCZ234 ∷ Bx2-301 ∷ []) (CCZ234 ∷ Toff324 ∷ Bx4-301 ∷ Toff324 ∷ CCZ234 ∷ CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ [])
  b1 = at 2 6 (Bx4-301 ∷ []) (refl) ▸
       at 5 1 (CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸
       at 5 6 (CCZ013 ∷ []) (sym (wl0231 (lit c4))) ▸
       at 5 1 (CCZ034 ∷ Toff403 ∷ CZ14 ∷ Toff403 ∷ CCZ034 ∷ CZ14 ∷ []) (wp0214 c4) ▸
       at 7 1 (Bx3-41 ∷ []) (refl) ▸
       at 10 1 (Bx3-41 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ234 ∷ Toff324 ∷ Bx4-301 ∷ Toff324 ∷ CCZ234 ∷ CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ []) (Bx3-4201 ∷ [])
  b2 = at 5 6 (Bx4-301 ∷ []) (refl) ▸
       at 0 6 (Bx3-4201 ∷ []) (refl) ▸ done

-- cQ @0214233041: 7 steps
lem-cQ-at0214233041 : Ws → ⟪ (CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ
lem-cQ-at0214233041 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ234 ∷ [])
  b0 = at 0 1 (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0330 (lit c4)) ▸
       at 4 2 (CCZ012 ∷ CS24 ∷ []) (sym (wp0141 c4)) ▸
       at 3 2 (CCZ012 ∷ CX43 ∷ []) (sym (c₃ (CCZ) (CX₁₀))) ▸
       at 2 2 (CCZ012 ∷ CS23⁻ ∷ []) (sym (wl0331 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ CX43 ∷ []) (sym (c₃ (CCZ) (CX₁₀))) ▸
       at 0 2 (CCZ012 ∷ CS23 ∷ []) (sym (wl0294 (lit c4))) ▸
       at 1 5 (CCZ234 ∷ []) (sym (wl0330 (lit c4))) ▸ done

-- sym-ab @0214233041: 18 steps
lem-sym-ab-at0214233041 : Ws → ⟪ (Bx2-4301 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ []) ⟫ʷ
lem-sym-ab-at0214233041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-4301 ∷ []) (CCZ234 ∷ Toff234 ∷ CCZ023 ∷ Toff302 ∷ Bx2-31 ∷ Toff302 ∷ CCZ023 ∷ Bx2-31 ∷ Toff234 ∷ CCZ234 ∷ Bx4-201 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff234 ∷ Bx4-201 ∷ Toff234 ∷ CCZ234 ∷ Bx4-201 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wp0162 c4)) ▸
       at 2 1 (CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ []) (wl0288 (lit c4)) ▸
       at 4 1 (Bx2-31 ∷ []) (refl) ▸
       at 7 1 (Bx2-31 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff234 ∷ CCZ023 ∷ Toff302 ∷ Bx2-31 ∷ Toff302 ∷ CCZ023 ∷ Bx2-31 ∷ Toff234 ∷ CCZ234 ∷ Bx4-201 ∷ []) (CCZ234 ∷ Toff234 ∷ Bx3-201 ∷ Toff234 ∷ CCZ234 ∷ CCZ023 ∷ Toff302 ∷ Bx2-31 ∷ Toff302 ∷ CCZ023 ∷ Bx2-31 ∷ [])
  b1 = at 2 6 (Bx3-201 ∷ []) (refl) ▸
       at 5 1 (CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸
       at 5 6 (CCZ012 ∷ []) (sym (wp0162 c4)) ▸
       at 5 1 (CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ []) (wl0288 (lit c4)) ▸
       at 7 1 (Bx2-31 ∷ []) (refl) ▸
       at 10 1 (Bx2-31 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ234 ∷ Toff234 ∷ Bx3-201 ∷ Toff234 ∷ CCZ234 ∷ CCZ023 ∷ Toff302 ∷ Bx2-31 ∷ Toff302 ∷ CCZ023 ∷ Bx2-31 ∷ []) (Bx2-3401 ∷ [])
  b2 = at 5 6 (Bx3-201 ∷ []) (refl) ▸
       at 0 6 (Bx2-3401 ∷ []) (refl) ▸ done

-- sym-ab @03143041: 18 steps
lem-sym-ab-at03143041 : Ws → ⟪ (Bx3-4201 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ []) ⟫ʷ
lem-sym-ab-at03143041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-4201 ∷ []) (CCZ234 ∷ Toff324 ∷ CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ Toff324 ∷ CCZ234 ∷ Bx4-301 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff324 ∷ Bx4-301 ∷ Toff324 ∷ CCZ234 ∷ Bx4-301 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (sym (wp0214 c4)) ▸
       at 2 1 (CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ []) (wl0231 (lit c4)) ▸
       at 4 1 (Bx3-21 ∷ []) (refl) ▸
       at 7 1 (Bx3-21 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff324 ∷ CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ Toff324 ∷ CCZ234 ∷ Bx4-301 ∷ []) (CCZ234 ∷ Toff324 ∷ Bx2-301 ∷ Toff324 ∷ CCZ234 ∷ CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ [])
  b1 = at 2 6 (Bx2-301 ∷ []) (refl) ▸
       at 5 1 (CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸
       at 5 6 (CCZ013 ∷ []) (sym (wp0214 c4)) ▸
       at 5 1 (CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ []) (wl0231 (lit c4)) ▸
       at 7 1 (Bx3-21 ∷ []) (refl) ▸
       at 10 1 (Bx3-21 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ234 ∷ Toff324 ∷ Bx2-301 ∷ Toff324 ∷ CCZ234 ∷ CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ []) (Bx3-2401 ∷ [])
  b2 = at 5 6 (Bx2-301 ∷ []) (refl) ▸
       at 0 6 (Bx3-2401 ∷ []) (refl) ▸ done

-- sym-ab @0213243041: 18 steps
lem-sym-ab-at0213243041 : Ws → ⟪ (Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ []) ⟫ʷ
lem-sym-ab-at0213243041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-3401 ∷ []) (CCZ234 ∷ Toff234 ∷ CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ Toff234 ∷ CCZ234 ∷ Bx3-201 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff234 ∷ Bx3-201 ∷ Toff234 ∷ CCZ234 ∷ Bx3-201 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff302 ∷ Bx2-31 ∷ Toff302 ∷ CCZ023 ∷ Bx2-31 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wl0288 (lit c4))) ▸
       at 2 1 (CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ []) (wp0162 c4) ▸
       at 4 1 (Bx2-41 ∷ []) (refl) ▸
       at 7 1 (Bx2-41 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff234 ∷ CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ Toff234 ∷ CCZ234 ∷ Bx3-201 ∷ []) (CCZ234 ∷ Toff234 ∷ Bx4-201 ∷ Toff234 ∷ CCZ234 ∷ CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ [])
  b1 = at 2 6 (Bx4-201 ∷ []) (refl) ▸
       at 5 1 (CCZ023 ∷ Toff302 ∷ Bx2-31 ∷ Toff302 ∷ CCZ023 ∷ Bx2-31 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸
       at 5 6 (CCZ012 ∷ []) (sym (wl0288 (lit c4))) ▸
       at 5 1 (CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ []) (wp0162 c4) ▸
       at 7 1 (Bx2-41 ∷ []) (refl) ▸
       at 10 1 (Bx2-41 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ234 ∷ Toff234 ∷ Bx4-201 ∷ Toff234 ∷ CCZ234 ∷ CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ []) (Bx2-4301 ∷ [])
  b2 = at 5 6 (Bx4-201 ∷ []) (refl) ▸
       at 0 6 (Bx2-4301 ∷ []) (refl) ▸ done

-- sym-ab @02142041: 18 steps
lem-sym-ab-at02142041 : Ws → ⟪ (Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ []) ⟫ʷ
lem-sym-ab-at02142041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-4031 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ Toff204 ∷ CCZ024 ∷ Bx4-231 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff204 ∷ Bx4-231 ∷ Toff204 ∷ CCZ024 ∷ Bx4-231 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (sym (wl1319 (lit c4))) ▸
       at 2 1 (CCZ023 ∷ Toff023 ∷ CZ01 ∷ Toff023 ∷ CCZ023 ∷ CZ01 ∷ []) (sym (wl1155 (lit c4))) ▸
       at 4 1 (Bx2-01 ∷ []) (refl) ▸
       at 7 1 (Bx2-01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff204 ∷ CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ Toff204 ∷ CCZ024 ∷ Bx4-231 ∷ []) (CCZ024 ∷ Toff204 ∷ Bx0-231 ∷ Toff204 ∷ CCZ024 ∷ CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ [])
  b1 = at 2 6 (Bx0-231 ∷ []) (refl) ▸
       at 5 1 (CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸
       at 5 6 (CCZ123 ∷ []) (sym (wl1319 (lit c4))) ▸
       at 5 1 (CCZ023 ∷ Toff023 ∷ CZ01 ∷ Toff023 ∷ CCZ023 ∷ CZ01 ∷ []) (sym (wl1155 (lit c4))) ▸
       at 7 1 (Bx2-01 ∷ []) (refl) ▸
       at 10 1 (Bx2-01 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ024 ∷ Toff204 ∷ Bx0-231 ∷ Toff204 ∷ CCZ024 ∷ CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ []) (Bx2-0431 ∷ [])
  b2 = at 5 6 (Bx0-231 ∷ []) (refl) ▸
       at 0 6 (Bx2-0431 ∷ []) (refl) ▸ done

-- nat-SWbc @02132130: 23 steps
lem-nat-SWbc-at02132130 : Ws → ⟪ (Sw01 ∷ Bx2-3104 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ []) ⟫ʷ
lem-nat-SWbc-at02132130 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw01 ∷ Bx2-3104 ∷ Sw01 ∷ []) (CCZ023 ∷ Toff203 ∷ CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ Sw01 ∷ CCZ023 ∷ Bx2-34 ∷ Toff213 ∷ CCZ123 ∷ Bx3-204 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx3-204 ∷ Toff213 ∷ CCZ123 ∷ Bx3-204 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0030 (lit c4))) ▸
       at 1 2 (Toff203 ∷ Sw01 ∷ []) (wl0031 (lit c4)) ▸
       at 3 1 (CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ []) (refl) ▸
       at 2 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0135 (lit c4))) ▸
       at 3 2 (Toff312 ∷ Sw01 ∷ []) (wl1340 (lit c4)) ▸
       at 4 2 (Bx2-34 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 5 2 (Toff312 ∷ Sw01 ∷ []) (wl1340 (lit c4)) ▸ done

  b1 : Chain (CCZ023 ∷ Toff203 ∷ CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ Sw01 ∷ CCZ023 ∷ Bx2-34 ∷ Toff213 ∷ CCZ123 ∷ Bx3-204 ∷ Sw01 ∷ []) (CCZ023 ∷ Toff203 ∷ CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ Toff203 ∷ CCZ023 ∷ CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Sw01 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ Sw01 ∷ [])
  b1 = at 6 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0135 (lit c4))) ▸
       at 7 2 (Bx2-34 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 8 2 (Toff203 ∷ Sw01 ∷ []) (wl0031 (lit c4)) ▸
       at 9 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0030 (lit c4))) ▸
       at 11 1 (CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ []) (refl) ▸
       at 10 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0135 (lit c4))) ▸
       at 11 2 (Toff312 ∷ Sw01 ∷ []) (wl1340 (lit c4)) ▸
       at 12 2 (Bx2-34 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸ done

  b2 : Chain (CCZ023 ∷ Toff203 ∷ CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ Toff203 ∷ CCZ023 ∷ CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Sw01 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ Sw01 ∷ []) (Bx2-3014 ∷ [])
  b2 = at 13 2 (Toff312 ∷ Sw01 ∷ []) (wl1340 (lit c4)) ▸
       at 14 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0135 (lit c4))) ▸
       at 15 2 (Bx2-34 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 16 2 [] (wl0018 (lit c4)) ▸
       at 2 6 (Bx3-214 ∷ []) (refl) ▸
       at 5 6 (Bx3-214 ∷ []) (refl) ▸
       at 0 6 (Bx2-3014 ∷ []) (refl) ▸ done

-- nat-SWbc @02132031: 23 steps
lem-nat-SWbc-at02132031 : Ws → ⟪ (Sw01 ∷ Bx2-3014 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ []) ⟫ʷ
lem-nat-SWbc-at02132031 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw01 ∷ Bx2-3014 ∷ Sw01 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ Sw01 ∷ CCZ123 ∷ Bx2-34 ∷ Toff203 ∷ CCZ023 ∷ Bx3-214 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx3-214 ∷ Toff203 ∷ CCZ023 ∷ Bx3-214 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0135 (lit c4))) ▸
       at 1 2 (Toff213 ∷ Sw01 ∷ []) (wl0136 (lit c4)) ▸
       at 3 1 (CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ []) (refl) ▸
       at 2 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0030 (lit c4))) ▸
       at 3 2 (Toff302 ∷ Sw01 ∷ []) (wl0063 (lit c4)) ▸
       at 4 2 (Bx2-34 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 5 2 (Toff302 ∷ Sw01 ∷ []) (wl0063 (lit c4)) ▸ done

  b1 : Chain (CCZ123 ∷ Toff213 ∷ CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ Sw01 ∷ CCZ123 ∷ Bx2-34 ∷ Toff203 ∷ CCZ023 ∷ Bx3-214 ∷ Sw01 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ Toff213 ∷ CCZ123 ∷ CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Sw01 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ Sw01 ∷ [])
  b1 = at 6 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0030 (lit c4))) ▸
       at 7 2 (Bx2-34 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 8 2 (Toff213 ∷ Sw01 ∷ []) (wl0136 (lit c4)) ▸
       at 9 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0135 (lit c4))) ▸
       at 11 1 (CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ []) (refl) ▸
       at 10 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0030 (lit c4))) ▸
       at 11 2 (Toff302 ∷ Sw01 ∷ []) (wl0063 (lit c4)) ▸
       at 12 2 (Bx2-34 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸ done

  b2 : Chain (CCZ123 ∷ Toff213 ∷ CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ Toff213 ∷ CCZ123 ∷ CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Sw01 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ Sw01 ∷ []) (Bx2-3104 ∷ [])
  b2 = at 13 2 (Toff302 ∷ Sw01 ∷ []) (wl0063 (lit c4)) ▸
       at 14 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0030 (lit c4))) ▸
       at 15 2 (Bx2-34 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 16 2 [] (wl0018 (lit c4)) ▸
       at 2 6 (Bx3-204 ∷ []) (refl) ▸
       at 5 6 (Bx3-204 ∷ []) (refl) ▸
       at 0 6 (Bx2-3104 ∷ []) (refl) ▸ done

-- sym-ab @02102441: 18 steps
lem-sym-ab-at02102441 : Ws → ⟪ (Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ []) ⟫ʷ
lem-sym-ab-at02102441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-0431 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ Toff204 ∷ CCZ024 ∷ Bx0-231 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff204 ∷ Bx0-231 ∷ Toff204 ∷ CCZ024 ∷ Bx0-231 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (wl1155 (lit c4)) ▸
       at 2 1 (CCZ234 ∷ Toff423 ∷ CZ14 ∷ Toff423 ∷ CCZ234 ∷ CZ14 ∷ []) (wl1319 (lit c4)) ▸
       at 4 1 (Bx2-41 ∷ []) (refl) ▸
       at 7 1 (Bx2-41 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff204 ∷ CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ Toff204 ∷ CCZ024 ∷ Bx0-231 ∷ []) (CCZ024 ∷ Toff204 ∷ Bx4-231 ∷ Toff204 ∷ CCZ024 ∷ CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ [])
  b1 = at 2 6 (Bx4-231 ∷ []) (refl) ▸
       at 5 1 (CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸
       at 5 6 (CCZ123 ∷ []) (wl1155 (lit c4)) ▸
       at 5 1 (CCZ234 ∷ Toff423 ∷ CZ14 ∷ Toff423 ∷ CCZ234 ∷ CZ14 ∷ []) (wl1319 (lit c4)) ▸
       at 7 1 (Bx2-41 ∷ []) (refl) ▸
       at 10 1 (Bx2-41 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ024 ∷ Toff204 ∷ Bx4-231 ∷ Toff204 ∷ CCZ024 ∷ CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ []) (Bx2-4031 ∷ [])
  b2 = at 5 6 (Bx4-231 ∷ []) (refl) ▸
       at 0 6 (Bx2-4031 ∷ []) (refl) ▸ done

-- cQ @0213243041: 7 steps
lem-cQ-at0213243041 : Ws → ⟪ (CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ
lem-cQ-at0213243041 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ234 ∷ [])
  b0 = at 0 1 (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) (wl0293 (lit c4)) ▸
       at 4 2 (CCZ012 ∷ CS23 ∷ []) (sym (wl0294 (lit c4))) ▸
       at 3 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 2 2 (CCZ012 ∷ CS24⁻ ∷ []) (sym (wp0140 c4)) ▸
       at 1 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 0 2 (CCZ012 ∷ CS24 ∷ []) (sym (wp0141 c4)) ▸
       at 1 5 (CCZ234 ∷ []) (sym (wl0293 (lit c4))) ▸ done

-- sym-ab @0314203241: 18 steps
lem-sym-ab-at0314203241 : Ws → ⟪ (Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ []) ⟫ʷ
lem-sym-ab-at0314203241 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-4021 ∷ []) (CCZ034 ∷ Toff304 ∷ CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ Toff304 ∷ CCZ034 ∷ Bx4-321 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff304 ∷ Bx4-321 ∷ Toff304 ∷ CCZ034 ∷ Bx4-321 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff423 ∷ Bx3-41 ∷ Toff423 ∷ CCZ234 ∷ Bx3-41 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (sym (wl1319 (lit c4))) ▸
       at 2 1 (CCZ023 ∷ Toff023 ∷ CZ01 ∷ Toff023 ∷ CCZ023 ∷ CZ01 ∷ []) (sym (wl1155 (lit c4))) ▸
       at 4 1 (Bx3-01 ∷ []) (refl) ▸
       at 7 1 (Bx3-01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff304 ∷ CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ Toff304 ∷ CCZ034 ∷ Bx4-321 ∷ []) (CCZ034 ∷ Toff304 ∷ Bx0-321 ∷ Toff304 ∷ CCZ034 ∷ CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ [])
  b1 = at 2 6 (Bx0-321 ∷ []) (refl) ▸
       at 5 1 (CCZ234 ∷ Toff423 ∷ Bx3-41 ∷ Toff423 ∷ CCZ234 ∷ Bx3-41 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸
       at 5 6 (CCZ123 ∷ []) (sym (wl1319 (lit c4))) ▸
       at 5 1 (CCZ023 ∷ Toff023 ∷ CZ01 ∷ Toff023 ∷ CCZ023 ∷ CZ01 ∷ []) (sym (wl1155 (lit c4))) ▸
       at 7 1 (Bx3-01 ∷ []) (refl) ▸
       at 10 1 (Bx3-01 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ034 ∷ Toff304 ∷ Bx0-321 ∷ Toff304 ∷ CCZ034 ∷ CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ []) (Bx3-0421 ∷ [])
  b2 = at 5 6 (Bx0-321 ∷ []) (refl) ▸
       at 0 6 (Bx3-0421 ∷ []) (refl) ▸ done

-- nat-SWbc @03122130: 23 steps
lem-nat-SWbc-at03122130 : Ws → ⟪ (Sw01 ∷ Bx3-2104 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ []) ⟫ʷ
lem-nat-SWbc-at03122130 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw01 ∷ Bx3-2104 ∷ Sw01 ∷ []) (CCZ023 ∷ Toff302 ∷ CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ Sw01 ∷ CCZ023 ∷ Bx3-24 ∷ Toff312 ∷ CCZ123 ∷ Bx2-304 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx2-304 ∷ Toff312 ∷ CCZ123 ∷ Bx2-304 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0030 (lit c4))) ▸
       at 1 2 (Toff302 ∷ Sw01 ∷ []) (wl0063 (lit c4)) ▸
       at 3 1 (CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ []) (refl) ▸
       at 2 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0135 (lit c4))) ▸
       at 3 2 (Toff213 ∷ Sw01 ∷ []) (wl0136 (lit c4)) ▸
       at 4 2 (Bx3-24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 5 2 (Toff213 ∷ Sw01 ∷ []) (wl0136 (lit c4)) ▸ done

  b1 : Chain (CCZ023 ∷ Toff302 ∷ CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ Sw01 ∷ CCZ023 ∷ Bx3-24 ∷ Toff312 ∷ CCZ123 ∷ Bx2-304 ∷ Sw01 ∷ []) (CCZ023 ∷ Toff302 ∷ CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ Toff302 ∷ CCZ023 ∷ CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Sw01 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ Sw01 ∷ [])
  b1 = at 6 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0135 (lit c4))) ▸
       at 7 2 (Bx3-24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 8 2 (Toff302 ∷ Sw01 ∷ []) (wl0063 (lit c4)) ▸
       at 9 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0030 (lit c4))) ▸
       at 11 1 (CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ []) (refl) ▸
       at 10 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0135 (lit c4))) ▸
       at 11 2 (Toff213 ∷ Sw01 ∷ []) (wl0136 (lit c4)) ▸
       at 12 2 (Bx3-24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸ done

  b2 : Chain (CCZ023 ∷ Toff302 ∷ CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ Toff302 ∷ CCZ023 ∷ CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Sw01 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ Sw01 ∷ []) (Bx3-2014 ∷ [])
  b2 = at 13 2 (Toff213 ∷ Sw01 ∷ []) (wl0136 (lit c4)) ▸
       at 14 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0135 (lit c4))) ▸
       at 15 2 (Bx3-24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 16 2 [] (wl0018 (lit c4)) ▸
       at 2 6 (Bx2-314 ∷ []) (refl) ▸
       at 5 6 (Bx2-314 ∷ []) (refl) ▸
       at 0 6 (Bx3-2014 ∷ []) (refl) ▸ done

-- nat-SWbc @03122031: 23 steps
lem-nat-SWbc-at03122031 : Ws → ⟪ (Sw01 ∷ Bx3-2014 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ []) ⟫ʷ
lem-nat-SWbc-at03122031 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw01 ∷ Bx3-2014 ∷ Sw01 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ Sw01 ∷ CCZ123 ∷ Bx3-24 ∷ Toff302 ∷ CCZ023 ∷ Bx2-314 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-314 ∷ Toff302 ∷ CCZ023 ∷ Bx2-314 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0135 (lit c4))) ▸
       at 1 2 (Toff312 ∷ Sw01 ∷ []) (wl1340 (lit c4)) ▸
       at 3 1 (CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ []) (refl) ▸
       at 2 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0030 (lit c4))) ▸
       at 3 2 (Toff203 ∷ Sw01 ∷ []) (wl0031 (lit c4)) ▸
       at 4 2 (Bx3-24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 5 2 (Toff203 ∷ Sw01 ∷ []) (wl0031 (lit c4)) ▸ done

  b1 : Chain (CCZ123 ∷ Toff312 ∷ CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ Sw01 ∷ CCZ123 ∷ Bx3-24 ∷ Toff302 ∷ CCZ023 ∷ Bx2-314 ∷ Sw01 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ Toff312 ∷ CCZ123 ∷ CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Sw01 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ Sw01 ∷ [])
  b1 = at 6 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0030 (lit c4))) ▸
       at 7 2 (Bx3-24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 8 2 (Toff312 ∷ Sw01 ∷ []) (wl1340 (lit c4)) ▸
       at 9 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0135 (lit c4))) ▸
       at 11 1 (CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ []) (refl) ▸
       at 10 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0030 (lit c4))) ▸
       at 11 2 (Toff203 ∷ Sw01 ∷ []) (wl0031 (lit c4)) ▸
       at 12 2 (Bx3-24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸ done

  b2 : Chain (CCZ123 ∷ Toff312 ∷ CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ Toff312 ∷ CCZ123 ∷ CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Sw01 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ Sw01 ∷ []) (Bx3-2104 ∷ [])
  b2 = at 13 2 (Toff203 ∷ Sw01 ∷ []) (wl0031 (lit c4)) ▸
       at 14 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0030 (lit c4))) ▸
       at 15 2 (Bx3-24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 16 2 [] (wl0018 (lit c4)) ▸
       at 2 6 (Bx2-304 ∷ []) (refl) ▸
       at 5 6 (Bx2-304 ∷ []) (refl) ▸
       at 0 6 (Bx3-2104 ∷ []) (refl) ▸ done

-- sym-ab @0310243241: 18 steps
lem-sym-ab-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ []) ⟫ʷ
lem-sym-ab-at0310243241 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-0421 ∷ []) (CCZ034 ∷ Toff304 ∷ CCZ234 ∷ Toff423 ∷ Bx3-41 ∷ Toff423 ∷ CCZ234 ∷ Bx3-41 ∷ Toff304 ∷ CCZ034 ∷ Bx0-321 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff304 ∷ Bx0-321 ∷ Toff304 ∷ CCZ034 ∷ Bx0-321 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (wl1155 (lit c4)) ▸
       at 2 1 (CCZ234 ∷ Toff423 ∷ CZ14 ∷ Toff423 ∷ CCZ234 ∷ CZ14 ∷ []) (wl1319 (lit c4)) ▸
       at 4 1 (Bx3-41 ∷ []) (refl) ▸
       at 7 1 (Bx3-41 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff304 ∷ CCZ234 ∷ Toff423 ∷ Bx3-41 ∷ Toff423 ∷ CCZ234 ∷ Bx3-41 ∷ Toff304 ∷ CCZ034 ∷ Bx0-321 ∷ []) (CCZ034 ∷ Toff304 ∷ Bx4-321 ∷ Toff304 ∷ CCZ034 ∷ CCZ234 ∷ Toff423 ∷ Bx3-41 ∷ Toff423 ∷ CCZ234 ∷ Bx3-41 ∷ [])
  b1 = at 2 6 (Bx4-321 ∷ []) (refl) ▸
       at 5 1 (CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸
       at 5 6 (CCZ123 ∷ []) (wl1155 (lit c4)) ▸
       at 5 1 (CCZ234 ∷ Toff423 ∷ CZ14 ∷ Toff423 ∷ CCZ234 ∷ CZ14 ∷ []) (wl1319 (lit c4)) ▸
       at 7 1 (Bx3-41 ∷ []) (refl) ▸
       at 10 1 (Bx3-41 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ034 ∷ Toff304 ∷ Bx4-321 ∷ Toff304 ∷ CCZ034 ∷ CCZ234 ∷ Toff423 ∷ Bx3-41 ∷ Toff423 ∷ CCZ234 ∷ Bx3-41 ∷ []) (Bx3-4021 ∷ [])
  b2 = at 5 6 (Bx4-321 ∷ []) (refl) ▸
       at 0 6 (Bx3-4021 ∷ []) (refl) ▸ done

-- sym-ab @0330: 18 steps
lem-sym-ab-at0330 : Ws → ⟪ (Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ []) ⟫ʷ
lem-sym-ab-at0330 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-1204 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ Toff312 ∷ CCZ123 ∷ Bx1-304 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff312 ∷ Bx1-304 ∷ Toff312 ∷ CCZ123 ∷ Bx1-304 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (wp0008 c4) ▸
       at 2 1 (CCZ023 ∷ Toff203 ∷ CZ24 ∷ Toff203 ∷ CCZ023 ∷ CZ24 ∷ []) (sym (wp0111 c4)) ▸
       at 4 1 (Bx3-24 ∷ []) (refl) ▸
       at 7 1 (Bx3-24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff312 ∷ CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ Toff312 ∷ CCZ123 ∷ Bx1-304 ∷ []) (CCZ123 ∷ Toff312 ∷ Bx2-304 ∷ Toff312 ∷ CCZ123 ∷ CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ [])
  b1 = at 2 6 (Bx2-304 ∷ []) (refl) ▸
       at 5 1 (CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸
       at 5 6 (CCZ034 ∷ []) (wp0008 c4) ▸
       at 5 1 (CCZ023 ∷ Toff203 ∷ CZ24 ∷ Toff203 ∷ CCZ023 ∷ CZ24 ∷ []) (sym (wp0111 c4)) ▸
       at 7 1 (Bx3-24 ∷ []) (refl) ▸
       at 10 1 (Bx3-24 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ123 ∷ Toff312 ∷ Bx2-304 ∷ Toff312 ∷ CCZ123 ∷ CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ []) (Bx3-2104 ∷ [])
  b2 = at 5 6 (Bx2-304 ∷ []) (refl) ▸
       at 0 6 (Bx3-2104 ∷ []) (refl) ▸ done

-- sym-ab @022330: 18 steps
lem-sym-ab-at022330 : Ws → ⟪ (Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ []) ⟫ʷ
lem-sym-ab-at022330 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-1304 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ Toff213 ∷ CCZ123 ∷ Bx1-204 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff213 ∷ Bx1-204 ∷ Toff213 ∷ CCZ123 ∷ Bx1-204 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (wp0130 c4) ▸
       at 2 1 (CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ []) (sym (wp0131 c4)) ▸
       at 4 1 (Bx2-34 ∷ []) (refl) ▸
       at 7 1 (Bx2-34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff213 ∷ CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ Toff213 ∷ CCZ123 ∷ Bx1-204 ∷ []) (CCZ123 ∷ Toff213 ∷ Bx3-204 ∷ Toff213 ∷ CCZ123 ∷ CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ [])
  b1 = at 2 6 (Bx3-204 ∷ []) (refl) ▸
       at 5 1 (CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸
       at 5 6 (CCZ024 ∷ []) (wp0130 c4) ▸
       at 5 1 (CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ []) (sym (wp0131 c4)) ▸
       at 7 1 (Bx2-34 ∷ []) (refl) ▸
       at 10 1 (Bx2-34 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ123 ∷ Toff213 ∷ Bx3-204 ∷ Toff213 ∷ CCZ123 ∷ CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ []) (Bx2-3104 ∷ [])
  b2 = at 5 6 (Bx3-204 ∷ []) (refl) ▸
       at 0 6 (Bx2-3104 ∷ []) (refl) ▸ done

-- sym-ab @03122130: 18 steps
lem-sym-ab-at03122130 : Ws → ⟪ (Bx3-2104 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-sym-ab-at03122130 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-2104 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ Toff312 ∷ CCZ123 ∷ Bx2-304 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff312 ∷ Bx2-304 ∷ Toff312 ∷ CCZ123 ∷ Bx2-304 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (wp0111 c4) ▸
       at 2 1 (CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (sym (wp0008 c4)) ▸
       at 4 1 (Bx3-14 ∷ []) (refl) ▸
       at 7 1 (Bx3-14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff312 ∷ CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ Toff312 ∷ CCZ123 ∷ Bx2-304 ∷ []) (CCZ123 ∷ Toff312 ∷ Bx1-304 ∷ Toff312 ∷ CCZ123 ∷ CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ [])
  b1 = at 2 6 (Bx1-304 ∷ []) (refl) ▸
       at 5 1 (CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸
       at 5 6 (CCZ034 ∷ []) (wp0111 c4) ▸
       at 5 1 (CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (sym (wp0008 c4)) ▸
       at 7 1 (Bx3-14 ∷ []) (refl) ▸
       at 10 1 (Bx3-14 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ123 ∷ Toff312 ∷ Bx1-304 ∷ Toff312 ∷ CCZ123 ∷ CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ []) (Bx3-1204 ∷ [])
  b2 = at 5 6 (Bx1-304 ∷ []) (refl) ▸
       at 0 6 (Bx3-1204 ∷ []) (refl) ▸ done
