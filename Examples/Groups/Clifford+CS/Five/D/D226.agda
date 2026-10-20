{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D226 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0214 ; wl0220 ; wl0221 ; wl0222 ; wl0256 ; wl0275 ; wl0348 ; wl0447 ; wl0448 ; wl0489 ; wl0498 ; wl0514 ; wl0670 ; wl0698 ; wl0761 ; wl0850 ; wl0852 ; wl1112 ; wl1206 ; wl1344 ; wl1404 ; wl1405 ; wl1406 ; wl1407 ; wl1408 ; wp0006 ; wp0053 ; wp0054 ; wp0061 ; wp0065 ; wp0066 ; wp0069 ; wp0070 ; wp0173 ; wp0268 ; wp0272 ; wp0298 ; wp0299 ; wp0543 ; wp0550 ; wp0574 ; wp0593 ; wp0683 ; wp0725 ; wp0823 ; wp1209 ; wp1217 ; wp1253 ; wp1254 ; wp1255 ; wp1256 ; wp1257 ; wp1258)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-box-perm-2134-at03102132)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-box-perm-2134-at021021 ; lem-box-perm-2134-at0220 ; lem-box-perm-2134-at032032)
open import Examples.Groups.Clifford+CS.Five.D.D012 using (lem-CK-box-at033440)
open import Examples.Groups.Clifford+CS.Five.D.D014 using (lem-box-cP-at032032)
open import Examples.Groups.Clifford+CS.Five.D.D017 using (lem-box-cP-at02102331 ; lem-box-cP-at142142 ; lem-box-perm-1324-at021021 ; lem-box-perm-3124-at021021 ; lem-box-perm-3214-at032032 ; lem-box2-at032032)
open import Examples.Groups.Clifford+CS.Five.D.D021 using (lem-box-perm-2314-at02132031 ; lem-box-perm-2431-at142142 ; lem-box-perm-3214-at03122031 ; lem-box2-at033440 ; lem-box2-at142142)
open import Examples.Groups.Clifford+CS.Five.D.D030 using (lem-box-box-3-at021021)
open import Examples.Groups.Clifford+CS.Five.D.D032 using (lem-box-perm-2341-at0314213042 ; lem-box-perm-3241-at142142 ; lem-box-perm-4123-at032032 ; lem-box-perm-4213-at132132)
open import Examples.Groups.Clifford+CS.Five.D.D037 using (lem-box-box-1-at03102132)
open import Examples.Groups.Clifford+CS.Five.D.D044 using (lem-box-box-3-at03102132)
open import Examples.Groups.Clifford+CS.Five.D.D071 using (lem-Tu-box-at0220 ; lem-Tu-box-at0314213042)
open import Examples.Groups.Clifford+CS.Five.D.D223 using (lem-L-CCZ013-0 ; lem-L-Toff-0)
open import Examples.Groups.Clifford+CS.Five.D.D225 using (lem-nf-toff-cczat0)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CCZ013-CS24 ; lem-comm-CCZ013-CSd24 ; lem-comm-CCZ014-CS23 ; lem-comm-CCZ014-CSd23 ; lem-comm-TOFF214-CX03)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-CCZ023-CX14 ; lem-comm-TOFF023-CX14)

-- F1-toff-ccz@0: 310 steps
lem-F1-toff-cczat0 : Ws → ⟪ (CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ
lem-F1-toff-cczat0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (run b38))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx2-0134 ∷ Bx3-2014 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ [])
  b0 = at 0 48 (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ []) (lem-L-Toff-0 c4) ▸
       at 4 75 (Bx2-0134 ∷ []) (lem-L-CCZ013-0 c4) ▸
       at 5 48 (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ []) (lem-L-Toff-0 c4) ▸
       at 4 0 (Toff312 ∷ Toff312 ∷ []) (sym (wl0489 (lit c4))) ▸
       at 6 1 (Bx2-1034 ∷ []) (lem-box-perm-2134-at021021 c4) ▸
       at 5 3 (Bx2-1034 ∷ Bx3-1024 ∷ []) (lem-Tu-box-at0220 c4) ▸
       at 5 1 (Bx2-0134 ∷ []) (lem-box-perm-2134-at0220 c4) ▸
       at 6 1 (Bx3-2014 ∷ []) (lem-box-perm-3214-at032032 c4) ▸ done

  b1 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx2-0134 ∷ Bx3-2014 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ K0 ∷ CS34 ∷ CX03 ∷ Toff214 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0⁻ ∷ Toff312 ∷ Toff034 ∷ [])
  b1 = at 5 2 (Bx3-2014 ∷ Bx2-0134 ∷ []) (lem-box-box-3-at021021 c4) ▸
       at 5 1 (Bx3-1024 ∷ []) (lem-box-perm-3214-at03122031 c4) ▸
       at 6 1 (Bx2-0314 ∷ []) (lem-box-perm-1324-at021021 c4) ▸
       at 6 1 (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-box-cP-at02102331 c4) ▸
       at 10 1 (K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1253 c4)) ▸
       at 9 2 (K0 ∷ Toff214 ∷ []) (sym (c₁ (K) (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑))) ▸
       at 10 2 (CS34 ∷ Toff214 ∷ []) (sym (wl0761 (lit c4))) ▸
       at 11 2 (CX03 ∷ Toff214 ∷ []) (lem-comm-TOFF214-CX03 (lit c4)) ▸ done

  b2 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ K0 ∷ CS34 ∷ CX03 ∷ Toff214 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0⁻ ∷ Toff312 ∷ Toff034 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ CCZ023 ∷ K0 ∷ Toff214 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0⁻ ∷ CCZ234 ∷ CCZ023 ∷ Toff214 ∷ Toff312 ∷ Toff034 ∷ [])
  b2 = at 12 2 (CS34⁻ ∷ Toff214 ∷ []) (sym (wl1404 (lit c4))) ▸
       at 13 2 (CX03 ∷ Toff214 ∷ []) (lem-comm-TOFF214-CX03 (lit c4)) ▸
       at 14 2 (CS04 ∷ Toff214 ∷ []) (sym (wp0683 c4)) ▸
       at 15 2 (K0⁻ ∷ Toff214 ∷ []) (sym (c₁ (K • iI) (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑))) ▸
       at 9 7 (Toff034 ∷ []) (wp1253 c4) ▸
       at 8 2 (Toff034 ∷ CCZ234 ∷ CCZ023 ∷ []) (wp1254 c4) ▸
       at 8 1 (K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1253 c4)) ▸
       at 7 2 (K0 ∷ Toff214 ∷ []) (sym (c₁ (K) (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑))) ▸ done

  b3 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ CCZ023 ∷ K0 ∷ Toff214 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0⁻ ∷ CCZ234 ∷ CCZ023 ∷ Toff214 ∷ Toff312 ∷ Toff034 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ CCZ023 ∷ Toff034 ∷ CCZ134 ∷ CCZ234 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ Toff312 ∷ Toff034 ∷ [])
  b3 = at 8 2 (CS34 ∷ Toff214 ∷ []) (sym (wl0761 (lit c4))) ▸
       at 9 2 (CX03 ∷ Toff214 ∷ []) (lem-comm-TOFF214-CX03 (lit c4)) ▸
       at 10 2 (CS34⁻ ∷ Toff214 ∷ []) (sym (wl1404 (lit c4))) ▸
       at 11 2 (CX03 ∷ Toff214 ∷ []) (lem-comm-TOFF214-CX03 (lit c4)) ▸
       at 12 2 (CS04 ∷ Toff214 ∷ []) (sym (wp0683 c4)) ▸
       at 13 2 (K0⁻ ∷ Toff214 ∷ []) (sym (c₁ (K • iI) (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑))) ▸
       at 7 7 (Toff034 ∷ []) (wp1253 c4) ▸
       at 8 2 (CCZ134 ∷ CCZ234 ∷ Toff214 ∷ []) (sym (wl1344 (lit c4))) ▸ done

  b4 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ CCZ023 ∷ Toff034 ∷ CCZ134 ∷ CCZ234 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ Toff312 ∷ Toff034 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ234 ∷ CCZ134 ∷ CCZ023 ∷ CCZ234 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ Toff312 ∷ Toff034 ∷ [])
  b4 = at 6 2 (Toff034 ∷ CCZ234 ∷ CCZ023 ∷ []) (wp1254 c4) ▸
       at 9 1 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl0698 (lit c4)) ▸
       at 8 2 (CS34 ∷ CCZ023 ∷ []) (wp0543 c4) ▸
       at 9 2 (CX14 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CX14 (lit c4)) ▸
       at 10 2 (CS34⁻ ∷ CCZ023 ∷ []) (wp0574 c4) ▸
       at 11 2 (CX14 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CX14 (lit c4)) ▸
       at 12 2 (CS13 ∷ CCZ023 ∷ []) (wl0670 (lit c4)) ▸
       at 8 5 (CCZ134 ∷ []) (sym (wl0698 (lit c4))) ▸ done

  b5 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ234 ∷ CCZ134 ∷ CCZ023 ∷ CCZ234 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ Toff312 ∷ Toff034 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Bx2-0134 ∷ Bx3-1024 ∷ Toff034 ∷ [])
  b5 = at 9 2 (CCZ234 ∷ CCZ023 ∷ []) (wp0550 c4) ▸
       at 7 3 (CCZ134 ∷ []) (sym (wl1405 (lit c4))) ▸
       at 8 4 (Bx2-0314 ∷ []) (sym (lem-box-cP-at02102331 c4)) ▸
       at 8 1 (Bx2-0134 ∷ []) (sym (lem-box-perm-1324-at021021 c4)) ▸
       at 8 0 (Toff312 ∷ Toff312 ∷ []) (sym (wl0489 (lit c4))) ▸
       at 10 1 (Bx2-1034 ∷ []) (lem-box-perm-2134-at021021 c4) ▸
       at 9 3 (Bx2-1034 ∷ Bx3-1024 ∷ []) (lem-Tu-box-at0220 c4) ▸
       at 9 1 (Bx2-0134 ∷ []) (lem-box-perm-2134-at0220 c4) ▸ done

  b6 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Bx2-0134 ∷ Bx3-1024 ∷ Toff034 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Bx3-1024 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ K0 ∷ CS34 ∷ Toff214 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0⁻ ∷ [])
  b6 = at 10 1 (Bx3-2014 ∷ []) (lem-box-perm-3214-at032032 c4) ▸
       at 9 2 (Bx3-2014 ∷ Bx2-0134 ∷ []) (lem-box-box-3-at021021 c4) ▸
       at 9 1 (Bx3-1024 ∷ []) (lem-box-perm-3214-at03122031 c4) ▸
       at 10 1 (Bx2-0314 ∷ []) (lem-box-perm-1324-at021021 c4) ▸
       at 10 1 (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-box-cP-at02102331 c4) ▸
       at 14 1 (K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1253 c4)) ▸
       at 13 2 (K0 ∷ Toff214 ∷ []) (sym (c₁ (K) (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑))) ▸
       at 14 2 (CS34 ∷ Toff214 ∷ []) (sym (wl0761 (lit c4))) ▸ done

  b7 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Bx3-1024 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ K0 ∷ CS34 ∷ Toff214 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0⁻ ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Bx3-1024 ∷ CCZ023 ∷ Toff214 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0⁻ ∷ CCZ234 ∷ CCZ023 ∷ Toff214 ∷ [])
  b7 = at 15 2 (CX03 ∷ Toff214 ∷ []) (lem-comm-TOFF214-CX03 (lit c4)) ▸
       at 16 2 (CS34⁻ ∷ Toff214 ∷ []) (sym (wl1404 (lit c4))) ▸
       at 17 2 (CX03 ∷ Toff214 ∷ []) (lem-comm-TOFF214-CX03 (lit c4)) ▸
       at 18 2 (CS04 ∷ Toff214 ∷ []) (sym (wp0683 c4)) ▸
       at 19 2 (K0⁻ ∷ Toff214 ∷ []) (sym (c₁ (K • iI) (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑))) ▸
       at 13 7 (Toff034 ∷ []) (wp1253 c4) ▸
       at 12 2 (Toff034 ∷ CCZ234 ∷ CCZ023 ∷ []) (wp1254 c4) ▸
       at 12 1 (K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1253 c4)) ▸ done

  b8 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Bx3-1024 ∷ CCZ023 ∷ Toff214 ∷ K0 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K0⁻ ∷ CCZ234 ∷ CCZ023 ∷ Toff214 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Bx3-1024 ∷ CCZ023 ∷ Toff034 ∷ Toff214 ∷ CCZ234 ∷ CCZ023 ∷ Toff214 ∷ [])
  b8 = at 11 2 (K0 ∷ Toff214 ∷ []) (sym (c₁ (K) (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑))) ▸
       at 12 2 (CS34 ∷ Toff214 ∷ []) (sym (wl0761 (lit c4))) ▸
       at 13 2 (CX03 ∷ Toff214 ∷ []) (lem-comm-TOFF214-CX03 (lit c4)) ▸
       at 14 2 (CS34⁻ ∷ Toff214 ∷ []) (sym (wl1404 (lit c4))) ▸
       at 15 2 (CX03 ∷ Toff214 ∷ []) (lem-comm-TOFF214-CX03 (lit c4)) ▸
       at 16 2 (CS04 ∷ Toff214 ∷ []) (sym (wp0683 c4)) ▸
       at 17 2 (K0⁻ ∷ Toff214 ∷ []) (sym (c₁ (K • iI) (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑))) ▸
       at 11 7 (Toff034 ∷ []) (wp1253 c4) ▸ done

  b9 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Bx3-1024 ∷ CCZ023 ∷ Toff034 ∷ Toff214 ∷ CCZ234 ∷ CCZ023 ∷ Toff214 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ234 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ CCZ023 ∷ CCZ234 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ [])
  b9 = at 12 2 (CCZ134 ∷ CCZ234 ∷ Toff214 ∷ []) (sym (wl1344 (lit c4))) ▸
       at 10 2 (Toff034 ∷ CCZ234 ∷ CCZ023 ∷ []) (wp1254 c4) ▸
       at 13 1 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl0698 (lit c4)) ▸
       at 12 2 (CS34 ∷ CCZ023 ∷ []) (wp0543 c4) ▸
       at 13 2 (CX14 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CX14 (lit c4)) ▸
       at 14 2 (CS34⁻ ∷ CCZ023 ∷ []) (wp0574 c4) ▸
       at 15 2 (CX14 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CX14 (lit c4)) ▸
       at 16 2 (CS13 ∷ CCZ023 ∷ []) (wl0670 (lit c4)) ▸ done

  b10 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ234 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ CCZ023 ∷ CCZ234 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Bx3-4102 ∷ Bx0-4132 ∷ CCZ134 ∷ Bx2-0134 ∷ [])
  b10 = at 12 5 (CCZ134 ∷ []) (sym (wl0698 (lit c4))) ▸
       at 13 2 (CCZ234 ∷ CCZ023 ∷ []) (wp0550 c4) ▸
       at 11 3 (CCZ134 ∷ []) (sym (wl1405 (lit c4))) ▸
       at 12 4 (Bx2-0314 ∷ []) (sym (lem-box-cP-at02102331 c4)) ▸
       at 12 1 (Bx2-0134 ∷ []) (sym (lem-box-perm-1324-at021021 c4)) ▸
       at 9 0 (Toff034 ∷ Toff034 ∷ []) (sym (wp0006 c4)) ▸
       at 11 1 (Bx3-4102 ∷ []) (lem-box-perm-4123-at032032 c4) ▸
       at 10 3 (Bx3-4102 ∷ Bx0-4132 ∷ []) (lem-Tu-box-at0314213042 c4) ▸ done

  b11 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Bx3-4102 ∷ Bx0-4132 ∷ CCZ134 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ CCZ124 ∷ CCZ134 ∷ Toff324 ∷ Bx2-0134 ∷ [])
  b11 = at 10 1 (Bx3-1024 ∷ []) (lem-box-perm-2341-at0314213042 c4) ▸
       at 10 1 (Bx3-0124 ∷ []) (lem-box-perm-2134-at032032 c4) ▸
       at 11 1 (Bx0-3124 ∷ []) (lem-box-perm-3241-at142142 c4) ▸
       at 10 2 (Bx0-3124 ∷ Bx3-0124 ∷ []) (lem-box-box-1-at03102132 c4) ▸
       at 10 1 (Bx0-4132 ∷ []) (lem-box-perm-4213-at132132 c4) ▸
       at 11 1 (Bx3-1024 ∷ []) (lem-box-perm-2134-at03102132 c4) ▸
       at 11 1 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at032032 c4) ▸
       at 14 2 (CCZ124 ∷ CCZ134 ∷ Toff324 ∷ []) (sym (wl1406 (lit c4))) ▸ done

  b12 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ CCZ124 ∷ CCZ134 ∷ Toff324 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ013 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ CCZ013 ∷ Toff324 ∷ Bx2-0134 ∷ [])
  b12 = at 14 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 13 2 (CS24 ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CS24 (lit c4)) ▸
       at 14 2 (CX12 ∷ CCZ013 ∷ []) (wl0448 (lit c4)) ▸
       at 15 2 (CS24⁻ ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CSd24 (lit c4)) ▸
       at 16 2 (CX12 ∷ CCZ013 ∷ []) (wl0448 (lit c4)) ▸
       at 17 2 (CS14 ∷ CCZ013 ∷ []) (wp0299 c4) ▸
       at 13 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 14 2 (CCZ134 ∷ CCZ013 ∷ []) (wp0593 c4) ▸ done

  b13 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ013 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ CCZ013 ∷ Toff324 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Bx2-0134 ∷ Bx3-1024 ∷ [])
  b13 = at 12 3 (CCZ134 ∷ Toff324 ∷ []) (sym (wl1206 (lit c4))) ▸
       at 11 2 (CCZ134 ∷ CCZ013 ∷ []) (wp0593 c4) ▸
       at 12 4 (Bx3-1024 ∷ []) (sym (lem-box-cP-at032032 c4)) ▸
       at 12 1 (Bx3-0124 ∷ []) (lem-box-perm-2134-at032032 c4) ▸
       at 13 1 (Bx2-3014 ∷ []) (lem-box-perm-3124-at021021 c4) ▸
       at 12 2 (Bx2-3014 ∷ Bx3-0124 ∷ []) (lem-box-box-3-at03102132 c4) ▸
       at 12 1 (Bx2-0134 ∷ []) (lem-box-perm-2314-at02132031 c4) ▸
       at 13 1 (Bx3-1024 ∷ []) (lem-box-perm-2134-at03102132 c4) ▸ done

  b14 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Bx2-0134 ∷ Bx3-1024 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CCZ134 ∷ Toff023 ∷ Bx2-0134 ∷ Bx3-1024 ∷ [])
  b14 = at 10 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at142142 c4) ▸
       at 14 1 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl0698 (lit c4)) ▸
       at 13 2 (CS34 ∷ Toff023 ∷ []) (sym (wp0725 c4)) ▸
       at 14 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 15 2 (CS34⁻ ∷ Toff023 ∷ []) (sym (wp0823 c4)) ▸
       at 16 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 17 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 13 5 (CCZ134 ∷ []) (sym (wl0698 (lit c4))) ▸ done

  b15 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CCZ134 ∷ Toff023 ∷ Bx2-0134 ∷ Bx3-1024 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ CCZ014 ∷ CCZ134 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Bx2-0134 ∷ Bx3-1024 ∷ [])
  b15 = at 12 2 (CCZ134 ∷ CCZ014 ∷ []) (wp0272 c4) ▸
       at 12 1 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl0698 (lit c4)) ▸
       at 11 2 (CS34 ∷ Toff023 ∷ []) (sym (wp0725 c4)) ▸
       at 12 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 13 2 (CS34⁻ ∷ Toff023 ∷ []) (sym (wp0823 c4)) ▸
       at 14 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 15 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 11 5 (CCZ134 ∷ []) (sym (wl0698 (lit c4))) ▸ done

  b16 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Bx3-1024 ∷ Toff034 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ CCZ014 ∷ CCZ134 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Bx2-0134 ∷ Bx3-1024 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx3-0124 ∷ Bx0-3124 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ Bx0-4132 ∷ Bx2-0134 ∷ Bx3-1024 ∷ [])
  b16 = at 10 2 (CCZ134 ∷ CCZ014 ∷ []) (wp0272 c4) ▸
       at 11 4 (Bx0-4132 ∷ []) (sym (lem-box-cP-at142142 c4)) ▸
       at 5 0 (Toff034 ∷ Toff034 ∷ []) (sym (wp0006 c4)) ▸
       at 7 1 (Bx3-4102 ∷ []) (lem-box-perm-4123-at032032 c4) ▸
       at 6 3 (Bx3-4102 ∷ Bx0-4132 ∷ []) (lem-Tu-box-at0314213042 c4) ▸
       at 6 1 (Bx3-1024 ∷ []) (lem-box-perm-2341-at0314213042 c4) ▸
       at 6 1 (Bx3-0124 ∷ []) (lem-box-perm-2134-at032032 c4) ▸
       at 7 1 (Bx0-3124 ∷ []) (lem-box-perm-3241-at142142 c4) ▸ done

  b17 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx3-0124 ∷ Bx0-3124 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ Bx0-4132 ∷ Bx2-0134 ∷ Bx3-1024 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ013 ∷ Toff324 ∷ CS24 ∷ CX12 ∷ CCZ013 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ134 ∷ Toff324 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ Bx0-4132 ∷ Bx2-0134 ∷ Bx3-1024 ∷ [])
  b17 = at 6 2 (Bx0-3124 ∷ Bx3-0124 ∷ []) (lem-box-box-1-at03102132 c4) ▸
       at 6 1 (Bx0-4132 ∷ []) (lem-box-perm-4213-at132132 c4) ▸
       at 7 1 (Bx3-1024 ∷ []) (lem-box-perm-2134-at03102132 c4) ▸
       at 7 1 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at032032 c4) ▸
       at 10 2 (CCZ124 ∷ CCZ134 ∷ Toff324 ∷ []) (sym (wl1406 (lit c4))) ▸
       at 10 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 9 2 (CS24 ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CS24 (lit c4)) ▸
       at 10 2 (CX12 ∷ CCZ013 ∷ []) (wl0448 (lit c4)) ▸ done

  b18 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ013 ∷ Toff324 ∷ CS24 ∷ CX12 ∷ CCZ013 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ134 ∷ Toff324 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ Bx0-4132 ∷ Bx2-0134 ∷ Bx3-1024 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Bx3-1024 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ Bx0-4132 ∷ Bx2-0134 ∷ Bx3-1024 ∷ [])
  b18 = at 11 2 (CS24⁻ ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CSd24 (lit c4)) ▸
       at 12 2 (CX12 ∷ CCZ013 ∷ []) (wl0448 (lit c4)) ▸
       at 13 2 (CS14 ∷ CCZ013 ∷ []) (wp0299 c4) ▸
       at 9 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 10 2 (CCZ134 ∷ CCZ013 ∷ []) (wp0593 c4) ▸
       at 8 3 (CCZ134 ∷ Toff324 ∷ []) (sym (wl1206 (lit c4))) ▸
       at 7 2 (CCZ134 ∷ CCZ013 ∷ []) (wp0593 c4) ▸
       at 8 4 (Bx3-1024 ∷ []) (sym (lem-box-cP-at032032 c4)) ▸ done

  b19 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Bx3-1024 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ Bx0-4132 ∷ Bx2-0134 ∷ Bx3-1024 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ CCZ013 ∷ Toff312 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Toff324 ∷ CX01 ∷ CS02 ∷ CCZ013 ∷ Toff324 ∷ Toff034 ∷ CCZ134 ∷ Bx0-4132 ∷ Bx2-0134 ∷ Bx3-1024 ∷ [])
  b19 = at 8 1 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at032032 c4) ▸
       at 11 2 (Toff312 ∷ Toff324 ∷ []) (sym (wl0852 (lit c4))) ▸
       at 10 2 (Toff312 ∷ CCZ012 ∷ CCZ013 ∷ []) (wl0498 (lit c4)) ▸
       at 9 2 (Toff312 ∷ Toff324 ∷ []) (sym (wl0852 (lit c4))) ▸
       at 11 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 10 2 (CS12 ∷ Toff324 ∷ []) (sym (wl0214 (lit c4))) ▸
       at 11 2 (CX01 ∷ Toff324 ∷ []) (sym (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 12 2 (CS12⁻ ∷ Toff324 ∷ []) (sym (wl0447 (lit c4))) ▸ done

  b20 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ CCZ013 ∷ Toff312 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Toff324 ∷ CX01 ∷ CS02 ∷ CCZ013 ∷ Toff324 ∷ Toff034 ∷ CCZ134 ∷ Bx0-4132 ∷ Bx2-0134 ∷ Bx3-1024 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Bx3-4102 ∷ Bx0-4132 ∷ CCZ134 ∷ Bx0-4132 ∷ Bx2-0134 ∷ Bx3-1024 ∷ [])
  b20 = at 13 2 (CX01 ∷ Toff324 ∷ []) (sym (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 14 2 (CS02 ∷ Toff324 ∷ []) (sym (wp0298 c4)) ▸
       at 10 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 8 3 (Toff312 ∷ CCZ013 ∷ []) (wl0850 (lit c4)) ▸
       at 9 4 (Bx3-1024 ∷ []) (sym (lem-box-cP-at032032 c4)) ▸
       at 9 0 (Toff034 ∷ Toff034 ∷ []) (sym (wp0006 c4)) ▸
       at 11 1 (Bx3-4102 ∷ []) (lem-box-perm-4123-at032032 c4) ▸
       at 10 3 (Bx3-4102 ∷ Bx0-4132 ∷ []) (lem-Tu-box-at0314213042 c4) ▸ done

  b21 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Bx3-4102 ∷ Bx0-4132 ∷ CCZ134 ∷ Bx0-4132 ∷ Bx2-0134 ∷ Bx3-1024 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ CCZ124 ∷ CCZ134 ∷ Toff324 ∷ Bx0-4132 ∷ Bx2-0134 ∷ Bx3-1024 ∷ [])
  b21 = at 10 1 (Bx3-1024 ∷ []) (lem-box-perm-2341-at0314213042 c4) ▸
       at 10 1 (Bx3-0124 ∷ []) (lem-box-perm-2134-at032032 c4) ▸
       at 11 1 (Bx0-3124 ∷ []) (lem-box-perm-3241-at142142 c4) ▸
       at 10 2 (Bx0-3124 ∷ Bx3-0124 ∷ []) (lem-box-box-1-at03102132 c4) ▸
       at 10 1 (Bx0-4132 ∷ []) (lem-box-perm-4213-at132132 c4) ▸
       at 11 1 (Bx3-1024 ∷ []) (lem-box-perm-2134-at03102132 c4) ▸
       at 11 1 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at032032 c4) ▸
       at 14 2 (CCZ124 ∷ CCZ134 ∷ Toff324 ∷ []) (sym (wl1406 (lit c4))) ▸ done

  b22 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ CCZ124 ∷ CCZ134 ∷ Toff324 ∷ Bx0-4132 ∷ Bx2-0134 ∷ Bx3-1024 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ013 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ CCZ013 ∷ Toff324 ∷ Bx0-4132 ∷ Bx2-0134 ∷ Bx3-1024 ∷ [])
  b22 = at 14 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 13 2 (CS24 ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CS24 (lit c4)) ▸
       at 14 2 (CX12 ∷ CCZ013 ∷ []) (wl0448 (lit c4)) ▸
       at 15 2 (CS24⁻ ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CSd24 (lit c4)) ▸
       at 16 2 (CX12 ∷ CCZ013 ∷ []) (wl0448 (lit c4)) ▸
       at 17 2 (CS14 ∷ CCZ013 ∷ []) (wp0299 c4) ▸
       at 13 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 14 2 (CCZ134 ∷ CCZ013 ∷ []) (wp0593 c4) ▸ done

  b23 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ013 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ CCZ013 ∷ Toff324 ∷ Bx0-4132 ∷ Bx2-0134 ∷ Bx3-1024 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Bx0-4132 ∷ Bx3-1024 ∷ Bx2-0134 ∷ Bx3-1024 ∷ [])
  b23 = at 12 3 (CCZ134 ∷ Toff324 ∷ []) (sym (wl1206 (lit c4))) ▸
       at 11 2 (CCZ134 ∷ CCZ013 ∷ []) (wp0593 c4) ▸
       at 12 4 (Bx3-1024 ∷ []) (sym (lem-box-cP-at032032 c4)) ▸
       at 12 1 (Bx3-0124 ∷ []) (lem-box-perm-2134-at032032 c4) ▸
       at 13 1 (Bx0-3124 ∷ []) (lem-box-perm-3241-at142142 c4) ▸
       at 12 2 (Bx0-3124 ∷ Bx3-0124 ∷ []) (lem-box-box-1-at03102132 c4) ▸
       at 12 1 (Bx0-4132 ∷ []) (lem-box-perm-4213-at132132 c4) ▸
       at 13 1 (Bx3-1024 ∷ []) (lem-box-perm-2134-at03102132 c4) ▸ done

  b24 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Bx0-4132 ∷ Bx3-1024 ∷ Bx2-0134 ∷ Bx3-1024 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ Bx0-4132 ∷ Bx2-0134 ∷ [])
  b24 = at 13 1 (Bx3-0124 ∷ []) (lem-box-perm-2134-at032032 c4) ▸
       at 14 1 (Bx2-3014 ∷ []) (lem-box-perm-3124-at021021 c4) ▸
       at 13 2 (Bx2-3014 ∷ Bx3-0124 ∷ []) (lem-box-box-3-at03102132 c4) ▸
       at 13 1 (Bx2-0134 ∷ []) (lem-box-perm-2314-at02132031 c4) ▸
       at 14 1 (Bx3-1024 ∷ []) (lem-box-perm-2134-at03102132 c4) ▸
       at 14 2 [] (lem-box2-at032032 c4) ▸
       at 10 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at142142 c4) ▸
       at 14 1 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl0698 (lit c4)) ▸ done

  b25 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ Bx0-4132 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ CCZ014 ∷ Toff023 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Bx0-4132 ∷ Bx2-0134 ∷ [])
  b25 = at 13 2 (CS34 ∷ Toff023 ∷ []) (sym (wp0725 c4)) ▸
       at 14 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 15 2 (CS34⁻ ∷ Toff023 ∷ []) (sym (wp0823 c4)) ▸
       at 16 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 17 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 13 5 (CCZ134 ∷ []) (sym (wl0698 (lit c4))) ▸
       at 12 2 (CCZ134 ∷ CCZ014 ∷ []) (wp0272 c4) ▸
       at 12 1 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl0698 (lit c4)) ▸ done

  b26 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ CCZ014 ∷ Toff023 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Bx0-4132 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ Bx0-4132 ∷ Bx0-4132 ∷ Bx2-0134 ∷ [])
  b26 = at 11 2 (CS34 ∷ Toff023 ∷ []) (sym (wp0725 c4)) ▸
       at 12 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 13 2 (CS34⁻ ∷ Toff023 ∷ []) (sym (wp0823 c4)) ▸
       at 14 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 15 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 11 5 (CCZ134 ∷ []) (sym (wl0698 (lit c4))) ▸
       at 10 2 (CCZ134 ∷ CCZ014 ∷ []) (wp0272 c4) ▸
       at 11 4 (Bx0-4132 ∷ []) (sym (lem-box-cP-at142142 c4)) ▸ done

  b27 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Bx0-4132 ∷ CCZ134 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ Bx0-4132 ∷ Bx0-4132 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ Toff023 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ Bx2-0134 ∷ [])
  b27 = at 11 2 [] (lem-box2-at142142 c4) ▸
       at 6 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at142142 c4) ▸
       at 10 1 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl0698 (lit c4)) ▸
       at 9 2 (CS34 ∷ Toff023 ∷ []) (sym (wp0725 c4)) ▸
       at 10 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 11 2 (CS34⁻ ∷ Toff023 ∷ []) (sym (wp0823 c4)) ▸
       at 12 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 13 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸ done

  b28 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ Toff023 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ014 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ Bx2-0134 ∷ [])
  b28 = at 9 5 (CCZ134 ∷ []) (sym (wl0698 (lit c4))) ▸
       at 8 2 (CCZ134 ∷ CCZ014 ∷ []) (wp0272 c4) ▸
       at 8 1 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl0698 (lit c4)) ▸
       at 7 2 (CS34 ∷ Toff023 ∷ []) (sym (wp0725 c4)) ▸
       at 8 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 9 2 (CS34⁻ ∷ Toff023 ∷ []) (sym (wp0823 c4)) ▸
       at 10 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 11 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸ done

  b29 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ014 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ CCZ014 ∷ Toff023 ∷ Toff012 ∷ CCZ124 ∷ K3 ∷ CCZ014 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3⁻ ∷ Toff023 ∷ Toff034 ∷ CCZ134 ∷ Bx2-0134 ∷ [])
  b29 = at 7 5 (CCZ134 ∷ []) (sym (wl0698 (lit c4))) ▸
       at 6 2 (CCZ134 ∷ CCZ014 ∷ []) (wp0272 c4) ▸
       at 7 4 (Bx0-4132 ∷ []) (sym (lem-box-cP-at142142 c4)) ▸
       at 7 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at142142 c4) ▸
       at 10 2 (Toff012 ∷ Toff312 ∷ Toff023 ∷ []) (sym (wl1407 (lit c4))) ▸
       at 9 2 (Toff012 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp1255 c4) ▸
       at 12 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3⁻ ∷ []) (sym (wl0514 (lit c4))) ▸
       at 11 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸ done

  b30 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ CCZ014 ∷ Toff023 ∷ Toff012 ∷ CCZ124 ∷ K3 ∷ CCZ014 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3⁻ ∷ Toff023 ∷ Toff034 ∷ CCZ134 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ CCZ014 ∷ Toff012 ∷ Toff023 ∷ CCZ124 ∷ Toff312 ∷ CCZ014 ∷ Toff023 ∷ Toff034 ∷ CCZ134 ∷ Bx2-0134 ∷ [])
  b30 = at 12 2 (CS23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CS23 (lit c4)) ▸
       at 13 2 (CX12 ∷ CCZ014 ∷ []) (wp0054 c4) ▸
       at 14 2 (CS23⁻ ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CSd23 (lit c4)) ▸
       at 15 2 (CX12 ∷ CCZ014 ∷ []) (wp0054 c4) ▸
       at 16 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 17 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 11 7 (Toff312 ∷ []) (wl0514 (lit c4)) ▸
       at 8 2 (Toff012 ∷ Toff023 ∷ []) (sym (wl0275 (lit c4))) ▸ done

  b31 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ CCZ014 ∷ Toff012 ∷ Toff023 ∷ CCZ124 ∷ Toff312 ∷ CCZ014 ∷ Toff023 ∷ Toff034 ∷ CCZ134 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ CCZ014 ∷ Toff012 ∷ CCZ124 ∷ Toff012 ∷ Toff312 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff034 ∷ CCZ134 ∷ Bx2-0134 ∷ [])
  b31 = at 10 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 9 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 10 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 11 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 12 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 13 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 9 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 10 2 (Toff012 ∷ Toff312 ∷ Toff023 ∷ []) (sym (wl1407 (lit c4))) ▸ done

  b32 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ CCZ014 ∷ Toff012 ∷ CCZ124 ∷ Toff012 ∷ Toff312 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff034 ∷ CCZ134 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ CCZ124 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CCZ014 ∷ CS13 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff034 ∷ CCZ134 ∷ Bx2-0134 ∷ [])
  b32 = at 8 3 (CCZ124 ∷ []) (sym (wp1256 c4)) ▸
       at 7 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 9 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3⁻ ∷ []) (sym (wl0514 (lit c4))) ▸
       at 8 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 9 2 (CS23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CS23 (lit c4)) ▸
       at 10 2 (CX12 ∷ CCZ014 ∷ []) (wp0054 c4) ▸
       at 11 2 (CS23⁻ ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CSd23 (lit c4)) ▸
       at 12 2 (CX12 ∷ CCZ014 ∷ []) (wp0054 c4) ▸ done

  b33 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ CCZ124 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CCZ014 ∷ CS13 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff034 ∷ CCZ134 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ CCZ124 ∷ Toff312 ∷ CCZ014 ∷ Toff034 ∷ Toff023 ∷ CCZ134 ∷ CCZ014 ∷ Toff023 ∷ CCZ134 ∷ Bx2-0134 ∷ [])
  b33 = at 13 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 14 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 8 7 (Toff312 ∷ []) (wl0514 (lit c4)) ▸
       at 9 4 (Bx0-4132 ∷ []) (sym (lem-box-cP-at142142 c4)) ▸
       at 9 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at142142 c4) ▸
       at 12 2 (Toff034 ∷ Toff023 ∷ []) (wp0173 c4) ▸
       at 11 2 (Toff034 ∷ CCZ134 ∷ CCZ014 ∷ []) (wp1209 c4) ▸
       at 10 2 (Toff034 ∷ Toff023 ∷ []) (wp0173 c4) ▸ done

  b34 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ CCZ124 ∷ Toff312 ∷ CCZ014 ∷ Toff034 ∷ Toff023 ∷ CCZ134 ∷ CCZ014 ∷ Toff023 ∷ CCZ134 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ CCZ124 ∷ Toff312 ∷ Toff034 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ134 ∷ Bx2-0134 ∷ [])
  b34 = at 12 1 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl0698 (lit c4)) ▸
       at 11 2 (CS34 ∷ Toff023 ∷ []) (sym (wp0725 c4)) ▸
       at 12 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 13 2 (CS34⁻ ∷ Toff023 ∷ []) (sym (wp0823 c4)) ▸
       at 14 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 15 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 11 5 (CCZ134 ∷ []) (sym (wl0698 (lit c4))) ▸
       at 9 3 (Toff034 ∷ CCZ014 ∷ []) (wp0268 c4) ▸ done

  b35 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ CCZ124 ∷ Toff312 ∷ Toff034 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ134 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ CCZ124 ∷ Toff312 ∷ Toff034 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ Toff023 ∷ Bx2-0134 ∷ [])
  b35 = at 10 4 (Bx0-4132 ∷ []) (sym (lem-box-cP-at142142 c4)) ▸
       at 10 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at142142 c4) ▸
       at 14 1 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl0698 (lit c4)) ▸
       at 13 2 (CS34 ∷ Toff023 ∷ []) (sym (wp0725 c4)) ▸
       at 14 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 15 2 (CS34⁻ ∷ Toff023 ∷ []) (sym (wp0823 c4)) ▸
       at 16 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 17 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸ done

  b36 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ CCZ124 ∷ Toff312 ∷ Toff034 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ Toff023 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ CCZ124 ∷ Toff312 ∷ Toff034 ∷ CCZ014 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Bx2-0134 ∷ [])
  b36 = at 13 5 (CCZ134 ∷ []) (sym (wl0698 (lit c4))) ▸
       at 12 2 (CCZ134 ∷ CCZ014 ∷ []) (wp0272 c4) ▸
       at 12 1 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl0698 (lit c4)) ▸
       at 11 2 (CS34 ∷ Toff023 ∷ []) (sym (wp0725 c4)) ▸
       at 12 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 13 2 (CS34⁻ ∷ Toff023 ∷ []) (sym (wp0823 c4)) ▸
       at 14 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 15 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸ done

  b37 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CCZ134 ∷ CCZ124 ∷ Toff312 ∷ Toff034 ∷ CCZ014 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Bx2-0134 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CK40 ∷ Bx3-1240 ∷ CK40⁻ ∷ Bx0-1234 ∷ Bx2-0134 ∷ [])
  b37 = at 11 5 (CCZ134 ∷ []) (sym (wl0698 (lit c4))) ▸
       at 10 2 (CCZ134 ∷ CCZ014 ∷ []) (wp0272 c4) ▸
       at 11 4 (Bx0-4132 ∷ []) (sym (lem-box-cP-at142142 c4)) ▸
       at 11 1 (Bx0-1234 ∷ []) (lem-box-perm-2431-at142142 c4) ▸
       at 6 2 (Toff312 ∷ CCZ134 ∷ Toff312 ∷ []) (wl1408 (lit c4)) ▸
       at 8 2 [] (wl0489 (lit c4)) ▸
       at 7 3 (Toff034 ∷ []) (wp1257 c4) ▸
       at 4 4 (CK40 ∷ Bx3-1240 ∷ CK40⁻ ∷ []) (sym (lem-CK-box-at033440 c4)) ▸ done

  b38 : Chain (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ CK40 ∷ Bx3-1240 ∷ CK40⁻ ∷ Bx0-1234 ∷ Bx2-0134 ∷ []) (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ [])
  b38 = at 0 4 (CK40 ∷ Bx3-1240 ∷ CK40⁻ ∷ []) (sym (lem-CK-box-at033440 c4)) ▸
       at 2 2 [] (wp1258 c4) ▸
       at 1 2 [] (lem-box2-at033440 c4) ▸
       at 0 2 [] (wp1217 c4) ▸
       at 0 0 [] (wl1112 (lit c4)) ▸
       at 0 2 (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) (sym (lem-nf-toff-cczat0 c4)) ▸ done
