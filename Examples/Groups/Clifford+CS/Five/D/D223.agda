{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D223 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0018 ; wl0196 ; wl0420 ; wl0442 ; wl0754 ; wl0807 ; wl0808 ; wl0852 ; wl0861 ; wl0878 ; wl0879 ; wl0942 ; wl1180 ; wl1371 ; wl1373 ; wp0013 ; wp0295 ; wp0296 ; wp0352 ; wp0737 ; wp0768 ; wp0790 ; wp0814 ; wp0998 ; wp1046 ; wp1218 ; wp1270 ; wp1271 ; wl0003 ; wl0006 ; wl0013 ; wl0017 ; wl0087 ; wl0090 ; wl0099 ; wp1272 ; wp1308)
open import Examples.Groups.Clifford+CS.Five.Chain

open import Examples.Groups.Clifford+CS.Five.TR2 using (lem-TR2-1b52048e ; lem-TR2-ff6c1f51)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-F1-order-Iat0 ; lem-F1-order-Kat2 ; lem-F1-order-Kat3 ; lem-F1-order-SKat2 ; lem-F1-order-SKat3 ; lem-F1-order-Sat2 ; lem-F1-order-Sat3 ; lem-F2-I-K0 ; lem-F2-I-K1 ; lem-F2-I-K2 ; lem-F2-I-K3 ; lem-F2-I-S0 ; lem-F2-I-S1 ; lem-F2-I-S2 ; lem-F2-I-S3 ; lem-F2-K0-K1 ; lem-F2-K0-K2 ; lem-F2-K0-K3 ; lem-F2-K1-K2 ; lem-F2-K1-K3 ; lem-F2-K2-K3 ; lem-F2-S0-K1 ; lem-F2-S0-K2 ; lem-F2-S0-K3 ; lem-F2-S0-S1 ; lem-F2-S0-S2 ; lem-F2-S0-S3 ; lem-F2-S1-K0 ; lem-F2-S1-K2 ; lem-F2-S1-K3 ; lem-F2-S1-S2 ; lem-F2-S1-S3 ; lem-F2-S2-K0 ; lem-F2-S2-K1 ; lem-F2-S2-K3 ; lem-F2-S2-S3 ; lem-F2-S3-K0 ; lem-F2-S3-K1 ; lem-F2-S3-K2)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-S-sym-xt-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.D012 using (lem-CK-box-at033440)
open import Examples.Groups.Clifford+CS.Five.D.D014 using (lem-F2-S0-CS1 ; lem-F2-S0-CS2 ; lem-F2-S2-CS0)
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-box-cP-at031031 ; lem-box-perm-1324-at03102132)
open import Examples.Groups.Clifford+CS.Five.D.D017 using (lem-box-cP-at02142041 ; lem-box-cP-at0314203241 ; lem-box2-at03102132)
open import Examples.Groups.Clifford+CS.Five.D.D019 using (lem-box-perm-2341-at03102132)
open import Examples.Groups.Clifford+CS.Five.D.D020 using (lem-F2-I-CS0 ; lem-F2-I-CS1 ; lem-F2-I-CS2 ; lem-F2-S1-CS2 ; lem-F2-S3-CS0 ; lem-F2-S3-CS1)
open import Examples.Groups.Clifford+CS.Five.D.D021 using (lem-box-perm-2431-at02142041 ; lem-box-perm-4132-at021021 ; lem-box-perm-4132-at03102132 ; lem-box2-at02142041 ; lem-box2-at0314203241)
open import Examples.Groups.Clifford+CS.Five.D.D025 using (lem-F2-K1-CS2)
open import Examples.Groups.Clifford+CS.Five.D.D026 using (lem-F1-comm-CS-S0at2 ; lem-F2-K3-CS0 ; lem-F2-K3-CS1)
open import Examples.Groups.Clifford+CS.Five.D.D027 using (lem-F1-comm-CS-S1at2)
open import Examples.Groups.Clifford+CS.Five.D.D030 using (lem-box-box-3-at021021 ; lem-box-perm-2431-at0314203241 ; lem-box-perm-3241-at02142041 ; lem-box-perm-3241-at0314203241 ; lem-box-perm-4213-at02132031 ; lem-box-perm-4213-at03122031)
open import Examples.Groups.Clifford+CS.Five.D.D032 using (lem-ckt-Dinv)
open import Examples.Groups.Clifford+CS.Five.D.D038 using (lem-F1-order-CSat2 ; lem-F2-K0-CS1 ; lem-F2-K0-CS2 ; lem-F2-K2-CS0)
open import Examples.Groups.Clifford+CS.Five.D.D043 using (lem-L-CX01-2 ; lem-L-CX10-2)
open import Examples.Groups.Clifford+CS.Five.D.D044 using (lem-Tu-box-at0314203241 ; lem-box-box-3-at03102132)
open import Examples.Groups.Clifford+CS.Five.D.D067 using (lem-F1-X-CS0at2 ; lem-F2-CS0-CS2)
open import Examples.Groups.Clifford+CS.Five.D.D068 using (lem-F1-X-CS1at2)
open import Examples.Groups.Clifford+CS.Five.D.D070 using (lem-F1-CS-K0at2 ; lem-F1-CS-K1at2 ; lem-Tu-box-at02142041)
open import Examples.Groups.Clifford+CS.Five.D.D196 using (lem-deb-Q-lo-at02132031)
open import Examples.Groups.Clifford+CS.Five.D.D197 using (lem-deb-Q-hi-at132132)
open import Examples.Groups.Clifford+CS.Five.D.D206 using (lem-deb-P-hi ; lem-deb-P-hi-at132132 ; lem-deb-P-lo-at02132031 ; lem-deb-P-lo-at132132)
open import Examples.Groups.Clifford+CS.Five.D.D207 using (lem-deb-AD-at02132031 ; lem-deb-rel-272at0-R)
open import Examples.Groups.Clifford+CS.Five.D.D214 using (lem-F1-comm-CSu-CSat0)
open import Examples.Groups.Clifford+CS.Five.D.D215 using (lem-L-CCZ-0 ; lem-deb-rel-269at0-R ; lem-deb-rel-269at1-R)
open import Examples.Groups.Clifford+CS.Five.D.D216 using (lem-ckt-A-R)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-push-CK40-sw0-L ; lem-comm-push-CS04-sw0-L ; lem-comm-push-CS04-sw1-L ; lem-comm-push-CS04-sw1-R)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-TOFF213-CX04 ; lem-comm-TOFF312-CX04 ; lem-comm-push-CK40-sw1-L)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-TOFF314-CX02 ; lem-comm-push-CK40-sw1-R ; lem-comm-push-CK41-sw0-R ; lem-comm-push-CS14-sw0-R)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R ; lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L ; lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L ; lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R ; lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R ; lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L ; lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R ; lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L)

-- nf-cx-ccz@0: 265 steps
lem-nf-cx-cczat0 : Ws → ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ Bx3-4021 ∷ []) ⟫ʷ
lem-nf-cx-cczat0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (run b33)))))))))))))))))))))))))))))))))
  where
  b0 : Chain (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) (Bx3-0124 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-0124 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ [])
  b0 = at 0 45 (Bx3-0124 ∷ []) (lem-L-CCZ-0 c4) ▸
       at 1 5 (Toff324 ∷ []) (lem-L-CX01-2 c4) ▸
       at 2 5 (Toff234 ∷ []) (lem-L-CX10-2 c4) ▸
       at 3 5 (Toff324 ∷ []) (lem-L-CX01-2 c4) ▸
       at 4 45 (Bx3-0124 ∷ []) (lem-L-CCZ-0 c4) ▸
       at 5 5 (Toff324 ∷ []) (lem-L-CX01-2 c4) ▸
       at 6 5 (Toff234 ∷ []) (lem-L-CX10-2 c4) ▸
       at 7 5 (Toff324 ∷ []) (lem-L-CX01-2 c4) ▸ done

  b1 : Chain (Bx3-0124 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-0124 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ []) (Bx3-0124 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ023 ∷ Toff324 ∷ CS24 ∷ CX02 ∷ Toff314 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ CCZ023 ∷ Toff314 ∷ Toff234 ∷ Toff324 ∷ [])
  b1 = at 4 1 (Bx3-0214 ∷ []) (lem-box-perm-1324-at03102132 c4) ▸
       at 4 1 (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-box-cP-at031031 c4) ▸
       at 7 2 (Toff324 ∷ Toff314 ∷ []) (wl1180 (lit c4)) ▸
       at 6 2 (Toff324 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp1046 c4) ▸
       at 5 2 (Toff324 ∷ Toff314 ∷ []) (wl1180 (lit c4)) ▸
       at 7 1 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (wp0296 c4) ▸
       at 6 2 (CS24 ∷ Toff314 ∷ []) (sym (wl0754 (lit c4))) ▸
       at 7 2 (CX02 ∷ Toff314 ∷ []) (lem-comm-TOFF314-CX02 (lit c4)) ▸ done

  b2 : Chain (Bx3-0124 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ023 ∷ Toff324 ∷ CS24 ∷ CX02 ∷ Toff314 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ CCZ023 ∷ Toff314 ∷ Toff234 ∷ Toff324 ∷ []) (Bx3-0124 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff234 ∷ Bx3-0124 ∷ Toff234 ∷ Toff324 ∷ [])
  b2 = at 8 2 (CS24⁻ ∷ Toff314 ∷ []) (sym (wl1371 (lit c4))) ▸
       at 9 2 (CX02 ∷ Toff314 ∷ []) (lem-comm-TOFF314-CX02 (lit c4)) ▸
       at 10 2 (CS04 ∷ Toff314 ∷ []) (sym (wp0998 c4)) ▸
       at 6 5 (CCZ024 ∷ []) (sym (wp0296 c4)) ▸
       at 4 3 (Toff324 ∷ CCZ023 ∷ []) (wp0814 c4) ▸
       at 5 4 (Bx3-0214 ∷ []) (sym (lem-box-cP-at031031 c4)) ▸
       at 5 1 (Bx3-0124 ∷ []) (sym (lem-box-perm-1324-at03102132 c4)) ▸
       at 5 0 (Toff234 ∷ Toff234 ∷ []) (sym (wl0420 (lit c4))) ▸ done

  b3 : Chain (Bx3-0124 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff234 ∷ Bx3-0124 ∷ Toff234 ∷ Toff324 ∷ []) (Bx3-0124 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ Toff324 ∷ [])
  b3 = at 7 1 (Bx3-4021 ∷ []) (lem-box-perm-4132-at03102132 c4) ▸
       at 6 3 (Bx3-4021 ∷ Bx2-4031 ∷ []) (lem-Tu-box-at0314203241 c4) ▸
       at 6 1 (Bx3-0124 ∷ []) (lem-box-perm-2431-at0314203241 c4) ▸
       at 7 1 (Bx2-3014 ∷ []) (lem-box-perm-3241-at02142041 c4) ▸
       at 6 2 (Bx2-3014 ∷ Bx3-0124 ∷ []) (lem-box-box-3-at03102132 c4) ▸
       at 6 1 (Bx2-4031 ∷ []) (lem-box-perm-4213-at02132031 c4) ▸
       at 7 1 (Bx3-0214 ∷ []) (lem-box-perm-1324-at03102132 c4) ▸
       at 7 1 (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-box-cP-at031031 c4) ▸ done

  b4 : Chain (Bx3-0124 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ Toff324 ∷ []) (Bx3-0124 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ023 ∷ Toff324 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Toff314 ∷ CS04 ∷ CCZ023 ∷ Toff314 ∷ [])
  b4 = at 10 2 (Toff324 ∷ Toff314 ∷ []) (wl1180 (lit c4)) ▸
       at 9 2 (Toff324 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp1046 c4) ▸
       at 8 2 (Toff324 ∷ Toff314 ∷ []) (wl1180 (lit c4)) ▸
       at 10 1 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (wp0296 c4) ▸
       at 9 2 (CS24 ∷ Toff314 ∷ []) (sym (wl0754 (lit c4))) ▸
       at 10 2 (CX02 ∷ Toff314 ∷ []) (lem-comm-TOFF314-CX02 (lit c4)) ▸
       at 11 2 (CS24⁻ ∷ Toff314 ∷ []) (sym (wl1371 (lit c4))) ▸
       at 12 2 (CX02 ∷ Toff314 ∷ []) (lem-comm-TOFF314-CX02 (lit c4)) ▸ done

  b5 : Chain (Bx3-0124 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ023 ∷ Toff324 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Toff314 ∷ CS04 ∷ CCZ023 ∷ Toff314 ∷ []) (Bx3-0124 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-0134 ∷ Bx3-4021 ∷ Bx3-0124 ∷ [])
  b5 = at 13 2 (CS04 ∷ Toff314 ∷ []) (sym (wp0998 c4)) ▸
       at 9 5 (CCZ024 ∷ []) (sym (wp0296 c4)) ▸
       at 7 3 (Toff324 ∷ CCZ023 ∷ []) (wp0814 c4) ▸
       at 8 4 (Bx3-0214 ∷ []) (sym (lem-box-cP-at031031 c4)) ▸
       at 8 1 (Bx3-0124 ∷ []) (sym (lem-box-perm-1324-at03102132 c4)) ▸
       at 6 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0442 (lit c4))) ▸
       at 7 3 (Bx2-4031 ∷ Bx3-4021 ∷ []) (lem-Tu-box-at02142041 c4) ▸
       at 7 1 (Bx2-0134 ∷ []) (lem-box-perm-2431-at02142041 c4) ▸ done

  b6 : Chain (Bx3-0124 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-0134 ∷ Bx3-4021 ∷ Bx3-0124 ∷ []) (Bx3-0124 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ Bx3-0124 ∷ Bx3-0124 ∷ [])
  b6 = at 8 1 (Bx3-2014 ∷ []) (lem-box-perm-3241-at0314203241 c4) ▸
       at 7 2 (Bx3-2014 ∷ Bx2-0134 ∷ []) (lem-box-box-3-at021021 c4) ▸
       at 7 1 (Bx3-4021 ∷ []) (lem-box-perm-4213-at03122031 c4) ▸
       at 8 1 (Bx2-4031 ∷ []) (lem-box-perm-4132-at021021 c4) ▸
       at 7 1 (Bx3-0124 ∷ []) (lem-box-perm-2431-at0314203241 c4) ▸
       at 8 1 (Bx2-3014 ∷ []) (lem-box-perm-3241-at02142041 c4) ▸
       at 7 2 (Bx2-3014 ∷ Bx3-0124 ∷ []) (lem-box-box-3-at03102132 c4) ▸
       at 7 1 (Bx2-4031 ∷ []) (lem-box-perm-4213-at02132031 c4) ▸ done

  b7 : Chain (Bx3-0124 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ Bx3-0124 ∷ Bx3-0124 ∷ []) (CCZ023 ∷ Toff324 ∷ Toff314 ∷ CCZ024 ∷ CCZ023 ∷ Toff314 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ [])
  b7 = at 8 1 (Bx3-4021 ∷ []) (lem-box-perm-4132-at03102132 c4) ▸
       at 8 1 (Bx3-0124 ∷ []) (lem-box-perm-2431-at0314203241 c4) ▸
       at 8 2 [] (lem-box2-at03102132 c4) ▸
       at 0 1 (Bx3-0214 ∷ []) (lem-box-perm-1324-at03102132 c4) ▸
       at 0 1 (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-box-cP-at031031 c4) ▸
       at 3 2 (Toff324 ∷ Toff314 ∷ []) (wl1180 (lit c4)) ▸
       at 2 2 (Toff324 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp1046 c4) ▸
       at 1 2 (Toff324 ∷ Toff314 ∷ []) (wl1180 (lit c4)) ▸ done

  b8 : Chain (CCZ023 ∷ Toff324 ∷ Toff314 ∷ CCZ024 ∷ CCZ023 ∷ Toff314 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ []) (Toff324 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ [])
  b8 = at 3 1 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (wp0296 c4) ▸
       at 2 2 (CS24 ∷ Toff314 ∷ []) (sym (wl0754 (lit c4))) ▸
       at 3 2 (CX02 ∷ Toff314 ∷ []) (lem-comm-TOFF314-CX02 (lit c4)) ▸
       at 4 2 (CS24⁻ ∷ Toff314 ∷ []) (sym (wl1371 (lit c4))) ▸
       at 5 2 (CX02 ∷ Toff314 ∷ []) (lem-comm-TOFF314-CX02 (lit c4)) ▸
       at 6 2 (CS04 ∷ Toff314 ∷ []) (sym (wp0998 c4)) ▸
       at 2 5 (CCZ024 ∷ []) (sym (wp0296 c4)) ▸
       at 0 3 (Toff324 ∷ CCZ023 ∷ []) (wp0814 c4) ▸ done

  b9 : Chain (Toff324 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ []) (Toff324 ∷ Toff234 ∷ Bx2-3014 ∷ Bx3-0124 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ [])
  b9 = at 1 4 (Bx3-0214 ∷ []) (sym (lem-box-cP-at031031 c4)) ▸
       at 1 1 (Bx3-0124 ∷ []) (sym (lem-box-perm-1324-at03102132 c4)) ▸
       at 1 0 (Toff234 ∷ Toff234 ∷ []) (sym (wl0420 (lit c4))) ▸
       at 3 1 (Bx3-4021 ∷ []) (lem-box-perm-4132-at03102132 c4) ▸
       at 2 3 (Bx3-4021 ∷ Bx2-4031 ∷ []) (lem-Tu-box-at0314203241 c4) ▸
       at 2 1 (Bx3-0124 ∷ []) (lem-box-perm-2431-at0314203241 c4) ▸
       at 3 1 (Bx2-3014 ∷ []) (lem-box-perm-3241-at02142041 c4) ▸
       at 2 2 (Bx2-3014 ∷ Bx3-0124 ∷ []) (lem-box-box-3-at03102132 c4) ▸ done

  b10 : Chain (Toff324 ∷ Toff234 ∷ Bx2-3014 ∷ Bx3-0124 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ []) (Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ023 ∷ Toff324 ∷ CS24 ∷ Toff314 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ CCZ023 ∷ Toff314 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ [])
  b10 = at 2 1 (Bx2-4031 ∷ []) (lem-box-perm-4213-at02132031 c4) ▸
       at 3 1 (Bx3-0214 ∷ []) (lem-box-perm-1324-at03102132 c4) ▸
       at 3 1 (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-box-cP-at031031 c4) ▸
       at 6 2 (Toff324 ∷ Toff314 ∷ []) (wl1180 (lit c4)) ▸
       at 5 2 (Toff324 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp1046 c4) ▸
       at 4 2 (Toff324 ∷ Toff314 ∷ []) (wl1180 (lit c4)) ▸
       at 6 1 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (wp0296 c4) ▸
       at 5 2 (CS24 ∷ Toff314 ∷ []) (sym (wl0754 (lit c4))) ▸ done

  b11 : Chain (Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ023 ∷ Toff324 ∷ CS24 ∷ Toff314 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ CCZ023 ∷ Toff314 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ []) (Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Toff324 ∷ Bx3-0124 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ [])
  b11 = at 6 2 (CX02 ∷ Toff314 ∷ []) (lem-comm-TOFF314-CX02 (lit c4)) ▸
       at 7 2 (CS24⁻ ∷ Toff314 ∷ []) (sym (wl1371 (lit c4))) ▸
       at 8 2 (CX02 ∷ Toff314 ∷ []) (lem-comm-TOFF314-CX02 (lit c4)) ▸
       at 9 2 (CS04 ∷ Toff314 ∷ []) (sym (wp0998 c4)) ▸
       at 5 5 (CCZ024 ∷ []) (sym (wp0296 c4)) ▸
       at 3 3 (Toff324 ∷ CCZ023 ∷ []) (wp0814 c4) ▸
       at 4 4 (Bx3-0214 ∷ []) (sym (lem-box-cP-at031031 c4)) ▸
       at 4 1 (Bx3-0124 ∷ []) (sym (lem-box-perm-1324-at03102132 c4)) ▸ done

  b12 : Chain (Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Toff324 ∷ Bx3-0124 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ []) (Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Toff324 ∷ CCZ023 ∷ Toff324 ∷ CS24 ∷ CX02 ∷ Toff314 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ CCZ023 ∷ Toff314 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ [])
  b12 = at 4 1 (Bx3-0214 ∷ []) (lem-box-perm-1324-at03102132 c4) ▸
       at 4 1 (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-box-cP-at031031 c4) ▸
       at 7 2 (Toff324 ∷ Toff314 ∷ []) (wl1180 (lit c4)) ▸
       at 6 2 (Toff324 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp1046 c4) ▸
       at 5 2 (Toff324 ∷ Toff314 ∷ []) (wl1180 (lit c4)) ▸
       at 7 1 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (wp0296 c4) ▸
       at 6 2 (CS24 ∷ Toff314 ∷ []) (sym (wl0754 (lit c4))) ▸
       at 7 2 (CX02 ∷ Toff314 ∷ []) (lem-comm-TOFF314-CX02 (lit c4)) ▸ done

  b13 : Chain (Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Toff324 ∷ CCZ023 ∷ Toff324 ∷ CS24 ∷ CX02 ∷ Toff314 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ CCZ023 ∷ Toff314 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ []) (Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff234 ∷ Bx3-0124 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ [])
  b13 = at 8 2 (CS24⁻ ∷ Toff314 ∷ []) (sym (wl1371 (lit c4))) ▸
       at 9 2 (CX02 ∷ Toff314 ∷ []) (lem-comm-TOFF314-CX02 (lit c4)) ▸
       at 10 2 (CS04 ∷ Toff314 ∷ []) (sym (wp0998 c4)) ▸
       at 6 5 (CCZ024 ∷ []) (sym (wp0296 c4)) ▸
       at 4 3 (Toff324 ∷ CCZ023 ∷ []) (wp0814 c4) ▸
       at 5 4 (Bx3-0214 ∷ []) (sym (lem-box-cP-at031031 c4)) ▸
       at 5 1 (Bx3-0124 ∷ []) (sym (lem-box-perm-1324-at03102132 c4)) ▸
       at 5 0 (Toff234 ∷ Toff234 ∷ []) (sym (wl0420 (lit c4))) ▸ done

  b14 : Chain (Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff234 ∷ Bx3-0124 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ []) (Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ Toff324 ∷ Bx2-4031 ∷ [])
  b14 = at 7 1 (Bx3-4021 ∷ []) (lem-box-perm-4132-at03102132 c4) ▸
       at 6 3 (Bx3-4021 ∷ Bx2-4031 ∷ []) (lem-Tu-box-at0314203241 c4) ▸
       at 6 1 (Bx3-0124 ∷ []) (lem-box-perm-2431-at0314203241 c4) ▸
       at 7 1 (Bx2-3014 ∷ []) (lem-box-perm-3241-at02142041 c4) ▸
       at 6 2 (Bx2-3014 ∷ Bx3-0124 ∷ []) (lem-box-box-3-at03102132 c4) ▸
       at 6 1 (Bx2-4031 ∷ []) (lem-box-perm-4213-at02132031 c4) ▸
       at 7 1 (Bx3-0214 ∷ []) (lem-box-perm-1324-at03102132 c4) ▸
       at 7 1 (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-box-cP-at031031 c4) ▸ done

  b15 : Chain (Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ Toff324 ∷ Bx2-4031 ∷ []) (Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ023 ∷ Toff324 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Toff314 ∷ CS04 ∷ CCZ023 ∷ Toff314 ∷ Bx2-4031 ∷ [])
  b15 = at 10 2 (Toff324 ∷ Toff314 ∷ []) (wl1180 (lit c4)) ▸
       at 9 2 (Toff324 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp1046 c4) ▸
       at 8 2 (Toff324 ∷ Toff314 ∷ []) (wl1180 (lit c4)) ▸
       at 10 1 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (wp0296 c4) ▸
       at 9 2 (CS24 ∷ Toff314 ∷ []) (sym (wl0754 (lit c4))) ▸
       at 10 2 (CX02 ∷ Toff314 ∷ []) (lem-comm-TOFF314-CX02 (lit c4)) ▸
       at 11 2 (CS24⁻ ∷ Toff314 ∷ []) (sym (wl1371 (lit c4))) ▸
       at 12 2 (CX02 ∷ Toff314 ∷ []) (lem-comm-TOFF314-CX02 (lit c4)) ▸ done

  b16 : Chain (Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ023 ∷ Toff324 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Toff314 ∷ CS04 ∷ CCZ023 ∷ Toff314 ∷ Bx2-4031 ∷ []) (Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Toff324 ∷ Bx2-4031 ∷ Bx3-0124 ∷ [])
  b16 = at 13 2 (CS04 ∷ Toff314 ∷ []) (sym (wp0998 c4)) ▸
       at 9 5 (CCZ024 ∷ []) (sym (wp0296 c4)) ▸
       at 7 3 (Toff324 ∷ CCZ023 ∷ []) (wp0814 c4) ▸
       at 8 4 (Bx3-0214 ∷ []) (sym (lem-box-cP-at031031 c4)) ▸
       at 8 1 (Bx3-0124 ∷ []) (sym (lem-box-perm-1324-at03102132 c4)) ▸
       at 9 1 (Bx2-3014 ∷ []) (lem-box-perm-3241-at02142041 c4) ▸
       at 8 2 (Bx2-3014 ∷ Bx3-0124 ∷ []) (lem-box-box-3-at03102132 c4) ▸
       at 8 1 (Bx2-4031 ∷ []) (lem-box-perm-4213-at02132031 c4) ▸ done

  b17 : Chain (Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Toff324 ∷ Bx2-4031 ∷ Bx3-0124 ∷ []) (Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Bx3-0124 ∷ [])
  b17 = at 6 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0442 (lit c4))) ▸
       at 7 3 (Bx2-4031 ∷ Bx3-4021 ∷ []) (lem-Tu-box-at02142041 c4) ▸
       at 7 1 (Bx2-0134 ∷ []) (lem-box-perm-2431-at02142041 c4) ▸
       at 8 1 (Bx3-2014 ∷ []) (lem-box-perm-3241-at0314203241 c4) ▸
       at 7 2 (Bx3-2014 ∷ Bx2-0134 ∷ []) (lem-box-box-3-at021021 c4) ▸
       at 7 1 (Bx3-4021 ∷ []) (lem-box-perm-4213-at03122031 c4) ▸
       at 8 1 (Bx2-4031 ∷ []) (lem-box-perm-4132-at021021 c4) ▸
       at 8 2 [] (lem-box2-at02142041 c4) ▸ done

  b18 : Chain (Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Bx3-0124 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Bx2-0134 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ [])
  b18 = at 7 1 (Bx3-0124 ∷ []) (lem-box-perm-2431-at0314203241 c4) ▸
       at 7 2 [] (lem-box2-at03102132 c4) ▸
       at 2 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0442 (lit c4))) ▸
       at 3 3 (Bx2-4031 ∷ Bx3-4021 ∷ []) (lem-Tu-box-at02142041 c4) ▸
       at 3 1 (Bx2-0134 ∷ []) (lem-box-perm-2431-at02142041 c4) ▸
       at 4 1 (Bx3-2014 ∷ []) (lem-box-perm-3241-at0314203241 c4) ▸
       at 3 2 (Bx3-2014 ∷ Bx2-0134 ∷ []) (lem-box-box-3-at021021 c4) ▸
       at 3 1 (Bx3-4021 ∷ []) (lem-box-perm-4213-at03122031 c4) ▸ done

  b19 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Bx2-0134 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Toff324 ∷ Bx3-4021 ∷ Bx2-4031 ∷ Toff234 ∷ Toff324 ∷ [])
  b19 = at 4 1 (Bx2-4031 ∷ []) (lem-box-perm-4132-at021021 c4) ▸
       at 4 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0442 (lit c4))) ▸
       at 5 3 (Bx2-4031 ∷ Bx3-4021 ∷ []) (lem-Tu-box-at02142041 c4) ▸
       at 5 1 (Bx2-0134 ∷ []) (lem-box-perm-2431-at02142041 c4) ▸
       at 6 1 (Bx3-2014 ∷ []) (lem-box-perm-3241-at0314203241 c4) ▸
       at 5 2 (Bx3-2014 ∷ Bx2-0134 ∷ []) (lem-box-box-3-at021021 c4) ▸
       at 5 1 (Bx3-4021 ∷ []) (lem-box-perm-4213-at03122031 c4) ▸
       at 6 1 (Bx2-4031 ∷ []) (lem-box-perm-4132-at021021 c4) ▸ done

  b20 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Toff324 ∷ Bx3-4021 ∷ Bx2-4031 ∷ Toff234 ∷ Toff324 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Toff324 ∷ Bx3-4021 ∷ CCZ024 ∷ Toff234 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ Toff213 ∷ CX04 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff324 ∷ [])
  b20 = at 6 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at02142041 c4) ▸
       at 9 2 (Toff234 ∷ Toff213 ∷ []) (wl0942 (lit c4)) ▸
       at 8 2 (Toff234 ∷ CCZ034 ∷ CCZ024 ∷ []) (wp0790 c4) ▸
       at 7 2 (Toff234 ∷ Toff213 ∷ []) (wl0942 (lit c4)) ▸
       at 9 1 (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (wp0352 c4) ▸
       at 8 2 (CS34 ∷ Toff213 ∷ []) (sym (wl0808 (lit c4))) ▸
       at 9 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 10 2 (CS34⁻ ∷ Toff213 ∷ []) (sym (wl0807 (lit c4))) ▸ done

  b21 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Toff324 ∷ Bx3-4021 ∷ CCZ024 ∷ Toff234 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ Toff213 ∷ CX04 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff324 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Toff324 ∷ Bx3-4021 ∷ Toff234 ∷ Toff324 ∷ Bx2-0134 ∷ Bx3-4021 ∷ [])
  b21 = at 11 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 12 2 (CS03 ∷ Toff213 ∷ []) (sym (wl0196 (lit c4))) ▸
       at 8 5 (CCZ034 ∷ []) (sym (wp0352 c4)) ▸
       at 6 3 (Toff234 ∷ CCZ024 ∷ []) (wp0768 c4) ▸
       at 7 4 (Bx2-4031 ∷ []) (sym (lem-box-cP-at02142041 c4)) ▸
       at 7 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0442 (lit c4))) ▸
       at 8 3 (Bx2-4031 ∷ Bx3-4021 ∷ []) (lem-Tu-box-at02142041 c4) ▸
       at 8 1 (Bx2-0134 ∷ []) (lem-box-perm-2431-at02142041 c4) ▸ done

  b22 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Toff324 ∷ Bx3-4021 ∷ Toff234 ∷ Toff324 ∷ Bx2-0134 ∷ Bx3-4021 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Toff324 ∷ Bx3-4021 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ Bx3-0124 ∷ [])
  b22 = at 9 1 (Bx3-2014 ∷ []) (lem-box-perm-3241-at0314203241 c4) ▸
       at 8 2 (Bx3-2014 ∷ Bx2-0134 ∷ []) (lem-box-box-3-at021021 c4) ▸
       at 8 1 (Bx3-4021 ∷ []) (lem-box-perm-4213-at03122031 c4) ▸
       at 9 1 (Bx2-4031 ∷ []) (lem-box-perm-4132-at021021 c4) ▸
       at 8 1 (Bx3-0124 ∷ []) (lem-box-perm-2431-at0314203241 c4) ▸
       at 9 1 (Bx2-3014 ∷ []) (lem-box-perm-3241-at02142041 c4) ▸
       at 8 2 (Bx2-3014 ∷ Bx3-0124 ∷ []) (lem-box-box-3-at03102132 c4) ▸
       at 8 1 (Bx2-4031 ∷ []) (lem-box-perm-4213-at02132031 c4) ▸ done

  b23 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Toff324 ∷ Bx3-4021 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ Bx3-0124 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Bx3-4021 ∷ Toff324 ∷ Bx2-4031 ∷ Bx3-4021 ∷ [])
  b23 = at 9 1 (Bx3-4021 ∷ []) (lem-box-perm-4132-at03102132 c4) ▸
       at 5 0 (Toff234 ∷ Toff234 ∷ []) (sym (wl0420 (lit c4))) ▸
       at 6 3 (Bx3-4021 ∷ Bx2-4031 ∷ []) (lem-Tu-box-at0314203241 c4) ▸
       at 6 1 (Bx3-0124 ∷ []) (lem-box-perm-2431-at0314203241 c4) ▸
       at 7 1 (Bx2-3014 ∷ []) (lem-box-perm-3241-at02142041 c4) ▸
       at 6 2 (Bx2-3014 ∷ Bx3-0124 ∷ []) (lem-box-box-3-at03102132 c4) ▸
       at 6 1 (Bx2-4031 ∷ []) (lem-box-perm-4213-at02132031 c4) ▸
       at 7 1 (Bx3-4021 ∷ []) (lem-box-perm-4132-at03102132 c4) ▸ done

  b24 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Bx3-4021 ∷ Toff324 ∷ Bx2-4031 ∷ Bx3-4021 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ034 ∷ Toff324 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ Toff312 ∷ CX04 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ Bx2-4031 ∷ Bx3-4021 ∷ [])
  b24 = at 7 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203241 c4) ▸
       at 10 2 (Toff324 ∷ Toff312 ∷ []) (wl0852 (lit c4)) ▸
       at 9 2 (Toff324 ∷ CCZ024 ∷ CCZ034 ∷ []) (wp0295 c4) ▸
       at 8 2 (Toff324 ∷ Toff312 ∷ []) (wl0852 (lit c4)) ▸
       at 10 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0013 c4) ▸
       at 9 2 (CS24 ∷ Toff312 ∷ []) (sym (wl0879 (lit c4))) ▸
       at 10 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 11 2 (CS24⁻ ∷ Toff312 ∷ []) (sym (wl0878 (lit c4))) ▸ done

  b25 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ034 ∷ Toff324 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ Toff312 ∷ CX04 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ Bx2-4031 ∷ Bx3-4021 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Toff324 ∷ Bx2-3014 ∷ Bx3-0124 ∷ Bx3-4021 ∷ [])
  b25 = at 12 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 13 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 9 5 (CCZ024 ∷ []) (sym (wp0013 c4)) ▸
       at 7 3 (Toff324 ∷ CCZ034 ∷ []) (wp0737 c4) ▸
       at 8 4 (Bx3-4021 ∷ []) (sym (lem-box-cP-at0314203241 c4)) ▸
       at 8 1 (Bx3-0124 ∷ []) (lem-box-perm-2431-at0314203241 c4) ▸
       at 9 1 (Bx2-3014 ∷ []) (lem-box-perm-3241-at02142041 c4) ▸
       at 8 2 (Bx2-3014 ∷ Bx3-0124 ∷ []) (lem-box-box-3-at03102132 c4) ▸ done

  b26 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Toff324 ∷ Bx2-3014 ∷ Bx3-0124 ∷ Bx3-4021 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-2014 ∷ Bx2-0134 ∷ Bx2-4031 ∷ [])
  b26 = at 8 1 (Bx2-4031 ∷ []) (lem-box-perm-4213-at02132031 c4) ▸
       at 9 1 (Bx3-4021 ∷ []) (lem-box-perm-4132-at03102132 c4) ▸
       at 9 2 [] (lem-box2-at0314203241 c4) ▸
       at 6 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0442 (lit c4))) ▸
       at 7 3 (Bx2-4031 ∷ Bx3-4021 ∷ []) (lem-Tu-box-at02142041 c4) ▸
       at 7 1 (Bx2-0134 ∷ []) (lem-box-perm-2431-at02142041 c4) ▸
       at 8 1 (Bx3-2014 ∷ []) (lem-box-perm-3241-at0314203241 c4) ▸
       at 7 2 (Bx3-2014 ∷ Bx2-0134 ∷ []) (lem-box-box-3-at021021 c4) ▸ done

  b27 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-2014 ∷ Bx2-0134 ∷ Bx2-4031 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ034 ∷ Toff324 ∷ Toff312 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ [])
  b27 = at 7 1 (Bx3-4021 ∷ []) (lem-box-perm-4213-at03122031 c4) ▸
       at 8 1 (Bx2-4031 ∷ []) (lem-box-perm-4132-at021021 c4) ▸
       at 8 2 [] (lem-box2-at02142041 c4) ▸
       at 3 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203241 c4) ▸
       at 6 2 (Toff324 ∷ Toff312 ∷ []) (wl0852 (lit c4)) ▸
       at 5 2 (Toff324 ∷ CCZ024 ∷ CCZ034 ∷ []) (wp0295 c4) ▸
       at 4 2 (Toff324 ∷ Toff312 ∷ []) (wl0852 (lit c4)) ▸
       at 6 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0013 c4) ▸ done

  b28 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ034 ∷ Toff324 ∷ Toff312 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Bx3-4021 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ [])
  b28 = at 5 2 (CS24 ∷ Toff312 ∷ []) (sym (wl0879 (lit c4))) ▸
       at 6 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 7 2 (CS24⁻ ∷ Toff312 ∷ []) (sym (wl0878 (lit c4))) ▸
       at 8 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 9 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 5 5 (CCZ024 ∷ []) (sym (wp0013 c4)) ▸
       at 3 3 (Toff324 ∷ CCZ034 ∷ []) (wp0737 c4) ▸
       at 4 4 (Bx3-4021 ∷ []) (sym (lem-box-cP-at0314203241 c4)) ▸ done

  b29 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Bx3-4021 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff324 ∷ Bx3-4021 ∷ [])
  b29 = at 4 0 (Toff234 ∷ Toff234 ∷ []) (sym (wl0420 (lit c4))) ▸
       at 5 3 (Bx3-4021 ∷ Bx2-4031 ∷ []) (lem-Tu-box-at0314203241 c4) ▸
       at 5 1 (Bx3-0124 ∷ []) (lem-box-perm-2431-at0314203241 c4) ▸
       at 6 1 (Bx2-3014 ∷ []) (lem-box-perm-3241-at02142041 c4) ▸
       at 5 2 (Bx2-3014 ∷ Bx3-0124 ∷ []) (lem-box-box-3-at03102132 c4) ▸
       at 5 1 (Bx2-4031 ∷ []) (lem-box-perm-4213-at02132031 c4) ▸
       at 6 1 (Bx3-4021 ∷ []) (lem-box-perm-4132-at03102132 c4) ▸
       at 6 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203241 c4) ▸ done

  b30 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff324 ∷ Bx3-4021 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ034 ∷ Toff324 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ Toff312 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ Bx3-4021 ∷ [])
  b30 = at 9 2 (Toff324 ∷ Toff312 ∷ []) (wl0852 (lit c4)) ▸
       at 8 2 (Toff324 ∷ CCZ024 ∷ CCZ034 ∷ []) (wp0295 c4) ▸
       at 7 2 (Toff324 ∷ Toff312 ∷ []) (wl0852 (lit c4)) ▸
       at 9 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0013 c4) ▸
       at 8 2 (CS24 ∷ Toff312 ∷ []) (sym (wl0879 (lit c4))) ▸
       at 9 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 10 2 (CS24⁻ ∷ Toff312 ∷ []) (sym (wl0878 (lit c4))) ▸
       at 11 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸ done

  b31 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ034 ∷ Toff324 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ Toff312 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ Bx3-4021 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-0134 ∷ Bx3-4021 ∷ [])
  b31 = at 12 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 8 5 (CCZ024 ∷ []) (sym (wp0013 c4)) ▸
       at 6 3 (Toff324 ∷ CCZ034 ∷ []) (wp0737 c4) ▸
       at 7 4 (Bx3-4021 ∷ []) (sym (lem-box-cP-at0314203241 c4)) ▸
       at 7 2 [] (lem-box2-at0314203241 c4) ▸
       at 5 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0442 (lit c4))) ▸
       at 6 3 (Bx2-4031 ∷ Bx3-4021 ∷ []) (lem-Tu-box-at02142041 c4) ▸
       at 6 1 (Bx2-0134 ∷ []) (lem-box-perm-2431-at02142041 c4) ▸ done

  b32 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-0134 ∷ Bx3-4021 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ Bx3-0124 ∷ [])
  b32 = at 7 1 (Bx3-2014 ∷ []) (lem-box-perm-3241-at0314203241 c4) ▸
       at 6 2 (Bx3-2014 ∷ Bx2-0134 ∷ []) (lem-box-box-3-at021021 c4) ▸
       at 6 1 (Bx3-4021 ∷ []) (lem-box-perm-4213-at03122031 c4) ▸
       at 7 1 (Bx2-4031 ∷ []) (lem-box-perm-4132-at021021 c4) ▸
       at 6 1 (Bx3-0124 ∷ []) (lem-box-perm-2431-at0314203241 c4) ▸
       at 7 1 (Bx2-3014 ∷ []) (lem-box-perm-3241-at02142041 c4) ▸
       at 6 2 (Bx2-3014 ∷ Bx3-0124 ∷ []) (lem-box-box-3-at03102132 c4) ▸
       at 6 1 (Bx2-4031 ∷ []) (lem-box-perm-4213-at02132031 c4) ▸ done

  b33 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ Bx3-0124 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ Bx3-4021 ∷ [])
  b33 = at 7 1 (Bx3-4021 ∷ []) (lem-box-perm-4132-at03102132 c4) ▸ done

-- L-CCZ013-0: 60 steps
lem-L-CCZ013-0 : Ws → ⟪ (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-L-CCZ013-0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-0214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ [])
  b0 = at 0 5 (Toff324 ∷ []) (lem-L-CX01-2 c4) ▸
       at 1 5 (Toff234 ∷ []) (lem-L-CX10-2 c4) ▸
       at 2 5 (Toff324 ∷ []) (lem-L-CX01-2 c4) ▸
       at 3 45 (Bx3-0124 ∷ []) (lem-L-CCZ-0 c4) ▸
       at 4 5 (Toff324 ∷ []) (lem-L-CX01-2 c4) ▸
       at 5 5 (Toff234 ∷ []) (lem-L-CX10-2 c4) ▸
       at 6 5 (Toff324 ∷ []) (lem-L-CX01-2 c4) ▸
       at 3 1 (Bx3-0214 ∷ []) (lem-box-perm-1324-at03102132 c4) ▸ done

  b1 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-0214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ023 ∷ Toff324 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ Toff314 ∷ CX02 ∷ CS04 ∷ CCZ023 ∷ Toff314 ∷ Toff234 ∷ Toff324 ∷ [])
  b1 = at 3 1 (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-box-cP-at031031 c4) ▸
       at 6 2 (Toff324 ∷ Toff314 ∷ []) (wl1180 (lit c4)) ▸
       at 5 2 (Toff324 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp1046 c4) ▸
       at 4 2 (Toff324 ∷ Toff314 ∷ []) (wl1180 (lit c4)) ▸
       at 6 1 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (wp0296 c4) ▸
       at 5 2 (CS24 ∷ Toff314 ∷ []) (sym (wl0754 (lit c4))) ▸
       at 6 2 (CX02 ∷ Toff314 ∷ []) (lem-comm-TOFF314-CX02 (lit c4)) ▸
       at 7 2 (CS24⁻ ∷ Toff314 ∷ []) (sym (wl1371 (lit c4))) ▸ done

  b2 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ023 ∷ Toff324 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ Toff314 ∷ CX02 ∷ CS04 ∷ CCZ023 ∷ Toff314 ∷ Toff234 ∷ Toff324 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff234 ∷ Bx3-4021 ∷ Toff234 ∷ Toff324 ∷ [])
  b2 = at 8 2 (CX02 ∷ Toff314 ∷ []) (lem-comm-TOFF314-CX02 (lit c4)) ▸
       at 9 2 (CS04 ∷ Toff314 ∷ []) (sym (wp0998 c4)) ▸
       at 5 5 (CCZ024 ∷ []) (sym (wp0296 c4)) ▸
       at 3 3 (Toff324 ∷ CCZ023 ∷ []) (wp0814 c4) ▸
       at 4 4 (Bx3-0214 ∷ []) (sym (lem-box-cP-at031031 c4)) ▸
       at 4 1 (Bx3-0124 ∷ []) (sym (lem-box-perm-1324-at03102132 c4)) ▸
       at 4 0 (Toff234 ∷ Toff234 ∷ []) (sym (wl0420 (lit c4))) ▸
       at 6 1 (Bx3-4021 ∷ []) (lem-box-perm-4132-at03102132 c4) ▸ done

  b3 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff234 ∷ Bx3-4021 ∷ Toff234 ∷ Toff324 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff324 ∷ Toff314 ∷ [])
  b3 = at 5 3 (Bx3-4021 ∷ Bx2-4031 ∷ []) (lem-Tu-box-at0314203241 c4) ▸
       at 5 1 (Bx3-0124 ∷ []) (lem-box-perm-2431-at0314203241 c4) ▸
       at 6 1 (Bx2-3014 ∷ []) (lem-box-perm-3241-at02142041 c4) ▸
       at 5 2 (Bx2-3014 ∷ Bx3-0124 ∷ []) (lem-box-box-3-at03102132 c4) ▸
       at 5 1 (Bx2-4031 ∷ []) (lem-box-perm-4213-at02132031 c4) ▸
       at 6 1 (Bx3-0214 ∷ []) (lem-box-perm-1324-at03102132 c4) ▸
       at 6 1 (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-box-cP-at031031 c4) ▸
       at 9 2 (Toff324 ∷ Toff314 ∷ []) (wl1180 (lit c4)) ▸ done

  b4 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff324 ∷ Toff314 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ023 ∷ Toff324 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ [])
  b4 = at 8 2 (Toff324 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp1046 c4) ▸
       at 7 2 (Toff324 ∷ Toff314 ∷ []) (wl1180 (lit c4)) ▸
       at 9 1 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (wp0296 c4) ▸
       at 8 2 (CS24 ∷ Toff314 ∷ []) (sym (wl0754 (lit c4))) ▸
       at 9 2 (CX02 ∷ Toff314 ∷ []) (lem-comm-TOFF314-CX02 (lit c4)) ▸
       at 10 2 (CS24⁻ ∷ Toff314 ∷ []) (sym (wl1371 (lit c4))) ▸
       at 11 2 (CX02 ∷ Toff314 ∷ []) (lem-comm-TOFF314-CX02 (lit c4)) ▸
       at 12 2 (CS04 ∷ Toff314 ∷ []) (sym (wp0998 c4)) ▸ done

  b5 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ023 ∷ Toff324 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-0134 ∷ Bx3-2014 ∷ Bx3-0124 ∷ [])
  b5 = at 8 5 (CCZ024 ∷ []) (sym (wp0296 c4)) ▸
       at 6 3 (Toff324 ∷ CCZ023 ∷ []) (wp0814 c4) ▸
       at 7 4 (Bx3-0214 ∷ []) (sym (lem-box-cP-at031031 c4)) ▸
       at 7 1 (Bx3-0124 ∷ []) (sym (lem-box-perm-1324-at03102132 c4)) ▸
       at 5 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0442 (lit c4))) ▸
       at 6 3 (Bx2-4031 ∷ Bx3-4021 ∷ []) (lem-Tu-box-at02142041 c4) ▸
       at 6 1 (Bx2-0134 ∷ []) (lem-box-perm-2431-at02142041 c4) ▸
       at 7 1 (Bx3-2014 ∷ []) (lem-box-perm-3241-at0314203241 c4) ▸ done

  b6 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-0134 ∷ Bx3-2014 ∷ Bx3-0124 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ Bx3-4021 ∷ Bx3-0124 ∷ [])
  b6 = at 6 2 (Bx3-2014 ∷ Bx2-0134 ∷ []) (lem-box-box-3-at021021 c4) ▸
       at 6 1 (Bx3-4021 ∷ []) (lem-box-perm-4213-at03122031 c4) ▸
       at 7 1 (Bx2-4031 ∷ []) (lem-box-perm-4132-at021021 c4) ▸
       at 6 1 (Bx3-0124 ∷ []) (lem-box-perm-2431-at0314203241 c4) ▸
       at 7 1 (Bx2-3014 ∷ []) (lem-box-perm-3241-at02142041 c4) ▸
       at 6 2 (Bx2-3014 ∷ Bx3-0124 ∷ []) (lem-box-box-3-at03102132 c4) ▸
       at 6 1 (Bx2-4031 ∷ []) (lem-box-perm-4213-at02132031 c4) ▸
       at 7 1 (Bx3-4021 ∷ []) (lem-box-perm-4132-at03102132 c4) ▸ done

  b7 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ Bx3-4021 ∷ Bx3-0124 ∷ []) (Bx2-0134 ∷ [])
  b7 = at 7 1 (Bx3-0124 ∷ []) (lem-box-perm-2431-at0314203241 c4) ▸
       at 7 2 [] (lem-box2-at03102132 c4) ▸
       at 0 6 [] (wl1373 (lit c4)) ▸
       at 0 1 (Bx2-0134 ∷ []) (lem-box-perm-2431-at02142041 c4) ▸ done

-- L-Toff-0: 4 steps
lem-L-Toff-0 : Ws → ⟪ (CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ []) ⟫ʷ
lem-L-Toff-0 c4 = run b0
  where
  b0 : Chain (CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ [])
  b0 = at 1 45 (Bx3-0124 ∷ []) (lem-L-CCZ-0 c4) ▸
       at 2 2 (CK40⁻ ∷ []) (wp1218 c4) ▸
       at 1 1 (Bx3-1240 ∷ []) (lem-box-perm-2341-at03102132 c4) ▸
       at 0 3 (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ []) (lem-CK-box-at033440 c4) ▸ done

-- F1-rel-269@0: 4 steps
lem-F1-rel-269at0 : Ws → ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-F1-rel-269at0 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 0 3 (CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (lem-deb-P-hi-at132132 c4) ▸
       at 42 3 (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (lem-deb-P-lo-at02132031 c4) ▸
       at 0 83 (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS12 ∷ CS12 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (sym (wp1270 c4)) ▸
       at 0 83 (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (sym (lem-deb-rel-269at0-R c4)) ▸ done

-- F1-rel-269@1: 12 steps
lem-F1-rel-269at1 : Ws → ⟪ (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-F1-rel-269at1 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ []) (CK42 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ CS12 ∷ CS12 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CK42 ∷ CCZ234 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι1 ∷ S3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι1 ∷ CS23 ∷ CS23 ∷ CS24 ∷ CS24 ∷ CS24 ∷ [])
  b0 = at 0 3 (CK42 ∷ CCZ234 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ CS23 ∷ CS23 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (lem-deb-P-hi c4) ▸
       at 42 3 (CK42 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS12 ∷ CS12 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (lem-deb-P-lo-at132132 c4) ▸
       at 16 1 (ι1 ∷ []) (uₛ (iI) (iI ↑) Eq.refl) ▸
       at 35 1 (ι1 ∷ []) (uₛ (iI) (iI ↑) Eq.refl) ▸
       at 58 1 (ι1 ∷ []) (uₛ (iI) (iI ↑) Eq.refl) ▸
       at 77 1 (ι1 ∷ []) (uₛ (iI) (iI ↑) Eq.refl) ▸
       at 0 83 (CK42 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ S1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ CS12 ∷ CS12 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CK42 ∷ CCZ234 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι1 ∷ S3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι1 ∷ CS23 ∷ CS23 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (sym (wp1271 c4)) ▸
       at 16 1 (ι ∷ []) (uₛ (iI ↑) (iI) Eq.refl) ▸ done

  b1 : Chain (CK42 ∷ CCZ124 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι1 ∷ CS12 ∷ CS12 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CK42 ∷ CCZ234 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι1 ∷ S3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι1 ∷ CS23 ∷ CS23 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ [])
  b1 = at 35 1 (ι ∷ []) (uₛ (iI ↑) (iI) Eq.refl) ▸
       at 58 1 (ι ∷ []) (uₛ (iI ↑) (iI) Eq.refl) ▸
       at 77 1 (ι ∷ []) (uₛ (iI ↑) (iI) Eq.refl) ▸
       at 0 83 (Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) (sym (lem-deb-rel-269at1-R c4)) ▸ done

-- F1-rel-272@0: 30 steps
lem-F1-rel-272at0 : Ws → ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F1-rel-272at0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sw12 ∷ Sb0-2-43-1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 8 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 9 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 (lit c4))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 11 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 12 0 (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) (lem-TR2-1b52048e c4) ▸
       at 11 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R (lit c4)) ▸
       at 12 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R (lit c4)) ▸
       at 13 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R (lit c4)) ▸ done

  b1 : Chain (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sw12 ∷ Sb0-2-43-1 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sw12 ∷ Sb1-0-42-3 ∷ Sw01 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sw01 ∷ Sw12 ∷ Sb0-1-42-3 ∷ [])
  b1 = at 14 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R (lit c4)) ▸
       at 15 2 [] (wl0006 (lit c4)) ▸
       at 10 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R (lit c4)) ▸
       at 11 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R (lit c4)) ▸
       at 12 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R (lit c4)) ▸
       at 13 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R (lit c4)) ▸
       at 14 2 [] (wl0003 (lit c4)) ▸
       at 9 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R (lit c4)) ▸ done

  b2 : Chain (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sw12 ∷ Sb1-0-42-3 ∷ Sw01 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sw01 ∷ Sw12 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sw12 ∷ Sw12 ∷ Sb0-1-42-3 ∷ [])
  b2 = at 10 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R (lit c4)) ▸
       at 11 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R (lit c4)) ▸
       at 12 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R (lit c4)) ▸
       at 13 2 [] (wl0018 (lit c4)) ▸
       at 8 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R (lit c4)) ▸
       at 9 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R (lit c4)) ▸
       at 10 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R (lit c4)) ▸
       at 11 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R (lit c4)) ▸ done

  b3 : Chain (Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sw12 ∷ Sw12 ∷ Sb0-1-42-3 ∷ []) (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ [])
  b3 = at 12 2 [] (wl0006 (lit c4)) ▸
       at 0 5 (CK41 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (lem-deb-Q-hi-at132132 c4) ▸
       at 33 5 (CK41 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (lem-deb-Q-lo-at02132031 c4) ▸
       at 65 2 (Sb0-1-42-3 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F1-comm-CSu-CSat0 c4)) ▸
       at 0 65 (CK41 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS14 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CK41 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (sym (wp1272 c4)) ▸
       at 0 67 (Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (sym (lem-deb-rel-272at0-R c4)) ▸ done

-- ckt-A: 264 steps
lem-ckt-A : Ws → ⟪ (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ
lem-ckt-A c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (run b32))))))))))))))))))))))))))))))))
  where
  b0 : Chain (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ []) (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ CS04 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sw12 ∷ [])
  b0 = at 19 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 18 2 (Sw12 ∷ S4 ∷ []) (sym (c₃ (Swap ↑) (S ↑))) ▸
       at 17 2 (Sw12 ∷ CK40 ∷ []) (lem-comm-push-CK40-sw1-L (lit c4)) ▸
       at 16 2 (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L (lit c4)) ▸
       at 15 2 (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L (lit c4)) ▸
       at 14 2 (Sw12 ∷ CK40 ∷ []) (lem-comm-push-CK40-sw1-L (lit c4)) ▸
       at 13 2 (Sw12 ∷ S4 ∷ []) (sym (c₃ (Swap ↑) (S ↑))) ▸
       at 12 2 (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L (lit c4)) ▸ done

  b1 : Chain (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ CS04 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sw12 ∷ []) (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ Sw12 ∷ S4 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sw12 ∷ [])
  b1 = at 11 2 (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L (lit c4)) ▸
       at 10 2 (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L (lit c4)) ▸
       at 9 2 (Sw12 ∷ Sb1-0-42-3 ∷ []) (lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L (lit c4)) ▸
       at 8 2 (Sw12 ∷ CK42 ∷ []) (wl0087 (lit c4)) ▸
       at 7 2 (Sw12 ∷ Sb1-0-42-3 ∷ []) (lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L (lit c4)) ▸
       at 6 2 (Sw12 ∷ CK42 ∷ []) (wl0087 (lit c4)) ▸
       at 5 2 (Sw12 ∷ Sb1-0-42-3 ∷ []) (lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L (lit c4)) ▸
       at 4 2 (Sw12 ∷ S4 ∷ []) (sym (c₃ (Swap ↑) (S ↑))) ▸ done

  b2 : Chain (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ Sw12 ∷ S4 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sw12 ∷ []) (Sw12 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CK40 ∷ CS04 ∷ Sw01 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw01 ∷ Sw12 ∷ [])
  b2 = at 3 2 (Sw12 ∷ CK40 ∷ []) (lem-comm-push-CK40-sw1-L (lit c4)) ▸
       at 2 2 (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L (lit c4)) ▸
       at 1 2 (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L (lit c4)) ▸
       at 0 2 (Sw12 ∷ CK40 ∷ []) (lem-comm-push-CK40-sw1-L (lit c4)) ▸
       at 20 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 (lit c4))) ▸
       at 19 2 (Sw01 ∷ S4 ∷ []) (sym (c₂ (Swap) (S ↑ ↑))) ▸
       at 18 2 (Sw01 ∷ CK41 ∷ []) (lem-comm-push-CK40-sw0-L (lit c4)) ▸
       at 17 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸ done

  b3 : Chain (Sw12 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CK40 ∷ CS04 ∷ Sw01 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ Sw01 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw01 ∷ Sw12 ∷ [])
  b3 = at 16 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 15 2 (Sw01 ∷ CK41 ∷ []) (lem-comm-push-CK40-sw0-L (lit c4)) ▸
       at 14 2 (Sw01 ∷ S4 ∷ []) (sym (c₂ (Swap) (S ↑ ↑))) ▸
       at 13 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 12 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 11 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 10 2 (Sw01 ∷ Sb0-1-42-3 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L (lit c4)) ▸
       at 9 2 (Sw01 ∷ CK42 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑))) ▸ done

  b4 : Chain (Sw12 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ Sw01 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw01 ∷ Sw12 ∷ [])
  b4 = at 8 2 (Sw01 ∷ Sb0-1-42-3 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L (lit c4)) ▸
       at 7 2 (Sw01 ∷ CK42 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑))) ▸
       at 6 2 (Sw01 ∷ Sb0-1-42-3 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L (lit c4)) ▸
       at 5 2 (Sw01 ∷ S4 ∷ []) (sym (c₂ (Swap) (S ↑ ↑))) ▸
       at 4 2 (Sw01 ∷ CK41 ∷ []) (lem-comm-push-CK40-sw0-L (lit c4)) ▸
       at 3 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 2 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L (lit c4)) ▸
       at 1 2 (Sw01 ∷ CK41 ∷ []) (lem-comm-push-CK40-sw0-L (lit c4)) ▸ done

  b5 : Chain (Sw12 ∷ Sw01 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ Sw23 ∷ CS14 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b5 = at 21 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 (lit c4))) ▸
       at 20 2 (Sw23 ∷ S4 ∷ []) (sym (c₄ (Swap ↑ ↑) (S))) ▸
       at 19 2 (Sw23 ∷ CK41 ∷ []) (wl0099 (lit c4)) ▸
       at 18 2 (Sw23 ∷ CS14 ∷ []) (wl0017 (lit c4)) ▸
       at 17 2 (Sw23 ∷ CS14 ∷ []) (wl0017 (lit c4)) ▸
       at 16 2 (Sw23 ∷ CK41 ∷ []) (wl0099 (lit c4)) ▸
       at 15 2 (Sw23 ∷ S4 ∷ []) (sym (c₄ (Swap ↑ ↑) (S))) ▸
       at 14 2 (Sw23 ∷ CS14 ∷ []) (wl0017 (lit c4)) ▸ done

  b6 : Chain (Sw12 ∷ Sw01 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ Sw23 ∷ CS14 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw23 ∷ S4 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b6 = at 13 2 (Sw23 ∷ CS14 ∷ []) (wl0017 (lit c4)) ▸
       at 12 2 (Sw23 ∷ CS14 ∷ []) (wl0017 (lit c4)) ▸
       at 11 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸
       at 10 2 (Sw23 ∷ CK43 ∷ []) (wl0090 (lit c4)) ▸
       at 9 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸
       at 8 2 (Sw23 ∷ CK43 ∷ []) (wl0090 (lit c4)) ▸
       at 7 2 (Sw23 ∷ Sb0-1-43-2 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L (lit c4)) ▸
       at 6 2 (Sw23 ∷ S4 ∷ []) (sym (c₄ (Swap ↑ ↑) (S))) ▸ done

  b7 : Chain (Sw12 ∷ Sw01 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw23 ∷ S4 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw23 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CK41 ∷ CS14 ∷ Sw12 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b7 = at 5 2 (Sw23 ∷ CK41 ∷ []) (wl0099 (lit c4)) ▸
       at 4 2 (Sw23 ∷ CS14 ∷ []) (wl0017 (lit c4)) ▸
       at 3 2 (Sw23 ∷ CS14 ∷ []) (wl0017 (lit c4)) ▸
       at 2 2 (Sw23 ∷ CK41 ∷ []) (wl0099 (lit c4)) ▸
       at 22 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 (lit c4))) ▸
       at 21 2 (Sw12 ∷ S4 ∷ []) (sym (c₃ (Swap ↑) (S ↑))) ▸
       at 20 2 (Sw12 ∷ CK42 ∷ []) (wl0087 (lit c4)) ▸
       at 19 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸ done

  b8 : Chain (Sw12 ∷ Sw01 ∷ Sw23 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CK41 ∷ CS14 ∷ Sw12 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw23 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ Sw12 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b8 = at 18 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 17 2 (Sw12 ∷ CK42 ∷ []) (wl0087 (lit c4)) ▸
       at 16 2 (Sw12 ∷ S4 ∷ []) (sym (c₃ (Swap ↑) (S ↑))) ▸
       at 15 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 14 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 13 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 12 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸
       at 11 2 (Sw12 ∷ CK43 ∷ []) (sym (c₃ (Swap ↑) (CK₁₀))) ▸ done

  b9 : Chain (Sw12 ∷ Sw01 ∷ Sw23 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ Sw12 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b9 = at 10 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸
       at 9 2 (Sw12 ∷ CK43 ∷ []) (sym (c₃ (Swap ↑) (CK₁₀))) ▸
       at 8 2 (Sw12 ∷ Sb0-2-43-1 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L (lit c4)) ▸
       at 7 2 (Sw12 ∷ S4 ∷ []) (sym (c₃ (Swap ↑) (S ↑))) ▸
       at 6 2 (Sw12 ∷ CK42 ∷ []) (wl0087 (lit c4)) ▸
       at 5 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 4 2 (Sw12 ∷ CS24 ∷ []) (wl0013 (lit c4)) ▸
       at 3 2 (Sw12 ∷ CK42 ∷ []) (wl0087 (lit c4)) ▸ done

  b10 : Chain (Sw12 ∷ Sw01 ∷ Sw23 ∷ Sw12 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw23 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sw12 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b10 = at 4 19 (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ []) (lem-TR2-ff6c1f51 c4) ▸
       at 3 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0087 (lit c4))) ▸
       at 4 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 5 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 6 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0087 (lit c4))) ▸
       at 7 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 8 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R (lit c4)) ▸
       at 9 2 (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀)) ▸ done

  b11 : Chain (Sw12 ∷ Sw01 ∷ Sw23 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sw12 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw23 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CK41 ∷ Sw12 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b11 = at 10 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R (lit c4)) ▸
       at 11 2 (CK43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CK₁₀)) ▸
       at 12 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R (lit c4)) ▸
       at 13 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 14 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 15 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 16 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 17 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0087 (lit c4))) ▸ done

  b12 : Chain (Sw12 ∷ Sw01 ∷ Sw23 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CK41 ∷ Sw12 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw23 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw12 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b12 = at 18 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 19 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 20 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0087 (lit c4))) ▸
       at 21 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 22 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0087 (lit c4))) ▸
       at 23 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 24 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 25 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0087 (lit c4))) ▸ done

  b13 : Chain (Sw12 ∷ Sw01 ∷ Sw23 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ Sw12 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw23 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ Sw12 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b13 = at 26 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 27 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R (lit c4)) ▸
       at 28 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0087 (lit c4))) ▸
       at 29 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 30 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 31 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0087 (lit c4))) ▸
       at 32 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 33 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0087 (lit c4))) ▸ done

  b14 : Chain (Sw12 ∷ Sw01 ∷ Sw23 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ Sw12 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw23 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sw12 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b14 = at 34 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 35 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 36 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0087 (lit c4))) ▸
       at 37 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 38 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R (lit c4)) ▸
       at 39 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R (lit c4)) ▸
       at 40 2 (Sb0-1-43-2 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R (lit c4)) ▸
       at 41 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0087 (lit c4))) ▸ done

  b15 : Chain (Sw12 ∷ Sw01 ∷ Sw23 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ Sw12 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ CK41 ∷ CS14 ∷ CS14 ∷ Sw23 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b15 = at 42 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 43 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 (lit c4))) ▸
       at 44 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0087 (lit c4))) ▸
       at 45 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 46 2 [] (wl0006 (lit c4)) ▸
       at 2 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0099 (lit c4))) ▸
       at 3 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 4 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0017 (lit c4))) ▸ done

  b16 : Chain (Sw12 ∷ Sw01 ∷ CK41 ∷ CS14 ∷ CS14 ∷ Sw23 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CK43 ∷ Sb0-1-43-2 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ Sw23 ∷ CS14 ∷ CS14 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b16 = at 5 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0099 (lit c4))) ▸
       at 6 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 7 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R (lit c4)) ▸
       at 8 2 (CK42 ∷ Sw23 ∷ []) (sym (wl0090 (lit c4))) ▸
       at 9 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R (lit c4)) ▸
       at 10 2 (CK42 ∷ Sw23 ∷ []) (sym (wl0090 (lit c4))) ▸
       at 11 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R (lit c4)) ▸
       at 12 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0017 (lit c4))) ▸ done

  b17 : Chain (Sw12 ∷ Sw01 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ Sw23 ∷ CS14 ∷ CS14 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw23 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b17 = at 13 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 14 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 15 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 16 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0099 (lit c4))) ▸
       at 17 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 18 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 19 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0099 (lit c4))) ▸
       at 20 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸ done

  b18 : Chain (Sw12 ∷ Sw01 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw23 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ Sw23 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b18 = at 21 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0099 (lit c4))) ▸
       at 22 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 23 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 24 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0099 (lit c4))) ▸
       at 25 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 26 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R (lit c4)) ▸
       at 27 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0099 (lit c4))) ▸
       at 28 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0017 (lit c4))) ▸ done

  b19 : Chain (Sw12 ∷ Sw01 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ Sw23 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw23 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b19 = at 29 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 30 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0099 (lit c4))) ▸
       at 31 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸
       at 32 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0099 (lit c4))) ▸
       at 33 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 34 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 35 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0099 (lit c4))) ▸
       at 36 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸ done

  b20 : Chain (Sw12 ∷ Sw01 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw23 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ Sb0-1-43-2 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw23 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ [])
  b20 = at 37 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R (lit c4)) ▸
       at 38 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R (lit c4)) ▸
       at 39 2 (Sb0-1-42-3 ∷ Sw23 ∷ []) (lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R (lit c4)) ▸
       at 40 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0099 (lit c4))) ▸
       at 41 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 42 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0017 (lit c4))) ▸
       at 43 2 (CK41 ∷ Sw23 ∷ []) (sym (wl0099 (lit c4))) ▸
       at 44 2 (S4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (S)) ▸ done

  b21 : Chain (Sw12 ∷ Sw01 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw23 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sw01 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw01 ∷ Sw12 ∷ [])
  b21 = at 45 2 [] (wl0003 (lit c4)) ▸
       at 1 2 (CK40 ∷ Sw01 ∷ []) (lem-comm-push-CK41-sw0-R (lit c4)) ▸
       at 2 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 3 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 4 2 (CK40 ∷ Sw01 ∷ []) (lem-comm-push-CK41-sw0-R (lit c4)) ▸
       at 5 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 6 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R (lit c4)) ▸
       at 7 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸ done

  b22 : Chain (Sw12 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sw01 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CK40 ∷ Sw01 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw01 ∷ Sw12 ∷ [])
  b22 = at 8 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R (lit c4)) ▸
       at 9 2 (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑)) ▸
       at 10 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R (lit c4)) ▸
       at 11 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 12 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 13 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 14 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 15 2 (CK40 ∷ Sw01 ∷ []) (lem-comm-push-CK41-sw0-R (lit c4)) ▸ done

  b23 : Chain (Sw12 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CK40 ∷ Sw01 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ Sw01 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw01 ∷ Sw12 ∷ [])
  b23 = at 16 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 17 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 18 2 (CK40 ∷ Sw01 ∷ []) (lem-comm-push-CK41-sw0-R (lit c4)) ▸
       at 19 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 20 2 (CK40 ∷ Sw01 ∷ []) (lem-comm-push-CK41-sw0-R (lit c4)) ▸
       at 21 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 22 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 23 2 (CK40 ∷ Sw01 ∷ []) (lem-comm-push-CK41-sw0-R (lit c4)) ▸ done

  b24 : Chain (Sw12 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ Sw01 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CK40 ∷ Sw01 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw01 ∷ Sw12 ∷ [])
  b24 = at 24 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 25 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R (lit c4)) ▸
       at 26 2 (CK40 ∷ Sw01 ∷ []) (lem-comm-push-CK41-sw0-R (lit c4)) ▸
       at 27 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 28 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 29 2 (CK40 ∷ Sw01 ∷ []) (lem-comm-push-CK41-sw0-R (lit c4)) ▸
       at 30 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 31 2 (CK40 ∷ Sw01 ∷ []) (lem-comm-push-CK41-sw0-R (lit c4)) ▸ done

  b25 : Chain (Sw12 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CK40 ∷ Sw01 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sw01 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw01 ∷ Sw12 ∷ [])
  b25 = at 32 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 33 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 34 2 (CK40 ∷ Sw01 ∷ []) (lem-comm-push-CK41-sw0-R (lit c4)) ▸
       at 35 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 36 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R (lit c4)) ▸
       at 37 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R (lit c4)) ▸
       at 38 2 (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R (lit c4)) ▸
       at 39 2 (CK40 ∷ Sw01 ∷ []) (lem-comm-push-CK41-sw0-R (lit c4)) ▸ done

  b26 : Chain (Sw12 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK40 ∷ Sw01 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sw01 ∷ Sw12 ∷ []) (CK40 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sw12 ∷ [])
  b26 = at 40 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 41 2 (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R (lit c4)) ▸
       at 42 2 (CK40 ∷ Sw01 ∷ []) (lem-comm-push-CK41-sw0-R (lit c4)) ▸
       at 43 2 (S4 ∷ Sw01 ∷ []) (c₂ (Swap) (S ↑ ↑)) ▸
       at 44 2 [] (wl0018 (lit c4)) ▸
       at 0 2 (CK40 ∷ Sw12 ∷ []) (lem-comm-push-CK40-sw1-R (lit c4)) ▸
       at 1 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R (lit c4)) ▸
       at 2 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R (lit c4)) ▸ done

  b27 : Chain (CK40 ∷ CS04 ∷ CS04 ∷ Sw12 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CK42 ∷ Sb1-0-42-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sw12 ∷ []) (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ Sw12 ∷ CS04 ∷ CS04 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sw12 ∷ [])
  b27 = at 3 2 (CK40 ∷ Sw12 ∷ []) (lem-comm-push-CK40-sw1-R (lit c4)) ▸
       at 4 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 5 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R (lit c4)) ▸
       at 6 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0087 (lit c4))) ▸
       at 7 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R (lit c4)) ▸
       at 8 2 (CK41 ∷ Sw12 ∷ []) (sym (wl0087 (lit c4))) ▸
       at 9 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R (lit c4)) ▸
       at 10 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R (lit c4)) ▸ done

  b28 : Chain (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ Sw12 ∷ CS04 ∷ CS04 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sw12 ∷ []) (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sw12 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sw12 ∷ [])
  b28 = at 11 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R (lit c4)) ▸
       at 12 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R (lit c4)) ▸
       at 13 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 14 2 (CK40 ∷ Sw12 ∷ []) (lem-comm-push-CK40-sw1-R (lit c4)) ▸
       at 15 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R (lit c4)) ▸
       at 16 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R (lit c4)) ▸
       at 17 2 (CK40 ∷ Sw12 ∷ []) (lem-comm-push-CK40-sw1-R (lit c4)) ▸
       at 18 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸ done

  b29 : Chain (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sw12 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sw12 ∷ []) (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ Sw12 ∷ CS04 ∷ CK40 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sw12 ∷ [])
  b29 = at 19 2 (CK40 ∷ Sw12 ∷ []) (lem-comm-push-CK40-sw1-R (lit c4)) ▸
       at 20 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R (lit c4)) ▸
       at 21 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R (lit c4)) ▸
       at 22 2 (CK40 ∷ Sw12 ∷ []) (lem-comm-push-CK40-sw1-R (lit c4)) ▸
       at 23 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 24 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R (lit c4)) ▸
       at 25 2 (CK40 ∷ Sw12 ∷ []) (lem-comm-push-CK40-sw1-R (lit c4)) ▸
       at 26 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R (lit c4)) ▸ done

  b30 : Chain (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ Sw12 ∷ CS04 ∷ CK40 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sw12 ∷ []) (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sw12 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sw12 ∷ [])
  b30 = at 27 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R (lit c4)) ▸
       at 28 2 (CK40 ∷ Sw12 ∷ []) (lem-comm-push-CK40-sw1-R (lit c4)) ▸
       at 29 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸
       at 30 2 (CK40 ∷ Sw12 ∷ []) (lem-comm-push-CK40-sw1-R (lit c4)) ▸
       at 31 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R (lit c4)) ▸
       at 32 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R (lit c4)) ▸
       at 33 2 (CK40 ∷ Sw12 ∷ []) (lem-comm-push-CK40-sw1-R (lit c4)) ▸
       at 34 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸ done

  b31 : Chain (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sw12 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ Sb1-0-42-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sw12 ∷ []) (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sw12 ∷ Sw12 ∷ [])
  b31 = at 35 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R (lit c4)) ▸
       at 36 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R (lit c4)) ▸
       at 37 2 (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R (lit c4)) ▸
       at 38 2 (CK40 ∷ Sw12 ∷ []) (lem-comm-push-CK40-sw1-R (lit c4)) ▸
       at 39 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R (lit c4)) ▸
       at 40 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R (lit c4)) ▸
       at 41 2 (CK40 ∷ Sw12 ∷ []) (lem-comm-push-CK40-sw1-R (lit c4)) ▸
       at 42 2 (S4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (S ↑)) ▸ done

  b32 : Chain (CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS04 ∷ CS04 ∷ CS04 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ CS04 ∷ CS04 ∷ CK40 ∷ S4 ∷ Sw12 ∷ Sw12 ∷ []) (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ [])
  b32 = at 43 2 [] (wl0006 (lit c4)) ▸
       at 0 30 (CK41 ∷ CS14 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ S0 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ ι ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (lem-deb-AD-at02132031 c4) ▸
       at 42 13 (X0 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X0 ∷ []) (sym (lem-ckt-Dinv c4)) ▸
       at 43 1 (Sb2-4-01-3 ∷ []) (lem-S-sym-xt-at14213243 c4) ▸
       at 44 1 (Sb2-4-01-3 ∷ []) (lem-S-sym-xt-at14213243 c4) ▸
       at 45 1 (Sb2-4-01-3 ∷ []) (lem-S-sym-xt-at14213243 c4) ▸
       at 0 42 (X0 ∷ CCZ014 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ S4 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ CS14 ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ S4 ∷ S4 ∷ S4 ∷ ι ∷ CS01 ∷ X0 ∷ []) (wp1308 c4) ▸
       at 0 54 (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ CS04 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (lem-ckt-A-R c4)) ▸ done
