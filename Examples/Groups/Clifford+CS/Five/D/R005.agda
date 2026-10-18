{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R005 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0002 ; wl0003 ; wl0004 ; wl0005 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0011 ; wl0012 ; wl0013 ; wl0014 ; wl0018 ; wl0019 ; wl0020 ; wl0021 ; wl0022 ; wl0028 ; wl0029 ; wl0033 ; wl0036 ; wl0037 ; wl0038 ; wl0044 ; wl0045 ; wl0046 ; wl0047 ; wl0050 ; wl0051 ; wl0057 ; wl0058 ; wl0059 ; wl0060 ; wl0064 ; wl0065 ; wl0066 ; wl0067 ; wl0072 ; wl0075 ; wl0084 ; wl0085 ; wl0086 ; wl0087 ; wl0090 ; wl0091 ; wl0093 ; wl0094 ; wl0095 ; wl0096 ; wl0097 ; wl0098 ; wl0099 ; wl0100)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-push-CS04-sw1-R ; lem-comm-push-CX04-sw0-L ; lem-comm-push-CX04-sw1-L)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-push-TOFF023-sw3-L ; lem-comm-push-TOFF024-sw3-L)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-push-CCZ023-sw3-L ; lem-comm-push-CCZ024-sw3-L ; lem-comm-push-SWAP04-sw2-L ; lem-comm-push-TOFF203-sw3-L ; lem-comm-push-TOFF204-sw3-L)
-- comm CX21 TOFF034: 15 steps
lem-comm-CX21-TOFF034 : WsL → ⟪ (CX21 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CX21 ∷ []) ⟫ʷ
lem-comm-CX21-TOFF034 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX21 ∷ Toff034 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ CX43 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CX32 ∷ []) (wl0057 c4) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CX42 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ CX43 ∷ []) (wl0058 c4) ▸
       at 4 2 (Toff012 ∷ CX43 ∷ []) (sym (c₃ (Toff) (CX₁₀))) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ CX43 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Toff034 ∷ CX21 ∷ [])
  b1 = at 5 2 (Sw23 ∷ CX42 ∷ []) (wl0059 c4) ▸
       at 6 1 (Sw34 ∷ CX32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 7 2 (Sw12 ∷ CX31 ∷ []) (wl0060 c4) ▸
       at 8 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (wl0003 c4) ▸
       at 0 9 (Toff034 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CCZ124 CS03: 9 steps
lem-comm-CCZ124-CS03 : WsL → ⟪ (CCZ124 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CCZ124 ∷ []) ⟫ʷ
lem-comm-CCZ124-CS03 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ124 ∷ CS03 ∷ []) (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CCZ124 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CCZ234 ∷ []) (wl0037 c4) ▸
       at 2 2 (CS01 ∷ CCZ234 ∷ []) (sym (c₂ (CS) (CCZ))) ▸
       at 3 2 (Sw12 ∷ CCZ134 ∷ []) (wl0044 c4) ▸
       at 4 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CCZ124 ∷ []) (CS03 ∷ CCZ124 ∷ [])
  b1 = at 0 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CCZ024 CX31: 11 steps
lem-comm-CCZ024-CX31 : WsL → ⟪ (CCZ024 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ CCZ024 ∷ []) ⟫ʷ
lem-comm-CCZ024-CX31 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ024 ∷ CX31 ∷ []) (Sw12 ∷ Sw34 ∷ Sw34 ∷ CX32 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX32 ∷ Sw12 ∷ []) (sym (wl0060 c4)) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CX42 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX43 ∷ Sw23 ∷ []) (sym (wl0059 c4)) ▸
       at 3 2 (CX43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CX₁₀)) ▸
       at 2 2 (CX42 ∷ Sw23 ∷ []) (sym (wl0058 c4)) ▸
       at 2 1 (Sw34 ∷ CX32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw34 ∷ CX32 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (CX31 ∷ CCZ024 ∷ [])
  b1 = at 1 2 [] (wl0004 c4) ▸
       at 0 2 (CX31 ∷ Sw12 ∷ []) (sym (wl0057 c4)) ▸
       at 1 7 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF034 CX12: 15 steps
lem-comm-TOFF034-CX12 : WsL → ⟪ (Toff034 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ Toff034 ∷ []) ⟫ʷ
lem-comm-TOFF034-CX12 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff034 ∷ CX12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CX34 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 8 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX23 ∷ Sw12 ∷ []) (sym (wl0022 c4)) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (CX24 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX34 ∷ Sw23 ∷ []) (sym (wl0021 c4)) ▸
       at 4 2 (CX34 ∷ Toff012 ∷ []) (c₃ (Toff) (CX₀₁)) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CX34 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (CX12 ∷ Toff034 ∷ [])
  b1 = at 3 2 (CX24 ∷ Sw23 ∷ []) (sym (wl0020 c4)) ▸
       at 3 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0004 c4) ▸
       at 1 2 (CX13 ∷ Sw12 ∷ []) (sym (wl0019 c4)) ▸
       at 1 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 1 9 (Toff034 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CCZ014 CX23: 9 steps
lem-comm-CCZ014-CX23 : WsL → ⟪ (CCZ014 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ CCZ014 ∷ []) ⟫ʷ
lem-comm-CCZ014-CX23 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ014 ∷ CX23 ∷ []) (CX23 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CX24 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX34 ∷ Sw23 ∷ []) (sym (wl0021 c4)) ▸
       at 2 2 (CX34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CX₀₁)) ▸
       at 1 2 (CX24 ∷ Sw23 ∷ []) (sym (wl0020 c4)) ▸
       at 1 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0004 c4) ▸ done

  b1 : Chain (CX23 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) (CX23 ∷ CCZ014 ∷ [])
  b1 = at 1 5 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF023 CX14: 23 steps
lem-comm-TOFF023-CX14 : WsL → ⟪ (Toff023 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ Toff023 ∷ []) ⟫ʷ
lem-comm-TOFF023-CX14 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Toff023 ∷ CX14 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ CX23 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Toff024 ∷ []) (lem-comm-push-TOFF023-sw3-L c4) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (Toff034 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 10 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX23 ∷ Sw12 ∷ []) (sym (wl0022 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ CX23 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ CX13 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ [])
  b1 = at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 8 3 (CX24 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX34 ∷ Sw23 ∷ []) (sym (wl0021 c4)) ▸
       at 6 2 (CX34 ∷ Toff012 ∷ []) (c₃ (Toff) (CX₀₁)) ▸
       at 5 2 (CX24 ∷ Sw23 ∷ []) (sym (wl0020 c4)) ▸
       at 5 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 3 2 (CX13 ∷ Sw12 ∷ []) (sym (wl0019 c4)) ▸ done

  b2 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ CX13 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ []) (CX14 ∷ Toff023 ∷ [])
  b2 = at 3 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0003 c4) ▸
       at 3 9 (Toff034 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸
       at 4 2 (Sw34 ∷ Toff023 ∷ []) (lem-comm-push-TOFF024-sw3-L c4) ▸
       at 0 5 (CX14 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CX23 TOFF014: 9 steps
lem-comm-CX23-TOFF014 : WsL → ⟪ (CX23 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CX23 ∷ []) ⟫ʷ
lem-comm-CX23-TOFF014 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX23 ∷ Toff014 ∷ []) (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ CX23 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CX24 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ CX34 ∷ []) (wl0020 c4) ▸
       at 2 2 (Toff012 ∷ CX34 ∷ []) (sym (c₃ (Toff) (CX₀₁))) ▸
       at 3 2 (Sw23 ∷ CX24 ∷ []) (wl0021 c4) ▸
       at 4 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ CX23 ∷ []) (Toff014 ∷ CX23 ∷ [])
  b1 = at 0 5 (Toff014 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CCZ034 CS12: 15 steps
lem-comm-CCZ034-CS12 : WsL → ⟪ (CCZ034 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CCZ034 ∷ []) ⟫ʷ
lem-comm-CCZ034-CS12 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ034 ∷ CS12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS34 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 8 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CS23 ∷ Sw12 ∷ []) (sym (wl0047 c4)) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 c4)) ▸
       at 4 2 (CS34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS)) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS34 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (CS12 ∷ CCZ034 ∷ [])
  b1 = at 3 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 3 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0004 c4) ▸
       at 1 2 (CS13 ∷ Sw12 ∷ []) (sym (wl0046 c4)) ▸
       at 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 1 9 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF013 CS24: 15 steps
lem-comm-TOFF013-CS24 : WsL → ⟪ (Toff013 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Toff013 ∷ []) ⟫ʷ
lem-comm-TOFF013-CS24 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff013 ∷ CS24 ∷ []) (Sw34 ∷ Sw34 ∷ Sw23 ∷ CS34 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 c4)) ▸
       at 3 2 (CS34 ∷ Toff012 ∷ []) (c₃ (Toff) (CS)) ▸ done

  b1 : Chain (Sw34 ∷ Sw34 ∷ Sw23 ∷ CS34 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ []) (CS24 ∷ Toff013 ∷ [])
  b1 = at 2 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 2 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0004 c4) ▸
       at 2 5 (Toff014 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 0 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF014 CX23: 9 steps
lem-comm-TOFF014-CX23 : WsL → ⟪ (Toff014 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ Toff014 ∷ []) ⟫ʷ
lem-comm-TOFF014-CX23 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff014 ∷ CX23 ∷ []) (CX23 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CX24 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX34 ∷ Sw23 ∷ []) (sym (wl0021 c4)) ▸
       at 2 2 (CX34 ∷ Toff012 ∷ []) (c₃ (Toff) (CX₀₁)) ▸
       at 1 2 (CX24 ∷ Sw23 ∷ []) (sym (wl0020 c4)) ▸
       at 1 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0004 c4) ▸ done

  b1 : Chain (CX23 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ []) (CX23 ∷ Toff014 ∷ [])
  b1 = at 1 5 (Toff014 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CCZ024 CS13: 11 steps
lem-comm-CCZ024-CS13 : WsL → ⟪ (CCZ024 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CCZ024 ∷ []) ⟫ʷ
lem-comm-CCZ024-CS13 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ024 ∷ CS13 ∷ []) (Sw12 ∷ Sw34 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS23 ∷ Sw12 ∷ []) (sym (wl0047 c4)) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 c4)) ▸
       at 3 2 (CS34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS)) ▸
       at 2 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 2 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (CS13 ∷ CCZ024 ∷ [])
  b1 = at 1 2 [] (wl0004 c4) ▸
       at 0 2 (CS13 ∷ Sw12 ∷ []) (sym (wl0046 c4)) ▸
       at 1 7 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CCZ024 CSd13: 11 steps
lem-comm-CCZ024-CSd13 : WsL → ⟪ (CCZ024 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CCZ024 ∷ []) ⟫ʷ
lem-comm-CCZ024-CSd13 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ024 ∷ CS13⁻ ∷ []) (Sw12 ∷ Sw34 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS23⁻ ∷ Sw12 ∷ []) (sym (wl0029 c4)) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 3 2 (CS34⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS • CS • CS)) ▸
       at 2 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 2 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (CS13⁻ ∷ CCZ024 ∷ [])
  b1 = at 1 2 [] (wl0004 c4) ▸
       at 0 2 (CS13⁻ ∷ Sw12 ∷ []) (sym (wl0028 c4)) ▸
       at 1 7 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF013 CX24: 15 steps
lem-comm-TOFF013-CX24 : WsL → ⟪ (Toff013 ∷ CX24 ∷ []) ⟫ʷ ≈ ⟪ (CX24 ∷ Toff013 ∷ []) ⟫ʷ
lem-comm-TOFF013-CX24 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff013 ∷ CX24 ∷ []) (Sw34 ∷ Sw34 ∷ Sw23 ∷ CX34 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CX24 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX34 ∷ Sw23 ∷ []) (sym (wl0021 c4)) ▸
       at 3 2 (CX34 ∷ Toff012 ∷ []) (c₃ (Toff) (CX₀₁)) ▸ done

  b1 : Chain (Sw34 ∷ Sw34 ∷ Sw23 ∷ CX34 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ []) (CX24 ∷ Toff013 ∷ [])
  b1 = at 2 2 (CX24 ∷ Sw23 ∷ []) (sym (wl0020 c4)) ▸
       at 2 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0004 c4) ▸
       at 2 5 (Toff014 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 0 3 (CX24 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CCZ034 CX12: 15 steps
lem-comm-CCZ034-CX12 : WsL → ⟪ (CCZ034 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ CCZ034 ∷ []) ⟫ʷ
lem-comm-CCZ034-CX12 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ034 ∷ CX12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CX34 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 8 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX23 ∷ Sw12 ∷ []) (sym (wl0022 c4)) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (CX24 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX34 ∷ Sw23 ∷ []) (sym (wl0021 c4)) ▸
       at 4 2 (CX34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CX₀₁)) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CX34 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (CX12 ∷ CCZ034 ∷ [])
  b1 = at 3 2 (CX24 ∷ Sw23 ∷ []) (sym (wl0020 c4)) ▸
       at 3 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0004 c4) ▸
       at 1 2 (CX13 ∷ Sw12 ∷ []) (sym (wl0019 c4)) ▸
       at 1 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 1 9 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm SWAP12 BOX(3;04): 13 steps
lem-comm-SWAP12-BOX⟨3·04⟩ : WsL → ⟪ (Sw12 ∷ Bx3-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-04 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-SWAP12-BOX⟨3·04⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx3-04 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw13 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (Sw13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Sw23 ∷ []) (sym (wl0075 c4)) ▸
       at 3 2 (CZ01 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 4 2 (Sw12 ∷ Sw13 ∷ []) (sym (wl0096 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw13 ∷ Sw23 ∷ Sw34 ∷ []) (Bx3-04 ∷ Sw12 ∷ [])
  b1 = at 5 1 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 0 7 (CZ04 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Bx3-04 ∷ []) (refl) ▸ done


-- comm TOFF213 CS04: 13 steps
lem-comm-TOFF213-CS04 : WsL → ⟪ (Toff213 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Toff213 ∷ []) ⟫ʷ
lem-comm-TOFF213-CS04 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff213 ∷ CS04 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Toff314 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Toff324 ∷ []) (sym (wl0038 c4)) ▸
       at 3 2 (CS01 ∷ Toff324 ∷ []) (sym (c₂ (CS) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 4 2 (Sw12 ∷ Toff314 ∷ []) (sym (wl0045 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Toff314 ∷ Sw23 ∷ Sw34 ∷ []) (CS04 ∷ Toff213 ∷ [])
  b1 = at 5 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 6 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 0 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF023 CS14: 23 steps
lem-comm-TOFF023-CS14 : WsL → ⟪ (Toff023 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Toff023 ∷ []) ⟫ʷ
lem-comm-TOFF023-CS14 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Toff023 ∷ CS14 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Toff024 ∷ []) (lem-comm-push-TOFF023-sw3-L c4) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (Toff034 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 10 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CS23 ∷ Sw12 ∷ []) (sym (wl0047 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ [])
  b1 = at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 8 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 c4)) ▸
       at 6 2 (CS34 ∷ Toff012 ∷ []) (c₃ (Toff) (CS)) ▸
       at 5 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 3 2 (CS13 ∷ Sw12 ∷ []) (sym (wl0046 c4)) ▸ done

  b2 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ []) (CS14 ∷ Toff023 ∷ [])
  b2 = at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0003 c4) ▸
       at 3 9 (Toff034 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸
       at 4 2 (Sw34 ∷ Toff023 ∷ []) (lem-comm-push-TOFF024-sw3-L c4) ▸
       at 0 5 (CS14 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CS14 TOFF203: 7 steps
lem-comm-CS14-TOFF203 : WsL → ⟪ (CS14 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CS14 ∷ []) ⟫ʷ
lem-comm-CS14-TOFF203 c4 = run b0
  where
  b0 : Chain (CS14 ∷ Toff203 ∷ []) (Toff203 ∷ CS14 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CS24 ∷ []) (wl0013 c4) ▸
       at 1 2 (Sw23 ∷ CS34 ∷ []) (wl0011 c4) ▸
       at 2 2 (Toff102 ∷ CS34 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (CS))) ▸
       at 3 2 (Sw23 ∷ CS24 ∷ []) (wl0008 c4) ▸
       at 4 2 (Sw12 ∷ CS14 ∷ []) (wl0005 c4) ▸
       at 0 5 (Toff203 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CCZ124 CX03: 9 steps
lem-comm-CCZ124-CX03 : WsL → ⟪ (CCZ124 ∷ CX03 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ CCZ124 ∷ []) ⟫ʷ
lem-comm-CCZ124-CX03 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ124 ∷ CX03 ∷ []) (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ CCZ124 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CCZ234 ∷ []) (wl0037 c4) ▸
       at 2 2 (CX01 ∷ CCZ234 ∷ []) (sym (c₂ (CX₀₁) (CCZ))) ▸
       at 3 2 (Sw12 ∷ CCZ134 ∷ []) (wl0044 c4) ▸
       at 4 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ CCZ124 ∷ []) (CX03 ∷ CCZ124 ∷ [])
  b1 = at 0 5 (CX03 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF203 CK41: 23 steps
lem-comm-TOFF203-CK41 : WsL → ⟪ (Toff203 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ Toff203 ∷ []) ⟫ʷ
lem-comm-TOFF203-CK41 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Toff203 ∷ CK41 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ CK32 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Toff204 ∷ []) (lem-comm-push-TOFF203-sw3-L c4) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (Toff304 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 10 3 (CK31 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CK32 ∷ Sw12 ∷ []) (sym (wl0094 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ CK32 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ CK31 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ [])
  b1 = at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 8 3 (CK42 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CK43 ∷ Sw23 ∷ []) (sym (wl0091 c4)) ▸
       at 6 2 (CK43 ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (CK₁₀)) ▸
       at 5 2 (CK42 ∷ Sw23 ∷ []) (sym (wl0090 c4)) ▸
       at 5 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 3 2 (CK31 ∷ Sw12 ∷ []) (sym (wl0095 c4)) ▸ done

  b2 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ CK31 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ []) (CK41 ∷ Toff203 ∷ [])
  b2 = at 3 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0003 c4) ▸
       at 3 9 (Toff304 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff204 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸
       at 4 2 (Sw34 ∷ Toff203 ∷ []) (lem-comm-push-TOFF204-sw3-L c4) ▸
       at 0 5 (CK41 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CCZ034 CX21: 15 steps
lem-comm-CCZ034-CX21 : WsL → ⟪ (CCZ034 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ CCZ034 ∷ []) ⟫ʷ
lem-comm-CCZ034-CX21 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ034 ∷ CX21 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CX43 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 8 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX32 ∷ Sw12 ∷ []) (sym (wl0060 c4)) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (CX42 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX43 ∷ Sw23 ∷ []) (sym (wl0059 c4)) ▸
       at 4 2 (CX43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CX₁₀)) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CX43 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (CX21 ∷ CCZ034 ∷ [])
  b1 = at 3 2 (CX42 ∷ Sw23 ∷ []) (sym (wl0058 c4)) ▸
       at 3 1 (Sw34 ∷ CX32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0004 c4) ▸
       at 1 2 (CX31 ∷ Sw12 ∷ []) (sym (wl0057 c4)) ▸
       at 1 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 1 9 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm SWAP12 BOX(3;40): 13 steps
lem-comm-SWAP12-BOX⟨3·40⟩ : WsL → ⟪ (Sw12 ∷ Bx3-40 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-40 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-SWAP12-BOX⟨3·40⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx3-40 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw13 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (Sw13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Sw23 ∷ []) (sym (wl0075 c4)) ▸
       at 3 2 (CZ01 ∷ Sw23 ∷ []) (sym (c₂ (CZ) (Swap))) ▸
       at 4 2 (Sw12 ∷ Sw13 ∷ []) (sym (wl0096 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw13 ∷ Sw23 ∷ Sw34 ∷ []) (Bx3-40 ∷ Sw12 ∷ [])
  b1 = at 5 1 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 0 7 (CZ04 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Bx3-40 ∷ []) (refl) ▸ done


-- comm CX14 TOFF302: 7 steps
lem-comm-CX14-TOFF302 : WsL → ⟪ (CX14 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CX14 ∷ []) ⟫ʷ
lem-comm-CX14-TOFF302 c4 = run b0
  where
  b0 : Chain (CX14 ∷ Toff302 ∷ []) (Toff302 ∷ CX14 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CX24 ∷ []) (wl0050 c4) ▸
       at 1 2 (Sw23 ∷ CX34 ∷ []) (wl0020 c4) ▸
       at 2 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 3 2 (Sw23 ∷ CX24 ∷ []) (wl0021 c4) ▸
       at 4 2 (Sw12 ∷ CX14 ∷ []) (wl0051 c4) ▸
       at 0 5 (Toff302 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF024 CS13: 11 steps
lem-comm-TOFF024-CS13 : WsL → ⟪ (Toff024 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff024 ∷ []) ⟫ʷ
lem-comm-TOFF024-CS13 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff024 ∷ CS13 ∷ []) (Sw12 ∷ Sw34 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS23 ∷ Sw12 ∷ []) (sym (wl0047 c4)) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 c4)) ▸
       at 3 2 (CS34 ∷ Toff012 ∷ []) (c₃ (Toff) (CS)) ▸
       at 2 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 2 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (CS13 ∷ Toff024 ∷ [])
  b1 = at 1 2 [] (wl0004 c4) ▸
       at 0 2 (CS13 ∷ Sw12 ∷ []) (sym (wl0046 c4)) ▸
       at 1 7 (Toff024 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp SWAP03 at 2: 4 steps
lem-resp-SWAP03-at-2 : WsL → ⟪ (Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Sw13 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-SWAP03-at-2 c4 = run b0
  where
  b0 : Chain (Sw03 ∷ []) (Sw12 ∷ Sw01 ∷ Sw13 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ Sw03 ∷ []) (wl0097 c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ Sw13 ∷ []) (sym (wl0098 c4)) ▸ done


-- resp SWAP03 at 1: 2 steps
lem-resp-SWAP03-at-1 : WsL → ⟪ (Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Sw13 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-SWAP03-at-1 c4 = run b0
  where
  b0 : Chain (Sw03 ∷ []) (Sw01 ∷ Sw13 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ Sw13 ∷ []) (sym (wl0098 c4)) ▸ done


-- comm CCZ134 CX02: 23 steps
lem-comm-CCZ134-CX02 : WsL → ⟪ (CCZ134 ∷ CX02 ∷ []) ⟫ʷ ≈ ⟪ (CX02 ∷ CCZ134 ∷ []) ⟫ʷ
lem-comm-CCZ134-CX02 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CCZ134 ∷ CX02 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ CCZ124 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ CCZ124 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ CCZ234 ∷ []) (wl0037 c4) ▸
       at 5 2 (CX01 ∷ CCZ234 ∷ []) (sym (c₂ (CX₀₁) (CCZ))) ▸
       at 6 2 (Sw12 ∷ CCZ134 ∷ []) (wl0044 c4) ▸
       at 7 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 8 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (CX02 ∷ CCZ134 ∷ [])
  b2 = at 10 2 [] (wl0004 c4) ▸
       at 2 7 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0004 c4) ▸
       at 1 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 1 5 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push TOFF302 sw3 L: 76 steps
lem-comm-push-TOFF302-sw3-L : WsL → ⟪ (Toff302 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ Toff402 ∷ []) ⟫ʷ
lem-comm-push-TOFF302-sw3-L c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (run b9)))))))))
  where
  b0 : Chain (Toff302 ∷ Sw34 ∷ []) (Sw12 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Toff301 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K3 ∷ Sw23 ∷ []) (sym (wl0064 c4)) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸ done

  b1 : Chain (Sw12 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ []) (K3 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw12 ∷ Sw34 ∷ [])
  b1 = at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K3 ∷ Sw23 ∷ []) (sym (wl0064 c4)) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 0 2 (K3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K)) ▸ done

  b2 : Chain (K3 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw12 ∷ Sw34 ∷ []) (K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K3 ∷ Sw12 ∷ ι ∷ Sw12 ∷ Sw34 ∷ [])
  b2 = at 1 2 (CS23 ∷ Sw12 ∷ []) (sym (wl0047 c4)) ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw12 ∷ []) (sym (wl0029 c4)) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 6 2 (K3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K)) ▸ done

  b3 : Chain (K3 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K3 ∷ Sw12 ∷ ι ∷ Sw12 ∷ Sw34 ∷ []) (K3 ∷ CS23 ∷ CX02 ∷ Sw34 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ [])
  b3 = at 7 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 8 2 [] (wl0006 c4) ▸
       at 7 2 (Sw34 ∷ ι ∷ []) (c₁ (iI) (Swap ↑ ↑)) ▸
       at 6 2 (Sw34 ∷ K4 ∷ []) (wl0066 c4) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸ done

  b4 : Chain (K3 ∷ CS23 ∷ CX02 ∷ Sw34 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ []) (Sw34 ∷ Sw12 ∷ K4 ∷ CS14 ∷ Sw12 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ [])
  b4 = at 4 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ K4 ∷ []) (wl0066 c4) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 3 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 c4)) ▸ done

  b5 : Chain (Sw34 ∷ Sw12 ∷ K4 ∷ CS14 ∷ Sw12 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ []) (Sw34 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ [])
  b5 = at 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0006 c4) ▸
       at 5 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0014 c4)) ▸
       at 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 7 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 8 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸ done

  b6 : Chain (Sw34 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ []) (Sw34 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw34 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ [])
  b6 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 2 (K3 ∷ Sw34 ∷ []) (sym (wl0066 c4)) ▸
       at 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b7 : Chain (Sw34 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw34 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ []) (Sw34 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ [])
  b7 = at 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 9 2 (K3 ∷ Sw34 ∷ []) (sym (wl0066 c4)) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 2 (K2 ∷ Sw23 ∷ []) (sym (wl0067 c4)) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸ done

  b8 : Chain (Sw34 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ []) (Sw34 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ [])
  b8 = at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 10 2 (K2 ∷ Sw23 ∷ []) (sym (wl0067 c4)) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b9 : Chain (Sw34 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (Sw34 ∷ Toff402 ∷ [])
  b9 = at 4 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff301 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff401 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff402 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push TOFF402 sw3 L: 76 steps
lem-comm-push-TOFF402-sw3-L : WsL → ⟪ (Toff402 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ Toff302 ∷ []) ⟫ʷ
lem-comm-push-TOFF402-sw3-L c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (run b9)))))))))
  where
  b0 : Chain (Toff402 ∷ Sw34 ∷ []) (Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K3 ∷ Sw23 ∷ []) (sym (wl0064 c4)) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b1 = at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K3 ∷ Sw23 ∷ []) (sym (wl0064 c4)) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 10 2 [] (wl0003 c4) ▸ done

  b2 : Chain (Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw34 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b2 = at 1 2 (K4 ∷ Sw34 ∷ []) (sym (wl0065 c4)) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸ done

  b3 : Chain (Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw34 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (K4 ∷ CS24 ∷ CX02 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw34 ∷ [])
  b3 = at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K4 ∷ Sw34 ∷ []) (sym (wl0065 c4)) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 9 2 [] (wl0004 c4) ▸
       at 0 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 1 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0005 c4)) ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (K4 ∷ CS24 ∷ CX02 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw34 ∷ []) (K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ Sw34 ∷ ι ∷ [])
  b4 = at 3 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0007 c4)) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 6 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 7 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 8 2 [] (wl0006 c4) ▸
       at 7 2 (Sw34 ∷ ι ∷ []) (c₁ (iI) (Swap ↑ ↑)) ▸ done

  b5 : Chain (K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ Sw34 ∷ ι ∷ []) (K4 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ Sw34 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K3 ∷ ι ∷ [])
  b5 = at 6 2 (Sw34 ∷ K3 ∷ []) (wl0065 c4) ▸
       at 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0004 c4) ▸
       at 4 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸
       at 3 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 2 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸
       at 1 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (K4 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ Sw34 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K3 ∷ ι ∷ []) (Sw34 ∷ Sw12 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw12 ∷ CX02 ∷ CS03 ∷ K3 ∷ ι ∷ [])
  b6 = at 3 2 [] (wl0004 c4) ▸
       at 0 2 (Sw34 ∷ K3 ∷ []) (wl0065 c4) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 2 (K3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K)) ▸
       at 3 2 (CS13 ∷ Sw12 ∷ []) (sym (wl0046 c4)) ▸
       at 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0006 c4) ▸
       at 5 2 (CS13⁻ ∷ Sw12 ∷ []) (sym (wl0028 c4)) ▸ done

  b7 : Chain (Sw34 ∷ Sw12 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw12 ∷ CX02 ∷ CS03 ∷ K3 ∷ ι ∷ []) (Sw34 ∷ Sw12 ∷ Sw23 ∷ K2 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw12 ∷ [])
  b7 = at 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 7 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 8 2 (K3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K)) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 2 (K2 ∷ Sw23 ∷ []) (sym (wl0067 c4)) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (Sw34 ∷ Sw12 ∷ Sw23 ∷ K2 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw12 ∷ []) (Sw34 ∷ Sw12 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ Sw23 ∷ ι ∷ Sw12 ∷ [])
  b8 = at 4 2 [] (wl0003 c4) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0003 c4) ▸
       at 9 2 (K2 ∷ Sw23 ∷ []) (sym (wl0067 c4)) ▸ done

  b9 : Chain (Sw34 ∷ Sw12 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ Sw23 ∷ ι ∷ Sw12 ∷ []) (Sw34 ∷ Toff302 ∷ [])
  b9 = at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 3 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff301 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff302 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF302 CX14: 23 steps
lem-comm-TOFF302-CX14 : WsL → ⟪ (Toff302 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ Toff302 ∷ []) ⟫ʷ
lem-comm-TOFF302-CX14 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Toff302 ∷ CX14 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ CX23 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Toff402 ∷ []) (lem-comm-push-TOFF302-sw3-L c4) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (Toff403 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 10 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX23 ∷ Sw12 ∷ []) (sym (wl0022 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ CX23 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ CX13 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ [])
  b1 = at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 8 3 (CX24 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX34 ∷ Sw23 ∷ []) (sym (wl0021 c4)) ▸
       at 6 2 (CX34 ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CX₀₁)) ▸
       at 5 2 (CX24 ∷ Sw23 ∷ []) (sym (wl0020 c4)) ▸
       at 5 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 3 2 (CX13 ∷ Sw12 ∷ []) (sym (wl0019 c4)) ▸ done

  b2 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ CX13 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ []) (CX14 ∷ Toff302 ∷ [])
  b2 = at 3 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0003 c4) ▸
       at 3 9 (Toff403 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff402 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸
       at 4 2 (Sw34 ∷ Toff302 ∷ []) (lem-comm-push-TOFF402-sw3-L c4) ▸
       at 0 5 (CX14 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF304 CX12: 15 steps
lem-comm-TOFF304-CX12 : WsL → ⟪ (Toff304 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ Toff304 ∷ []) ⟫ʷ
lem-comm-TOFF304-CX12 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff304 ∷ CX12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CX34 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 8 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX23 ∷ Sw12 ∷ []) (sym (wl0022 c4)) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (CX24 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX34 ∷ Sw23 ∷ []) (sym (wl0021 c4)) ▸
       at 4 2 (CX34 ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (CX₀₁)) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CX34 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (CX12 ∷ Toff304 ∷ [])
  b1 = at 3 2 (CX24 ∷ Sw23 ∷ []) (sym (wl0020 c4)) ▸
       at 3 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0004 c4) ▸
       at 1 2 (CX13 ∷ Sw12 ∷ []) (sym (wl0019 c4)) ▸
       at 1 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 1 9 (Toff304 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CCZ123 CX04: 13 steps
lem-comm-CCZ123-CX04 : WsL → ⟪ (CCZ123 ∷ CX04 ∷ []) ⟫ʷ ≈ ⟪ (CX04 ∷ CCZ123 ∷ []) ⟫ʷ
lem-comm-CCZ123-CX04 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ123 ∷ CX04 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CCZ134 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ CCZ234 ∷ []) (wl0037 c4) ▸
       at 3 2 (CX01 ∷ CCZ234 ∷ []) (sym (c₂ (CX₀₁) (CCZ))) ▸
       at 4 2 (Sw12 ∷ CCZ134 ∷ []) (wl0044 c4) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CCZ134 ∷ Sw23 ∷ Sw34 ∷ []) (CX04 ∷ CCZ123 ∷ [])
  b1 = at 5 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 6 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 0 7 (CX04 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF302 CS14: 23 steps
lem-comm-TOFF302-CS14 : WsL → ⟪ (Toff302 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Toff302 ∷ []) ⟫ʷ
lem-comm-TOFF302-CS14 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Toff302 ∷ CS14 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Toff402 ∷ []) (lem-comm-push-TOFF302-sw3-L c4) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (Toff403 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 10 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CS23 ∷ Sw12 ∷ []) (sym (wl0047 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ [])
  b1 = at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 8 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 c4)) ▸
       at 6 2 (CS34 ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CS)) ▸
       at 5 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 3 2 (CS13 ∷ Sw12 ∷ []) (sym (wl0046 c4)) ▸ done

  b2 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ CS13 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ []) (CS14 ∷ Toff302 ∷ [])
  b2 = at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0003 c4) ▸
       at 3 9 (Toff403 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff402 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸
       at 4 2 (Sw34 ∷ Toff302 ∷ []) (lem-comm-push-TOFF402-sw3-L c4) ▸
       at 0 5 (CS14 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF302 CSd14: 23 steps
lem-comm-TOFF302-CSd14 : WsL → ⟪ (Toff302 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Toff302 ∷ []) ⟫ʷ
lem-comm-TOFF302-CSd14 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Toff302 ∷ CS14⁻ ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ CS23⁻ ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Toff402 ∷ []) (lem-comm-push-TOFF302-sw3-L c4) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (Toff403 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 10 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CS23⁻ ∷ Sw12 ∷ []) (sym (wl0029 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ CS23⁻ ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ CS13⁻ ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ [])
  b1 = at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 8 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 6 2 (CS34⁻ ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CS • CS • CS)) ▸
       at 5 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 5 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 3 2 (CS13⁻ ∷ Sw12 ∷ []) (sym (wl0028 c4)) ▸ done

  b2 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ CS13⁻ ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ []) (CS14⁻ ∷ Toff302 ∷ [])
  b2 = at 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0003 c4) ▸
       at 3 9 (Toff403 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff402 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸
       at 4 2 (Sw34 ∷ Toff302 ∷ []) (lem-comm-push-TOFF402-sw3-L c4) ▸
       at 0 5 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CCZ134 CSd02: 23 steps
lem-comm-CCZ134-CSd02 : WsL → ⟪ (CCZ134 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CCZ134 ∷ []) ⟫ʷ
lem-comm-CCZ134-CSd02 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CCZ134 ∷ CS02⁻ ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ CCZ124 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ CCZ124 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ CCZ234 ∷ []) (wl0037 c4) ▸
       at 5 2 (CS01⁻ ∷ CCZ234 ∷ []) (sym (c₂ (CS • CS • CS) (CCZ))) ▸
       at 6 2 (Sw12 ∷ CCZ134 ∷ []) (wl0044 c4) ▸
       at 7 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 8 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (CS02⁻ ∷ CCZ134 ∷ [])
  b2 = at 10 2 [] (wl0004 c4) ▸
       at 2 7 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0004 c4) ▸
       at 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 1 5 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CCZ023 CX14: 23 steps
lem-comm-CCZ023-CX14 : WsL → ⟪ (CCZ023 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (CX14 ∷ CCZ023 ∷ []) ⟫ʷ
lem-comm-CCZ023-CX14 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CCZ023 ∷ CX14 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ CX23 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ CCZ024 ∷ []) (lem-comm-push-CCZ023-sw3-L c4) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 10 3 (CX13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX23 ∷ Sw12 ∷ []) (sym (wl0022 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ CX23 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ CX13 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ [])
  b1 = at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 8 3 (CX24 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX34 ∷ Sw23 ∷ []) (sym (wl0021 c4)) ▸
       at 6 2 (CX34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CX₀₁)) ▸
       at 5 2 (CX24 ∷ Sw23 ∷ []) (sym (wl0020 c4)) ▸
       at 5 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 3 2 (CX13 ∷ Sw12 ∷ []) (sym (wl0019 c4)) ▸ done

  b2 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ CX13 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ []) (CX14 ∷ CCZ023 ∷ [])
  b2 = at 3 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0003 c4) ▸
       at 3 9 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸
       at 4 2 (Sw34 ∷ CCZ023 ∷ []) (lem-comm-push-CCZ024-sw3-L c4) ▸
       at 0 5 (CX14 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CZ02 CCZ134: 23 steps
lem-comm-CZ02-CCZ134 : WsL → ⟪ (CZ02 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CZ02 ∷ []) ⟫ʷ
lem-comm-CZ02-CCZ134 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CZ02 ∷ CCZ134 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ CCZ124 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CZ03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CZ04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 8 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ CCZ124 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 c4)) ▸
       at 5 2 (CCZ234 ∷ CZ01 ∷ []) (c₂ (CZ) (CCZ)) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 4 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸
       at 3 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (CCZ134 ∷ CZ02 ∷ [])
  b2 = at 2 2 [] (wl0004 c4) ▸
       at 3 7 (CZ04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CZ03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 4 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 0 5 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CS14 TOFF302: 7 steps
lem-comm-CS14-TOFF302 : WsL → ⟪ (CS14 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CS14 ∷ []) ⟫ʷ
lem-comm-CS14-TOFF302 c4 = run b0
  where
  b0 : Chain (CS14 ∷ Toff302 ∷ []) (Toff302 ∷ CS14 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CS24 ∷ []) (wl0013 c4) ▸
       at 1 2 (Sw23 ∷ CS34 ∷ []) (wl0011 c4) ▸
       at 2 2 (Toff201 ∷ CS34 ∷ []) (sym (c₃ (Toffᵗ) (CS))) ▸
       at 3 2 (Sw23 ∷ CS24 ∷ []) (wl0008 c4) ▸
       at 4 2 (Sw12 ∷ CS14 ∷ []) (wl0005 c4) ▸
       at 0 5 (Toff302 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CK41 at 3: 6 steps
lem-resp-CK41-at-3 : WsL → ⟪ (CK41 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CK42 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CK41-at-3 c4 = run b0
  where
  b0 : Chain (CK41 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CK42 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 2 (Sw23 ∷ CK41 ∷ []) (wl0099 c4) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (Sw12 ∷ CK42 ∷ []) (wl0087 c4) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ CK42 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑))) ▸ done


-- comm TOFF302 CK41: 23 steps
lem-comm-TOFF302-CK41 : WsL → ⟪ (Toff302 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ Toff302 ∷ []) ⟫ʷ
lem-comm-TOFF302-CK41 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Toff302 ∷ CK41 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ CK32 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Toff402 ∷ []) (lem-comm-push-TOFF302-sw3-L c4) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (Toff403 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 10 3 (CK31 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CK32 ∷ Sw12 ∷ []) (sym (wl0094 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ CK32 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ CK31 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ [])
  b1 = at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 8 3 (CK42 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CK43 ∷ Sw23 ∷ []) (sym (wl0091 c4)) ▸
       at 6 2 (CK43 ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CK₁₀)) ▸
       at 5 2 (CK42 ∷ Sw23 ∷ []) (sym (wl0090 c4)) ▸
       at 5 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 3 2 (CK31 ∷ Sw12 ∷ []) (sym (wl0095 c4)) ▸ done

  b2 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ CK31 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ []) (CK41 ∷ Toff302 ∷ [])
  b2 = at 3 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0003 c4) ▸
       at 3 9 (Toff403 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff402 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸
       at 4 2 (Sw34 ∷ Toff302 ∷ []) (lem-comm-push-TOFF402-sw3-L c4) ▸
       at 0 5 (CK41 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm SWAP14 BOX(3;02): 7 steps
lem-comm-SWAP14-BOX⟨3·02⟩ : WsL → ⟪ (Sw14 ∷ Bx3-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-02 ∷ Sw14 ∷ []) ⟫ʷ
lem-comm-SWAP14-BOX⟨3·02⟩ c4 = run b0
  where
  b0 : Chain (Sw14 ∷ Bx3-02 ∷ []) (Bx3-02 ∷ Sw14 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 1 1 (Sw12 ∷ CZ01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ Sw24 ∷ []) (sym (wl0072 c4)) ▸
       at 1 2 (CZ01 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸
       at 2 2 (Sw12 ∷ Sw14 ∷ []) (sym (wl0093 c4)) ▸
       at 0 3 (CZ02 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Bx3-02 ∷ []) (refl) ▸ done


-- resp CK42 at 3: 6 steps
lem-resp-CK42-at-3 : WsL → ⟪ (CK42 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CK43 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CK42-at-3 c4 = run b0
  where
  b0 : Chain (CK42 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CK43 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 2 (Sw23 ∷ CK43 ∷ []) (wl0090 c4) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (Sw12 ∷ CK43 ∷ []) (sym (c₃ (Swap ↑) (CK₁₀))) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ CK43 ∷ []) (sym (c₂ (Swap) (CK₁₀ ↑))) ▸ done


-- comm TOFF301 CK42: 15 steps
lem-comm-TOFF301-CK42 : WsL → ⟪ (Toff301 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ Toff301 ∷ []) ⟫ʷ
lem-comm-TOFF301-CK42 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff301 ∷ CK42 ∷ []) (Sw34 ∷ Sw34 ∷ Sw23 ∷ CK43 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (Toff401 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw34 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CK42 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CK43 ∷ Sw23 ∷ []) (sym (wl0091 c4)) ▸
       at 3 2 (CK43 ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CK₁₀)) ▸ done

  b1 : Chain (Sw34 ∷ Sw34 ∷ Sw23 ∷ CK43 ∷ Toff201 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ []) (CK42 ∷ Toff301 ∷ [])
  b1 = at 2 2 (CK42 ∷ Sw23 ∷ []) (sym (wl0090 c4)) ▸
       at 2 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0004 c4) ▸
       at 2 5 (Toff401 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 0 3 (CK42 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CX20 CCZ134: 23 steps
lem-comm-CX20-CCZ134 : WsL → ⟪ (CX20 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CX20 ∷ []) ⟫ʷ
lem-comm-CX20-CCZ134 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX20 ∷ CCZ134 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CCZ124 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CX40 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 8 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ CCZ124 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 c4)) ▸
       at 5 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 4 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸
       at 3 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (CCZ134 ∷ CX20 ∷ [])
  b2 = at 2 2 [] (wl0004 c4) ▸
       at 3 7 (CX40 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 0 5 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push SWAP04 sw0 L: 5 steps
lem-comm-push-SWAP04-sw0-L : WsL → ⟪ (Sw04 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Sw14 ∷ []) ⟫ʷ
lem-comm-push-SWAP04-sw0-L c4 = run b0
  where
  b0 : Chain (Sw04 ∷ Sw01 ∷ []) (Sw01 ∷ Sw14 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 2 (Sw01 ∷ Sw13 ∷ []) (sym (wl0098 c4)) ▸
       at 0 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 3 (Sw14 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp SWAP04 at 1: 2 steps
lem-resp-SWAP04-at-1 : WsL → ⟪ (Sw04 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Sw14 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-SWAP04-at-1 c4 = run b0
  where
  b0 : Chain (Sw04 ∷ []) (Sw01 ∷ Sw14 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ Sw14 ∷ []) (lem-comm-push-SWAP04-sw0-L c4) ▸ done


-- comm push CX04 sw2 L: 7 steps
lem-comm-push-CX04-sw2-L : WsL → ⟪ (CX04 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CX04 ∷ []) ⟫ʷ
lem-comm-push-CX04-sw2-L c4 = run b0
  where
  b0 : Chain (CX04 ∷ Sw23 ∷ []) (Sw23 ∷ CX04 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0002 c4) ▸
       at 4 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 3 2 (Sw34 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap ↑)) ▸
       at 2 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 0 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0002 c4)) ▸
       at 1 7 (CX04 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CX04 at 3: 6 steps
lem-resp-CX04-at-3 : WsL → ⟪ (CX04 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX14 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CX04-at-3 c4 = run b0
  where
  b0 : Chain (CX04 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX14 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 2 (Sw23 ∷ CX04 ∷ []) (lem-comm-push-CX04-sw2-L c4) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (Sw12 ∷ CX04 ∷ []) (lem-comm-push-CX04-sw1-L c4) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ CX14 ∷ []) (lem-comm-push-CX04-sw0-L c4) ▸ done


-- comm SWAP04 BOX(3;21): 13 steps
lem-comm-SWAP04-BOX⟨3·21⟩ : WsL → ⟪ (Sw04 ∷ Bx3-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-21 ∷ Sw04 ∷ []) ⟫ʷ
lem-comm-SWAP04-BOX⟨3·21⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw04 ∷ Bx3-21 ∷ []) (Sw34 ∷ Sw23 ∷ CZ13 ∷ Sw12 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CZ12 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CZ23 ∷ Sw12 ∷ []) (sym (wl0036 c4)) ▸
       at 3 2 (CZ23 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ)) ▸
       at 2 2 (CZ13 ∷ Sw12 ∷ []) (sym (wl0033 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ CZ13 ∷ Sw12 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Bx3-21 ∷ Sw04 ∷ [])
  b1 = at 2 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0003 c4) ▸
       at 0 2 (CZ12 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 1 7 (Sw04 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Bx3-21 ∷ []) (refl) ▸ done


-- comm CCZ134 CX20: 23 steps
lem-comm-CCZ134-CX20 : WsL → ⟪ (CCZ134 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ CCZ134 ∷ []) ⟫ʷ
lem-comm-CCZ134-CX20 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CCZ134 ∷ CX20 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ CCZ124 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CX40 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ CCZ124 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ CCZ234 ∷ []) (wl0037 c4) ▸
       at 5 2 (CX10 ∷ CCZ234 ∷ []) (sym (c₂ (CX₁₀) (CCZ))) ▸
       at 6 2 (Sw12 ∷ CCZ134 ∷ []) (wl0044 c4) ▸
       at 7 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 8 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (CX20 ∷ CCZ134 ∷ [])
  b2 = at 10 2 [] (wl0004 c4) ▸
       at 2 7 (CX40 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0004 c4) ▸
       at 1 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 1 5 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF312 CK40: 13 steps
lem-comm-TOFF312-CK40 : WsL → ⟪ (Toff312 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ Toff312 ∷ []) ⟫ʷ
lem-comm-TOFF312-CK40 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff312 ∷ CK40 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Toff413 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Toff423 ∷ []) (sym (wl0085 c4)) ▸
       at 3 2 (CK10 ∷ Toff423 ∷ []) (sym (c₂ (CK₁₀) (Toffᵗ))) ▸
       at 4 2 (Sw12 ∷ Toff413 ∷ []) (sym (wl0084 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Toff413 ∷ Sw23 ∷ Sw34 ∷ []) (CK40 ∷ Toff312 ∷ [])
  b1 = at 5 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 6 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 0 7 (CK40 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CCZ034 CSd12: 15 steps
lem-comm-CCZ034-CSd12 : WsL → ⟪ (CCZ034 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CCZ034 ∷ []) ⟫ʷ
lem-comm-CCZ034-CSd12 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ034 ∷ CS12⁻ ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS34⁻ ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CS23⁻ ∷ Sw12 ∷ []) (sym (wl0029 c4)) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 4 2 (CS34⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS • CS • CS)) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS34⁻ ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (CS12⁻ ∷ CCZ034 ∷ [])
  b1 = at 3 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 3 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0004 c4) ▸
       at 1 2 (CS13⁻ ∷ Sw12 ∷ []) (sym (wl0028 c4)) ▸
       at 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 1 9 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CCZ014 CS23: 9 steps
lem-comm-CCZ014-CS23 : WsL → ⟪ (CCZ014 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CCZ014 ∷ []) ⟫ʷ
lem-comm-CCZ014-CS23 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ014 ∷ CS23 ∷ []) (CS23 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 c4)) ▸
       at 2 2 (CS34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS)) ▸
       at 1 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 1 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0004 c4) ▸ done

  b1 : Chain (CS23 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) (CS23 ∷ CCZ014 ∷ [])
  b1 = at 1 5 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CCZ014 CSd23: 9 steps
lem-comm-CCZ014-CSd23 : WsL → ⟪ (CCZ014 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CCZ014 ∷ []) ⟫ʷ
lem-comm-CCZ014-CSd23 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ014 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 2 2 (CS34⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS • CS • CS)) ▸
       at 1 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 1 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0004 c4) ▸ done

  b1 : Chain (CS23⁻ ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) (CS23⁻ ∷ CCZ014 ∷ [])
  b1 = at 1 5 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF314 CX02: 23 steps
lem-comm-TOFF314-CX02 : WsL → ⟪ (Toff314 ∷ CX02 ∷ []) ⟫ʷ ≈ ⟪ (CX02 ∷ Toff314 ∷ []) ⟫ʷ
lem-comm-TOFF314-CX02 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Toff314 ∷ CX02 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Toff214 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Toff214 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ Toff324 ∷ []) (sym (wl0038 c4)) ▸
       at 5 2 (CX01 ∷ Toff324 ∷ []) (sym (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 6 2 (Sw12 ∷ Toff314 ∷ []) (sym (wl0045 c4)) ▸
       at 7 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 8 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (CX02 ∷ Toff314 ∷ [])
  b2 = at 10 2 [] (wl0004 c4) ▸
       at 2 7 (CX04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0004 c4) ▸
       at 1 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 1 5 (Toff314 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp SWAP02 at 1: 2 steps
lem-resp-SWAP02-at-1 : WsL → ⟪ (Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Sw12 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-SWAP02-at-1 c4 = run b0
  where
  b0 : Chain (Sw02 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ Sw12 ∷ []) (sym (wl0100 c4)) ▸ done


-- comm SWAP02 BOX(3;41): 11 steps
lem-comm-SWAP02-BOX⟨3·41⟩ : WsL → ⟪ (Sw02 ∷ Bx3-41 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-41 ∷ Sw02 ∷ []) ⟫ʷ
lem-comm-SWAP02-BOX⟨3·41⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw02 ∷ Bx3-41 ∷ []) (Sw34 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw02 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 1 1 (Sw34 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Sw02 ∷ []) (c₃ (Swap ↑ • Swap • Swap ↑) (Swap)) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (Sw03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CZ12 ∷ Sw03 ∷ []) (sym (wl0086 c4)) ▸
       at 3 1 (Sw23 ∷ Sw02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw02 ∷ Sw34 ∷ []) (Bx3-41 ∷ Sw02 ∷ [])
  b1 = at 4 2 (Sw34 ∷ Sw02 ∷ []) (c₃ (Swap ↑ • Swap • Swap ↑) (Swap)) ▸
       at 0 5 (CZ14 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Bx3-41 ∷ []) (refl) ▸ done


-- comm CX31 TOFF204: 11 steps
lem-comm-CX31-TOFF204 : WsL → ⟪ (CX31 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CX31 ∷ []) ⟫ʷ
lem-comm-CX31-TOFF204 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX31 ∷ Toff204 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ CX32 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CX32 ∷ []) (wl0057 c4) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CX42 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ CX43 ∷ []) (wl0058 c4) ▸
       at 3 2 (Toff102 ∷ CX43 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (CX₁₀))) ▸
       at 4 2 (Sw23 ∷ CX42 ∷ []) (wl0059 c4) ▸
       at 5 1 (Sw34 ∷ CX32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ CX32 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ []) (Toff204 ∷ CX31 ∷ [])
  b1 = at 7 2 [] (wl0004 c4) ▸
       at 6 2 (Sw12 ∷ CX31 ∷ []) (wl0060 c4) ▸
       at 0 7 (Toff204 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm SWAP03 BOX(2;41): 21 steps
lem-comm-SWAP03-BOX⟨2·41⟩ : WsL → ⟪ (Sw03 ∷ Bx2-41 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-41 ∷ Sw03 ∷ []) ⟫ʷ
lem-comm-SWAP03-BOX⟨2·41⟩ c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw03 ∷ Bx2-41 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 1 1 (Sw34 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (Sw04 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ Sw04 ∷ []) (lem-comm-push-SWAP04-sw2-L c4) ▸
       at 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CZ12 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ CZ12 ∷ Sw04 ∷ Sw23 ∷ Sw34 ∷ [])
  b1 = at 7 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CZ23 ∷ Sw12 ∷ []) (sym (wl0036 c4)) ▸
       at 5 2 (CZ23 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ)) ▸
       at 4 2 (CZ13 ∷ Sw12 ∷ []) (sym (wl0033 c4)) ▸
       at 4 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸
       at 2 2 (CZ12 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 3 7 (Sw04 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw34 ∷ Sw23 ∷ CZ12 ∷ Sw04 ∷ Sw23 ∷ Sw34 ∷ []) (Bx2-41 ∷ Sw03 ∷ [])
  b2 = at 3 2 (Sw23 ∷ Sw04 ∷ []) (lem-comm-push-SWAP04-sw2-L c4) ▸
       at 4 1 (Sw34 ∷ Sw03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸
       at 0 5 (CZ14 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Bx2-41 ∷ []) (refl) ▸ done


-- comm CX24 TOFF301: 5 steps
lem-comm-CX24-TOFF301 : WsL → ⟪ (CX24 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CX24 ∷ []) ⟫ʷ
lem-comm-CX24-TOFF301 c4 = run b0
  where
  b0 : Chain (CX24 ∷ Toff301 ∷ []) (Toff301 ∷ CX24 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ CX34 ∷ []) (wl0020 c4) ▸
       at 1 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 2 2 (Sw23 ∷ CX24 ∷ []) (wl0021 c4) ▸
       at 0 3 (Toff301 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CX21 TOFF304: 15 steps
lem-comm-CX21-TOFF304 : WsL → ⟪ (CX21 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CX21 ∷ []) ⟫ʷ
lem-comm-CX21-TOFF304 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX21 ∷ Toff304 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ CX43 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CX32 ∷ []) (wl0057 c4) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CX42 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ CX43 ∷ []) (wl0058 c4) ▸
       at 4 2 (Toff102 ∷ CX43 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (CX₁₀))) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ CX43 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Toff304 ∷ CX21 ∷ [])
  b1 = at 5 2 (Sw23 ∷ CX42 ∷ []) (wl0059 c4) ▸
       at 6 1 (Sw34 ∷ CX32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 7 2 (Sw12 ∷ CX31 ∷ []) (wl0060 c4) ▸
       at 8 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (wl0003 c4) ▸
       at 0 9 (Toff304 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CX20 TOFF314: 23 steps
lem-comm-CX20-TOFF314 : WsL → ⟪ (CX20 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CX20 ∷ []) ⟫ʷ
lem-comm-CX20-TOFF314 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX20 ∷ Toff314 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Toff214 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CX30 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CX40 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 8 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Toff214 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Toff324 ∷ Sw12 ∷ []) (wl0045 c4) ▸
       at 5 2 (Toff324 ∷ CX10 ∷ []) (c₂ (CX₁₀) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 2 (Toff314 ∷ Sw12 ∷ []) (wl0038 c4) ▸
       at 4 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸
       at 3 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Toff314 ∷ CX20 ∷ [])
  b2 = at 2 2 [] (wl0004 c4) ▸
       at 3 7 (CX40 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 0 5 (Toff314 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CK40 TOFF312: 13 steps
lem-comm-CK40-TOFF312 : WsL → ⟪ (CK40 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CK40 ∷ []) ⟫ʷ
lem-comm-CK40-TOFF312 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CK40 ∷ Toff312 ∷ []) (Sw34 ∷ Sw23 ∷ Toff413 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Toff423 ∷ Sw12 ∷ []) (wl0084 c4) ▸
       at 3 2 (Toff423 ∷ CK10 ∷ []) (c₂ (CK₁₀) (Toffᵗ)) ▸
       at 2 2 (Toff413 ∷ Sw12 ∷ []) (wl0085 c4) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Toff413 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Toff312 ∷ CK40 ∷ [])
  b1 = at 2 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0003 c4) ▸
       at 1 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0004 c4) ▸
       at 1 7 (CK40 ∷ []) (by-assoc Eq.refl) ▸ done

