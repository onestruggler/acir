{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R004 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0002 ; wl0003 ; wl0004 ; wl0005 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0010 ; wl0011 ; wl0012 ; wl0013 ; wl0014 ; wl0016 ; wl0018 ; wl0019 ; wl0020 ; wl0021 ; wl0022 ; wl0028 ; wl0029 ; wl0032 ; wl0033 ; wl0034 ; wl0035 ; wl0036 ; wl0037 ; wl0038 ; wl0040 ; wl0044 ; wl0045 ; wl0046 ; wl0047 ; wl0053 ; wl0055 ; wl0056 ; wl0057 ; wl0058 ; wl0059 ; wl0060 ; wl0069 ; wl0072 ; wl0073 ; wl0074 ; wl0078 ; wl0080 ; wl0084 ; wl0085 ; wl0087 ; wl0089 ; wl0090 ; wl0091 ; wl0092 ; wl0093 ; wl0094 ; wl0095)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-push-CS04-sw1-R)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-push-TOFF023-sw3-L ; lem-comm-push-TOFF024-sw3-L)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-push-CK40-sw0-L ; lem-comm-push-CK40-sw1-L)
-- comm CS04 CCZ123: 13 steps
lem-comm-CS04-CCZ123 : WsL → ⟪ (CS04 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CS04 ∷ []) ⟫ʷ
lem-comm-CS04-CCZ123 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS04 ∷ CCZ123 ∷ []) (Sw34 ∷ Sw23 ∷ CCZ134 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 c4)) ▸
       at 3 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 2 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ CCZ134 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (CCZ123 ∷ CS04 ∷ [])
  b1 = at 2 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0003 c4) ▸
       at 1 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0004 c4) ▸
       at 1 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CK40 TOFF213: 13 steps
lem-comm-CK40-TOFF213 : WsL → ⟪ (CK40 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CK40 ∷ []) ⟫ʷ
lem-comm-CK40-TOFF213 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CK40 ∷ Toff213 ∷ []) (Sw34 ∷ Sw23 ∷ Toff314 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Toff324 ∷ Sw12 ∷ []) (wl0045 c4) ▸
       at 3 2 (Toff324 ∷ CK10 ∷ []) (c₂ (CK₁₀) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 2 (Toff314 ∷ Sw12 ∷ []) (wl0038 c4) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Toff314 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Toff213 ∷ CK40 ∷ [])
  b1 = at 2 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0003 c4) ▸
       at 1 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0004 c4) ▸
       at 1 7 (CK40 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push CK40 sw2 L: 7 steps
lem-comm-push-CK40-sw2-L : WsL → ⟪ (CK40 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CK40 ∷ []) ⟫ʷ
lem-comm-push-CK40-sw2-L c4 = run b0
  where
  b0 : Chain (CK40 ∷ Sw23 ∷ []) (Sw23 ∷ CK40 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0002 c4) ▸
       at 4 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 3 2 (Sw34 ∷ CK10 ∷ []) (c₂ (CK₁₀) (Swap ↑)) ▸
       at 2 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 0 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0002 c4)) ▸
       at 1 7 (CK40 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CK40 at 3: 6 steps
lem-resp-CK40-at-3 : WsL → ⟪ (CK40 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CK40-at-3 c4 = run b0
  where
  b0 : Chain (CK40 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 2 (Sw23 ∷ CK40 ∷ []) (lem-comm-push-CK40-sw2-L c4) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (Sw12 ∷ CK40 ∷ []) (lem-comm-push-CK40-sw1-L c4) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ CK41 ∷ []) (lem-comm-push-CK40-sw0-L c4) ▸ done


-- comm CSd13 TOFF204: 11 steps
lem-comm-CSd13-TOFF204 : WsL → ⟪ (CS13⁻ ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-comm-CSd13-TOFF204 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS13⁻ ∷ Toff204 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CS23⁻ ∷ []) (wl0028 c4) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ CS34⁻ ∷ []) (wl0012 c4) ▸
       at 3 2 (Toff102 ∷ CS34⁻ ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (CS • CS • CS))) ▸
       at 4 2 (Sw23 ∷ CS24⁻ ∷ []) (wl0009 c4) ▸
       at 5 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ []) (Toff204 ∷ CS13⁻ ∷ [])
  b1 = at 7 2 [] (wl0004 c4) ▸
       at 6 2 (Sw12 ∷ CS13⁻ ∷ []) (wl0029 c4) ▸
       at 0 7 (Toff204 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CS13 TOFF204: 11 steps
lem-comm-CS13-TOFF204 : WsL → ⟪ (CS13 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CS13 ∷ []) ⟫ʷ
lem-comm-CS13-TOFF204 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS13 ∷ Toff204 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CS23 ∷ []) (wl0046 c4) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ CS34 ∷ []) (wl0011 c4) ▸
       at 3 2 (Toff102 ∷ CS34 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (CS))) ▸
       at 4 2 (Sw23 ∷ CS24 ∷ []) (wl0008 c4) ▸
       at 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ []) (Toff204 ∷ CS13 ∷ [])
  b1 = at 7 2 [] (wl0004 c4) ▸
       at 6 2 (Sw12 ∷ CS13 ∷ []) (wl0047 c4) ▸
       at 0 7 (Toff204 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CX41 CCZ023: 7 steps
lem-comm-CX41-CCZ023 : WsL → ⟪ (CX41 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CX41 ∷ []) ⟫ʷ
lem-comm-CX41-CCZ023 c4 = run b0
  where
  b0 : Chain (CX41 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX41 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CX42 ∷ []) (wl0069 c4) ▸
       at 1 2 (Sw23 ∷ CX43 ∷ []) (wl0058 c4) ▸
       at 2 2 (CCZ012 ∷ CX43 ∷ []) (sym (c₃ (CCZ) (CX₁₀))) ▸
       at 3 2 (Sw23 ∷ CX42 ∷ []) (wl0059 c4) ▸
       at 4 2 (Sw12 ∷ CX41 ∷ []) (wl0089 c4) ▸
       at 0 5 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CZ03 TOFF214: 9 steps
lem-comm-CZ03-TOFF214 : WsL → ⟪ (CZ03 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CZ03 ∷ []) ⟫ʷ
lem-comm-CZ03-TOFF214 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ03 ∷ Toff214 ∷ []) (Toff214 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Toff324 ∷ Sw12 ∷ []) (wl0045 c4) ▸
       at 2 2 (Toff324 ∷ CZ01 ∷ []) (c₂ (CZ) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 1 2 (Toff314 ∷ Sw12 ∷ []) (wl0038 c4) ▸
       at 1 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸ done

  b1 : Chain (Toff214 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ []) (Toff214 ∷ CZ03 ∷ [])
  b1 = at 1 5 (CZ03 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF214 CSd03: 9 steps
lem-comm-TOFF214-CSd03 : WsL → ⟪ (Toff214 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Toff214 ∷ []) ⟫ʷ
lem-comm-TOFF214-CSd03 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff214 ∷ CS03⁻ ∷ []) (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Toff214 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ Toff324 ∷ []) (sym (wl0038 c4)) ▸
       at 2 2 (CS01⁻ ∷ Toff324 ∷ []) (sym (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 3 2 (Sw12 ∷ Toff314 ∷ []) (sym (wl0045 c4)) ▸
       at 4 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Toff214 ∷ []) (CS03⁻ ∷ Toff214 ∷ [])
  b1 = at 0 5 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CSd14 TOFF203: 7 steps
lem-comm-CSd14-TOFF203 : WsL → ⟪ (CS14⁻ ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CS14⁻ ∷ []) ⟫ʷ
lem-comm-CSd14-TOFF203 c4 = run b0
  where
  b0 : Chain (CS14⁻ ∷ Toff203 ∷ []) (Toff203 ∷ CS14⁻ ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CS24⁻ ∷ []) (wl0014 c4) ▸
       at 1 2 (Sw23 ∷ CS34⁻ ∷ []) (wl0012 c4) ▸
       at 2 2 (Toff102 ∷ CS34⁻ ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (CS • CS • CS))) ▸
       at 3 2 (Sw23 ∷ CS24⁻ ∷ []) (wl0009 c4) ▸
       at 4 2 (Sw12 ∷ CS14⁻ ∷ []) (wl0007 c4) ▸
       at 0 5 (Toff203 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CZ03 CCZ124: 9 steps
lem-comm-CZ03-CCZ124 : WsL → ⟪ (CZ03 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CZ03 ∷ []) ⟫ʷ
lem-comm-CZ03-CCZ124 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ03 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 c4)) ▸
       at 2 2 (CCZ234 ∷ CZ01 ∷ []) (c₂ (CZ) (CCZ)) ▸
       at 1 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 1 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸ done

  b1 : Chain (CCZ124 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ []) (CCZ124 ∷ CZ03 ∷ [])
  b1 = at 1 5 (CZ03 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CX03 CCZ124: 9 steps
lem-comm-CX03-CCZ124 : WsL → ⟪ (CX03 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CX03 ∷ []) ⟫ʷ
lem-comm-CX03-CCZ124 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX03 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 c4)) ▸
       at 2 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 1 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 1 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸ done

  b1 : Chain (CCZ124 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) (CCZ124 ∷ CX03 ∷ [])
  b1 = at 1 5 (CX03 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push TOFF203 sw3 L: 76 steps
lem-comm-push-TOFF203-sw3-L : WsL → ⟪ (Toff203 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ Toff204 ∷ []) ⟫ʷ
lem-comm-push-TOFF203-sw3-L c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (run b9)))))))))
  where
  b0 : Chain (Toff203 ∷ Sw34 ∷ []) (Sw12 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Toff103 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸ done

  b1 : Chain (Sw12 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ []) (K2 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw34 ∷ [])
  b1 = at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 0 2 (K2 ∷ Sw12 ∷ []) (sym (wl0040 c4)) ▸ done

  b2 : Chain (K2 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw34 ∷ []) (K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ Sw12 ∷ ι ∷ Sw12 ∷ Sw34 ∷ [])
  b2 = at 1 2 (CS23 ∷ Sw12 ∷ []) (sym (wl0047 c4)) ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw12 ∷ []) (sym (wl0029 c4)) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 6 2 (K2 ∷ Sw12 ∷ []) (sym (wl0040 c4)) ▸ done

  b3 : Chain (K2 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ Sw12 ∷ ι ∷ Sw12 ∷ Sw34 ∷ []) (K2 ∷ CS23 ∷ CX02 ∷ Sw34 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ [])
  b3 = at 7 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 8 2 [] (wl0006 c4) ▸
       at 7 2 (Sw34 ∷ ι ∷ []) (c₁ (iI) (Swap ↑ ↑)) ▸
       at 6 2 (Sw34 ∷ K2 ∷ []) (c₃ (K ↑ ↑) (Swap)) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸ done

  b4 : Chain (K2 ∷ CS23 ∷ CX02 ∷ Sw34 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ []) (Sw34 ∷ Sw12 ∷ K1 ∷ CS14 ∷ Sw12 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ [])
  b4 = at 4 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ K2 ∷ []) (c₃ (K ↑ ↑) (Swap)) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 2 (K1 ∷ Sw12 ∷ []) (sym (wl0073 c4)) ▸
       at 3 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 c4)) ▸ done

  b5 : Chain (Sw34 ∷ Sw12 ∷ K1 ∷ CS14 ∷ Sw12 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ []) (Sw34 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ [])
  b5 = at 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0006 c4) ▸
       at 5 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0014 c4)) ▸
       at 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 7 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 8 2 (K1 ∷ Sw12 ∷ []) (sym (wl0073 c4)) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸ done

  b6 : Chain (Sw34 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ []) (Sw34 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw34 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ [])
  b6 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b7 : Chain (Sw34 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw34 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ []) (Sw34 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ [])
  b7 = at 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 9 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸ done

  b8 : Chain (Sw34 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ []) (Sw34 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ [])
  b8 = at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 10 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b9 : Chain (Sw34 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (Sw34 ∷ Toff204 ∷ [])
  b9 = at 4 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff104 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff204 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push TOFF204 sw3 L: 76 steps
lem-comm-push-TOFF204-sw3-L : WsL → ⟪ (Toff204 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ Toff203 ∷ []) ⟫ʷ
lem-comm-push-TOFF204-sw3-L c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (run b9)))))))))
  where
  b0 : Chain (Toff204 ∷ Sw34 ∷ []) (Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b1 = at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 10 2 [] (wl0003 c4) ▸ done

  b2 : Chain (Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b2 = at 1 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸ done

  b3 : Chain (Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (K2 ∷ CS24 ∷ CX02 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw34 ∷ [])
  b3 = at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 9 2 [] (wl0004 c4) ▸
       at 0 2 (K2 ∷ Sw12 ∷ []) (sym (wl0040 c4)) ▸
       at 1 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0005 c4)) ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (K2 ∷ CS24 ∷ CX02 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw34 ∷ []) (K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ Sw34 ∷ ι ∷ [])
  b4 = at 3 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0007 c4)) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 6 2 (K2 ∷ Sw12 ∷ []) (sym (wl0040 c4)) ▸
       at 7 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 8 2 [] (wl0006 c4) ▸
       at 7 2 (Sw34 ∷ ι ∷ []) (c₁ (iI) (Swap ↑ ↑)) ▸ done

  b5 : Chain (K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ Sw34 ∷ ι ∷ []) (K2 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ Sw34 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ [])
  b5 = at 6 2 (Sw34 ∷ K2 ∷ []) (c₃ (K ↑ ↑) (Swap)) ▸
       at 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0004 c4) ▸
       at 4 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸
       at 3 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 2 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸
       at 1 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (K2 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ Sw34 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ []) (Sw34 ∷ Sw12 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw12 ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ [])
  b6 = at 3 2 [] (wl0004 c4) ▸
       at 0 2 (Sw34 ∷ K2 ∷ []) (c₃ (K ↑ ↑) (Swap)) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 2 (K1 ∷ Sw12 ∷ []) (sym (wl0073 c4)) ▸
       at 3 2 (CS13 ∷ Sw12 ∷ []) (sym (wl0046 c4)) ▸
       at 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0006 c4) ▸
       at 5 2 (CS13⁻ ∷ Sw12 ∷ []) (sym (wl0028 c4)) ▸ done

  b7 : Chain (Sw34 ∷ Sw12 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw12 ∷ CX02 ∷ CS03 ∷ K2 ∷ ι ∷ []) (Sw34 ∷ Sw12 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw12 ∷ [])
  b7 = at 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 7 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 8 2 (K1 ∷ Sw12 ∷ []) (sym (wl0073 c4)) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (Sw34 ∷ Sw12 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw12 ∷ []) (Sw34 ∷ Sw12 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw23 ∷ ι ∷ Sw12 ∷ [])
  b8 = at 4 2 [] (wl0003 c4) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0003 c4) ▸
       at 9 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸ done

  b9 : Chain (Sw34 ∷ Sw12 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw23 ∷ ι ∷ Sw12 ∷ []) (Sw34 ∷ Toff203 ∷ [])
  b9 = at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 3 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff203 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF203 CSd14: 23 steps
lem-comm-TOFF203-CSd14 : WsL → ⟪ (Toff203 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Toff203 ∷ []) ⟫ʷ
lem-comm-TOFF203-CSd14 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Toff203 ∷ CS14⁻ ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ CS23⁻ ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Toff204 ∷ []) (lem-comm-push-TOFF203-sw3-L c4) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (Toff304 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 10 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CS23⁻ ∷ Sw12 ∷ []) (sym (wl0029 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ CS23⁻ ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ CS13⁻ ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ [])
  b1 = at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 8 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 6 2 (CS34⁻ ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (CS • CS • CS)) ▸
       at 5 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 5 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 3 2 (CS13⁻ ∷ Sw12 ∷ []) (sym (wl0028 c4)) ▸ done

  b2 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ CS13⁻ ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ []) (CS14⁻ ∷ Toff203 ∷ [])
  b2 = at 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0003 c4) ▸
       at 3 9 (Toff304 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff204 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸
       at 4 2 (Sw34 ∷ Toff203 ∷ []) (lem-comm-push-TOFF204-sw3-L c4) ▸
       at 0 5 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CSd03 TOFF214: 9 steps
lem-comm-CSd03-TOFF214 : WsL → ⟪ (CS03⁻ ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-comm-CSd03-TOFF214 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03⁻ ∷ Toff214 ∷ []) (Toff214 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Toff324 ∷ Sw12 ∷ []) (wl0045 c4) ▸
       at 2 2 (Toff324 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 1 2 (Toff314 ∷ Sw12 ∷ []) (wl0038 c4) ▸
       at 1 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸ done

  b1 : Chain (Toff214 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (Toff214 ∷ CS03⁻ ∷ [])
  b1 = at 1 5 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CK41 CCZ023: 7 steps
lem-comm-CK41-CCZ023 : WsL → ⟪ (CK41 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CK41 ∷ []) ⟫ʷ
lem-comm-CK41-CCZ023 c4 = run b0
  where
  b0 : Chain (CK41 ∷ CCZ023 ∷ []) (CCZ023 ∷ CK41 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CK42 ∷ []) (wl0087 c4) ▸
       at 1 2 (Sw23 ∷ CK43 ∷ []) (wl0090 c4) ▸
       at 2 2 (CCZ012 ∷ CK43 ∷ []) (sym (c₃ (CCZ) (CK₁₀))) ▸
       at 3 2 (Sw23 ∷ CK42 ∷ []) (wl0091 c4) ▸
       at 4 2 (Sw12 ∷ CK41 ∷ []) (wl0092 c4) ▸
       at 0 5 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CK41 TOFF023: 7 steps
lem-comm-CK41-TOFF023 : WsL → ⟪ (CK41 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CK41 ∷ []) ⟫ʷ
lem-comm-CK41-TOFF023 c4 = run b0
  where
  b0 : Chain (CK41 ∷ Toff023 ∷ []) (Toff023 ∷ CK41 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CK42 ∷ []) (wl0087 c4) ▸
       at 1 2 (Sw23 ∷ CK43 ∷ []) (wl0090 c4) ▸
       at 2 2 (Toff012 ∷ CK43 ∷ []) (sym (c₃ (Toff) (CK₁₀))) ▸
       at 3 2 (Sw23 ∷ CK42 ∷ []) (wl0091 c4) ▸
       at 4 2 (Sw12 ∷ CK41 ∷ []) (wl0092 c4) ▸
       at 0 5 (Toff023 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CS23 TOFF014: 9 steps
lem-comm-CS23-TOFF014 : WsL → ⟪ (CS23 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CS23 ∷ []) ⟫ʷ
lem-comm-CS23-TOFF014 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS23 ∷ Toff014 ∷ []) (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ CS23 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ CS34 ∷ []) (wl0011 c4) ▸
       at 2 2 (Toff012 ∷ CS34 ∷ []) (sym (c₃ (Toff) (CS))) ▸
       at 3 2 (Sw23 ∷ CS24 ∷ []) (wl0008 c4) ▸
       at 4 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ CS23 ∷ []) (Toff014 ∷ CS23 ∷ [])
  b1 = at 0 5 (Toff014 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CZ13 TOFF024: 11 steps
lem-comm-CZ13-TOFF024 : WsL → ⟪ (CZ13 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CZ13 ∷ []) ⟫ʷ
lem-comm-CZ13-TOFF024 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ13 ∷ Toff024 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ CZ23 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CZ23 ∷ []) (wl0033 c4) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CZ24 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ CZ34 ∷ []) (wl0034 c4) ▸
       at 3 2 (Toff012 ∷ CZ34 ∷ []) (sym (c₃ (Toff) (CZ))) ▸
       at 4 2 (Sw23 ∷ CZ24 ∷ []) (wl0035 c4) ▸
       at 5 1 (Sw34 ∷ CZ23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ CZ23 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ []) (Toff024 ∷ CZ13 ∷ [])
  b1 = at 7 2 [] (wl0004 c4) ▸
       at 6 2 (Sw12 ∷ CZ13 ∷ []) (wl0036 c4) ▸
       at 0 7 (Toff024 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CK42 CCZ013: 5 steps
lem-comm-CK42-CCZ013 : WsL → ⟪ (CK42 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CK42 ∷ []) ⟫ʷ
lem-comm-CK42-CCZ013 c4 = run b0
  where
  b0 : Chain (CK42 ∷ CCZ013 ∷ []) (CCZ013 ∷ CK42 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ CK43 ∷ []) (wl0090 c4) ▸
       at 1 2 (CCZ012 ∷ CK43 ∷ []) (sym (c₃ (CCZ) (CK₁₀))) ▸
       at 2 2 (Sw23 ∷ CK42 ∷ []) (wl0091 c4) ▸
       at 0 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CK42 TOFF013: 5 steps
lem-comm-CK42-TOFF013 : WsL → ⟪ (CK42 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CK42 ∷ []) ⟫ʷ
lem-comm-CK42-TOFF013 c4 = run b0
  where
  b0 : Chain (CK42 ∷ Toff013 ∷ []) (Toff013 ∷ CK42 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ CK43 ∷ []) (wl0090 c4) ▸
       at 1 2 (Toff012 ∷ CK43 ∷ []) (sym (c₃ (Toff) (CK₁₀))) ▸
       at 2 2 (Sw23 ∷ CK42 ∷ []) (wl0091 c4) ▸
       at 0 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm SWAP14 BOX(2;03): 9 steps
lem-comm-SWAP14-BOX⟨2·03⟩ : WsL → ⟪ (Sw14 ∷ Bx2-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-03 ∷ Sw14 ∷ []) ⟫ʷ
lem-comm-SWAP14-BOX⟨2·03⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw14 ∷ Bx2-03 ∷ []) (CZ03 ∷ Sw14 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 1 1 (Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw14 ∷ []) (wl0074 c4) ▸
       at 1 2 (Sw12 ∷ Sw24 ∷ []) (sym (wl0072 c4)) ▸
       at 2 2 (CZ01 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸
       at 3 2 (Sw12 ∷ Sw14 ∷ []) (sym (wl0093 c4)) ▸
       at 4 2 (Sw23 ∷ Sw14 ∷ []) (wl0074 c4) ▸
       at 0 5 (CZ03 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CZ03 ∷ Sw14 ∷ []) (Bx2-03 ∷ Sw14 ∷ [])
  b1 = at 0 1 (Bx2-03 ∷ []) (refl) ▸ done


-- resp SWAP24 at 3: 6 steps
lem-resp-SWAP24-at-3 : WsL → ⟪ (Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw34 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-SWAP24-at-3 c4 = run b0
  where
  b0 : Chain (Sw24 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw34 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 2 (Sw23 ∷ Sw34 ∷ []) (sym (wl0055 c4)) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸ done


-- comm SWAP24 BOX(0;13): 7 steps
lem-comm-SWAP24-BOX⟨0·13⟩ : WsL → ⟪ (Sw24 ∷ Bx0-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-13 ∷ Sw24 ∷ []) ⟫ʷ
lem-comm-SWAP24-BOX⟨0·13⟩ c4 = run b0
  where
  b0 : Chain (Sw24 ∷ Bx0-13 ∷ []) (Bx0-13 ∷ Sw24 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 1 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw34 ∷ []) (sym (wl0055 c4)) ▸
       at 1 2 (CZ12 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 2 2 (Sw23 ∷ Sw24 ∷ []) (sym (wl0056 c4)) ▸
       at 0 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Bx0-13 ∷ []) (refl) ▸ done


-- comm SWAP23 BOX(0;41): 11 steps
lem-comm-SWAP23-BOX⟨0·41⟩ : WsL → ⟪ (Sw23 ∷ Bx0-41 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-41 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-SWAP23-BOX⟨0·41⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Bx0-41 ∷ []) (Sw34 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 1 1 (Sw34 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (Sw24 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ Sw34 ∷ []) (sym (wl0055 c4)) ▸
       at 2 2 (CZ12 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 3 2 (Sw23 ∷ Sw24 ∷ []) (sym (wl0056 c4)) ▸
       at 4 1 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ []) (Bx0-41 ∷ Sw23 ∷ [])
  b1 = at 6 2 [] (wl0004 c4) ▸
       at 0 5 (CZ14 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Bx0-41 ∷ []) (refl) ▸ done


-- comm TOFF213 CSd04: 13 steps
lem-comm-TOFF213-CSd04 : WsL → ⟪ (Toff213 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ Toff213 ∷ []) ⟫ʷ
lem-comm-TOFF213-CSd04 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff213 ∷ CS04⁻ ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Toff314 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Toff324 ∷ []) (sym (wl0038 c4)) ▸
       at 3 2 (CS01⁻ ∷ Toff324 ∷ []) (sym (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 4 2 (Sw12 ∷ Toff314 ∷ []) (sym (wl0045 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Toff314 ∷ Sw23 ∷ Sw34 ∷ []) (CS04⁻ ∷ Toff213 ∷ [])
  b1 = at 5 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 6 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 0 7 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF213 CK40: 13 steps
lem-comm-TOFF213-CK40 : WsL → ⟪ (Toff213 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ Toff213 ∷ []) ⟫ʷ
lem-comm-TOFF213-CK40 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff213 ∷ CK40 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Toff314 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Toff324 ∷ []) (sym (wl0038 c4)) ▸
       at 3 2 (CK10 ∷ Toff324 ∷ []) (sym (c₂ (CK₁₀) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 4 2 (Sw12 ∷ Toff314 ∷ []) (sym (wl0045 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Toff314 ∷ Sw23 ∷ Sw34 ∷ []) (CK40 ∷ Toff213 ∷ [])
  b1 = at 5 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 6 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 0 7 (CK40 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push CCZ023 sw3 L: 58 steps
lem-comm-push-CCZ023-sw3-L : WsL → ⟪ (CCZ023 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ CCZ024 ∷ []) ⟫ʷ
lem-comm-push-CCZ023-sw3-L c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (CCZ023 ∷ Sw34 ∷ []) (Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw12 ∷ CCZ013 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ []) (CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw12 ∷ CX01 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ [])
  b1 = at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 0 2 (CS23 ∷ Sw12 ∷ []) (sym (wl0047 c4)) ▸
       at 3 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS23⁻ ∷ Sw12 ∷ []) (sym (wl0029 c4)) ▸ done

  b2 : Chain (CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw12 ∷ CX01 ∷ CS03 ∷ Sw12 ∷ Sw34 ∷ []) (CS23 ∷ CX02 ∷ Sw34 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ CX02 ∷ CS04 ∷ [])
  b2 = at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 5 2 [] (wl0006 c4) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸ done

  b3 : Chain (CS23 ∷ CX02 ∷ Sw34 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ CX02 ∷ CS04 ∷ []) (Sw34 ∷ Sw12 ∷ CS14 ∷ CX01 ∷ Sw12 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ [])
  b3 = at 3 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 c4)) ▸
       at 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0006 c4) ▸ done

  b4 : Chain (Sw34 ∷ Sw12 ∷ CS14 ∷ CX01 ∷ Sw12 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (Sw34 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ Sw34 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ [])
  b4 = at 4 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0014 c4)) ▸
       at 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0006 c4) ▸
       at 6 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0004 c4) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b5 : Chain (Sw34 ∷ Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ Sw34 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ []) (Sw34 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ [])
  b5 = at 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0004 c4) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0003 c4) ▸ done

  b6 : Chain (Sw34 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ []) (Sw34 ∷ Sw12 ∷ Sw34 ∷ CCZ013 ∷ Sw34 ∷ Sw12 ∷ [])
  b6 = at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0003 c4) ▸
       at 4 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw34 ∷ Sw12 ∷ Sw34 ∷ CCZ013 ∷ Sw34 ∷ Sw12 ∷ []) (Sw34 ∷ CCZ024 ∷ [])
  b7 = at 2 3 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push CCZ024 sw3 L: 58 steps
lem-comm-push-CCZ024-sw3-L : WsL → ⟪ (CCZ024 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ CCZ023 ∷ []) ⟫ʷ
lem-comm-push-CCZ024-sw3-L c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (CCZ024 ∷ Sw34 ∷ []) (Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (Sw12 ∷ CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b1 = at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b2 : Chain (Sw12 ∷ CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw34 ∷ [])
  b2 = at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸
       at 0 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0005 c4)) ▸
       at 3 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸ done

  b3 : Chain (CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw12 ∷ Sw34 ∷ []) (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ [])
  b3 = at 1 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0007 c4)) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 5 2 [] (wl0006 c4) ▸
       at 4 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸ done

  b4 : Chain (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ []) (Sw34 ∷ Sw12 ∷ CS13 ∷ Sw12 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ [])
  b4 = at 3 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸
       at 2 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 1 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸
       at 0 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0004 c4) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 2 (CS13 ∷ Sw12 ∷ []) (sym (wl0046 c4)) ▸ done

  b5 : Chain (Sw34 ∷ Sw12 ∷ CS13 ∷ Sw12 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ []) (Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw12 ∷ [])
  b5 = at 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0006 c4) ▸
       at 4 2 (CS13⁻ ∷ Sw12 ∷ []) (sym (wl0028 c4)) ▸
       at 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0006 c4) ▸
       at 6 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Sw12 ∷ []) (Sw34 ∷ Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw12 ∷ [])
  b6 = at 3 2 [] (wl0003 c4) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 3 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw34 ∷ Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw12 ∷ []) (Sw34 ∷ CCZ023 ∷ [])
  b7 = at 2 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CCZ023 CK41: 23 steps
lem-comm-CCZ023-CK41 : WsL → ⟪ (CCZ023 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CCZ023 ∷ []) ⟫ʷ
lem-comm-CCZ023-CK41 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CCZ023 ∷ CK41 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ CK32 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ CCZ024 ∷ []) (lem-comm-push-CCZ023-sw3-L c4) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 10 3 (CK31 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CK32 ∷ Sw12 ∷ []) (sym (wl0094 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ CK32 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ CK31 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ [])
  b1 = at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 8 3 (CK42 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CK43 ∷ Sw23 ∷ []) (sym (wl0091 c4)) ▸
       at 6 2 (CK43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CK₁₀)) ▸
       at 5 2 (CK42 ∷ Sw23 ∷ []) (sym (wl0090 c4)) ▸
       at 5 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 3 2 (CK31 ∷ Sw12 ∷ []) (sym (wl0095 c4)) ▸ done

  b2 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ CK31 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ []) (CK41 ∷ CCZ023 ∷ [])
  b2 = at 3 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0003 c4) ▸
       at 3 9 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸
       at 4 2 (Sw34 ∷ CCZ023 ∷ []) (lem-comm-push-CCZ024-sw3-L c4) ▸
       at 0 5 (CK41 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF023 CK41: 23 steps
lem-comm-TOFF023-CK41 : WsL → ⟪ (Toff023 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ Toff023 ∷ []) ⟫ʷ
lem-comm-TOFF023-CK41 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Toff023 ∷ CK41 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ CK32 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Toff024 ∷ []) (lem-comm-push-TOFF023-sw3-L c4) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (Toff034 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 10 3 (CK31 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CK32 ∷ Sw12 ∷ []) (sym (wl0094 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ CK32 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ CK31 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ [])
  b1 = at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 8 3 (CK42 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CK43 ∷ Sw23 ∷ []) (sym (wl0091 c4)) ▸
       at 6 2 (CK43 ∷ Toff012 ∷ []) (c₃ (Toff) (CK₁₀)) ▸
       at 5 2 (CK42 ∷ Sw23 ∷ []) (sym (wl0090 c4)) ▸
       at 5 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 3 2 (CK31 ∷ Sw12 ∷ []) (sym (wl0095 c4)) ▸ done

  b2 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ CK31 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ []) (CK41 ∷ Toff023 ∷ [])
  b2 = at 3 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0003 c4) ▸
       at 3 9 (Toff034 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸
       at 4 2 (Sw34 ∷ Toff023 ∷ []) (lem-comm-push-TOFF024-sw3-L c4) ▸
       at 0 5 (CK41 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CCZ013 CK42: 15 steps
lem-comm-CCZ013-CK42 : WsL → ⟪ (CCZ013 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CCZ013 ∷ []) ⟫ʷ
lem-comm-CCZ013-CK42 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ013 ∷ CK42 ∷ []) (Sw34 ∷ Sw34 ∷ Sw23 ∷ CK43 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CK42 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CK43 ∷ Sw23 ∷ []) (sym (wl0091 c4)) ▸
       at 3 2 (CK43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CK₁₀)) ▸ done

  b1 : Chain (Sw34 ∷ Sw34 ∷ Sw23 ∷ CK43 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ []) (CK42 ∷ CCZ013 ∷ [])
  b1 = at 2 2 (CK42 ∷ Sw23 ∷ []) (sym (wl0090 c4)) ▸
       at 2 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0004 c4) ▸
       at 2 5 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 0 3 (CK42 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF013 CK42: 15 steps
lem-comm-TOFF013-CK42 : WsL → ⟪ (Toff013 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ Toff013 ∷ []) ⟫ʷ
lem-comm-TOFF013-CK42 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff013 ∷ CK42 ∷ []) (Sw34 ∷ Sw34 ∷ Sw23 ∷ CK43 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CK42 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CK43 ∷ Sw23 ∷ []) (sym (wl0091 c4)) ▸
       at 3 2 (CK43 ∷ Toff012 ∷ []) (c₃ (Toff) (CK₁₀)) ▸ done

  b1 : Chain (Sw34 ∷ Sw34 ∷ Sw23 ∷ CK43 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ []) (CK42 ∷ Toff013 ∷ [])
  b1 = at 2 2 (CK42 ∷ Sw23 ∷ []) (sym (wl0090 c4)) ▸
       at 2 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0004 c4) ▸
       at 2 5 (Toff014 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 0 3 (CK42 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CCZ024 CX13: 11 steps
lem-comm-CCZ024-CX13 : WsL → ⟪ (CCZ024 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ CCZ024 ∷ []) ⟫ʷ
lem-comm-CCZ024-CX13 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CCZ024 ∷ CX13 ∷ []) (Sw12 ∷ Sw34 ∷ Sw34 ∷ CX23 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX23 ∷ Sw12 ∷ []) (sym (wl0022 c4)) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CX24 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX34 ∷ Sw23 ∷ []) (sym (wl0021 c4)) ▸
       at 3 2 (CX34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CX₀₁)) ▸
       at 2 2 (CX24 ∷ Sw23 ∷ []) (sym (wl0020 c4)) ▸
       at 2 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw34 ∷ CX23 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (CX13 ∷ CCZ024 ∷ [])
  b1 = at 1 2 [] (wl0004 c4) ▸
       at 0 2 (CX13 ∷ Sw12 ∷ []) (sym (wl0019 c4)) ▸
       at 1 7 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF213 CX04: 13 steps
lem-comm-TOFF213-CX04 : WsL → ⟪ (Toff213 ∷ CX04 ∷ []) ⟫ʷ ≈ ⟪ (CX04 ∷ Toff213 ∷ []) ⟫ʷ
lem-comm-TOFF213-CX04 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff213 ∷ CX04 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Toff314 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Toff324 ∷ []) (sym (wl0038 c4)) ▸
       at 3 2 (CX01 ∷ Toff324 ∷ []) (sym (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 4 2 (Sw12 ∷ Toff314 ∷ []) (sym (wl0045 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Toff314 ∷ Sw23 ∷ Sw34 ∷ []) (CX04 ∷ Toff213 ∷ [])
  b1 = at 5 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 6 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 0 7 (CX04 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CZ02 TOFF314: 23 steps
lem-comm-CZ02-TOFF314 : WsL → ⟪ (CZ02 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CZ02 ∷ []) ⟫ʷ
lem-comm-CZ02-TOFF314 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CZ02 ∷ Toff314 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Toff214 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CZ03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CZ04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 8 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Toff214 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Toff324 ∷ Sw12 ∷ []) (wl0045 c4) ▸
       at 5 2 (Toff324 ∷ CZ01 ∷ []) (c₂ (CZ) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 2 (Toff314 ∷ Sw12 ∷ []) (wl0038 c4) ▸
       at 4 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸
       at 3 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Toff314 ∷ CZ02 ∷ [])
  b2 = at 2 2 [] (wl0004 c4) ▸
       at 3 7 (CZ04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CZ03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 4 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 0 5 (Toff314 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CSd02 TOFF314: 23 steps
lem-comm-CSd02-TOFF314 : WsL → ⟪ (CS02⁻ ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-comm-CSd02-TOFF314 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS02⁻ ∷ Toff314 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Toff214 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 8 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Toff214 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Toff324 ∷ Sw12 ∷ []) (wl0045 c4) ▸
       at 5 2 (Toff324 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 2 (Toff314 ∷ Sw12 ∷ []) (wl0038 c4) ▸
       at 4 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸
       at 3 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Toff314 ∷ CS02⁻ ∷ [])
  b2 = at 2 2 [] (wl0004 c4) ▸
       at 3 7 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 0 5 (Toff314 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CS02 TOFF314: 23 steps
lem-comm-CS02-TOFF314 : WsL → ⟪ (CS02 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS02 ∷ []) ⟫ʷ
lem-comm-CS02-TOFF314 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS02 ∷ Toff314 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Toff214 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 8 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Toff214 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Toff324 ∷ Sw12 ∷ []) (wl0045 c4) ▸
       at 5 2 (Toff324 ∷ CS01 ∷ []) (c₂ (CS) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 2 (Toff314 ∷ Sw12 ∷ []) (wl0038 c4) ▸
       at 4 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸
       at 3 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Toff314 ∷ CS02 ∷ [])
  b2 = at 2 2 [] (wl0004 c4) ▸
       at 3 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 0 5 (Toff314 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp TOFF413 at 2: 4 steps
lem-resp-TOFF413-at-2 : WsL → ⟪ (Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff423 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF413-at-2 c4 = run b0
  where
  b0 : Chain (Toff413 ∷ []) (Sw12 ∷ Sw01 ∷ Toff423 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ Toff423 ∷ []) (sym (wl0085 c4)) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ Toff423 ∷ []) (sym (c₂ (Swap) (Toffᵗ))) ▸ done


-- comm CX04 TOFF312: 13 steps
lem-comm-CX04-TOFF312 : WsL → ⟪ (CX04 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CX04 ∷ []) ⟫ʷ
lem-comm-CX04-TOFF312 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX04 ∷ Toff312 ∷ []) (Sw34 ∷ Sw23 ∷ Toff413 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Toff423 ∷ Sw12 ∷ []) (wl0084 c4) ▸
       at 3 2 (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ)) ▸
       at 2 2 (Toff413 ∷ Sw12 ∷ []) (wl0085 c4) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Toff413 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (Toff312 ∷ CX04 ∷ [])
  b1 = at 2 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0003 c4) ▸
       at 1 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0004 c4) ▸
       at 1 7 (CX04 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CX30 CCZ124: 9 steps
lem-comm-CX30-CCZ124 : WsL → ⟪ (CX30 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CX30 ∷ []) ⟫ʷ
lem-comm-CX30-CCZ124 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX30 ∷ CCZ124 ∷ []) (CCZ124 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 c4)) ▸
       at 2 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 1 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 1 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸ done

  b1 : Chain (CCZ124 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) (CCZ124 ∷ CX30 ∷ [])
  b1 = at 1 5 (CX30 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CX30 TOFF214: 9 steps
lem-comm-CX30-TOFF214 : WsL → ⟪ (CX30 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CX30 ∷ []) ⟫ʷ
lem-comm-CX30-TOFF214 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX30 ∷ Toff214 ∷ []) (Toff214 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Toff324 ∷ Sw12 ∷ []) (wl0045 c4) ▸
       at 2 2 (Toff324 ∷ CX10 ∷ []) (c₂ (CX₁₀) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 1 2 (Toff314 ∷ Sw12 ∷ []) (wl0038 c4) ▸
       at 1 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸ done

  b1 : Chain (Toff214 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) (Toff214 ∷ CX30 ∷ [])
  b1 = at 1 5 (CX30 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CZ14 TOFF203: 7 steps
lem-comm-CZ14-TOFF203 : WsL → ⟪ (CZ14 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CZ14 ∷ []) ⟫ʷ
lem-comm-CZ14-TOFF203 c4 = run b0
  where
  b0 : Chain (CZ14 ∷ Toff203 ∷ []) (Toff203 ∷ CZ14 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CZ24 ∷ []) (wl0032 c4) ▸
       at 1 2 (Sw23 ∷ CZ34 ∷ []) (wl0034 c4) ▸
       at 2 2 (Toff102 ∷ CZ34 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (CZ))) ▸
       at 3 2 (Sw23 ∷ CZ24 ∷ []) (wl0035 c4) ▸
       at 4 2 (Sw12 ∷ CZ14 ∷ []) (wl0053 c4) ▸
       at 0 5 (Toff203 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CS12 TOFF304: 15 steps
lem-comm-CS12-TOFF304 : WsL → ⟪ (CS12 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CS12 ∷ []) ⟫ʷ
lem-comm-CS12-TOFF304 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS12 ∷ Toff304 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ CS34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CS23 ∷ []) (wl0046 c4) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ CS34 ∷ []) (wl0011 c4) ▸
       at 4 2 (Toff102 ∷ CS34 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (CS))) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ CS34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Toff304 ∷ CS12 ∷ [])
  b1 = at 5 2 (Sw23 ∷ CS24 ∷ []) (wl0008 c4) ▸
       at 6 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 7 2 (Sw12 ∷ CS13 ∷ []) (wl0047 c4) ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (wl0003 c4) ▸
       at 0 9 (Toff304 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF314 CSd02: 23 steps
lem-comm-TOFF314-CSd02 : WsL → ⟪ (Toff314 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Toff314 ∷ []) ⟫ʷ
lem-comm-TOFF314-CSd02 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Toff314 ∷ CS02⁻ ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Toff214 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Toff214 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ Toff324 ∷ []) (sym (wl0038 c4)) ▸
       at 5 2 (CS01⁻ ∷ Toff324 ∷ []) (sym (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 6 2 (Sw12 ∷ Toff314 ∷ []) (sym (wl0045 c4)) ▸
       at 7 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 8 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Toff213 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (CS02⁻ ∷ Toff314 ∷ [])
  b2 = at 10 2 [] (wl0004 c4) ▸
       at 2 7 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0004 c4) ▸
       at 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 1 5 (Toff314 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CSd14 TOFF302: 7 steps
lem-comm-CSd14-TOFF302 : WsL → ⟪ (CS14⁻ ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CS14⁻ ∷ []) ⟫ʷ
lem-comm-CSd14-TOFF302 c4 = run b0
  where
  b0 : Chain (CS14⁻ ∷ Toff302 ∷ []) (Toff302 ∷ CS14⁻ ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CS24⁻ ∷ []) (wl0014 c4) ▸
       at 1 2 (Sw23 ∷ CS34⁻ ∷ []) (wl0012 c4) ▸
       at 2 2 (Toff201 ∷ CS34⁻ ∷ []) (sym (c₃ (Toffᵗ) (CS • CS • CS))) ▸
       at 3 2 (Sw23 ∷ CS24⁻ ∷ []) (wl0009 c4) ▸
       at 4 2 (Sw12 ∷ CS14⁻ ∷ []) (wl0007 c4) ▸
       at 0 5 (Toff302 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CX30 at 2: 4 steps
lem-resp-CX30-at-2 : WsL → ⟪ (CX30 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX31 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX30-at-2 c4 = run b0
  where
  b0 : Chain (CX30 ∷ []) (Sw12 ∷ Sw01 ∷ CX31 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ CX30 ∷ []) (wl0080 c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ CX31 ∷ []) (wl0078 c4) ▸ done


-- comm CSd02 CCZ134: 23 steps
lem-comm-CSd02-CCZ134 : WsL → ⟪ (CS02⁻ ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-comm-CSd02-CCZ134 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS02⁻ ∷ CCZ134 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ CCZ124 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 8 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ CCZ124 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 c4)) ▸
       at 5 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 4 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸
       at 3 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (CCZ134 ∷ CS02⁻ ∷ [])
  b2 = at 2 2 [] (wl0004 c4) ▸
       at 3 7 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 0 5 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CS02 CCZ134: 23 steps
lem-comm-CS02-CCZ134 : WsL → ⟪ (CS02 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CS02 ∷ []) ⟫ʷ
lem-comm-CS02-CCZ134 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS02 ∷ CCZ134 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CCZ124 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 8 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CCZ124 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0044 c4)) ▸
       at 5 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 4 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 4 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸
       at 3 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (CCZ134 ∷ CS02 ∷ [])
  b2 = at 2 2 [] (wl0004 c4) ▸
       at 3 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 0 5 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CZ14 TOFF302: 7 steps
lem-comm-CZ14-TOFF302 : WsL → ⟪ (CZ14 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CZ14 ∷ []) ⟫ʷ
lem-comm-CZ14-TOFF302 c4 = run b0
  where
  b0 : Chain (CZ14 ∷ Toff302 ∷ []) (Toff302 ∷ CZ14 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ Toff201 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CZ24 ∷ []) (wl0032 c4) ▸
       at 1 2 (Sw23 ∷ CZ34 ∷ []) (wl0034 c4) ▸
       at 2 2 (Toff201 ∷ CZ34 ∷ []) (sym (c₃ (Toffᵗ) (CZ))) ▸
       at 3 2 (Sw23 ∷ CZ24 ∷ []) (wl0035 c4) ▸
       at 4 2 (Sw12 ∷ CZ14 ∷ []) (wl0053 c4) ▸
       at 0 5 (Toff302 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CS03 TOFF214: 9 steps
lem-comm-CS03-TOFF214 : WsL → ⟪ (CS03 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CS03 ∷ []) ⟫ʷ
lem-comm-CS03-TOFF214 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS03 ∷ Toff214 ∷ []) (Toff214 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Toff324 ∷ Sw12 ∷ []) (wl0045 c4) ▸
       at 2 2 (Toff324 ∷ CS01 ∷ []) (c₂ (CS) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 1 2 (Toff314 ∷ Sw12 ∷ []) (wl0038 c4) ▸
       at 1 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸ done

  b1 : Chain (Toff214 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (Toff214 ∷ CS03 ∷ [])
  b1 = at 1 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF214 CS03: 9 steps
lem-comm-TOFF214-CS03 : WsL → ⟪ (Toff214 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff214 ∷ []) ⟫ʷ
lem-comm-TOFF214-CS03 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff214 ∷ CS03 ∷ []) (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Toff214 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ Toff324 ∷ []) (sym (wl0038 c4)) ▸
       at 2 2 (CS01 ∷ Toff324 ∷ []) (sym (c₂ (CS) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 3 2 (Sw12 ∷ Toff314 ∷ []) (sym (wl0045 c4)) ▸
       at 4 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Toff214 ∷ []) (CS03 ∷ Toff214 ∷ [])
  b1 = at 0 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CZ23 TOFF014: 9 steps
lem-comm-CZ23-TOFF014 : WsL → ⟪ (CZ23 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CZ23 ∷ []) ⟫ʷ
lem-comm-CZ23-TOFF014 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ23 ∷ Toff014 ∷ []) (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ CZ23 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CZ24 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ CZ34 ∷ []) (wl0034 c4) ▸
       at 2 2 (Toff012 ∷ CZ34 ∷ []) (sym (c₃ (Toff) (CZ))) ▸
       at 3 2 (Sw23 ∷ CZ24 ∷ []) (wl0035 c4) ▸
       at 4 1 (Sw34 ∷ CZ23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ CZ23 ∷ []) (Toff014 ∷ CZ23 ∷ [])
  b1 = at 0 5 (Toff014 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CZ24 TOFF301: 5 steps
lem-comm-CZ24-TOFF301 : WsL → ⟪ (CZ24 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CZ24 ∷ []) ⟫ʷ
lem-comm-CZ24-TOFF301 c4 = run b0
  where
  b0 : Chain (CZ24 ∷ Toff301 ∷ []) (Toff301 ∷ CZ24 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ CZ34 ∷ []) (wl0034 c4) ▸
       at 1 2 (Toff201 ∷ CZ34 ∷ []) (sym (c₃ (Toffᵗ) (CZ))) ▸
       at 2 2 (Sw23 ∷ CZ24 ∷ []) (wl0035 c4) ▸
       at 0 3 (Toff301 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm SWAP14 BOX(3;20): 7 steps
lem-comm-SWAP14-BOX⟨3·20⟩ : WsL → ⟪ (Sw14 ∷ Bx3-20 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-20 ∷ Sw14 ∷ []) ⟫ʷ
lem-comm-SWAP14-BOX⟨3·20⟩ c4 = run b0
  where
  b0 : Chain (Sw14 ∷ Bx3-20 ∷ []) (Bx3-20 ∷ Sw14 ∷ [])
  b0 = at 1 1 (CZ02 ∷ []) (refl) ▸
       at 1 1 (Sw12 ∷ CZ01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ Sw24 ∷ []) (sym (wl0072 c4)) ▸
       at 1 2 (CZ01 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸
       at 2 2 (Sw12 ∷ Sw14 ∷ []) (sym (wl0093 c4)) ▸
       at 0 3 (CZ02 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Bx3-20 ∷ []) (refl) ▸ done


-- comm CX31 TOFF024: 11 steps
lem-comm-CX31-TOFF024 : WsL → ⟪ (CX31 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CX31 ∷ []) ⟫ʷ
lem-comm-CX31-TOFF024 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX31 ∷ Toff024 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ CX32 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CX32 ∷ []) (wl0057 c4) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CX42 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ CX43 ∷ []) (wl0058 c4) ▸
       at 3 2 (Toff012 ∷ CX43 ∷ []) (sym (c₃ (Toff) (CX₁₀))) ▸
       at 4 2 (Sw23 ∷ CX42 ∷ []) (wl0059 c4) ▸
       at 5 1 (Sw34 ∷ CX32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ CX32 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ []) (Toff024 ∷ CX31 ∷ [])
  b1 = at 7 2 [] (wl0004 c4) ▸
       at 6 2 (Sw12 ∷ CX31 ∷ []) (wl0060 c4) ▸
       at 0 7 (Toff024 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CCZ134 CS02: 23 steps
lem-comm-CCZ134-CS02 : WsL → ⟪ (CCZ134 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CCZ134 ∷ []) ⟫ʷ
lem-comm-CCZ134-CS02 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CCZ134 ∷ CS02 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ CCZ124 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ CCZ124 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw12 ∷ CCZ234 ∷ []) (wl0037 c4) ▸
       at 5 2 (CS01 ∷ CCZ234 ∷ []) (sym (c₂ (CS) (CCZ))) ▸
       at 6 2 (Sw12 ∷ CCZ134 ∷ []) (wl0044 c4) ▸
       at 7 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 8 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Sw23 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw34 ∷ Sw34 ∷ Sw23 ∷ []) (CS02 ∷ CCZ134 ∷ [])
  b2 = at 10 2 [] (wl0004 c4) ▸
       at 2 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0004 c4) ▸
       at 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0003 c4) ▸
       at 1 5 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF312 CX04: 13 steps
lem-comm-TOFF312-CX04 : WsL → ⟪ (Toff312 ∷ CX04 ∷ []) ⟫ʷ ≈ ⟪ (CX04 ∷ Toff312 ∷ []) ⟫ʷ
lem-comm-TOFF312-CX04 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff312 ∷ CX04 ∷ []) (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Toff413 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (Toff413 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Toff423 ∷ []) (sym (wl0085 c4)) ▸
       at 3 2 (CX01 ∷ Toff423 ∷ []) (sym (c₂ (CX₀₁) (Toffᵗ))) ▸
       at 4 2 (Sw12 ∷ Toff413 ∷ []) (sym (wl0084 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Toff413 ∷ Sw23 ∷ Sw34 ∷ []) (CX04 ∷ Toff312 ∷ [])
  b1 = at 5 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 6 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 0 7 (CX04 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CZ13 TOFF204: 11 steps
lem-comm-CZ13-TOFF204 : WsL → ⟪ (CZ13 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CZ13 ∷ []) ⟫ʷ
lem-comm-CZ13-TOFF204 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ13 ∷ Toff204 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ CZ23 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CZ23 ∷ []) (wl0033 c4) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CZ24 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ CZ34 ∷ []) (wl0034 c4) ▸
       at 3 2 (Toff102 ∷ CZ34 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (CZ))) ▸
       at 4 2 (Sw23 ∷ CZ24 ∷ []) (wl0035 c4) ▸
       at 5 1 (Sw34 ∷ CZ23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ CZ23 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ []) (Toff204 ∷ CZ13 ∷ [])
  b1 = at 7 2 [] (wl0004 c4) ▸
       at 6 2 (Sw12 ∷ CZ13 ∷ []) (wl0036 c4) ▸
       at 0 7 (Toff204 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CX03 at 2: 4 steps
lem-resp-CX03-at-2 : WsL → ⟪ (CX03 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX13 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX03-at-2 c4 = run b0
  where
  b0 : Chain (CX03 ∷ []) (Sw12 ∷ Sw01 ∷ CX13 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ CX03 ∷ []) (wl0010 c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ CX13 ∷ []) (wl0016 c4) ▸ done


-- comm push SWAP04 sw2 L: 7 steps
lem-comm-push-SWAP04-sw2-L : WsL → ⟪ (Sw04 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw04 ∷ []) ⟫ʷ
lem-comm-push-SWAP04-sw2-L c4 = run b0
  where
  b0 : Chain (Sw04 ∷ Sw23 ∷ []) (Sw23 ∷ Sw04 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0002 c4) ▸
       at 4 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 3 2 (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑)) ▸
       at 2 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 0 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0002 c4)) ▸
       at 1 7 (Sw04 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm SWAP03 BOX(2;14): 21 steps
lem-comm-SWAP03-BOX⟨2·14⟩ : WsL → ⟪ (Sw03 ∷ Bx2-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-14 ∷ Sw03 ∷ []) ⟫ʷ
lem-comm-SWAP03-BOX⟨2·14⟩ c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw03 ∷ Bx2-14 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ [])
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

  b2 : Chain (Sw34 ∷ Sw23 ∷ CZ12 ∷ Sw04 ∷ Sw23 ∷ Sw34 ∷ []) (Bx2-14 ∷ Sw03 ∷ [])
  b2 = at 3 2 (Sw23 ∷ Sw04 ∷ []) (lem-comm-push-SWAP04-sw2-L c4) ▸
       at 4 1 (Sw34 ∷ Sw03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸
       at 0 5 (CZ14 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Bx2-14 ∷ []) (refl) ▸ done


-- comm SWAP14 BOX(2;30): 9 steps
lem-comm-SWAP14-BOX⟨2·30⟩ : WsL → ⟪ (Sw14 ∷ Bx2-30 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-30 ∷ Sw14 ∷ []) ⟫ʷ
lem-comm-SWAP14-BOX⟨2·30⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw14 ∷ Bx2-30 ∷ []) (CZ03 ∷ Sw14 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 1 1 (Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ Sw14 ∷ []) (wl0074 c4) ▸
       at 1 2 (Sw12 ∷ Sw24 ∷ []) (sym (wl0072 c4)) ▸
       at 2 2 (CZ01 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸
       at 3 2 (Sw12 ∷ Sw14 ∷ []) (sym (wl0093 c4)) ▸
       at 4 2 (Sw23 ∷ Sw14 ∷ []) (wl0074 c4) ▸
       at 0 5 (CZ03 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CZ03 ∷ Sw14 ∷ []) (Bx2-30 ∷ Sw14 ∷ [])
  b1 = at 0 1 (Bx2-30 ∷ []) (refl) ▸ done

