{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R002 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0002 ; wl0003 ; wl0004 ; wl0005 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0010 ; wl0011 ; wl0012 ; wl0013 ; wl0014 ; wl0016 ; wl0017 ; wl0018 ; wl0020 ; wl0021 ; wl0025 ; wl0028 ; wl0029 ; wl0031 ; wl0032 ; wl0033 ; wl0034 ; wl0035 ; wl0036 ; wl0037 ; wl0039 ; wl0040 ; wl0041 ; wl0046 ; wl0047 ; wl0048 ; wl0050 ; wl0051 ; wl0052 ; wl0053 ; wl0054 ; wl0055 ; wl0056 ; wl0057 ; wl0058 ; wl0059 ; wl0060 ; wl0061 ; wl0062 ; wl0063 ; wl0064 ; wl0065 ; wl0066 ; wl0067 ; wl0068 ; wl0069 ; wl0070 ; wl0071 ; wl0072 ; wl0073)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-push-CS04-sw0-L ; lem-comm-push-CS04-sw1-L ; lem-comm-push-CS04-sw1-R ; lem-comm-push-CS04-sw2-L ; lem-comm-push-CS04-sw2-R ; lem-comm-push-CSd04-sw0-L ; lem-comm-push-CSd04-sw1-L ; lem-comm-push-TOFF024-sw0-L ; lem-comm-push-TOFF034-sw0-L ; lem-comm-push-TOFF034-sw1-L)
-- comm CS23 CCZ014: 9 steps
lem-comm-CS23-CCZ014 : WsL → ⟪ (CS23 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CS23 ∷ []) ⟫ʷ
lem-comm-CS23-CCZ014 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS23 ∷ CCZ014 ∷ []) (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ CS23 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ CS34 ∷ []) (wl0011 c4) ▸
       at 2 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 3 2 (Sw23 ∷ CS24 ∷ []) (wl0008 c4) ▸
       at 4 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ CS23 ∷ []) (CCZ014 ∷ CS23 ∷ [])
  b1 = at 0 5 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CS24 at 3: 6 steps
lem-resp-CS24-at-3 : WsL → ⟪ (CS24 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS34 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CS24-at-3 c4 = run b0
  where
  b0 : Chain (CS24 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS34 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 2 (Sw23 ∷ CS34 ∷ []) (wl0011 c4) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ CS34 ∷ []) (sym (c₂ (Swap) (CS ↑))) ▸ done


-- comm CX23 CCZ014: 9 steps
lem-comm-CX23-CCZ014 : WsL → ⟪ (CX23 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CX23 ∷ []) ⟫ʷ
lem-comm-CX23-CCZ014 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX23 ∷ CCZ014 ∷ []) (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ CX23 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CX24 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ CX34 ∷ []) (wl0020 c4) ▸
       at 2 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 3 2 (Sw23 ∷ CX24 ∷ []) (wl0021 c4) ▸
       at 4 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ CX23 ∷ []) (CCZ014 ∷ CX23 ∷ [])
  b1 = at 0 5 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CCZ124 at 3: 7 steps
lem-resp-CCZ124-at-3 : WsL → ⟪ (CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CCZ234 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CCZ124-at-3 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CCZ234 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (Sw12 ∷ CCZ234 ∷ []) (wl0037 c4) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ CCZ234 ∷ []) (sym (c₂ (Swap) (CCZ))) ▸ done


-- resp TOFF023 at 1: 2 steps
lem-resp-TOFF023-at-1 : WsL → ⟪ (Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF023-at-1 c4 = run b0
  where
  b0 : Chain (Toff023 ∷ []) (Sw01 ∷ Toff123 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ Toff123 ∷ []) (sym (wl0052 c4)) ▸ done


-- resp TOFF024 at 1: 2 steps
lem-resp-TOFF024-at-1 : WsL → ⟪ (Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff124 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF024-at-1 c4 = run b0
  where
  b0 : Chain (Toff024 ∷ []) (Sw01 ∷ Toff124 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ Toff124 ∷ []) (lem-comm-push-TOFF024-sw0-L c4) ▸ done


-- comm CX14 TOFF023: 7 steps
lem-comm-CX14-TOFF023 : WsL → ⟪ (CX14 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CX14 ∷ []) ⟫ʷ
lem-comm-CX14-TOFF023 c4 = run b0
  where
  b0 : Chain (CX14 ∷ Toff023 ∷ []) (Toff023 ∷ CX14 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CX24 ∷ []) (wl0050 c4) ▸
       at 1 2 (Sw23 ∷ CX34 ∷ []) (wl0020 c4) ▸
       at 2 2 (Toff012 ∷ CX34 ∷ []) (sym (c₃ (Toff) (CX₀₁))) ▸
       at 3 2 (Sw23 ∷ CX24 ∷ []) (wl0021 c4) ▸
       at 4 2 (Sw12 ∷ CX14 ∷ []) (wl0051 c4) ▸
       at 0 5 (Toff023 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp TOFF024 at 3: 7 steps
lem-resp-TOFF024-at-3 : WsL → ⟪ (Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff134 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF024-at-3 c4 = run b0
  where
  b0 : Chain (Toff024 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff134 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (Toff034 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (Sw12 ∷ Toff034 ∷ []) (lem-comm-push-TOFF034-sw1-L c4) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ Toff134 ∷ []) (lem-comm-push-TOFF034-sw0-L c4) ▸ done


-- comm CZ14 CCZ023: 7 steps
lem-comm-CZ14-CCZ023 : WsL → ⟪ (CZ14 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CZ14 ∷ []) ⟫ʷ
lem-comm-CZ14-CCZ023 c4 = run b0
  where
  b0 : Chain (CZ14 ∷ CCZ023 ∷ []) (CCZ023 ∷ CZ14 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CZ24 ∷ []) (wl0032 c4) ▸
       at 1 2 (Sw23 ∷ CZ34 ∷ []) (wl0034 c4) ▸
       at 2 2 (CCZ012 ∷ CZ34 ∷ []) (sym (c₃ (CCZ) (CZ))) ▸
       at 3 2 (Sw23 ∷ CZ24 ∷ []) (wl0035 c4) ▸
       at 4 2 (Sw12 ∷ CZ14 ∷ []) (wl0053 c4) ▸
       at 0 5 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CZ14 TOFF023: 7 steps
lem-comm-CZ14-TOFF023 : WsL → ⟪ (CZ14 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CZ14 ∷ []) ⟫ʷ
lem-comm-CZ14-TOFF023 c4 = run b0
  where
  b0 : Chain (CZ14 ∷ Toff023 ∷ []) (Toff023 ∷ CZ14 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CZ24 ∷ []) (wl0032 c4) ▸
       at 1 2 (Sw23 ∷ CZ34 ∷ []) (wl0034 c4) ▸
       at 2 2 (Toff012 ∷ CZ34 ∷ []) (sym (c₃ (Toff) (CZ))) ▸
       at 3 2 (Sw23 ∷ CZ24 ∷ []) (wl0035 c4) ▸
       at 4 2 (Sw12 ∷ CZ14 ∷ []) (wl0053 c4) ▸
       at 0 5 (Toff023 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF024 CSd13: 11 steps
lem-comm-TOFF024-CSd13 : WsL → ⟪ (Toff024 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Toff024 ∷ []) ⟫ʷ
lem-comm-TOFF024-CSd13 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff024 ∷ CS13⁻ ∷ []) (Sw12 ∷ Sw34 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS23⁻ ∷ Sw12 ∷ []) (sym (wl0029 c4)) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 3 2 (CS34⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (CS • CS • CS)) ▸
       at 2 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 2 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (CS13⁻ ∷ Toff024 ∷ [])
  b1 = at 1 2 [] (wl0004 c4) ▸
       at 0 2 (CS13⁻ ∷ Sw12 ∷ []) (sym (wl0028 c4)) ▸
       at 1 7 (Toff024 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CX24 CCZ013: 5 steps
lem-comm-CX24-CCZ013 : WsL → ⟪ (CX24 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CX24 ∷ []) ⟫ʷ
lem-comm-CX24-CCZ013 c4 = run b0
  where
  b0 : Chain (CX24 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX24 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ CX34 ∷ []) (wl0020 c4) ▸
       at 1 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 2 2 (Sw23 ∷ CX24 ∷ []) (wl0021 c4) ▸
       at 0 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CSd24 TOFF013: 5 steps
lem-comm-CSd24-TOFF013 : WsL → ⟪ (CS24⁻ ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS24⁻ ∷ []) ⟫ʷ
lem-comm-CSd24-TOFF013 c4 = run b0
  where
  b0 : Chain (CS24⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS24⁻ ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ CS34⁻ ∷ []) (wl0012 c4) ▸
       at 1 2 (Toff012 ∷ CS34⁻ ∷ []) (sym (c₃ (Toff) (CS • CS • CS))) ▸
       at 2 2 (Sw23 ∷ CS24⁻ ∷ []) (wl0009 c4) ▸
       at 0 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp TOFF134 at 2: 4 steps
lem-resp-TOFF134-at-2 : WsL → ⟪ (Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff234 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF134-at-2 c4 = run b0
  where
  b0 : Chain (Toff134 ∷ []) (Sw12 ∷ Sw01 ∷ Toff234 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ Toff234 ∷ []) (sym (wl0054 c4)) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ Toff234 ∷ []) (sym (c₂ (Swap) (Toff))) ▸ done


-- resp TOFF013 at 2: 5 steps
lem-resp-TOFF013-at-2 : WsL → ⟪ (Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff123 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF013-at-2 c4 = run b0
  where
  b0 : Chain (Toff013 ∷ []) (Sw12 ∷ Sw01 ∷ Toff123 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 3 (Toff023 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ Toff123 ∷ []) (sym (wl0052 c4)) ▸ done


-- comm CX24 TOFF013: 5 steps
lem-comm-CX24-TOFF013 : WsL → ⟪ (CX24 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CX24 ∷ []) ⟫ʷ
lem-comm-CX24-TOFF013 c4 = run b0
  where
  b0 : Chain (CX24 ∷ Toff013 ∷ []) (Toff013 ∷ CX24 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ CX34 ∷ []) (wl0020 c4) ▸
       at 1 2 (Toff012 ∷ CX34 ∷ []) (sym (c₃ (Toff) (CX₀₁))) ▸
       at 2 2 (Sw23 ∷ CX24 ∷ []) (wl0021 c4) ▸
       at 0 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CZ24 CCZ013: 5 steps
lem-comm-CZ24-CCZ013 : WsL → ⟪ (CZ24 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CZ24 ∷ []) ⟫ʷ
lem-comm-CZ24-CCZ013 c4 = run b0
  where
  b0 : Chain (CZ24 ∷ CCZ013 ∷ []) (CCZ013 ∷ CZ24 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ CZ34 ∷ []) (wl0034 c4) ▸
       at 1 2 (CCZ012 ∷ CZ34 ∷ []) (sym (c₃ (CCZ) (CZ))) ▸
       at 2 2 (Sw23 ∷ CZ24 ∷ []) (wl0035 c4) ▸
       at 0 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CZ24 TOFF013: 5 steps
lem-comm-CZ24-TOFF013 : WsL → ⟪ (CZ24 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CZ24 ∷ []) ⟫ʷ
lem-comm-CZ24-TOFF013 c4 = run b0
  where
  b0 : Chain (CZ24 ∷ Toff013 ∷ []) (Toff013 ∷ CZ24 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw23 ∷ CZ34 ∷ []) (wl0034 c4) ▸
       at 1 2 (Toff012 ∷ CZ34 ∷ []) (sym (c₃ (Toff) (CZ))) ▸
       at 2 2 (Sw23 ∷ CZ24 ∷ []) (wl0035 c4) ▸
       at 0 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm SWAP23 BOX(0;14): 11 steps
lem-comm-SWAP23-BOX⟨0·14⟩ : WsL → ⟪ (Sw23 ∷ Bx0-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-14 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-SWAP23-BOX⟨0·14⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Bx0-14 ∷ []) (Sw34 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 1 1 (Sw34 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (Sw24 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ Sw34 ∷ []) (sym (wl0055 c4)) ▸
       at 2 2 (CZ12 ∷ Sw34 ∷ []) (sym (c₃ (CZ ↑) (Swap))) ▸
       at 3 2 (Sw23 ∷ Sw24 ∷ []) (sym (wl0056 c4)) ▸
       at 4 1 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ []) (Bx0-14 ∷ Sw23 ∷ [])
  b1 = at 6 2 [] (wl0004 c4) ▸
       at 0 5 (CZ14 ∷ []) (by-assoc Eq.refl) ▸
       at 0 1 (Bx0-14 ∷ []) (refl) ▸ done


-- resp TOFF203 at 1: 2 steps
lem-resp-TOFF203-at-1 : WsL → ⟪ (Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF203-at-1 c4 = run b0
  where
  b0 : Chain (Toff203 ∷ []) (Sw01 ∷ Toff213 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ Toff213 ∷ []) (sym (wl0031 c4)) ▸ done


-- comm push CSd04 sw2 L: 7 steps
lem-comm-push-CSd04-sw2-L : WsL → ⟪ (CS04⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-comm-push-CSd04-sw2-L c4 = run b0
  where
  b0 : Chain (CS04⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS04⁻ ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0002 c4) ▸
       at 4 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 3 2 (Sw34 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Swap ↑)) ▸
       at 2 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 0 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0002 c4)) ▸
       at 1 7 (CS04⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CSd04 at 3: 6 steps
lem-resp-CSd04-at-3 : WsL → ⟪ (CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS14⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CSd04-at-3 c4 = run b0
  where
  b0 : Chain (CS04⁻ ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS14⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 2 (Sw23 ∷ CS04⁻ ∷ []) (lem-comm-push-CSd04-sw2-L c4) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (Sw12 ∷ CS04⁻ ∷ []) (lem-comm-push-CSd04-sw1-L c4) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ CS14⁻ ∷ []) (lem-comm-push-CSd04-sw0-L c4) ▸ done


-- resp CS04 at 3: 6 steps
lem-resp-CS04-at-3 : WsL → ⟪ (CS04 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CS04-at-3 c4 = run b0
  where
  b0 : Chain (CS04 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 2 (Sw23 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw2-L c4) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L c4) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L c4) ▸ done


-- comm CX21 CCZ034: 15 steps
lem-comm-CX21-CCZ034 : WsL → ⟪ (CX21 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CX21 ∷ []) ⟫ʷ
lem-comm-CX21-CCZ034 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX21 ∷ CCZ034 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ CX43 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CX31 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CX32 ∷ []) (wl0057 c4) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CX42 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ CX43 ∷ []) (wl0058 c4) ▸
       at 4 2 (CCZ012 ∷ CX43 ∷ []) (sym (c₃ (CCZ) (CX₁₀))) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ CX43 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (CCZ034 ∷ CX21 ∷ [])
  b1 = at 5 2 (Sw23 ∷ CX42 ∷ []) (wl0059 c4) ▸
       at 6 1 (Sw34 ∷ CX32 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 7 2 (Sw12 ∷ CX31 ∷ []) (wl0060 c4) ▸
       at 8 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (wl0003 c4) ▸
       at 0 9 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CX31 at 2: 4 steps
lem-resp-CX31-at-2 : WsL → ⟪ (CX31 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX32 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX31-at-2 c4 = run b0
  where
  b0 : Chain (CX31 ∷ []) (Sw12 ∷ Sw01 ∷ CX32 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ CX32 ∷ []) (wl0057 c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ CX32 ∷ []) (sym (c₂ (Swap) (CX₁₀))) ▸ done


-- comm SWAP13 BOX(0;24): 9 steps
lem-comm-SWAP13-BOX⟨0·24⟩ : WsL → ⟪ (Sw13 ∷ Bx0-24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-24 ∷ Sw13 ∷ []) ⟫ʷ
lem-comm-SWAP13-BOX⟨0·24⟩ c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw13 ∷ Bx0-24 ∷ []) (CZ24 ∷ Sw13 ∷ [])
  b0 = at 1 1 (CZ24 ∷ []) (refl) ▸
       at 1 1 (Sw34 ∷ CZ23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (Sw14 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CZ23 ∷ Sw14 ∷ []) (sym (wl0061 c4)) ▸
       at 2 1 (Sw34 ∷ Sw13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 0 3 (CZ24 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CZ24 ∷ Sw13 ∷ []) (Bx0-24 ∷ Sw13 ∷ [])
  b1 = at 0 1 (Bx0-24 ∷ []) (refl) ▸ done


-- resp CZ14 at 3: 6 steps
lem-resp-CZ14-at-3 : WsL → ⟪ (CZ14 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CZ24 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CZ14-at-3 c4 = run b0
  where
  b0 : Chain (CZ14 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CZ24 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 2 (Sw23 ∷ CZ14 ∷ []) (wl0062 c4) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (Sw12 ∷ CZ24 ∷ []) (wl0032 c4) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ CZ24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CZ • Swap ↑))) ▸ done


-- resp TOFF302 at 1: 2 steps
lem-resp-TOFF302-at-1 : WsL → ⟪ (Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff312 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF302-at-1 c4 = run b0
  where
  b0 : Chain (Toff302 ∷ []) (Sw01 ∷ Toff312 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ Toff312 ∷ []) (sym (wl0063 c4)) ▸ done


-- comm CZ13 CCZ024: 11 steps
lem-comm-CZ13-CCZ024 : WsL → ⟪ (CZ13 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CZ13 ∷ []) ⟫ʷ
lem-comm-CZ13-CCZ024 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ13 ∷ CCZ024 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ CZ23 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CZ23 ∷ []) (wl0033 c4) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CZ24 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ CZ34 ∷ []) (wl0034 c4) ▸
       at 3 2 (CCZ012 ∷ CZ34 ∷ []) (sym (c₃ (CCZ) (CZ))) ▸
       at 4 2 (Sw23 ∷ CZ24 ∷ []) (wl0035 c4) ▸
       at 5 1 (Sw34 ∷ CZ23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ CZ23 ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ []) (CCZ024 ∷ CZ13 ∷ [])
  b1 = at 7 2 [] (wl0004 c4) ▸
       at 6 2 (Sw12 ∷ CZ13 ∷ []) (wl0036 c4) ▸
       at 0 7 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF013 CSd24: 15 steps
lem-comm-TOFF013-CSd24 : WsL → ⟪ (Toff013 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ Toff013 ∷ []) ⟫ʷ
lem-comm-TOFF013-CSd24 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff013 ∷ CS24⁻ ∷ []) (Sw34 ∷ Sw34 ∷ Sw23 ∷ CS34⁻ ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 3 2 (CS34⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (CS • CS • CS)) ▸ done

  b1 : Chain (Sw34 ∷ Sw34 ∷ Sw23 ∷ CS34⁻ ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw34 ∷ []) (CS24⁻ ∷ Toff013 ∷ [])
  b1 = at 2 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 2 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0004 c4) ▸
       at 2 5 (Toff014 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 0 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CSd13 TOFF024: 11 steps
lem-comm-CSd13-TOFF024 : WsL → ⟪ (CS13⁻ ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-comm-CSd13-TOFF024 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS13⁻ ∷ Toff024 ∷ []) (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ CS23⁻ ∷ []) (wl0028 c4) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ CS34⁻ ∷ []) (wl0012 c4) ▸
       at 3 2 (Toff012 ∷ CS34⁻ ∷ []) (sym (c₃ (Toff) (CS • CS • CS))) ▸
       at 4 2 (Sw23 ∷ CS24⁻ ∷ []) (wl0009 c4) ▸
       at 5 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ Sw34 ∷ Sw12 ∷ []) (Toff024 ∷ CS13⁻ ∷ [])
  b1 = at 7 2 [] (wl0004 c4) ▸
       at 6 2 (Sw12 ∷ CS13⁻ ∷ []) (wl0029 c4) ▸
       at 0 7 (Toff024 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push TOFF401 sw2 L: 62 steps
lem-comm-push-TOFF401-sw2-L : WsL → ⟪ (Toff401 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Toff401 ∷ []) ⟫ʷ
lem-comm-push-TOFF401-sw2-L c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Toff401 ∷ Sw23 ∷ []) (Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K3 ∷ Sw23 ∷ []) (sym (wl0064 c4)) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸ done

  b1 : Chain (Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (K4 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw23 ∷ [])
  b1 = at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K3 ∷ Sw23 ∷ []) (sym (wl0064 c4)) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 0 2 (K4 ∷ Sw34 ∷ []) (sym (wl0065 c4)) ▸ done

  b2 : Chain (K4 ∷ Sw34 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw23 ∷ []) (K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw34 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw23 ∷ [])
  b2 = at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Sw34 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw23 ∷ []) (K4 ∷ CS14 ∷ CX01 ∷ Sw23 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ [])
  b3 = at 6 2 (K4 ∷ Sw34 ∷ []) (sym (wl0065 c4)) ▸
       at 7 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 7 2 (Sw23 ∷ ι ∷ []) (c₁ (iI) (Swap ↑)) ▸
       at 6 2 (Sw23 ∷ K4 ∷ []) (sym (c₄ (Swap ↑ ↑) (K))) ▸
       at 5 2 (Sw23 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw2-L c4) ▸
       at 4 2 (Sw23 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap)) ▸
       at 3 2 (Sw23 ∷ CS14⁻ ∷ []) (wl0048 c4) ▸ done

  b4 : Chain (K4 ∷ CS14 ∷ CX01 ∷ Sw23 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ []) (Sw23 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw34 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ [])
  b4 = at 2 2 (Sw23 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap)) ▸
       at 1 2 (Sw23 ∷ CS14 ∷ []) (wl0017 c4) ▸
       at 0 2 (Sw23 ∷ K4 ∷ []) (sym (c₄ (Swap ↑ ↑) (K))) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 2 (K3 ∷ Sw34 ∷ []) (sym (wl0066 c4)) ▸
       at 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0004 c4) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b5 : Chain (Sw23 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw34 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ [])
  b5 = at 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0004 c4) ▸
       at 8 2 (K3 ∷ Sw34 ∷ []) (sym (wl0066 c4)) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸ done

  b6 : Chain (Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ K3 ∷ ι ∷ Sw34 ∷ [])
  b6 = at 3 2 (K2 ∷ Sw23 ∷ []) (sym (wl0067 c4)) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0003 c4) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw23 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ K3 ∷ ι ∷ Sw34 ∷ []) (Sw23 ∷ Toff401 ∷ [])
  b7 = at 8 2 [] (wl0003 c4) ▸
       at 9 2 (K2 ∷ Sw23 ∷ []) (sym (wl0067 c4)) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 3 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff301 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff401 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push TOFF402 sw0 L: 62 steps
lem-comm-push-TOFF402-sw0-L : WsL → ⟪ (Toff402 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff412 ∷ []) ⟫ʷ
lem-comm-push-TOFF402-sw0-L c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Toff402 ∷ Sw01 ∷ []) (Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K3 ∷ Sw23 ∷ []) (sym (wl0064 c4)) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ []) (Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ [])
  b1 = at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K3 ∷ Sw23 ∷ []) (sym (wl0064 c4)) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 10 2 [] (wl0003 c4) ▸ done

  b2 : Chain (Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ []) (Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw34 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ [])
  b2 = at 1 2 (K4 ∷ Sw34 ∷ []) (sym (wl0065 c4)) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸ done

  b3 : Chain (Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw34 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ []) (K4 ∷ CS24 ∷ CX02 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw01 ∷ [])
  b3 = at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K4 ∷ Sw34 ∷ []) (sym (wl0065 c4)) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 9 2 [] (wl0004 c4) ▸
       at 0 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 1 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0005 c4)) ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (K4 ∷ CS24 ∷ CX02 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw01 ∷ []) (K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ Sw01 ∷ ι ∷ [])
  b4 = at 3 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0007 c4)) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 6 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 7 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 8 2 [] (wl0006 c4) ▸
       at 7 2 (Sw01 ∷ ι ∷ []) (sym (wl0025 c4)) ▸ done

  b5 : Chain (K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ Sw01 ∷ ι ∷ []) (Sw01 ∷ Sw34 ∷ Sw34 ∷ K4 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K4 ∷ ι ∷ [])
  b5 = at 6 2 (Sw01 ∷ K4 ∷ []) (sym (c₂ (Swap) (K ↑ ↑))) ▸
       at 5 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L c4) ▸
       at 4 2 (Sw01 ∷ CX12 ∷ []) (wl0039 c4) ▸
       at 3 2 (Sw01 ∷ CS24⁻ ∷ []) (sym (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 2 2 (Sw01 ∷ CX12 ∷ []) (wl0039 c4) ▸
       at 1 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸
       at 0 2 (Sw01 ∷ K4 ∷ []) (sym (c₂ (Swap) (K ↑ ↑))) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸ done

  b6 : Chain (Sw01 ∷ Sw34 ∷ Sw34 ∷ K4 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K4 ∷ ι ∷ []) (Sw01 ∷ Sw34 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ K4 ∷ ι ∷ [])
  b6 = at 2 2 (K3 ∷ Sw34 ∷ []) (sym (wl0066 c4)) ▸
       at 4 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0004 c4) ▸
       at 4 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 6 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 8 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (Sw01 ∷ Sw34 ∷ K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw34 ∷ Sw34 ∷ CS13 ∷ Sw34 ∷ K4 ∷ ι ∷ []) (Sw01 ∷ Toff412 ∷ [])
  b7 = at 7 2 [] (wl0004 c4) ▸
       at 8 2 (K3 ∷ Sw34 ∷ []) (sym (wl0066 c4)) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 2 8 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (wl0068 c4) ▸
       at 2 8 (Toff312 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff412 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp TOFF401 at 3: 7 steps
lem-resp-TOFF401-at-3 : WsL → ⟪ (Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff412 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF401-at-3 c4 = run b0
  where
  b0 : Chain (Toff401 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff412 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 2 (Sw23 ∷ Toff401 ∷ []) (lem-comm-push-TOFF401-sw2-L c4) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 3 (Toff402 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ Toff412 ∷ []) (lem-comm-push-TOFF402-sw0-L c4) ▸ done


-- resp CZ24 at 3: 6 steps
lem-resp-CZ24-at-3 : WsL → ⟪ (CZ24 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CZ34 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CZ24-at-3 c4 = run b0
  where
  b0 : Chain (CZ24 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CZ34 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 2 (Sw23 ∷ CZ34 ∷ []) (wl0034 c4) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (Sw12 ∷ CZ34 ∷ []) (sym (c₃ (Swap ↑) (CZ))) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ CZ34 ∷ []) (sym (c₂ (Swap) (CZ ↑))) ▸ done


-- resp CX41 at 2: 4 steps
lem-resp-CX41-at-2 : WsL → ⟪ (CX41 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX42 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX41-at-2 c4 = run b0
  where
  b0 : Chain (CX41 ∷ []) (Sw12 ∷ Sw01 ∷ CX42 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ CX42 ∷ []) (wl0069 c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ CX42 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CX₁₀ • Swap ↑))) ▸ done


-- resp CX41 at 3: 6 steps
lem-resp-CX41-at-3 : WsL → ⟪ (CX41 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX42 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CX41-at-3 c4 = run b0
  where
  b0 : Chain (CX41 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX42 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 2 (Sw23 ∷ CX41 ∷ []) (wl0070 c4) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (Sw12 ∷ CX42 ∷ []) (wl0069 c4) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ CX42 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CX₁₀ • Swap ↑))) ▸ done


-- resp CSd24 at 3: 6 steps
lem-resp-CSd24-at-3 : WsL → ⟪ (CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS34⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CSd24-at-3 c4 = run b0
  where
  b0 : Chain (CS24⁻ ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS34⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 2 (Sw23 ∷ CS34⁻ ∷ []) (wl0012 c4) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (Sw12 ∷ CS34⁻ ∷ []) (sym (c₃ (Swap ↑) (CS • CS • CS))) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ CS34⁻ ∷ []) (sym (c₂ (Swap) ((CS • CS • CS) ↑))) ▸ done


-- resp CX14 at 3: 6 steps
lem-resp-CX14-at-3 : WsL → ⟪ (CX14 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX24 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CX14-at-3 c4 = run b0
  where
  b0 : Chain (CX14 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX24 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 2 (Sw23 ∷ CX14 ∷ []) (wl0071 c4) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (Sw12 ∷ CX24 ∷ []) (wl0050 c4) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ CX24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CX₀₁ • Swap ↑))) ▸ done


-- comm CS12 TOFF034: 15 steps
lem-comm-CS12-TOFF034 : WsL → ⟪ (CS12 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CS12 ∷ []) ⟫ʷ
lem-comm-CS12-TOFF034 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS12 ∷ Toff034 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ CS34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw12 ∷ CS23 ∷ []) (wl0046 c4) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ CS34 ∷ []) (wl0011 c4) ▸
       at 4 2 (Toff012 ∷ CS34 ∷ []) (sym (c₃ (Toff) (CS))) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ CS34 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Toff034 ∷ CS12 ∷ [])
  b1 = at 5 2 (Sw23 ∷ CS24 ∷ []) (wl0008 c4) ▸
       at 6 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 7 2 (Sw12 ∷ CS13 ∷ []) (wl0047 c4) ▸
       at 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (wl0003 c4) ▸
       at 0 9 (Toff034 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp SWAP14 at 2: 4 steps
lem-resp-SWAP14-at-2 : WsL → ⟪ (Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Sw24 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-SWAP14-at-2 c4 = run b0
  where
  b0 : Chain (Sw14 ∷ []) (Sw12 ∷ Sw01 ∷ Sw24 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ Sw24 ∷ []) (sym (wl0072 c4)) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ Sw24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • Swap • Swap ↑))) ▸ done


-- resp TOFF301 at 2: 5 steps
lem-resp-TOFF301-at-2 : WsL → ⟪ (Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff312 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF301-at-2 c4 = run b0
  where
  b0 : Chain (Toff301 ∷ []) (Sw12 ∷ Sw01 ∷ Toff312 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 3 (Toff302 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ Toff312 ∷ []) (sym (wl0063 c4)) ▸ done


-- comm push TOFF304 sw1 L: 110 steps
lem-comm-push-TOFF304-sw1-L : WsL → ⟪ (Toff304 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Toff304 ∷ []) ⟫ʷ
lem-comm-push-TOFF304-sw1-L c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (Toff304 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Toff204 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b1 = at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b2 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b2 = at 11 2 [] (wl0003 c4) ▸
       at 2 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b3 : Chain (Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ K2 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b3 = at 9 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 10 2 [] (wl0004 c4) ▸
       at 1 2 (K2 ∷ Sw12 ∷ []) (sym (wl0040 c4)) ▸
       at 2 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0005 c4)) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸ done

  b4 : Chain (Sw23 ∷ K2 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw12 ∷ [])
  b4 = at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0007 c4)) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 7 2 (K2 ∷ Sw12 ∷ []) (sym (wl0040 c4)) ▸
       at 8 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 9 2 [] (wl0006 c4) ▸ done

  b5 : Chain (Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw12 ∷ []) (K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw23 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw12 ∷ [])
  b5 = at 0 2 (K3 ∷ Sw23 ∷ []) (sym (wl0064 c4)) ▸
       at 1 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 c4)) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS04 ∷ Sw23 ∷ []) (lem-comm-push-CS04-sw2-R c4) ▸ done

  b6 : Chain (K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw23 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw12 ∷ []) (K3 ∷ CS34 ∷ CX03 ∷ Sw12 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K3 ∷ ι ∷ [])
  b6 = at 6 2 (K3 ∷ Sw23 ∷ []) (sym (wl0064 c4)) ▸
       at 7 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 8 2 [] (wl0003 c4) ▸
       at 7 2 (Sw12 ∷ ι ∷ []) (c₁ (iI) (Swap)) ▸
       at 6 2 (Sw12 ∷ K3 ∷ []) (sym (c₃ (Swap ↑) (K))) ▸
       at 5 2 (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L c4) ▸
       at 4 2 (Sw12 ∷ CX03 ∷ []) (wl0010 c4) ▸
       at 3 2 (Sw12 ∷ CS34⁻ ∷ []) (sym (c₃ (Swap ↑) (CS • CS • CS))) ▸ done

  b7 : Chain (K3 ∷ CS34 ∷ CX03 ∷ Sw12 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K3 ∷ ι ∷ []) (Sw12 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ Sw23 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K3 ∷ ι ∷ [])
  b7 = at 2 2 (Sw12 ∷ CX03 ∷ []) (wl0010 c4) ▸
       at 1 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 0 2 (Sw12 ∷ K3 ∷ []) (sym (c₃ (Swap ↑) (K))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 2 (K2 ∷ Sw23 ∷ []) (sym (wl0067 c4)) ▸
       at 3 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 5 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0003 c4) ▸ done

  b8 : Chain (Sw12 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ Sw23 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K3 ∷ ι ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ [])
  b8 = at 5 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 7 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 7 2 (CS04 ∷ Sw23 ∷ []) (lem-comm-push-CS04-sw2-R c4) ▸
       at 8 2 (K2 ∷ Sw23 ∷ []) (sym (wl0067 c4)) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 3 2 (K1 ∷ Sw12 ∷ []) (sym (wl0073 c4)) ▸ done

  b9 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ Sw12 ∷ ι ∷ Sw23 ∷ [])
  b9 = at 4 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 c4)) ▸
       at 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0006 c4) ▸
       at 6 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0014 c4)) ▸
       at 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0006 c4) ▸
       at 8 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 9 2 (K1 ∷ Sw12 ∷ []) (sym (wl0073 c4)) ▸ done

  b10 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ Sw12 ∷ ι ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ [])
  b10 = at 10 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 6 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0004 c4) ▸ done

  b11 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b11 = at 8 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 10 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0004 c4) ▸
       at 10 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 11 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b12 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw23 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b12 = at 6 2 [] (wl0003 c4) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0003 c4) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (wl0003 c4) ▸
       at 11 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸ done

  b13 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ Sw23 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Toff304 ∷ [])
  b13 = at 12 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 5 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff104 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff204 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff304 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push TOFF304 sw0 L: 86 steps
lem-comm-push-TOFF304-sw0-L : WsL → ⟪ (Toff304 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff314 ∷ []) ⟫ʷ
lem-comm-push-TOFF304-sw0-L c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (Toff304 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Toff204 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ [])
  b1 = at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b2 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ [])
  b2 = at 11 2 [] (wl0003 c4) ▸
       at 2 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b3 : Chain (Sw23 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ K2 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ [])
  b3 = at 9 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 10 2 [] (wl0004 c4) ▸
       at 1 2 (K2 ∷ Sw12 ∷ []) (sym (wl0040 c4)) ▸
       at 2 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0005 c4)) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸ done

  b4 : Chain (Sw23 ∷ K2 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw01 ∷ []) (Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw01 ∷ [])
  b4 = at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0007 c4)) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 7 2 (K2 ∷ Sw12 ∷ []) (sym (wl0040 c4)) ▸
       at 8 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 9 2 [] (wl0006 c4) ▸ done

  b5 : Chain (Sw23 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw01 ∷ []) (K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw23 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw01 ∷ [])
  b5 = at 0 2 (K3 ∷ Sw23 ∷ []) (sym (wl0064 c4)) ▸
       at 1 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 c4)) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS04 ∷ Sw23 ∷ []) (lem-comm-push-CS04-sw2-R c4) ▸ done

  b6 : Chain (K3 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw23 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw01 ∷ []) (K3 ∷ CS34 ∷ CX03 ∷ Sw01 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3 ∷ ι ∷ [])
  b6 = at 6 2 (K3 ∷ Sw23 ∷ []) (sym (wl0064 c4)) ▸
       at 7 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 8 2 [] (wl0003 c4) ▸
       at 7 2 (Sw01 ∷ ι ∷ []) (sym (wl0025 c4)) ▸
       at 6 2 (Sw01 ∷ K3 ∷ []) (sym (c₂ (Swap) (K ↑))) ▸
       at 5 2 (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L c4) ▸
       at 4 2 (Sw01 ∷ CX13 ∷ []) (wl0016 c4) ▸
       at 3 2 (Sw01 ∷ CS34⁻ ∷ []) (sym (c₂ (Swap) ((CS • CS • CS) ↑))) ▸ done

  b7 : Chain (K3 ∷ CS34 ∷ CX03 ∷ Sw01 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3 ∷ ι ∷ []) (Sw01 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX12 ∷ Sw23 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3 ∷ ι ∷ [])
  b7 = at 2 2 (Sw01 ∷ CX13 ∷ []) (wl0016 c4) ▸
       at 1 2 (Sw01 ∷ CS34 ∷ []) (sym (c₂ (Swap) (CS ↑))) ▸
       at 0 2 (Sw01 ∷ K3 ∷ []) (sym (c₂ (Swap) (K ↑))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 2 (K2 ∷ Sw23 ∷ []) (sym (wl0067 c4)) ▸
       at 3 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 5 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0003 c4) ▸ done

  b8 : Chain (Sw01 ∷ Sw23 ∷ K2 ∷ CS24 ∷ CX12 ∷ Sw23 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3 ∷ ι ∷ []) (Sw01 ∷ Sw23 ∷ Sw34 ∷ K2 ∷ Sw34 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2 ∷ ι ∷ Sw23 ∷ [])
  b8 = at 5 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 7 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 7 2 (CS14 ∷ Sw23 ∷ []) (sym (wl0017 c4)) ▸
       at 8 2 (K2 ∷ Sw23 ∷ []) (sym (wl0067 c4)) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 2 (K2 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ ↑) (Swap))) ▸ done

  b9 : Chain (Sw01 ∷ Sw23 ∷ Sw34 ∷ K2 ∷ Sw34 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2 ∷ ι ∷ Sw23 ∷ []) (Sw01 ∷ Sw23 ∷ Sw34 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw34 ∷ K2 ∷ ι ∷ Sw23 ∷ [])
  b9 = at 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 5 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 7 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸
       at 7 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 9 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸ done

  b10 : Chain (Sw01 ∷ Sw23 ∷ Sw34 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw34 ∷ K2 ∷ ι ∷ Sw23 ∷ []) (Sw01 ∷ Toff314 ∷ [])
  b10 = at 9 2 (K2 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ ↑) (Swap))) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 3 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (wl0041 c4) ▸
       at 3 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff314 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp TOFF304 at 2: 4 steps
lem-resp-TOFF304-at-2 : WsL → ⟪ (Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff314 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF304-at-2 c4 = run b0
  where
  b0 : Chain (Toff304 ∷ []) (Sw12 ∷ Sw01 ∷ Toff314 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ Toff304 ∷ []) (lem-comm-push-TOFF304-sw1-L c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ Toff314 ∷ []) (lem-comm-push-TOFF304-sw0-L c4) ▸ done


-- comm SWAP14 BOX(0;32): 3 steps
lem-comm-SWAP14-BOX⟨0·32⟩ : WsL → ⟪ (Sw14 ∷ Bx0-32 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-32 ∷ Sw14 ∷ []) ⟫ʷ
lem-comm-SWAP14-BOX⟨0·32⟩ c4 = run b0
  where
  b0 : Chain (Sw14 ∷ Bx0-32 ∷ []) (Bx0-32 ∷ Sw14 ∷ [])
  b0 = at 1 1 (CZ23 ∷ []) (refl) ▸
       at 0 2 (CZ23 ∷ Sw14 ∷ []) (sym (wl0061 c4)) ▸
       at 0 1 (Bx0-32 ∷ []) (refl) ▸ done


-- comm CZ23 CCZ014: 9 steps
lem-comm-CZ23-CCZ014 : WsL → ⟪ (CZ23 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CZ23 ∷ []) ⟫ʷ
lem-comm-CZ23-CCZ014 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ23 ∷ CCZ014 ∷ []) (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ CZ23 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CZ24 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ CZ34 ∷ []) (wl0034 c4) ▸
       at 2 2 (CCZ012 ∷ CZ34 ∷ []) (sym (c₃ (CCZ) (CZ))) ▸
       at 3 2 (Sw23 ∷ CZ24 ∷ []) (wl0035 c4) ▸
       at 4 1 (Sw34 ∷ CZ23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ CZ23 ∷ []) (CCZ014 ∷ CZ23 ∷ [])
  b1 = at 0 5 (CCZ014 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push TOFF023 sw3 L: 76 steps
lem-comm-push-TOFF023-sw3-L : WsL → ⟪ (Toff023 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ Toff024 ∷ []) ⟫ʷ
lem-comm-push-TOFF023-sw3-L c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (run b9)))))))))
  where
  b0 : Chain (Toff023 ∷ Sw34 ∷ []) (Sw12 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Toff013 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸ done

  b1 : Chain (Sw12 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ []) (K0 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw34 ∷ [])
  b1 = at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 0 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸ done

  b2 : Chain (K0 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw34 ∷ []) (K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ Sw12 ∷ ι ∷ Sw12 ∷ Sw34 ∷ [])
  b2 = at 1 2 (CS23 ∷ Sw12 ∷ []) (sym (wl0047 c4)) ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ Sw12 ∷ []) (sym (wl0029 c4)) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 6 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸ done

  b3 : Chain (K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ Sw12 ∷ ι ∷ Sw12 ∷ Sw34 ∷ []) (K0 ∷ CS23 ∷ CX02 ∷ Sw34 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ [])
  b3 = at 7 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 8 2 [] (wl0006 c4) ▸
       at 7 2 (Sw34 ∷ ι ∷ []) (c₁ (iI) (Swap ↑ ↑)) ▸
       at 6 2 (Sw34 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ ↑)) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸ done

  b4 : Chain (K0 ∷ CS23 ∷ CX02 ∷ Sw34 ∷ Sw34 ∷ CS23⁻ ∷ Sw34 ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ []) (Sw34 ∷ Sw12 ∷ K0 ∷ CS14 ∷ Sw12 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ [])
  b4 = at 4 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CS24 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ ↑)) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 3 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 c4)) ▸ done

  b5 : Chain (Sw34 ∷ Sw12 ∷ K0 ∷ CS14 ∷ Sw12 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ ι ∷ []) (Sw34 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ [])
  b5 = at 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0006 c4) ▸
       at 5 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0014 c4)) ▸
       at 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 7 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 8 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸ done

  b6 : Chain (Sw34 ∷ Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ []) (Sw34 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw34 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ [])
  b6 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b7 : Chain (Sw34 ∷ Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw34 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ []) (Sw34 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ [])
  b7 = at 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0004 c4) ▸
       at 9 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸ done

  b8 : Chain (Sw34 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ []) (Sw34 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ [])
  b8 = at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0003 c4) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0003 c4) ▸
       at 10 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b9 : Chain (Sw34 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) (Sw34 ∷ Toff024 ∷ [])
  b9 = at 4 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff014 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff024 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push TOFF024 sw3 L: 76 steps
lem-comm-push-TOFF024-sw3-L : WsL → ⟪ (Toff024 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ Toff023 ∷ []) ⟫ʷ
lem-comm-push-TOFF024-sw3-L c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (run b9)))))))))
  where
  b0 : Chain (Toff024 ∷ Sw34 ∷ []) (Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b1 = at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 10 2 [] (wl0003 c4) ▸ done

  b2 : Chain (Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ [])
  b2 = at 1 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 2 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸ done

  b3 : Chain (Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw34 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw34 ∷ []) (K0 ∷ CS24 ∷ CX02 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw34 ∷ [])
  b3 = at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 9 2 [] (wl0004 c4) ▸
       at 0 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 1 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0005 c4)) ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (K0 ∷ CS24 ∷ CX02 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw34 ∷ []) (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ Sw34 ∷ ι ∷ [])
  b4 = at 3 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0007 c4)) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 6 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 7 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 8 2 [] (wl0006 c4) ▸
       at 7 2 (Sw34 ∷ ι ∷ []) (c₁ (iI) (Swap ↑ ↑)) ▸ done

  b5 : Chain (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0 ∷ Sw34 ∷ ι ∷ []) (K0 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ Sw34 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ [])
  b5 = at 6 2 (Sw34 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ ↑)) ▸
       at 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0004 c4) ▸
       at 4 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸
       at 3 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 2 2 (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap)) ▸
       at 1 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (K0 ∷ Sw34 ∷ CS23 ∷ Sw34 ∷ Sw34 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ []) (Sw34 ∷ Sw12 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw12 ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ [])
  b6 = at 3 2 [] (wl0004 c4) ▸
       at 0 2 (Sw34 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ ↑)) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 3 2 (CS13 ∷ Sw12 ∷ []) (sym (wl0046 c4)) ▸
       at 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0006 c4) ▸
       at 5 2 (CS13⁻ ∷ Sw12 ∷ []) (sym (wl0028 c4)) ▸ done

  b7 : Chain (Sw34 ∷ Sw12 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw12 ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ []) (Sw34 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ [])
  b7 = at 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 7 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 8 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (Sw34 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ []) (Sw34 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw12 ∷ [])
  b8 = at 4 2 [] (wl0003 c4) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0003 c4) ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸ done

  b9 : Chain (Sw34 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ Sw23 ∷ ι ∷ Sw12 ∷ []) (Sw34 ∷ Toff023 ∷ [])
  b9 = at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 3 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff023 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm TOFF023 CSd14: 23 steps
lem-comm-TOFF023-CSd14 : WsL → ⟪ (Toff023 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Toff023 ∷ []) ⟫ʷ
lem-comm-TOFF023-CSd14 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Toff023 ∷ CS14⁻ ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ CS23⁻ ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw34 ∷ Toff024 ∷ []) (lem-comm-push-TOFF023-sw3-L c4) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (Toff034 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 10 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CS23⁻ ∷ Sw12 ∷ []) (sym (wl0029 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ CS23⁻ ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ []) (Sw34 ∷ Sw23 ∷ Sw23 ∷ CS13⁻ ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ [])
  b1 = at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 8 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 6 2 (CS34⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (CS • CS • CS)) ▸
       at 5 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 5 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0004 c4) ▸
       at 3 2 (CS13⁻ ∷ Sw12 ∷ []) (sym (wl0028 c4)) ▸ done

  b2 : Chain (Sw34 ∷ Sw23 ∷ Sw23 ∷ CS13⁻ ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ []) (CS14⁻ ∷ Toff023 ∷ [])
  b2 = at 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0003 c4) ▸
       at 3 9 (Toff034 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸
       at 4 2 (Sw34 ∷ Toff023 ∷ []) (lem-comm-push-TOFF024-sw3-L c4) ▸
       at 0 5 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CSd23 TOFF014: 9 steps
lem-comm-CSd23-TOFF014 : WsL → ⟪ (CS23⁻ ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CS23⁻ ∷ []) ⟫ʷ
lem-comm-CSd23-TOFF014 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS23⁻ ∷ Toff014 ∷ []) (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ CS23⁻ ∷ [])
  b0 = at 1 1 (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 1 3 (CS24⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ CS34⁻ ∷ []) (wl0012 c4) ▸
       at 2 2 (Toff012 ∷ CS34⁻ ∷ []) (sym (c₃ (Toff) (CS • CS • CS))) ▸
       at 3 2 (Sw23 ∷ CS24⁻ ∷ []) (wl0009 c4) ▸
       at 4 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0004 c4) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ CS23⁻ ∷ []) (Toff014 ∷ CS23⁻ ∷ [])
  b1 = at 0 5 (Toff014 ∷ []) (by-assoc Eq.refl) ▸ done


-- comm push TOFF403 sw1 L: 110 steps
lem-comm-push-TOFF403-sw1-L : WsL → ⟪ (Toff403 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Toff403 ∷ []) ⟫ʷ
lem-comm-push-TOFF403-sw1-L c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (Toff403 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Toff402 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (K3 ∷ Sw23 ∷ []) (sym (wl0064 c4)) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b1 = at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K3 ∷ Sw23 ∷ []) (sym (wl0064 c4)) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b2 : Chain (Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b2 = at 11 2 [] (wl0003 c4) ▸
       at 2 2 (K4 ∷ Sw34 ∷ []) (sym (wl0065 c4)) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 3 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 5 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b3 : Chain (Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ K4 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  b3 = at 9 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K4 ∷ Sw34 ∷ []) (sym (wl0065 c4)) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 10 2 [] (wl0004 c4) ▸
       at 1 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 2 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0005 c4)) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸ done

  b4 : Chain (Sw23 ∷ K4 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw12 ∷ [])
  b4 = at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0007 c4)) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 7 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸
       at 8 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 9 2 [] (wl0006 c4) ▸ done

  b5 : Chain (Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw12 ∷ []) (K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw23 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw12 ∷ [])
  b5 = at 0 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 1 2 (CS34 ∷ Sw23 ∷ []) (sym (wl0008 c4)) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ Sw23 ∷ []) (sym (wl0009 c4)) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CX03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS04 ∷ Sw23 ∷ []) (lem-comm-push-CS04-sw2-R c4) ▸ done

  b6 : Chain (K4 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ Sw23 ∷ K4 ∷ ι ∷ Sw23 ∷ Sw12 ∷ []) (K4 ∷ CS34 ∷ CX03 ∷ Sw12 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K4 ∷ ι ∷ [])
  b6 = at 6 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 7 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 8 2 [] (wl0003 c4) ▸
       at 7 2 (Sw12 ∷ ι ∷ []) (c₁ (iI) (Swap)) ▸
       at 6 2 (Sw12 ∷ K4 ∷ []) (sym (c₃ (Swap ↑) (K ↑))) ▸
       at 5 2 (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L c4) ▸
       at 4 2 (Sw12 ∷ CX03 ∷ []) (wl0010 c4) ▸
       at 3 2 (Sw12 ∷ CS34⁻ ∷ []) (sym (c₃ (Swap ↑) (CS • CS • CS))) ▸ done

  b7 : Chain (K4 ∷ CS34 ∷ CX03 ∷ Sw12 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K4 ∷ ι ∷ []) (Sw12 ∷ Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ Sw23 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K4 ∷ ι ∷ [])
  b7 = at 2 2 (Sw12 ∷ CX03 ∷ []) (wl0010 c4) ▸
       at 1 2 (Sw12 ∷ CS34 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 0 2 (Sw12 ∷ K4 ∷ []) (sym (c₃ (Swap ↑) (K ↑))) ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 2 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 3 2 (CS24 ∷ Sw23 ∷ []) (sym (wl0011 c4)) ▸
       at 5 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0003 c4) ▸ done

  b8 : Chain (Sw12 ∷ Sw23 ∷ K4 ∷ CS24 ∷ CX02 ∷ Sw23 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ K4 ∷ ι ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ K4 ∷ Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ Sw23 ∷ [])
  b8 = at 5 2 (CS24⁻ ∷ Sw23 ∷ []) (sym (wl0012 c4)) ▸
       at 7 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 7 2 (CS04 ∷ Sw23 ∷ []) (lem-comm-push-CS04-sw2-R c4) ▸
       at 8 2 (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K)) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 3 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸ done

  b9 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ K4 ∷ Sw12 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K4 ∷ ι ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ Sw12 ∷ ι ∷ Sw23 ∷ [])
  b9 = at 4 2 (CS14 ∷ Sw12 ∷ []) (sym (wl0013 c4)) ▸
       at 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0006 c4) ▸
       at 6 2 (CS14⁻ ∷ Sw12 ∷ []) (sym (wl0014 c4)) ▸
       at 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0006 c4) ▸
       at 8 2 (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4) ▸
       at 9 2 (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑)) ▸ done

  b10 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ K4 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K4 ∷ Sw12 ∷ ι ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ [])
  b10 = at 10 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0004 c4)) ▸
       at 4 2 (K3 ∷ Sw34 ∷ []) (sym (wl0066 c4)) ▸
       at 6 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0004 c4) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0004 c4) ▸ done

  b11 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ K3 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K4 ∷ ι ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b11 = at 8 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 10 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0004 c4) ▸
       at 10 2 (K3 ∷ Sw34 ∷ []) (sym (wl0066 c4)) ▸
       at 11 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 5 2 (K2 ∷ Sw23 ∷ []) (sym (wl0067 c4)) ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b12 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K3 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ Sw23 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ [])
  b12 = at 6 2 [] (wl0003 c4) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0003 c4) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] (wl0003 c4) ▸
       at 11 2 (K2 ∷ Sw23 ∷ []) (sym (wl0067 c4)) ▸ done

  b13 : Chain (Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ Sw23 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Toff403 ∷ [])
  b13 = at 12 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 5 8 (Toff201 ∷ []) (by-assoc Eq.refl) ▸
       at 4 3 (Toff301 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff401 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff402 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff403 ∷ []) (by-assoc Eq.refl) ▸ done

