{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R006 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0002 ; wl0003 ; wl0004 ; wl0005 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0010 ; wl0013 ; wl0019 ; wl0021 ; wl0027 ; wl0030 ; wl0031 ; wl0032 ; wl0033 ; wl0034 ; wl0037 ; wl0038 ; wl0042 ; wl0044 ; wl0047 ; wl0048 ; wl0053 ; wl0056 ; wl0059 ; wl0065 ; wl0066 ; wl0069 ; wl0078 ; wl0079 ; wl0084 ; wl0088 ; wl0092 ; wl0096 ; wl0097 ; wl0098 ; wl0099 ; wl0100 ; wl0101 ; wl0102 ; wl0103 ; wl0104 ; wl0105 ; wl0106 ; wl0107 ; wl0108 ; wl0109 ; wl0110 ; wl0111 ; wl0112 ; wl0113 ; wl0114 ; wl0115 ; wl0116 ; wl0117 ; wl0118)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-BOX⟨0·23⟩ ; lem-nat-1-BOX⟨0·24⟩ ; lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-TOFF203 ; lem-nat-2-BOX⟨0·32⟩ ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF012 ; lem-nat-2-TOFF013 ; lem-nat-2-TOFF102 ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ024 ; lem-nat-3-CZ13 ; lem-nat-3-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-CCZ013 ; lem-nat-1-CCZ014 ; lem-nat-1-TOFF103 ; lem-nat-2-TOFF201 ; lem-nat-2-TOFF304 ; lem-nat-3-CCZ023 ; lem-nat-3-TOFF203 ; lem-nat-3-TOFF402)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-CCZ014 ; lem-nat-0-TOFF104 ; lem-nat-0-TOFF412 ; lem-nat-1-TOFF104 ; lem-nat-1-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-CZ04 ; lem-nat-0-CZ14 ; lem-nat-0-TOFF204 ; lem-nat-0-TOFF214 ; lem-nat-1-TOFF013 ; lem-nat-2-TOFF104)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨0·14⟩ ; lem-nat-0-BOX⟨1·24⟩ ; lem-nat-1-BOX⟨1·04⟩ ; lem-nat-1-TOFF023 ; lem-nat-2-CCZ014)
-- nat 0 BOX(2;134): 8 steps
lem-nat-0-BOX⟨2·134⟩ : WsL → ⟪ (Sw01 ∷ Bx2-134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-034 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·134⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-134 ∷ []) (Bx2-034 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx1-24 ∷ Toff213 ∷ CCZ123 ∷ Bx1-24 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 1 2 (Toff203 ∷ Sw01 ∷ []) (wl0004 c4) ▸
       at 2 2 (Bx0-24 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·24⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw01 ∷ []) (wl0004 c4) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 5 2 (Bx0-24 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·24⟩ c4) ▸
       at 0 6 (Bx2-034 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;2034): 8 steps
lem-nat-0-BOX⟨1·2034⟩ : WsL → ⟪ (Sw01 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·2034⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-2034 ∷ []) (Bx0-2134 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx2-134 ∷ Toff102 ∷ CCZ012 ∷ Bx2-134 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 1 2 (Toff012 ∷ Sw01 ∷ []) (wl0097 c4) ▸
       at 2 2 (Bx2-034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·134⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw01 ∷ []) (wl0097 c4) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 5 2 (Bx2-034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·134⟩ c4) ▸
       at 0 6 (Bx0-2134 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;24): 2 steps
lem-nat-0-BOX⟨0·24⟩ : WsL → ⟪ (Sw01 ∷ Bx0-24 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-24 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·24⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-24 ∷ []) (Bx1-24 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Bx0-24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 0 1 (Bx1-24 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOX(2;034): 8 steps
lem-nat-0-BOX⟨2·034⟩ : WsL → ⟪ (Sw01 ∷ Bx2-034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-134 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·034⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-034 ∷ []) (Bx2-134 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 1 2 (Toff213 ∷ Sw01 ∷ []) (wl0104 c4) ▸
       at 2 2 (Bx1-24 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·24⟩ c4) ▸
       at 3 2 (Toff213 ∷ Sw01 ∷ []) (wl0104 c4) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 5 2 (Bx1-24 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·24⟩ c4) ▸
       at 0 6 (Bx2-134 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;2134): 8 steps
lem-nat-0-BOX⟨0·2134⟩ : WsL → ⟪ (Sw01 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·2134⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-2134 ∷ []) (Bx1-2034 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-034 ∷ Toff012 ∷ CCZ012 ∷ Bx2-034 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 1 2 (Toff102 ∷ Sw01 ∷ []) (wl0099 c4) ▸
       at 2 2 (Bx2-134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·034⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw01 ∷ []) (wl0099 c4) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 5 2 (Bx2-134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·034⟩ c4) ▸
       at 0 6 (Bx1-2034 ∷ []) (refl) ▸ done


-- nat 1 CZ01: 2 steps
lem-nat-1-CZ01 : WsL → ⟪ (Sw12 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CZ01 c4 = run b0
  where
  b0 : Chain (Sw12 ∷ CZ01 ∷ []) (CZ02 ∷ Sw12 ∷ [])
  b0 = at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 3 (CZ02 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 CZ02: 2 steps
lem-nat-1-CZ02 : WsL → ⟪ (Sw12 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CZ02 c4 = run b0
  where
  b0 : Chain (Sw12 ∷ CZ02 ∷ []) (CZ01 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ CZ01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0001 c4) ▸ done


-- nat 1 BOX(2;014): 8 steps
lem-nat-1-BOX⟨2·014⟩ : WsL → ⟪ (Sw12 ∷ Bx2-014 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-024 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·014⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-014 ∷ []) (Bx1-024 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 1 2 (Toff102 ∷ Sw12 ∷ []) (wl0044 c4) ▸
       at 2 2 (Bx0-14 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·24⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw12 ∷ []) (wl0044 c4) ▸
       at 4 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 5 2 (Bx0-14 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·24⟩ c4) ▸
       at 0 6 (Bx1-024 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;2314): 8 steps
lem-nat-1-BOX⟨0·2314⟩ : WsL → ⟪ (Sw12 ∷ Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·2314⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-2314 ∷ []) (Bx0-1324 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-014 ∷ Toff023 ∷ CCZ023 ∷ Bx2-014 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 2 2 (Bx1-024 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·014⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx1-024 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·014⟩ c4) ▸
       at 0 6 (Bx0-1324 ∷ []) (refl) ▸ done


-- nat 1 CX20: 2 steps
lem-nat-1-CX20 : WsL → ⟪ (Sw12 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CX20 c4 = run b0
  where
  b0 : Chain (Sw12 ∷ CX20 ∷ []) (CX10 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ CX10 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0001 c4) ▸ done


-- nat 1 CX10: 2 steps
lem-nat-1-CX10 : WsL → ⟪ (Sw12 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CX10 c4 = run b0
  where
  b0 : Chain (Sw12 ∷ CX10 ∷ []) (CX20 ∷ Sw12 ∷ [])
  b0 = at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 3 (CX20 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CZ02 at 1: 2 steps
lem-resp-CZ02-at-1 : WsL → ⟪ (CZ02 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CZ12 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CZ02-at-1 c4 = run b0
  where
  b0 : Chain (CZ02 ∷ []) (Sw01 ∷ CZ12 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 0 2 (Sw01 ∷ CZ12 ∷ []) (wl0105 c4) ▸ done


-- resp CX20 at 1: 2 steps
lem-resp-CX20-at-1 : WsL → ⟪ (CX20 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX21 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CX20-at-1 c4 = run b0
  where
  b0 : Chain (CX20 ∷ []) (Sw01 ∷ CX21 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 0 2 (Sw01 ∷ CX21 ∷ []) (wl0106 c4) ▸ done


-- nat 2 CZ13: 2 steps
lem-nat-2-CZ13 : WsL → ⟪ (Sw23 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CZ13 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CZ13 ∷ []) (CZ12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0006 c4) ▸ done


-- nat 2 BOX(0;13): 3 steps
lem-nat-2-BOX⟨0·13⟩ : WsL → ⟪ (Sw23 ∷ Bx0-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-12 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·13⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-13 ∷ []) (Bx0-12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ12 ∷ Sw23 ∷ []) (lem-nat-2-CZ13 c4) ▸
       at 0 1 (Bx0-12 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;043): 8 steps
lem-nat-2-BOX⟨1·043⟩ : WsL → ⟪ (Sw23 ∷ Bx1-043 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-042 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·043⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-043 ∷ []) (Bx1-042 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Toff104 ∷ CCZ014 ∷ Bx0-13 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4) ▸
       at 2 2 (Bx0-12 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·13⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 5 2 (Bx0-12 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·13⟩ c4) ▸
       at 0 6 (Bx1-042 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;1243): 8 steps
lem-nat-2-BOX⟨0·1243⟩ : WsL → ⟪ (Sw23 ∷ Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·1243⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-1243 ∷ []) (Bx0-1342 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-043 ∷ Toff012 ∷ CCZ012 ∷ Bx1-043 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 2 2 (Bx1-042 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·043⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4) ▸
       at 4 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 5 2 (Bx1-042 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·043⟩ c4) ▸
       at 0 6 (Bx0-1342 ∷ []) (refl) ▸ done


-- nat 3 CZ24: 2 steps
lem-nat-3-CZ24 : WsL → ⟪ (Sw34 ∷ CZ24 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CZ24 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CZ24 ∷ []) (CZ23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CZ23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0007 c4) ▸ done


-- nat 3 BOX(0;24): 3 steps
lem-nat-3-BOX⟨0·24⟩ : WsL → ⟪ (Sw34 ∷ Bx0-24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-23 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·24⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-24 ∷ []) (Bx0-23 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ24 ∷ []) (refl) ▸
       at 0 2 (CZ23 ∷ Sw34 ∷ []) (lem-nat-3-CZ24 c4) ▸
       at 0 1 (Bx0-23 ∷ []) (refl) ▸ done


-- nat 3 BOX(2;034): 8 steps
lem-nat-3-BOX⟨2·034⟩ : WsL → ⟪ (Sw34 ∷ Bx2-034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-043 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·034⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx2-034 ∷ []) (Bx2-043 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 1 2 (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 c4) ▸
       at 2 2 (Bx0-23 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·24⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 c4) ▸
       at 4 2 (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4) ▸
       at 5 2 (Bx0-23 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·24⟩ c4) ▸
       at 0 6 (Bx2-043 ∷ []) (refl) ▸ done


-- nat 3 BOX(0;2134): 8 steps
lem-nat-3-BOX⟨0·2134⟩ : WsL → ⟪ (Sw34 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·2134⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx0-2134 ∷ []) (Bx0-2143 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-034 ∷ Toff012 ∷ CCZ012 ∷ Bx2-034 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 1 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 2 2 (Bx2-043 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·034⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw34 ∷ []) (sym (c₃ (Toff) (Swap))) ▸
       at 4 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 5 2 (Bx2-043 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·034⟩ c4) ▸
       at 0 6 (Bx0-2143 ∷ []) (refl) ▸ done


-- nat 2 CZ12: 2 steps
lem-nat-2-CZ12 : WsL → ⟪ (Sw23 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CZ12 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CZ12 ∷ []) (CZ13 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 0 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 BOX(0;12): 3 steps
lem-nat-2-BOX⟨0·12⟩ : WsL → ⟪ (Sw23 ∷ Bx0-12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-13 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·12⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-12 ∷ []) (Bx0-13 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw23 ∷ []) (lem-nat-2-CZ12 c4) ▸
       at 0 1 (Bx0-13 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;042): 8 steps
lem-nat-2-BOX⟨1·042⟩ : WsL → ⟪ (Sw23 ∷ Bx1-042 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-043 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·042⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-042 ∷ []) (Bx1-043 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 1 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4) ▸
       at 2 2 (Bx0-13 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·12⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4) ▸
       at 5 2 (Bx0-13 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·12⟩ c4) ▸
       at 0 6 (Bx1-043 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;1342): 8 steps
lem-nat-2-BOX⟨0·1342⟩ : WsL → ⟪ (Sw23 ∷ Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·1342⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-1342 ∷ []) (Bx0-1243 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-042 ∷ Toff013 ∷ CCZ013 ∷ Bx1-042 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 2 2 (Bx1-043 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·042⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 4 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 5 2 (Bx1-043 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·042⟩ c4) ▸
       at 0 6 (Bx0-1243 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;043): 8 steps
lem-nat-1-BOX⟨2·043⟩ : WsL → ⟪ (Sw12 ∷ Bx2-043 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-043 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·043⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-043 ∷ []) (Bx1-043 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ CCZ024 ∷ Bx0-23 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 2 2 (Bx0-13 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·23⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx0-13 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·23⟩ c4) ▸
       at 0 6 (Bx1-043 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;2143): 8 steps
lem-nat-1-BOX⟨0·2143⟩ : WsL → ⟪ (Sw12 ∷ Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·2143⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-2143 ∷ []) (Bx0-1243 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-043 ∷ Toff012 ∷ CCZ012 ∷ Bx2-043 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 1 2 (Toff012 ∷ Sw12 ∷ []) (wl0038 c4) ▸
       at 2 2 (Bx1-043 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·043⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw12 ∷ []) (wl0038 c4) ▸
       at 4 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 5 2 (Bx1-043 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·043⟩ c4) ▸
       at 0 6 (Bx0-1243 ∷ []) (refl) ▸ done


-- nat 2 BOX(3;042): 8 steps
lem-nat-2-BOX⟨3·042⟩ : WsL → ⟪ (Sw23 ∷ Bx3-042 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-043 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·042⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx3-042 ∷ []) (Bx2-043 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 1 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4) ▸
       at 2 2 (Bx0-23 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·32⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4) ▸
       at 4 2 (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4) ▸
       at 5 2 (Bx0-23 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·32⟩ c4) ▸
       at 0 6 (Bx2-043 ∷ []) (refl) ▸ done


-- nat 2 BOX(0;3142): 8 steps
lem-nat-2-BOX⟨0·3142⟩ : WsL → ⟪ (Sw23 ∷ Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·3142⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-3142 ∷ []) (Bx0-2143 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-042 ∷ Toff013 ∷ CCZ013 ∷ Bx3-042 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 1 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 2 2 (Bx2-043 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·042⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 4 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 5 2 (Bx2-043 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·042⟩ c4) ▸
       at 0 6 (Bx0-2143 ∷ []) (refl) ▸ done


-- resp TOFF104 at 2: 74 steps
lem-resp-TOFF104-at-2 : WsL → ⟪ (Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff214 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF104-at-2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (run b9)))))))))
  where
  b0 : Chain (Toff104 ∷ []) (Sw12 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 1 3 (Toff204 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 1 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b1 = at 3 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 6 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸ done

  b2 : Chain (Sw12 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b2 = at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 11 2 [] (wl0006 c4) ▸
       at 2 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 3 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b3 : Chain (Sw12 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ Sw34 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b3 = at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 5 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 9 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 10 2 [] (wl0007 c4) ▸ done

  b4 : Chain (Sw12 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw12 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b4 = at 1 2 (K2 ∷ Sw12 ∷ []) (sym (wl0056 c4)) ▸
       at 2 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 c4)) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 3 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0009 c4)) ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 5 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (Sw12 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw12 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ Sw01 ∷ ι ∷ Sw01 ∷ Sw12 ∷ [])
  b5 = at 6 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 7 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 8 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K2 ∷ Sw12 ∷ []) (sym (wl0056 c4)) ▸
       at 8 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 9 2 [] (wl0001 c4) ▸
       at 8 2 (Sw01 ∷ ι ∷ []) (sym (wl0030 c4)) ▸ done

  b6 : Chain (Sw12 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K2 ∷ Sw01 ∷ ι ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ K2 ∷ CS24 ∷ CX02 ∷ Sw01 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw12 ∷ [])
  b6 = at 7 2 (Sw01 ∷ K2 ∷ []) (sym (c₂ (Swap) (K))) ▸
       at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 7 2 (Sw01 ∷ CS13 ∷ []) (wl0019 c4) ▸
       at 6 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 7 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ CX12 ∷ []) (wl0048 c4) ▸
       at 4 2 (Sw01 ∷ CS24⁻ ∷ []) (sym (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸ done

  b7 : Chain (Sw12 ∷ K2 ∷ CS24 ∷ CX02 ∷ Sw01 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw34 ∷ K2 ∷ CS23 ∷ CX12 ∷ Sw34 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw12 ∷ [])
  b7 = at 3 2 (Sw01 ∷ CX12 ∷ []) (wl0048 c4) ▸
       at 2 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸
       at 1 2 (Sw01 ∷ K2 ∷ []) (sym (c₂ (Swap) (K))) ▸
       at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 3 2 (K2 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ ↑) (Swap))) ▸
       at 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0007 c4) ▸
       at 5 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸ done

  b8 : Chain (Sw12 ∷ Sw01 ∷ Sw34 ∷ K2 ∷ CS23 ∷ CX12 ∷ Sw34 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Sw34 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw34 ∷ Sw01 ∷ Sw12 ∷ [])
  b8 = at 7 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0007 c4) ▸
       at 7 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 9 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0007 c4) ▸
       at 9 2 (K2 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ ↑) (Swap))) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 3 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (wl0059 c4) ▸ done

  b9 : Chain (Sw12 ∷ Sw01 ∷ Sw34 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ Sw34 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ Toff214 ∷ Sw01 ∷ Sw12 ∷ [])
  b9 = at 3 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp TOFF104 at 3: 143 steps
lem-resp-TOFF104-at-3 : WsL → ⟪ (Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff214 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF104-at-3 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (run b17)))))))))))))))))
  where
  b0 : Chain (Toff104 ∷ []) (Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 0 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸ done

  b1 : Chain (Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ []) (Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ [])
  b1 = at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 8 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 9 2 [] (wl0006 c4) ▸ done

  b2 : Chain (Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ []) (K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ [])
  b2 = at 0 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 1 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 5 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 3 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 7 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸ done

  b3 : Chain (K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw23 ∷ Sw23 ∷ []) (K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw23 ∷ [])
  b3 = at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 7 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 8 2 [] (wl0007 c4) ▸
       at 7 2 (Sw23 ∷ ι ∷ []) (c₁ (iI) (Swap ↑)) ▸
       at 6 2 (Sw23 ∷ K1 ∷ []) (c₂ (K ↑) (Swap)) ▸
       at 5 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 10 3 (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4) ▸ done

  b4 : Chain (K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw23 ∷ []) (K1 ∷ CS14 ∷ Sw23 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw23 ∷ [])
  b4 = at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 2 (Sw34 ∷ CS01 ∷ []) (c₂ (CS) (Swap ↑)) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 5 3 (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (sym (wl0013 c4)) ▸
       at 6 7 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw23 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap)) ▸
       at 3 2 (Sw23 ∷ CS14⁻ ∷ []) (wl0033 c4) ▸
       at 2 2 (Sw23 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap)) ▸ done

  b5 : Chain (K1 ∷ CS14 ∷ Sw23 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw34 ∷ Sw34 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw23 ∷ [])
  b5 = at 1 2 (Sw23 ∷ CS14 ∷ []) (wl0021 c4) ▸
       at 0 2 (Sw23 ∷ K1 ∷ []) (c₂ (K ↑) (Swap)) ▸
       at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 2 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0007 c4) ▸
       at 4 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (Sw23 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ Sw34 ∷ Sw34 ∷ CS13⁻ ∷ Sw34 ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw23 ∷ [])
  b6 = at 5 2 [] (wl0007 c4) ▸
       at 6 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0007 c4) ▸
       at 8 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸ done

  b7 : Chain (Sw23 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw23 ∷ [])
  b7 = at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0006 c4) ▸
       at 5 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] (wl0006 c4) ▸ done

  b8 : Chain (Sw23 ∷ Sw34 ∷ Sw23 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Toff204 ∷ Sw12 ∷ Sw23 ∷ [])
  b8 = at 9 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 10 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸
       at 3 8 (Toff102 ∷ []) (by-assoc Eq.refl) ▸
       at 2 3 (Toff103 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff104 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 2 3 (Toff204 ∷ []) (by-assoc Eq.refl) ▸ done

  b9 : Chain (Sw23 ∷ Sw12 ∷ Toff204 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b9 = at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 2 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b10 = at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 7 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (K1 ∷ Sw23 ∷ []) (sym (c₂ (K ↑) (Swap))) ▸
       at 11 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b11 : Chain (Sw23 ∷ Sw12 ∷ Sw12 ∷ Sw34 ∷ K1 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K1 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b11 = at 12 2 [] (wl0006 c4) ▸
       at 3 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 6 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b12 : Chain (Sw23 ∷ Sw12 ∷ Sw12 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K1 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ K2 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b12 = at 10 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 8 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 10 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 11 2 [] (wl0007 c4) ▸
       at 2 2 (K2 ∷ Sw12 ∷ []) (sym (wl0056 c4)) ▸
       at 3 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 c4)) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸ done

  b13 : Chain (Sw23 ∷ Sw12 ∷ K2 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b13 = at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0009 c4)) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 8 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 9 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b14 : Chain (Sw23 ∷ Sw12 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K1 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw01 ∷ Sw34 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b14 = at 7 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K2 ∷ Sw12 ∷ []) (sym (wl0056 c4)) ▸
       at 9 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 10 2 [] (wl0001 c4) ▸
       at 9 2 (Sw01 ∷ ι ∷ []) (sym (wl0030 c4)) ▸
       at 8 2 (Sw01 ∷ K2 ∷ []) (sym (c₂ (Swap) (K))) ▸
       at 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸ done

  b15 : Chain (Sw23 ∷ Sw12 ∷ K2 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw01 ∷ Sw34 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b15 = at 8 2 (Sw01 ∷ CS13 ∷ []) (wl0019 c4) ▸
       at 7 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 8 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ CX12 ∷ []) (wl0048 c4) ▸
       at 5 2 (Sw01 ∷ CS24⁻ ∷ []) (sym (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 4 2 (Sw01 ∷ CX12 ∷ []) (wl0048 c4) ▸
       at 3 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸
       at 2 2 (Sw01 ∷ K2 ∷ []) (sym (c₂ (Swap) (K))) ▸ done

  b16 : Chain (Sw23 ∷ Sw12 ∷ Sw01 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw34 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw34 ∷ CS14 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b16 = at 3 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 2 (K2 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ ↑) (Swap))) ▸
       at 6 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0007 c4) ▸
       at 6 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 8 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0007 c4) ▸
       at 8 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸ done

  b17 : Chain (Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw34 ∷ K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw34 ∷ CS14 ∷ K2 ∷ ι ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff214 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b17 = at 10 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] (wl0007 c4) ▸
       at 10 2 (K2 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ ↑) (Swap))) ▸
       at 11 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 4 8 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (wl0059 c4) ▸
       at 4 8 (Toff213 ∷ []) (by-assoc Eq.refl) ▸
       at 3 3 (Toff214 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOX(2;014): 8 steps
lem-nat-0-BOX⟨2·014⟩ : WsL → ⟪ (Sw01 ∷ Bx2-014 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-104 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·014⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-014 ∷ []) (Bx2-104 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 1 2 (Toff201 ∷ Sw01 ∷ []) (wl0107 c4) ▸
       at 2 2 (Bx1-24 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·24⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw01 ∷ []) (wl0107 c4) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 5 2 (Bx1-24 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·24⟩ c4) ▸
       at 0 6 (Bx2-104 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;2314): 8 steps
lem-nat-0-BOX⟨0·2314⟩ : WsL → ⟪ (Sw01 ∷ Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2304 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·2314⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-2314 ∷ []) (Bx1-2304 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-014 ∷ Toff023 ∷ CCZ023 ∷ Bx2-014 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 1 2 (Toff123 ∷ Sw01 ∷ []) (wl0108 c4) ▸
       at 2 2 (Bx2-104 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·014⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw01 ∷ []) (wl0108 c4) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 5 2 (Bx2-104 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·014⟩ c4) ▸
       at 0 6 (Bx1-2304 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;104): 8 steps
lem-nat-0-BOX⟨2·104⟩ : WsL → ⟪ (Sw01 ∷ Bx2-104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-014 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·104⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-104 ∷ []) (Bx2-014 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx1-24 ∷ Toff201 ∷ CCZ012 ∷ Bx1-24 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 1 2 (Toff201 ∷ Sw01 ∷ []) (wl0107 c4) ▸
       at 2 2 (Bx0-24 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·24⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw01 ∷ []) (wl0107 c4) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 5 2 (Bx0-24 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·24⟩ c4) ▸
       at 0 6 (Bx2-014 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;2304): 8 steps
lem-nat-0-BOX⟨1·2304⟩ : WsL → ⟪ (Sw01 ∷ Bx1-2304 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·2304⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-2304 ∷ []) (Bx0-2314 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx2-104 ∷ Toff123 ∷ CCZ123 ∷ Bx2-104 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 1 2 (Toff023 ∷ Sw01 ∷ []) (wl0053 c4) ▸
       at 2 2 (Bx2-014 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·104⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw01 ∷ []) (wl0053 c4) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 5 2 (Bx2-014 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·104⟩ c4) ▸
       at 0 6 (Bx0-2314 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;23): 2 steps
lem-nat-0-BOX⟨0·23⟩ : WsL → ⟪ (Sw01 ∷ Bx0-23 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-23 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·23⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-23 ∷ []) (Bx1-23 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Bx0-23 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ)) ▸
       at 0 1 (Bx1-23 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOX(2;043): 8 steps
lem-nat-0-BOX⟨2·043⟩ : WsL → ⟪ (Sw01 ∷ Bx2-043 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-143 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·043⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-043 ∷ []) (Bx2-143 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ CCZ024 ∷ Bx0-23 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4) ▸
       at 2 2 (Bx1-23 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·23⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 5 2 (Bx1-23 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·23⟩ c4) ▸
       at 0 6 (Bx2-143 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;2143): 8 steps
lem-nat-0-BOX⟨0·2143⟩ : WsL → ⟪ (Sw01 ∷ Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2043 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·2143⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-2143 ∷ []) (Bx1-2043 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-043 ∷ Toff012 ∷ CCZ012 ∷ Bx2-043 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 1 2 (Toff102 ∷ Sw01 ∷ []) (wl0099 c4) ▸
       at 2 2 (Bx2-143 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·043⟩ c4) ▸
       at 3 2 (Toff102 ∷ Sw01 ∷ []) (wl0099 c4) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 5 2 (Bx2-143 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·043⟩ c4) ▸
       at 0 6 (Bx1-2043 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;23): 2 steps
lem-nat-0-BOX⟨1·23⟩ : WsL → ⟪ (Sw01 ∷ Bx1-23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-23 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·23⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-23 ∷ []) (Bx0-23 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Bx1-23 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ)) ▸
       at 0 1 (Bx0-23 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOX(2;143): 8 steps
lem-nat-0-BOX⟨2·143⟩ : WsL → ⟪ (Sw01 ∷ Bx2-143 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-043 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·143⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-143 ∷ []) (Bx2-043 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff214 ∷ Bx1-23 ∷ Toff214 ∷ CCZ124 ∷ Bx1-23 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 1 2 (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4) ▸
       at 2 2 (Bx0-23 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·23⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4) ▸
       at 4 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 5 2 (Bx0-23 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·23⟩ c4) ▸
       at 0 6 (Bx2-043 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;2043): 8 steps
lem-nat-0-BOX⟨1·2043⟩ : WsL → ⟪ (Sw01 ∷ Bx1-2043 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·2043⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-2043 ∷ []) (Bx0-2143 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx2-143 ∷ Toff102 ∷ CCZ012 ∷ Bx2-143 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 1 2 (Toff012 ∷ Sw01 ∷ []) (wl0097 c4) ▸
       at 2 2 (Bx2-043 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·143⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw01 ∷ []) (wl0097 c4) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 5 2 (Bx2-043 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·143⟩ c4) ▸
       at 0 6 (Bx0-2143 ∷ []) (refl) ▸ done


-- resp TOFF023 at 1: 2 steps
lem-resp-TOFF023-at-1 : WsL → ⟪ (Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF023-at-1 c4 = run b0
  where
  b0 : Chain (Toff023 ∷ []) (Sw01 ∷ Toff123 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 0 2 (Sw01 ∷ Toff123 ∷ []) (sym (wl0053 c4)) ▸ done


-- resp CZ04 at 2: 12 steps
lem-resp-CZ04-at-2 : WsL → ⟪ (CZ04 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CZ14 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CZ04-at-2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CZ04 ∷ []) (Sw12 ∷ Sw34 ∷ CZ03 ∷ Sw34 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 1 (Sw34 ∷ CZ03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 1 2 (Sw12 ∷ CZ03 ∷ []) (wl0098 c4) ▸
       at 0 2 (Sw12 ∷ Sw34 ∷ []) (sym (c₃ (Swap ↑) (Swap))) ▸
       at 1 3 (CZ04 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 1 1 (Sw34 ∷ CZ03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ CZ03 ∷ Sw34 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ []) (Sw12 ∷ Sw01 ∷ CZ14 ∷ Sw01 ∷ Sw12 ∷ [])
  b1 = at 3 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 2 2 (Sw01 ∷ CZ13 ∷ []) (wl0088 c4) ▸
       at 1 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 2 3 (CZ14 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CZ04 at 1: 6 steps
lem-resp-CZ04-at-1 : WsL → ⟪ (CZ04 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CZ14 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CZ04-at-1 c4 = run b0
  where
  b0 : Chain (CZ04 ∷ []) (Sw01 ∷ CZ14 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 0 1 (Sw34 ∷ CZ03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 2 (Sw01 ∷ CZ13 ∷ []) (wl0088 c4) ▸
       at 0 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 3 (CZ14 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 BOX(0;21): 3 steps
lem-nat-1-BOX⟨0·21⟩ : WsL → ⟪ (Sw12 ∷ Bx0-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-12 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·21⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-21 ∷ []) (Bx0-12 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (CZ12 ∷ Sw12 ∷ []) (sym (wl0109 c4)) ▸
       at 0 1 (Bx0-12 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;041): 8 steps
lem-nat-1-BOX⟨2·041⟩ : WsL → ⟪ (Sw12 ∷ Bx2-041 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-042 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·041⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-041 ∷ []) (Bx1-042 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 1 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 2 2 (Bx0-12 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·21⟩ c4) ▸
       at 3 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 4 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 5 2 (Bx0-12 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·21⟩ c4) ▸
       at 0 6 (Bx1-042 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;2341): 8 steps
lem-nat-1-BOX⟨0·2341⟩ : WsL → ⟪ (Sw12 ∷ Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·2341⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-2341 ∷ []) (Bx0-1342 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-041 ∷ Toff023 ∷ CCZ023 ∷ Bx2-041 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 1 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 2 2 (Bx1-042 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·041⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4) ▸
       at 4 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 5 2 (Bx1-042 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·041⟩ c4) ▸
       at 0 6 (Bx0-1342 ∷ []) (refl) ▸ done


-- nat 1 CS01: 2 steps
lem-nat-1-CS01 : WsL → ⟪ (Sw12 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CS01 c4 = run b0
  where
  b0 : Chain (Sw12 ∷ CS01 ∷ []) (CS02 ∷ Sw12 ∷ [])
  b0 = at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 3 (CS02 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 CS02: 2 steps
lem-nat-1-CS02 : WsL → ⟪ (Sw12 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CS02 c4 = run b0
  where
  b0 : Chain (Sw12 ∷ CS02 ∷ []) (CS01 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0001 c4) ▸ done


-- nat 1 BOX(0;12): 3 steps
lem-nat-1-BOX⟨0·12⟩ : WsL → ⟪ (Sw12 ∷ Bx0-12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-21 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·12⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-12 ∷ []) (Bx0-21 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ12 ∷ []) (refl) ▸
       at 0 2 (CZ12 ∷ Sw12 ∷ []) (sym (wl0109 c4)) ▸
       at 0 1 (Bx0-21 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;042): 8 steps
lem-nat-1-BOX⟨1·042⟩ : WsL → ⟪ (Sw12 ∷ Bx1-042 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-041 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·042⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-042 ∷ []) (Bx2-041 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 1 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 2 2 (Bx0-21 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·12⟩ c4) ▸
       at 3 2 (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4) ▸
       at 4 2 (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4) ▸
       at 5 2 (Bx0-21 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·12⟩ c4) ▸
       at 0 6 (Bx2-041 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;1342): 8 steps
lem-nat-1-BOX⟨0·1342⟩ : WsL → ⟪ (Sw12 ∷ Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·1342⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-1342 ∷ []) (Bx0-2341 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-042 ∷ Toff013 ∷ CCZ013 ∷ Bx1-042 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 2 2 (Bx2-041 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·042⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx2-041 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·042⟩ c4) ▸
       at 0 6 (Bx0-2341 ∷ []) (refl) ▸ done


-- resp TOFF024 at 1: 71 steps
lem-resp-TOFF024-at-1 : WsL → ⟪ (Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff124 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF024-at-1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (Toff024 ∷ []) (Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 0 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ []) (Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ [])
  b1 = at 4 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX01 ∷ Sw23 ∷ []) (sym (c₂ (CX₀₁) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 7 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (c₁ (K) (Swap ↑))) ▸
       at 9 2 (ι ∷ Sw23 ∷ []) (sym (c₁ (iI) (Swap ↑))) ▸ done

  b2 : Chain (Sw12 ∷ Sw34 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ []) (Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ [])
  b2 = at 10 2 [] (wl0006 c4) ▸
       at 1 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 4 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 2 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸
       at 6 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 4 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CX01 ∷ Sw34 ∷ []) (sym (c₂ (CX₀₁) (Swap ↑))) ▸ done

  b3 : Chain (Sw12 ∷ K0 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Sw34 ∷ CS03 ∷ K0 ∷ ι ∷ Sw34 ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ []) (K0 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ [])
  b3 = at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 6 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw34 ∷ []) (sym (c₁ (K) (Swap ↑ ↑))) ▸
       at 8 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 9 2 [] (wl0007 c4) ▸
       at 0 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 1 2 (CS24 ∷ Sw12 ∷ []) (sym (wl0008 c4)) ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸ done

  b4 : Chain (K0 ∷ CS24 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ []) (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ [])
  b4 = at 2 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS24⁻ ∷ Sw12 ∷ []) (sym (wl0009 c4)) ▸
       at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 4 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸
       at 6 2 (CS03 ∷ Sw12 ∷ []) (sym (wl0010 c4)) ▸
       at 7 2 (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap)) ▸ done

  b5 : Chain (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw34 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw01 ∷ Sw01 ∷ []) (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw01 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw01 ∷ [])
  b5 = at 5 3 (CS04 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw12 ∷ []) (sym (c₁ (K) (Swap))) ▸
       at 7 2 (ι ∷ Sw12 ∷ []) (sym (c₁ (iI) (Swap))) ▸
       at 8 2 [] (wl0001 c4) ▸
       at 7 2 (Sw01 ∷ ι ∷ []) (sym (wl0030 c4)) ▸
       at 6 2 (Sw01 ∷ K1 ∷ []) (wl0031 c4) ▸
       at 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸ done

  b6 : Chain (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Sw34 ∷ CS03 ∷ Sw01 ∷ Sw34 ∷ K1 ∷ ι ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ [])
  b6 = at 6 2 (Sw01 ∷ CS13 ∷ []) (wl0019 c4) ▸
       at 5 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 6 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ CX12 ∷ []) (wl0048 c4) ▸
       at 3 2 (Sw01 ∷ CS24⁻ ∷ []) (sym (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 2 2 (Sw01 ∷ CX12 ∷ []) (wl0048 c4) ▸
       at 1 2 (Sw01 ∷ CS24 ∷ []) (sym (c₂ (Swap) (Swap ↑ • CS • Swap ↑))) ▸
       at 0 2 (Sw01 ∷ K1 ∷ []) (wl0031 c4) ▸ done

  b7 : Chain (Sw01 ∷ K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ []) (Sw01 ∷ Sw34 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw34 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ [])
  b7 = at 1 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 2 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 4 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0007 c4) ▸
       at 4 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸
       at 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0007 c4) ▸
       at 6 2 (CX12 ∷ Sw34 ∷ []) (sym (c₃ (CX₀₁ ↑) (Swap))) ▸ done

  b8 : Chain (Sw01 ∷ Sw34 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw34 ∷ CS14 ∷ K1 ∷ ι ∷ Sw01 ∷ []) (Sw01 ∷ Toff124 ∷ Sw01 ∷ [])
  b8 = at 8 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] (wl0007 c4) ▸
       at 8 2 (K1 ∷ Sw34 ∷ []) (sym (c₂ (K ↑) (Swap ↑))) ▸
       at 9 2 (ι ∷ Sw34 ∷ []) (sym (c₁ (iI) (Swap ↑ ↑))) ▸
       at 2 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (wl0032 c4) ▸
       at 2 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 1 3 (Toff124 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CZ03 at 1: 2 steps
lem-resp-CZ03-at-1 : WsL → ⟪ (CZ03 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CZ13 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CZ03-at-1 c4 = run b0
  where
  b0 : Chain (CZ03 ∷ []) (Sw01 ∷ CZ13 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 0 2 (Sw01 ∷ CZ13 ∷ []) (wl0088 c4) ▸ done


-- resp TOFF301 at 2: 5 steps
lem-resp-TOFF301-at-2 : WsL → ⟪ (Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff312 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF301-at-2 c4 = run b0
  where
  b0 : Chain (Toff301 ∷ []) (Sw12 ∷ Sw01 ∷ Toff312 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0001 c4)) ▸
       at 1 3 (Toff302 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 1 2 (Sw01 ∷ Toff312 ∷ []) (sym (wl0110 c4)) ▸ done


-- nat 2 BOXd(0;14): 3 steps
lem-nat-2-BOXd⟨0·14⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻0-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-14 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·14⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻0-14 ∷ []) (Bx⁻0-14 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ14 ∷ Sw23 ∷ []) (sym (wl0042 c4)) ▸
       at 0 1 (Bx⁻0-14 ∷ []) (refl) ▸ done


-- nat 2 BOXd(1;024): 8 steps
lem-nat-2-BOXd⟨1·024⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻1-024 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-034 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·024⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻1-024 ∷ []) (Bx⁻1-034 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻0-14 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻0-14 ∷ Toff102 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-14 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·14⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 2 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 3 2 (Bx⁻0-14 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·14⟩ c4) ▸
       at 4 2 (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4) ▸
       at 5 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 0 6 (Bx⁻1-034 ∷ []) (refl) ▸ done


-- nat 2 BOXd(0;1324): 8 steps
lem-nat-2-BOXd⟨0·1324⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-1234 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·1324⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻0-1324 ∷ []) (Bx⁻0-1234 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻1-024 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻1-024 ∷ Toff013 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-034 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·024⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 3 2 (Bx⁻1-034 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·024⟩ c4) ▸
       at 4 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 5 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 0 6 (Bx⁻0-1234 ∷ []) (refl) ▸ done


-- nat 3 BOXd(0;13): 3 steps
lem-nat-3-BOXd⟨0·13⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻0-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-14 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·13⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻0-13 ∷ []) (Bx⁻0-14 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ13 ∷ []) (refl) ▸
       at 0 2 (CZ14 ∷ Sw34 ∷ []) (lem-nat-3-CZ13 c4) ▸
       at 0 1 (Bx⁻0-14 ∷ []) (refl) ▸ done


-- nat 3 BOXd(1;023): 8 steps
lem-nat-3-BOXd⟨1·023⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻1-023 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-024 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨1·023⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻1-023 ∷ []) (Bx⁻1-024 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻0-13 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻0-13 ∷ Toff102 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-14 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·13⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 2 2 (Toff102 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (Swap))) ▸
       at 3 2 (Bx⁻0-14 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·13⟩ c4) ▸
       at 4 2 (Toff102 ∷ Sw34 ∷ []) (sym (c₃ (K ↑ • CCZ • K ↑ • iI) (Swap))) ▸
       at 5 2 (CCZ012 ∷ Sw34 ∷ []) (sym (c₃ (CCZ) (Swap))) ▸
       at 0 6 (Bx⁻1-024 ∷ []) (refl) ▸ done


-- nat 3 BOXd(0;1423): 8 steps
lem-nat-3-BOXd⟨0·1423⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-1324 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·1423⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻0-1423 ∷ []) (Bx⁻0-1324 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻1-023 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻1-023 ∷ Toff014 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-024 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·023⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 2 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4) ▸
       at 3 2 (Bx⁻1-024 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·023⟩ c4) ▸
       at 4 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4) ▸
       at 5 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 0 6 (Bx⁻0-1324 ∷ []) (refl) ▸ done


-- nat 0 BOXd(1;03): 3 steps
lem-nat-0-BOXd⟨1·03⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻1-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-13 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·03⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻1-03 ∷ []) (Bx⁻0-13 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ13 ∷ Sw01 ∷ []) (sym (wl0092 c4)) ▸
       at 0 1 (Bx⁻0-13 ∷ []) (refl) ▸ done


-- nat 0 BOXd(0;123): 8 steps
lem-nat-0-BOXd⟨0·123⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻0-123 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-023 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨0·123⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻0-123 ∷ []) (Bx⁻1-023 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻1-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻1-03 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-13 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·03⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 2 2 (Toff102 ∷ Sw01 ∷ []) (wl0099 c4) ▸
       at 3 2 (Bx⁻0-13 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·03⟩ c4) ▸
       at 4 2 (Toff102 ∷ Sw01 ∷ []) (wl0099 c4) ▸
       at 5 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 0 6 (Bx⁻1-023 ∷ []) (refl) ▸ done


-- nat 0 BOXd(1;0423): 8 steps
lem-nat-0-BOXd⟨1·0423⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-1423 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·0423⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻1-0423 ∷ []) (Bx⁻0-1423 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻0-123 ∷ CCZ014 ∷ Toff104 ∷ Bx⁻0-123 ∷ Toff104 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-023 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·123⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 2 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 3 2 (Bx⁻1-023 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·123⟩ c4) ▸
       at 4 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 5 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 0 6 (Bx⁻0-1423 ∷ []) (refl) ▸ done


-- nat 1 BOXd(2;03): 3 steps
lem-nat-1-BOXd⟨2·03⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻2-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-03 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·03⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻2-03 ∷ []) (Bx⁻1-03 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ03 ∷ []) (refl) ▸
       at 0 2 (CZ03 ∷ Sw12 ∷ []) (sym (wl0098 c4)) ▸
       at 0 1 (Bx⁻1-03 ∷ []) (refl) ▸ done


-- nat 1 BOXd(0;213): 8 steps
lem-nat-1-BOXd⟨0·213⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻0-213 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-123 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·213⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻0-213 ∷ []) (Bx⁻0-123 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-03 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·03⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 2 2 (Toff012 ∷ Sw12 ∷ []) (wl0038 c4) ▸
       at 3 2 (Bx⁻1-03 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·03⟩ c4) ▸
       at 4 2 (Toff012 ∷ Sw12 ∷ []) (wl0038 c4) ▸
       at 5 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 0 6 (Bx⁻0-123 ∷ []) (refl) ▸ done


-- nat 1 BOXd(2;0413): 8 steps
lem-nat-1-BOXd⟨2·0413⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0423 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·0413⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻2-0413 ∷ []) (Bx⁻1-0423 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-123 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·213⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 2 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 3 2 (Bx⁻0-123 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·213⟩ c4) ▸
       at 4 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 5 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 0 6 (Bx⁻1-0423 ∷ []) (refl) ▸ done


-- nat 1 BOXd(0;24): 3 steps
lem-nat-1-BOXd⟨0·24⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻0-24 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-14 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·24⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻0-24 ∷ []) (Bx⁻0-14 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ24 ∷ []) (refl) ▸
       at 0 2 (CZ14 ∷ Sw12 ∷ []) (sym (wl0005 c4)) ▸
       at 0 1 (Bx⁻0-14 ∷ []) (refl) ▸ done


-- nat 1 BOXd(2;034): 8 steps
lem-nat-1-BOXd⟨2·034⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻2-034 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-034 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·034⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻2-034 ∷ []) (Bx⁻1-034 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻0-24 ∷ CCZ023 ∷ Toff203 ∷ Bx⁻0-24 ∷ Toff203 ∷ CCZ023 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-14 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·24⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 2 2 (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4) ▸
       at 3 2 (Bx⁻0-14 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·24⟩ c4) ▸
       at 4 2 (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4) ▸
       at 5 2 (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4) ▸
       at 0 6 (Bx⁻1-034 ∷ []) (refl) ▸ done


-- nat 1 BOXd(0;2134): 8 steps
lem-nat-1-BOXd⟨0·2134⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-1234 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·2134⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻0-2134 ∷ []) (Bx⁻0-1234 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻2-034 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-034 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-034 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·034⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 2 2 (Toff012 ∷ Sw12 ∷ []) (wl0038 c4) ▸
       at 3 2 (Bx⁻1-034 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·034⟩ c4) ▸
       at 4 2 (Toff012 ∷ Sw12 ∷ []) (wl0038 c4) ▸
       at 5 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 0 6 (Bx⁻0-1234 ∷ []) (refl) ▸ done


-- nat 2 BOXd(0;34): 3 steps
lem-nat-2-BOXd⟨0·34⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻0-34 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-24 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·34⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻0-34 ∷ []) (Bx⁻0-24 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ34 ∷ []) (refl) ▸
       at 0 2 (CZ24 ∷ Sw23 ∷ []) (sym (wl0027 c4)) ▸
       at 0 1 (Bx⁻0-24 ∷ []) (refl) ▸ done


-- nat 2 BOXd(3;024): 8 steps
lem-nat-2-BOXd⟨3·024⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻3-024 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-034 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨3·024⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻3-024 ∷ []) (Bx⁻2-034 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻0-34 ∷ CCZ023 ∷ Toff302 ∷ Bx⁻0-34 ∷ Toff302 ∷ CCZ023 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-24 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·34⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 2 2 (Toff203 ∷ Sw23 ∷ []) (wl0066 c4) ▸
       at 3 2 (Bx⁻0-24 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·34⟩ c4) ▸
       at 4 2 (Toff203 ∷ Sw23 ∷ []) (wl0066 c4) ▸
       at 5 2 (CCZ023 ∷ Sw23 ∷ []) (sym (wl0065 c4)) ▸
       at 0 6 (Bx⁻2-034 ∷ []) (refl) ▸ done


-- nat 2 BOXd(0;3124): 8 steps
lem-nat-2-BOXd⟨0·3124⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-2134 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·3124⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx⁻0-3124 ∷ []) (Bx⁻0-2134 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx⁻3-024 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻3-024 ∷ Toff013 ∷ CCZ013 ∷ []) (refl) ▸
       at 0 2 (Bx⁻2-034 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨3·024⟩ c4) ▸
       at 1 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 2 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 3 2 (Bx⁻2-034 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨3·024⟩ c4) ▸
       at 4 2 (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4) ▸
       at 5 2 (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4) ▸
       at 0 6 (Bx⁻0-2134 ∷ []) (refl) ▸ done


-- nat 3 BOXd(0;43): 3 steps
lem-nat-3-BOXd⟨0·43⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻0-43 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-34 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·43⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻0-43 ∷ []) (Bx⁻0-34 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CZ34 ∷ []) (refl) ▸
       at 0 2 (CZ34 ∷ Sw34 ∷ []) (sym (wl0069 c4)) ▸
       at 0 1 (Bx⁻0-34 ∷ []) (refl) ▸ done


-- nat 3 BOXd(4;023): 8 steps
lem-nat-3-BOXd⟨4·023⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻4-023 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻3-024 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨4·023⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻4-023 ∷ []) (Bx⁻3-024 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻0-43 ∷ CCZ024 ∷ Toff402 ∷ Bx⁻0-43 ∷ Toff402 ∷ CCZ024 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-34 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·43⟩ c4) ▸
       at 1 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 2 2 (Toff302 ∷ Sw34 ∷ []) (lem-nat-3-TOFF402 c4) ▸
       at 3 2 (Bx⁻0-34 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·43⟩ c4) ▸
       at 4 2 (Toff302 ∷ Sw34 ∷ []) (lem-nat-3-TOFF402 c4) ▸
       at 5 2 (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4) ▸
       at 0 6 (Bx⁻3-024 ∷ []) (refl) ▸ done


-- nat 3 BOXd(0;4123): 8 steps
lem-nat-3-BOXd⟨0·4123⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-3124 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·4123⟩ c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx⁻0-4123 ∷ []) (Bx⁻0-3124 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx⁻4-023 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻4-023 ∷ Toff014 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻3-024 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨4·023⟩ c4) ▸
       at 1 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 2 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4) ▸
       at 3 2 (Bx⁻3-024 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨4·023⟩ c4) ▸
       at 4 2 (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4) ▸
       at 5 2 (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4) ▸
       at 0 6 (Bx⁻0-3124 ∷ []) (refl) ▸ done


-- nat 0 BOXd(1;43): 2 steps
lem-nat-0-BOXd⟨1·43⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻1-43 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-43 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·43⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻1-43 ∷ []) (Bx⁻0-43 ∷ Sw01 ∷ [])
  b0 = at 0 2 (Bx⁻1-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 0 1 (Bx⁻0-43 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOXd(4;123): 8 steps
lem-nat-0-BOXd⟨4·123⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻4-123 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-023 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨4·123⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻4-123 ∷ []) (Bx⁻4-023 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻1-43 ∷ CCZ124 ∷ Toff412 ∷ Bx⁻1-43 ∷ Toff412 ∷ CCZ124 ∷ []) (refl) ▸
       at 0 2 (Bx⁻0-43 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·43⟩ c4) ▸
       at 1 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 2 2 (Toff402 ∷ Sw01 ∷ []) (lem-nat-0-TOFF412 c4) ▸
       at 3 2 (Bx⁻0-43 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·43⟩ c4) ▸
       at 4 2 (Toff402 ∷ Sw01 ∷ []) (lem-nat-0-TOFF412 c4) ▸
       at 5 2 (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4) ▸
       at 0 6 (Bx⁻4-023 ∷ []) (refl) ▸ done


-- nat 0 BOXd(1;4023): 8 steps
lem-nat-0-BOXd⟨1·4023⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻1-4023 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-4123 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·4023⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx⁻1-4023 ∷ []) (Bx⁻0-4123 ∷ Sw01 ∷ [])
  b0 = at 1 1 (Bx⁻4-123 ∷ CCZ014 ∷ Toff104 ∷ Bx⁻4-123 ∷ Toff104 ∷ CCZ014 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-023 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·123⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 2 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 3 2 (Bx⁻4-023 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·123⟩ c4) ▸
       at 4 2 (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4) ▸
       at 5 2 (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4) ▸
       at 0 6 (Bx⁻0-4123 ∷ []) (refl) ▸ done


-- nat 1 BOXd(2;43): 2 steps
lem-nat-1-BOXd⟨2·43⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻2-43 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-43 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·43⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻2-43 ∷ []) (Bx⁻1-43 ∷ Sw12 ∷ [])
  b0 = at 0 2 (Bx⁻2-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 0 1 (Bx⁻1-43 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 1 BOXd(4;213): 8 steps
lem-nat-1-BOXd⟨4·213⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻4-213 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-123 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨4·213⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻4-213 ∷ []) (Bx⁻4-123 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻2-43 ∷ CCZ124 ∷ Toff412 ∷ Bx⁻2-43 ∷ Toff412 ∷ CCZ124 ∷ []) (refl) ▸
       at 0 2 (Bx⁻1-43 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·43⟩ c4) ▸
       at 1 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 2 2 (Toff412 ∷ Sw12 ∷ []) (wl0079 c4) ▸
       at 3 2 (Bx⁻1-43 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·43⟩ c4) ▸
       at 4 2 (Toff412 ∷ Sw12 ∷ []) (wl0079 c4) ▸
       at 5 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0078 c4)) ▸
       at 0 6 (Bx⁻4-123 ∷ []) (refl) ▸ done


-- nat 1 BOXd(2;4013): 8 steps
lem-nat-1-BOXd⟨2·4013⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-4023 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·4013⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx⁻2-4013 ∷ []) (Bx⁻1-4023 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx⁻4-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻4-213 ∷ Toff204 ∷ CCZ024 ∷ []) (refl) ▸
       at 0 2 (Bx⁻4-123 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·213⟩ c4) ▸
       at 1 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 2 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 3 2 (Bx⁻4-123 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·213⟩ c4) ▸
       at 4 2 (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4) ▸
       at 5 2 (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4) ▸
       at 0 6 (Bx⁻1-4023 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;24): 3 steps
lem-nat-1-BOX⟨1·24⟩ : WsL → ⟪ (Sw12 ∷ Bx1-24 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-14 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·24⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-24 ∷ []) (Bx2-14 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CZ24 ∷ []) (refl) ▸
       at 0 2 (CZ14 ∷ Sw12 ∷ []) (sym (wl0005 c4)) ▸
       at 0 1 (Bx2-14 ∷ []) (refl) ▸ done


-- nat 1 BOX(2;134): 8 steps
lem-nat-1-BOX⟨2·134⟩ : WsL → ⟪ (Sw12 ∷ Bx2-134 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-234 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·134⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx2-134 ∷ []) (Bx1-234 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx1-24 ∷ Toff213 ∷ CCZ123 ∷ Bx1-24 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 c4)) ▸
       at 1 2 (Toff123 ∷ Sw12 ∷ []) (wl0112 c4) ▸
       at 2 2 (Bx2-14 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·24⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw12 ∷ []) (wl0112 c4) ▸
       at 4 2 (CCZ123 ∷ Sw12 ∷ []) (sym (wl0111 c4)) ▸
       at 5 2 (Bx2-14 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·24⟩ c4) ▸
       at 0 6 (Bx1-234 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;2034): 8 steps
lem-nat-1-BOX⟨1·2034⟩ : WsL → ⟪ (Sw12 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·2034⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-2034 ∷ []) (Bx2-1034 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx2-134 ∷ Toff102 ∷ CCZ012 ∷ Bx2-134 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 1 2 (Toff201 ∷ Sw12 ∷ []) (wl0047 c4) ▸
       at 2 2 (Bx1-234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·134⟩ c4) ▸
       at 3 2 (Toff201 ∷ Sw12 ∷ []) (wl0047 c4) ▸
       at 4 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 5 2 (Bx1-234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·134⟩ c4) ▸
       at 0 6 (Bx2-1034 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;14): 3 steps
lem-nat-2-BOX⟨2·14⟩ : WsL → ⟪ (Sw23 ∷ Bx2-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-14 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·14⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-14 ∷ []) (Bx3-14 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ14 ∷ Sw23 ∷ []) (sym (wl0042 c4)) ▸
       at 0 1 (Bx3-14 ∷ []) (refl) ▸ done


-- nat 2 BOX(1;234): 8 steps
lem-nat-2-BOX⟨1·234⟩ : WsL → ⟪ (Sw23 ∷ Bx1-234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-324 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·234⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx1-234 ∷ []) (Bx1-324 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0113 c4)) ▸
       at 1 2 (Toff123 ∷ Sw23 ∷ []) (wl0114 c4) ▸
       at 2 2 (Bx3-14 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·14⟩ c4) ▸
       at 3 2 (Toff123 ∷ Sw23 ∷ []) (wl0114 c4) ▸
       at 4 2 (CCZ123 ∷ Sw23 ∷ []) (sym (wl0113 c4)) ▸
       at 5 2 (Bx3-14 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·14⟩ c4) ▸
       at 0 6 (Bx1-324 ∷ []) (refl) ▸ done


-- nat 2 BOX(2;1034): 8 steps
lem-nat-2-BOX⟨2·1034⟩ : WsL → ⟪ (Sw23 ∷ Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·1034⟩ c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx2-1034 ∷ []) (Bx3-1024 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx1-234 ∷ Toff201 ∷ CCZ012 ∷ Bx1-234 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 1 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 2 2 (Bx1-324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·234⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4) ▸
       at 4 2 (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4) ▸
       at 5 2 (Bx1-324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·234⟩ c4) ▸
       at 0 6 (Bx3-1024 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;024): 8 steps
lem-nat-0-BOX⟨1·024⟩ : WsL → ⟪ (Sw01 ∷ Bx1-024 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-124 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·024⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-024 ∷ []) (Bx0-124 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 1 2 (Toff012 ∷ Sw01 ∷ []) (wl0097 c4) ▸
       at 2 2 (Bx1-04 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·14⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw01 ∷ []) (wl0097 c4) ▸
       at 4 2 (CCZ012 ∷ Sw01 ∷ []) (sym (wl0096 c4)) ▸
       at 5 2 (Bx1-04 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·14⟩ c4) ▸
       at 0 6 (Bx0-124 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;1324): 8 steps
lem-nat-0-BOX⟨0·1324⟩ : WsL → ⟪ (Sw01 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·1324⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-1324 ∷ []) (Bx1-0324 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-024 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 1 2 (Toff103 ∷ Sw01 ∷ []) (wl0101 c4) ▸
       at 2 2 (Bx0-124 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·024⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw01 ∷ []) (wl0101 c4) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 5 2 (Bx0-124 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·024⟩ c4) ▸
       at 0 6 (Bx1-0324 ∷ []) (refl) ▸ done


-- nat 1 BOX(0;124): 8 steps
lem-nat-1-BOX⟨0·124⟩ : WsL → ⟪ (Sw12 ∷ Bx0-124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-214 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·124⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-124 ∷ []) (Bx0-214 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-04 ∷ Toff012 ∷ CCZ012 ∷ Bx1-04 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 1 2 (Toff012 ∷ Sw12 ∷ []) (wl0038 c4) ▸
       at 2 2 (Bx2-04 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·04⟩ c4) ▸
       at 3 2 (Toff012 ∷ Sw12 ∷ []) (wl0038 c4) ▸
       at 4 2 (CCZ012 ∷ Sw12 ∷ []) (sym (wl0037 c4)) ▸
       at 5 2 (Bx2-04 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·04⟩ c4) ▸
       at 0 6 (Bx0-214 ∷ []) (refl) ▸ done


-- nat 1 BOX(1;0324): 8 steps
lem-nat-1-BOX⟨1·0324⟩ : WsL → ⟪ (Sw12 ∷ Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·0324⟩ c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-0324 ∷ []) (Bx2-0314 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-124 ∷ Toff103 ∷ CCZ013 ∷ Bx0-124 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 1 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 2 2 (Bx0-214 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·124⟩ c4) ▸
       at 3 2 (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4) ▸
       at 4 2 (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4) ▸
       at 5 2 (Bx0-214 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·124⟩ c4) ▸
       at 0 6 (Bx2-0314 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;14): 3 steps
lem-nat-0-BOX⟨3·14⟩ : WsL → ⟪ (Sw01 ∷ Bx3-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-04 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·14⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-14 ∷ []) (Bx3-04 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw01 ∷ []) (lem-nat-0-CZ14 c4) ▸
       at 0 1 (Bx3-04 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;324): 8 steps
lem-nat-0-BOX⟨1·324⟩ : WsL → ⟪ (Sw01 ∷ Bx1-324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-324 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·324⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-324 ∷ []) (Bx0-324 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 1 2 (Toff023 ∷ Sw01 ∷ []) (wl0053 c4) ▸
       at 2 2 (Bx3-04 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·14⟩ c4) ▸
       at 3 2 (Toff023 ∷ Sw01 ∷ []) (wl0053 c4) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 5 2 (Bx3-04 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·14⟩ c4) ▸
       at 0 6 (Bx0-324 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;1024): 8 steps
lem-nat-0-BOX⟨3·1024⟩ : WsL → ⟪ (Sw01 ∷ Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·1024⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-1024 ∷ []) (Bx3-0124 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx1-324 ∷ Toff301 ∷ CCZ013 ∷ Bx1-324 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 1 2 (Toff301 ∷ Sw01 ∷ []) (wl0115 c4) ▸
       at 2 2 (Bx0-324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·324⟩ c4) ▸
       at 3 2 (Toff301 ∷ Sw01 ∷ []) (wl0115 c4) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 5 2 (Bx0-324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·324⟩ c4) ▸
       at 0 6 (Bx3-0124 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;04): 3 steps
lem-nat-0-BOX⟨3·04⟩ : WsL → ⟪ (Sw01 ∷ Bx3-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-14 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·04⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-04 ∷ []) (Bx3-14 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ04 ∷ []) (refl) ▸
       at 0 2 (CZ14 ∷ Sw01 ∷ []) (lem-nat-0-CZ04 c4) ▸
       at 0 1 (Bx3-14 ∷ []) (refl) ▸ done


-- nat 0 BOX(0;314): 8 steps
lem-nat-0-BOX⟨0·314⟩ : WsL → ⟪ (Sw01 ∷ Bx0-314 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-304 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·314⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-314 ∷ []) (Bx1-304 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 1 2 (Toff103 ∷ Sw01 ∷ []) (wl0101 c4) ▸
       at 2 2 (Bx3-14 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·04⟩ c4) ▸
       at 3 2 (Toff103 ∷ Sw01 ∷ []) (wl0101 c4) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 5 2 (Bx3-14 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·04⟩ c4) ▸
       at 0 6 (Bx1-304 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;0214): 8 steps
lem-nat-0-BOX⟨3·0214⟩ : WsL → ⟪ (Sw01 ∷ Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·0214⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-0214 ∷ []) (Bx3-1204 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-314 ∷ Toff302 ∷ CCZ023 ∷ Bx0-314 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 1 2 (Toff312 ∷ Sw01 ∷ []) (wl0116 c4) ▸
       at 2 2 (Bx1-304 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·314⟩ c4) ▸
       at 3 2 (Toff312 ∷ Sw01 ∷ []) (wl0116 c4) ▸
       at 4 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0103 c4)) ▸
       at 5 2 (Bx1-304 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·314⟩ c4) ▸
       at 0 6 (Bx3-1204 ∷ []) (refl) ▸ done


-- nat 0 BOX(1;304): 8 steps
lem-nat-0-BOX⟨1·304⟩ : WsL → ⟪ (Sw01 ∷ Bx1-304 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-314 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·304⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx1-304 ∷ []) (Bx0-314 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ []) (refl) ▸
       at 0 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 1 2 (Toff013 ∷ Sw01 ∷ []) (wl0102 c4) ▸
       at 2 2 (Bx3-04 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·14⟩ c4) ▸
       at 3 2 (Toff013 ∷ Sw01 ∷ []) (wl0102 c4) ▸
       at 4 2 (CCZ013 ∷ Sw01 ∷ []) (sym (wl0100 c4)) ▸
       at 5 2 (Bx3-04 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·14⟩ c4) ▸
       at 0 6 (Bx0-314 ∷ []) (refl) ▸ done


-- nat 0 BOX(3;1204): 8 steps
lem-nat-0-BOX⟨3·1204⟩ : WsL → ⟪ (Sw01 ∷ Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·1204⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx3-1204 ∷ []) (Bx3-0214 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx1-304 ∷ Toff312 ∷ CCZ123 ∷ Bx1-304 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 1 2 (Toff302 ∷ Sw01 ∷ []) (wl0110 c4) ▸
       at 2 2 (Bx0-314 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·304⟩ c4) ▸
       at 3 2 (Toff302 ∷ Sw01 ∷ []) (wl0110 c4) ▸
       at 4 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0003 c4)) ▸
       at 5 2 (Bx0-314 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·304⟩ c4) ▸
       at 0 6 (Bx3-0214 ∷ []) (refl) ▸ done


-- resp CK40 at 1: 6 steps
lem-resp-CK40-at-1 : WsL → ⟪ (CK40 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK41 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CK40-at-1 c4 = run b0
  where
  b0 : Chain (CK40 ∷ []) (Sw01 ∷ CK41 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 0 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 2 (Sw01 ∷ CK31 ∷ []) (wl0117 c4) ▸
       at 0 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 3 (CK41 ∷ []) (by-assoc Eq.refl) ▸ done


-- resp CKd40 at 1: 6 steps
lem-resp-CKd40-at-1 : WsL → ⟪ (CK40⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK41⁻ ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CKd40-at-1 c4 = run b0
  where
  b0 : Chain (CK40⁻ ∷ []) (Sw01 ∷ CK41⁻ ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0002 c4)) ▸
       at 0 1 (Sw34 ∷ CK30⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 2 (Sw01 ∷ CK31⁻ ∷ []) (wl0118 c4) ▸
       at 0 2 (Sw01 ∷ Sw34 ∷ []) (sym (c₂ (Swap) (Swap ↑))) ▸
       at 1 3 (CK41⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- comm CKd40 CCZ123: 13 steps
lem-comm-CKd40-CCZ123 : WsL → ⟪ (CK40⁻ ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CK40⁻ ∷ []) ⟫ʷ
lem-comm-CKd40-CCZ123 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CK40⁻ ∷ CCZ123 ∷ []) (Sw34 ∷ Sw23 ∷ CCZ134 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 6 3 (CCZ124 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CCZ134 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CCZ234 ∷ Sw12 ∷ []) (sym (wl0084 c4)) ▸
       at 3 2 (CCZ234 ∷ CK10⁻ ∷ []) (c₂ (S ↑ • CK₁₀) (CCZ)) ▸
       at 2 2 (CCZ134 ∷ Sw12 ∷ []) (sym (wl0034 c4)) ▸ done

  b1 : Chain (Sw34 ∷ Sw23 ∷ CCZ134 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) (CCZ123 ∷ CK40⁻ ∷ [])
  b1 = at 2 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0006 c4) ▸
       at 1 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0007 c4) ▸
       at 1 7 (CK40⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 CS13: 2 steps
lem-nat-2-CS13 : WsL → ⟪ (Sw23 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CS13 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CS13 ∷ []) (CS12 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0006 c4) ▸ done


-- nat 2 CS12: 2 steps
lem-nat-2-CS12 : WsL → ⟪ (Sw23 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CS12 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CS12 ∷ []) (CS13 ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 0 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 CS14: 2 steps
lem-nat-3-CS14 : WsL → ⟪ (Sw34 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CS14 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CS14 ∷ []) (CS13 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0007 c4) ▸ done


-- nat 3 CS13: 2 steps
lem-nat-3-CS13 : WsL → ⟪ (Sw34 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CS13 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CS13 ∷ []) (CS14 ∷ Sw34 ∷ [])
  b0 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 0 3 (CS14 ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 2 CSd13: 2 steps
lem-nat-2-CSd13 : WsL → ⟪ (Sw23 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CSd13 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CS13⁻ ∷ []) (CS12⁻ ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0006 c4) ▸ done


-- nat 2 CSd12: 2 steps
lem-nat-2-CSd12 : WsL → ⟪ (Sw23 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CSd12 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ CS12⁻ ∷ []) (CS13⁻ ∷ Sw23 ∷ [])
  b0 = at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0006 c4)) ▸
       at 0 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 3 CSd14: 2 steps
lem-nat-3-CSd14 : WsL → ⟪ (Sw34 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CSd14 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CS14⁻ ∷ []) (CS13⁻ ∷ Sw34 ∷ [])
  b0 = at 1 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0007 c4) ▸ done


-- nat 3 CSd13: 2 steps
lem-nat-3-CSd13 : WsL → ⟪ (Sw34 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CSd13 c4 = run b0
  where
  b0 : Chain (Sw34 ∷ CS13⁻ ∷ []) (CS14⁻ ∷ Sw34 ∷ [])
  b0 = at 2 0 (Sw34 ∷ Sw34 ∷ []) (sym (wl0007 c4)) ▸
       at 0 3 (CS14⁻ ∷ []) (by-assoc Eq.refl) ▸ done


-- nat 0 BOX(2;41): 3 steps
lem-nat-0-BOX⟨2·41⟩ : WsL → ⟪ (Sw01 ∷ Bx2-41 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-40 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·41⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-41 ∷ []) (Bx2-40 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CZ14 ∷ []) (refl) ▸
       at 0 2 (CZ04 ∷ Sw01 ∷ []) (lem-nat-0-CZ14 c4) ▸
       at 0 1 (Bx2-40 ∷ []) (refl) ▸ done


-- nat 0 BOX(4;231): 8 steps
lem-nat-0-BOX⟨4·231⟩ : WsL → ⟪ (Sw01 ∷ Bx4-231 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-230 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·231⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-231 ∷ []) (Bx4-230 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 1 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 2 2 (Bx2-40 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·41⟩ c4) ▸
       at 3 2 (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ)) ▸
       at 4 2 (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ)) ▸
       at 5 2 (Bx2-40 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·41⟩ c4) ▸
       at 0 6 (Bx4-230 ∷ []) (refl) ▸ done


-- nat 0 BOX(2;4031): 8 steps
lem-nat-0-BOX⟨2·4031⟩ : WsL → ⟪ (Sw01 ∷ Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4130 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·4031⟩ c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx2-4031 ∷ []) (Bx2-4130 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx4-231 ∷ Toff204 ∷ CCZ024 ∷ Bx4-231 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 1 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4) ▸
       at 2 2 (Bx4-230 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·231⟩ c4) ▸
       at 3 2 (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4) ▸
       at 5 2 (Bx4-230 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·231⟩ c4) ▸
       at 0 6 (Bx2-4130 ∷ []) (refl) ▸ done


-- nat 2 TOFF314: 2 steps
lem-nat-2-TOFF314 : WsL → ⟪ (Sw23 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF314 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Toff314 ∷ []) (Toff214 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0006 c4) ▸ done

