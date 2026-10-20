{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R006 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0002 ; wl0003 ; wl0004 ; wl0005 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0010 ; wl0013 ; wl0019 ; wl0021 ; wl0027 ; wl0030 ; wl0031 ; wl0032 ; wl0033 ; wl0034 ; wl0037 ; wl0038 ; wl0042 ; wl0044 ; wl0047 ; wl0048 ; wl0053 ; wl0056 ; wl0059 ; wl0065 ; wl0066 ; wl0069 ; wl0078 ; wl0079 ; wl0084 ; wl0088 ; wl0092 ; wl0096 ; wl0097 ; wl0098 ; wl0099 ; wl0100 ; wl0101 ; wl0102 ; wl0103 ; wl0104 ; wl0105 ; wl0106 ; wl0107 ; wl0108 ; wl0109 ; wl0110 ; wl0111 ; wl0112 ; wl0113 ; wl0114 ; wl0115 ; wl0116 ; wl0117 ; wl0118)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-BOX⟨0·23⟩ ; lem-nat-1-BOX⟨0·24⟩ ; lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-TOFF203 ; lem-nat-2-BOX⟨0·32⟩ ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF012 ; lem-nat-2-TOFF013 ; lem-nat-2-TOFF102 ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ024 ; lem-nat-3-CZ13 ; lem-nat-3-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-CCZ013 ; lem-nat-1-CCZ014 ; lem-nat-1-TOFF103 ; lem-nat-2-TOFF201 ; lem-nat-2-TOFF304 ; lem-nat-3-CCZ023 ; lem-nat-3-TOFF203 ; lem-nat-3-TOFF402)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-CCZ014 ; lem-nat-0-TOFF104 ; lem-nat-0-TOFF412 ; lem-nat-1-TOFF104 ; lem-nat-1-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-CZ04 ; lem-nat-0-CZ14 ; lem-nat-0-TOFF204 ; lem-nat-0-TOFF214 ; lem-nat-1-TOFF013 ; lem-nat-2-TOFF104)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨0·14⟩ ; lem-nat-0-BOX⟨1·24⟩ ; lem-nat-1-BOX⟨1·04⟩ ; lem-nat-1-TOFF023 ; lem-nat-2-CCZ014)

private
  q1 : WsL → Eqn
  q1 c4 = eqn (CCZ023 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ123 ∷ []) (wl0003 c4)
  q2 : WsL → Eqn
  q2 c4 = eqn (Sw01 ∷ Toff213 ∷ []) (Toff203 ∷ Sw01 ∷ []) (wl0004 c4)
  q3 : WsL → Eqn
  q3 c4 = eqn (Sw01 ∷ Bx1-24 ∷ []) (Bx0-24 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·24⟩ c4)

-- nat 0 BOX(2;134): 8 steps
lem-nat-0-BOX⟨2·134⟩ : WsL → ⟪ (Sw01 ∷ Bx2-134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-034 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·134⟩ c4 = derive (Sw01 ∷ Bx2-134 ∷ []) (Bx2-034 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff213 ∷ Bx1-24 ∷ Toff213 ∷ CCZ123 ∷ Bx1-24 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw 2 (q3 c4) ∷
   rw 3 (q2 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   rw 5 (q3 c4) ∷
   re 0 6 (Bx2-034 ∷ []) ∷ []) Eq.refl

private
  q4 : WsL → Eqn
  q4 c4 = eqn (CCZ012 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ012 ∷ []) (wl0096 c4)
  q5 : WsL → Eqn
  q5 c4 = eqn (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) (wl0097 c4)
  q6 : WsL → Eqn
  q6 c4 = eqn (Sw01 ∷ Bx2-134 ∷ []) (Bx2-034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·134⟩ c4)

-- nat 0 BOX(1;2034): 8 steps
lem-nat-0-BOX⟨1·2034⟩ : WsL → ⟪ (Sw01 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·2034⟩ c4 = derive (Sw01 ∷ Bx1-2034 ∷ []) (Bx0-2134 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff102 ∷ Bx2-134 ∷ Toff102 ∷ CCZ012 ∷ Bx2-134 ∷ []) ∷
   rw⁻ 0 (q4 c4) ∷
   rw 1 (q5 c4) ∷
   rw 2 (q6 c4) ∷
   rw 3 (q5 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   rw 5 (q6 c4) ∷
   re 0 6 (Bx0-2134 ∷ []) ∷ []) Eq.refl

private
  q7 : WsL → Eqn
  q7 c4 = eqn (Sw01 ∷ Bx0-24 ∷ []) (Bx0-24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑))

-- nat 0 BOX(0;24): 2 steps
lem-nat-0-BOX⟨0·24⟩ : WsL → ⟪ (Sw01 ∷ Bx0-24 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-24 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·24⟩ c4 = derive (Sw01 ∷ Bx0-24 ∷ []) (Bx1-24 ∷ Sw01 ∷ [])
  (rw 0 (q7 c4) ∷
   re 0 1 (Bx1-24 ∷ []) ∷ []) Eq.refl

private
  q8 : WsL → Eqn
  q8 c4 = eqn (CCZ123 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ023 ∷ []) (wl0103 c4)
  q9 : WsL → Eqn
  q9 c4 = eqn (Sw01 ∷ Toff203 ∷ []) (Toff213 ∷ Sw01 ∷ []) (wl0104 c4)
  q10 : WsL → Eqn
  q10 c4 = eqn (Sw01 ∷ Bx0-24 ∷ []) (Bx1-24 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·24⟩ c4)

-- nat 0 BOX(2;034): 8 steps
lem-nat-0-BOX⟨2·034⟩ : WsL → ⟪ (Sw01 ∷ Bx2-034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-134 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·034⟩ c4 = derive (Sw01 ∷ Bx2-034 ∷ []) (Bx2-134 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) ∷
   rw⁻ 0 (q8 c4) ∷
   rw 1 (q9 c4) ∷
   rw 2 (q10 c4) ∷
   rw 3 (q9 c4) ∷
   rw⁻ 4 (q8 c4) ∷
   rw 5 (q10 c4) ∷
   re 0 6 (Bx2-134 ∷ []) ∷ []) Eq.refl

private
  q11 : WsL → Eqn
  q11 c4 = eqn (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) (wl0099 c4)
  q12 : WsL → Eqn
  q12 c4 = eqn (Sw01 ∷ Bx2-034 ∷ []) (Bx2-134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·034⟩ c4)

-- nat 0 BOX(0;2134): 8 steps
lem-nat-0-BOX⟨0·2134⟩ : WsL → ⟪ (Sw01 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·2134⟩ c4 = derive (Sw01 ∷ Bx0-2134 ∷ []) (Bx1-2034 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-034 ∷ Toff012 ∷ CCZ012 ∷ Bx2-034 ∷ []) ∷
   rw⁻ 0 (q4 c4) ∷
   rw 1 (q11 c4) ∷
   rw 2 (q12 c4) ∷
   rw 3 (q11 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   rw 5 (q12 c4) ∷
   re 0 6 (Bx1-2034 ∷ []) ∷ []) Eq.refl

private
  q13 : WsL → Eqn
  q13 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 c4)

-- nat 1 CZ01: 2 steps
lem-nat-1-CZ01 : WsL → ⟪ (Sw12 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CZ01 c4 = derive (Sw12 ∷ CZ01 ∷ []) (CZ02 ∷ Sw12 ∷ [])
  (rw⁻ 2 (q13 c4) ∷
   re 0 3 (CZ02 ∷ []) ∷ []) Eq.refl

-- nat 1 CZ02: 2 steps
lem-nat-1-CZ02 : WsL → ⟪ (Sw12 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CZ02 c4 = derive (Sw12 ∷ CZ02 ∷ []) (CZ01 ∷ Sw12 ∷ [])
  (re 1 1 (Sw12 ∷ CZ01 ∷ Sw12 ∷ []) ∷
   rw 0 (q13 c4) ∷ []) Eq.refl

private
  q14 : WsL → Eqn
  q14 c4 = eqn (CCZ012 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ012 ∷ []) (wl0037 c4)
  q15 : WsL → Eqn
  q15 c4 = eqn (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) (wl0044 c4)
  q16 : WsL → Eqn
  q16 c4 = eqn (Sw12 ∷ Bx0-24 ∷ []) (Bx0-14 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·24⟩ c4)

-- nat 1 BOX(2;014): 8 steps
lem-nat-1-BOX⟨2·014⟩ : WsL → ⟪ (Sw12 ∷ Bx2-014 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-024 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·014⟩ c4 = derive (Sw12 ∷ Bx2-014 ∷ []) (Bx1-024 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) ∷
   rw⁻ 0 (q14 c4) ∷
   rw 1 (q15 c4) ∷
   rw 2 (q16 c4) ∷
   rw 3 (q15 c4) ∷
   rw⁻ 4 (q14 c4) ∷
   rw 5 (q16 c4) ∷
   re 0 6 (Bx1-024 ∷ []) ∷ []) Eq.refl

private
  q17 : WsL → Eqn
  q17 c4 = eqn (Sw12 ∷ CCZ023 ∷ []) (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4)
  q18 : WsL → Eqn
  q18 c4 = eqn (Sw12 ∷ Toff023 ∷ []) (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4)
  q19 : WsL → Eqn
  q19 c4 = eqn (Sw12 ∷ Bx2-014 ∷ []) (Bx1-024 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·014⟩ c4)

-- nat 1 BOX(0;2314): 8 steps
lem-nat-1-BOX⟨0·2314⟩ : WsL → ⟪ (Sw12 ∷ Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·2314⟩ c4 = derive (Sw12 ∷ Bx0-2314 ∷ []) (Bx0-1324 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-014 ∷ Toff023 ∷ CCZ023 ∷ Bx2-014 ∷ []) ∷
   rw 0 (q17 c4) ∷
   rw 1 (q18 c4) ∷
   rw 2 (q19 c4) ∷
   rw 3 (q18 c4) ∷
   rw 4 (q17 c4) ∷
   rw 5 (q19 c4) ∷
   re 0 6 (Bx0-1324 ∷ []) ∷ []) Eq.refl

-- nat 1 CX20: 2 steps
lem-nat-1-CX20 : WsL → ⟪ (Sw12 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CX20 c4 = derive (Sw12 ∷ CX20 ∷ []) (CX10 ∷ Sw12 ∷ [])
  (re 1 1 (Sw12 ∷ CX10 ∷ Sw12 ∷ []) ∷
   rw 0 (q13 c4) ∷ []) Eq.refl

-- nat 1 CX10: 2 steps
lem-nat-1-CX10 : WsL → ⟪ (Sw12 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CX10 c4 = derive (Sw12 ∷ CX10 ∷ []) (CX20 ∷ Sw12 ∷ [])
  (rw⁻ 2 (q13 c4) ∷
   re 0 3 (CX20 ∷ []) ∷ []) Eq.refl

private
  q20 : WsL → Eqn
  q20 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 c4)
  q21 : WsL → Eqn
  q21 c4 = eqn (CZ02 ∷ Sw01 ∷ []) (Sw01 ∷ CZ12 ∷ []) (wl0105 c4)

-- resp CZ02 at 1: 2 steps
lem-resp-CZ02-at-1 : WsL → ⟪ (CZ02 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CZ12 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CZ02-at-1 c4 = derive (CZ02 ∷ []) (Sw01 ∷ CZ12 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q20 c4) ∷
   rw 0 (q21 c4) ∷ []) Eq.refl

private
  q22 : WsL → Eqn
  q22 c4 = eqn (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ []) (wl0106 c4)

-- resp CX20 at 1: 2 steps
lem-resp-CX20-at-1 : WsL → ⟪ (CX20 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX21 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CX20-at-1 c4 = derive (CX20 ∷ []) (Sw01 ∷ CX21 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q20 c4) ∷
   rw 0 (q22 c4) ∷ []) Eq.refl

private
  q23 : WsL → Eqn
  q23 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0006 c4)

-- nat 2 CZ13: 2 steps
lem-nat-2-CZ13 : WsL → ⟪ (Sw23 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CZ13 c4 = derive (Sw23 ∷ CZ13 ∷ []) (CZ12 ∷ Sw23 ∷ [])
  (re 1 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 0 (q23 c4) ∷ []) Eq.refl

private
  q24 : WsL → Eqn
  q24 c4 = eqn (Sw23 ∷ CZ13 ∷ []) (CZ12 ∷ Sw23 ∷ []) (lem-nat-2-CZ13 c4)

-- nat 2 BOX(0;13): 3 steps
lem-nat-2-BOX⟨0·13⟩ : WsL → ⟪ (Sw23 ∷ Bx0-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-12 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·13⟩ c4 = derive (Sw23 ∷ Bx0-13 ∷ []) (Bx0-12 ∷ Sw23 ∷ [])
  (re 1 1 (CZ13 ∷ []) ∷
   rw 0 (q24 c4) ∷
   re 0 1 (Bx0-12 ∷ []) ∷ []) Eq.refl

private
  q25 : WsL → Eqn
  q25 c4 = eqn (Sw23 ∷ CCZ014 ∷ []) (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4)
  q26 : WsL → Eqn
  q26 c4 = eqn (Sw23 ∷ Toff104 ∷ []) (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4)
  q27 : WsL → Eqn
  q27 c4 = eqn (Sw23 ∷ Bx0-13 ∷ []) (Bx0-12 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·13⟩ c4)

-- nat 2 BOX(1;043): 8 steps
lem-nat-2-BOX⟨1·043⟩ : WsL → ⟪ (Sw23 ∷ Bx1-043 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-042 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·043⟩ c4 = derive (Sw23 ∷ Bx1-043 ∷ []) (Bx1-042 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Toff104 ∷ CCZ014 ∷ Bx0-13 ∷ []) ∷
   rw 0 (q25 c4) ∷
   rw 1 (q26 c4) ∷
   rw 2 (q27 c4) ∷
   rw 3 (q26 c4) ∷
   rw 4 (q25 c4) ∷
   rw 5 (q27 c4) ∷
   re 0 6 (Bx1-042 ∷ []) ∷ []) Eq.refl

private
  q28 : WsL → Eqn
  q28 c4 = eqn (Sw23 ∷ CCZ012 ∷ []) (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4)
  q29 : WsL → Eqn
  q29 c4 = eqn (Sw23 ∷ Toff012 ∷ []) (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4)
  q30 : WsL → Eqn
  q30 c4 = eqn (Sw23 ∷ Bx1-043 ∷ []) (Bx1-042 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·043⟩ c4)

-- nat 2 BOX(0;1243): 8 steps
lem-nat-2-BOX⟨0·1243⟩ : WsL → ⟪ (Sw23 ∷ Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·1243⟩ c4 = derive (Sw23 ∷ Bx0-1243 ∷ []) (Bx0-1342 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-043 ∷ Toff012 ∷ CCZ012 ∷ Bx1-043 ∷ []) ∷
   rw 0 (q28 c4) ∷
   rw 1 (q29 c4) ∷
   rw 2 (q30 c4) ∷
   rw 3 (q29 c4) ∷
   rw 4 (q28 c4) ∷
   rw 5 (q30 c4) ∷
   re 0 6 (Bx0-1342 ∷ []) ∷ []) Eq.refl

private
  q31 : WsL → Eqn
  q31 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0007 c4)

-- nat 3 CZ24: 2 steps
lem-nat-3-CZ24 : WsL → ⟪ (Sw34 ∷ CZ24 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CZ24 c4 = derive (Sw34 ∷ CZ24 ∷ []) (CZ23 ∷ Sw34 ∷ [])
  (re 1 1 (Sw34 ∷ CZ23 ∷ Sw34 ∷ []) ∷
   rw 0 (q31 c4) ∷ []) Eq.refl

private
  q32 : WsL → Eqn
  q32 c4 = eqn (Sw34 ∷ CZ24 ∷ []) (CZ23 ∷ Sw34 ∷ []) (lem-nat-3-CZ24 c4)

-- nat 3 BOX(0;24): 3 steps
lem-nat-3-BOX⟨0·24⟩ : WsL → ⟪ (Sw34 ∷ Bx0-24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-23 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·24⟩ c4 = derive (Sw34 ∷ Bx0-24 ∷ []) (Bx0-23 ∷ Sw34 ∷ [])
  (re 1 1 (CZ24 ∷ []) ∷
   rw 0 (q32 c4) ∷
   re 0 1 (Bx0-23 ∷ []) ∷ []) Eq.refl

private
  q33 : WsL → Eqn
  q33 c4 = eqn (Sw34 ∷ CCZ023 ∷ []) (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4)
  q34 : WsL → Eqn
  q34 c4 = eqn (Sw34 ∷ Toff203 ∷ []) (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 c4)
  q35 : WsL → Eqn
  q35 c4 = eqn (Sw34 ∷ Bx0-24 ∷ []) (Bx0-23 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·24⟩ c4)

-- nat 3 BOX(2;034): 8 steps
lem-nat-3-BOX⟨2·034⟩ : WsL → ⟪ (Sw34 ∷ Bx2-034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-043 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·034⟩ c4 = derive (Sw34 ∷ Bx2-034 ∷ []) (Bx2-043 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ []) ∷
   rw 0 (q33 c4) ∷
   rw 1 (q34 c4) ∷
   rw 2 (q35 c4) ∷
   rw 3 (q34 c4) ∷
   rw 4 (q33 c4) ∷
   rw 5 (q35 c4) ∷
   re 0 6 (Bx2-043 ∷ []) ∷ []) Eq.refl

private
  q36 : WsL → Eqn
  q36 c4 = eqn (CCZ012 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (Swap))
  q37 : WsL → Eqn
  q37 c4 = eqn (Toff012 ∷ Sw34 ∷ []) (Sw34 ∷ Toff012 ∷ []) (c₃ (Toff) (Swap))
  q38 : WsL → Eqn
  q38 c4 = eqn (Sw34 ∷ Bx2-034 ∷ []) (Bx2-043 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·034⟩ c4)

-- nat 3 BOX(0;2134): 8 steps
lem-nat-3-BOX⟨0·2134⟩ : WsL → ⟪ (Sw34 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·2134⟩ c4 = derive (Sw34 ∷ Bx0-2134 ∷ []) (Bx0-2143 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-034 ∷ Toff012 ∷ CCZ012 ∷ Bx2-034 ∷ []) ∷
   rw⁻ 0 (q36 c4) ∷
   rw⁻ 1 (q37 c4) ∷
   rw 2 (q38 c4) ∷
   rw⁻ 3 (q37 c4) ∷
   rw⁻ 4 (q36 c4) ∷
   rw 5 (q38 c4) ∷
   re 0 6 (Bx0-2143 ∷ []) ∷ []) Eq.refl

-- nat 2 CZ12: 2 steps
lem-nat-2-CZ12 : WsL → ⟪ (Sw23 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CZ12 c4 = derive (Sw23 ∷ CZ12 ∷ []) (CZ13 ∷ Sw23 ∷ [])
  (rw⁻ 2 (q23 c4) ∷
   re 0 3 (CZ13 ∷ []) ∷ []) Eq.refl

private
  q39 : WsL → Eqn
  q39 c4 = eqn (Sw23 ∷ CZ12 ∷ []) (CZ13 ∷ Sw23 ∷ []) (lem-nat-2-CZ12 c4)

-- nat 2 BOX(0;12): 3 steps
lem-nat-2-BOX⟨0·12⟩ : WsL → ⟪ (Sw23 ∷ Bx0-12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-13 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·12⟩ c4 = derive (Sw23 ∷ Bx0-12 ∷ []) (Bx0-13 ∷ Sw23 ∷ [])
  (re 1 1 (CZ12 ∷ []) ∷
   rw 0 (q39 c4) ∷
   re 0 1 (Bx0-13 ∷ []) ∷ []) Eq.refl

private
  q40 : WsL → Eqn
  q40 c4 = eqn (Sw23 ∷ Bx0-12 ∷ []) (Bx0-13 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·12⟩ c4)

-- nat 2 BOX(1;042): 8 steps
lem-nat-2-BOX⟨1·042⟩ : WsL → ⟪ (Sw23 ∷ Bx1-042 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-043 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·042⟩ c4 = derive (Sw23 ∷ Bx1-042 ∷ []) (Bx1-043 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) ∷
   rw 0 (q25 c4) ∷
   rw 1 (q26 c4) ∷
   rw 2 (q40 c4) ∷
   rw 3 (q26 c4) ∷
   rw 4 (q25 c4) ∷
   rw 5 (q40 c4) ∷
   re 0 6 (Bx1-043 ∷ []) ∷ []) Eq.refl

private
  q41 : WsL → Eqn
  q41 c4 = eqn (Sw23 ∷ CCZ013 ∷ []) (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4)
  q42 : WsL → Eqn
  q42 c4 = eqn (Sw23 ∷ Toff013 ∷ []) (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4)
  q43 : WsL → Eqn
  q43 c4 = eqn (Sw23 ∷ Bx1-042 ∷ []) (Bx1-043 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·042⟩ c4)

-- nat 2 BOX(0;1342): 8 steps
lem-nat-2-BOX⟨0·1342⟩ : WsL → ⟪ (Sw23 ∷ Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·1342⟩ c4 = derive (Sw23 ∷ Bx0-1342 ∷ []) (Bx0-1243 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-042 ∷ Toff013 ∷ CCZ013 ∷ Bx1-042 ∷ []) ∷
   rw 0 (q41 c4) ∷
   rw 1 (q42 c4) ∷
   rw 2 (q43 c4) ∷
   rw 3 (q42 c4) ∷
   rw 4 (q41 c4) ∷
   rw 5 (q43 c4) ∷
   re 0 6 (Bx0-1243 ∷ []) ∷ []) Eq.refl

private
  q44 : WsL → Eqn
  q44 c4 = eqn (Sw12 ∷ CCZ024 ∷ []) (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4)
  q45 : WsL → Eqn
  q45 c4 = eqn (Sw12 ∷ Toff204 ∷ []) (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4)
  q46 : WsL → Eqn
  q46 c4 = eqn (Sw12 ∷ Bx0-23 ∷ []) (Bx0-13 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·23⟩ c4)

-- nat 1 BOX(2;043): 8 steps
lem-nat-1-BOX⟨2·043⟩ : WsL → ⟪ (Sw12 ∷ Bx2-043 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-043 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·043⟩ c4 = derive (Sw12 ∷ Bx2-043 ∷ []) (Bx1-043 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ CCZ024 ∷ Bx0-23 ∷ []) ∷
   rw 0 (q44 c4) ∷
   rw 1 (q45 c4) ∷
   rw 2 (q46 c4) ∷
   rw 3 (q45 c4) ∷
   rw 4 (q44 c4) ∷
   rw 5 (q46 c4) ∷
   re 0 6 (Bx1-043 ∷ []) ∷ []) Eq.refl

private
  q47 : WsL → Eqn
  q47 c4 = eqn (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) (wl0038 c4)
  q48 : WsL → Eqn
  q48 c4 = eqn (Sw12 ∷ Bx2-043 ∷ []) (Bx1-043 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·043⟩ c4)

-- nat 1 BOX(0;2143): 8 steps
lem-nat-1-BOX⟨0·2143⟩ : WsL → ⟪ (Sw12 ∷ Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·2143⟩ c4 = derive (Sw12 ∷ Bx0-2143 ∷ []) (Bx0-1243 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-043 ∷ Toff012 ∷ CCZ012 ∷ Bx2-043 ∷ []) ∷
   rw⁻ 0 (q14 c4) ∷
   rw 1 (q47 c4) ∷
   rw 2 (q48 c4) ∷
   rw 3 (q47 c4) ∷
   rw⁻ 4 (q14 c4) ∷
   rw 5 (q48 c4) ∷
   re 0 6 (Bx0-1243 ∷ []) ∷ []) Eq.refl

private
  q49 : WsL → Eqn
  q49 c4 = eqn (Sw23 ∷ CCZ034 ∷ []) (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4)
  q50 : WsL → Eqn
  q50 c4 = eqn (Sw23 ∷ Toff304 ∷ []) (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4)
  q51 : WsL → Eqn
  q51 c4 = eqn (Sw23 ∷ Bx0-32 ∷ []) (Bx0-23 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·32⟩ c4)

-- nat 2 BOX(3;042): 8 steps
lem-nat-2-BOX⟨3·042⟩ : WsL → ⟪ (Sw23 ∷ Bx3-042 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-043 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·042⟩ c4 = derive (Sw23 ∷ Bx3-042 ∷ []) (Bx2-043 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) ∷
   rw 0 (q49 c4) ∷
   rw 1 (q50 c4) ∷
   rw 2 (q51 c4) ∷
   rw 3 (q50 c4) ∷
   rw 4 (q49 c4) ∷
   rw 5 (q51 c4) ∷
   re 0 6 (Bx2-043 ∷ []) ∷ []) Eq.refl

private
  q52 : WsL → Eqn
  q52 c4 = eqn (Sw23 ∷ Bx3-042 ∷ []) (Bx2-043 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·042⟩ c4)

-- nat 2 BOX(0;3142): 8 steps
lem-nat-2-BOX⟨0·3142⟩ : WsL → ⟪ (Sw23 ∷ Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·3142⟩ c4 = derive (Sw23 ∷ Bx0-3142 ∷ []) (Bx0-2143 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-042 ∷ Toff013 ∷ CCZ013 ∷ Bx3-042 ∷ []) ∷
   rw 0 (q41 c4) ∷
   rw 1 (q42 c4) ∷
   rw 2 (q52 c4) ∷
   rw 3 (q42 c4) ∷
   rw 4 (q41 c4) ∷
   rw 5 (q52 c4) ∷
   re 0 6 (Bx0-2143 ∷ []) ∷ []) Eq.refl

private
  q53 : WsL → Eqn
  q53 c4 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (c₂ (K ↑) (Swap))
  q54 : WsL → Eqn
  q54 c4 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap))
  q55 : WsL → Eqn
  q55 c4 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (c₁ (iI) (Swap ↑))
  q56 : WsL → Eqn
  q56 c4 = eqn (K1 ∷ Sw34 ∷ []) (Sw34 ∷ K1 ∷ []) (c₂ (K ↑) (Swap ↑))
  q57 : WsL → Eqn
  q57 c4 = eqn (CX01 ∷ Sw34 ∷ []) (Sw34 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap ↑))
  q58 : WsL → Eqn
  q58 c4 = eqn (ι ∷ Sw34 ∷ []) (Sw34 ∷ ι ∷ []) (c₁ (iI) (Swap ↑ ↑))
  q59 : WsL → Eqn
  q59 c4 = eqn (K2 ∷ Sw12 ∷ []) (Sw12 ∷ K1 ∷ []) (wl0056 c4)
  q60 : WsL → Eqn
  q60 c4 = eqn (CS24 ∷ Sw12 ∷ []) (Sw12 ∷ CS14 ∷ []) (wl0008 c4)
  q61 : WsL → Eqn
  q61 c4 = eqn (CS24⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS14⁻ ∷ []) (wl0009 c4)
  q62 : WsL → Eqn
  q62 c4 = eqn (Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap))
  q63 : WsL → Eqn
  q63 c4 = eqn (CS03 ∷ Sw12 ∷ []) (Sw12 ∷ CS03 ∷ []) (wl0010 c4)
  q64 : WsL → Eqn
  q64 c4 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (c₁ (iI) (Swap))
  q65 : WsL → Eqn
  q65 c4 = eqn (Sw01 ∷ ι ∷ []) (ι ∷ Sw01 ∷ []) (wl0030 c4)
  q66 : WsL → Eqn
  q66 c4 = eqn (Sw01 ∷ K2 ∷ []) (K2 ∷ Sw01 ∷ []) (c₂ (Swap) (K))
  q67 : WsL → Eqn
  q67 c4 = eqn (Sw01 ∷ Sw34 ∷ []) (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑))
  q68 : WsL → Eqn
  q68 c4 = eqn (CS03 ∷ Sw01 ∷ []) (Sw01 ∷ CS13 ∷ []) (wl0019 c4)
  q69 : WsL → Eqn
  q69 c4 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wl0048 c4)
  q70 : WsL → Eqn
  q70 c4 = eqn (Sw01 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))
  q71 : WsL → Eqn
  q71 c4 = eqn (Sw01 ∷ CS24 ∷ []) (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑))
  q72 : WsL → Eqn
  q72 c4 = eqn (K2 ∷ Sw34 ∷ []) (Sw34 ∷ K2 ∷ []) (c₃ (K ↑ ↑) (Swap))
  q73 : WsL → Eqn
  q73 c4 = eqn (CX12 ∷ Sw34 ∷ []) (Sw34 ∷ CX12 ∷ []) (c₃ (CX₀₁ ↑) (Swap))
  q74 : WsL → Eqn
  q74 c4 = eqn (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι ∷ []) (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (wl0059 c4)

-- resp TOFF104 at 2: 74 steps
lem-resp-TOFF104-at-2 : WsL → ⟪ (Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff214 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF104-at-2 c4 = derive (Toff104 ∷ []) (Sw12 ∷ Sw01 ∷ Toff214 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q13 c4) ∷
   rw⁻ 0 (q13 c4) ∷
   re 1 3 (Toff204 ∷ []) ∷
   rw⁻ 2 (q20 c4) ∷
   re 1 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) ∷
   re 2 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) ∷
   re 3 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 3 (q53 c4) ∷
   rw⁻ 6 (q23 c4) ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 (q54 c4) ∷
   rw⁻ 8 (q23 c4) ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 (q54 c4) ∷
   rw⁻ 10 (q23 c4) ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 (q53 c4) ∷
   rw⁻ 10 (q55 c4) ∷
   rw 11 (q23 c4) ∷
   rw⁻ 2 (q56 c4) ∷
   rw⁻ 5 (q31 c4) ∷
   re 3 3 (CS14 ∷ []) ∷
   rw⁻ 4 (q57 c4) ∷
   rw⁻ 7 (q31 c4) ∷
   re 5 3 (CS14⁻ ∷ []) ∷
   rw⁻ 6 (q57 c4) ∷
   rw⁻ 9 (q31 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw⁻ 8 (q56 c4) ∷
   rw⁻ 9 (q58 c4) ∷
   rw 10 (q31 c4) ∷
   rw⁻ 1 (q59 c4) ∷
   rw⁻ 2 (q60 c4) ∷
   rw⁻ 5 (q13 c4) ∷
   re 3 3 (CX02 ∷ []) ∷
   rw⁻ 4 (q61 c4) ∷
   rw⁻ 7 (q13 c4) ∷
   re 5 3 (CX02 ∷ []) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 6 (q62 c4) ∷
   rw⁻ 7 (q63 c4) ∷
   rw 8 (q62 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw⁻ 7 (q59 c4) ∷
   rw⁻ 8 (q64 c4) ∷
   rw 9 (q13 c4) ∷
   rw⁻ 8 (q65 c4) ∷
   rw⁻ 7 (q66 c4) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw⁻ 8 (q67 c4) ∷
   rw 7 (q68 c4) ∷
   rw⁻ 6 (q67 c4) ∷
   re 7 3 (CS14 ∷ []) ∷
   rw 5 (q69 c4) ∷
   rw⁻ 4 (q70 c4) ∷
   rw 3 (q69 c4) ∷
   rw⁻ 2 (q71 c4) ∷
   rw⁻ 1 (q66 c4) ∷
   rw⁻ 2 (q31 c4) ∷
   rw⁻ 3 (q72 c4) ∷
   re 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 4 (q31 c4) ∷
   rw⁻ 5 (q73 c4) ∷
   re 7 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 6 (q31 c4) ∷
   rw⁻ 7 (q73 c4) ∷
   re 9 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 8 (q31 c4) ∷
   rw⁻ 9 (q72 c4) ∷
   rw⁻ 10 (q58 c4) ∷
   rw 3 (q74 c4) ∷
   re 3 8 (Toff213 ∷ []) ∷
   re 2 3 (Toff214 ∷ []) ∷ []) Eq.refl

private
  q75 : WsL → Eqn
  q75 c4 = eqn (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4)
  q76 : WsL → Eqn
  q76 c4 = eqn (CS01 ∷ Sw34 ∷ []) (Sw34 ∷ CS01 ∷ []) (c₂ (CS) (Swap ↑))
  q77 : WsL → Eqn
  q77 c4 = eqn (CS14⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS14⁻ ∷ []) (wl0033 c4)
  q78 : WsL → Eqn
  q78 c4 = eqn (CS14 ∷ Sw23 ∷ []) (Sw23 ∷ CS14 ∷ []) (wl0021 c4)

-- resp TOFF104 at 3: 143 steps
lem-resp-TOFF104-at-3 : WsL → ⟪ (Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff214 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF104-at-3 c4 = derive (Toff104 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff214 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q23 c4) ∷
   re 0 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) ∷
   re 1 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 1 (q53 c4) ∷
   rw⁻ 4 (q23 c4) ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 (q54 c4) ∷
   rw⁻ 6 (q23 c4) ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 (q54 c4) ∷
   rw⁻ 8 (q23 c4) ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 (q53 c4) ∷
   rw⁻ 8 (q55 c4) ∷
   rw 9 (q23 c4) ∷
   rw⁻ 0 (q56 c4) ∷
   rw⁻ 3 (q31 c4) ∷
   re 1 3 (CS14 ∷ []) ∷
   rw⁻ 2 (q57 c4) ∷
   rw⁻ 5 (q31 c4) ∷
   re 3 3 (CS14⁻ ∷ []) ∷
   rw⁻ 4 (q57 c4) ∷
   rw⁻ 7 (q31 c4) ∷
   re 5 3 (CS04 ∷ []) ∷
   rw⁻ 6 (q56 c4) ∷
   rw⁻ 7 (q58 c4) ∷
   rw 8 (q31 c4) ∷
   rw 7 (q55 c4) ∷
   rw 6 (q53 c4) ∷
   re 5 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 10 (q75 c4) ∷
   rw 9 (q62 c4) ∷
   rw 8 (q76 c4) ∷
   rw 7 (q62 c4) ∷
   rw⁻ 5 (q75 c4) ∷
   re 6 7 (CS04 ∷ []) ∷
   rw 4 (q54 c4) ∷
   rw 3 (q77 c4) ∷
   rw 2 (q54 c4) ∷
   rw 1 (q78 c4) ∷
   rw 0 (q53 c4) ∷
   rw⁻ 1 (q31 c4) ∷
   rw⁻ 2 (q56 c4) ∷
   re 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 3 (q31 c4) ∷
   rw⁻ 4 (q57 c4) ∷
   re 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q31 c4) ∷
   rw⁻ 6 (q57 c4) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q31 c4) ∷
   rw⁻ 8 (q56 c4) ∷
   rw⁻ 9 (q58 c4) ∷
   rw⁻ 2 (q23 c4) ∷
   rw⁻ 3 (q53 c4) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 (q23 c4) ∷
   rw⁻ 5 (q54 c4) ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 (q23 c4) ∷
   rw⁻ 7 (q54 c4) ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 (q23 c4) ∷
   rw⁻ 9 (q53 c4) ∷
   rw⁻ 10 (q55 c4) ∷
   re 3 8 (Toff102 ∷ []) ∷
   re 2 3 (Toff103 ∷ []) ∷
   re 1 3 (Toff104 ∷ []) ∷
   rw⁻ 2 (q13 c4) ∷
   rw⁻ 1 (q13 c4) ∷
   re 2 3 (Toff204 ∷ []) ∷
   rw⁻ 3 (q20 c4) ∷
   re 2 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) ∷
   re 3 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) ∷
   re 4 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 4 (q53 c4) ∷
   rw⁻ 7 (q23 c4) ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 (q54 c4) ∷
   rw⁻ 9 (q23 c4) ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 (q54 c4) ∷
   rw⁻ 11 (q23 c4) ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 (q53 c4) ∷
   rw⁻ 11 (q55 c4) ∷
   rw 12 (q23 c4) ∷
   rw⁻ 3 (q56 c4) ∷
   rw⁻ 6 (q31 c4) ∷
   re 4 3 (CS14 ∷ []) ∷
   rw⁻ 5 (q57 c4) ∷
   rw⁻ 8 (q31 c4) ∷
   re 6 3 (CS14⁻ ∷ []) ∷
   rw⁻ 7 (q57 c4) ∷
   rw⁻ 10 (q31 c4) ∷
   re 8 3 (CS04 ∷ []) ∷
   rw⁻ 9 (q56 c4) ∷
   rw⁻ 10 (q58 c4) ∷
   rw 11 (q31 c4) ∷
   rw⁻ 2 (q59 c4) ∷
   rw⁻ 3 (q60 c4) ∷
   rw⁻ 6 (q13 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   rw⁻ 5 (q61 c4) ∷
   rw⁻ 8 (q13 c4) ∷
   re 6 3 (CX02 ∷ []) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q62 c4) ∷
   rw⁻ 8 (q63 c4) ∷
   rw 9 (q62 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw⁻ 8 (q59 c4) ∷
   rw⁻ 9 (q64 c4) ∷
   rw 10 (q13 c4) ∷
   rw⁻ 9 (q65 c4) ∷
   rw⁻ 8 (q66 c4) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw⁻ 9 (q67 c4) ∷
   rw 8 (q68 c4) ∷
   rw⁻ 7 (q67 c4) ∷
   re 8 3 (CS14 ∷ []) ∷
   rw 6 (q69 c4) ∷
   rw⁻ 5 (q70 c4) ∷
   rw 4 (q69 c4) ∷
   rw⁻ 3 (q71 c4) ∷
   rw⁻ 2 (q66 c4) ∷
   rw⁻ 3 (q31 c4) ∷
   rw⁻ 4 (q72 c4) ∷
   re 6 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 5 (q31 c4) ∷
   rw⁻ 6 (q73 c4) ∷
   re 8 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 7 (q31 c4) ∷
   rw⁻ 8 (q73 c4) ∷
   re 10 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 9 (q31 c4) ∷
   rw⁻ 10 (q72 c4) ∷
   rw⁻ 11 (q58 c4) ∷
   rw 4 (q74 c4) ∷
   re 4 8 (Toff213 ∷ []) ∷
   re 3 3 (Toff214 ∷ []) ∷ []) Eq.refl

private
  q79 : WsL → Eqn
  q79 c4 = eqn (Sw01 ∷ Toff201 ∷ []) (Toff201 ∷ Sw01 ∷ []) (wl0107 c4)

-- nat 0 BOX(2;014): 8 steps
lem-nat-0-BOX⟨2·014⟩ : WsL → ⟪ (Sw01 ∷ Bx2-014 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-104 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·014⟩ c4 = derive (Sw01 ∷ Bx2-014 ∷ []) (Bx2-104 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) ∷
   rw⁻ 0 (q4 c4) ∷
   rw 1 (q79 c4) ∷
   rw 2 (q10 c4) ∷
   rw 3 (q79 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   rw 5 (q10 c4) ∷
   re 0 6 (Bx2-104 ∷ []) ∷ []) Eq.refl

private
  q80 : WsL → Eqn
  q80 c4 = eqn (Sw01 ∷ Toff023 ∷ []) (Toff123 ∷ Sw01 ∷ []) (wl0108 c4)
  q81 : WsL → Eqn
  q81 c4 = eqn (Sw01 ∷ Bx2-014 ∷ []) (Bx2-104 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·014⟩ c4)

-- nat 0 BOX(0;2314): 8 steps
lem-nat-0-BOX⟨0·2314⟩ : WsL → ⟪ (Sw01 ∷ Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2304 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·2314⟩ c4 = derive (Sw01 ∷ Bx0-2314 ∷ []) (Bx1-2304 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-014 ∷ Toff023 ∷ CCZ023 ∷ Bx2-014 ∷ []) ∷
   rw⁻ 0 (q8 c4) ∷
   rw 1 (q80 c4) ∷
   rw 2 (q81 c4) ∷
   rw 3 (q80 c4) ∷
   rw⁻ 4 (q8 c4) ∷
   rw 5 (q81 c4) ∷
   re 0 6 (Bx1-2304 ∷ []) ∷ []) Eq.refl

-- nat 0 BOX(2;104): 8 steps
lem-nat-0-BOX⟨2·104⟩ : WsL → ⟪ (Sw01 ∷ Bx2-104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-014 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·104⟩ c4 = derive (Sw01 ∷ Bx2-104 ∷ []) (Bx2-014 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff201 ∷ Bx1-24 ∷ Toff201 ∷ CCZ012 ∷ Bx1-24 ∷ []) ∷
   rw⁻ 0 (q4 c4) ∷
   rw 1 (q79 c4) ∷
   rw 2 (q3 c4) ∷
   rw 3 (q79 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   rw 5 (q3 c4) ∷
   re 0 6 (Bx2-014 ∷ []) ∷ []) Eq.refl

private
  q82 : WsL → Eqn
  q82 c4 = eqn (Sw01 ∷ Toff123 ∷ []) (Toff023 ∷ Sw01 ∷ []) (wl0053 c4)
  q83 : WsL → Eqn
  q83 c4 = eqn (Sw01 ∷ Bx2-104 ∷ []) (Bx2-014 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·104⟩ c4)

-- nat 0 BOX(1;2304): 8 steps
lem-nat-0-BOX⟨1·2304⟩ : WsL → ⟪ (Sw01 ∷ Bx1-2304 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·2304⟩ c4 = derive (Sw01 ∷ Bx1-2304 ∷ []) (Bx0-2314 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff123 ∷ Bx2-104 ∷ Toff123 ∷ CCZ123 ∷ Bx2-104 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   rw 1 (q82 c4) ∷
   rw 2 (q83 c4) ∷
   rw 3 (q82 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   rw 5 (q83 c4) ∷
   re 0 6 (Bx0-2314 ∷ []) ∷ []) Eq.refl

private
  q84 : WsL → Eqn
  q84 c4 = eqn (Sw01 ∷ Bx0-23 ∷ []) (Bx0-23 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ))

-- nat 0 BOX(0;23): 2 steps
lem-nat-0-BOX⟨0·23⟩ : WsL → ⟪ (Sw01 ∷ Bx0-23 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-23 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·23⟩ c4 = derive (Sw01 ∷ Bx0-23 ∷ []) (Bx1-23 ∷ Sw01 ∷ [])
  (rw 0 (q84 c4) ∷
   re 0 1 (Bx1-23 ∷ []) ∷ []) Eq.refl

private
  q85 : WsL → Eqn
  q85 c4 = eqn (Sw01 ∷ CCZ024 ∷ []) (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4)
  q86 : WsL → Eqn
  q86 c4 = eqn (Sw01 ∷ Toff204 ∷ []) (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4)
  q87 : WsL → Eqn
  q87 c4 = eqn (Sw01 ∷ Bx0-23 ∷ []) (Bx1-23 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·23⟩ c4)

-- nat 0 BOX(2;043): 8 steps
lem-nat-0-BOX⟨2·043⟩ : WsL → ⟪ (Sw01 ∷ Bx2-043 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-143 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·043⟩ c4 = derive (Sw01 ∷ Bx2-043 ∷ []) (Bx2-143 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ CCZ024 ∷ Bx0-23 ∷ []) ∷
   rw 0 (q85 c4) ∷
   rw 1 (q86 c4) ∷
   rw 2 (q87 c4) ∷
   rw 3 (q86 c4) ∷
   rw 4 (q85 c4) ∷
   rw 5 (q87 c4) ∷
   re 0 6 (Bx2-143 ∷ []) ∷ []) Eq.refl

private
  q88 : WsL → Eqn
  q88 c4 = eqn (Sw01 ∷ Bx2-043 ∷ []) (Bx2-143 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·043⟩ c4)

-- nat 0 BOX(0;2143): 8 steps
lem-nat-0-BOX⟨0·2143⟩ : WsL → ⟪ (Sw01 ∷ Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2043 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·2143⟩ c4 = derive (Sw01 ∷ Bx0-2143 ∷ []) (Bx1-2043 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-043 ∷ Toff012 ∷ CCZ012 ∷ Bx2-043 ∷ []) ∷
   rw⁻ 0 (q4 c4) ∷
   rw 1 (q11 c4) ∷
   rw 2 (q88 c4) ∷
   rw 3 (q11 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   rw 5 (q88 c4) ∷
   re 0 6 (Bx1-2043 ∷ []) ∷ []) Eq.refl

private
  q89 : WsL → Eqn
  q89 c4 = eqn (Sw01 ∷ Bx1-23 ∷ []) (Bx1-23 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ))

-- nat 0 BOX(1;23): 2 steps
lem-nat-0-BOX⟨1·23⟩ : WsL → ⟪ (Sw01 ∷ Bx1-23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-23 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·23⟩ c4 = derive (Sw01 ∷ Bx1-23 ∷ []) (Bx0-23 ∷ Sw01 ∷ [])
  (rw 0 (q89 c4) ∷
   re 0 1 (Bx0-23 ∷ []) ∷ []) Eq.refl

private
  q90 : WsL → Eqn
  q90 c4 = eqn (Sw01 ∷ CCZ124 ∷ []) (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4)
  q91 : WsL → Eqn
  q91 c4 = eqn (Sw01 ∷ Toff214 ∷ []) (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4)
  q92 : WsL → Eqn
  q92 c4 = eqn (Sw01 ∷ Bx1-23 ∷ []) (Bx0-23 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·23⟩ c4)

-- nat 0 BOX(2;143): 8 steps
lem-nat-0-BOX⟨2·143⟩ : WsL → ⟪ (Sw01 ∷ Bx2-143 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-043 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·143⟩ c4 = derive (Sw01 ∷ Bx2-143 ∷ []) (Bx2-043 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff214 ∷ Bx1-23 ∷ Toff214 ∷ CCZ124 ∷ Bx1-23 ∷ []) ∷
   rw 0 (q90 c4) ∷
   rw 1 (q91 c4) ∷
   rw 2 (q92 c4) ∷
   rw 3 (q91 c4) ∷
   rw 4 (q90 c4) ∷
   rw 5 (q92 c4) ∷
   re 0 6 (Bx2-043 ∷ []) ∷ []) Eq.refl

private
  q93 : WsL → Eqn
  q93 c4 = eqn (Sw01 ∷ Bx2-143 ∷ []) (Bx2-043 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·143⟩ c4)

-- nat 0 BOX(1;2043): 8 steps
lem-nat-0-BOX⟨1·2043⟩ : WsL → ⟪ (Sw01 ∷ Bx1-2043 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·2043⟩ c4 = derive (Sw01 ∷ Bx1-2043 ∷ []) (Bx0-2143 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff102 ∷ Bx2-143 ∷ Toff102 ∷ CCZ012 ∷ Bx2-143 ∷ []) ∷
   rw⁻ 0 (q4 c4) ∷
   rw 1 (q5 c4) ∷
   rw 2 (q93 c4) ∷
   rw 3 (q5 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   rw 5 (q93 c4) ∷
   re 0 6 (Bx0-2143 ∷ []) ∷ []) Eq.refl

-- resp TOFF023 at 1: 2 steps
lem-resp-TOFF023-at-1 : WsL → ⟪ (Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF023-at-1 c4 = derive (Toff023 ∷ []) (Sw01 ∷ Toff123 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q20 c4) ∷
   rw⁻ 0 (q82 c4) ∷ []) Eq.refl

private
  q94 : WsL → Eqn
  q94 c4 = eqn (CZ03 ∷ Sw12 ∷ []) (Sw12 ∷ CZ03 ∷ []) (wl0098 c4)
  q95 : WsL → Eqn
  q95 c4 = eqn (CZ03 ∷ Sw01 ∷ []) (Sw01 ∷ CZ13 ∷ []) (wl0088 c4)

-- resp CZ04 at 2: 12 steps
lem-resp-CZ04-at-2 : WsL → ⟪ (CZ04 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CZ14 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CZ04-at-2 c4 = derive (CZ04 ∷ []) (Sw12 ∷ Sw01 ∷ CZ14 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q13 c4) ∷
   re 0 1 (Sw34 ∷ CZ03 ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q62 c4) ∷
   rw 1 (q94 c4) ∷
   rw⁻ 0 (q62 c4) ∷
   re 1 3 (CZ04 ∷ []) ∷
   rw⁻ 2 (q20 c4) ∷
   re 1 1 (Sw34 ∷ CZ03 ∷ Sw34 ∷ []) ∷
   rw⁻ 3 (q67 c4) ∷
   rw 2 (q95 c4) ∷
   rw⁻ 1 (q67 c4) ∷
   re 2 3 (CZ14 ∷ []) ∷ []) Eq.refl

-- resp CZ04 at 1: 6 steps
lem-resp-CZ04-at-1 : WsL → ⟪ (CZ04 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CZ14 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CZ04-at-1 c4 = derive (CZ04 ∷ []) (Sw01 ∷ CZ14 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q20 c4) ∷
   re 0 1 (Sw34 ∷ CZ03 ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q67 c4) ∷
   rw 1 (q95 c4) ∷
   rw⁻ 0 (q67 c4) ∷
   re 1 3 (CZ14 ∷ []) ∷ []) Eq.refl

private
  q96 : WsL → Eqn
  q96 c4 = eqn (CZ12 ∷ Sw12 ∷ []) (Sw12 ∷ CZ12 ∷ []) (wl0109 c4)

-- nat 1 BOX(0;21): 3 steps
lem-nat-1-BOX⟨0·21⟩ : WsL → ⟪ (Sw12 ∷ Bx0-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-12 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·21⟩ c4 = derive (Sw12 ∷ Bx0-21 ∷ []) (Bx0-12 ∷ Sw12 ∷ [])
  (re 1 1 (CZ12 ∷ []) ∷
   rw⁻ 0 (q96 c4) ∷
   re 0 1 (Bx0-12 ∷ []) ∷ []) Eq.refl

private
  q97 : WsL → Eqn
  q97 c4 = eqn (Sw12 ∷ Bx0-21 ∷ []) (Bx0-12 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·21⟩ c4)

-- nat 1 BOX(2;041): 8 steps
lem-nat-1-BOX⟨2·041⟩ : WsL → ⟪ (Sw12 ∷ Bx2-041 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-042 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·041⟩ c4 = derive (Sw12 ∷ Bx2-041 ∷ []) (Bx1-042 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) ∷
   rw 0 (q44 c4) ∷
   rw 1 (q45 c4) ∷
   rw 2 (q97 c4) ∷
   rw 3 (q45 c4) ∷
   rw 4 (q44 c4) ∷
   rw 5 (q97 c4) ∷
   re 0 6 (Bx1-042 ∷ []) ∷ []) Eq.refl

private
  q98 : WsL → Eqn
  q98 c4 = eqn (Sw12 ∷ Bx2-041 ∷ []) (Bx1-042 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·041⟩ c4)

-- nat 1 BOX(0;2341): 8 steps
lem-nat-1-BOX⟨0·2341⟩ : WsL → ⟪ (Sw12 ∷ Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·2341⟩ c4 = derive (Sw12 ∷ Bx0-2341 ∷ []) (Bx0-1342 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-041 ∷ Toff023 ∷ CCZ023 ∷ Bx2-041 ∷ []) ∷
   rw 0 (q17 c4) ∷
   rw 1 (q18 c4) ∷
   rw 2 (q98 c4) ∷
   rw 3 (q18 c4) ∷
   rw 4 (q17 c4) ∷
   rw 5 (q98 c4) ∷
   re 0 6 (Bx0-1342 ∷ []) ∷ []) Eq.refl

-- nat 1 CS01: 2 steps
lem-nat-1-CS01 : WsL → ⟪ (Sw12 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CS01 c4 = derive (Sw12 ∷ CS01 ∷ []) (CS02 ∷ Sw12 ∷ [])
  (rw⁻ 2 (q13 c4) ∷
   re 0 3 (CS02 ∷ []) ∷ []) Eq.refl

-- nat 1 CS02: 2 steps
lem-nat-1-CS02 : WsL → ⟪ (Sw12 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CS02 c4 = derive (Sw12 ∷ CS02 ∷ []) (CS01 ∷ Sw12 ∷ [])
  (re 1 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 0 (q13 c4) ∷ []) Eq.refl

-- nat 1 BOX(0;12): 3 steps
lem-nat-1-BOX⟨0·12⟩ : WsL → ⟪ (Sw12 ∷ Bx0-12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-21 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·12⟩ c4 = derive (Sw12 ∷ Bx0-12 ∷ []) (Bx0-21 ∷ Sw12 ∷ [])
  (re 1 1 (CZ12 ∷ []) ∷
   rw⁻ 0 (q96 c4) ∷
   re 0 1 (Bx0-21 ∷ []) ∷ []) Eq.refl

private
  q99 : WsL → Eqn
  q99 c4 = eqn (Sw12 ∷ CCZ014 ∷ []) (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4)
  q100 : WsL → Eqn
  q100 c4 = eqn (Sw12 ∷ Toff104 ∷ []) (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4)
  q101 : WsL → Eqn
  q101 c4 = eqn (Sw12 ∷ Bx0-12 ∷ []) (Bx0-21 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·12⟩ c4)

-- nat 1 BOX(1;042): 8 steps
lem-nat-1-BOX⟨1·042⟩ : WsL → ⟪ (Sw12 ∷ Bx1-042 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-041 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·042⟩ c4 = derive (Sw12 ∷ Bx1-042 ∷ []) (Bx2-041 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) ∷
   rw 0 (q99 c4) ∷
   rw 1 (q100 c4) ∷
   rw 2 (q101 c4) ∷
   rw 3 (q100 c4) ∷
   rw 4 (q99 c4) ∷
   rw 5 (q101 c4) ∷
   re 0 6 (Bx2-041 ∷ []) ∷ []) Eq.refl

private
  q102 : WsL → Eqn
  q102 c4 = eqn (Sw12 ∷ CCZ013 ∷ []) (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4)
  q103 : WsL → Eqn
  q103 c4 = eqn (Sw12 ∷ Toff013 ∷ []) (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4)
  q104 : WsL → Eqn
  q104 c4 = eqn (Sw12 ∷ Bx1-042 ∷ []) (Bx2-041 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·042⟩ c4)

-- nat 1 BOX(0;1342): 8 steps
lem-nat-1-BOX⟨0·1342⟩ : WsL → ⟪ (Sw12 ∷ Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·1342⟩ c4 = derive (Sw12 ∷ Bx0-1342 ∷ []) (Bx0-2341 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-042 ∷ Toff013 ∷ CCZ013 ∷ Bx1-042 ∷ []) ∷
   rw 0 (q102 c4) ∷
   rw 1 (q103 c4) ∷
   rw 2 (q104 c4) ∷
   rw 3 (q103 c4) ∷
   rw 4 (q102 c4) ∷
   rw 5 (q104 c4) ∷
   re 0 6 (Bx0-2341 ∷ []) ∷ []) Eq.refl

private
  q105 : WsL → Eqn
  q105 c4 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (c₁ (K) (Swap ↑))
  q106 : WsL → Eqn
  q106 c4 = eqn (K0 ∷ Sw34 ∷ []) (Sw34 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ ↑))
  q107 : WsL → Eqn
  q107 c4 = eqn (K0 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ []) (c₁ (K) (Swap))
  q108 : WsL → Eqn
  q108 c4 = eqn (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ []) (wl0031 c4)
  q109 : WsL → Eqn
  q109 c4 = eqn (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (wl0032 c4)

-- resp TOFF024 at 1: 71 steps
lem-resp-TOFF024-at-1 : WsL → ⟪ (Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff124 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF024-at-1 c4 = derive (Toff024 ∷ []) (Sw01 ∷ Toff124 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q20 c4) ∷
   re 0 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) ∷
   re 1 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) ∷
   re 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 2 (q105 c4) ∷
   rw⁻ 5 (q23 c4) ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 (q54 c4) ∷
   rw⁻ 7 (q23 c4) ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 (q54 c4) ∷
   rw⁻ 9 (q23 c4) ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 (q105 c4) ∷
   rw⁻ 9 (q55 c4) ∷
   rw 10 (q23 c4) ∷
   rw⁻ 1 (q106 c4) ∷
   rw⁻ 4 (q31 c4) ∷
   re 2 3 (CS14 ∷ []) ∷
   rw⁻ 3 (q57 c4) ∷
   rw⁻ 6 (q31 c4) ∷
   re 4 3 (CS14⁻ ∷ []) ∷
   rw⁻ 5 (q57 c4) ∷
   rw⁻ 8 (q31 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw⁻ 7 (q106 c4) ∷
   rw⁻ 8 (q58 c4) ∷
   rw 9 (q31 c4) ∷
   rw⁻ 0 (q107 c4) ∷
   rw⁻ 1 (q60 c4) ∷
   rw⁻ 4 (q13 c4) ∷
   re 2 3 (CX02 ∷ []) ∷
   rw⁻ 3 (q61 c4) ∷
   rw⁻ 6 (q13 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 5 (q62 c4) ∷
   rw⁻ 6 (q63 c4) ∷
   rw 7 (q62 c4) ∷
   re 5 3 (CS04 ∷ []) ∷
   rw⁻ 6 (q107 c4) ∷
   rw⁻ 7 (q64 c4) ∷
   rw 8 (q13 c4) ∷
   rw⁻ 7 (q65 c4) ∷
   rw 6 (q108 c4) ∷
   re 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw⁻ 7 (q67 c4) ∷
   rw 6 (q68 c4) ∷
   rw⁻ 5 (q67 c4) ∷
   re 6 3 (CS14 ∷ []) ∷
   rw 4 (q69 c4) ∷
   rw⁻ 3 (q70 c4) ∷
   rw 2 (q69 c4) ∷
   rw⁻ 1 (q71 c4) ∷
   rw 0 (q108 c4) ∷
   rw⁻ 1 (q31 c4) ∷
   rw⁻ 2 (q56 c4) ∷
   re 4 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 3 (q31 c4) ∷
   rw⁻ 4 (q73 c4) ∷
   re 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q31 c4) ∷
   rw⁻ 6 (q73 c4) ∷
   re 8 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 7 (q31 c4) ∷
   rw⁻ 8 (q56 c4) ∷
   rw⁻ 9 (q58 c4) ∷
   rw 2 (q109 c4) ∷
   re 2 8 (Toff123 ∷ []) ∷
   re 1 3 (Toff124 ∷ []) ∷ []) Eq.refl

-- resp CZ03 at 1: 2 steps
lem-resp-CZ03-at-1 : WsL → ⟪ (CZ03 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CZ13 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CZ03-at-1 c4 = derive (CZ03 ∷ []) (Sw01 ∷ CZ13 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q20 c4) ∷
   rw 0 (q95 c4) ∷ []) Eq.refl

private
  q110 : WsL → Eqn
  q110 c4 = eqn (Sw01 ∷ Toff312 ∷ []) (Toff302 ∷ Sw01 ∷ []) (wl0110 c4)

-- resp TOFF301 at 2: 5 steps
lem-resp-TOFF301-at-2 : WsL → ⟪ (Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff312 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF301-at-2 c4 = derive (Toff301 ∷ []) (Sw12 ∷ Sw01 ∷ Toff312 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q13 c4) ∷
   rw⁻ 0 (q13 c4) ∷
   re 1 3 (Toff302 ∷ []) ∷
   rw⁻ 2 (q20 c4) ∷
   rw⁻ 1 (q110 c4) ∷ []) Eq.refl

private
  q111 : WsL → Eqn
  q111 c4 = eqn (CZ14 ∷ Sw23 ∷ []) (Sw23 ∷ CZ14 ∷ []) (wl0042 c4)

-- nat 2 BOXd(0;14): 3 steps
lem-nat-2-BOXd⟨0·14⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻0-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-14 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·14⟩ c4 = derive (Sw23 ∷ Bx⁻0-14 ∷ []) (Bx⁻0-14 ∷ Sw23 ∷ [])
  (re 1 1 (CZ14 ∷ []) ∷
   rw⁻ 0 (q111 c4) ∷
   re 0 1 (Bx⁻0-14 ∷ []) ∷ []) Eq.refl

private
  q112 : WsL → Eqn
  q112 c4 = eqn (Sw23 ∷ Bx⁻0-14 ∷ []) (Bx⁻0-14 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·14⟩ c4)
  q113 : WsL → Eqn
  q113 c4 = eqn (Sw23 ∷ Toff102 ∷ []) (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4)

-- nat 2 BOXd(1;024): 8 steps
lem-nat-2-BOXd⟨1·024⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻1-024 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-034 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·024⟩ c4 = derive (Sw23 ∷ Bx⁻1-024 ∷ []) (Bx⁻1-034 ∷ Sw23 ∷ [])
  (re 1 1 (Bx⁻0-14 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻0-14 ∷ Toff102 ∷ CCZ012 ∷ []) ∷
   rw 0 (q112 c4) ∷
   rw 1 (q28 c4) ∷
   rw 2 (q113 c4) ∷
   rw 3 (q112 c4) ∷
   rw 4 (q113 c4) ∷
   rw 5 (q28 c4) ∷
   re 0 6 (Bx⁻1-034 ∷ []) ∷ []) Eq.refl

private
  q114 : WsL → Eqn
  q114 c4 = eqn (Sw23 ∷ Bx⁻1-024 ∷ []) (Bx⁻1-034 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·024⟩ c4)

-- nat 2 BOXd(0;1324): 8 steps
lem-nat-2-BOXd⟨0·1324⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-1234 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·1324⟩ c4 = derive (Sw23 ∷ Bx⁻0-1324 ∷ []) (Bx⁻0-1234 ∷ Sw23 ∷ [])
  (re 1 1 (Bx⁻1-024 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻1-024 ∷ Toff013 ∷ CCZ013 ∷ []) ∷
   rw 0 (q114 c4) ∷
   rw 1 (q41 c4) ∷
   rw 2 (q42 c4) ∷
   rw 3 (q114 c4) ∷
   rw 4 (q42 c4) ∷
   rw 5 (q41 c4) ∷
   re 0 6 (Bx⁻0-1234 ∷ []) ∷ []) Eq.refl

private
  q115 : WsL → Eqn
  q115 c4 = eqn (Sw34 ∷ CZ13 ∷ []) (CZ14 ∷ Sw34 ∷ []) (lem-nat-3-CZ13 c4)

-- nat 3 BOXd(0;13): 3 steps
lem-nat-3-BOXd⟨0·13⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻0-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-14 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·13⟩ c4 = derive (Sw34 ∷ Bx⁻0-13 ∷ []) (Bx⁻0-14 ∷ Sw34 ∷ [])
  (re 1 1 (CZ13 ∷ []) ∷
   rw 0 (q115 c4) ∷
   re 0 1 (Bx⁻0-14 ∷ []) ∷ []) Eq.refl

private
  q116 : WsL → Eqn
  q116 c4 = eqn (Sw34 ∷ Bx⁻0-13 ∷ []) (Bx⁻0-14 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·13⟩ c4)
  q117 : WsL → Eqn
  q117 c4 = eqn (Toff102 ∷ Sw34 ∷ []) (Sw34 ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (Swap))

-- nat 3 BOXd(1;023): 8 steps
lem-nat-3-BOXd⟨1·023⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻1-023 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-024 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨1·023⟩ c4 = derive (Sw34 ∷ Bx⁻1-023 ∷ []) (Bx⁻1-024 ∷ Sw34 ∷ [])
  (re 1 1 (Bx⁻0-13 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻0-13 ∷ Toff102 ∷ CCZ012 ∷ []) ∷
   rw 0 (q116 c4) ∷
   rw⁻ 1 (q36 c4) ∷
   rw⁻ 2 (q117 c4) ∷
   rw 3 (q116 c4) ∷
   rw⁻ 4 (q117 c4) ∷
   rw⁻ 5 (q36 c4) ∷
   re 0 6 (Bx⁻1-024 ∷ []) ∷ []) Eq.refl

private
  q118 : WsL → Eqn
  q118 c4 = eqn (Sw34 ∷ Bx⁻1-023 ∷ []) (Bx⁻1-024 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·023⟩ c4)
  q119 : WsL → Eqn
  q119 c4 = eqn (Sw34 ∷ CCZ014 ∷ []) (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4)
  q120 : WsL → Eqn
  q120 c4 = eqn (Sw34 ∷ Toff014 ∷ []) (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4)

-- nat 3 BOXd(0;1423): 8 steps
lem-nat-3-BOXd⟨0·1423⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-1324 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·1423⟩ c4 = derive (Sw34 ∷ Bx⁻0-1423 ∷ []) (Bx⁻0-1324 ∷ Sw34 ∷ [])
  (re 1 1 (Bx⁻1-023 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻1-023 ∷ Toff014 ∷ CCZ014 ∷ []) ∷
   rw 0 (q118 c4) ∷
   rw 1 (q119 c4) ∷
   rw 2 (q120 c4) ∷
   rw 3 (q118 c4) ∷
   rw 4 (q120 c4) ∷
   rw 5 (q119 c4) ∷
   re 0 6 (Bx⁻0-1324 ∷ []) ∷ []) Eq.refl

private
  q121 : WsL → Eqn
  q121 c4 = eqn (CZ13 ∷ Sw01 ∷ []) (Sw01 ∷ CZ03 ∷ []) (wl0092 c4)

-- nat 0 BOXd(1;03): 3 steps
lem-nat-0-BOXd⟨1·03⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻1-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-13 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·03⟩ c4 = derive (Sw01 ∷ Bx⁻1-03 ∷ []) (Bx⁻0-13 ∷ Sw01 ∷ [])
  (re 1 1 (CZ03 ∷ []) ∷
   rw⁻ 0 (q121 c4) ∷
   re 0 1 (Bx⁻0-13 ∷ []) ∷ []) Eq.refl

private
  q122 : WsL → Eqn
  q122 c4 = eqn (Sw01 ∷ Bx⁻1-03 ∷ []) (Bx⁻0-13 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·03⟩ c4)

-- nat 0 BOXd(0;123): 8 steps
lem-nat-0-BOXd⟨0·123⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻0-123 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-023 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨0·123⟩ c4 = derive (Sw01 ∷ Bx⁻0-123 ∷ []) (Bx⁻1-023 ∷ Sw01 ∷ [])
  (re 1 1 (Bx⁻1-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻1-03 ∷ Toff012 ∷ CCZ012 ∷ []) ∷
   rw 0 (q122 c4) ∷
   rw⁻ 1 (q4 c4) ∷
   rw 2 (q11 c4) ∷
   rw 3 (q122 c4) ∷
   rw 4 (q11 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   re 0 6 (Bx⁻1-023 ∷ []) ∷ []) Eq.refl

private
  q123 : WsL → Eqn
  q123 c4 = eqn (Sw01 ∷ Bx⁻0-123 ∷ []) (Bx⁻1-023 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·123⟩ c4)
  q124 : WsL → Eqn
  q124 c4 = eqn (Sw01 ∷ CCZ014 ∷ []) (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4)
  q125 : WsL → Eqn
  q125 c4 = eqn (Sw01 ∷ Toff104 ∷ []) (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4)

-- nat 0 BOXd(1;0423): 8 steps
lem-nat-0-BOXd⟨1·0423⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-1423 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·0423⟩ c4 = derive (Sw01 ∷ Bx⁻1-0423 ∷ []) (Bx⁻0-1423 ∷ Sw01 ∷ [])
  (re 1 1 (Bx⁻0-123 ∷ CCZ014 ∷ Toff104 ∷ Bx⁻0-123 ∷ Toff104 ∷ CCZ014 ∷ []) ∷
   rw 0 (q123 c4) ∷
   rw 1 (q124 c4) ∷
   rw 2 (q125 c4) ∷
   rw 3 (q123 c4) ∷
   rw 4 (q125 c4) ∷
   rw 5 (q124 c4) ∷
   re 0 6 (Bx⁻0-1423 ∷ []) ∷ []) Eq.refl

-- nat 1 BOXd(2;03): 3 steps
lem-nat-1-BOXd⟨2·03⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻2-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-03 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·03⟩ c4 = derive (Sw12 ∷ Bx⁻2-03 ∷ []) (Bx⁻1-03 ∷ Sw12 ∷ [])
  (re 1 1 (CZ03 ∷ []) ∷
   rw⁻ 0 (q94 c4) ∷
   re 0 1 (Bx⁻1-03 ∷ []) ∷ []) Eq.refl

private
  q126 : WsL → Eqn
  q126 c4 = eqn (Sw12 ∷ Bx⁻2-03 ∷ []) (Bx⁻1-03 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·03⟩ c4)

-- nat 1 BOXd(0;213): 8 steps
lem-nat-1-BOXd⟨0·213⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻0-213 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-123 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·213⟩ c4 = derive (Sw12 ∷ Bx⁻0-213 ∷ []) (Bx⁻0-123 ∷ Sw12 ∷ [])
  (re 1 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) ∷
   rw 0 (q126 c4) ∷
   rw⁻ 1 (q14 c4) ∷
   rw 2 (q47 c4) ∷
   rw 3 (q126 c4) ∷
   rw 4 (q47 c4) ∷
   rw⁻ 5 (q14 c4) ∷
   re 0 6 (Bx⁻0-123 ∷ []) ∷ []) Eq.refl

private
  q127 : WsL → Eqn
  q127 c4 = eqn (Sw12 ∷ Bx⁻0-213 ∷ []) (Bx⁻0-123 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·213⟩ c4)

-- nat 1 BOXd(2;0413): 8 steps
lem-nat-1-BOXd⟨2·0413⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0423 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·0413⟩ c4 = derive (Sw12 ∷ Bx⁻2-0413 ∷ []) (Bx⁻1-0423 ∷ Sw12 ∷ [])
  (re 1 1 (Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) ∷
   rw 0 (q127 c4) ∷
   rw 1 (q44 c4) ∷
   rw 2 (q45 c4) ∷
   rw 3 (q127 c4) ∷
   rw 4 (q45 c4) ∷
   rw 5 (q44 c4) ∷
   re 0 6 (Bx⁻1-0423 ∷ []) ∷ []) Eq.refl

private
  q128 : WsL → Eqn
  q128 c4 = eqn (CZ14 ∷ Sw12 ∷ []) (Sw12 ∷ CZ24 ∷ []) (wl0005 c4)

-- nat 1 BOXd(0;24): 3 steps
lem-nat-1-BOXd⟨0·24⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻0-24 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-14 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·24⟩ c4 = derive (Sw12 ∷ Bx⁻0-24 ∷ []) (Bx⁻0-14 ∷ Sw12 ∷ [])
  (re 1 1 (CZ24 ∷ []) ∷
   rw⁻ 0 (q128 c4) ∷
   re 0 1 (Bx⁻0-14 ∷ []) ∷ []) Eq.refl

private
  q129 : WsL → Eqn
  q129 c4 = eqn (Sw12 ∷ Bx⁻0-24 ∷ []) (Bx⁻0-14 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·24⟩ c4)
  q130 : WsL → Eqn
  q130 c4 = eqn (Sw12 ∷ Toff203 ∷ []) (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4)

-- nat 1 BOXd(2;034): 8 steps
lem-nat-1-BOXd⟨2·034⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻2-034 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-034 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·034⟩ c4 = derive (Sw12 ∷ Bx⁻2-034 ∷ []) (Bx⁻1-034 ∷ Sw12 ∷ [])
  (re 1 1 (Bx⁻0-24 ∷ CCZ023 ∷ Toff203 ∷ Bx⁻0-24 ∷ Toff203 ∷ CCZ023 ∷ []) ∷
   rw 0 (q129 c4) ∷
   rw 1 (q17 c4) ∷
   rw 2 (q130 c4) ∷
   rw 3 (q129 c4) ∷
   rw 4 (q130 c4) ∷
   rw 5 (q17 c4) ∷
   re 0 6 (Bx⁻1-034 ∷ []) ∷ []) Eq.refl

private
  q131 : WsL → Eqn
  q131 c4 = eqn (Sw12 ∷ Bx⁻2-034 ∷ []) (Bx⁻1-034 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·034⟩ c4)

-- nat 1 BOXd(0;2134): 8 steps
lem-nat-1-BOXd⟨0·2134⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-1234 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·2134⟩ c4 = derive (Sw12 ∷ Bx⁻0-2134 ∷ []) (Bx⁻0-1234 ∷ Sw12 ∷ [])
  (re 1 1 (Bx⁻2-034 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-034 ∷ Toff012 ∷ CCZ012 ∷ []) ∷
   rw 0 (q131 c4) ∷
   rw⁻ 1 (q14 c4) ∷
   rw 2 (q47 c4) ∷
   rw 3 (q131 c4) ∷
   rw 4 (q47 c4) ∷
   rw⁻ 5 (q14 c4) ∷
   re 0 6 (Bx⁻0-1234 ∷ []) ∷ []) Eq.refl

private
  q132 : WsL → Eqn
  q132 c4 = eqn (CZ24 ∷ Sw23 ∷ []) (Sw23 ∷ CZ34 ∷ []) (wl0027 c4)

-- nat 2 BOXd(0;34): 3 steps
lem-nat-2-BOXd⟨0·34⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻0-34 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-24 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·34⟩ c4 = derive (Sw23 ∷ Bx⁻0-34 ∷ []) (Bx⁻0-24 ∷ Sw23 ∷ [])
  (re 1 1 (CZ34 ∷ []) ∷
   rw⁻ 0 (q132 c4) ∷
   re 0 1 (Bx⁻0-24 ∷ []) ∷ []) Eq.refl

private
  q133 : WsL → Eqn
  q133 c4 = eqn (Sw23 ∷ Bx⁻0-34 ∷ []) (Bx⁻0-24 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·34⟩ c4)
  q134 : WsL → Eqn
  q134 c4 = eqn (CCZ023 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ023 ∷ []) (wl0065 c4)
  q135 : WsL → Eqn
  q135 c4 = eqn (Sw23 ∷ Toff302 ∷ []) (Toff203 ∷ Sw23 ∷ []) (wl0066 c4)

-- nat 2 BOXd(3;024): 8 steps
lem-nat-2-BOXd⟨3·024⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻3-024 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-034 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨3·024⟩ c4 = derive (Sw23 ∷ Bx⁻3-024 ∷ []) (Bx⁻2-034 ∷ Sw23 ∷ [])
  (re 1 1 (Bx⁻0-34 ∷ CCZ023 ∷ Toff302 ∷ Bx⁻0-34 ∷ Toff302 ∷ CCZ023 ∷ []) ∷
   rw 0 (q133 c4) ∷
   rw⁻ 1 (q134 c4) ∷
   rw 2 (q135 c4) ∷
   rw 3 (q133 c4) ∷
   rw 4 (q135 c4) ∷
   rw⁻ 5 (q134 c4) ∷
   re 0 6 (Bx⁻2-034 ∷ []) ∷ []) Eq.refl

private
  q136 : WsL → Eqn
  q136 c4 = eqn (Sw23 ∷ Bx⁻3-024 ∷ []) (Bx⁻2-034 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨3·024⟩ c4)

-- nat 2 BOXd(0;3124): 8 steps
lem-nat-2-BOXd⟨0·3124⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-2134 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·3124⟩ c4 = derive (Sw23 ∷ Bx⁻0-3124 ∷ []) (Bx⁻0-2134 ∷ Sw23 ∷ [])
  (re 1 1 (Bx⁻3-024 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻3-024 ∷ Toff013 ∷ CCZ013 ∷ []) ∷
   rw 0 (q136 c4) ∷
   rw 1 (q41 c4) ∷
   rw 2 (q42 c4) ∷
   rw 3 (q136 c4) ∷
   rw 4 (q42 c4) ∷
   rw 5 (q41 c4) ∷
   re 0 6 (Bx⁻0-2134 ∷ []) ∷ []) Eq.refl

private
  q137 : WsL → Eqn
  q137 c4 = eqn (CZ34 ∷ Sw34 ∷ []) (Sw34 ∷ CZ34 ∷ []) (wl0069 c4)

-- nat 3 BOXd(0;43): 3 steps
lem-nat-3-BOXd⟨0·43⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻0-43 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-34 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·43⟩ c4 = derive (Sw34 ∷ Bx⁻0-43 ∷ []) (Bx⁻0-34 ∷ Sw34 ∷ [])
  (re 1 1 (CZ34 ∷ []) ∷
   rw⁻ 0 (q137 c4) ∷
   re 0 1 (Bx⁻0-34 ∷ []) ∷ []) Eq.refl

private
  q138 : WsL → Eqn
  q138 c4 = eqn (Sw34 ∷ Bx⁻0-43 ∷ []) (Bx⁻0-34 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·43⟩ c4)
  q139 : WsL → Eqn
  q139 c4 = eqn (Sw34 ∷ CCZ024 ∷ []) (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4)
  q140 : WsL → Eqn
  q140 c4 = eqn (Sw34 ∷ Toff402 ∷ []) (Toff302 ∷ Sw34 ∷ []) (lem-nat-3-TOFF402 c4)

-- nat 3 BOXd(4;023): 8 steps
lem-nat-3-BOXd⟨4·023⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻4-023 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻3-024 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨4·023⟩ c4 = derive (Sw34 ∷ Bx⁻4-023 ∷ []) (Bx⁻3-024 ∷ Sw34 ∷ [])
  (re 1 1 (Bx⁻0-43 ∷ CCZ024 ∷ Toff402 ∷ Bx⁻0-43 ∷ Toff402 ∷ CCZ024 ∷ []) ∷
   rw 0 (q138 c4) ∷
   rw 1 (q139 c4) ∷
   rw 2 (q140 c4) ∷
   rw 3 (q138 c4) ∷
   rw 4 (q140 c4) ∷
   rw 5 (q139 c4) ∷
   re 0 6 (Bx⁻3-024 ∷ []) ∷ []) Eq.refl

private
  q141 : WsL → Eqn
  q141 c4 = eqn (Sw34 ∷ Bx⁻4-023 ∷ []) (Bx⁻3-024 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨4·023⟩ c4)

-- nat 3 BOXd(0;4123): 8 steps
lem-nat-3-BOXd⟨0·4123⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-3124 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·4123⟩ c4 = derive (Sw34 ∷ Bx⁻0-4123 ∷ []) (Bx⁻0-3124 ∷ Sw34 ∷ [])
  (re 1 1 (Bx⁻4-023 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻4-023 ∷ Toff014 ∷ CCZ014 ∷ []) ∷
   rw 0 (q141 c4) ∷
   rw 1 (q119 c4) ∷
   rw 2 (q120 c4) ∷
   rw 3 (q141 c4) ∷
   rw 4 (q120 c4) ∷
   rw 5 (q119 c4) ∷
   re 0 6 (Bx⁻0-3124 ∷ []) ∷ []) Eq.refl

private
  q142 : WsL → Eqn
  q142 c4 = eqn (Sw01 ∷ Bx⁻1-43 ∷ []) (Bx⁻1-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑))

-- nat 0 BOXd(1;43): 2 steps
lem-nat-0-BOXd⟨1·43⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻1-43 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-43 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·43⟩ c4 = derive (Sw01 ∷ Bx⁻1-43 ∷ []) (Bx⁻0-43 ∷ Sw01 ∷ [])
  (rw 0 (q142 c4) ∷
   re 0 1 (Bx⁻0-43 ∷ []) ∷ []) Eq.refl

private
  q143 : WsL → Eqn
  q143 c4 = eqn (Sw01 ∷ Bx⁻1-43 ∷ []) (Bx⁻0-43 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·43⟩ c4)
  q144 : WsL → Eqn
  q144 c4 = eqn (Sw01 ∷ Toff412 ∷ []) (Toff402 ∷ Sw01 ∷ []) (lem-nat-0-TOFF412 c4)

-- nat 0 BOXd(4;123): 8 steps
lem-nat-0-BOXd⟨4·123⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻4-123 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-023 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨4·123⟩ c4 = derive (Sw01 ∷ Bx⁻4-123 ∷ []) (Bx⁻4-023 ∷ Sw01 ∷ [])
  (re 1 1 (Bx⁻1-43 ∷ CCZ124 ∷ Toff412 ∷ Bx⁻1-43 ∷ Toff412 ∷ CCZ124 ∷ []) ∷
   rw 0 (q143 c4) ∷
   rw 1 (q90 c4) ∷
   rw 2 (q144 c4) ∷
   rw 3 (q143 c4) ∷
   rw 4 (q144 c4) ∷
   rw 5 (q90 c4) ∷
   re 0 6 (Bx⁻4-023 ∷ []) ∷ []) Eq.refl

private
  q145 : WsL → Eqn
  q145 c4 = eqn (Sw01 ∷ Bx⁻4-123 ∷ []) (Bx⁻4-023 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·123⟩ c4)

-- nat 0 BOXd(1;4023): 8 steps
lem-nat-0-BOXd⟨1·4023⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻1-4023 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-4123 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·4023⟩ c4 = derive (Sw01 ∷ Bx⁻1-4023 ∷ []) (Bx⁻0-4123 ∷ Sw01 ∷ [])
  (re 1 1 (Bx⁻4-123 ∷ CCZ014 ∷ Toff104 ∷ Bx⁻4-123 ∷ Toff104 ∷ CCZ014 ∷ []) ∷
   rw 0 (q145 c4) ∷
   rw 1 (q124 c4) ∷
   rw 2 (q125 c4) ∷
   rw 3 (q145 c4) ∷
   rw 4 (q125 c4) ∷
   rw 5 (q124 c4) ∷
   re 0 6 (Bx⁻0-4123 ∷ []) ∷ []) Eq.refl

private
  q146 : WsL → Eqn
  q146 c4 = eqn (Sw12 ∷ Bx⁻2-43 ∷ []) (Bx⁻2-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ))

-- nat 1 BOXd(2;43): 2 steps
lem-nat-1-BOXd⟨2·43⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻2-43 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-43 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·43⟩ c4 = derive (Sw12 ∷ Bx⁻2-43 ∷ []) (Bx⁻1-43 ∷ Sw12 ∷ [])
  (rw 0 (q146 c4) ∷
   re 0 1 (Bx⁻1-43 ∷ []) ∷ []) Eq.refl

private
  q147 : WsL → Eqn
  q147 c4 = eqn (Sw12 ∷ Bx⁻2-43 ∷ []) (Bx⁻1-43 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·43⟩ c4)
  q148 : WsL → Eqn
  q148 c4 = eqn (CCZ124 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ124 ∷ []) (wl0078 c4)
  q149 : WsL → Eqn
  q149 c4 = eqn (Sw12 ∷ Toff412 ∷ []) (Toff412 ∷ Sw12 ∷ []) (wl0079 c4)

-- nat 1 BOXd(4;213): 8 steps
lem-nat-1-BOXd⟨4·213⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻4-213 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-123 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨4·213⟩ c4 = derive (Sw12 ∷ Bx⁻4-213 ∷ []) (Bx⁻4-123 ∷ Sw12 ∷ [])
  (re 1 1 (Bx⁻2-43 ∷ CCZ124 ∷ Toff412 ∷ Bx⁻2-43 ∷ Toff412 ∷ CCZ124 ∷ []) ∷
   rw 0 (q147 c4) ∷
   rw⁻ 1 (q148 c4) ∷
   rw 2 (q149 c4) ∷
   rw 3 (q147 c4) ∷
   rw 4 (q149 c4) ∷
   rw⁻ 5 (q148 c4) ∷
   re 0 6 (Bx⁻4-123 ∷ []) ∷ []) Eq.refl

private
  q150 : WsL → Eqn
  q150 c4 = eqn (Sw12 ∷ Bx⁻4-213 ∷ []) (Bx⁻4-123 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·213⟩ c4)

-- nat 1 BOXd(2;4013): 8 steps
lem-nat-1-BOXd⟨2·4013⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-4023 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·4013⟩ c4 = derive (Sw12 ∷ Bx⁻2-4013 ∷ []) (Bx⁻1-4023 ∷ Sw12 ∷ [])
  (re 1 1 (Bx⁻4-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻4-213 ∷ Toff204 ∷ CCZ024 ∷ []) ∷
   rw 0 (q150 c4) ∷
   rw 1 (q44 c4) ∷
   rw 2 (q45 c4) ∷
   rw 3 (q150 c4) ∷
   rw 4 (q45 c4) ∷
   rw 5 (q44 c4) ∷
   re 0 6 (Bx⁻1-4023 ∷ []) ∷ []) Eq.refl

-- nat 1 BOX(1;24): 3 steps
lem-nat-1-BOX⟨1·24⟩ : WsL → ⟪ (Sw12 ∷ Bx1-24 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-14 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·24⟩ c4 = derive (Sw12 ∷ Bx1-24 ∷ []) (Bx2-14 ∷ Sw12 ∷ [])
  (re 1 1 (CZ24 ∷ []) ∷
   rw⁻ 0 (q128 c4) ∷
   re 0 1 (Bx2-14 ∷ []) ∷ []) Eq.refl

private
  q151 : WsL → Eqn
  q151 c4 = eqn (CCZ123 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ123 ∷ []) (wl0111 c4)
  q152 : WsL → Eqn
  q152 c4 = eqn (Sw12 ∷ Toff213 ∷ []) (Toff123 ∷ Sw12 ∷ []) (wl0112 c4)
  q153 : WsL → Eqn
  q153 c4 = eqn (Sw12 ∷ Bx1-24 ∷ []) (Bx2-14 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·24⟩ c4)

-- nat 1 BOX(2;134): 8 steps
lem-nat-1-BOX⟨2·134⟩ : WsL → ⟪ (Sw12 ∷ Bx2-134 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-234 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·134⟩ c4 = derive (Sw12 ∷ Bx2-134 ∷ []) (Bx1-234 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff213 ∷ Bx1-24 ∷ Toff213 ∷ CCZ123 ∷ Bx1-24 ∷ []) ∷
   rw⁻ 0 (q151 c4) ∷
   rw 1 (q152 c4) ∷
   rw 2 (q153 c4) ∷
   rw 3 (q152 c4) ∷
   rw⁻ 4 (q151 c4) ∷
   rw 5 (q153 c4) ∷
   re 0 6 (Bx1-234 ∷ []) ∷ []) Eq.refl

private
  q154 : WsL → Eqn
  q154 c4 = eqn (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) (wl0047 c4)
  q155 : WsL → Eqn
  q155 c4 = eqn (Sw12 ∷ Bx2-134 ∷ []) (Bx1-234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·134⟩ c4)

-- nat 1 BOX(1;2034): 8 steps
lem-nat-1-BOX⟨1·2034⟩ : WsL → ⟪ (Sw12 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·2034⟩ c4 = derive (Sw12 ∷ Bx1-2034 ∷ []) (Bx2-1034 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff102 ∷ Bx2-134 ∷ Toff102 ∷ CCZ012 ∷ Bx2-134 ∷ []) ∷
   rw⁻ 0 (q14 c4) ∷
   rw 1 (q154 c4) ∷
   rw 2 (q155 c4) ∷
   rw 3 (q154 c4) ∷
   rw⁻ 4 (q14 c4) ∷
   rw 5 (q155 c4) ∷
   re 0 6 (Bx2-1034 ∷ []) ∷ []) Eq.refl

-- nat 2 BOX(2;14): 3 steps
lem-nat-2-BOX⟨2·14⟩ : WsL → ⟪ (Sw23 ∷ Bx2-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-14 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·14⟩ c4 = derive (Sw23 ∷ Bx2-14 ∷ []) (Bx3-14 ∷ Sw23 ∷ [])
  (re 1 1 (CZ14 ∷ []) ∷
   rw⁻ 0 (q111 c4) ∷
   re 0 1 (Bx3-14 ∷ []) ∷ []) Eq.refl

private
  q156 : WsL → Eqn
  q156 c4 = eqn (CCZ123 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ123 ∷ []) (wl0113 c4)
  q157 : WsL → Eqn
  q157 c4 = eqn (Sw23 ∷ Toff123 ∷ []) (Toff123 ∷ Sw23 ∷ []) (wl0114 c4)
  q158 : WsL → Eqn
  q158 c4 = eqn (Sw23 ∷ Bx2-14 ∷ []) (Bx3-14 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·14⟩ c4)

-- nat 2 BOX(1;234): 8 steps
lem-nat-2-BOX⟨1·234⟩ : WsL → ⟪ (Sw23 ∷ Bx1-234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-324 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·234⟩ c4 = derive (Sw23 ∷ Bx1-234 ∷ []) (Bx1-324 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) ∷
   rw⁻ 0 (q156 c4) ∷
   rw 1 (q157 c4) ∷
   rw 2 (q158 c4) ∷
   rw 3 (q157 c4) ∷
   rw⁻ 4 (q156 c4) ∷
   rw 5 (q158 c4) ∷
   re 0 6 (Bx1-324 ∷ []) ∷ []) Eq.refl

private
  q159 : WsL → Eqn
  q159 c4 = eqn (Sw23 ∷ Toff201 ∷ []) (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4)
  q160 : WsL → Eqn
  q160 c4 = eqn (Sw23 ∷ Bx1-234 ∷ []) (Bx1-324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·234⟩ c4)

-- nat 2 BOX(2;1034): 8 steps
lem-nat-2-BOX⟨2·1034⟩ : WsL → ⟪ (Sw23 ∷ Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·1034⟩ c4 = derive (Sw23 ∷ Bx2-1034 ∷ []) (Bx3-1024 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff201 ∷ Bx1-234 ∷ Toff201 ∷ CCZ012 ∷ Bx1-234 ∷ []) ∷
   rw 0 (q28 c4) ∷
   rw 1 (q159 c4) ∷
   rw 2 (q160 c4) ∷
   rw 3 (q159 c4) ∷
   rw 4 (q28 c4) ∷
   rw 5 (q160 c4) ∷
   re 0 6 (Bx3-1024 ∷ []) ∷ []) Eq.refl

private
  q161 : WsL → Eqn
  q161 c4 = eqn (Sw01 ∷ Bx0-14 ∷ []) (Bx1-04 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·14⟩ c4)

-- nat 0 BOX(1;024): 8 steps
lem-nat-0-BOX⟨1·024⟩ : WsL → ⟪ (Sw01 ∷ Bx1-024 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-124 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·024⟩ c4 = derive (Sw01 ∷ Bx1-024 ∷ []) (Bx0-124 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff102 ∷ Bx0-14 ∷ Toff102 ∷ CCZ012 ∷ Bx0-14 ∷ []) ∷
   rw⁻ 0 (q4 c4) ∷
   rw 1 (q5 c4) ∷
   rw 2 (q161 c4) ∷
   rw 3 (q5 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   rw 5 (q161 c4) ∷
   re 0 6 (Bx0-124 ∷ []) ∷ []) Eq.refl

private
  q162 : WsL → Eqn
  q162 c4 = eqn (CCZ013 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ013 ∷ []) (wl0100 c4)
  q163 : WsL → Eqn
  q163 c4 = eqn (Sw01 ∷ Toff013 ∷ []) (Toff103 ∷ Sw01 ∷ []) (wl0101 c4)
  q164 : WsL → Eqn
  q164 c4 = eqn (Sw01 ∷ Bx1-024 ∷ []) (Bx0-124 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·024⟩ c4)

-- nat 0 BOX(0;1324): 8 steps
lem-nat-0-BOX⟨0·1324⟩ : WsL → ⟪ (Sw01 ∷ Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·1324⟩ c4 = derive (Sw01 ∷ Bx0-1324 ∷ []) (Bx1-0324 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-024 ∷ Toff013 ∷ CCZ013 ∷ Bx1-024 ∷ []) ∷
   rw⁻ 0 (q162 c4) ∷
   rw 1 (q163 c4) ∷
   rw 2 (q164 c4) ∷
   rw 3 (q163 c4) ∷
   rw⁻ 4 (q162 c4) ∷
   rw 5 (q164 c4) ∷
   re 0 6 (Bx1-0324 ∷ []) ∷ []) Eq.refl

private
  q165 : WsL → Eqn
  q165 c4 = eqn (Sw12 ∷ Bx1-04 ∷ []) (Bx2-04 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·04⟩ c4)

-- nat 1 BOX(0;124): 8 steps
lem-nat-1-BOX⟨0·124⟩ : WsL → ⟪ (Sw12 ∷ Bx0-124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-214 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·124⟩ c4 = derive (Sw12 ∷ Bx0-124 ∷ []) (Bx0-214 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-04 ∷ Toff012 ∷ CCZ012 ∷ Bx1-04 ∷ []) ∷
   rw⁻ 0 (q14 c4) ∷
   rw 1 (q47 c4) ∷
   rw 2 (q165 c4) ∷
   rw 3 (q47 c4) ∷
   rw⁻ 4 (q14 c4) ∷
   rw 5 (q165 c4) ∷
   re 0 6 (Bx0-214 ∷ []) ∷ []) Eq.refl

private
  q166 : WsL → Eqn
  q166 c4 = eqn (Sw12 ∷ Toff103 ∷ []) (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4)
  q167 : WsL → Eqn
  q167 c4 = eqn (Sw12 ∷ Bx0-124 ∷ []) (Bx0-214 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·124⟩ c4)

-- nat 1 BOX(1;0324): 8 steps
lem-nat-1-BOX⟨1·0324⟩ : WsL → ⟪ (Sw12 ∷ Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·0324⟩ c4 = derive (Sw12 ∷ Bx1-0324 ∷ []) (Bx2-0314 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-124 ∷ Toff103 ∷ CCZ013 ∷ Bx0-124 ∷ []) ∷
   rw 0 (q102 c4) ∷
   rw 1 (q166 c4) ∷
   rw 2 (q167 c4) ∷
   rw 3 (q166 c4) ∷
   rw 4 (q102 c4) ∷
   rw 5 (q167 c4) ∷
   re 0 6 (Bx2-0314 ∷ []) ∷ []) Eq.refl

private
  q168 : WsL → Eqn
  q168 c4 = eqn (Sw01 ∷ CZ14 ∷ []) (CZ04 ∷ Sw01 ∷ []) (lem-nat-0-CZ14 c4)

-- nat 0 BOX(3;14): 3 steps
lem-nat-0-BOX⟨3·14⟩ : WsL → ⟪ (Sw01 ∷ Bx3-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-04 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·14⟩ c4 = derive (Sw01 ∷ Bx3-14 ∷ []) (Bx3-04 ∷ Sw01 ∷ [])
  (re 1 1 (CZ14 ∷ []) ∷
   rw 0 (q168 c4) ∷
   re 0 1 (Bx3-04 ∷ []) ∷ []) Eq.refl

private
  q169 : WsL → Eqn
  q169 c4 = eqn (Sw01 ∷ Bx3-14 ∷ []) (Bx3-04 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·14⟩ c4)

-- nat 0 BOX(1;324): 8 steps
lem-nat-0-BOX⟨1·324⟩ : WsL → ⟪ (Sw01 ∷ Bx1-324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-324 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·324⟩ c4 = derive (Sw01 ∷ Bx1-324 ∷ []) (Bx0-324 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   rw 1 (q82 c4) ∷
   rw 2 (q169 c4) ∷
   rw 3 (q82 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   rw 5 (q169 c4) ∷
   re 0 6 (Bx0-324 ∷ []) ∷ []) Eq.refl

private
  q170 : WsL → Eqn
  q170 c4 = eqn (Sw01 ∷ Toff301 ∷ []) (Toff301 ∷ Sw01 ∷ []) (wl0115 c4)
  q171 : WsL → Eqn
  q171 c4 = eqn (Sw01 ∷ Bx1-324 ∷ []) (Bx0-324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·324⟩ c4)

-- nat 0 BOX(3;1024): 8 steps
lem-nat-0-BOX⟨3·1024⟩ : WsL → ⟪ (Sw01 ∷ Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·1024⟩ c4 = derive (Sw01 ∷ Bx3-1024 ∷ []) (Bx3-0124 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff301 ∷ Bx1-324 ∷ Toff301 ∷ CCZ013 ∷ Bx1-324 ∷ []) ∷
   rw⁻ 0 (q162 c4) ∷
   rw 1 (q170 c4) ∷
   rw 2 (q171 c4) ∷
   rw 3 (q170 c4) ∷
   rw⁻ 4 (q162 c4) ∷
   rw 5 (q171 c4) ∷
   re 0 6 (Bx3-0124 ∷ []) ∷ []) Eq.refl

private
  q172 : WsL → Eqn
  q172 c4 = eqn (Sw01 ∷ CZ04 ∷ []) (CZ14 ∷ Sw01 ∷ []) (lem-nat-0-CZ04 c4)

-- nat 0 BOX(3;04): 3 steps
lem-nat-0-BOX⟨3·04⟩ : WsL → ⟪ (Sw01 ∷ Bx3-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-14 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·04⟩ c4 = derive (Sw01 ∷ Bx3-04 ∷ []) (Bx3-14 ∷ Sw01 ∷ [])
  (re 1 1 (CZ04 ∷ []) ∷
   rw 0 (q172 c4) ∷
   re 0 1 (Bx3-14 ∷ []) ∷ []) Eq.refl

private
  q173 : WsL → Eqn
  q173 c4 = eqn (Sw01 ∷ Bx3-04 ∷ []) (Bx3-14 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·04⟩ c4)

-- nat 0 BOX(0;314): 8 steps
lem-nat-0-BOX⟨0·314⟩ : WsL → ⟪ (Sw01 ∷ Bx0-314 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-304 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·314⟩ c4 = derive (Sw01 ∷ Bx0-314 ∷ []) (Bx1-304 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ []) ∷
   rw⁻ 0 (q162 c4) ∷
   rw 1 (q163 c4) ∷
   rw 2 (q173 c4) ∷
   rw 3 (q163 c4) ∷
   rw⁻ 4 (q162 c4) ∷
   rw 5 (q173 c4) ∷
   re 0 6 (Bx1-304 ∷ []) ∷ []) Eq.refl

private
  q174 : WsL → Eqn
  q174 c4 = eqn (Sw01 ∷ Toff302 ∷ []) (Toff312 ∷ Sw01 ∷ []) (wl0116 c4)
  q175 : WsL → Eqn
  q175 c4 = eqn (Sw01 ∷ Bx0-314 ∷ []) (Bx1-304 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·314⟩ c4)

-- nat 0 BOX(3;0214): 8 steps
lem-nat-0-BOX⟨3·0214⟩ : WsL → ⟪ (Sw01 ∷ Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·0214⟩ c4 = derive (Sw01 ∷ Bx3-0214 ∷ []) (Bx3-1204 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-314 ∷ Toff302 ∷ CCZ023 ∷ Bx0-314 ∷ []) ∷
   rw⁻ 0 (q8 c4) ∷
   rw 1 (q174 c4) ∷
   rw 2 (q175 c4) ∷
   rw 3 (q174 c4) ∷
   rw⁻ 4 (q8 c4) ∷
   rw 5 (q175 c4) ∷
   re 0 6 (Bx3-1204 ∷ []) ∷ []) Eq.refl

private
  q176 : WsL → Eqn
  q176 c4 = eqn (Sw01 ∷ Toff103 ∷ []) (Toff013 ∷ Sw01 ∷ []) (wl0102 c4)

-- nat 0 BOX(1;304): 8 steps
lem-nat-0-BOX⟨1·304⟩ : WsL → ⟪ (Sw01 ∷ Bx1-304 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-314 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·304⟩ c4 = derive (Sw01 ∷ Bx1-304 ∷ []) (Bx0-314 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ []) ∷
   rw⁻ 0 (q162 c4) ∷
   rw 1 (q176 c4) ∷
   rw 2 (q169 c4) ∷
   rw 3 (q176 c4) ∷
   rw⁻ 4 (q162 c4) ∷
   rw 5 (q169 c4) ∷
   re 0 6 (Bx0-314 ∷ []) ∷ []) Eq.refl

private
  q177 : WsL → Eqn
  q177 c4 = eqn (Sw01 ∷ Bx1-304 ∷ []) (Bx0-314 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·304⟩ c4)

-- nat 0 BOX(3;1204): 8 steps
lem-nat-0-BOX⟨3·1204⟩ : WsL → ⟪ (Sw01 ∷ Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·1204⟩ c4 = derive (Sw01 ∷ Bx3-1204 ∷ []) (Bx3-0214 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff312 ∷ Bx1-304 ∷ Toff312 ∷ CCZ123 ∷ Bx1-304 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   rw 1 (q110 c4) ∷
   rw 2 (q177 c4) ∷
   rw 3 (q110 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   rw 5 (q177 c4) ∷
   re 0 6 (Bx3-0214 ∷ []) ∷ []) Eq.refl

private
  q178 : WsL → Eqn
  q178 c4 = eqn (CK30 ∷ Sw01 ∷ []) (Sw01 ∷ CK31 ∷ []) (wl0117 c4)

-- resp CK40 at 1: 6 steps
lem-resp-CK40-at-1 : WsL → ⟪ (CK40 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK41 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CK40-at-1 c4 = derive (CK40 ∷ []) (Sw01 ∷ CK41 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q20 c4) ∷
   re 0 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q67 c4) ∷
   rw 1 (q178 c4) ∷
   rw⁻ 0 (q67 c4) ∷
   re 1 3 (CK41 ∷ []) ∷ []) Eq.refl

private
  q179 : WsL → Eqn
  q179 c4 = eqn (CK30⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CK31⁻ ∷ []) (wl0118 c4)

-- resp CKd40 at 1: 6 steps
lem-resp-CKd40-at-1 : WsL → ⟪ (CK40⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK41⁻ ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CKd40-at-1 c4 = derive (CK40⁻ ∷ []) (Sw01 ∷ CK41⁻ ∷ Sw01 ∷ [])
  (rw⁻ 1 (q20 c4) ∷
   re 0 1 (Sw34 ∷ CK30⁻ ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q67 c4) ∷
   rw 1 (q179 c4) ∷
   rw⁻ 0 (q67 c4) ∷
   re 1 3 (CK41⁻ ∷ []) ∷ []) Eq.refl

private
  q180 : WsL → Eqn
  q180 c4 = eqn (CCZ234 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ134 ∷ []) (wl0084 c4)
  q181 : WsL → Eqn
  q181 c4 = eqn (CK10⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ CK10⁻ ∷ []) (c₂ (S ↑ • CK₁₀) (CCZ))
  q182 : WsL → Eqn
  q182 c4 = eqn (CCZ134 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ234 ∷ []) (wl0034 c4)

-- comm CKd40 CCZ123: 13 steps
lem-comm-CKd40-CCZ123 : WsL → ⟪ (CK40⁻ ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CK40⁻ ∷ []) ⟫ʷ
lem-comm-CKd40-CCZ123 c4 = derive (CK40⁻ ∷ CCZ123 ∷ []) (CCZ123 ∷ CK40⁻ ∷ [])
  (re 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 8 (q31 c4) ∷
   re 6 3 (CCZ124 ∷ []) ∷
   rw⁻ 7 (q23 c4) ∷
   re 5 3 (CCZ134 ∷ []) ∷
   rw⁻ 4 (q180 c4) ∷
   rw 3 (q181 c4) ∷
   rw⁻ 2 (q182 c4) ∷
   re 2 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) ∷
   rw 1 (q23 c4) ∷
   re 1 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) ∷
   rw 0 (q31 c4) ∷
   re 1 7 (CK40⁻ ∷ []) ∷ []) Eq.refl

-- nat 2 CS13: 2 steps
lem-nat-2-CS13 : WsL → ⟪ (Sw23 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CS13 c4 = derive (Sw23 ∷ CS13 ∷ []) (CS12 ∷ Sw23 ∷ [])
  (re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 0 (q23 c4) ∷ []) Eq.refl

-- nat 2 CS12: 2 steps
lem-nat-2-CS12 : WsL → ⟪ (Sw23 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CS12 c4 = derive (Sw23 ∷ CS12 ∷ []) (CS13 ∷ Sw23 ∷ [])
  (rw⁻ 2 (q23 c4) ∷
   re 0 3 (CS13 ∷ []) ∷ []) Eq.refl

-- nat 3 CS14: 2 steps
lem-nat-3-CS14 : WsL → ⟪ (Sw34 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CS14 c4 = derive (Sw34 ∷ CS14 ∷ []) (CS13 ∷ Sw34 ∷ [])
  (re 1 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 0 (q31 c4) ∷ []) Eq.refl

-- nat 3 CS13: 2 steps
lem-nat-3-CS13 : WsL → ⟪ (Sw34 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CS13 c4 = derive (Sw34 ∷ CS13 ∷ []) (CS14 ∷ Sw34 ∷ [])
  (rw⁻ 2 (q31 c4) ∷
   re 0 3 (CS14 ∷ []) ∷ []) Eq.refl

-- nat 2 CSd13: 2 steps
lem-nat-2-CSd13 : WsL → ⟪ (Sw23 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CSd13 c4 = derive (Sw23 ∷ CS13⁻ ∷ []) (CS12⁻ ∷ Sw23 ∷ [])
  (re 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 0 (q23 c4) ∷ []) Eq.refl

-- nat 2 CSd12: 2 steps
lem-nat-2-CSd12 : WsL → ⟪ (Sw23 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CSd12 c4 = derive (Sw23 ∷ CS12⁻ ∷ []) (CS13⁻ ∷ Sw23 ∷ [])
  (rw⁻ 2 (q23 c4) ∷
   re 0 3 (CS13⁻ ∷ []) ∷ []) Eq.refl

-- nat 3 CSd14: 2 steps
lem-nat-3-CSd14 : WsL → ⟪ (Sw34 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CSd14 c4 = derive (Sw34 ∷ CS14⁻ ∷ []) (CS13⁻ ∷ Sw34 ∷ [])
  (re 1 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 0 (q31 c4) ∷ []) Eq.refl

-- nat 3 CSd13: 2 steps
lem-nat-3-CSd13 : WsL → ⟪ (Sw34 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CSd13 c4 = derive (Sw34 ∷ CS13⁻ ∷ []) (CS14⁻ ∷ Sw34 ∷ [])
  (rw⁻ 2 (q31 c4) ∷
   re 0 3 (CS14⁻ ∷ []) ∷ []) Eq.refl

-- nat 0 BOX(2;41): 3 steps
lem-nat-0-BOX⟨2·41⟩ : WsL → ⟪ (Sw01 ∷ Bx2-41 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-40 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·41⟩ c4 = derive (Sw01 ∷ Bx2-41 ∷ []) (Bx2-40 ∷ Sw01 ∷ [])
  (re 1 1 (CZ14 ∷ []) ∷
   rw 0 (q168 c4) ∷
   re 0 1 (Bx2-40 ∷ []) ∷ []) Eq.refl

private
  q183 : WsL → Eqn
  q183 c4 = eqn (Sw01 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ))
  q184 : WsL → Eqn
  q184 c4 = eqn (Sw01 ∷ Toff423 ∷ []) (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ))
  q185 : WsL → Eqn
  q185 c4 = eqn (Sw01 ∷ Bx2-41 ∷ []) (Bx2-40 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·41⟩ c4)

-- nat 0 BOX(4;231): 8 steps
lem-nat-0-BOX⟨4·231⟩ : WsL → ⟪ (Sw01 ∷ Bx4-231 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-230 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·231⟩ c4 = derive (Sw01 ∷ Bx4-231 ∷ []) (Bx4-230 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ []) ∷
   rw 0 (q183 c4) ∷
   rw 1 (q184 c4) ∷
   rw 2 (q185 c4) ∷
   rw 3 (q184 c4) ∷
   rw 4 (q183 c4) ∷
   rw 5 (q185 c4) ∷
   re 0 6 (Bx4-230 ∷ []) ∷ []) Eq.refl

private
  q186 : WsL → Eqn
  q186 c4 = eqn (Sw01 ∷ Bx4-231 ∷ []) (Bx4-230 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·231⟩ c4)

-- nat 0 BOX(2;4031): 8 steps
lem-nat-0-BOX⟨2·4031⟩ : WsL → ⟪ (Sw01 ∷ Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4130 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·4031⟩ c4 = derive (Sw01 ∷ Bx2-4031 ∷ []) (Bx2-4130 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff204 ∷ Bx4-231 ∷ Toff204 ∷ CCZ024 ∷ Bx4-231 ∷ []) ∷
   rw 0 (q85 c4) ∷
   rw 1 (q86 c4) ∷
   rw 2 (q186 c4) ∷
   rw 3 (q86 c4) ∷
   rw 4 (q85 c4) ∷
   rw 5 (q186 c4) ∷
   re 0 6 (Bx2-4130 ∷ []) ∷ []) Eq.refl

-- nat 2 TOFF314: 2 steps
lem-nat-2-TOFF314 : WsL → ⟪ (Sw23 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF314 c4 = derive (Sw23 ∷ Toff314 ∷ []) (Toff214 ∷ Sw23 ∷ [])
  (re 1 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) ∷
   rw 0 (q23 c4) ∷ []) Eq.refl
