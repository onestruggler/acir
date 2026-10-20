{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R009 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0003 ; wl0004 ; wl0006 ; wl0008 ; wl0009 ; wl0011 ; wl0012 ; wl0018 ; wl0019 ; wl0020 ; wl0021 ; wl0022 ; wl0028 ; wl0029 ; wl0046 ; wl0047 ; wl0090 ; wl0091 ; wl0094 ; wl0095 ; wl0122 ; wl0123 ; wl0143 ; wl0144)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-push-BOX⟨0·312⟩-sw3-R ; lem-comm-push-BOX⟨0·31⟩-sw3-R ; lem-comm-push-BOX⟨0·41⟩-sw3-L ; lem-comm-push-BOX⟨0·42⟩-sw2-R ; lem-comm-push-BOX⟨0·43⟩-sw2-L ; lem-comm-push-BOX⟨4·02⟩-sw2-R ; lem-comm-push-BOX⟨4·03⟩-sw0-R)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-push-CCZ014-sw2-L ; lem-comm-push-CCZ024-sw0-L ; lem-comm-push-CCZ034-sw0-L ; lem-comm-push-CCZ034-sw1-L ; lem-comm-push-TOFF023-sw3-L ; lem-comm-push-TOFF024-sw0-L ; lem-comm-push-TOFF024-sw3-L ; lem-comm-push-TOFF034-sw0-L ; lem-comm-push-TOFF034-sw1-L ; lem-comm-push-TOFF204-sw0-L ; lem-comm-push-TOFF304-sw0-L ; lem-comm-push-TOFF304-sw1-L ; lem-comm-push-TOFF401-sw2-L ; lem-comm-push-TOFF402-sw0-L)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-comm-push-BOX⟨0·123⟩-sw0-L ; lem-comm-push-BOX⟨0·213⟩-sw1-L ; lem-comm-push-BOX⟨1·023⟩-sw2-L ; lem-comm-push-BOX⟨1·032⟩-sw1-L ; lem-comm-push-BOX⟨1·032⟩-sw2-R ; lem-comm-push-BOX⟨2·031⟩-sw1-R ; lem-comm-push-CCZ014-sw0-L ; lem-comm-push-CCZ014-sw2-R ; lem-comm-push-CCZ023-sw3-L ; lem-comm-push-CCZ024-sw3-L ; lem-comm-push-TOFF014-sw2-L ; lem-comm-push-TOFF014-sw2-R ; lem-comm-push-TOFF104-sw0-L ; lem-comm-push-TOFF104-sw2-L ; lem-comm-push-TOFF203-sw3-L ; lem-comm-push-TOFF204-sw3-L ; lem-comm-push-TOFF302-sw3-L ; lem-comm-push-TOFF402-sw3-L ; lem-comm-push-TOFF403-sw0-L ; lem-comm-push-TOFF403-sw1-L)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-comm-push-BOX⟨0·123⟩-sw1-R ; lem-comm-push-BOX⟨1·023⟩-sw0-R ; lem-comm-push-BOX⟨2·031⟩-sw2-R ; lem-comm-push-BOX⟨2·4103⟩-sw1-L ; lem-comm-push-BOX⟨3·021⟩-sw2-L ; lem-comm-push-BOX⟨4·012⟩-sw1-L ; lem-comm-push-BOX⟨4·021⟩-sw1-R ; lem-comm-push-CCZ014-sw0-R ; lem-comm-push-CCZ023-sw3-R ; lem-comm-push-CCZ034-sw1-R ; lem-comm-push-CCZ034-sw3-R ; lem-comm-push-CCZ124-sw0-L ; lem-comm-push-TOFF014-sw0-R ; lem-comm-push-TOFF034-sw1-R ; lem-comm-push-TOFF302-sw3-R ; lem-comm-push-TOFF401-sw0-L ; lem-comm-push-TOFF412-sw0-L)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-comm-push-BOX⟨0·213⟩-sw2-R ; lem-comm-push-BOX⟨0·413⟩-sw1-R ; lem-comm-push-BOX⟨1·4203⟩-sw1-R ; lem-comm-push-BOX⟨1·430⟩-sw1-R ; lem-comm-push-BOX⟨2·031⟩-sw0-R ; lem-comm-push-BOX⟨2·130⟩-sw1-R ; lem-comm-push-BOX⟨2·1430⟩-sw2-R ; lem-comm-push-BOX⟨2·430⟩-sw0-R ; lem-comm-push-BOX⟨3·1420⟩-sw3-R ; lem-comm-push-BOX⟨4·1320⟩-sw2-R ; lem-comm-push-CCZ024-sw0-R ; lem-comm-push-CCZ124-sw0-R ; lem-comm-push-TOFF024-sw0-R ; lem-comm-push-TOFF024-sw3-R ; lem-comm-push-TOFF304-sw3-R ; lem-comm-push-TOFF401-sw0-R ; lem-comm-push-TOFF401-sw2-R ; lem-comm-push-TOFF402-sw0-R ; lem-comm-push-TOFF412-sw0-R)

-- resp CCZ034 at 2: 4 steps
lem-resp-CCZ034-at-2 : WsL → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CCZ134 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CCZ034-at-2 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ []) (Sw12 ∷ Sw01 ∷ CCZ134 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ CCZ034 ∷ []) (lem-comm-push-CCZ034-sw1-L c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ CCZ134 ∷ []) (lem-comm-push-CCZ034-sw0-L c4) ▸ done

-- resp CCZ034 at 1: 2 steps
lem-resp-CCZ034-at-1 : WsL → ⟪ (CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CCZ134 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CCZ034-at-1 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ []) (Sw01 ∷ CCZ134 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ CCZ134 ∷ []) (lem-comm-push-CCZ034-sw0-L c4) ▸ done

-- resp TOFF034 at 1: 2 steps
lem-resp-TOFF034-at-1 : WsL → ⟪ (Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff134 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF034-at-1 c4 = run b0
  where
  b0 : Chain (Toff034 ∷ []) (Sw01 ∷ Toff134 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ Toff134 ∷ []) (lem-comm-push-TOFF034-sw0-L c4) ▸ done

-- resp TOFF034 at 2: 4 steps
lem-resp-TOFF034-at-2 : WsL → ⟪ (Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff134 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF034-at-2 c4 = run b0
  where
  b0 : Chain (Toff034 ∷ []) (Sw12 ∷ Sw01 ∷ Toff134 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ Toff034 ∷ []) (lem-comm-push-TOFF034-sw1-L c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ Toff134 ∷ []) (lem-comm-push-TOFF034-sw0-L c4) ▸ done

-- resp CCZ014 at 2: 5 steps
lem-resp-CCZ014-at-2 : WsL → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CCZ124 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CCZ014-at-2 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ []) (Sw12 ∷ Sw01 ∷ CCZ124 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 3 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ CCZ124 ∷ []) (lem-comm-push-CCZ024-sw0-L c4) ▸ done

-- resp TOFF204 at 1: 2 steps
lem-resp-TOFF204-at-1 : WsL → ⟪ (Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff214 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF204-at-1 c4 = run b0
  where
  b0 : Chain (Toff204 ∷ []) (Sw01 ∷ Toff214 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ Toff214 ∷ []) (lem-comm-push-TOFF204-sw0-L c4) ▸ done

-- resp CCZ024 at 1: 2 steps
lem-resp-CCZ024-at-1 : WsL → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CCZ124 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CCZ024-at-1 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ []) (Sw01 ∷ CCZ124 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ CCZ124 ∷ []) (lem-comm-push-CCZ024-sw0-L c4) ▸ done

-- resp CCZ024 at 3: 7 steps
lem-resp-CCZ024-at-3 : WsL → ⟪ (CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CCZ134 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CCZ024-at-3 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CCZ134 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (Sw12 ∷ CCZ034 ∷ []) (lem-comm-push-CCZ034-sw1-L c4) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ CCZ134 ∷ []) (lem-comm-push-CCZ034-sw0-L c4) ▸ done

-- resp CCZ014 at 3: 7 steps
lem-resp-CCZ014-at-3 : WsL → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CCZ124 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CCZ014-at-3 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CCZ124 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 2 (Sw23 ∷ CCZ014 ∷ []) (lem-comm-push-CCZ014-sw2-L c4) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 3 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ CCZ124 ∷ []) (lem-comm-push-CCZ024-sw0-L c4) ▸ done

-- resp TOFF014 at 2: 5 steps
lem-resp-TOFF014-at-2 : WsL → ⟪ (Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff124 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF014-at-2 c4 = run b0
  where
  b0 : Chain (Toff014 ∷ []) (Sw12 ∷ Sw01 ∷ Toff124 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 3 (Toff024 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ Toff124 ∷ []) (lem-comm-push-TOFF024-sw0-L c4) ▸ done

-- resp TOFF024 at 1: 2 steps
lem-resp-TOFF024-at-1 : WsL → ⟪ (Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff124 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF024-at-1 c4 = run b0
  where
  b0 : Chain (Toff024 ∷ []) (Sw01 ∷ Toff124 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ Toff124 ∷ []) (lem-comm-push-TOFF024-sw0-L c4) ▸ done

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

-- resp TOFF304 at 2: 4 steps
lem-resp-TOFF304-at-2 : WsL → ⟪ (Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff314 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF304-at-2 c4 = run b0
  where
  b0 : Chain (Toff304 ∷ []) (Sw12 ∷ Sw01 ∷ Toff314 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ Toff304 ∷ []) (lem-comm-push-TOFF304-sw1-L c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ Toff314 ∷ []) (lem-comm-push-TOFF304-sw0-L c4) ▸ done

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

-- resp TOFF402 at 3: 7 steps
lem-resp-TOFF402-at-3 : WsL → ⟪ (Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff413 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF402-at-3 c4 = run b0
  where
  b0 : Chain (Toff402 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff413 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (Toff403 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (Sw12 ∷ Toff403 ∷ []) (lem-comm-push-TOFF403-sw1-L c4) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ Toff413 ∷ []) (lem-comm-push-TOFF403-sw0-L c4) ▸ done

-- resp TOFF304 at 1: 2 steps
lem-resp-TOFF304-at-1 : WsL → ⟪ (Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff314 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF304-at-1 c4 = run b0
  where
  b0 : Chain (Toff304 ∷ []) (Sw01 ∷ Toff314 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ Toff314 ∷ []) (lem-comm-push-TOFF304-sw0-L c4) ▸ done

-- resp TOFF401 at 2: 5 steps
lem-resp-TOFF401-at-2 : WsL → ⟪ (Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff412 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF401-at-2 c4 = run b0
  where
  b0 : Chain (Toff401 ∷ []) (Sw12 ∷ Sw01 ∷ Toff412 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 3 (Toff402 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ Toff412 ∷ []) (lem-comm-push-TOFF402-sw0-L c4) ▸ done

-- resp TOFF204 at 3: 7 steps
lem-resp-TOFF204-at-3 : WsL → ⟪ (Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff314 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF204-at-3 c4 = run b0
  where
  b0 : Chain (Toff204 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff314 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (Toff304 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 2 (Sw12 ∷ Toff304 ∷ []) (lem-comm-push-TOFF304-sw1-L c4) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ Toff314 ∷ []) (lem-comm-push-TOFF304-sw0-L c4) ▸ done

-- resp TOFF014 at 3: 7 steps
lem-resp-TOFF014-at-3 : WsL → ⟪ (Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff124 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF014-at-3 c4 = run b0
  where
  b0 : Chain (Toff014 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff124 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 2 (Sw23 ∷ Toff014 ∷ []) (lem-comm-push-TOFF014-sw2-L c4) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 3 (Toff024 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ Toff124 ∷ []) (lem-comm-push-TOFF024-sw0-L c4) ▸ done

-- resp TOFF403 at 2: 4 steps
lem-resp-TOFF403-at-2 : WsL → ⟪ (Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff413 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF403-at-2 c4 = run b0
  where
  b0 : Chain (Toff403 ∷ []) (Sw12 ∷ Sw01 ∷ Toff413 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 2 (Sw12 ∷ Toff403 ∷ []) (lem-comm-push-TOFF403-sw1-L c4) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ Toff413 ∷ []) (lem-comm-push-TOFF403-sw0-L c4) ▸ done

-- resp TOFF104 at 2: 5 steps
lem-resp-TOFF104-at-2 : WsL → ⟪ (Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff214 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF104-at-2 c4 = run b0
  where
  b0 : Chain (Toff104 ∷ []) (Sw12 ∷ Sw01 ∷ Toff214 ∷ Sw01 ∷ Sw12 ∷ [])
  b0 = at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 3 (Toff204 ∷ []) (by-assoc Eq.refl) ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 1 2 (Sw01 ∷ Toff214 ∷ []) (lem-comm-push-TOFF204-sw0-L c4) ▸ done

-- resp TOFF104 at 3: 7 steps
lem-resp-TOFF104-at-3 : WsL → ⟪ (Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff214 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF104-at-3 c4 = run b0
  where
  b0 : Chain (Toff104 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff214 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 2 (Sw23 ∷ Toff104 ∷ []) (lem-comm-push-TOFF104-sw2-L c4) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 3 (Toff204 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 2 2 (Sw01 ∷ Toff214 ∷ []) (lem-comm-push-TOFF204-sw0-L c4) ▸ done

-- resp TOFF402 at 1: 2 steps
lem-resp-TOFF402-at-1 : WsL → ⟪ (Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff412 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF402-at-1 c4 = run b0
  where
  b0 : Chain (Toff402 ∷ []) (Sw01 ∷ Toff412 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ Toff412 ∷ []) (lem-comm-push-TOFF402-sw0-L c4) ▸ done

-- resp TOFF403 at 1: 2 steps
lem-resp-TOFF403-at-1 : WsL → ⟪ (Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff413 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF403-at-1 c4 = run b0
  where
  b0 : Chain (Toff403 ∷ []) (Sw01 ∷ Toff413 ∷ Sw01 ∷ [])
  b0 = at 1 0 (Sw01 ∷ Sw01 ∷ []) (sym (wl0018 c4)) ▸
       at 0 2 (Sw01 ∷ Toff413 ∷ []) (lem-comm-push-TOFF403-sw0-L c4) ▸ done

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

-- comm push BOX(2;0413) sw1 L: 12 steps
lem-comm-push-BOX⟨2·0413⟩-sw1-L : WsL → ⟪ (Bx2-0413 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Bx1-0423 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨2·0413⟩-sw1-L c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-0413 ∷ Sw12 ∷ []) (CCZ024 ∷ Sw12 ∷ Toff104 ∷ Sw12 ∷ Sw12 ∷ Bx0-123 ∷ Toff104 ∷ CCZ014 ∷ Bx0-123 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (refl) ▸
       at 5 2 (Sw12 ∷ Bx0-123 ∷ []) (lem-comm-push-BOX⟨0·213⟩-sw1-L c4) ▸
       at 4 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0006 c4) ▸
       at 3 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0006 c4) ▸
       at 2 2 (Sw12 ∷ Bx0-123 ∷ []) (lem-comm-push-BOX⟨0·213⟩-sw1-L c4) ▸
       at 1 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CCZ024 ∷ Sw12 ∷ Toff104 ∷ Sw12 ∷ Sw12 ∷ Bx0-123 ∷ Toff104 ∷ CCZ014 ∷ Bx0-123 ∷ []) (Sw12 ∷ Bx1-0423 ∷ [])
  b1 = at 3 2 [] (wl0006 c4) ▸
       at 0 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0006 c4) ▸
       at 1 6 (Bx1-0423 ∷ []) (refl) ▸ done

-- comm push BOX(1;0423) sw0 L: 8 steps
lem-comm-push-BOX⟨1·0423⟩-sw0-L : WsL → ⟪ (Bx1-0423 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·0423⟩-sw0-L c4 = run b0
  where
  b0 : Chain (Bx1-0423 ∷ Sw01 ∷ []) (Sw01 ∷ Bx0-1423 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff104 ∷ Bx0-123 ∷ Toff104 ∷ CCZ014 ∷ Bx0-123 ∷ []) (refl) ▸
       at 5 2 (Sw01 ∷ Bx1-023 ∷ []) (lem-comm-push-BOX⟨0·123⟩-sw0-L c4) ▸
       at 4 2 (Sw01 ∷ CCZ014 ∷ []) (lem-comm-push-CCZ014-sw0-L c4) ▸
       at 3 2 (Sw01 ∷ Toff014 ∷ []) (lem-comm-push-TOFF104-sw0-L c4) ▸
       at 2 2 (Sw01 ∷ Bx1-023 ∷ []) (lem-comm-push-BOX⟨0·123⟩-sw0-L c4) ▸
       at 1 2 (Sw01 ∷ Toff014 ∷ []) (lem-comm-push-TOFF104-sw0-L c4) ▸
       at 0 2 (Sw01 ∷ CCZ014 ∷ []) (lem-comm-push-CCZ014-sw0-L c4) ▸
       at 1 6 (Bx0-1423 ∷ []) (refl) ▸ done

-- comm push BOX(0;1423) sw2 L: 8 steps
lem-comm-push-BOX⟨0·1423⟩-sw2-L : WsL → ⟪ (Bx0-1423 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Bx0-1432 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·1423⟩-sw2-L c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ Sw23 ∷ []) (Sw23 ∷ Bx0-1432 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ []) (refl) ▸
       at 5 2 (Sw23 ∷ Bx1-032 ∷ []) (lem-comm-push-BOX⟨1·023⟩-sw2-L c4) ▸
       at 4 2 (Sw23 ∷ CCZ014 ∷ []) (lem-comm-push-CCZ014-sw2-L c4) ▸
       at 3 2 (Sw23 ∷ Toff014 ∷ []) (lem-comm-push-TOFF014-sw2-L c4) ▸
       at 2 2 (Sw23 ∷ Bx1-032 ∷ []) (lem-comm-push-BOX⟨1·023⟩-sw2-L c4) ▸
       at 1 2 (Sw23 ∷ Toff014 ∷ []) (lem-comm-push-TOFF014-sw2-L c4) ▸
       at 0 2 (Sw23 ∷ CCZ014 ∷ []) (lem-comm-push-CCZ014-sw2-L c4) ▸
       at 1 6 (Bx0-1432 ∷ []) (refl) ▸ done

-- comm push BOX(0;1432) sw1 L: 12 steps
lem-comm-push-BOX⟨0·1432⟩-sw1-L : WsL → ⟪ (Bx0-1432 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Bx0-2431 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·1432⟩-sw1-L c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-1432 ∷ Sw12 ∷ []) (CCZ014 ∷ Sw12 ∷ Sw12 ∷ Toff014 ∷ Sw12 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ CCZ014 ∷ Bx1-032 ∷ []) (refl) ▸
       at 5 2 (Sw12 ∷ Bx2-031 ∷ []) (lem-comm-push-BOX⟨1·032⟩-sw1-L c4) ▸
       at 4 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 5 3 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (Toff024 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Bx2-031 ∷ []) (lem-comm-push-BOX⟨1·032⟩-sw1-L c4) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸ done

  b1 : Chain (CCZ014 ∷ Sw12 ∷ Sw12 ∷ Toff014 ∷ Sw12 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) (Sw12 ∷ Bx0-2431 ∷ [])
  b1 = at 2 3 (Toff024 ∷ []) (by-assoc Eq.refl) ▸
       at 0 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 3 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸
       at 1 6 (Bx0-2431 ∷ []) (refl) ▸ done

-- comm push BOX(0;2431) sw1 R: 12 steps
lem-comm-push-BOX⟨0·2431⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·2431⟩-sw1-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx0-2431 ∷ []) (CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ Sw12 ∷ CCZ024 ∷ Bx2-031 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) (refl) ▸
       at 1 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0006 c4) ▸
       at 2 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0006 c4) ▸
       at 2 2 (Bx1-032 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨2·031⟩-sw1-R c4) ▸
       at 4 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0006 c4) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ Sw12 ∷ CCZ024 ∷ Bx2-031 ∷ []) (Bx0-1432 ∷ Sw12 ∷ [])
  b1 = at 5 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0006 c4) ▸
       at 5 2 (Bx1-032 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨2·031⟩-sw1-R c4) ▸
       at 0 6 (Bx0-1432 ∷ []) (refl) ▸ done

-- comm push BOX(0;1432) sw2 R: 8 steps
lem-comm-push-BOX⟨0·1432⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·1432⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-1432 ∷ []) (Bx0-1423 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ CCZ014 ∷ Bx1-032 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-comm-push-CCZ014-sw2-R c4) ▸
       at 1 2 (Toff014 ∷ Sw23 ∷ []) (lem-comm-push-TOFF014-sw2-R c4) ▸
       at 2 2 (Bx1-023 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨1·032⟩-sw2-R c4) ▸
       at 3 2 (Toff014 ∷ Sw23 ∷ []) (lem-comm-push-TOFF014-sw2-R c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-comm-push-CCZ014-sw2-R c4) ▸
       at 5 2 (Bx1-023 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨1·032⟩-sw2-R c4) ▸
       at 0 6 (Bx0-1423 ∷ []) (refl) ▸ done

-- comm push BOX(0;1423) sw0 R: 8 steps
lem-comm-push-BOX⟨0·1423⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·1423⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-1423 ∷ []) (Bx1-0423 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw01 ∷ []) (lem-comm-push-CCZ014-sw0-R c4) ▸
       at 1 2 (Toff104 ∷ Sw01 ∷ []) (lem-comm-push-TOFF014-sw0-R c4) ▸
       at 2 2 (Bx0-123 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨1·023⟩-sw0-R c4) ▸
       at 3 2 (Toff104 ∷ Sw01 ∷ []) (lem-comm-push-TOFF014-sw0-R c4) ▸
       at 4 2 (CCZ014 ∷ Sw01 ∷ []) (lem-comm-push-CCZ014-sw0-R c4) ▸
       at 5 2 (Bx0-123 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨1·023⟩-sw0-R c4) ▸
       at 0 6 (Bx1-0423 ∷ []) (refl) ▸ done

-- comm push BOX(1;0423) sw1 R: 12 steps
lem-comm-push-BOX⟨1·0423⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·0423⟩-sw1-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx1-0423 ∷ []) (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ Sw12 ∷ CCZ014 ∷ Bx0-123 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-123 ∷ Toff104 ∷ CCZ014 ∷ Bx0-123 ∷ []) (refl) ▸
       at 2 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 0 3 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 1 3 (Toff204 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Bx0-213 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨0·123⟩-sw1-R c4) ▸
       at 5 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 3 3 (Toff204 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ Sw12 ∷ CCZ014 ∷ Bx0-123 ∷ []) (Bx2-0413 ∷ Sw12 ∷ [])
  b1 = at 6 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (CCZ024 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Bx0-213 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨0·123⟩-sw1-R c4) ▸
       at 0 6 (Bx2-0413 ∷ []) (refl) ▸ done

-- comm push BOX(4;213) sw0 L: 8 steps
lem-comm-push-BOX⟨4·213⟩-sw0-L : WsL → ⟪ (Bx4-213 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Bx4-203 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·213⟩-sw0-L c4 = run b0
  where
  b0 : Chain (Bx4-213 ∷ Sw01 ∷ []) (Sw01 ∷ Bx4-203 ∷ [])
  b0 = at 0 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) (refl) ▸
       at 5 2 (Sw01 ∷ Bx2-43 ∷ []) (sym (c₂ (Swap) (CZ ↑))) ▸
       at 4 2 (Sw01 ∷ CCZ024 ∷ []) (lem-comm-push-CCZ124-sw0-L c4) ▸
       at 3 2 (Sw01 ∷ Toff402 ∷ []) (lem-comm-push-TOFF412-sw0-L c4) ▸
       at 2 2 (Sw01 ∷ Bx2-43 ∷ []) (sym (c₂ (Swap) (CZ ↑))) ▸
       at 1 2 (Sw01 ∷ Toff402 ∷ []) (lem-comm-push-TOFF412-sw0-L c4) ▸
       at 0 2 (Sw01 ∷ CCZ024 ∷ []) (lem-comm-push-CCZ124-sw0-L c4) ▸
       at 1 6 (Bx4-203 ∷ []) (refl) ▸ done

-- comm push SBOX(2;4;10;3) sw1 L: 9 steps
lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L : WsL → ⟪ (Sb2-4-10-3 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sb1-4-20-3 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb2-4-10-3 ∷ Sw12 ∷ []) (Sw12 ∷ Bx1-4203 ∷ Toff302 ∷ Sb2-4-3-0 ∷ Toff302 ∷ Sb⁻2-4-3-0 ∷ [])
  b0 = at 0 1 (Bx2-4103 ∷ Toff301 ∷ Sb2-4-3-0 ∷ Toff301 ∷ Sb⁻2-4-3-0 ∷ []) (refl) ▸
       at 4 2 (Sw12 ∷ Sb⁻2-4-3-0 ∷ []) (sym (c₃ (Swap ↑) (CS • CS • CS))) ▸
       at 3 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 4 3 (Toff302 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw12 ∷ Sb2-4-3-0 ∷ []) (sym (c₃ (Swap ↑) (CS))) ▸
       at 1 0 (Sw12 ∷ Sw12 ∷ []) (sym (wl0006 c4)) ▸
       at 2 3 (Toff302 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 (Sw12 ∷ Bx1-4203 ∷ []) (lem-comm-push-BOX⟨2·4103⟩-sw1-L c4) ▸ done

  b1 : Chain (Sw12 ∷ Bx1-4203 ∷ Toff302 ∷ Sb2-4-3-0 ∷ Toff302 ∷ Sb⁻2-4-3-0 ∷ []) (Sw12 ∷ Sb1-4-20-3 ∷ [])
  b1 = at 1 5 (Sb1-4-20-3 ∷ []) (refl) ▸ done

-- comm push BOX(4;103) sw0 L: 8 steps
lem-comm-push-BOX⟨4·103⟩-sw0-L : WsL → ⟪ (Bx4-103 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Bx4-013 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·103⟩-sw0-L c4 = run b0
  where
  b0 : Chain (Bx4-103 ∷ Sw01 ∷ []) (Sw01 ∷ Bx4-013 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff401 ∷ Bx1-43 ∷ Toff401 ∷ CCZ014 ∷ Bx1-43 ∷ []) (refl) ▸
       at 5 2 (Sw01 ∷ Bx1-43 ∷ []) (sym (c₂ (Swap) (CZ ↑))) ▸
       at 4 2 (Sw01 ∷ CCZ014 ∷ []) (lem-comm-push-CCZ014-sw0-L c4) ▸
       at 3 2 (Sw01 ∷ Toff401 ∷ []) (lem-comm-push-TOFF401-sw0-L c4) ▸
       at 2 2 (Sw01 ∷ Bx1-43 ∷ []) (sym (c₂ (Swap) (CZ ↑))) ▸
       at 1 2 (Sw01 ∷ Toff401 ∷ []) (lem-comm-push-TOFF401-sw0-L c4) ▸
       at 0 2 (Sw01 ∷ CCZ014 ∷ []) (lem-comm-push-CCZ014-sw0-L c4) ▸
       at 1 6 (Bx4-013 ∷ []) (refl) ▸ done

-- comm push BOX(4;013) sw2 L: 8 steps
lem-comm-push-BOX⟨4·013⟩-sw2-L : WsL → ⟪ (Bx4-013 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Bx4-012 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·013⟩-sw2-L c4 = run b0
  where
  b0 : Chain (Bx4-013 ∷ Sw23 ∷ []) (Sw23 ∷ Bx4-012 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) (refl) ▸
       at 5 2 (Sw23 ∷ Bx0-42 ∷ []) (lem-comm-push-BOX⟨0·43⟩-sw2-L c4) ▸
       at 4 2 (Sw23 ∷ CCZ014 ∷ []) (lem-comm-push-CCZ014-sw2-L c4) ▸
       at 3 2 (Sw23 ∷ Toff401 ∷ []) (lem-comm-push-TOFF401-sw2-L c4) ▸
       at 2 2 (Sw23 ∷ Bx0-42 ∷ []) (lem-comm-push-BOX⟨0·43⟩-sw2-L c4) ▸
       at 1 2 (Sw23 ∷ Toff401 ∷ []) (lem-comm-push-TOFF401-sw2-L c4) ▸
       at 0 2 (Sw23 ∷ CCZ014 ∷ []) (lem-comm-push-CCZ014-sw2-L c4) ▸
       at 1 6 (Bx4-012 ∷ []) (refl) ▸ done

-- comm push BOX(0;4312) sw1 L: 8 steps
lem-comm-push-BOX⟨0·4312⟩-sw1-L : WsL → ⟪ (Bx0-4312 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Bx0-4321 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·4312⟩-sw1-L c4 = run b0
  where
  b0 : Chain (Bx0-4312 ∷ Sw12 ∷ []) (Sw12 ∷ Bx0-4321 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ []) (refl) ▸
       at 5 2 (Sw12 ∷ Bx4-021 ∷ []) (lem-comm-push-BOX⟨4·012⟩-sw1-L c4) ▸
       at 4 2 (Sw12 ∷ CCZ034 ∷ []) (lem-comm-push-CCZ034-sw1-L c4) ▸
       at 3 2 (Sw12 ∷ Toff034 ∷ []) (lem-comm-push-TOFF034-sw1-L c4) ▸
       at 2 2 (Sw12 ∷ Bx4-021 ∷ []) (lem-comm-push-BOX⟨4·012⟩-sw1-L c4) ▸
       at 1 2 (Sw12 ∷ Toff034 ∷ []) (lem-comm-push-TOFF034-sw1-L c4) ▸
       at 0 2 (Sw12 ∷ CCZ034 ∷ []) (lem-comm-push-CCZ034-sw1-L c4) ▸
       at 1 6 (Bx0-4321 ∷ []) (refl) ▸ done

-- comm push BOX(4;021) sw3 L: 8 steps
lem-comm-push-BOX⟨4·021⟩-sw3-L : WsL → ⟪ (Bx4-021 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ Bx3-021 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·021⟩-sw3-L c4 = run b0
  where
  b0 : Chain (Bx4-021 ∷ Sw34 ∷ []) (Sw34 ∷ Bx3-021 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) (refl) ▸
       at 5 2 (Sw34 ∷ Bx0-31 ∷ []) (lem-comm-push-BOX⟨0·41⟩-sw3-L c4) ▸
       at 4 2 (Sw34 ∷ CCZ023 ∷ []) (lem-comm-push-CCZ024-sw3-L c4) ▸
       at 3 2 (Sw34 ∷ Toff302 ∷ []) (lem-comm-push-TOFF402-sw3-L c4) ▸
       at 2 2 (Sw34 ∷ Bx0-31 ∷ []) (lem-comm-push-BOX⟨0·41⟩-sw3-L c4) ▸
       at 1 2 (Sw34 ∷ Toff302 ∷ []) (lem-comm-push-TOFF402-sw3-L c4) ▸
       at 0 2 (Sw34 ∷ CCZ023 ∷ []) (lem-comm-push-CCZ024-sw3-L c4) ▸
       at 1 6 (Bx3-021 ∷ []) (refl) ▸ done

-- comm push BOX(0;3421) sw2 L: 12 steps
lem-comm-push-BOX⟨0·3421⟩-sw2-L : WsL → ⟪ (Bx0-3421 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Bx0-2431 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·3421⟩-sw2-L c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-3421 ∷ Sw23 ∷ []) (CCZ034 ∷ Sw23 ∷ Toff024 ∷ Sw23 ∷ Sw23 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ []) (refl) ▸
       at 5 2 (Sw23 ∷ Bx2-031 ∷ []) (lem-comm-push-BOX⟨3·021⟩-sw2-L c4) ▸
       at 4 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] (wl0003 c4) ▸
       at 3 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] (wl0003 c4) ▸
       at 2 2 (Sw23 ∷ Bx2-031 ∷ []) (lem-comm-push-BOX⟨3·021⟩-sw2-L c4) ▸
       at 1 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CCZ034 ∷ Sw23 ∷ Toff024 ∷ Sw23 ∷ Sw23 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) (Sw23 ∷ Bx0-2431 ∷ [])
  b1 = at 3 2 [] (wl0003 c4) ▸
       at 0 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] (wl0003 c4) ▸
       at 1 6 (Bx0-2431 ∷ []) (refl) ▸ done

-- comm push BOX(0;2431) sw2 R: 12 steps
lem-comm-push-BOX⟨0·2431⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·2431⟩-sw2-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Bx0-2431 ∷ []) (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ Sw23 ∷ CCZ024 ∷ Bx2-031 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) (refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 3 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (Toff034 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Bx3-021 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨2·031⟩-sw2-R c4) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 3 (Toff034 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ Sw23 ∷ CCZ024 ∷ Bx2-031 ∷ []) (Bx0-3421 ∷ Sw23 ∷ [])
  b1 = at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Bx3-021 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨2·031⟩-sw2-R c4) ▸
       at 0 6 (Bx0-3421 ∷ []) (refl) ▸ done

-- comm push BOX(3;021) sw3 R: 8 steps
lem-comm-push-BOX⟨3·021⟩-sw3-R : WsL → ⟪ (Sw34 ∷ Bx3-021 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-021 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨3·021⟩-sw3-R c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-021 ∷ []) (Bx4-021 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw34 ∷ []) (lem-comm-push-CCZ023-sw3-R c4) ▸
       at 1 2 (Toff402 ∷ Sw34 ∷ []) (lem-comm-push-TOFF302-sw3-R c4) ▸
       at 2 2 (Bx0-41 ∷ Sw34 ∷ []) (lem-comm-push-BOX⟨0·31⟩-sw3-R c4) ▸
       at 3 2 (Toff402 ∷ Sw34 ∷ []) (lem-comm-push-TOFF302-sw3-R c4) ▸
       at 4 2 (CCZ024 ∷ Sw34 ∷ []) (lem-comm-push-CCZ023-sw3-R c4) ▸
       at 5 2 (Bx0-41 ∷ Sw34 ∷ []) (lem-comm-push-BOX⟨0·31⟩-sw3-R c4) ▸
       at 0 6 (Bx4-021 ∷ []) (refl) ▸ done

-- comm push BOX(0;4321) sw1 R: 8 steps
lem-comm-push-BOX⟨0·4321⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx0-4321 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·4321⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx0-4321 ∷ []) (Bx0-4312 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-021 ∷ Toff034 ∷ CCZ034 ∷ Bx4-021 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw12 ∷ []) (lem-comm-push-CCZ034-sw1-R c4) ▸
       at 1 2 (Toff034 ∷ Sw12 ∷ []) (lem-comm-push-TOFF034-sw1-R c4) ▸
       at 2 2 (Bx4-012 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨4·021⟩-sw1-R c4) ▸
       at 3 2 (Toff034 ∷ Sw12 ∷ []) (lem-comm-push-TOFF034-sw1-R c4) ▸
       at 4 2 (CCZ034 ∷ Sw12 ∷ []) (lem-comm-push-CCZ034-sw1-R c4) ▸
       at 5 2 (Bx4-012 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨4·021⟩-sw1-R c4) ▸
       at 0 6 (Bx0-4312 ∷ []) (refl) ▸ done

-- comm push BOX(4;012) sw2 R: 8 steps
lem-comm-push-BOX⟨4·012⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx4-012 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-013 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·012⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx4-012 ∷ []) (Bx4-013 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-comm-push-CCZ014-sw2-R c4) ▸
       at 1 2 (Toff401 ∷ Sw23 ∷ []) (lem-comm-push-TOFF401-sw2-R c4) ▸
       at 2 2 (Bx0-43 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨0·42⟩-sw2-R c4) ▸
       at 3 2 (Toff401 ∷ Sw23 ∷ []) (lem-comm-push-TOFF401-sw2-R c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-comm-push-CCZ014-sw2-R c4) ▸
       at 5 2 (Bx0-43 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨0·42⟩-sw2-R c4) ▸
       at 0 6 (Bx4-013 ∷ []) (refl) ▸ done

-- comm push BOX(4;013) sw0 R: 8 steps
lem-comm-push-BOX⟨4·013⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx4-013 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-103 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·013⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-013 ∷ []) (Bx4-103 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw01 ∷ []) (lem-comm-push-CCZ014-sw0-R c4) ▸
       at 1 2 (Toff401 ∷ Sw01 ∷ []) (lem-comm-push-TOFF401-sw0-R c4) ▸
       at 2 2 (Bx0-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 3 2 (Toff401 ∷ Sw01 ∷ []) (lem-comm-push-TOFF401-sw0-R c4) ▸
       at 4 2 (CCZ014 ∷ Sw01 ∷ []) (lem-comm-push-CCZ014-sw0-R c4) ▸
       at 5 2 (Bx0-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 0 6 (Bx4-103 ∷ []) (refl) ▸ done

-- comm push SBOX(1;4;20;3) sw1 R: 9 steps
lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Sb1-4-20-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-10-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Sb1-4-20-3 ∷ []) (Bx2-4103 ∷ Toff301 ∷ Sb1-4-3-0 ∷ Toff301 ∷ Sb⁻1-4-3-0 ∷ Sw12 ∷ [])
  b0 = at 1 1 (Bx1-4203 ∷ Toff302 ∷ Sb1-4-3-0 ∷ Toff302 ∷ Sb⁻1-4-3-0 ∷ []) (refl) ▸
       at 0 2 (Bx2-4103 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨1·4203⟩-sw1-R c4) ▸
       at 2 1 (Sw12 ∷ Toff301 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0006 c4) ▸
       at 2 2 (Sb1-4-3-0 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS)) ▸
       at 4 1 (Sw12 ∷ Toff301 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0006 c4) ▸
       at 4 2 (Sb⁻1-4-3-0 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS)) ▸ done

  b1 : Chain (Bx2-4103 ∷ Toff301 ∷ Sb1-4-3-0 ∷ Toff301 ∷ Sb⁻1-4-3-0 ∷ Sw12 ∷ []) (Sb2-4-10-3 ∷ Sw12 ∷ [])
  b1 = at 0 5 (Sb2-4-10-3 ∷ []) (refl) ▸ done

-- comm push BOX(4;203) sw0 R: 8 steps
lem-comm-push-BOX⟨4·203⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx4-203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-213 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·203⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-203 ∷ []) (Bx4-213 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-comm-push-CCZ024-sw0-R c4) ▸
       at 1 2 (Toff412 ∷ Sw01 ∷ []) (lem-comm-push-TOFF402-sw0-R c4) ▸
       at 2 2 (Bx2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 3 2 (Toff412 ∷ Sw01 ∷ []) (lem-comm-push-TOFF402-sw0-R c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-comm-push-CCZ024-sw0-R c4) ▸
       at 5 2 (Bx2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 0 6 (Bx4-213 ∷ []) (refl) ▸ done

-- comm push BOX(0;2431) sw0 R: 8 steps
lem-comm-push-BOX⟨0·2431⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2430 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·2431⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-2431 ∷ []) (Bx1-2430 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-comm-push-CCZ024-sw0-R c4) ▸
       at 1 2 (Toff124 ∷ Sw01 ∷ []) (lem-comm-push-TOFF024-sw0-R c4) ▸
       at 2 2 (Bx2-130 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨2·031⟩-sw0-R c4) ▸
       at 3 2 (Toff124 ∷ Sw01 ∷ []) (lem-comm-push-TOFF024-sw0-R c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-comm-push-CCZ024-sw0-R c4) ▸
       at 5 2 (Bx2-130 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨2·031⟩-sw0-R c4) ▸
       at 0 6 (Bx1-2430 ∷ []) (refl) ▸ done

-- comm push BOX(1;2430) sw1 R: 8 steps
lem-comm-push-BOX⟨1·2430⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx1-2430 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·2430⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx1-2430 ∷ []) (Bx2-1430 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff124 ∷ Bx2-130 ∷ Toff124 ∷ CCZ124 ∷ Bx2-130 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0122 c4)) ▸
       at 1 2 (Toff214 ∷ Sw12 ∷ []) (wl0123 c4) ▸
       at 2 2 (Bx1-230 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨2·130⟩-sw1-R c4) ▸
       at 3 2 (Toff214 ∷ Sw12 ∷ []) (wl0123 c4) ▸
       at 4 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0122 c4)) ▸
       at 5 2 (Bx1-230 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨2·130⟩-sw1-R c4) ▸
       at 0 6 (Bx2-1430 ∷ []) (refl) ▸ done

-- comm push SBOX(2;1;43;0) sw2 R: 9 steps
lem-comm-push-SBOX⟨2·1·43·0⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb2-1-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-42-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨2·1·43·0⟩-sw2-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Sb2-1-43-0 ∷ []) (Bx3-1420 ∷ Toff024 ∷ Sb2-1-0-3 ∷ Toff024 ∷ Sb⁻2-1-0-3 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx2-1430 ∷ Toff034 ∷ Sb2-1-0-3 ∷ Toff034 ∷ Sb⁻2-1-0-3 ∷ []) (refl) ▸
       at 0 2 (Bx3-1420 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨2·1430⟩-sw2-R c4) ▸
       at 2 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0003 c4) ▸
       at 2 2 (Sb2-1-0-3 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 4 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0003 c4) ▸
       at 4 2 (Sb⁻2-1-0-3 ∷ Sw23 ∷ []) (sym (c₂ (CS • CS • CS) (Swap))) ▸ done

  b1 : Chain (Bx3-1420 ∷ Toff024 ∷ Sb2-1-0-3 ∷ Toff024 ∷ Sb⁻2-1-0-3 ∷ Sw23 ∷ []) (Sb3-1-42-0 ∷ Sw23 ∷ [])
  b1 = at 0 5 (Sb3-1-42-0 ∷ []) (refl) ▸ done

-- comm push SBOX(3;1;42;0) sw3 R: 7 steps
lem-comm-push-SBOX⟨3·1·42·0⟩-sw3-R : WsL → ⟪ (Sw34 ∷ Sb3-1-42-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-32-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨3·1·42·0⟩-sw3-R c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Sb3-1-42-0 ∷ []) (Sb4-1-32-0 ∷ Sw34 ∷ [])
  b0 = at 1 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) (refl) ▸
       at 0 2 (Bx4-1320 ∷ Sw34 ∷ []) (lem-comm-push-BOX⟨3·1420⟩-sw3-R c4) ▸
       at 1 2 (Toff023 ∷ Sw34 ∷ []) (lem-comm-push-TOFF024-sw3-R c4) ▸
       at 2 2 (Sb3-1-0-2 ∷ Sw34 ∷ []) (sym (c₂ (CS) (Swap ↑))) ▸
       at 3 2 (Toff023 ∷ Sw34 ∷ []) (lem-comm-push-TOFF024-sw3-R c4) ▸
       at 4 2 (Sb⁻3-1-0-2 ∷ Sw34 ∷ []) (sym (c₂ (CS • CS • CS) (Swap ↑))) ▸
       at 0 5 (Sb4-1-32-0 ∷ []) (refl) ▸ done

-- comm push SBOX(4;1;32;0) sw2 R: 7 steps
lem-comm-push-SBOX⟨4·1·32·0⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Sb4-1-32-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-23-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-SBOX⟨4·1·32·0⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb4-1-32-0 ∷ []) (Sb4-1-23-0 ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx4-1320 ∷ Toff023 ∷ Sb4-1-0-2 ∷ Toff023 ∷ Sb⁻4-1-0-2 ∷ []) (refl) ▸
       at 0 2 (Bx4-1230 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨4·1320⟩-sw2-R c4) ▸
       at 1 2 (Toff023 ∷ Sw23 ∷ []) (wl0143 c4) ▸
       at 2 2 (Sb4-1-0-2 ∷ Sw23 ∷ []) (sym (c₂ (CS) (Swap))) ▸
       at 3 2 (Toff023 ∷ Sw23 ∷ []) (wl0143 c4) ▸
       at 4 2 (Sb⁻4-1-0-2 ∷ Sw23 ∷ []) (sym (c₂ (CS • CS • CS) (Swap))) ▸
       at 0 5 (Sb4-1-23-0 ∷ []) (refl) ▸ done

-- comm push BOX(4;1230) sw1 R: 8 steps
lem-comm-push-BOX⟨4·1230⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2130 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·1230⟩-sw1-R c4 = run b0
  where
  b0 : Chain (Sw12 ∷ Bx4-1230 ∷ []) (Bx4-2130 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx1-430 ∷ Toff412 ∷ CCZ124 ∷ Bx1-430 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0122 c4)) ▸
       at 1 2 (Toff412 ∷ Sw12 ∷ []) (wl0144 c4) ▸
       at 2 2 (Bx2-430 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨1·430⟩-sw1-R c4) ▸
       at 3 2 (Toff412 ∷ Sw12 ∷ []) (wl0144 c4) ▸
       at 4 2 (CCZ124 ∷ Sw12 ∷ []) (sym (wl0122 c4)) ▸
       at 5 2 (Bx2-430 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨1·430⟩-sw1-R c4) ▸
       at 0 6 (Bx4-2130 ∷ []) (refl) ▸ done

-- comm push BOX(4;2130) sw0 R: 8 steps
lem-comm-push-BOX⟨4·2130⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx4-2130 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·2130⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx4-2130 ∷ []) (Bx4-2031 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx2-430 ∷ Toff412 ∷ CCZ124 ∷ Bx2-430 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (lem-comm-push-CCZ124-sw0-R c4) ▸
       at 1 2 (Toff402 ∷ Sw01 ∷ []) (lem-comm-push-TOFF412-sw0-R c4) ▸
       at 2 2 (Bx2-431 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨2·430⟩-sw0-R c4) ▸
       at 3 2 (Toff402 ∷ Sw01 ∷ []) (lem-comm-push-TOFF412-sw0-R c4) ▸
       at 4 2 (CCZ024 ∷ Sw01 ∷ []) (lem-comm-push-CCZ124-sw0-R c4) ▸
       at 5 2 (Bx2-431 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨2·430⟩-sw0-R c4) ▸
       at 0 6 (Bx4-2031 ∷ []) (refl) ▸ done

-- comm push BOX(2;0413) sw2 R: 12 steps
lem-comm-push-BOX⟨2·0413⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨2·0413⟩-sw2-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Bx2-0413 ∷ []) (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ Sw23 ∷ CCZ024 ∷ Bx0-213 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (refl) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 0 3 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 1 3 (Toff304 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Bx0-312 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨0·213⟩-sw2-R c4) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 3 3 (Toff304 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ Sw23 ∷ CCZ024 ∷ Bx0-213 ∷ []) (Bx3-0412 ∷ Sw23 ∷ [])
  b1 = at 6 0 (Sw23 ∷ Sw23 ∷ []) (sym (wl0003 c4)) ▸
       at 4 3 (CCZ034 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Bx0-312 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨0·213⟩-sw2-R c4) ▸
       at 0 6 (Bx3-0412 ∷ []) (refl) ▸ done

-- comm push BOX(3;0412) sw3 R: 8 steps
lem-comm-push-BOX⟨3·0412⟩-sw3-R : WsL → ⟪ (Sw34 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨3·0412⟩-sw3-R c4 = run b0
  where
  b0 : Chain (Sw34 ∷ Bx3-0412 ∷ []) (Bx4-0312 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw34 ∷ []) (lem-comm-push-CCZ034-sw3-R c4) ▸
       at 1 2 (Toff403 ∷ Sw34 ∷ []) (lem-comm-push-TOFF304-sw3-R c4) ▸
       at 2 2 (Bx0-412 ∷ Sw34 ∷ []) (lem-comm-push-BOX⟨0·312⟩-sw3-R c4) ▸
       at 3 2 (Toff403 ∷ Sw34 ∷ []) (lem-comm-push-TOFF304-sw3-R c4) ▸
       at 4 2 (CCZ034 ∷ Sw34 ∷ []) (lem-comm-push-CCZ034-sw3-R c4) ▸
       at 5 2 (Bx0-412 ∷ Sw34 ∷ []) (lem-comm-push-BOX⟨0·312⟩-sw3-R c4) ▸
       at 0 6 (Bx4-0312 ∷ []) (refl) ▸ done

-- comm push BOX(0;412) sw2 R: 8 steps
lem-comm-push-BOX⟨0·412⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx0-412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-413 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·412⟩-sw2-R c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Bx0-412 ∷ []) (Bx0-413 ∷ Sw23 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-02 ∷ Toff014 ∷ CCZ014 ∷ Bx4-02 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw23 ∷ []) (lem-comm-push-CCZ014-sw2-R c4) ▸
       at 1 2 (Toff014 ∷ Sw23 ∷ []) (lem-comm-push-TOFF014-sw2-R c4) ▸
       at 2 2 (Bx4-03 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨4·02⟩-sw2-R c4) ▸
       at 3 2 (Toff014 ∷ Sw23 ∷ []) (lem-comm-push-TOFF014-sw2-R c4) ▸
       at 4 2 (CCZ014 ∷ Sw23 ∷ []) (lem-comm-push-CCZ014-sw2-R c4) ▸
       at 5 2 (Bx4-03 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨4·02⟩-sw2-R c4) ▸
       at 0 6 (Bx0-413 ∷ []) (refl) ▸ done

-- comm push BOX(4;0213) sw1 R: 12 steps
lem-comm-push-BOX⟨4·0213⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·0213⟩-sw1-R c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx4-0213 ∷ []) (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ Sw12 ∷ CCZ024 ∷ Bx0-413 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-413 ∷ Toff402 ∷ CCZ024 ∷ Bx0-413 ∷ []) (refl) ▸
       at 1 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 0 2 [] (wl0006 c4) ▸
       at 2 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 [] (wl0006 c4) ▸
       at 2 2 (Bx0-423 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨0·413⟩-sw1-R c4) ▸
       at 4 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] (wl0006 c4) ▸ done

  b1 : Chain (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ Sw12 ∷ CCZ024 ∷ Bx0-413 ∷ []) (Bx4-0123 ∷ Sw12 ∷ [])
  b1 = at 5 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] (wl0006 c4) ▸
       at 5 2 (Bx0-423 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨0·413⟩-sw1-R c4) ▸
       at 0 6 (Bx4-0123 ∷ []) (refl) ▸ done

-- comm push BOX(0;423) sw0 R: 8 steps
lem-comm-push-BOX⟨0·423⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx0-423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-423 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·423⟩-sw0-R c4 = run b0
  where
  b0 : Chain (Sw01 ∷ Bx0-423 ∷ []) (Bx1-423 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (lem-comm-push-CCZ024-sw0-R c4) ▸
       at 1 2 (Toff124 ∷ Sw01 ∷ []) (lem-comm-push-TOFF024-sw0-R c4) ▸
       at 2 2 (Bx4-13 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨4·03⟩-sw0-R c4) ▸
       at 3 2 (Toff124 ∷ Sw01 ∷ []) (lem-comm-push-TOFF024-sw0-R c4) ▸
       at 4 2 (CCZ124 ∷ Sw01 ∷ []) (lem-comm-push-CCZ024-sw0-R c4) ▸
       at 5 2 (Bx4-13 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨4·03⟩-sw0-R c4) ▸
       at 0 6 (Bx1-423 ∷ []) (refl) ▸ done
