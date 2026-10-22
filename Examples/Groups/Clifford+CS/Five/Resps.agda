------------------------------------------------------------------------
-- Presentations of groups
--
-- The placed-window tables of the five-wire derivations
--
-- For each idle wire i, the letters that avoid it with a four-wire word
-- u and ⟪ g ⟫ ≈ place i u (Five.Win.Resp): a letter spelled off i by
-- its literal entry, one spelled across i by its respelling lemma
-- (Five.D.R*: the letter wrapped in the swaps of the cycle that place
-- conjugates by); pwᵢ is the placed window with wire i idle.  Written by
-- `scratchpad/five/emit5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Resps where

open import Data.Maybe using (Maybe ; just ; nothing)
import Data.Maybe as Maybe
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (_•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Flat using (by-flat)
open import Examples.Groups.Clifford+CS.Five.Lits
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-resp-CCZ013-at-2 ; lem-resp-CCZ023-at-1 ; lem-resp-CCZ124-at-3 ; lem-resp-CCZ134-at-2 ; lem-resp-CS02-at-1 ; lem-resp-CS03-at-1 ; lem-resp-CS03-at-2 ; lem-resp-CS13-at-2 ; lem-resp-CS14-at-2 ; lem-resp-CS14-at-3 ; lem-resp-CS24-at-3 ; lem-resp-CSd02-at-1 ; lem-resp-CSd03-at-1 ; lem-resp-CSd03-at-2 ; lem-resp-CSd13-at-2 ; lem-resp-CSd14-at-2 ; lem-resp-CSd14-at-3 ; lem-resp-CSd24-at-3 ; lem-resp-CX02-at-1 ; lem-resp-CX03-at-1 ; lem-resp-CX13-at-2 ; lem-resp-CX14-at-2 ; lem-resp-CX14-at-3 ; lem-resp-CX20-at-1 ; lem-resp-CX24-at-3 ; lem-resp-CX30-at-1 ; lem-resp-CX31-at-2 ; lem-resp-CX41-at-2 ; lem-resp-CX41-at-3 ; lem-resp-CX42-at-3 ; lem-resp-CZ02-at-1 ; lem-resp-CZ03-at-1 ; lem-resp-CZ13-at-2 ; lem-resp-CZ14-at-2 ; lem-resp-CZ14-at-3 ; lem-resp-CZ24-at-3 ; lem-resp-SWAP13-at-2 ; lem-resp-SWAP14-at-2 ; lem-resp-SWAP14-at-3 ; lem-resp-TOFF013-at-2 ; lem-resp-TOFF023-at-1 ; lem-resp-TOFF103-at-2 ; lem-resp-TOFF124-at-3 ; lem-resp-TOFF134-at-2 ; lem-resp-TOFF203-at-1 ; lem-resp-TOFF214-at-3 ; lem-resp-TOFF301-at-2 ; lem-resp-TOFF302-at-1 ; lem-resp-TOFF314-at-2 ; lem-resp-TOFF412-at-3)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-resp-CK41-at-2 ; lem-resp-CX03-at-2 ; lem-resp-CX30-at-2 ; lem-resp-SWAP03-at-1 ; lem-resp-SWAP03-at-2 ; lem-resp-SWAP24-at-3 ; lem-resp-TOFF413-at-2)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-resp-CK41-at-3 ; lem-resp-CK42-at-3 ; lem-resp-CZ03-at-2 ; lem-resp-SWAP02-at-1)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-resp-CK02-at-1 ; lem-resp-CK03-at-1 ; lem-resp-CK03-at-2)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-resp-CS04-at-1 ; lem-resp-CS04-at-2 ; lem-resp-CS04-at-3 ; lem-resp-CSd04-at-1 ; lem-resp-CSd04-at-2 ; lem-resp-CSd04-at-3 ; lem-resp-CX04-at-1 ; lem-resp-CX04-at-2 ; lem-resp-CZ04-at-1)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-resp-CK40-at-1 ; lem-resp-CK40-at-2 ; lem-resp-CK40-at-3 ; lem-resp-CKd40-at-1 ; lem-resp-CX04-at-3 ; lem-resp-CX40-at-1 ; lem-resp-CX40-at-2 ; lem-resp-CX40-at-3 ; lem-resp-CZ04-at-2 ; lem-resp-CZ04-at-3 ; lem-resp-SWAP04-at-1)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-resp-CCZ014-at-2 ; lem-resp-CCZ014-at-3 ; lem-resp-CCZ024-at-1 ; lem-resp-CCZ024-at-3 ; lem-resp-CCZ034-at-1 ; lem-resp-CCZ034-at-2 ; lem-resp-TOFF014-at-2 ; lem-resp-TOFF014-at-3 ; lem-resp-TOFF024-at-1 ; lem-resp-TOFF024-at-3 ; lem-resp-TOFF034-at-1 ; lem-resp-TOFF034-at-2 ; lem-resp-TOFF104-at-2 ; lem-resp-TOFF104-at-3 ; lem-resp-TOFF204-at-1 ; lem-resp-TOFF204-at-3 ; lem-resp-TOFF304-at-1 ; lem-resp-TOFF304-at-2 ; lem-resp-TOFF401-at-2 ; lem-resp-TOFF401-at-3 ; lem-resp-TOFF402-at-1 ; lem-resp-TOFF402-at-3 ; lem-resp-TOFF403-at-1 ; lem-resp-TOFF403-at-2)

resp0 : WsL → (g : Mac) → Maybe (W0.Resp g)
resp0 L g = Maybe.map W0.fromLit (lit0 g)

pw0 : (c4 : Complete 4) (L : WsL) → _
pw0 c4 L = W0.pwin (resp0 L) c4

resp1 : WsL → (g : Mac) → Maybe (W1.Resp g)
resp1 L CCZ023 = just (W1.resp (CCZ) (trans (lem-resp-CCZ023-at-1 L) (by-flat Eq.refl)))
resp1 L CCZ024 = just (W1.resp (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (trans (lem-resp-CCZ024-at-1 L) (by-flat Eq.refl)))
resp1 L CCZ034 = just (W1.resp (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (trans (lem-resp-CCZ034-at-1 L) (by-flat Eq.refl)))
resp1 L CK02 = just (W1.resp (CK₀₁) (trans (lem-resp-CK02-at-1 L) (by-flat Eq.refl)))
resp1 L CK03 = just (W1.resp (Swap ↑ • CK₀₁ • Swap ↑) (trans (lem-resp-CK03-at-1 L) (by-flat Eq.refl)))
resp1 L CK40 = just (W1.resp (Swap ↑ ↑ • (Swap ↑ • CK₁₀ • Swap ↑) • Swap ↑ ↑) (trans (lem-resp-CK40-at-1 L) (by-flat Eq.refl)))
resp1 L CK40⁻ = just (W1.resp (Swap ↑ ↑ • (Swap ↑ • (S ↑ • CK₁₀) • Swap ↑) • Swap ↑ ↑) (trans (lem-resp-CKd40-at-1 L) (by-flat Eq.refl)))
resp1 L CS02 = just (W1.resp (CS) (trans (lem-resp-CS02-at-1 L) (by-flat Eq.refl)))
resp1 L CS02⁻ = just (W1.resp (CS • CS • CS) (trans (lem-resp-CSd02-at-1 L) (by-flat Eq.refl)))
resp1 L CS03 = just (W1.resp (Swap ↑ • CS • Swap ↑) (trans (lem-resp-CS03-at-1 L) (by-flat Eq.refl)))
resp1 L CS03⁻ = just (W1.resp (Swap ↑ • (CS • CS • CS) • Swap ↑) (trans (lem-resp-CSd03-at-1 L) (by-flat Eq.refl)))
resp1 L CS04 = just (W1.resp (Swap ↑ ↑ • (Swap ↑ • CS • Swap ↑) • Swap ↑ ↑) (trans (lem-resp-CS04-at-1 L) (by-flat Eq.refl)))
resp1 L CS04⁻ = just (W1.resp (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (trans (lem-resp-CSd04-at-1 L) (by-flat Eq.refl)))
resp1 L CX02 = just (W1.resp (CX₀₁) (trans (lem-resp-CX02-at-1 L) (by-flat Eq.refl)))
resp1 L CX03 = just (W1.resp (Swap ↑ • CX₀₁ • Swap ↑) (trans (lem-resp-CX03-at-1 L) (by-flat Eq.refl)))
resp1 L CX04 = just (W1.resp (Swap ↑ ↑ • (Swap ↑ • CX₀₁ • Swap ↑) • Swap ↑ ↑) (trans (lem-resp-CX04-at-1 L) (by-flat Eq.refl)))
resp1 L CX20 = just (W1.resp (CX₁₀) (trans (lem-resp-CX20-at-1 L) (by-flat Eq.refl)))
resp1 L CX30 = just (W1.resp (Swap ↑ • CX₁₀ • Swap ↑) (trans (lem-resp-CX30-at-1 L) (by-flat Eq.refl)))
resp1 L CX40 = just (W1.resp (Swap ↑ ↑ • (Swap ↑ • CX₁₀ • Swap ↑) • Swap ↑ ↑) (trans (lem-resp-CX40-at-1 L) (by-flat Eq.refl)))
resp1 L CZ02 = just (W1.resp (CZ) (trans (lem-resp-CZ02-at-1 L) (by-flat Eq.refl)))
resp1 L CZ03 = just (W1.resp (Swap ↑ • CZ • Swap ↑) (trans (lem-resp-CZ03-at-1 L) (by-flat Eq.refl)))
resp1 L CZ04 = just (W1.resp (Swap ↑ ↑ • (Swap ↑ • CZ • Swap ↑) • Swap ↑ ↑) (trans (lem-resp-CZ04-at-1 L) (by-flat Eq.refl)))
resp1 L Sw02 = just (W1.resp (Swap) (trans (lem-resp-SWAP02-at-1 L) (by-flat Eq.refl)))
resp1 L Sw03 = just (W1.resp (Swap ↑ • Swap • Swap ↑) (trans (lem-resp-SWAP03-at-1 L) (by-flat Eq.refl)))
resp1 L Sw04 = just (W1.resp (Swap ↑ ↑ • (Swap ↑ • Swap • Swap ↑) • Swap ↑ ↑) (trans (lem-resp-SWAP04-at-1 L) (by-flat Eq.refl)))
resp1 L Toff023 = just (W1.resp (Toff) (trans (lem-resp-TOFF023-at-1 L) (by-flat Eq.refl)))
resp1 L Toff024 = just (W1.resp (Swap ↑ ↑ • Toff • Swap ↑ ↑) (trans (lem-resp-TOFF024-at-1 L) (by-flat Eq.refl)))
resp1 L Toff034 = just (W1.resp (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (trans (lem-resp-TOFF034-at-1 L) (by-flat Eq.refl)))
resp1 L Toff203 = just (W1.resp (K ↑ • CCZ • K ↑ • iI) (trans (lem-resp-TOFF203-at-1 L) (by-flat Eq.refl)))
resp1 L Toff204 = just (W1.resp (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) (trans (lem-resp-TOFF204-at-1 L) (by-flat Eq.refl)))
resp1 L Toff302 = just (W1.resp (Toffᵗ) (trans (lem-resp-TOFF302-at-1 L) (by-flat Eq.refl)))
resp1 L Toff304 = just (W1.resp (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (trans (lem-resp-TOFF304-at-1 L) (by-flat Eq.refl)))
resp1 L Toff402 = just (W1.resp (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) (trans (lem-resp-TOFF402-at-1 L) (by-flat Eq.refl)))
resp1 L Toff403 = just (W1.resp (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) (trans (lem-resp-TOFF403-at-1 L) (by-flat Eq.refl)))
resp1 L g = Maybe.map W1.fromLit (lit1 g)

pw1 : (c4 : Complete 4) (L : WsL) → _
pw1 c4 L = W1.pwin (resp1 L) c4

resp2 : WsL → (g : Mac) → Maybe (W2.Resp g)
resp2 L CCZ013 = just (W2.resp (CCZ) (trans (lem-resp-CCZ013-at-2 L) (by-flat Eq.refl)))
resp2 L CCZ014 = just (W2.resp (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (trans (lem-resp-CCZ014-at-2 L) (by-flat Eq.refl)))
resp2 L CCZ034 = just (W2.resp (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (trans (lem-resp-CCZ034-at-2 L) (by-flat Eq.refl)))
resp2 L CCZ134 = just (W2.resp (CCZ ↑) (trans (lem-resp-CCZ134-at-2 L) (by-flat Eq.refl)))
resp2 L CK03 = just (W2.resp (Swap ↑ • CK₀₁ • Swap ↑) (trans (lem-resp-CK03-at-2 L) (by-flat Eq.refl)))
resp2 L CK40 = just (W2.resp (Swap ↑ ↑ • (Swap ↑ • CK₁₀ • Swap ↑) • Swap ↑ ↑) (trans (lem-resp-CK40-at-2 L) (by-flat Eq.refl)))
resp2 L CK41 = just (W2.resp (Swap ↑ ↑ • (CK₁₀ ↑) • Swap ↑ ↑) (trans (lem-resp-CK41-at-2 L) (by-flat Eq.refl)))
resp2 L CS03 = just (W2.resp (Swap ↑ • CS • Swap ↑) (trans (lem-resp-CS03-at-2 L) (by-flat Eq.refl)))
resp2 L CS03⁻ = just (W2.resp (Swap ↑ • (CS • CS • CS) • Swap ↑) (trans (lem-resp-CSd03-at-2 L) (by-flat Eq.refl)))
resp2 L CS04 = just (W2.resp (Swap ↑ ↑ • (Swap ↑ • CS • Swap ↑) • Swap ↑ ↑) (trans (lem-resp-CS04-at-2 L) (by-flat Eq.refl)))
resp2 L CS04⁻ = just (W2.resp (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (trans (lem-resp-CSd04-at-2 L) (by-flat Eq.refl)))
resp2 L CS13 = just (W2.resp (CS ↑) (trans (lem-resp-CS13-at-2 L) (by-flat Eq.refl)))
resp2 L CS13⁻ = just (W2.resp ((CS • CS • CS) ↑) (trans (lem-resp-CSd13-at-2 L) (by-flat Eq.refl)))
resp2 L CS14 = just (W2.resp (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (trans (lem-resp-CS14-at-2 L) (by-flat Eq.refl)))
resp2 L CS14⁻ = just (W2.resp (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑) (trans (lem-resp-CSd14-at-2 L) (by-flat Eq.refl)))
resp2 L CX03 = just (W2.resp (Swap ↑ • CX₀₁ • Swap ↑) (trans (lem-resp-CX03-at-2 L) (by-flat Eq.refl)))
resp2 L CX04 = just (W2.resp (Swap ↑ ↑ • (Swap ↑ • CX₀₁ • Swap ↑) • Swap ↑ ↑) (trans (lem-resp-CX04-at-2 L) (by-flat Eq.refl)))
resp2 L CX13 = just (W2.resp (CX₀₁ ↑) (trans (lem-resp-CX13-at-2 L) (by-flat Eq.refl)))
resp2 L CX14 = just (W2.resp (Swap ↑ ↑ • (CX₀₁ ↑) • Swap ↑ ↑) (trans (lem-resp-CX14-at-2 L) (by-flat Eq.refl)))
resp2 L CX30 = just (W2.resp (Swap ↑ • CX₁₀ • Swap ↑) (trans (lem-resp-CX30-at-2 L) (by-flat Eq.refl)))
resp2 L CX31 = just (W2.resp (CX₁₀ ↑) (trans (lem-resp-CX31-at-2 L) (by-flat Eq.refl)))
resp2 L CX40 = just (W2.resp (Swap ↑ ↑ • (Swap ↑ • CX₁₀ • Swap ↑) • Swap ↑ ↑) (trans (lem-resp-CX40-at-2 L) (by-flat Eq.refl)))
resp2 L CX41 = just (W2.resp (Swap ↑ ↑ • (CX₁₀ ↑) • Swap ↑ ↑) (trans (lem-resp-CX41-at-2 L) (by-flat Eq.refl)))
resp2 L CZ03 = just (W2.resp (Swap ↑ • CZ • Swap ↑) (trans (lem-resp-CZ03-at-2 L) (by-flat Eq.refl)))
resp2 L CZ04 = just (W2.resp (Swap ↑ ↑ • (Swap ↑ • CZ • Swap ↑) • Swap ↑ ↑) (trans (lem-resp-CZ04-at-2 L) (by-flat Eq.refl)))
resp2 L CZ13 = just (W2.resp (CZ ↑) (trans (lem-resp-CZ13-at-2 L) (by-flat Eq.refl)))
resp2 L CZ14 = just (W2.resp (Swap ↑ ↑ • (CZ ↑) • Swap ↑ ↑) (trans (lem-resp-CZ14-at-2 L) (by-flat Eq.refl)))
resp2 L Sw03 = just (W2.resp (Swap ↑ • Swap • Swap ↑) (trans (lem-resp-SWAP03-at-2 L) (by-flat Eq.refl)))
resp2 L Sw13 = just (W2.resp (Swap ↑) (trans (lem-resp-SWAP13-at-2 L) (by-flat Eq.refl)))
resp2 L Sw14 = just (W2.resp (Swap ↑ ↑ • (Swap ↑) • Swap ↑ ↑) (trans (lem-resp-SWAP14-at-2 L) (by-flat Eq.refl)))
resp2 L Toff013 = just (W2.resp (Toff) (trans (lem-resp-TOFF013-at-2 L) (by-flat Eq.refl)))
resp2 L Toff014 = just (W2.resp (Swap ↑ ↑ • Toff • Swap ↑ ↑) (trans (lem-resp-TOFF014-at-2 L) (by-flat Eq.refl)))
resp2 L Toff034 = just (W2.resp (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (trans (lem-resp-TOFF034-at-2 L) (by-flat Eq.refl)))
resp2 L Toff103 = just (W2.resp (K ↑ • CCZ • K ↑ • iI) (trans (lem-resp-TOFF103-at-2 L) (by-flat Eq.refl)))
resp2 L Toff104 = just (W2.resp (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) (trans (lem-resp-TOFF104-at-2 L) (by-flat Eq.refl)))
resp2 L Toff134 = just (W2.resp (Toff ↑) (trans (lem-resp-TOFF134-at-2 L) (by-flat Eq.refl)))
resp2 L Toff301 = just (W2.resp (Toffᵗ) (trans (lem-resp-TOFF301-at-2 L) (by-flat Eq.refl)))
resp2 L Toff304 = just (W2.resp (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (trans (lem-resp-TOFF304-at-2 L) (by-flat Eq.refl)))
resp2 L Toff314 = just (W2.resp ((K ↑ • CCZ • K ↑ • iI) ↑) (trans (lem-resp-TOFF314-at-2 L) (by-flat Eq.refl)))
resp2 L Toff401 = just (W2.resp (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) (trans (lem-resp-TOFF401-at-2 L) (by-flat Eq.refl)))
resp2 L Toff403 = just (W2.resp (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) (trans (lem-resp-TOFF403-at-2 L) (by-flat Eq.refl)))
resp2 L Toff413 = just (W2.resp (Toffᵗ ↑) (trans (lem-resp-TOFF413-at-2 L) (by-flat Eq.refl)))
resp2 L g = Maybe.map W2.fromLit (lit2 g)

pw2 : (c4 : Complete 4) (L : WsL) → _
pw2 c4 L = W2.pwin (resp2 L) c4

resp3 : WsL → (g : Mac) → Maybe (W3.Resp g)
resp3 L CCZ014 = just (W3.resp (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (trans (lem-resp-CCZ014-at-3 L) (by-flat Eq.refl)))
resp3 L CCZ024 = just (W3.resp (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (trans (lem-resp-CCZ024-at-3 L) (by-flat Eq.refl)))
resp3 L CCZ124 = just (W3.resp (CCZ ↑) (trans (lem-resp-CCZ124-at-3 L) (by-flat Eq.refl)))
resp3 L CK40 = just (W3.resp (Swap ↑ ↑ • (Swap ↑ • CK₁₀ • Swap ↑) • Swap ↑ ↑) (trans (lem-resp-CK40-at-3 L) (by-flat Eq.refl)))
resp3 L CK41 = just (W3.resp (Swap ↑ ↑ • (CK₁₀ ↑) • Swap ↑ ↑) (trans (lem-resp-CK41-at-3 L) (by-flat Eq.refl)))
resp3 L CK42 = just (W3.resp (CK₁₀ ↑ ↑) (trans (lem-resp-CK42-at-3 L) (by-flat Eq.refl)))
resp3 L CS04 = just (W3.resp (Swap ↑ ↑ • (Swap ↑ • CS • Swap ↑) • Swap ↑ ↑) (trans (lem-resp-CS04-at-3 L) (by-flat Eq.refl)))
resp3 L CS04⁻ = just (W3.resp (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (trans (lem-resp-CSd04-at-3 L) (by-flat Eq.refl)))
resp3 L CS14 = just (W3.resp (Swap ↑ ↑ • (CS ↑) • Swap ↑ ↑) (trans (lem-resp-CS14-at-3 L) (by-flat Eq.refl)))
resp3 L CS14⁻ = just (W3.resp (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑) (trans (lem-resp-CSd14-at-3 L) (by-flat Eq.refl)))
resp3 L CS24 = just (W3.resp (CS ↑ ↑) (trans (lem-resp-CS24-at-3 L) (by-flat Eq.refl)))
resp3 L CS24⁻ = just (W3.resp ((CS • CS • CS) ↑ ↑) (trans (lem-resp-CSd24-at-3 L) (by-flat Eq.refl)))
resp3 L CX04 = just (W3.resp (Swap ↑ ↑ • (Swap ↑ • CX₀₁ • Swap ↑) • Swap ↑ ↑) (trans (lem-resp-CX04-at-3 L) (by-flat Eq.refl)))
resp3 L CX14 = just (W3.resp (Swap ↑ ↑ • (CX₀₁ ↑) • Swap ↑ ↑) (trans (lem-resp-CX14-at-3 L) (by-flat Eq.refl)))
resp3 L CX24 = just (W3.resp (CX₀₁ ↑ ↑) (trans (lem-resp-CX24-at-3 L) (by-flat Eq.refl)))
resp3 L CX40 = just (W3.resp (Swap ↑ ↑ • (Swap ↑ • CX₁₀ • Swap ↑) • Swap ↑ ↑) (trans (lem-resp-CX40-at-3 L) (by-flat Eq.refl)))
resp3 L CX41 = just (W3.resp (Swap ↑ ↑ • (CX₁₀ ↑) • Swap ↑ ↑) (trans (lem-resp-CX41-at-3 L) (by-flat Eq.refl)))
resp3 L CX42 = just (W3.resp (CX₁₀ ↑ ↑) (trans (lem-resp-CX42-at-3 L) (by-flat Eq.refl)))
resp3 L CZ04 = just (W3.resp (Swap ↑ ↑ • (Swap ↑ • CZ • Swap ↑) • Swap ↑ ↑) (trans (lem-resp-CZ04-at-3 L) (by-flat Eq.refl)))
resp3 L CZ14 = just (W3.resp (Swap ↑ ↑ • (CZ ↑) • Swap ↑ ↑) (trans (lem-resp-CZ14-at-3 L) (by-flat Eq.refl)))
resp3 L CZ24 = just (W3.resp (CZ ↑ ↑) (trans (lem-resp-CZ24-at-3 L) (by-flat Eq.refl)))
resp3 L Sw14 = just (W3.resp (Swap ↑ ↑ • (Swap ↑) • Swap ↑ ↑) (trans (lem-resp-SWAP14-at-3 L) (by-flat Eq.refl)))
resp3 L Sw24 = just (W3.resp (Swap ↑ ↑) (trans (lem-resp-SWAP24-at-3 L) (by-flat Eq.refl)))
resp3 L Toff014 = just (W3.resp (Swap ↑ ↑ • Toff • Swap ↑ ↑) (trans (lem-resp-TOFF014-at-3 L) (by-flat Eq.refl)))
resp3 L Toff024 = just (W3.resp (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (trans (lem-resp-TOFF024-at-3 L) (by-flat Eq.refl)))
resp3 L Toff104 = just (W3.resp (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) (trans (lem-resp-TOFF104-at-3 L) (by-flat Eq.refl)))
resp3 L Toff124 = just (W3.resp (Toff ↑) (trans (lem-resp-TOFF124-at-3 L) (by-flat Eq.refl)))
resp3 L Toff204 = just (W3.resp (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (trans (lem-resp-TOFF204-at-3 L) (by-flat Eq.refl)))
resp3 L Toff214 = just (W3.resp ((K ↑ • CCZ • K ↑ • iI) ↑) (trans (lem-resp-TOFF214-at-3 L) (by-flat Eq.refl)))
resp3 L Toff401 = just (W3.resp (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) (trans (lem-resp-TOFF401-at-3 L) (by-flat Eq.refl)))
resp3 L Toff402 = just (W3.resp (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) (trans (lem-resp-TOFF402-at-3 L) (by-flat Eq.refl)))
resp3 L Toff412 = just (W3.resp (Toffᵗ ↑) (trans (lem-resp-TOFF412-at-3 L) (by-flat Eq.refl)))
resp3 L g = Maybe.map W3.fromLit (lit3 g)

pw3 : (c4 : Complete 4) (L : WsL) → _
pw3 c4 L = W3.pwin (resp3 L) c4

resp4 : WsL → (g : Mac) → Maybe (W4.Resp g)
resp4 L g = Maybe.map W4.fromLit (lit4 g)

pw4 : (c4 : Complete 4) (L : WsL) → _
pw4 c4 L = W4.pwin (resp4 L) c4
