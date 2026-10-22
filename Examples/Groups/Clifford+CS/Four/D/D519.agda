{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD519 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D519 (W : Ws) (Sᴰ : SD519) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.LowComm using (low-comm ; low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Four.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

-- The lemmas of other derivation modules (DSig).
private
  lem-AXIOM-LF-at0312 : St 180
  lem-AXIOM-LF-at0312 = pickᴰ 0 Sᴰ
  lem-AXIOM-LF-at1302-part0 : St 181
  lem-AXIOM-LF-at1302-part0 = pickᴰ 1 Sᴰ
  lem-AXIOM-LF-at1302-part1 : St 182
  lem-AXIOM-LF-at1302-part1 = pickᴰ 2 Sᴰ
  lem-AXIOM-LF-at1302-part2 : St 183
  lem-AXIOM-LF-at1302-part2 = pickᴰ 3 Sᴰ
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part0 : St 184
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part0 = pickᴰ 4 Sᴰ
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part1 : St 185
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part1 = pickᴰ 5 Sᴰ
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part2 : St 186
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part2 = pickᴰ 6 Sᴰ
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part3 : St 187
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part3 = pickᴰ 7 Sᴰ
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part4 : St 188
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part4 = pickᴰ 8 Sᴰ
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part5 : St 189
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part5 = pickᴰ 9 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK31-X3 : St 190
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK31-X3 = pickᴰ 10 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CKd31-X3 : St 191
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CKd31-X3 = pickᴰ 11 Sᴰ
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~31-⟶0⟩-part0 : St 192
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~31-⟶0⟩-part0 = pickᴰ 12 Sᴰ
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~31-⟶0⟩-part1 : St 193
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~31-⟶0⟩-part1 = pickᴰ 13 Sᴰ
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~31-⟶0⟩-part2 : St 194
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~31-⟶0⟩-part2 = pickᴰ 14 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF203-X3 : St 195
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF203-X3 = pickᴰ 15 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS13-X3 : St 196
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS13-X3 = pickᴰ 16 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-CK21 : St 197
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-CK21 = pickᴰ 17 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CSd13-X3 : St 198
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CSd13-X3 = pickᴰ 18 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-CKd21 : St 199
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-CKd21 = pickᴰ 19 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS12 : St 200
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS12 = pickᴰ 20 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-CSd12 : St 201
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-CSd12 = pickᴰ 21 Sᴰ
  lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶1⟩-passes-white-iX-via-V2-conjugates-2-part0 : St 202
  lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶1⟩-passes-white-iX-via-V2-conjugates-2-part0 = pickᴰ 22 Sᴰ
  lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶1⟩-passes-white-iX-via-V2-conjugates-2-part1 : St 203
  lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶1⟩-passes-white-iX-via-V2-conjugates-2-part1 = pickᴰ 23 Sᴰ
  lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶1⟩-passes-white-iX-via-V2-conjugates-2-part2 : St 204
  lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶1⟩-passes-white-iX-via-V2-conjugates-2-part2 = pickᴰ 24 Sᴰ
  lem-comm-CCZ023-CZ12 : St 205
  lem-comm-CCZ023-CZ12 = pickᴰ 25 Sᴰ

private
  q1 : Eqn
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 3 W
  q3 : Eqn
  q3 = wE 464 W
  q4 : Eqn
  q4 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q5 : Eqn
  q5 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q6 : Eqn
  q6 = wE 1203 W
  q7 : Eqn
  q7 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q8 : Eqn
  q8 = wE 1204 W
  q9 : Eqn
  q9 = wE 151 W
  q10 : Eqn
  q10 = sE 180 lem-AXIOM-LF-at0312

-- LF CS01 CS01 CK10 CS01 CX13 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK20 CS03 CS03 CS03 S3 CK30 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 S3 S3 S3 S3 CK30 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS01 CS01 CS01 S1 CK10 CS01 CS01 CS01 CS01 CS01 CS01 S2 CK20 at 3: 235 steps
lem-LF-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK20-CS03-CS03-CS03-S3-CK30-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-S3-CK30-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS01-CS01-CS01-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-S2-CK20-at-3 : ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK20 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ Toff213 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ Toff213 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-LF-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK20-CS03-CS03-CS03-S3-CK30-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-S3-CK30-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS01-CS01-CS01-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-S2-CK20-at-3 = derive (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK20 ∷ []) (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ Toff213 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ Toff213 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  (rw 21 q1 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q2 ∷
   re 19 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 21 q2 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q2 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q2 ∷
   re 16 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 18 q2 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q2 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q2 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q2 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q2 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q2 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q2 ∷
   rw 9 q3 ∷
   re 8 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 10 q2 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q2 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q2 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q2 ∷
   re 4 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 6 q2 ∷
   rw 3 q4 ∷
   rw 2 q5 ∷
   rw 1 q4 ∷
   rw 0 q4 ∷
   rw 1 q6 ∷
   rw 2 q1 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 3 q1 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 4 q1 ∷
   re 2 3 (CK30 ∷ []) ∷
   rw 5 q1 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 6 q1 ∷
   re 4 3 (CX31 ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw⁻ 6 q4 ∷
   rw⁻ 7 q4 ∷
   rw⁻ 8 q5 ∷
   rw⁻ 9 q7 ∷
   rw⁻ 10 q4 ∷
   rw⁻ 11 q4 ∷
   rw⁻ 12 q4 ∷
   rw⁻ 13 q4 ∷
   rw⁻ 14 q4 ∷
   rw⁻ 15 q4 ∷
   rw 18 q1 ∷
   re 16 3 (CX31 ∷ []) ∷
   rw⁻ 17 q4 ∷
   rw⁻ 18 q4 ∷
   rw⁻ 19 q5 ∷
   rw⁻ 20 q4 ∷
   rw 21 q2 ∷
   rw 78 q1 ∷
   rw 77 q4 ∷
   rw 76 q4 ∷
   rw 75 q4 ∷
   rw 74 q4 ∷
   rw 73 q4 ∷
   rw 72 q4 ∷
   rw 71 q5 ∷
   rw 70 q7 ∷
   rw 69 q4 ∷
   rw 68 q4 ∷
   rw 67 q4 ∷
   re 66 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 68 q2 ∷
   re 65 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 67 q2 ∷
   re 64 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 66 q2 ∷
   re 63 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 65 q2 ∷
   re 62 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 64 q2 ∷
   re 61 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 63 q2 ∷
   re 60 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 62 q2 ∷
   re 59 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 61 q2 ∷
   re 58 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 60 q2 ∷
   re 57 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 59 q2 ∷
   re 56 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 58 q2 ∷
   rw 55 q3 ∷
   rw 54 q3 ∷
   rw 53 q3 ∷
   rw 52 q3 ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 53 q2 ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 52 q2 ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 51 q2 ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 50 q2 ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 49 q2 ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 48 q2 ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 47 q2 ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 46 q2 ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 45 q2 ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 44 q2 ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 43 q2 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 42 q2 ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 41 q2 ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 40 q2 ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 39 q2 ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 38 q2 ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 37 q2 ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 36 q2 ∷
   re 33 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 35 q2 ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 34 q2 ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 33 q2 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 32 q2 ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q2 ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 30 q2 ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q2 ∷
   re 26 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 28 q2 ∷
   rw 25 q3 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q2 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q2 ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q2 ∷
   rw 23 q8 ∷
   rw⁻ 22 q4 ∷
   rw⁻ 23 q4 ∷
   rw⁻ 24 q4 ∷
   rw⁻ 25 q7 ∷
   rw⁻ 26 q5 ∷
   rw⁻ 27 q4 ∷
   rw⁻ 28 q4 ∷
   rw⁻ 29 q4 ∷
   rw⁻ 30 q4 ∷
   rw⁻ 31 q4 ∷
   rw⁻ 32 q4 ∷
   rw 35 q1 ∷
   re 33 3 (CX31 ∷ []) ∷
   rw⁻ 34 q4 ∷
   rw⁻ 35 q4 ∷
   rw⁻ 36 q4 ∷
   rw⁻ 37 q4 ∷
   rw⁻ 38 q4 ∷
   rw⁻ 39 q4 ∷
   rw⁻ 40 q4 ∷
   rw⁻ 41 q4 ∷
   rw⁻ 42 q4 ∷
   rw⁻ 43 q4 ∷
   rw⁻ 44 q4 ∷
   rw⁻ 45 q4 ∷
   rw⁻ 46 q4 ∷
   rw⁻ 47 q4 ∷
   rw⁻ 48 q4 ∷
   rw⁻ 49 q4 ∷
   rw⁻ 50 q4 ∷
   rw⁻ 51 q4 ∷
   rw⁻ 52 q7 ∷
   rw⁻ 53 q7 ∷
   rw⁻ 54 q7 ∷
   rw⁻ 55 q7 ∷
   rw⁻ 56 q5 ∷
   rw⁻ 57 q4 ∷
   rw⁻ 58 q4 ∷
   rw⁻ 59 q4 ∷
   rw⁻ 60 q4 ∷
   rw⁻ 61 q4 ∷
   rw⁻ 62 q4 ∷
   rw⁻ 63 q4 ∷
   rw⁻ 64 q4 ∷
   rw⁻ 65 q4 ∷
   rw 68 q1 ∷
   re 66 3 (CX31 ∷ []) ∷
   rw 69 q1 ∷
   re 67 3 (CS03 ∷ []) ∷
   rw 70 q1 ∷
   re 68 3 (CS03 ∷ []) ∷
   rw 71 q1 ∷
   re 69 3 (CS03 ∷ []) ∷
   rw 70 q9 ∷
   rw 73 q1 ∷
   re 71 3 (CK30 ∷ []) ∷
   rw 74 q1 ∷
   re 72 3 (CS03 ∷ []) ∷
   rw 75 q1 ∷
   re 73 3 (CS03 ∷ []) ∷
   rw 76 q1 ∷
   re 74 3 (CS03 ∷ []) ∷
   rw 77 q1 ∷
   re 75 3 (CS03 ∷ []) ∷
   rw 78 q1 ∷
   re 76 3 (CS03 ∷ []) ∷
   rw 79 q1 ∷
   re 77 3 (CS03 ∷ []) ∷
   rw 78 q2 ∷
   rw 0 q10 ∷ []) Eq.refl

private
  q11 : Eqn
  q11 = sE 181 lem-AXIOM-LF-at1302-part0
  q12 : Eqn
  q12 = sE 182 lem-AXIOM-LF-at1302-part1
  q13 : Eqn
  q13 = sE 183 lem-AXIOM-LF-at1302-part2

-- AXIOM LF @1302: 3 steps
lem-AXIOM-LF-at1302 : ⟪ (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S2 ∷ CK21 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ Toff203 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ Toff203 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) ⟫ʷ
lem-AXIOM-LF-at1302 = derive (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S2 ∷ CK21 ∷ []) (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ Toff203 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ Toff203 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ [])
  (rw 0 q11 ∷
   rw 0 q12 ∷
   rw 0 q13 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = sE 184 lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part0
  q15 : Eqn
  q15 = sE 185 lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part1
  q16 : Eqn
  q16 = sE 186 lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part2
  q17 : Eqn
  q17 = sE 187 lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part3
  q18 : Eqn
  q18 = sE 188 lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part4
  q19 : Eqn
  q19 = sE 189 lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1-part5

-- Bar(SSKSKK;3,2->0) passes white iX via V2 conjugates 1: 6 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-white-iX-via-V2-conjugates-1 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ []) (X3 ∷ CS13⁻ ∷ X3 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS01⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ S1⁻ ∷ CK10⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  (rw 0 q14 ∷
   rw 0 q15 ∷
   rw 0 q16 ∷
   rw 0 q17 ∷
   rw 0 q18 ∷
   rw 0 q19 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = sE 192 lem-Bar⟨SSKSKK32-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~31-⟶0⟩-part0
  q21 : Eqn
  q21 = sE 193 lem-Bar⟨SSKSKK32-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~31-⟶0⟩-part1
  q22 : Eqn
  q22 = sE 194 lem-Bar⟨SSKSKK32-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~31-⟶0⟩-part2

-- Bar(SSKSKK;3,2->0) passes groups of WBar(SSKSKK;~3,1->0): 3 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~31-⟶0⟩ : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X3 ∷ X3 ∷ CX31 ∷ X3 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X3 ∷ CX31 ∷ X3 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X3 ∷ X3 ∷ CX31 ∷ X3 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X3 ∷ CX31 ∷ X3 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~31-⟶0⟩ = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X3 ∷ X3 ∷ CX31 ∷ X3 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X3 ∷ CX31 ∷ X3 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X3 ∷ X3 ∷ CX31 ∷ X3 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X3 ∷ CX31 ∷ X3 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  (rw 0 q20 ∷
   rw 0 q21 ∷
   rw 0 q22 ∷ []) Eq.refl

private
  q23 : Eqn
  q23 = sE 195 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF203-X3

-- Bar(SSKSKK;3,2->0) passes factors of X3 TOFF203 X3: 1 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-factors-of-X3-TOFF203-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ Toff203 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff203 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-factors-of-X3-TOFF203-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ Toff203 ∷ X3 ∷ []) (X3 ∷ Toff203 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  (rw 0 q23 ∷ []) Eq.refl

private
  q24 : Eqn
  q24 = sE 196 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS13-X3
  q25 : Eqn
  q25 = sE 197 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-CK21
  q26 : Eqn
  q26 = sE 198 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CSd13-X3
  q27 : Eqn
  q27 = sE 199 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-CKd21

-- Bar(SSKSKK;3,2->0) passes comm WBar(SSSKSS;~3,2->1): 4 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-comm-WBar⟨SSSKSS~32-⟶1⟩ : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CS13 ∷ X3 ∷ CK21 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ CK21⁻ ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ X3 ∷ CK21 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ CK21⁻ ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-comm-WBar⟨SSSKSS~32-⟶1⟩ = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CS13 ∷ X3 ∷ CK21 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ CK21⁻ ∷ []) (X3 ∷ CS13 ∷ X3 ∷ CK21 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ CK21⁻ ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  (rw 0 q24 ∷
   rw 3 q25 ∷
   rw 4 q26 ∷
   rw 7 q27 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = sE 190 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK31-X3
  q29 : Eqn
  q29 = sE 200 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS12
  q30 : Eqn
  q30 = sE 191 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CKd31-X3
  q31 : Eqn
  q31 = sE 201 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-CSd12

-- Bar(SSKSKK;3,2->0) passes comm WBar(SSKSKK;~3,2->1): 4 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-comm-WBar⟨SSKSKK~32-⟶1⟩ : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CK31 ∷ X3 ∷ CS12 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK31 ∷ X3 ∷ CS12 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ CS12⁻ ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-comm-WBar⟨SSKSKK~32-⟶1⟩ = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CK31 ∷ X3 ∷ CS12 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ CS12⁻ ∷ []) (X3 ∷ CK31 ∷ X3 ∷ CS12 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ CS12⁻ ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  (rw 0 q28 ∷
   rw 3 q29 ∷
   rw 4 q30 ∷
   rw 7 q31 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = sE 202 lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶1⟩-passes-white-iX-via-V2-conjugates-2-part0
  q33 : Eqn
  q33 = sE 203 lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶1⟩-passes-white-iX-via-V2-conjugates-2-part1
  q34 : Eqn
  q34 = sE 204 lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶1⟩-passes-white-iX-via-V2-conjugates-2-part2

-- Bar(['S', 'S', 'K', 'S', 'K', 'K'];3,0->1) passes white iX via V2 conjugates 2: 3 steps
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶1⟩-passes-white-iX-via-V2-conjugates-2 : ⟪ (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ []) ⟫ʷ
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶1⟩-passes-white-iX-via-V2-conjugates-2 = derive (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ CS23⁻ ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ [])
  (rw 0 q32 ∷
   rw 0 q33 ∷
   rw 0 q34 ∷ []) Eq.refl

private
  q35 : Eqn
  q35 = sE 205 lem-comm-CCZ023-CZ12

-- pass [CCZ023] [CZ12]: 1 steps
lem-pass-CCZ023-vs-CZ12 : ⟪ (CCZ023 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ CCZ023 ∷ []) ⟫ʷ
lem-pass-CCZ023-vs-CZ12 = derive (CCZ023 ∷ CZ12 ∷ []) (CZ12 ∷ CCZ023 ∷ [])
  (rw 0 q35 ∷ []) Eq.refl
