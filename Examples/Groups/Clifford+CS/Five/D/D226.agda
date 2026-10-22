{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD226 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D226 (Sᴰ : SD226) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

-- The lemmas of other derivation modules (DSig).
private
  lem-comm-CCZ013-CS24 : Ws → St 2050
  lem-comm-CCZ013-CS24 = pickᴰ 0 Sᴰ
  lem-comm-CCZ013-CSd24 : Ws → St 2320
  lem-comm-CCZ013-CSd24 = pickᴰ 1 Sᴰ
  lem-comm-CCZ014-CS23 : Ws → St 1548
  lem-comm-CCZ014-CS23 = pickᴰ 2 Sᴰ
  lem-comm-CCZ014-CSd23 : Ws → St 1549
  lem-comm-CCZ014-CSd23 = pickᴰ 3 Sᴰ
  lem-comm-TOFF214-CX03 : Ws → St 2321
  lem-comm-TOFF214-CX03 = pickᴰ 4 Sᴰ
  lem-comm-CCZ023-CX14 : Ws → St 1385
  lem-comm-CCZ023-CX14 = pickᴰ 5 Sᴰ
  lem-comm-TOFF023-CX14 : Ws → St 1060
  lem-comm-TOFF023-CX14 = pickᴰ 6 Sᴰ
  lem-box-perm-2134-at03102132 : Ws → St 136
  lem-box-perm-2134-at03102132 = pickᴰ 7 Sᴰ
  lem-box-perm-2134-at021021 : Ws → St 2322
  lem-box-perm-2134-at021021 = pickᴰ 8 Sᴰ
  lem-box-perm-2134-at0220 : Ws → St 2323
  lem-box-perm-2134-at0220 = pickᴰ 9 Sᴰ
  lem-box-perm-2134-at032032 : Ws → St 2324
  lem-box-perm-2134-at032032 = pickᴰ 10 Sᴰ
  lem-CK-box-at033440 : Ws → St 2237
  lem-CK-box-at033440 = pickᴰ 11 Sᴰ
  lem-box-cP-at032032 : Ws → St 868
  lem-box-cP-at032032 = pickᴰ 12 Sᴰ
  lem-box-cP-at02102331 : Ws → St 2325
  lem-box-cP-at02102331 = pickᴰ 13 Sᴰ
  lem-box-cP-at142142 : Ws → St 1167
  lem-box-cP-at142142 = pickᴰ 14 Sᴰ
  lem-box-perm-1324-at021021 : Ws → St 2326
  lem-box-perm-1324-at021021 = pickᴰ 15 Sᴰ
  lem-box-perm-3124-at021021 : Ws → St 2327
  lem-box-perm-3124-at021021 = pickᴰ 16 Sᴰ
  lem-box-perm-3214-at032032 : Ws → St 2328
  lem-box-perm-3214-at032032 = pickᴰ 17 Sᴰ
  lem-box2-at032032 : Ws → St 2329
  lem-box2-at032032 = pickᴰ 18 Sᴰ
  lem-box-perm-2314-at02132031 : Ws → St 2330
  lem-box-perm-2314-at02132031 = pickᴰ 19 Sᴰ
  lem-box-perm-2431-at142142 : Ws → St 2331
  lem-box-perm-2431-at142142 = pickᴰ 20 Sᴰ
  lem-box-perm-3214-at03122031 : Ws → St 2332
  lem-box-perm-3214-at03122031 = pickᴰ 21 Sᴰ
  lem-box2-at033440 : Ws → St 2333
  lem-box2-at033440 = pickᴰ 22 Sᴰ
  lem-box2-at142142 : Ws → St 2334
  lem-box2-at142142 = pickᴰ 23 Sᴰ
  lem-box-box-3-at021021 : Ws → St 2244
  lem-box-box-3-at021021 = pickᴰ 24 Sᴰ
  lem-box-perm-2341-at0314213042 : Ws → St 2335
  lem-box-perm-2341-at0314213042 = pickᴰ 25 Sᴰ
  lem-box-perm-3241-at142142 : Ws → St 2336
  lem-box-perm-3241-at142142 = pickᴰ 26 Sᴰ
  lem-box-perm-4123-at032032 : Ws → St 2337
  lem-box-perm-4123-at032032 = pickᴰ 27 Sᴰ
  lem-box-perm-4213-at132132 : Ws → St 2338
  lem-box-perm-4213-at132132 = pickᴰ 28 Sᴰ
  lem-box-box-1-at03102132 : Ws → St 1729
  lem-box-box-1-at03102132 = pickᴰ 29 Sᴰ
  lem-box-box-3-at03102132 : Ws → St 2252
  lem-box-box-3-at03102132 = pickᴰ 30 Sᴰ
  lem-Tu-box-at0220 : Ws → St 2339
  lem-Tu-box-at0220 = pickᴰ 31 Sᴰ
  lem-Tu-box-at0314213042 : Ws → St 2340
  lem-Tu-box-at0314213042 = pickᴰ 32 Sᴰ
  lem-L-CCZ013-0 : Ws → St 2317
  lem-L-CCZ013-0 = pickᴰ 33 Sᴰ
  lem-L-Toff-0 : Ws → St 2341
  lem-L-Toff-0 = pickᴰ 34 Sᴰ
  lem-nf-toff-cczat0 : Ws → St 2342
  lem-nf-toff-cczat0 = pickᴰ 35 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 2341 (lem-L-Toff-0 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 2317 (lem-L-CCZ013-0 c4)
  q3 : Ws → Eqn
  q3 c4 = wlE 489 (lit c4)
  q4 : Ws → Eqn
  q4 c4 = sE 2322 (lem-box-perm-2134-at021021 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 2339 (lem-Tu-box-at0220 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 2323 (lem-box-perm-2134-at0220 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 2328 (lem-box-perm-3214-at032032 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 2244 (lem-box-box-3-at021021 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 2332 (lem-box-perm-3214-at03122031 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 2326 (lem-box-perm-1324-at021021 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 2325 (lem-box-cP-at02102331 c4)
  q12 : Ws → Eqn
  q12 c4 = wpE 1253 c4
  q13 : Ws → Eqn
  q13 c4 = eqn (K0 ∷ Toff214 ∷ []) (Toff214 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑))
  q14 : Ws → Eqn
  q14 c4 = wlE 761 (lit c4)
  q15 : Ws → Eqn
  q15 c4 = sE 2321 (lem-comm-TOFF214-CX03 c4)
  q16 : Ws → Eqn
  q16 c4 = wlE 1404 (lit c4)
  q17 : Ws → Eqn
  q17 c4 = wpE 683 c4
  q18 : Ws → Eqn
  q18 c4 = eqn (K0⁻ ∷ Toff214 ∷ []) (Toff214 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑))
  q19 : Ws → Eqn
  q19 c4 = wpE 1254 c4
  q20 : Ws → Eqn
  q20 c4 = wlE 1344 (lit c4)
  q21 : Ws → Eqn
  q21 c4 = wlE 698 (lit c4)
  q22 : Ws → Eqn
  q22 c4 = wpE 543 c4
  q23 : Ws → Eqn
  q23 c4 = sE 1385 (lem-comm-CCZ023-CX14 c4)
  q24 : Ws → Eqn
  q24 c4 = wpE 574 c4
  q25 : Ws → Eqn
  q25 c4 = wlE 670 (lit c4)
  q26 : Ws → Eqn
  q26 c4 = wpE 550 c4
  q27 : Ws → Eqn
  q27 c4 = wlE 1405 (lit c4)
  q28 : Ws → Eqn
  q28 c4 = wpE 6 c4
  q29 : Ws → Eqn
  q29 c4 = sE 2337 (lem-box-perm-4123-at032032 c4)
  q30 : Ws → Eqn
  q30 c4 = sE 2340 (lem-Tu-box-at0314213042 c4)
  q31 : Ws → Eqn
  q31 c4 = sE 2335 (lem-box-perm-2341-at0314213042 c4)
  q32 : Ws → Eqn
  q32 c4 = sE 2324 (lem-box-perm-2134-at032032 c4)
  q33 : Ws → Eqn
  q33 c4 = sE 2336 (lem-box-perm-3241-at142142 c4)
  q34 : Ws → Eqn
  q34 c4 = sE 1729 (lem-box-box-1-at03102132 c4)
  q35 : Ws → Eqn
  q35 c4 = sE 2338 (lem-box-perm-4213-at132132 c4)
  q36 : Ws → Eqn
  q36 c4 = sE 136 (lem-box-perm-2134-at03102132 c4)
  q37 : Ws → Eqn
  q37 c4 = sE 868 (lem-box-cP-at032032 c4)
  q38 : Ws → Eqn
  q38 c4 = wlE 1406 (lit c4)
  q39 : Ws → Eqn
  q39 c4 = wlE 256 (lit c4)
  q40 : Ws → Eqn
  q40 c4 = sE 2050 (lem-comm-CCZ013-CS24 c4)
  q41 : Ws → Eqn
  q41 c4 = wlE 448 (lit c4)
  q42 : Ws → Eqn
  q42 c4 = sE 2320 (lem-comm-CCZ013-CSd24 c4)
  q43 : Ws → Eqn
  q43 c4 = wpE 299 c4
  q44 : Ws → Eqn
  q44 c4 = wpE 593 c4
  q45 : Ws → Eqn
  q45 c4 = wlE 1206 (lit c4)
  q46 : Ws → Eqn
  q46 c4 = sE 2327 (lem-box-perm-3124-at021021 c4)
  q47 : Ws → Eqn
  q47 c4 = sE 2252 (lem-box-box-3-at03102132 c4)
  q48 : Ws → Eqn
  q48 c4 = sE 2330 (lem-box-perm-2314-at02132031 c4)
  q49 : Ws → Eqn
  q49 c4 = sE 1167 (lem-box-cP-at142142 c4)
  q50 : Ws → Eqn
  q50 c4 = wpE 725 c4
  q51 : Ws → Eqn
  q51 c4 = sE 1060 (lem-comm-TOFF023-CX14 c4)
  q52 : Ws → Eqn
  q52 c4 = wpE 823 c4
  q53 : Ws → Eqn
  q53 c4 = wlE 222 (lit c4)
  q54 : Ws → Eqn
  q54 c4 = wpE 272 c4
  q55 : Ws → Eqn
  q55 c4 = wlE 852 (lit c4)
  q56 : Ws → Eqn
  q56 c4 = wlE 498 (lit c4)
  q57 : Ws → Eqn
  q57 c4 = wlE 348 (lit c4)
  q58 : Ws → Eqn
  q58 c4 = wlE 214 (lit c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (CX01 ∷ Toff324 ∷ []) (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI))
  q60 : Ws → Eqn
  q60 c4 = wlE 447 (lit c4)
  q61 : Ws → Eqn
  q61 c4 = wpE 298 c4
  q62 : Ws → Eqn
  q62 c4 = wlE 850 (lit c4)
  q63 : Ws → Eqn
  q63 c4 = sE 2329 (lem-box2-at032032 c4)
  q64 : Ws → Eqn
  q64 c4 = sE 2334 (lem-box2-at142142 c4)
  q65 : Ws → Eqn
  q65 c4 = wlE 1407 (lit c4)
  q66 : Ws → Eqn
  q66 c4 = wpE 1255 c4
  q67 : Ws → Eqn
  q67 c4 = wlE 514 (lit c4)
  q68 : Ws → Eqn
  q68 c4 = wpE 65 c4
  q69 : Ws → Eqn
  q69 c4 = sE 1548 (lem-comm-CCZ014-CS23 c4)
  q70 : Ws → Eqn
  q70 c4 = wpE 54 c4
  q71 : Ws → Eqn
  q71 c4 = sE 1549 (lem-comm-CCZ014-CSd23 c4)
  q72 : Ws → Eqn
  q72 c4 = wpE 53 c4
  q73 : Ws → Eqn
  q73 c4 = wpE 61 c4
  q74 : Ws → Eqn
  q74 c4 = wlE 275 (lit c4)
  q75 : Ws → Eqn
  q75 c4 = wlE 220 (lit c4)
  q76 : Ws → Eqn
  q76 c4 = wpE 70 c4
  q77 : Ws → Eqn
  q77 c4 = wpE 69 c4
  q78 : Ws → Eqn
  q78 c4 = wlE 221 (lit c4)
  q79 : Ws → Eqn
  q79 c4 = wpE 1256 c4
  q80 : Ws → Eqn
  q80 c4 = wpE 66 c4
  q81 : Ws → Eqn
  q81 c4 = wpE 173 c4
  q82 : Ws → Eqn
  q82 c4 = wpE 1209 c4
  q83 : Ws → Eqn
  q83 c4 = wpE 268 c4
  q84 : Ws → Eqn
  q84 c4 = sE 2331 (lem-box-perm-2431-at142142 c4)
  q85 : Ws → Eqn
  q85 c4 = wlE 1408 (lit c4)
  q86 : Ws → Eqn
  q86 c4 = wpE 1257 c4
  q87 : Ws → Eqn
  q87 c4 = sE 2237 (lem-CK-box-at033440 c4)
  q88 : Ws → Eqn
  q88 c4 = wpE 1258 c4
  q89 : Ws → Eqn
  q89 c4 = sE 2333 (lem-box2-at033440 c4)
  q90 : Ws → Eqn
  q90 c4 = wpE 1217 c4
  q91 : Ws → Eqn
  q91 c4 = wlE 1112 (lit c4)
  q92 : Ws → Eqn
  q92 c4 = sE 2342 (lem-nf-toff-cczat0 c4)

-- F1-toff-ccz@0: 310 steps
lem-F1-toff-cczat0 : Ws → ⟪ (CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ
lem-F1-toff-cczat0 c4 = derive (CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK40 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK40 ∷ S4 ∷ []) (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ [])
  (rw 0 (q1 c4) ∷
   rw 4 (q2 c4) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   rw 6 (q4 c4) ∷
   rw 5 (q5 c4) ∷
   rw 5 (q6 c4) ∷
   rw 6 (q7 c4) ∷
   rw 5 (q8 c4) ∷
   rw 5 (q9 c4) ∷
   rw 6 (q10 c4) ∷
   rw 6 (q11 c4) ∷
   rw⁻ 10 (q12 c4) ∷
   rw⁻ 9 (q13 c4) ∷
   rw⁻ 10 (q14 c4) ∷
   rw 11 (q15 c4) ∷
   rw⁻ 12 (q16 c4) ∷
   rw 13 (q15 c4) ∷
   rw⁻ 14 (q17 c4) ∷
   rw⁻ 15 (q18 c4) ∷
   rw 9 (q12 c4) ∷
   rw 8 (q19 c4) ∷
   rw⁻ 8 (q12 c4) ∷
   rw⁻ 7 (q13 c4) ∷
   rw⁻ 8 (q14 c4) ∷
   rw 9 (q15 c4) ∷
   rw⁻ 10 (q16 c4) ∷
   rw 11 (q15 c4) ∷
   rw⁻ 12 (q17 c4) ∷
   rw⁻ 13 (q18 c4) ∷
   rw 7 (q12 c4) ∷
   rw⁻ 8 (q20 c4) ∷
   rw 6 (q19 c4) ∷
   rw 9 (q21 c4) ∷
   rw 8 (q22 c4) ∷
   rw 9 (q23 c4) ∷
   rw 10 (q24 c4) ∷
   rw 11 (q23 c4) ∷
   rw 12 (q25 c4) ∷
   rw⁻ 8 (q21 c4) ∷
   rw 9 (q26 c4) ∷
   rw⁻ 7 (q27 c4) ∷
   rw⁻ 8 (q11 c4) ∷
   rw⁻ 8 (q10 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   rw 10 (q4 c4) ∷
   rw 9 (q5 c4) ∷
   rw 9 (q6 c4) ∷
   rw 10 (q7 c4) ∷
   rw 9 (q8 c4) ∷
   rw 9 (q9 c4) ∷
   rw 10 (q10 c4) ∷
   rw 10 (q11 c4) ∷
   rw⁻ 14 (q12 c4) ∷
   rw⁻ 13 (q13 c4) ∷
   rw⁻ 14 (q14 c4) ∷
   rw 15 (q15 c4) ∷
   rw⁻ 16 (q16 c4) ∷
   rw 17 (q15 c4) ∷
   rw⁻ 18 (q17 c4) ∷
   rw⁻ 19 (q18 c4) ∷
   rw 13 (q12 c4) ∷
   rw 12 (q19 c4) ∷
   rw⁻ 12 (q12 c4) ∷
   rw⁻ 11 (q13 c4) ∷
   rw⁻ 12 (q14 c4) ∷
   rw 13 (q15 c4) ∷
   rw⁻ 14 (q16 c4) ∷
   rw 15 (q15 c4) ∷
   rw⁻ 16 (q17 c4) ∷
   rw⁻ 17 (q18 c4) ∷
   rw 11 (q12 c4) ∷
   rw⁻ 12 (q20 c4) ∷
   rw 10 (q19 c4) ∷
   rw 13 (q21 c4) ∷
   rw 12 (q22 c4) ∷
   rw 13 (q23 c4) ∷
   rw 14 (q24 c4) ∷
   rw 15 (q23 c4) ∷
   rw 16 (q25 c4) ∷
   rw⁻ 12 (q21 c4) ∷
   rw 13 (q26 c4) ∷
   rw⁻ 11 (q27 c4) ∷
   rw⁻ 12 (q11 c4) ∷
   rw⁻ 12 (q10 c4) ∷
   rw⁻ 9 (q28 c4) ∷
   rw 11 (q29 c4) ∷
   rw 10 (q30 c4) ∷
   rw 10 (q31 c4) ∷
   rw 10 (q32 c4) ∷
   rw 11 (q33 c4) ∷
   rw 10 (q34 c4) ∷
   rw 10 (q35 c4) ∷
   rw 11 (q36 c4) ∷
   rw 11 (q37 c4) ∷
   rw⁻ 14 (q38 c4) ∷
   rw 14 (q39 c4) ∷
   rw 13 (q40 c4) ∷
   rw 14 (q41 c4) ∷
   rw 15 (q42 c4) ∷
   rw 16 (q41 c4) ∷
   rw 17 (q43 c4) ∷
   rw⁻ 13 (q39 c4) ∷
   rw 14 (q44 c4) ∷
   rw⁻ 12 (q45 c4) ∷
   rw 11 (q44 c4) ∷
   rw⁻ 12 (q37 c4) ∷
   rw 12 (q32 c4) ∷
   rw 13 (q46 c4) ∷
   rw 12 (q47 c4) ∷
   rw 12 (q48 c4) ∷
   rw 13 (q36 c4) ∷
   rw 10 (q49 c4) ∷
   rw 14 (q21 c4) ∷
   rw⁻ 13 (q50 c4) ∷
   rw 14 (q51 c4) ∷
   rw⁻ 15 (q52 c4) ∷
   rw 16 (q51 c4) ∷
   rw⁻ 17 (q53 c4) ∷
   rw⁻ 13 (q21 c4) ∷
   rw 12 (q54 c4) ∷
   rw 12 (q21 c4) ∷
   rw⁻ 11 (q50 c4) ∷
   rw 12 (q51 c4) ∷
   rw⁻ 13 (q52 c4) ∷
   rw 14 (q51 c4) ∷
   rw⁻ 15 (q53 c4) ∷
   rw⁻ 11 (q21 c4) ∷
   rw 10 (q54 c4) ∷
   rw⁻ 11 (q49 c4) ∷
   rw⁻ 5 (q28 c4) ∷
   rw 7 (q29 c4) ∷
   rw 6 (q30 c4) ∷
   rw 6 (q31 c4) ∷
   rw 6 (q32 c4) ∷
   rw 7 (q33 c4) ∷
   rw 6 (q34 c4) ∷
   rw 6 (q35 c4) ∷
   rw 7 (q36 c4) ∷
   rw 7 (q37 c4) ∷
   rw⁻ 10 (q38 c4) ∷
   rw 10 (q39 c4) ∷
   rw 9 (q40 c4) ∷
   rw 10 (q41 c4) ∷
   rw 11 (q42 c4) ∷
   rw 12 (q41 c4) ∷
   rw 13 (q43 c4) ∷
   rw⁻ 9 (q39 c4) ∷
   rw 10 (q44 c4) ∷
   rw⁻ 8 (q45 c4) ∷
   rw 7 (q44 c4) ∷
   rw⁻ 8 (q37 c4) ∷
   rw 8 (q37 c4) ∷
   rw⁻ 11 (q55 c4) ∷
   rw 10 (q56 c4) ∷
   rw⁻ 9 (q55 c4) ∷
   rw 11 (q57 c4) ∷
   rw⁻ 10 (q58 c4) ∷
   rw⁻ 11 (q59 c4) ∷
   rw⁻ 12 (q60 c4) ∷
   rw⁻ 13 (q59 c4) ∷
   rw⁻ 14 (q61 c4) ∷
   rw⁻ 10 (q57 c4) ∷
   rw 8 (q62 c4) ∷
   rw⁻ 9 (q37 c4) ∷
   rw⁻ 9 (q28 c4) ∷
   rw 11 (q29 c4) ∷
   rw 10 (q30 c4) ∷
   rw 10 (q31 c4) ∷
   rw 10 (q32 c4) ∷
   rw 11 (q33 c4) ∷
   rw 10 (q34 c4) ∷
   rw 10 (q35 c4) ∷
   rw 11 (q36 c4) ∷
   rw 11 (q37 c4) ∷
   rw⁻ 14 (q38 c4) ∷
   rw 14 (q39 c4) ∷
   rw 13 (q40 c4) ∷
   rw 14 (q41 c4) ∷
   rw 15 (q42 c4) ∷
   rw 16 (q41 c4) ∷
   rw 17 (q43 c4) ∷
   rw⁻ 13 (q39 c4) ∷
   rw 14 (q44 c4) ∷
   rw⁻ 12 (q45 c4) ∷
   rw 11 (q44 c4) ∷
   rw⁻ 12 (q37 c4) ∷
   rw 12 (q32 c4) ∷
   rw 13 (q33 c4) ∷
   rw 12 (q34 c4) ∷
   rw 12 (q35 c4) ∷
   rw 13 (q36 c4) ∷
   rw 13 (q32 c4) ∷
   rw 14 (q46 c4) ∷
   rw 13 (q47 c4) ∷
   rw 13 (q48 c4) ∷
   rw 14 (q36 c4) ∷
   rw 14 (q63 c4) ∷
   rw 10 (q49 c4) ∷
   rw 14 (q21 c4) ∷
   rw⁻ 13 (q50 c4) ∷
   rw 14 (q51 c4) ∷
   rw⁻ 15 (q52 c4) ∷
   rw 16 (q51 c4) ∷
   rw⁻ 17 (q53 c4) ∷
   rw⁻ 13 (q21 c4) ∷
   rw 12 (q54 c4) ∷
   rw 12 (q21 c4) ∷
   rw⁻ 11 (q50 c4) ∷
   rw 12 (q51 c4) ∷
   rw⁻ 13 (q52 c4) ∷
   rw 14 (q51 c4) ∷
   rw⁻ 15 (q53 c4) ∷
   rw⁻ 11 (q21 c4) ∷
   rw 10 (q54 c4) ∷
   rw⁻ 11 (q49 c4) ∷
   rw 11 (q64 c4) ∷
   rw 6 (q49 c4) ∷
   rw 10 (q21 c4) ∷
   rw⁻ 9 (q50 c4) ∷
   rw 10 (q51 c4) ∷
   rw⁻ 11 (q52 c4) ∷
   rw 12 (q51 c4) ∷
   rw⁻ 13 (q53 c4) ∷
   rw⁻ 9 (q21 c4) ∷
   rw 8 (q54 c4) ∷
   rw 8 (q21 c4) ∷
   rw⁻ 7 (q50 c4) ∷
   rw 8 (q51 c4) ∷
   rw⁻ 9 (q52 c4) ∷
   rw 10 (q51 c4) ∷
   rw⁻ 11 (q53 c4) ∷
   rw⁻ 7 (q21 c4) ∷
   rw 6 (q54 c4) ∷
   rw⁻ 7 (q49 c4) ∷
   rw 7 (q49 c4) ∷
   rw⁻ 10 (q65 c4) ∷
   rw 9 (q66 c4) ∷
   rw⁻ 12 (q67 c4) ∷
   rw 11 (q68 c4) ∷
   rw 12 (q69 c4) ∷
   rw 13 (q70 c4) ∷
   rw 14 (q71 c4) ∷
   rw 15 (q70 c4) ∷
   rw 16 (q72 c4) ∷
   rw 17 (q73 c4) ∷
   rw 11 (q67 c4) ∷
   rw⁻ 8 (q74 c4) ∷
   rw 10 (q75 c4) ∷
   rw⁻ 9 (q76 c4) ∷
   rw 10 (q51 c4) ∷
   rw⁻ 11 (q77 c4) ∷
   rw 12 (q51 c4) ∷
   rw⁻ 13 (q78 c4) ∷
   rw⁻ 9 (q75 c4) ∷
   rw⁻ 10 (q65 c4) ∷
   rw⁻ 8 (q79 c4) ∷
   rw 7 (q80 c4) ∷
   rw⁻ 9 (q67 c4) ∷
   rw 8 (q68 c4) ∷
   rw 9 (q69 c4) ∷
   rw 10 (q70 c4) ∷
   rw 11 (q71 c4) ∷
   rw 12 (q70 c4) ∷
   rw 13 (q72 c4) ∷
   rw 14 (q73 c4) ∷
   rw 8 (q67 c4) ∷
   rw⁻ 9 (q49 c4) ∷
   rw 9 (q49 c4) ∷
   rw 12 (q81 c4) ∷
   rw 11 (q82 c4) ∷
   rw 10 (q81 c4) ∷
   rw 12 (q21 c4) ∷
   rw⁻ 11 (q50 c4) ∷
   rw 12 (q51 c4) ∷
   rw⁻ 13 (q52 c4) ∷
   rw 14 (q51 c4) ∷
   rw⁻ 15 (q53 c4) ∷
   rw⁻ 11 (q21 c4) ∷
   rw 9 (q83 c4) ∷
   rw⁻ 10 (q49 c4) ∷
   rw 10 (q49 c4) ∷
   rw 14 (q21 c4) ∷
   rw⁻ 13 (q50 c4) ∷
   rw 14 (q51 c4) ∷
   rw⁻ 15 (q52 c4) ∷
   rw 16 (q51 c4) ∷
   rw⁻ 17 (q53 c4) ∷
   rw⁻ 13 (q21 c4) ∷
   rw 12 (q54 c4) ∷
   rw 12 (q21 c4) ∷
   rw⁻ 11 (q50 c4) ∷
   rw 12 (q51 c4) ∷
   rw⁻ 13 (q52 c4) ∷
   rw 14 (q51 c4) ∷
   rw⁻ 15 (q53 c4) ∷
   rw⁻ 11 (q21 c4) ∷
   rw 10 (q54 c4) ∷
   rw⁻ 11 (q49 c4) ∷
   rw 11 (q84 c4) ∷
   rw 6 (q85 c4) ∷
   rw 8 (q3 c4) ∷
   rw 7 (q86 c4) ∷
   rw⁻ 4 (q87 c4) ∷
   rw⁻ 0 (q87 c4) ∷
   rw 2 (q88 c4) ∷
   rw 1 (q89 c4) ∷
   rw 0 (q90 c4) ∷
   rw 0 (q91 c4) ∷
   rw⁻ 0 (q92 c4) ∷ []) Eq.refl
