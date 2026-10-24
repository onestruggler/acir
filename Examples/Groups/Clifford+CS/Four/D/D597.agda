{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD597 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D597 (W : Ws) (Sᴰ : SD597) where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.LowComm using (low-comm ; low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Four.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Four.Str using (ℓ)
open import Examples.Groups.Clifford+CS.Canonical using (can-≈)

-- The lemmas of other derivation modules (DSig).
private
  lem-pass-CCZ012-vs-CZ01 : St 886
  lem-pass-CCZ012-vs-CZ01 = pickᴰ 0 Sᴰ
  lem-pass-CS13-vs-CSd03 : St 1093
  lem-pass-CS13-vs-CSd03 = pickᴰ 1 Sᴰ
  lem-pass-CS13-vs-S0 : St 63
  lem-pass-CS13-vs-S0 = pickᴰ 2 Sᴰ
  lem-pass-CSd13-vs-CSd03 : St 1096
  lem-pass-CSd13-vs-CSd03 = pickᴰ 3 Sᴰ
  lem-pass-CSd13-vs-S0 : St 64
  lem-pass-CSd13-vs-S0 = pickᴰ 4 Sᴰ
  lem-pass-TOFF102-vs-S0 : St 1097
  lem-pass-TOFF102-vs-S0 = pickᴰ 5 Sᴰ
  lem-pass-TOFF102-vs-Sd0 : St 1098
  lem-pass-TOFF102-vs-Sd0 = pickᴰ 6 Sᴰ
  lem-pass-TOFF102-vs-X2-TOFF012-X2 : St 1099
  lem-pass-TOFF102-vs-X2-TOFF012-X2 = pickᴰ 7 Sᴰ
  lem-pass-CS12-vs-X2-TOFF102-X2 : St 1153
  lem-pass-CS12-vs-X2-TOFF102-X2 = pickᴰ 8 Sᴰ
  lem-pass-CSd12-vs-X2-TOFF102-X2 : St 1154
  lem-pass-CSd12-vs-X2-TOFF102-X2 = pickᴰ 9 Sᴰ
  lem-pass-TOFF201-vs-Sd0 : St 1155
  lem-pass-TOFF201-vs-Sd0 = pickᴰ 10 Sᴰ
  lem-pass-TOFF201-vs-Sd3 : St 1156
  lem-pass-TOFF201-vs-Sd3 = pickᴰ 11 Sᴰ
  lem-pass-TOFF201-vs-iI : St 164
  lem-pass-TOFF201-vs-iI = pickᴰ 12 Sᴰ
  lem-pass-CCZ012-vs-Z0 : St 1157
  lem-pass-CCZ012-vs-Z0 = pickᴰ 13 Sᴰ
  lem-pass-CS03-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02-part0 : St 1158
  lem-pass-CS03-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02-part0 = pickᴰ 14 Sᴰ
  lem-pass-TOFF102-vs-S3 : St 1159
  lem-pass-TOFF102-vs-S3 = pickᴰ 15 Sᴰ
  lem-pass-TOFF102-vs-Sd3 : St 1160
  lem-pass-TOFF102-vs-Sd3 = pickᴰ 16 Sᴰ
  lem-pass-TOFF102-vs-iI : St 1161
  lem-pass-TOFF102-vs-iI = pickᴰ 17 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK31-X3 : St 190
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK31-X3 = pickᴰ 18 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK30-X3 : St 1162
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK30-X3 = pickᴰ 19 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CKd30-X3 : St 1163
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CKd30-X3 = pickᴰ 20 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CKd31-X3 : St 191
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CKd31-X3 = pickᴰ 21 Sᴰ
  lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-CK32-X3 : St 1164
  lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-CK32-X3 = pickᴰ 22 Sᴰ
  lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-CK31-X3 : St 1165
  lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-CK31-X3 = pickᴰ 23 Sᴰ
  lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-CKd31-X3 : St 1166
  lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-CKd31-X3 = pickᴰ 24 Sᴰ
  lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-CKd32-X3 : St 1167
  lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-CKd32-X3 = pickᴰ 25 Sᴰ
  lem-pass-CCZ012-vs-CZ03 : St 1168
  lem-pass-CCZ012-vs-CZ03 = pickᴰ 26 Sᴰ
  lem-pass-CS03-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02-part2 : St 1169
  lem-pass-CS03-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02-part2 = pickᴰ 27 Sᴰ
  lem-pass-CCZ012-vs-CCZ013 : St 1107
  lem-pass-CCZ012-vs-CCZ013 = pickᴰ 28 Sᴰ
  lem-pass-Sd0-vs-CS03-TOFF012-CSd03-TOFF012 : St 1170
  lem-pass-Sd0-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 29 Sᴰ
  lem-pass-TOFF102-vs-CS03 : St 1124
  lem-pass-TOFF102-vs-CS03 = pickᴰ 30 Sᴰ
  lem-pass-TOFF102-vs-CSd03 : St 1125
  lem-pass-TOFF102-vs-CSd03 = pickᴰ 31 Sᴰ
  lem-pass-CCZ123-vs-CCZ012 : St 1171
  lem-pass-CCZ123-vs-CCZ012 = pickᴰ 32 Sᴰ
  lem-pass-CS12-vs-TOFF102-CS13-TOFF102-CSd13 : St 1172
  lem-pass-CS12-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 33 Sᴰ
  lem-pass-CSd12-vs-TOFF102-CS13-TOFF102-CSd13 : St 1173
  lem-pass-CSd12-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 34 Sᴰ
  lem-pass-TOFF103-vs-X2-TOFF102-X2 : St 1174
  lem-pass-TOFF103-vs-X2-TOFF102-X2 = pickᴰ 35 Sᴰ
  lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012 : St 1175
  lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 36 Sᴰ
  lem-pass-X2-CS21-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : St 1176
  lem-pass-X2-CS21-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = pickᴰ 37 Sᴰ
  lem-pass-CS13-vs-TOFF103-CS12-TOFF103-CSd12 : St 1177
  lem-pass-CS13-vs-TOFF103-CS12-TOFF103-CSd12 = pickᴰ 38 Sᴰ
  lem-pass-CSd13-vs-TOFF103-CS12-TOFF103-CSd12 : St 1178
  lem-pass-CSd13-vs-TOFF103-CS12-TOFF103-CSd12 = pickᴰ 39 Sᴰ
  lem-pass-S1-vs-TOFF102-CS13-TOFF102-CSd13 : St 1179
  lem-pass-S1-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 40 Sᴰ
  lem-pass-CS02-vs-TOFF201-CS23-TOFF201-CSd23 : St 1180
  lem-pass-CS02-vs-TOFF201-CS23-TOFF201-CSd23 = pickᴰ 41 Sᴰ
  lem-pass-CSd02-vs-TOFF201-CS23-TOFF201-CSd23 : St 1181
  lem-pass-CSd02-vs-TOFF201-CS23-TOFF201-CSd23 = pickᴰ 42 Sᴰ
  lem-pass-S2-vs-TOFF201-CS23-TOFF201-CSd23 : St 1182
  lem-pass-S2-vs-TOFF201-CS23-TOFF201-CSd23 = pickᴰ 43 Sᴰ
  lem-pass-Sd1-vs-TOFF102-CS13-TOFF102-CSd13 : St 1183
  lem-pass-Sd1-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 44 Sᴰ
  lem-pass-Sd2-vs-TOFF201-CS23-TOFF201-CSd23 : St 1184
  lem-pass-Sd2-vs-TOFF201-CS23-TOFF201-CSd23 = pickᴰ 45 Sᴰ
  lem-pass-TOFF012-vs-CS23 : St 1185
  lem-pass-TOFF012-vs-CS23 = pickᴰ 46 Sᴰ
  lem-pass-TOFF012-vs-CSd23 : St 1186
  lem-pass-TOFF012-vs-CSd23 = pickᴰ 47 Sᴰ
  lem-pass-TOFF013-vs-CCZ123 : St 1187
  lem-pass-TOFF013-vs-CCZ123 = pickᴰ 48 Sᴰ
  lem-pass-TOFF013-vs-CS23 : St 1188
  lem-pass-TOFF013-vs-CS23 = pickᴰ 49 Sᴰ
  lem-pass-TOFF023-vs-CS13 : St 1189
  lem-pass-TOFF023-vs-CS13 = pickᴰ 50 Sᴰ
  lem-pass-TOFF201-vs-CS03 : St 1190
  lem-pass-TOFF201-vs-CS03 = pickᴰ 51 Sᴰ
  lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 : St 1191
  lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 52 Sᴰ
  lem-pass-X2-CK20-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3 : St 1192
  lem-pass-X2-CK20-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3 = pickᴰ 53 Sᴰ
  lem-pass-X2-CKd20-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3 : St 1193
  lem-pass-X2-CKd20-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3 = pickᴰ 54 Sᴰ
  lem-pass-X2-CS20-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3 : St 1194
  lem-pass-X2-CS20-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3 = pickᴰ 55 Sᴰ
  lem-pass-X2-CS21-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 1195
  lem-pass-X2-CS21-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 56 Sᴰ
  lem-pass-X2-CSd20-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3 : St 1196
  lem-pass-X2-CSd20-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3 = pickᴰ 57 Sᴰ
  lem-pass-X2-CSd21-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 1197
  lem-pass-X2-CSd21-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 58 Sᴰ
  lem-pass-X3-CK31-X3-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 : St 1198
  lem-pass-X3-CK31-X3-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 = pickᴰ 59 Sᴰ
  lem-pass-X3-CKd32-X3-vs-CS23-TOFF201-CSd23-TOFF201 : St 1199
  lem-pass-X3-CKd32-X3-vs-CS23-TOFF201-CSd23-TOFF201 = pickᴰ 60 Sᴰ
  lem-pass-CS03-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02-part1 : St 1200
  lem-pass-CS03-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02-part1 = pickᴰ 61 Sᴰ
  lem-pass-TOFF201-vs-CSd03 : St 1201
  lem-pass-TOFF201-vs-CSd03 = pickᴰ 62 Sᴰ
  lem-pass-X2-CKd20-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 : St 1202
  lem-pass-X2-CKd20-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 = pickᴰ 63 Sᴰ
  lem-pass-X2-CSd20-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 : St 1203
  lem-pass-X2-CSd20-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 = pickᴰ 64 Sᴰ
  lem-pass-X2-CK20-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 : St 1204
  lem-pass-X2-CK20-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 = pickᴰ 65 Sᴰ
  lem-pass-X2-CK20-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 : St 1205
  lem-pass-X2-CK20-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 = pickᴰ 66 Sᴰ
  lem-pass-X2-CKd20-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 : St 1206
  lem-pass-X2-CKd20-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 = pickᴰ 67 Sᴰ
  lem-pass-X2-CS20-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 : St 1207
  lem-pass-X2-CS20-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 = pickᴰ 68 Sᴰ
  lem-pass-X2-CS20-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 : St 1208
  lem-pass-X2-CS20-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 = pickᴰ 69 Sᴰ
  lem-pass-X2-CSd20-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 : St 1209
  lem-pass-X2-CSd20-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 = pickᴰ 70 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF013-X3 : St 1210
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF013-X3 = pickᴰ 71 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX32-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CK21-CS12-CK21-CK21-X3 : St 1211
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX32-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CK21-CS12-CK21-CK21-X3 = pickᴰ 72 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS13-CS13-CS13-CK31-CS13-CS13-CX32-CS12-CS12-CS12-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CS12-CK21-CS12-CS12-X3 : St 1212
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS13-CS13-CS13-CK31-CS13-CS13-CX32-CS12-CS12-CS12-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CS12-CK21-CS12-CS12-X3 = pickᴰ 73 Sᴰ
  lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-TOFF123-X3 : St 1213
  lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-TOFF123-X3 = pickᴰ 74 Sᴰ

private
  q1 : Eqn
  q1 = wE 1474 W
  q2 : Eqn
  q2 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q3 : Eqn
  q3 = sE 1176 lem-pass-X2-CS21-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3
  q4 : Eqn
  q4 = wE 1475 W

-- pass [CS21] [X2 X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2 X3]: 5 steps
lem-pass-CS21-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 : ⟪ (ℓ "丶丘丞丈上中九丮九下三丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞丈上中九丮九下三丘丞丶") ⟫ʷ
lem-pass-CS21-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 = derive (ℓ "丶丘丞丈上中九丮九下三丘丞") (ℓ "丘丞丈上中九丮九下三丘丞丶")
  (rw 0 q1 ∷
   rw 13 q2 ∷
   rw 1 q3 ∷
   rw 11 q4 ∷
   rw⁻ 10 q2 ∷ []) Eq.refl

private
  q5 : Eqn
  q5 = wE 1347 W
  q6 : Eqn
  q6 = wE 128 W
  q7 : Eqn
  q7 = wE 1509 W
  q8 : Eqn
  q8 = sE 1171 lem-pass-CCZ123-vs-CCZ012
  q9 : Eqn
  q9 = wE 1510 W
  q10 : Eqn
  q10 = wE 1450 W
  q11 : Eqn
  q11 = wE 1437 W

-- pass [TOFF123] [TOFF102]: 7 steps
lem-pass-TOFF123-vs-TOFF102 : ⟪ (ℓ "乢习") ⟫ʷ ≈ ⟪ (ℓ "习乢") ⟫ʷ
lem-pass-TOFF123-vs-TOFF102 = derive (ℓ "乢习") (ℓ "习乢")
  (rw 1 q5 ∷
   rw 0 q6 ∷
   rw 2 q7 ∷
   rw 1 q8 ∷
   rw 2 q9 ∷
   rw 0 q10 ∷
   rw 1 q11 ∷ []) Eq.refl

private
  q12 : Eqn
  q12 = wE 1 W
  q13 : Eqn
  q13 = wE 173 W
  q14 : Eqn
  q14 = eqn (ℓ "丐乏") (ℓ "乏丐") (low-comm ((K ↑)) (Swap))
  q15 : Eqn
  q15 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q16 : Eqn
  q16 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q17 : Eqn
  q17 = wE 3 W
  q18 : Eqn
  q18 = wE 196 W
  q19 : Eqn
  q19 = wE 1516 W
  q20 : Eqn
  q20 = eqn (ℓ "丢乏") (ℓ "乏丢") (low-comm (CZ) (Swap))
  q21 : Eqn
  q21 = wE 43 W
  q22 : Eqn
  q22 = eqn (ℓ "丑乏") (ℓ "乏丑") (low-comm (((K • iI) ↑)) (Swap))
  q23 : Eqn
  q23 = sE 886 lem-pass-CCZ012-vs-CZ01
  q24 : Eqn
  q24 = sE 1107 lem-pass-CCZ012-vs-CCZ013
  q25 : Eqn
  q25 = wE 1517 W
  q26 : Eqn
  q26 = wE 175 W

-- pass [TOFF102] [X3 TOFF103 X3]: 118 steps
lem-pass-TOFF102-vs-X3-TOFF103-X3 : ⟪ (ℓ "习丞乡丞") ⟫ʷ ≈ ⟪ (ℓ "丞乡丞习") ⟫ʷ
lem-pass-TOFF102-vs-X3-TOFF103-X3 = derive (ℓ "习丞乡丞") (ℓ "丞乡丞习")
  (rw 4 q12 ∷
   rw 3 q13 ∷
   re 2 1 (ℓ "乏习乏") ∷
   re 3 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 2 q14 ∷
   rw 5 q12 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q15 ∷
   rw 7 q12 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q15 ∷
   rw 9 q12 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q14 ∷
   rw⁻ 9 q16 ∷
   rw 10 q17 ∷
   rw 9 q16 ∷
   rw 8 q14 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q17 ∷
   rw 6 q15 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 7 q17 ∷
   rw 4 q15 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q17 ∷
   rw 2 q14 ∷
   rw 3 q18 ∷
   re 3 8 (ℓ "习") ∷
   rw 1 q13 ∷
   rw 2 q19 ∷
   rw⁻ 1 q14 ∷
   rw⁻ 2 q20 ∷
   re 4 1 (ℓ "丶丣丷丣丧") ∷
   rw 5 q12 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q15 ∷
   rw 7 q12 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q15 ∷
   rw 9 q12 ∷
   re 7 3 (ℓ "中") ∷
   rw 3 q12 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q17 ∷
   rw⁻ 5 q15 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q17 ∷
   rw⁻ 7 q15 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q17 ∷
   rw 4 q21 ∷
   re 4 5 (ℓ "乙") ∷
   re 3 3 (ℓ "乚") ∷
   rw⁻ 4 q22 ∷
   rw 5 q17 ∷
   rw 0 q5 ∷
   rw 2 q7 ∷
   rw 1 q23 ∷
   rw 2 q24 ∷
   rw 3 q9 ∷
   rw 4 q12 ∷
   rw 3 q22 ∷
   re 2 1 (ℓ "乏乙乏") ∷
   re 3 1 (ℓ "丶丣丷丣丧") ∷
   rw 4 q12 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q15 ∷
   rw 6 q12 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q15 ∷
   rw 8 q12 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q17 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q17 ∷
   rw 5 q15 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 6 q17 ∷
   rw 3 q15 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 4 q17 ∷
   rw 3 q21 ∷
   re 3 5 (ℓ "乙") ∷
   rw 1 q20 ∷
   rw 0 q14 ∷
   rw 1 q25 ∷
   rw 0 q26 ∷
   re 2 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 1 q14 ∷
   rw 4 q12 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q15 ∷
   rw 6 q12 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q15 ∷
   rw 8 q12 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q14 ∷
   rw⁻ 8 q16 ∷
   rw 1 q12 ∷
   rw⁻ 2 q14 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q17 ∷
   rw⁻ 4 q15 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q17 ∷
   rw⁻ 6 q15 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q17 ∷
   rw⁻ 8 q14 ∷
   rw⁻ 9 q16 ∷
   rw 2 q18 ∷
   re 2 8 (ℓ "习") ∷
   re 1 3 (ℓ "乡") ∷
   rw 2 q26 ∷
   rw 3 q17 ∷
   rw 3 q10 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = sE 1172 lem-pass-CS12-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [TOFF102 CS13 TOFF102 CSd13] [CS12]: 1 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS12 : ⟪ (ℓ "习丽习举丶") ⟫ʷ ≈ ⟪ (ℓ "丶习丽习举") ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS12 = derive (ℓ "习丽习举丶") (ℓ "丶习丽习举")
  (rw⁻ 0 q27 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = sE 1173 lem-pass-CSd12-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [TOFF102 CS13 TOFF102 CSd13] [CSd12]: 1 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CSd12 : ⟪ (ℓ "习丽习举丷") ⟫ʷ ≈ ⟪ (ℓ "丷习丽习举") ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CSd12 = derive (ℓ "习丽习举丷") (ℓ "丷习丽习举")
  (rw⁻ 0 q28 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = sE 1154 lem-pass-CSd12-vs-X2-TOFF102-X2
  q30 : Eqn
  q30 = sE 1174 lem-pass-TOFF103-vs-X2-TOFF102-X2
  q31 : Eqn
  q31 = sE 1153 lem-pass-CS12-vs-X2-TOFF102-X2

-- pass [TOFF103 CS12 TOFF103 CSd12] [X2 TOFF102 X2]: 4 steps
lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-X2-TOFF102-X2 : ⟪ (ℓ "乡丶乡丷丘习丘") ⟫ʷ ≈ ⟪ (ℓ "丘习丘乡丶乡丷") ⟫ʷ
lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-X2-TOFF102-X2 = derive (ℓ "乡丶乡丷丘习丘") (ℓ "丘习丘乡丶乡丷")
  (rw 3 q29 ∷
   rw 2 q30 ∷
   rw 1 q31 ∷
   rw 0 q30 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = sE 1177 lem-pass-CS13-vs-TOFF103-CS12-TOFF103-CSd12

-- pass [TOFF103 CS12 TOFF103 CSd12] [CS13]: 1 steps
lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-CS13 : ⟪ (ℓ "乡丶乡丷丽") ⟫ʷ ≈ ⟪ (ℓ "丽乡丶乡丷") ⟫ʷ
lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-CS13 = derive (ℓ "乡丶乡丷丽") (ℓ "丽乡丶乡丷")
  (rw⁻ 0 q32 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = sE 1178 lem-pass-CSd13-vs-TOFF103-CS12-TOFF103-CSd12

-- pass [TOFF103 CS12 TOFF103 CSd12] [CSd13]: 1 steps
lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-CSd13 : ⟪ (ℓ "乡丶乡丷举") ⟫ʷ ≈ ⟪ (ℓ "举乡丶乡丷") ⟫ʷ
lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-CSd13 = derive (ℓ "乡丶乡丷举") (ℓ "举乡丶乡丷")
  (rw⁻ 0 q33 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = sE 1179 lem-pass-S1-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [TOFF102 CS13 TOFF102 CSd13] [S1]: 1 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-S1 : ⟪ (ℓ "习丽习举与") ⟫ʷ ≈ ⟪ (ℓ "与习丽习举") ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-S1 = derive (ℓ "习丽习举与") (ℓ "与习丽习举")
  (rw⁻ 0 q34 ∷ []) Eq.refl

private
  q35 : Eqn
  q35 = sE 1183 lem-pass-Sd1-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [TOFF102 CS13 TOFF102 CSd13] [Sd1]: 1 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-Sd1 : ⟪ (ℓ "习丽习举丏") ⟫ʷ ≈ ⟪ (ℓ "丏习丽习举") ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-Sd1 = derive (ℓ "习丽习举丏") (ℓ "丏习丽习举")
  (rw⁻ 0 q35 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = wE 1674 W
  q37 : Eqn
  q37 = sE 1199 lem-pass-X3-CKd32-X3-vs-CS23-TOFF201-CSd23-TOFF201
  q38 : Eqn
  q38 = wE 1675 W

-- pass [CKd32] [X3 CS23 TOFF201 CSd23 TOFF201 X3]: 3 steps
lem-pass-CKd32-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 : ⟪ (ℓ "乘丞义乣乊乣丞") ⟫ʷ ≈ ⟪ (ℓ "丞义乣乊乣丞乘") ⟫ʷ
lem-pass-CKd32-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 = derive (ℓ "乘丞义乣乊乣丞") (ℓ "丞义乣乊乣丞乘")
  (rw 0 q36 ∷
   rw 1 q37 ∷
   rw 5 q38 ∷ []) Eq.refl

private
  q39 : Eqn
  q39 = sE 1185 lem-pass-TOFF012-vs-CS23

-- pass [CS23] [TOFF012]: 1 steps
lem-pass-CS23-vs-TOFF012 : ⟪ (ℓ "义九") ⟫ʷ ≈ ⟪ (ℓ "九义") ⟫ʷ
lem-pass-CS23-vs-TOFF012 = derive (ℓ "义九") (ℓ "九义")
  (rw⁻ 0 q39 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = sE 1188 lem-pass-TOFF013-vs-CS23

-- pass [CS23] [TOFF013]: 1 steps
lem-pass-CS23-vs-TOFF013 : ⟪ (ℓ "义乞") ⟫ʷ ≈ ⟪ (ℓ "乞义") ⟫ʷ
lem-pass-CS23-vs-TOFF013 = derive (ℓ "义乞") (ℓ "乞义")
  (rw⁻ 0 q40 ∷ []) Eq.refl

private
  q41 : Eqn
  q41 = sE 1187 lem-pass-TOFF013-vs-CCZ123

-- pass [CCZ123] [TOFF013]: 1 steps
lem-pass-CCZ123-vs-TOFF013 : ⟪ (ℓ "乜乞") ⟫ʷ ≈ ⟪ (ℓ "乞乜") ⟫ʷ
lem-pass-CCZ123-vs-TOFF013 = derive (ℓ "乜乞") (ℓ "乞乜")
  (rw⁻ 0 q41 ∷ []) Eq.refl

private
  q42 : Eqn
  q42 = sE 1180 lem-pass-CS02-vs-TOFF201-CS23-TOFF201-CSd23

-- pass [TOFF201 CS23 TOFF201 CSd23] [CS02]: 1 steps
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CS02 : ⟪ (ℓ "乣义乣乊丧") ⟫ʷ ≈ ⟪ (ℓ "丧乣义乣乊") ⟫ʷ
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CS02 = derive (ℓ "乣义乣乊丧") (ℓ "丧乣义乣乊")
  (rw⁻ 0 q42 ∷ []) Eq.refl

private
  q43 : Eqn
  q43 = sE 1181 lem-pass-CSd02-vs-TOFF201-CS23-TOFF201-CSd23

-- pass [TOFF201 CS23 TOFF201 CSd23] [CSd02]: 1 steps
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CSd02 : ⟪ (ℓ "乣义乣乊丨") ⟫ʷ ≈ ⟪ (ℓ "丨乣义乣乊") ⟫ʷ
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CSd02 = derive (ℓ "乣义乣乊丨") (ℓ "丨乣义乣乊")
  (rw⁻ 0 q43 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = eqn (ℓ "丌丞") (ℓ "丞丌") (low₁-comm (X) ((X ↑ ↑)))
  q45 : Eqn
  q45 = wE 1366 W
  q46 : Eqn
  q46 = sE 1198 lem-pass-X3-CK31-X3-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0
  q47 : Eqn
  q47 = wE 1367 W

-- pass [CK31] [X0 X3 CS13 TOFF102 CSd13 TOFF102 X0 X3]: 5 steps
lem-pass-CK31-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 : ⟪ (ℓ "乔丌丞丽习举习丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞丽习举习丌丞乔") ⟫ʷ
lem-pass-CK31-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 = derive (ℓ "乔丌丞丽习举习丌丞") (ℓ "丌丞丽习举习丌丞乔")
  (rw 1 q44 ∷
   rw 0 q45 ∷
   rw 1 q46 ∷
   rw 7 q47 ∷
   rw⁻ 0 q44 ∷ []) Eq.refl

private
  q48 : Eqn
  q48 = sE 1189 lem-pass-TOFF023-vs-CS13

-- pass [CS13] [TOFF023]: 1 steps
lem-pass-CS13-vs-TOFF023 : ⟪ (ℓ "丽也") ⟫ʷ ≈ ⟪ (ℓ "也丽") ⟫ʷ
lem-pass-CS13-vs-TOFF023 = derive (ℓ "丽也") (ℓ "也丽")
  (rw⁻ 0 q48 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = wE 1687 W
  q50 : Eqn
  q50 = wE 1688 W

-- pass [X3 CKd32 X3] [X0 CS23 TOFF201 CSd23 TOFF201 X0]: 5 steps
lem-pass-X3-CKd32-X3-vs-X0-CS23-TOFF201-CSd23-TOFF201-X0 : ⟪ (ℓ "丞乘丞丌义乣乊乣丌") ⟫ʷ ≈ ⟪ (ℓ "丌义乣乊乣丌丞乘丞") ⟫ʷ
lem-pass-X3-CKd32-X3-vs-X0-CS23-TOFF201-CSd23-TOFF201-X0 = derive (ℓ "丞乘丞丌义乣乊乣丌") (ℓ "丌义乣乊乣丌丞乘丞")
  (rw 0 q49 ∷
   rw 1 q50 ∷
   rw 1 q37 ∷
   rw 5 q50 ∷
   rw 5 q49 ∷ []) Eq.refl

private
  q51 : Eqn
  q51 = sE 1190 lem-pass-TOFF201-vs-CS03

-- pass [CS03] [TOFF201]: 1 steps
lem-pass-CS03-vs-TOFF201 : ⟪ (ℓ "中乣") ⟫ʷ ≈ ⟪ (ℓ "乣中") ⟫ʷ
lem-pass-CS03-vs-TOFF201 = derive (ℓ "中乣") (ℓ "乣中")
  (rw⁻ 0 q51 ∷ []) Eq.refl

private
  q52 : Eqn
  q52 = sE 164 lem-pass-TOFF201-vs-iI
  q53 : Eqn
  q53 = sE 1155 lem-pass-TOFF201-vs-Sd0
  q54 : Eqn
  q54 = sE 1156 lem-pass-TOFF201-vs-Sd3
  q55 : Eqn
  q55 = sE 1190 lem-pass-TOFF201-vs-CS03

-- pass [TOFF201] [iI Sd0 Sd3 CS03]: 4 steps
lem-pass-TOFF201-vs-iI-Sd0-Sd3-CS03 : ⟪ (ℓ "乣一三丛中") ⟫ʷ ≈ ⟪ (ℓ "一三丛中乣") ⟫ʷ
lem-pass-TOFF201-vs-iI-Sd0-Sd3-CS03 = derive (ℓ "乣一三丛中") (ℓ "一三丛中乣")
  (rw 0 q52 ∷
   rw 1 q53 ∷
   rw 2 q54 ∷
   rw 3 q55 ∷ []) Eq.refl

private
  q56 : Eqn
  q56 = sE 1182 lem-pass-S2-vs-TOFF201-CS23-TOFF201-CSd23

-- pass [TOFF201 CS23 TOFF201 CSd23] [S2]: 1 steps
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-S2 : ⟪ (ℓ "乣义乣乊且") ⟫ʷ ≈ ⟪ (ℓ "且乣义乣乊") ⟫ʷ
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-S2 = derive (ℓ "乣义乣乊且") (ℓ "且乣义乣乊")
  (rw⁻ 0 q56 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = sE 1184 lem-pass-Sd2-vs-TOFF201-CS23-TOFF201-CSd23

-- pass [TOFF201 CS23 TOFF201 CSd23] [Sd2]: 1 steps
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-Sd2 : ⟪ (ℓ "乣义乣乊丕") ⟫ʷ ≈ ⟪ (ℓ "丕乣义乣乊") ⟫ʷ
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-Sd2 = derive (ℓ "乣义乣乊丕") (ℓ "丕乣义乣乊")
  (rw⁻ 0 q57 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = sE 1093 lem-pass-CS13-vs-CSd03
  q59 : Eqn
  q59 = sE 1125 lem-pass-TOFF102-vs-CSd03
  q60 : Eqn
  q60 = sE 1096 lem-pass-CSd13-vs-CSd03

-- pass [CSd03] [CS13 TOFF102 CSd13 TOFF102]: 4 steps
lem-pass-CSd03-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (ℓ "丮丽习举习") ⟫ʷ ≈ ⟪ (ℓ "丽习举习丮") ⟫ʷ
lem-pass-CSd03-vs-CS13-TOFF102-CSd13-TOFF102 = derive (ℓ "丮丽习举习") (ℓ "丽习举习丮")
  (rw⁻ 0 q58 ∷
   rw⁻ 1 q59 ∷
   rw⁻ 2 q60 ∷
   rw⁻ 3 q59 ∷ []) Eq.refl

private
  q61 : Eqn
  q61 = sE 63 lem-pass-CS13-vs-S0
  q62 : Eqn
  q62 = wE 1368 W
  q63 : Eqn
  q63 = sE 64 lem-pass-CSd13-vs-S0

-- pass [S0 CSd03] [CS13 TOFF102 CSd13 TOFF102]: 8 steps
lem-pass-S0-CSd03-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (ℓ "丈丮丽习举习") ⟫ʷ ≈ ⟪ (ℓ "丽习举习丈丮") ⟫ʷ
lem-pass-S0-CSd03-vs-CS13-TOFF102-CSd13-TOFF102 = derive (ℓ "丈丮丽习举习") (ℓ "丽习举习丈丮")
  (rw⁻ 1 q58 ∷
   rw⁻ 0 q61 ∷
   rw⁻ 2 q59 ∷
   rw 1 q62 ∷
   rw⁻ 3 q60 ∷
   rw⁻ 2 q63 ∷
   rw⁻ 4 q59 ∷
   rw 3 q62 ∷ []) Eq.refl

private
  q64 : Eqn
  q64 = wE 1493 W
  q65 : Eqn
  q65 = wE 1494 W
  q66 : Eqn
  q66 = sE 1195 lem-pass-X2-CS21-X2-vs-CS13-TOFF102-CSd13-TOFF102

-- pass [X2 CS21 X2] [X3 CS13 TOFF102 CSd13 TOFF102 X3]: 5 steps
lem-pass-X2-CS21-X2-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 : ⟪ (ℓ "丘丶丘丞丽习举习丞") ⟫ʷ ≈ ⟪ (ℓ "丞丽习举习丞丘丶丘") ⟫ʷ
lem-pass-X2-CS21-X2-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 = derive (ℓ "丘丶丘丞丽习举习丞") (ℓ "丞丽习举习丞丘丶丘")
  (rw 0 q64 ∷
   rw 1 q65 ∷
   rw 1 q66 ∷
   rw 5 q65 ∷
   rw 5 q64 ∷ []) Eq.refl

private
  q67 : Eqn
  q67 = wE 1499 W
  q68 : Eqn
  q68 = wE 1500 W
  q69 : Eqn
  q69 = sE 1197 lem-pass-X2-CSd21-X2-vs-CS13-TOFF102-CSd13-TOFF102

-- pass [X2 CSd21 X2] [X3 CS13 TOFF102 CSd13 TOFF102 X3]: 5 steps
lem-pass-X2-CSd21-X2-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 : ⟪ (ℓ "丘丷丘丞丽习举习丞") ⟫ʷ ≈ ⟪ (ℓ "丞丽习举习丞丘丷丘") ⟫ʷ
lem-pass-X2-CSd21-X2-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 = derive (ℓ "丘丷丘丞丽习举习丞") (ℓ "丞丽习举习丞丘丷丘")
  (rw 0 q67 ∷
   rw 1 q68 ∷
   rw 1 q69 ∷
   rw 5 q68 ∷
   rw 5 q67 ∷ []) Eq.refl

private
  q70 : Eqn
  q70 = wE 1466 W
  q71 : Eqn
  q71 = sE 1196 lem-pass-X2-CSd20-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3
  q72 : Eqn
  q72 = wE 1467 W

-- pass [CSd20] [X2 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X2 X3]: 5 steps
lem-pass-CSd20-vs-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X2-X3 : ⟪ (ℓ "丨丘丞丏丑与与丽习举习丏丏丐与丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞丏丑与与丽习举习丏丏丐与丘丞丨") ⟫ʷ
lem-pass-CSd20-vs-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X2-X3 = derive (ℓ "丨丘丞丏丑与与丽习举习丏丏丐与丘丞") (ℓ "丘丞丏丑与与丽习举习丏丏丐与丘丞丨")
  (rw 0 q70 ∷
   rw 17 q2 ∷
   rw 1 q71 ∷
   rw 15 q72 ∷
   rw⁻ 14 q2 ∷ []) Eq.refl

private
  q73 : Eqn
  q73 = wE 1464 W
  q74 : Eqn
  q74 = sE 1193 lem-pass-X2-CKd20-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3
  q75 : Eqn
  q75 = wE 1465 W

-- pass [CKd20] [X2 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X2 X3]: 5 steps
lem-pass-CKd20-vs-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X2-X3 : ⟪ (ℓ "久丘丞丏丑与与丽习举习丏丏丐与丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞丏丑与与丽习举习丏丏丐与丘丞久") ⟫ʷ
lem-pass-CKd20-vs-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X2-X3 = derive (ℓ "久丘丞丏丑与与丽习举习丏丏丐与丘丞") (ℓ "丘丞丏丑与与丽习举习丏丏丐与丘丞久")
  (rw 0 q73 ∷
   rw 17 q2 ∷
   rw 1 q74 ∷
   rw 15 q75 ∷
   rw⁻ 14 q2 ∷ []) Eq.refl

private
  q76 : Eqn
  q76 = wE 1407 W
  q77 : Eqn
  q77 = sE 1192 lem-pass-X2-CK20-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3
  q78 : Eqn
  q78 = wE 1408 W

-- pass [CK20] [X2 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X2 X3]: 5 steps
lem-pass-CK20-vs-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X2-X3 : ⟪ (ℓ "乄丘丞丏丑与与丽习举习丏丏丐与丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞丏丑与与丽习举习丏丏丐与丘丞乄") ⟫ʷ
lem-pass-CK20-vs-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X2-X3 = derive (ℓ "乄丘丞丏丑与与丽习举习丏丏丐与丘丞") (ℓ "丘丞丏丑与与丽习举习丏丏丐与丘丞乄")
  (rw 0 q76 ∷
   rw 17 q2 ∷
   rw 1 q77 ∷
   rw 15 q78 ∷
   rw⁻ 14 q2 ∷ []) Eq.refl

private
  q79 : Eqn
  q79 = wE 1462 W
  q80 : Eqn
  q80 = sE 1194 lem-pass-X2-CS20-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3
  q81 : Eqn
  q81 = wE 1463 W

-- pass [CS20] [X2 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X2 X3]: 5 steps
lem-pass-CS20-vs-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X2-X3 : ⟪ (ℓ "丧丘丞丏丑与与丽习举习丏丏丐与丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞丏丑与与丽习举习丏丏丐与丘丞丧") ⟫ʷ
lem-pass-CS20-vs-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X2-X3 = derive (ℓ "丧丘丞丏丑与与丽习举习丏丏丐与丘丞") (ℓ "丘丞丏丑与与丽习举习丏丏丐与丘丞丧")
  (rw 0 q79 ∷
   rw 17 q2 ∷
   rw 1 q80 ∷
   rw 15 q81 ∷
   rw⁻ 14 q2 ∷ []) Eq.refl

private
  q82 : Eqn
  q82 = wE 1680 W
  q83 : Eqn
  q83 = wE 1669 W
  q84 : Eqn
  q84 = wE 1670 W
  q85 : Eqn
  q85 = sE 1175 lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012

-- pass [X1 CS10 X1] [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3]: 7 steps
lem-pass-X1-CS10-X1-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : ⟪ (ℓ "丒丠丒丘丞中九丮九丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞中九丮九丘丞丒丠丒") ⟫ʷ
lem-pass-X1-CS10-X1-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = derive (ℓ "丒丠丒丘丞中九丮九丘丞") (ℓ "丘丞中九丮九丘丞丒丠丒")
  (rw 0 q82 ∷
   rw 1 q83 ∷
   rw 2 q84 ∷
   rw 2 q85 ∷
   rw 6 q84 ∷
   rw 6 q82 ∷
   rw 7 q83 ∷ []) Eq.refl

private
  q86 : Eqn
  q86 = wE 1678 W
  q87 : Eqn
  q87 = wE 1671 W
  q88 : Eqn
  q88 = wE 1679 W
  q89 : Eqn
  q89 = sE 1191 lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012

-- pass [X1 CSd10 X1] [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3]: 7 steps
lem-pass-X1-CSd10-X1-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : ⟪ (ℓ "丒両丒丘丞中九丮九丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞中九丮九丘丞丒両丒") ⟫ʷ
lem-pass-X1-CSd10-X1-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = derive (ℓ "丒両丒丘丞中九丮九丘丞") (ℓ "丘丞中九丮九丘丞丒両丒")
  (rw 0 q86 ∷
   rw 1 q87 ∷
   rw 2 q88 ∷
   rw 2 q89 ∷
   rw 6 q88 ∷
   rw 6 q86 ∷
   rw 7 q87 ∷ []) Eq.refl

private
  q90 : Eqn
  q90 = sE 1186 lem-pass-TOFF012-vs-CSd23

-- pass [CSd23] [TOFF012]: 1 steps
lem-pass-CSd23-vs-TOFF012 : ⟪ (ℓ "乊九") ⟫ʷ ≈ ⟪ (ℓ "九乊") ⟫ʷ
lem-pass-CSd23-vs-TOFF012 = derive (ℓ "乊九") (ℓ "九乊")
  (rw⁻ 0 q90 ∷ []) Eq.refl

private
  q91 : Eqn
  q91 = sE 1158 lem-pass-CS03-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02-part0
  q92 : Eqn
  q92 = sE 1200 lem-pass-CS03-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02-part1
  q93 : Eqn
  q93 = sE 1169 lem-pass-CS03-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02-part2

-- pass [CS03] [X1 X3 TOFF013 X1 X3 S0 CSd02 X1 X3 TOFF013 X1 X3 Sd0 CS02]: 3 steps
lem-pass-CS03-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02 : ⟪ (ℓ "中丒丞乞丒丞丈丨丒丞乞丒丞三丧") ⟫ʷ ≈ ⟪ (ℓ "丒丞乞丒丞丈丨丒丞乞丒丞三丧中") ⟫ʷ
lem-pass-CS03-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02 = derive (ℓ "中丒丞乞丒丞丈丨丒丞乞丒丞三丧") (ℓ "丒丞乞丒丞丈丨丒丞乞丒丞三丧中")
  (rw 0 q91 ∷
   rw 0 q92 ∷
   rw 0 q93 ∷ []) Eq.refl

private
  q94 : Eqn
  q94 = eqn (ℓ "丒乏") (ℓ "乏丒") (low-comm ((X ↑)) (Swap))
  q95 : Eqn
  q95 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q96 : Eqn
  q96 = wE 56 W
  q97 : Eqn
  q97 = wE 1446 W
  q98 : Eqn
  q98 = eqn (ℓ "不乏") (ℓ "乏不") (low₁-comm (Z) ((Swap ↑)))
  q99 : Eqn
  q99 = eqn (ℓ "下乏") (ℓ "乏下") (low₁-comm ((K • iI)) ((Swap ↑)))
  q100 : Eqn
  q100 = wE 53 W
  q101 : Eqn
  q101 = wE 1339 W
  q102 : Eqn
  q102 = sE 1157 lem-pass-CCZ012-vs-Z0
  q103 : Eqn
  q103 = sE 1168 lem-pass-CCZ012-vs-CZ03
  q104 : Eqn
  q104 = wE 54 W
  q105 : Eqn
  q105 = wE 1447 W
  q106 : Eqn
  q106 = wE 55 W

-- pass [TOFF012] [X1 X3 TOFF013 X1 X3]: 130 steps
lem-pass-TOFF012-vs-X1-X3-TOFF013-X1-X3 : ⟪ (ℓ "九丒丞乞丒丞") ⟫ʷ ≈ ⟪ (ℓ "丒丞乞丒丞九") ⟫ʷ
lem-pass-TOFF012-vs-X1-X3-TOFF013-X1-X3 = derive (ℓ "九丒丞乞丒丞") (ℓ "丒丞乞丒丞九")
  (rw 6 q12 ∷
   rw 5 q13 ∷
   rw 4 q94 ∷
   re 3 1 (ℓ "乏九乏") ∷
   re 4 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 3 q95 ∷
   rw 6 q12 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q15 ∷
   rw 8 q12 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q15 ∷
   rw 10 q12 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q95 ∷
   rw⁻ 10 q16 ∷
   rw 11 q17 ∷
   rw 10 q16 ∷
   rw 9 q95 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q17 ∷
   rw 7 q15 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q17 ∷
   rw 5 q15 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q17 ∷
   rw 3 q95 ∷
   rw 4 q96 ∷
   re 4 8 (ℓ "九") ∷
   rw 2 q13 ∷
   rw 1 q94 ∷
   rw 2 q97 ∷
   rw⁻ 1 q95 ∷
   rw⁻ 2 q98 ∷
   rw⁻ 3 q20 ∷
   rw 6 q12 ∷
   re 4 3 (ℓ "丯") ∷
   re 6 1 (ℓ "丶丣丷丣丧") ∷
   rw 7 q12 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q15 ∷
   rw 9 q12 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q15 ∷
   rw 11 q12 ∷
   re 9 3 (ℓ "中") ∷
   rw 5 q12 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q17 ∷
   rw⁻ 7 q15 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 8 q17 ∷
   rw⁻ 9 q15 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 10 q17 ∷
   rw 6 q21 ∷
   re 6 5 (ℓ "乙") ∷
   re 5 3 (ℓ "乚") ∷
   rw⁻ 6 q99 ∷
   rw 7 q17 ∷
   rw 0 q100 ∷
   rw 2 q101 ∷
   rw 1 q102 ∷
   rw 2 q23 ∷
   rw 3 q103 ∷
   rw 4 q24 ∷
   rw 5 q104 ∷
   rw 6 q12 ∷
   rw 5 q99 ∷
   re 4 1 (ℓ "乏乙乏") ∷
   re 5 1 (ℓ "丶丣丷丣丧") ∷
   rw 6 q12 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q15 ∷
   rw 8 q12 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q15 ∷
   rw 10 q12 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q17 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q17 ∷
   rw 7 q15 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q17 ∷
   rw 5 q15 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q17 ∷
   rw 5 q21 ∷
   re 5 5 (ℓ "乙") ∷
   re 3 1 (ℓ "乏丩乏") ∷
   rw 5 q17 ∷
   rw 2 q20 ∷
   rw 1 q98 ∷
   rw 0 q95 ∷
   rw 1 q105 ∷
   rw⁻ 0 q94 ∷
   rw 1 q26 ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 2 q95 ∷
   rw 5 q12 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q15 ∷
   rw 7 q12 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q15 ∷
   rw 9 q12 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q95 ∷
   rw⁻ 9 q16 ∷
   rw 2 q12 ∷
   rw⁻ 3 q95 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q17 ∷
   rw⁻ 5 q15 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q17 ∷
   rw⁻ 7 q15 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q17 ∷
   rw⁻ 9 q95 ∷
   rw⁻ 10 q16 ∷
   rw 3 q96 ∷
   re 3 8 (ℓ "九") ∷
   re 2 3 (ℓ "乞") ∷
   rw⁻ 3 q94 ∷
   rw 4 q26 ∷
   rw 5 q17 ∷
   rw 5 q106 ∷ []) Eq.refl

private
  q107 : Eqn
  q107 = sE 1170 lem-pass-Sd0-vs-CS03-TOFF012-CSd03-TOFF012

-- pass [CS03 TOFF012 CSd03 TOFF012] [Sd0]: 1 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-Sd0 : ⟪ (ℓ "中九丮九三") ⟫ʷ ≈ ⟪ (ℓ "三中九丮九") ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-Sd0 = derive (ℓ "中九丮九三") (ℓ "三中九丮九")
  (rw⁻ 0 q107 ∷ []) Eq.refl

private
  q108 : Eqn
  q108 = sE 1201 lem-pass-TOFF201-vs-CSd03

-- pass [CSd03] [TOFF201]: 1 steps
lem-pass-CSd03-vs-TOFF201 : ⟪ (ℓ "丮乣") ⟫ʷ ≈ ⟪ (ℓ "乣丮") ⟫ʷ
lem-pass-CSd03-vs-TOFF201 = derive (ℓ "丮乣") (ℓ "乣丮")
  (rw⁻ 0 q108 ∷ []) Eq.refl

private
  q109 : Eqn
  q109 = wE 1689 W

-- pass [X2 CS21 X2] [X0 X3 CS13 TOFF102 CSd13 TOFF102 X0 X3]: 7 steps
lem-pass-X2-CS21-X2-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 : ⟪ (ℓ "丘丶丘丌丞丽习举习丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞丽习举习丌丞丘丶丘") ⟫ʷ
lem-pass-X2-CS21-X2-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 = derive (ℓ "丘丶丘丌丞丽习举习丌丞") (ℓ "丌丞丽习举习丌丞丘丶丘")
  (rw 0 q109 ∷
   rw 1 q64 ∷
   rw 2 q65 ∷
   rw 2 q66 ∷
   rw 6 q65 ∷
   rw 6 q109 ∷
   rw 7 q64 ∷ []) Eq.refl

private
  q110 : Eqn
  q110 = wE 1749 W

-- pass [X2 CSd21 X2] [X0 X3 CS13 TOFF102 CSd13 TOFF102 X0 X3]: 7 steps
lem-pass-X2-CSd21-X2-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 : ⟪ (ℓ "丘丷丘丌丞丽习举习丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞丽习举习丌丞丘丷丘") ⟫ʷ
lem-pass-X2-CSd21-X2-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 = derive (ℓ "丘丷丘丌丞丽习举习丌丞") (ℓ "丌丞丽习举习丌丞丘丷丘")
  (rw 0 q110 ∷
   rw 1 q67 ∷
   rw 2 q68 ∷
   rw 2 q69 ∷
   rw 6 q68 ∷
   rw 6 q110 ∷
   rw 7 q67 ∷ []) Eq.refl

private
  q111 : Eqn
  q111 = sE 1161 lem-pass-TOFF102-vs-iI
  q112 : Eqn
  q112 = sE 1098 lem-pass-TOFF102-vs-Sd0
  q113 : Eqn
  q113 = sE 1160 lem-pass-TOFF102-vs-Sd3
  q114 : Eqn
  q114 = sE 1124 lem-pass-TOFF102-vs-CS03
  q115 : Eqn
  q115 = sE 1099 lem-pass-TOFF102-vs-X2-TOFF012-X2
  q116 : Eqn
  q116 = sE 1097 lem-pass-TOFF102-vs-S0
  q117 : Eqn
  q117 = sE 1159 lem-pass-TOFF102-vs-S3
  q118 : Eqn
  q118 = sE 1125 lem-pass-TOFF102-vs-CSd03

-- pass [TOFF102] [iI Sd0 Sd3 CS03 X2 TOFF012 X2 iI iI iI S0 S3 CSd03 X2 TOFF012 X2]: 12 steps
lem-pass-TOFF102-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2 : ⟪ (ℓ "习一三丛中丘九丘一一一丈业丮丘九丘") ⟫ʷ ≈ ⟪ (ℓ "一三丛中丘九丘一一一丈业丮丘九丘习") ⟫ʷ
lem-pass-TOFF102-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2 = derive (ℓ "习一三丛中丘九丘一一一丈业丮丘九丘") (ℓ "一三丛中丘九丘一一一丈业丮丘九丘习")
  (rw 0 q111 ∷
   rw 1 q112 ∷
   rw 2 q113 ∷
   rw 3 q114 ∷
   rw 4 q115 ∷
   rw 7 q111 ∷
   rw 8 q111 ∷
   rw 9 q111 ∷
   rw 10 q116 ∷
   rw 11 q117 ∷
   rw 12 q118 ∷
   rw 13 q115 ∷ []) Eq.refl

private
  q119 : Eqn
  q119 = eqn (ℓ "丌丘") (ℓ "丘丌") (low₁-comm (X) ((X ↑)))
  q120 : Eqn
  q120 = sE 1203 lem-pass-X2-CSd20-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3

-- pass [CSd20] [X0 X2 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X2 X3]: 7 steps
lem-pass-CSd20-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 : ⟪ (ℓ "丨丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞丨") ⟫ʷ
lem-pass-CSd20-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 = derive (ℓ "丨丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞") (ℓ "丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞丨")
  (rw 1 q119 ∷
   rw 0 q70 ∷
   rw 19 q2 ∷
   rw 1 q120 ∷
   rw 17 q72 ∷
   rw⁻ 0 q119 ∷
   rw⁻ 16 q2 ∷ []) Eq.refl

private
  q121 : Eqn
  q121 = sE 1202 lem-pass-X2-CKd20-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3

-- pass [CKd20] [X0 X2 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X2 X3]: 7 steps
lem-pass-CKd20-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 : ⟪ (ℓ "久丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞久") ⟫ʷ
lem-pass-CKd20-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 = derive (ℓ "久丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞") (ℓ "丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞久")
  (rw 1 q119 ∷
   rw 0 q73 ∷
   rw 19 q2 ∷
   rw 1 q121 ∷
   rw 17 q75 ∷
   rw⁻ 0 q119 ∷
   rw⁻ 16 q2 ∷ []) Eq.refl

private
  q122 : Eqn
  q122 = sE 1204 lem-pass-X2-CK20-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3

-- pass [CK20] [X0 X2 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X2 X3]: 7 steps
lem-pass-CK20-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 : ⟪ (ℓ "乄丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞乄") ⟫ʷ
lem-pass-CK20-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 = derive (ℓ "乄丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞") (ℓ "丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞乄")
  (rw 1 q119 ∷
   rw 0 q76 ∷
   rw 19 q2 ∷
   rw 1 q122 ∷
   rw 17 q78 ∷
   rw⁻ 0 q119 ∷
   rw⁻ 16 q2 ∷ []) Eq.refl

private
  q123 : Eqn
  q123 = sE 1207 lem-pass-X2-CS20-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3

-- pass [CS20] [X0 X2 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X2 X3]: 7 steps
lem-pass-CS20-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 : ⟪ (ℓ "丧丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞丧") ⟫ʷ
lem-pass-CS20-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 = derive (ℓ "丧丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞") (ℓ "丌丘丞丏丑与与丽习举习丏丏丐与丌丘丞丧")
  (rw 1 q119 ∷
   rw 0 q79 ∷
   rw 19 q2 ∷
   rw 1 q123 ∷
   rw 17 q81 ∷
   rw⁻ 0 q119 ∷
   rw⁻ 16 q2 ∷ []) Eq.refl

private
  q124 : Eqn
  q124 = sE 1209 lem-pass-X2-CSd20-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3

-- pass [CSd20] [X2 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X2 X3]: 5 steps
lem-pass-CSd20-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 : ⟪ (ℓ "丨丘丞与丐丽习举习丑丏丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞与丐丽习举习丑丏丘丞丨") ⟫ʷ
lem-pass-CSd20-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 = derive (ℓ "丨丘丞与丐丽习举习丑丏丘丞") (ℓ "丘丞与丐丽习举习丑丏丘丞丨")
  (rw 0 q70 ∷
   rw 13 q2 ∷
   rw 1 q124 ∷
   rw 11 q72 ∷
   rw⁻ 10 q2 ∷ []) Eq.refl

private
  q125 : Eqn
  q125 = sE 1206 lem-pass-X2-CKd20-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3

-- pass [CKd20] [X2 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X2 X3]: 5 steps
lem-pass-CKd20-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 : ⟪ (ℓ "久丘丞与丐丽习举习丑丏丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞与丐丽习举习丑丏丘丞久") ⟫ʷ
lem-pass-CKd20-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 = derive (ℓ "久丘丞与丐丽习举习丑丏丘丞") (ℓ "丘丞与丐丽习举习丑丏丘丞久")
  (rw 0 q73 ∷
   rw 13 q2 ∷
   rw 1 q125 ∷
   rw 11 q75 ∷
   rw⁻ 10 q2 ∷ []) Eq.refl

private
  q126 : Eqn
  q126 = sE 1205 lem-pass-X2-CK20-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3

-- pass [CK20] [X2 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X2 X3]: 5 steps
lem-pass-CK20-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 : ⟪ (ℓ "乄丘丞与丐丽习举习丑丏丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞与丐丽习举习丑丏丘丞乄") ⟫ʷ
lem-pass-CK20-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 = derive (ℓ "乄丘丞与丐丽习举习丑丏丘丞") (ℓ "丘丞与丐丽习举习丑丏丘丞乄")
  (rw 0 q76 ∷
   rw 13 q2 ∷
   rw 1 q126 ∷
   rw 11 q78 ∷
   rw⁻ 10 q2 ∷ []) Eq.refl

private
  q127 : Eqn
  q127 = sE 1208 lem-pass-X2-CS20-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3

-- pass [CS20] [X2 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X2 X3]: 5 steps
lem-pass-CS20-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 : ⟪ (ℓ "丧丘丞与丐丽习举习丑丏丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞与丐丽习举习丑丏丘丞丧") ⟫ʷ
lem-pass-CS20-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 = derive (ℓ "丧丘丞与丐丽习举习丑丏丘丞") (ℓ "丘丞与丐丽习举习丑丏丘丞丧")
  (rw 0 q79 ∷
   rw 13 q2 ∷
   rw 1 q127 ∷
   rw 11 q81 ∷
   rw⁻ 10 q2 ∷ []) Eq.refl

private
  q128 : Eqn
  q128 = sE 190 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK31-X3
  q129 : Eqn
  q129 = sE 1162 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK30-X3
  q130 : Eqn
  q130 = sE 1210 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF013-X3
  q131 : Eqn
  q131 = sE 1163 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CKd30-X3
  q132 : Eqn
  q132 = sE 191 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CKd31-X3

-- Bar(SSKSKK;3,2->0) passes III units 1: 5 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-III-units-1 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乔丞丞乑丞丞乞丞丞乒丞丞乕丞") ⟫ʷ ≈ ⟪ (ℓ "丞乔丞丞乑丞丞乞丞丞乒丞丞乕丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-III-units-1 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乔丞丞乑丞丞乞丞丞乒丞丞乕丞") (ℓ "丞乔丞丞乑丞丞乞丞丞乒丞丞乕丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 0 q128 ∷
   rw 3 q129 ∷
   rw 6 q130 ∷
   rw 9 q131 ∷
   rw 12 q132 ∷ []) Eq.refl

private
  q133 : Eqn
  q133 = sE 1212 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS13-CS13-CS13-CK31-CS13-CS13-CX32-CS12-CS12-CS12-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CS12-CK21-CS12-CS12-X3

-- Bar(SSKSKK;3,2->0) passes factors of X3 CS13 CS13 CS13 CK31 CS13 CS13 CX32 CS12 CS12 CS12 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CX32 CS12 CS12 CS12 CK21 CS12 CS12 X3: 1 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-factors-of-X3-CS13-CS13-CS13-CK31-CS13-CS13-CX32-CS12-CS12-CS12-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CS12-CK21-CS12-CS12-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞丽丽丽乔丽丽乖丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶乖丶丶丶乇丶丶丞") ⟫ʷ ≈ ⟪ (ℓ "丞丽丽丽乔丽丽乖丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶乖丶丶丶乇丶丶丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-factors-of-X3-CS13-CS13-CS13-CK31-CS13-CS13-CX32-CS12-CS12-CS12-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CS12-CK21-CS12-CS12-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞丽丽丽乔丽丽乖丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶乖丶丶丶乇丶丶丞") (ℓ "丞丽丽丽乔丽丽乖丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶乖丶丶丶乇丶丶丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 0 q133 ∷ []) Eq.refl

private
  q134 : Eqn
  q134 = sE 1211 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX32-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CK21-CS12-CK21-CK21-X3

-- Bar(SSKSKK;3,2->0) passes factors of X3 CS13 CS13 CK31 CS13 CK31 CK31 CX32 CK21 S2 CK21 S2 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CX32 CS12 CS12 CK21 CS12 CK21 CK21 X3: 1 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-factors-of-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX32-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CK21-CS12-CK21-CK21-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞丽丽乔丽乔乔乖乇且乇且丶丶丶乇且丶丶丶丶丶丶乖丶丶乇丶乇乇丞") ⟫ʷ ≈ ⟪ (ℓ "丞丽丽乔丽乔乔乖乇且乇且丶丶丶乇且丶丶丶丶丶丶乖丶丶乇丶乇乇丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-factors-of-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX32-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CK21-CS12-CK21-CK21-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞丽丽乔丽乔乔乖乇且乇且丶丶丶乇且丶丶丶丶丶丶乖丶丶乇丶乇乇丞") (ℓ "丞丽丽乔丽乔乔乖乇且乇且丶丶丶乇且丶丶丶丶丶丶乖丶丶乇丶乇乇丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 0 q134 ∷ []) Eq.refl

private
  q135 : Eqn
  q135 = sE 1164 lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-CK32-X3
  q136 : Eqn
  q136 = sE 1165 lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-CK31-X3
  q137 : Eqn
  q137 = sE 1213 lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-TOFF123-X3
  q138 : Eqn
  q138 = sE 1166 lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-CKd31-X3
  q139 : Eqn
  q139 = sE 1167 lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-CKd32-X3

-- Bar(['S', 'S', 'K', 'S', 'K', 'K'];3,0->1) passes III units 2: 5 steps
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶1⟩-passes-III-units-2 : ⟪ (ℓ "丽丽乔丽乔乔乐两丈两丈丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠两两丞乗丞丞乔丞丞乢丞丞乕丞丞乘丞") ⟫ʷ ≈ ⟪ (ℓ "丞乗丞丞乔丞丞乢丞丞乕丞丞乘丞丽丽乔丽乔乔乐两丈两丈丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠两两") ⟫ʷ
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶1⟩-passes-III-units-2 = derive (ℓ "丽丽乔丽乔乔乐两丈两丈丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠两两丞乗丞丞乔丞丞乢丞丞乕丞丞乘丞") (ℓ "丞乗丞丞乔丞丞乢丞丞乕丞丞乘丞丽丽乔丽乔乔乐两丈两丈丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠两两")
  (rw 0 q135 ∷
   rw 3 q136 ∷
   rw 6 q137 ∷
   rw 9 q138 ∷
   rw 12 q139 ∷ []) Eq.refl
