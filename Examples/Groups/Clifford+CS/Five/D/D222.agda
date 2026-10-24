{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD222 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D222 (Sᴰ : SD222) where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)

-- The lemmas of other derivation modules (DSig).
private
  lem-ckt-TST-at0440-part13 : Ws → St 2164
  lem-ckt-TST-at0440-part13 = pickᴰ 0 Sᴰ
  lem-ckt-TST-at0440-part37 : Ws → St 2165
  lem-ckt-TST-at0440-part37 = pickᴰ 1 Sᴰ
  lem-ckt-TST-at0440-part67 : Ws → St 2166
  lem-ckt-TST-at0440-part67 = pickᴰ 2 Sᴰ
  lem-ckt-TST-at0440-part68 : Ws → St 2167
  lem-ckt-TST-at0440-part68 = pickᴰ 3 Sᴰ
  lem-ckt-TST-at0440-part0 : Ws → St 2168
  lem-ckt-TST-at0440-part0 = pickᴰ 4 Sᴰ
  lem-ckt-TST-at0440-part1 : Ws → St 2169
  lem-ckt-TST-at0440-part1 = pickᴰ 5 Sᴰ
  lem-ckt-TST-at0440-part2 : Ws → St 2170
  lem-ckt-TST-at0440-part2 = pickᴰ 6 Sᴰ
  lem-ckt-TST-at0440-part3 : Ws → St 2171
  lem-ckt-TST-at0440-part3 = pickᴰ 7 Sᴰ
  lem-ckt-TST-at0440-part4 : Ws → St 2172
  lem-ckt-TST-at0440-part4 = pickᴰ 8 Sᴰ
  lem-ckt-TST-at0440-part5 : Ws → St 2173
  lem-ckt-TST-at0440-part5 = pickᴰ 9 Sᴰ
  lem-ckt-TST-at0440-part6 : Ws → St 2174
  lem-ckt-TST-at0440-part6 = pickᴰ 10 Sᴰ
  lem-ckt-TST-at0440-part7 : Ws → St 2175
  lem-ckt-TST-at0440-part7 = pickᴰ 11 Sᴰ
  lem-ckt-TST-at0440-part8 : Ws → St 2176
  lem-ckt-TST-at0440-part8 = pickᴰ 12 Sᴰ
  lem-ckt-TST-at0440-part9 : Ws → St 2177
  lem-ckt-TST-at0440-part9 = pickᴰ 13 Sᴰ
  lem-ckt-TST-at0440-part10 : Ws → St 2178
  lem-ckt-TST-at0440-part10 = pickᴰ 14 Sᴰ
  lem-ckt-TST-at0440-part11 : Ws → St 2179
  lem-ckt-TST-at0440-part11 = pickᴰ 15 Sᴰ
  lem-ckt-TST-at0440-part12 : Ws → St 2180
  lem-ckt-TST-at0440-part12 = pickᴰ 16 Sᴰ
  lem-ckt-TST-at0440-part14 : Ws → St 2181
  lem-ckt-TST-at0440-part14 = pickᴰ 17 Sᴰ
  lem-ckt-TST-at0440-part15 : Ws → St 2182
  lem-ckt-TST-at0440-part15 = pickᴰ 18 Sᴰ
  lem-ckt-TST-at0440-part16 : Ws → St 2183
  lem-ckt-TST-at0440-part16 = pickᴰ 19 Sᴰ
  lem-ckt-TST-at0440-part17 : Ws → St 2184
  lem-ckt-TST-at0440-part17 = pickᴰ 20 Sᴰ
  lem-ckt-TST-at0440-part18 : Ws → St 2185
  lem-ckt-TST-at0440-part18 = pickᴰ 21 Sᴰ
  lem-ckt-TST-at0440-part19 : Ws → St 2186
  lem-ckt-TST-at0440-part19 = pickᴰ 22 Sᴰ
  lem-ckt-TST-at0440-part20 : Ws → St 2187
  lem-ckt-TST-at0440-part20 = pickᴰ 23 Sᴰ
  lem-ckt-TST-at0440-part21 : Ws → St 2188
  lem-ckt-TST-at0440-part21 = pickᴰ 24 Sᴰ
  lem-ckt-TST-at0440-part22 : Ws → St 2189
  lem-ckt-TST-at0440-part22 = pickᴰ 25 Sᴰ
  lem-ckt-TST-at0440-part23 : Ws → St 2190
  lem-ckt-TST-at0440-part23 = pickᴰ 26 Sᴰ
  lem-ckt-TST-at0440-part24 : Ws → St 2191
  lem-ckt-TST-at0440-part24 = pickᴰ 27 Sᴰ
  lem-ckt-TST-at0440-part25 : Ws → St 2192
  lem-ckt-TST-at0440-part25 = pickᴰ 28 Sᴰ
  lem-ckt-TST-at0440-part26 : Ws → St 2193
  lem-ckt-TST-at0440-part26 = pickᴰ 29 Sᴰ
  lem-ckt-TST-at0440-part27 : Ws → St 2194
  lem-ckt-TST-at0440-part27 = pickᴰ 30 Sᴰ
  lem-ckt-TST-at0440-part28 : Ws → St 2195
  lem-ckt-TST-at0440-part28 = pickᴰ 31 Sᴰ
  lem-ckt-TST-at0440-part29 : Ws → St 2196
  lem-ckt-TST-at0440-part29 = pickᴰ 32 Sᴰ
  lem-ckt-TST-at0440-part30 : Ws → St 2197
  lem-ckt-TST-at0440-part30 = pickᴰ 33 Sᴰ
  lem-ckt-TST-at0440-part31 : Ws → St 2198
  lem-ckt-TST-at0440-part31 = pickᴰ 34 Sᴰ
  lem-ckt-TST-at0440-part32 : Ws → St 2199
  lem-ckt-TST-at0440-part32 = pickᴰ 35 Sᴰ
  lem-ckt-TST-at0440-part33 : Ws → St 2200
  lem-ckt-TST-at0440-part33 = pickᴰ 36 Sᴰ
  lem-ckt-TST-at0440-part34 : Ws → St 2201
  lem-ckt-TST-at0440-part34 = pickᴰ 37 Sᴰ
  lem-ckt-TST-at0440-part35 : Ws → St 2202
  lem-ckt-TST-at0440-part35 = pickᴰ 38 Sᴰ
  lem-ckt-TST-at0440-part36 : Ws → St 2203
  lem-ckt-TST-at0440-part36 = pickᴰ 39 Sᴰ
  lem-ckt-TST-at0440-part47 : Ws → St 2204
  lem-ckt-TST-at0440-part47 = pickᴰ 40 Sᴰ
  lem-ckt-TST-at0440-part50 : Ws → St 2205
  lem-ckt-TST-at0440-part50 = pickᴰ 41 Sᴰ
  lem-ckt-TST-at0440-part53 : Ws → St 2206
  lem-ckt-TST-at0440-part53 = pickᴰ 42 Sᴰ
  lem-ckt-TST-at0440-part56 : Ws → St 2207
  lem-ckt-TST-at0440-part56 = pickᴰ 43 Sᴰ
  lem-ckt-TST-at0440-part60 : Ws → St 2208
  lem-ckt-TST-at0440-part60 = pickᴰ 44 Sᴰ
  lem-ckt-TST-at0440-part64 : Ws → St 2209
  lem-ckt-TST-at0440-part64 = pickᴰ 45 Sᴰ
  lem-ckt-TST-at0440-part66 : Ws → St 2210
  lem-ckt-TST-at0440-part66 = pickᴰ 46 Sᴰ
  lem-ckt-TST-at0440-part38 : Ws → St 2211
  lem-ckt-TST-at0440-part38 = pickᴰ 47 Sᴰ
  lem-ckt-TST-at0440-part39 : Ws → St 2212
  lem-ckt-TST-at0440-part39 = pickᴰ 48 Sᴰ
  lem-ckt-TST-at0440-part41 : Ws → St 2213
  lem-ckt-TST-at0440-part41 = pickᴰ 49 Sᴰ
  lem-ckt-TST-at0440-part42 : Ws → St 2214
  lem-ckt-TST-at0440-part42 = pickᴰ 50 Sᴰ
  lem-ckt-TST-at0440-part43 : Ws → St 2215
  lem-ckt-TST-at0440-part43 = pickᴰ 51 Sᴰ
  lem-ckt-TST-at0440-part44 : Ws → St 2216
  lem-ckt-TST-at0440-part44 = pickᴰ 52 Sᴰ
  lem-ckt-TST-at0440-part46 : Ws → St 2217
  lem-ckt-TST-at0440-part46 = pickᴰ 53 Sᴰ
  lem-ckt-TST-at0440-part48 : Ws → St 2218
  lem-ckt-TST-at0440-part48 = pickᴰ 54 Sᴰ
  lem-ckt-TST-at0440-part49 : Ws → St 2219
  lem-ckt-TST-at0440-part49 = pickᴰ 55 Sᴰ
  lem-ckt-TST-at0440-part51 : Ws → St 2220
  lem-ckt-TST-at0440-part51 = pickᴰ 56 Sᴰ
  lem-ckt-TST-at0440-part52 : Ws → St 2221
  lem-ckt-TST-at0440-part52 = pickᴰ 57 Sᴰ
  lem-ckt-TST-at0440-part54 : Ws → St 2222
  lem-ckt-TST-at0440-part54 = pickᴰ 58 Sᴰ
  lem-ckt-TST-at0440-part55 : Ws → St 2223
  lem-ckt-TST-at0440-part55 = pickᴰ 59 Sᴰ
  lem-ckt-TST-at0440-part58 : Ws → St 2224
  lem-ckt-TST-at0440-part58 = pickᴰ 60 Sᴰ
  lem-ckt-TST-at0440-part59 : Ws → St 2225
  lem-ckt-TST-at0440-part59 = pickᴰ 61 Sᴰ
  lem-ckt-TST-at0440-part61 : Ws → St 2226
  lem-ckt-TST-at0440-part61 = pickᴰ 62 Sᴰ
  lem-ckt-TST-at0440-part62 : Ws → St 2227
  lem-ckt-TST-at0440-part62 = pickᴰ 63 Sᴰ
  lem-ckt-TST-at0440-part63 : Ws → St 2228
  lem-ckt-TST-at0440-part63 = pickᴰ 64 Sᴰ
  lem-ckt-TST-at0440-part65 : Ws → St 2229
  lem-ckt-TST-at0440-part65 = pickᴰ 65 Sᴰ
  lem-ckt-TST-at0440-part40 : Ws → St 2230
  lem-ckt-TST-at0440-part40 = pickᴰ 66 Sᴰ
  lem-ckt-TST-at0440-part45 : Ws → St 2231
  lem-ckt-TST-at0440-part45 = pickᴰ 67 Sᴰ
  lem-ckt-TST-at0440-part57 : Ws → St 2232
  lem-ckt-TST-at0440-part57 = pickᴰ 68 Sᴰ
  lem-ckt-TST-at0440-part69 : Ws → St 2233
  lem-ckt-TST-at0440-part69 = pickᴰ 69 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 2168 (lem-ckt-TST-at0440-part0 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 2169 (lem-ckt-TST-at0440-part1 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 2170 (lem-ckt-TST-at0440-part2 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 2171 (lem-ckt-TST-at0440-part3 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 2172 (lem-ckt-TST-at0440-part4 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 2173 (lem-ckt-TST-at0440-part5 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 2174 (lem-ckt-TST-at0440-part6 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 2175 (lem-ckt-TST-at0440-part7 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 2176 (lem-ckt-TST-at0440-part8 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 2177 (lem-ckt-TST-at0440-part9 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 2178 (lem-ckt-TST-at0440-part10 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 2179 (lem-ckt-TST-at0440-part11 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 2180 (lem-ckt-TST-at0440-part12 c4)
  q14 : Ws → Eqn
  q14 c4 = sE 2164 (lem-ckt-TST-at0440-part13 c4)
  q15 : Ws → Eqn
  q15 c4 = sE 2181 (lem-ckt-TST-at0440-part14 c4)
  q16 : Ws → Eqn
  q16 c4 = sE 2182 (lem-ckt-TST-at0440-part15 c4)
  q17 : Ws → Eqn
  q17 c4 = sE 2183 (lem-ckt-TST-at0440-part16 c4)
  q18 : Ws → Eqn
  q18 c4 = sE 2184 (lem-ckt-TST-at0440-part17 c4)
  q19 : Ws → Eqn
  q19 c4 = sE 2185 (lem-ckt-TST-at0440-part18 c4)
  q20 : Ws → Eqn
  q20 c4 = sE 2186 (lem-ckt-TST-at0440-part19 c4)
  q21 : Ws → Eqn
  q21 c4 = sE 2187 (lem-ckt-TST-at0440-part20 c4)
  q22 : Ws → Eqn
  q22 c4 = sE 2188 (lem-ckt-TST-at0440-part21 c4)
  q23 : Ws → Eqn
  q23 c4 = sE 2189 (lem-ckt-TST-at0440-part22 c4)
  q24 : Ws → Eqn
  q24 c4 = sE 2190 (lem-ckt-TST-at0440-part23 c4)
  q25 : Ws → Eqn
  q25 c4 = sE 2191 (lem-ckt-TST-at0440-part24 c4)
  q26 : Ws → Eqn
  q26 c4 = sE 2192 (lem-ckt-TST-at0440-part25 c4)
  q27 : Ws → Eqn
  q27 c4 = sE 2193 (lem-ckt-TST-at0440-part26 c4)
  q28 : Ws → Eqn
  q28 c4 = sE 2194 (lem-ckt-TST-at0440-part27 c4)
  q29 : Ws → Eqn
  q29 c4 = sE 2195 (lem-ckt-TST-at0440-part28 c4)
  q30 : Ws → Eqn
  q30 c4 = sE 2196 (lem-ckt-TST-at0440-part29 c4)
  q31 : Ws → Eqn
  q31 c4 = sE 2197 (lem-ckt-TST-at0440-part30 c4)
  q32 : Ws → Eqn
  q32 c4 = sE 2198 (lem-ckt-TST-at0440-part31 c4)
  q33 : Ws → Eqn
  q33 c4 = sE 2199 (lem-ckt-TST-at0440-part32 c4)
  q34 : Ws → Eqn
  q34 c4 = sE 2200 (lem-ckt-TST-at0440-part33 c4)
  q35 : Ws → Eqn
  q35 c4 = sE 2201 (lem-ckt-TST-at0440-part34 c4)
  q36 : Ws → Eqn
  q36 c4 = sE 2202 (lem-ckt-TST-at0440-part35 c4)
  q37 : Ws → Eqn
  q37 c4 = sE 2203 (lem-ckt-TST-at0440-part36 c4)
  q38 : Ws → Eqn
  q38 c4 = sE 2165 (lem-ckt-TST-at0440-part37 c4)
  q39 : Ws → Eqn
  q39 c4 = sE 2211 (lem-ckt-TST-at0440-part38 c4)
  q40 : Ws → Eqn
  q40 c4 = sE 2212 (lem-ckt-TST-at0440-part39 c4)
  q41 : Ws → Eqn
  q41 c4 = sE 2230 (lem-ckt-TST-at0440-part40 c4)
  q42 : Ws → Eqn
  q42 c4 = sE 2213 (lem-ckt-TST-at0440-part41 c4)
  q43 : Ws → Eqn
  q43 c4 = sE 2214 (lem-ckt-TST-at0440-part42 c4)
  q44 : Ws → Eqn
  q44 c4 = sE 2215 (lem-ckt-TST-at0440-part43 c4)
  q45 : Ws → Eqn
  q45 c4 = sE 2216 (lem-ckt-TST-at0440-part44 c4)
  q46 : Ws → Eqn
  q46 c4 = sE 2231 (lem-ckt-TST-at0440-part45 c4)
  q47 : Ws → Eqn
  q47 c4 = sE 2217 (lem-ckt-TST-at0440-part46 c4)
  q48 : Ws → Eqn
  q48 c4 = sE 2204 (lem-ckt-TST-at0440-part47 c4)
  q49 : Ws → Eqn
  q49 c4 = sE 2218 (lem-ckt-TST-at0440-part48 c4)
  q50 : Ws → Eqn
  q50 c4 = sE 2219 (lem-ckt-TST-at0440-part49 c4)
  q51 : Ws → Eqn
  q51 c4 = sE 2205 (lem-ckt-TST-at0440-part50 c4)
  q52 : Ws → Eqn
  q52 c4 = sE 2220 (lem-ckt-TST-at0440-part51 c4)
  q53 : Ws → Eqn
  q53 c4 = sE 2221 (lem-ckt-TST-at0440-part52 c4)
  q54 : Ws → Eqn
  q54 c4 = sE 2206 (lem-ckt-TST-at0440-part53 c4)
  q55 : Ws → Eqn
  q55 c4 = sE 2222 (lem-ckt-TST-at0440-part54 c4)
  q56 : Ws → Eqn
  q56 c4 = sE 2223 (lem-ckt-TST-at0440-part55 c4)
  q57 : Ws → Eqn
  q57 c4 = sE 2207 (lem-ckt-TST-at0440-part56 c4)
  q58 : Ws → Eqn
  q58 c4 = sE 2232 (lem-ckt-TST-at0440-part57 c4)
  q59 : Ws → Eqn
  q59 c4 = sE 2224 (lem-ckt-TST-at0440-part58 c4)
  q60 : Ws → Eqn
  q60 c4 = sE 2225 (lem-ckt-TST-at0440-part59 c4)
  q61 : Ws → Eqn
  q61 c4 = sE 2208 (lem-ckt-TST-at0440-part60 c4)
  q62 : Ws → Eqn
  q62 c4 = sE 2226 (lem-ckt-TST-at0440-part61 c4)
  q63 : Ws → Eqn
  q63 c4 = sE 2227 (lem-ckt-TST-at0440-part62 c4)
  q64 : Ws → Eqn
  q64 c4 = sE 2228 (lem-ckt-TST-at0440-part63 c4)
  q65 : Ws → Eqn
  q65 c4 = sE 2209 (lem-ckt-TST-at0440-part64 c4)
  q66 : Ws → Eqn
  q66 c4 = sE 2229 (lem-ckt-TST-at0440-part65 c4)
  q67 : Ws → Eqn
  q67 c4 = sE 2210 (lem-ckt-TST-at0440-part66 c4)
  q68 : Ws → Eqn
  q68 c4 = sE 2166 (lem-ckt-TST-at0440-part67 c4)
  q69 : Ws → Eqn
  q69 c4 = sE 2167 (lem-ckt-TST-at0440-part68 c4)
  q70 : Ws → Eqn
  q70 c4 = sE 2233 (lem-ckt-TST-at0440-part69 c4)

-- ckt-TST @0440: 70 steps
lem-ckt-TST-at0440 : Ws → ⟪ (ℓ "丒乢丘乇乇丘一乢乢乢丘乇乇丘一丞乢乢丞一丘乢乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一俊丒乢丘乇乇丘一乢乢乢丘乇乇丘一丞乢乢丞一丘乢乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一") ⟫ʷ ≈ ⟪ (ℓ "中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") ⟫ʷ
lem-ckt-TST-at0440 c4 = derive (ℓ "丒乢丘乇乇丘一乢乢乢丘乇乇丘一丞乢乢丞一丘乢乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一俊丒乢丘乇乇丘一乢乢乢丘乇乇丘一丞乢乢丞一丘乢乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一") (ℓ "中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上")
  (rw 0 (q1 c4) ∷
   rw 0 (q2 c4) ∷
   rw 0 (q3 c4) ∷
   rw 0 (q4 c4) ∷
   rw 0 (q5 c4) ∷
   rw 0 (q6 c4) ∷
   rw 0 (q7 c4) ∷
   rw 0 (q8 c4) ∷
   rw 0 (q9 c4) ∷
   rw 0 (q10 c4) ∷
   rw 0 (q11 c4) ∷
   rw 0 (q12 c4) ∷
   rw 0 (q13 c4) ∷
   rw 0 (q14 c4) ∷
   rw 0 (q15 c4) ∷
   rw 0 (q16 c4) ∷
   rw 0 (q17 c4) ∷
   rw 0 (q18 c4) ∷
   rw 0 (q19 c4) ∷
   rw 0 (q20 c4) ∷
   rw 0 (q21 c4) ∷
   rw 0 (q22 c4) ∷
   rw 0 (q23 c4) ∷
   rw 0 (q24 c4) ∷
   rw 0 (q25 c4) ∷
   rw 0 (q26 c4) ∷
   rw 0 (q27 c4) ∷
   rw 0 (q28 c4) ∷
   rw 0 (q29 c4) ∷
   rw 0 (q30 c4) ∷
   rw 0 (q31 c4) ∷
   rw 0 (q32 c4) ∷
   rw 0 (q33 c4) ∷
   rw 0 (q34 c4) ∷
   rw 0 (q35 c4) ∷
   rw 0 (q36 c4) ∷
   rw 0 (q37 c4) ∷
   rw 0 (q38 c4) ∷
   rw 0 (q39 c4) ∷
   rw 0 (q40 c4) ∷
   rw 0 (q41 c4) ∷
   rw 0 (q42 c4) ∷
   rw 0 (q43 c4) ∷
   rw 0 (q44 c4) ∷
   rw 0 (q45 c4) ∷
   rw 0 (q46 c4) ∷
   rw 0 (q47 c4) ∷
   rw 0 (q48 c4) ∷
   rw 0 (q49 c4) ∷
   rw 0 (q50 c4) ∷
   rw 0 (q51 c4) ∷
   rw 0 (q52 c4) ∷
   rw 0 (q53 c4) ∷
   rw 0 (q54 c4) ∷
   rw 0 (q55 c4) ∷
   rw 0 (q56 c4) ∷
   rw 0 (q57 c4) ∷
   rw 0 (q58 c4) ∷
   rw 0 (q59 c4) ∷
   rw 0 (q60 c4) ∷
   rw 0 (q61 c4) ∷
   rw 0 (q62 c4) ∷
   rw 0 (q63 c4) ∷
   rw 0 (q64 c4) ∷
   rw 0 (q65 c4) ∷
   rw 0 (q66 c4) ∷
   rw 0 (q67 c4) ∷
   rw 0 (q68 c4) ∷
   rw 0 (q69 c4) ∷
   rw 0 (q70 c4) ∷ []) Eq.refl
