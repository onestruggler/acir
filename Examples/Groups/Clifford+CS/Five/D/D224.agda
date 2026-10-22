{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD224 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D224 (Sᴰ : SD224) where

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
  lem-ckt-TST-part51 : Ws → St 2261
  lem-ckt-TST-part51 = pickᴰ 0 Sᴰ
  lem-ckt-TST-part19 : Ws → St 2262
  lem-ckt-TST-part19 = pickᴰ 1 Sᴰ
  lem-ckt-TST-part30 : Ws → St 2263
  lem-ckt-TST-part30 = pickᴰ 2 Sᴰ
  lem-ckt-TST-part39 : Ws → St 2264
  lem-ckt-TST-part39 = pickᴰ 3 Sᴰ
  lem-ckt-TST-part49 : Ws → St 2265
  lem-ckt-TST-part49 = pickᴰ 4 Sᴰ
  lem-ckt-TST-part0 : Ws → St 2266
  lem-ckt-TST-part0 = pickᴰ 5 Sᴰ
  lem-ckt-TST-part1 : Ws → St 2267
  lem-ckt-TST-part1 = pickᴰ 6 Sᴰ
  lem-ckt-TST-part2 : Ws → St 2268
  lem-ckt-TST-part2 = pickᴰ 7 Sᴰ
  lem-ckt-TST-part3 : Ws → St 2269
  lem-ckt-TST-part3 = pickᴰ 8 Sᴰ
  lem-ckt-TST-part4 : Ws → St 2270
  lem-ckt-TST-part4 = pickᴰ 9 Sᴰ
  lem-ckt-TST-part5 : Ws → St 2271
  lem-ckt-TST-part5 = pickᴰ 10 Sᴰ
  lem-ckt-TST-part6 : Ws → St 2272
  lem-ckt-TST-part6 = pickᴰ 11 Sᴰ
  lem-ckt-TST-part7 : Ws → St 2273
  lem-ckt-TST-part7 = pickᴰ 12 Sᴰ
  lem-ckt-TST-part8 : Ws → St 2274
  lem-ckt-TST-part8 = pickᴰ 13 Sᴰ
  lem-ckt-TST-part9 : Ws → St 2275
  lem-ckt-TST-part9 = pickᴰ 14 Sᴰ
  lem-ckt-TST-part10 : Ws → St 2276
  lem-ckt-TST-part10 = pickᴰ 15 Sᴰ
  lem-ckt-TST-part11 : Ws → St 2277
  lem-ckt-TST-part11 = pickᴰ 16 Sᴰ
  lem-ckt-TST-part12 : Ws → St 2278
  lem-ckt-TST-part12 = pickᴰ 17 Sᴰ
  lem-ckt-TST-part13 : Ws → St 2279
  lem-ckt-TST-part13 = pickᴰ 18 Sᴰ
  lem-ckt-TST-part14 : Ws → St 2280
  lem-ckt-TST-part14 = pickᴰ 19 Sᴰ
  lem-ckt-TST-part15 : Ws → St 2281
  lem-ckt-TST-part15 = pickᴰ 20 Sᴰ
  lem-ckt-TST-part16 : Ws → St 2282
  lem-ckt-TST-part16 = pickᴰ 21 Sᴰ
  lem-ckt-TST-part17 : Ws → St 2283
  lem-ckt-TST-part17 = pickᴰ 22 Sᴰ
  lem-ckt-TST-part18 : Ws → St 2284
  lem-ckt-TST-part18 = pickᴰ 23 Sᴰ
  lem-ckt-TST-part20 : Ws → St 2285
  lem-ckt-TST-part20 = pickᴰ 24 Sᴰ
  lem-ckt-TST-part32 : Ws → St 2286
  lem-ckt-TST-part32 = pickᴰ 25 Sᴰ
  lem-ckt-TST-part36 : Ws → St 2287
  lem-ckt-TST-part36 = pickᴰ 26 Sᴰ
  lem-ckt-TST-part42 : Ws → St 2288
  lem-ckt-TST-part42 = pickᴰ 27 Sᴰ
  lem-ckt-TST-part46 : Ws → St 2289
  lem-ckt-TST-part46 = pickᴰ 28 Sᴰ
  lem-ckt-TST-part50 : Ws → St 2290
  lem-ckt-TST-part50 = pickᴰ 29 Sᴰ
  lem-ckt-TST-part21 : Ws → St 2291
  lem-ckt-TST-part21 = pickᴰ 30 Sᴰ
  lem-ckt-TST-part24 : Ws → St 2292
  lem-ckt-TST-part24 = pickᴰ 31 Sᴰ
  lem-ckt-TST-part25 : Ws → St 2293
  lem-ckt-TST-part25 = pickᴰ 32 Sᴰ
  lem-ckt-TST-part26 : Ws → St 2294
  lem-ckt-TST-part26 = pickᴰ 33 Sᴰ
  lem-ckt-TST-part29 : Ws → St 2295
  lem-ckt-TST-part29 = pickᴰ 34 Sᴰ
  lem-ckt-TST-part31 : Ws → St 2296
  lem-ckt-TST-part31 = pickᴰ 35 Sᴰ
  lem-ckt-TST-part33 : Ws → St 2297
  lem-ckt-TST-part33 = pickᴰ 36 Sᴰ
  lem-ckt-TST-part34 : Ws → St 2298
  lem-ckt-TST-part34 = pickᴰ 37 Sᴰ
  lem-ckt-TST-part35 : Ws → St 2299
  lem-ckt-TST-part35 = pickᴰ 38 Sᴰ
  lem-ckt-TST-part37 : Ws → St 2300
  lem-ckt-TST-part37 = pickᴰ 39 Sᴰ
  lem-ckt-TST-part38 : Ws → St 2301
  lem-ckt-TST-part38 = pickᴰ 40 Sᴰ
  lem-ckt-TST-part41 : Ws → St 2302
  lem-ckt-TST-part41 = pickᴰ 41 Sᴰ
  lem-ckt-TST-part43 : Ws → St 2303
  lem-ckt-TST-part43 = pickᴰ 42 Sᴰ
  lem-ckt-TST-part44 : Ws → St 2304
  lem-ckt-TST-part44 = pickᴰ 43 Sᴰ
  lem-ckt-TST-part45 : Ws → St 2305
  lem-ckt-TST-part45 = pickᴰ 44 Sᴰ
  lem-ckt-TST-part47 : Ws → St 2306
  lem-ckt-TST-part47 = pickᴰ 45 Sᴰ
  lem-ckt-TST-part48 : Ws → St 2307
  lem-ckt-TST-part48 = pickᴰ 46 Sᴰ
  lem-ckt-TST-part52 : Ws → St 2308
  lem-ckt-TST-part52 = pickᴰ 47 Sᴰ
  lem-ckt-TST-part22 : Ws → St 2309
  lem-ckt-TST-part22 = pickᴰ 48 Sᴰ
  lem-ckt-TST-part23 : Ws → St 2310
  lem-ckt-TST-part23 = pickᴰ 49 Sᴰ
  lem-ckt-TST-part27 : Ws → St 2311
  lem-ckt-TST-part27 = pickᴰ 50 Sᴰ
  lem-ckt-TST-part28 : Ws → St 2312
  lem-ckt-TST-part28 = pickᴰ 51 Sᴰ
  lem-ckt-TST-part40 : Ws → St 2313
  lem-ckt-TST-part40 = pickᴰ 52 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 2266 (lem-ckt-TST-part0 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 2267 (lem-ckt-TST-part1 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 2268 (lem-ckt-TST-part2 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 2269 (lem-ckt-TST-part3 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 2270 (lem-ckt-TST-part4 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 2271 (lem-ckt-TST-part5 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 2272 (lem-ckt-TST-part6 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 2273 (lem-ckt-TST-part7 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 2274 (lem-ckt-TST-part8 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 2275 (lem-ckt-TST-part9 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 2276 (lem-ckt-TST-part10 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 2277 (lem-ckt-TST-part11 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 2278 (lem-ckt-TST-part12 c4)
  q14 : Ws → Eqn
  q14 c4 = sE 2279 (lem-ckt-TST-part13 c4)
  q15 : Ws → Eqn
  q15 c4 = sE 2280 (lem-ckt-TST-part14 c4)
  q16 : Ws → Eqn
  q16 c4 = sE 2281 (lem-ckt-TST-part15 c4)
  q17 : Ws → Eqn
  q17 c4 = sE 2282 (lem-ckt-TST-part16 c4)
  q18 : Ws → Eqn
  q18 c4 = sE 2283 (lem-ckt-TST-part17 c4)
  q19 : Ws → Eqn
  q19 c4 = sE 2284 (lem-ckt-TST-part18 c4)
  q20 : Ws → Eqn
  q20 c4 = sE 2262 (lem-ckt-TST-part19 c4)
  q21 : Ws → Eqn
  q21 c4 = sE 2285 (lem-ckt-TST-part20 c4)
  q22 : Ws → Eqn
  q22 c4 = sE 2291 (lem-ckt-TST-part21 c4)
  q23 : Ws → Eqn
  q23 c4 = sE 2309 (lem-ckt-TST-part22 c4)
  q24 : Ws → Eqn
  q24 c4 = sE 2310 (lem-ckt-TST-part23 c4)
  q25 : Ws → Eqn
  q25 c4 = sE 2292 (lem-ckt-TST-part24 c4)
  q26 : Ws → Eqn
  q26 c4 = sE 2293 (lem-ckt-TST-part25 c4)
  q27 : Ws → Eqn
  q27 c4 = sE 2294 (lem-ckt-TST-part26 c4)
  q28 : Ws → Eqn
  q28 c4 = sE 2311 (lem-ckt-TST-part27 c4)
  q29 : Ws → Eqn
  q29 c4 = sE 2312 (lem-ckt-TST-part28 c4)
  q30 : Ws → Eqn
  q30 c4 = sE 2295 (lem-ckt-TST-part29 c4)
  q31 : Ws → Eqn
  q31 c4 = sE 2263 (lem-ckt-TST-part30 c4)
  q32 : Ws → Eqn
  q32 c4 = sE 2296 (lem-ckt-TST-part31 c4)
  q33 : Ws → Eqn
  q33 c4 = sE 2286 (lem-ckt-TST-part32 c4)
  q34 : Ws → Eqn
  q34 c4 = sE 2297 (lem-ckt-TST-part33 c4)
  q35 : Ws → Eqn
  q35 c4 = sE 2298 (lem-ckt-TST-part34 c4)
  q36 : Ws → Eqn
  q36 c4 = sE 2299 (lem-ckt-TST-part35 c4)
  q37 : Ws → Eqn
  q37 c4 = sE 2287 (lem-ckt-TST-part36 c4)
  q38 : Ws → Eqn
  q38 c4 = sE 2300 (lem-ckt-TST-part37 c4)
  q39 : Ws → Eqn
  q39 c4 = sE 2301 (lem-ckt-TST-part38 c4)
  q40 : Ws → Eqn
  q40 c4 = sE 2264 (lem-ckt-TST-part39 c4)
  q41 : Ws → Eqn
  q41 c4 = sE 2313 (lem-ckt-TST-part40 c4)
  q42 : Ws → Eqn
  q42 c4 = sE 2302 (lem-ckt-TST-part41 c4)
  q43 : Ws → Eqn
  q43 c4 = sE 2288 (lem-ckt-TST-part42 c4)
  q44 : Ws → Eqn
  q44 c4 = sE 2303 (lem-ckt-TST-part43 c4)
  q45 : Ws → Eqn
  q45 c4 = sE 2304 (lem-ckt-TST-part44 c4)
  q46 : Ws → Eqn
  q46 c4 = sE 2305 (lem-ckt-TST-part45 c4)
  q47 : Ws → Eqn
  q47 c4 = sE 2289 (lem-ckt-TST-part46 c4)
  q48 : Ws → Eqn
  q48 c4 = sE 2306 (lem-ckt-TST-part47 c4)
  q49 : Ws → Eqn
  q49 c4 = sE 2307 (lem-ckt-TST-part48 c4)
  q50 : Ws → Eqn
  q50 c4 = sE 2265 (lem-ckt-TST-part49 c4)
  q51 : Ws → Eqn
  q51 c4 = sE 2290 (lem-ckt-TST-part50 c4)
  q52 : Ws → Eqn
  q52 c4 = sE 2261 (lem-ckt-TST-part51 c4)
  q53 : Ws → Eqn
  q53 c4 = sE 2308 (lem-ckt-TST-part52 c4)

-- ckt-TST: 53 steps
lem-ckt-TST : Ws → ⟪ (K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-0-41-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ
lem-ckt-TST c4 = derive (K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-0-41-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) (CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ S4 ∷ [])
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
   rw 0 (q53 c4) ∷ []) Eq.refl
