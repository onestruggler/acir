------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the four-wire derivations, each decided once
--
-- Each lemma is one window step of Four/D: two words on three wires with
-- the same operator, equal by completeness on three wires
-- (Windows.win, one evaluation, through the tables of Four.Lits),
-- stated over the macro letters as Four/D uses it.  Written by
-- scratchpad/four/winlib4.py, restated by winmac4.py and wintable4.py.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.Wins.W02 where

open import Data.List.Base using ([] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Four.Chain using (⟪_⟫ʷ ; _≈_)
open import Examples.Groups.Clifford+CS.Four.Letters
open import Examples.Groups.Clifford+CS.Four.Lits using (lw0 ; lw1 ; lw2 ; lw3)
open import Examples.Groups.Clifford+CS.Four.Str using (ℓ)

wn00216 : Base 3 → ⟪ (ℓ "丠並") ⟫ʷ ≈ ⟪ (ℓ "並丠") ⟫ʷ
wn00216 b = lw3 b (ℓ "丠並") (ℓ "並丠") tt tt Eq.refl
wn00217 : Base 3 → ⟪ (ℓ "丒並") ⟫ʷ ≈ ⟪ (ℓ "並丌") ⟫ʷ
wn00217 b = lw3 b (ℓ "丒並") (ℓ "並丌") tt tt Eq.refl
wn00218 : Base 3 → ⟪ (ℓ "临並") ⟫ʷ ≈ ⟪ (ℓ "並两") ⟫ʷ
wn00218 b = lw3 b (ℓ "临並") (ℓ "並两") tt tt Eq.refl
wn00219 : Base 3 → ⟪ (ℓ "並丠") ⟫ʷ ≈ ⟪ (ℓ "丠並") ⟫ʷ
wn00219 b = lw3 b (ℓ "並丠") (ℓ "丠並") tt tt Eq.refl
wn00220 : Base 3 → ⟪ (ℓ "並丌") ⟫ʷ ≈ ⟪ (ℓ "丒並") ⟫ʷ
wn00220 b = lw3 b (ℓ "並丌") (ℓ "丒並") tt tt Eq.refl
wn00221 : Base 3 → ⟪ (ℓ "並两") ⟫ʷ ≈ ⟪ (ℓ "临並") ⟫ʷ
wn00221 b = lw3 b (ℓ "並两") (ℓ "临並") tt tt Eq.refl
wn00222 : Base 3 → ⟪ (ℓ "丼丒") ⟫ʷ ≈ ⟪ (ℓ "丘丼") ⟫ʷ
wn00222 b = lw3 b (ℓ "丼丒") (ℓ "丘丼") tt tt Eq.refl
wn00223 : Base 3 → ⟪ (ℓ "丘乄丘丨") ⟫ʷ ≈ ⟪ (ℓ "丨丘乄丘") ⟫ʷ
wn00223 b = lw3 b (ℓ "丘乄丘丨") (ℓ "丨丘乄丘") tt tt Eq.refl
wn00224 : Base 3 → ⟪ (ℓ "上九下") ⟫ʷ ≈ ⟪ (ℓ "乙") ⟫ʷ
wn00224 b = lw3 b (ℓ "上九下") (ℓ "乙") tt tt Eq.refl
wn00225 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (ℓ "丞丞") ⟫ʷ
wn00225 b = lw0 b [] (ℓ "丞丞") tt tt Eq.refl
wn00226 : Base 3 → ⟪ (ℓ "乙下") ⟫ʷ ≈ ⟪ (ℓ "下九") ⟫ʷ
wn00226 b = lw3 b (ℓ "乙下") (ℓ "下九") tt tt Eq.refl
wn00227 : Base 3 → ⟪ (ℓ "九九") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00227 b = lw3 b (ℓ "九九") [] tt tt Eq.refl
wn00228 : Base 3 → ⟪ (ℓ "九上") ⟫ʷ ≈ ⟪ (ℓ "上乙") ⟫ʷ
wn00228 b = lw3 b (ℓ "九上") (ℓ "上乙") tt tt Eq.refl
wn00229 : Base 3 → ⟪ (ℓ "丶下") ⟫ʷ ≈ ⟪ (ℓ "下丶") ⟫ʷ
wn00229 b = lw3 b (ℓ "丶下") (ℓ "下丶") tt tt Eq.refl
wn00230 : Base 3 → ⟪ (ℓ "丶上") ⟫ʷ ≈ ⟪ (ℓ "上丶") ⟫ʷ
wn00230 b = lw3 b (ℓ "丶上") (ℓ "上丶") tt tt Eq.refl
wn00231 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (ℓ "丨丧") ⟫ʷ
wn00231 b = lw3 b [] (ℓ "丨丧") tt tt Eq.refl
wn00232 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (ℓ "久丨乄久丧乄") ⟫ʷ
wn00232 b = lw3 b [] (ℓ "久丨乄久丧乄") tt tt Eq.refl
wn00233 : Base 3 → ⟪ (ℓ "丘丧丘九") ⟫ʷ ≈ ⟪ (ℓ "九丘丧丘") ⟫ʷ
wn00233 b = lw3 b (ℓ "丘丧丘九") (ℓ "九丘丧丘") tt tt Eq.refl
wn00234 : Base 3 → ⟪ (ℓ "丞丽丞丶") ⟫ʷ ≈ ⟪ (ℓ "丶丞丽丞") ⟫ʷ
wn00234 b = lw0 b (ℓ "丞丽丞丶") (ℓ "丶丞丽丞") tt tt Eq.refl
wn00235 : Base 3 → ⟪ (ℓ "丞丽丞丷") ⟫ʷ ≈ ⟪ (ℓ "丷丞丽丞") ⟫ʷ
wn00235 b = lw0 b (ℓ "丞丽丞丷") (ℓ "丷丞丽丞") tt tt Eq.refl
wn00236 : Base 3 → ⟪ (ℓ "三乙") ⟫ʷ ≈ ⟪ (ℓ "乙三") ⟫ʷ
wn00236 b = lw3 b (ℓ "三乙") (ℓ "乙三") tt tt Eq.refl
wn00237 : Base 3 → ⟪ (ℓ "丈乙") ⟫ʷ ≈ ⟪ (ℓ "乙丈") ⟫ʷ
wn00237 b = lw3 b (ℓ "丈乙") (ℓ "乙丈") tt tt Eq.refl
wn00238 : Base 3 → ⟪ (ℓ "丘丨丘习") ⟫ʷ ≈ ⟪ (ℓ "习丘丨丘") ⟫ʷ
wn00238 b = lw3 b (ℓ "丘丨丘习") (ℓ "习丘丨丘") tt tt Eq.refl
wn00239 : Base 3 → ⟪ (ℓ "丘久丘习") ⟫ʷ ≈ ⟪ (ℓ "习丘久丘") ⟫ʷ
wn00239 b = lw3 b (ℓ "丘久丘习") (ℓ "习丘久丘") tt tt Eq.refl
wn00240 : Base 3 → ⟪ (ℓ "丘乄丘习") ⟫ʷ ≈ ⟪ (ℓ "习丘乄丘") ⟫ʷ
wn00240 b = lw3 b (ℓ "丘乄丘习") (ℓ "习丘乄丘") tt tt Eq.refl
wn00241 : Base 3 → ⟪ (ℓ "丘丧丘习") ⟫ʷ ≈ ⟪ (ℓ "习丘丧丘") ⟫ʷ
wn00241 b = lw3 b (ℓ "丘丧丘习") (ℓ "习丘丧丘") tt tt Eq.refl
wn00242 : Base 3 → ⟪ (ℓ "丧与") ⟫ʷ ≈ ⟪ (ℓ "与丧") ⟫ʷ
wn00242 b = lw3 b (ℓ "丧与") (ℓ "与丧") tt tt Eq.refl
wn00243 : Base 3 → ⟪ (ℓ "丧丏") ⟫ʷ ≈ ⟪ (ℓ "丏丧") ⟫ʷ
wn00243 b = lw3 b (ℓ "丧丏") (ℓ "丏丧") tt tt Eq.refl
wn00244 : Base 3 → ⟪ (ℓ "丧丘习丘") ⟫ʷ ≈ ⟪ (ℓ "丘习丘丧") ⟫ʷ
wn00244 b = lw3 b (ℓ "丧丘习丘") (ℓ "丘习丘丧") tt tt Eq.refl
wn00245 : Base 3 → ⟪ (ℓ "丧丠") ⟫ʷ ≈ ⟪ (ℓ "丠丧") ⟫ʷ
wn00245 b = lw3 b (ℓ "丧丠") (ℓ "丠丧") tt tt Eq.refl
wn00246 : Base 3 → ⟪ (ℓ "丧両") ⟫ʷ ≈ ⟪ (ℓ "両丧") ⟫ʷ
wn00246 b = lw3 b (ℓ "丧両") (ℓ "両丧") tt tt Eq.refl
wn00247 : Base 3 → ⟪ (ℓ "九丘习丘") ⟫ʷ ≈ ⟪ (ℓ "丘习丘九") ⟫ʷ
wn00247 b = lw3 b (ℓ "九丘习丘") (ℓ "丘习丘九") tt tt Eq.refl
wn00248 : Base 3 → ⟪ (ℓ "丘丨丘九") ⟫ʷ ≈ ⟪ (ℓ "九丘丨丘") ⟫ʷ
wn00248 b = lw3 b (ℓ "丘丨丘九") (ℓ "九丘丨丘") tt tt Eq.refl
wn00249 : Base 3 → ⟪ (ℓ "丞举丞丶") ⟫ʷ ≈ ⟪ (ℓ "丶丞举丞") ⟫ʷ
wn00249 b = lw0 b (ℓ "丞举丞丶") (ℓ "丶丞举丞") tt tt Eq.refl
wn00250 : Base 3 → ⟪ (ℓ "丞举丞丷") ⟫ʷ ≈ ⟪ (ℓ "丷丞举丞") ⟫ʷ
wn00250 b = lw0 b (ℓ "丞举丞丷") (ℓ "丷丞举丞") tt tt Eq.refl
wn00251 : Base 3 → ⟪ (ℓ "乙丧") ⟫ʷ ≈ ⟪ (ℓ "丧乙") ⟫ʷ
wn00251 b = lw3 b (ℓ "乙丧") (ℓ "丧乙") tt tt Eq.refl
wn00252 : Base 3 → ⟪ [] ⟫ʷ ≈ ⟪ (ℓ "个个") ⟫ʷ
wn00252 b = lw3 b [] (ℓ "个个") tt tt Eq.refl
wn00253 : Base 3 → ⟪ (ℓ "丹並") ⟫ʷ ≈ ⟪ (ℓ "並个") ⟫ʷ
wn00253 b = lw3 b (ℓ "丹並") (ℓ "並个") tt tt Eq.refl
wn00254 : Base 3 → ⟪ (ℓ "乙丨") ⟫ʷ ≈ ⟪ (ℓ "丨乙") ⟫ʷ
wn00254 b = lw3 b (ℓ "乙丨") (ℓ "丨乙") tt tt Eq.refl
wn00255 : Base 3 → ⟪ (ℓ "丘丶丘丽") ⟫ʷ ≈ ⟪ (ℓ "丽丘丶丘") ⟫ʷ
wn00255 b = lw0 b (ℓ "丘丶丘丽") (ℓ "丽丘丶丘") tt tt Eq.refl
wn00256 : Base 3 → ⟪ (ℓ "丘丶丘举") ⟫ʷ ≈ ⟪ (ℓ "举丘丶丘") ⟫ʷ
wn00256 b = lw0 b (ℓ "丘丶丘举") (ℓ "举丘丶丘") tt tt Eq.refl
wn00257 : Base 3 → ⟪ (ℓ "丘丽") ⟫ʷ ≈ ⟪ (ℓ "丽丘") ⟫ʷ
wn00257 b = lw0 b (ℓ "丘丽") (ℓ "丽丘") tt tt Eq.refl
wn00258 : Base 3 → ⟪ (ℓ "丘举") ⟫ʷ ≈ ⟪ (ℓ "举丘") ⟫ʷ
wn00258 b = lw0 b (ℓ "丘举") (ℓ "举丘") tt tt Eq.refl
wn00259 : Base 3 → ⟪ (ℓ "乜丽") ⟫ʷ ≈ ⟪ (ℓ "丽乜") ⟫ʷ
wn00259 b = lw0 b (ℓ "乜丽") (ℓ "丽乜") tt tt Eq.refl
wn00260 : Base 3 → ⟪ (ℓ "乜举") ⟫ʷ ≈ ⟪ (ℓ "举乜") ⟫ʷ
wn00260 b = lw0 b (ℓ "乜举") (ℓ "举乜") tt tt Eq.refl
wn00261 : Base 3 → ⟪ (ℓ "乃丷") ⟫ʷ ≈ ⟪ (ℓ "丷乃") ⟫ʷ
wn00261 b = lw3 b (ℓ "乃丷") (ℓ "丷乃") tt tt Eq.refl
wn00262 : Base 3 → ⟪ (ℓ "丧丨") ⟫ʷ ≈ ⟪ (ℓ "丨丧") ⟫ʷ
wn00262 b = lw3 b (ℓ "丧丨") (ℓ "丨丧") tt tt Eq.refl
wn00263 : Base 3 → ⟪ (ℓ "丧丈丨") ⟫ʷ ≈ ⟪ (ℓ "丈丨丧") ⟫ʷ
wn00263 b = lw3 b (ℓ "丧丈丨") (ℓ "丈丨丧") tt tt Eq.refl
wn00264 : Base 3 → ⟪ (ℓ "丨丠") ⟫ʷ ≈ ⟪ (ℓ "丠丨") ⟫ʷ
wn00264 b = lw3 b (ℓ "丨丠") (ℓ "丠丨") tt tt Eq.refl
wn00265 : Base 3 → ⟪ (ℓ "丈丠") ⟫ʷ ≈ ⟪ (ℓ "丠丈") ⟫ʷ
wn00265 b = lw3 b (ℓ "丈丠") (ℓ "丠丈") tt tt Eq.refl
wn00266 : Base 3 → ⟪ (ℓ "乜义") ⟫ʷ ≈ ⟪ (ℓ "义乜") ⟫ʷ
wn00266 b = lw0 b (ℓ "乜义") (ℓ "义乜") tt tt Eq.refl
wn00267 : Base 3 → ⟪ (ℓ "乜之") ⟫ʷ ≈ ⟪ (ℓ "之乜") ⟫ʷ
wn00267 b = lw0 b (ℓ "乜之") (ℓ "之乜") tt tt Eq.refl
wn00268 : Base 3 → ⟪ (ℓ "丈両") ⟫ʷ ≈ ⟪ (ℓ "両丈") ⟫ʷ
wn00268 b = lw3 b (ℓ "丈両") (ℓ "両丈") tt tt Eq.refl
wn00269 : Base 3 → ⟪ (ℓ "乜乊") ⟫ʷ ≈ ⟪ (ℓ "乊乜") ⟫ʷ
wn00269 b = lw0 b (ℓ "乜乊") (ℓ "乊乜") tt tt Eq.refl
wn00270 : Base 3 → ⟪ (ℓ "丨両") ⟫ʷ ≈ ⟪ (ℓ "両丨") ⟫ʷ
wn00270 b = lw3 b (ℓ "丨両") (ℓ "両丨") tt tt Eq.refl
wn00271 : Base 3 → ⟪ (ℓ "丐並") ⟫ʷ ≈ ⟪ (ℓ "並上") ⟫ʷ
wn00271 b = lw3 b (ℓ "丐並") (ℓ "並上") tt tt Eq.refl
wn00272 : Base 3 → ⟪ (ℓ "上丧丳丨丳丶上丁") ⟫ʷ ≈ ⟪ (ℓ "上丶丣丷丣丧上一") ⟫ʷ
wn00272 b = lw3 b (ℓ "上丧丳丨丳丶上丁") (ℓ "上丶丣丷丣丧上一") tt tt Eq.refl
wn00273 : Base 3 → ⟪ (ℓ "乇並") ⟫ʷ ≈ ⟪ (ℓ "並乄") ⟫ʷ
wn00273 b = lw3 b (ℓ "乇並") (ℓ "並乄") tt tt Eq.refl
wn00274 : Base 3 → ⟪ (ℓ "丐丧丳丨丳丶丐丁") ⟫ʷ ≈ ⟪ (ℓ "丐丶丣丷丣丧丐一") ⟫ʷ
wn00274 b = lw3 b (ℓ "丐丧丳丨丳丶丐丁") (ℓ "丐丶丣丷丣丧丐一") tt tt Eq.refl
wn00275 : Base 3 → ⟪ (ℓ "並乄") ⟫ʷ ≈ ⟪ (ℓ "乇並") ⟫ʷ
wn00275 b = lw3 b (ℓ "並乄") (ℓ "乇並") tt tt Eq.refl
wn00276 : Base 3 → ⟪ (ℓ "丞乔丞举") ⟫ʷ ≈ ⟪ (ℓ "举丞乔丞") ⟫ʷ
wn00276 b = lw0 b (ℓ "丞乔丞举") (ℓ "举丞乔丞") tt tt Eq.refl
wn00277 : Base 3 → ⟪ (ℓ "丘丶丘习") ⟫ʷ ≈ ⟪ (ℓ "习丘丶丘") ⟫ʷ
wn00277 b = lw3 b (ℓ "丘丶丘习") (ℓ "习丘丶丘") tt tt Eq.refl
wn00278 : Base 3 → ⟪ (ℓ "丘丶丘九") ⟫ʷ ≈ ⟪ (ℓ "九丘丶丘") ⟫ʷ
wn00278 b = lw3 b (ℓ "丘丶丘九") (ℓ "九丘丶丘") tt tt Eq.refl
wn00279 : Base 3 → ⟪ (ℓ "乔丼") ⟫ʷ ≈ ⟪ (ℓ "丼乗") ⟫ʷ
wn00279 b = lw0 b (ℓ "乔丼") (ℓ "丼乗") tt tt Eq.refl
wn00280 : Base 3 → ⟪ (ℓ "乗丼") ⟫ʷ ≈ ⟪ (ℓ "丼乔") ⟫ʷ
wn00280 b = lw0 b (ℓ "乗丼") (ℓ "丼乔") tt tt Eq.refl
wn00281 : Base 3 → ⟪ (ℓ "丘乇丘九") ⟫ʷ ≈ ⟪ (ℓ "九丘乇丘") ⟫ʷ
wn00281 b = lw3 b (ℓ "丘乇丘九") (ℓ "九丘乇丘") tt tt Eq.refl
wn00282 : Base 3 → ⟪ (ℓ "乕丼") ⟫ʷ ≈ ⟪ (ℓ "丼乘") ⟫ʷ
wn00282 b = lw0 b (ℓ "乕丼") (ℓ "丼乘") tt tt Eq.refl
wn00283 : Base 3 → ⟪ (ℓ "乘丼") ⟫ʷ ≈ ⟪ (ℓ "丼乕") ⟫ʷ
wn00283 b = lw0 b (ℓ "乘丼") (ℓ "丼乕") tt tt Eq.refl
wn00284 : Base 3 → ⟪ (ℓ "丘么丘九") ⟫ʷ ≈ ⟪ (ℓ "九丘么丘") ⟫ʷ
wn00284 b = lw3 b (ℓ "丘么丘九") (ℓ "九丘么丘") tt tt Eq.refl
wn00285 : Base 3 → ⟪ (ℓ "丘丷丘九") ⟫ʷ ≈ ⟪ (ℓ "九丘丷丘") ⟫ʷ
wn00285 b = lw3 b (ℓ "丘丷丘九") (ℓ "九丘丷丘") tt tt Eq.refl
wn00286 : Base 3 → ⟪ (ℓ "丧丧") ⟫ʷ ≈ ⟪ (ℓ "丧丧") ⟫ʷ
wn00286 b = lw3 b (ℓ "丧丧") (ℓ "丧丧") tt tt Eq.refl
wn00287 : Base 3 → ⟪ (ℓ "丘丷丘丽") ⟫ʷ ≈ ⟪ (ℓ "丽丘丷丘") ⟫ʷ
wn00287 b = lw0 b (ℓ "丘丷丘丽") (ℓ "丽丘丷丘") tt tt Eq.refl
wn00288 : Base 3 → ⟪ (ℓ "丘丷丘举") ⟫ʷ ≈ ⟪ (ℓ "举丘丷丘") ⟫ʷ
wn00288 b = lw0 b (ℓ "丘丷丘举") (ℓ "举丘丷丘") tt tt Eq.refl
wn00289 : Base 3 → ⟪ (ℓ "九与") ⟫ʷ ≈ ⟪ (ℓ "与九") ⟫ʷ
wn00289 b = lw3 b (ℓ "九与") (ℓ "与九") tt tt Eq.refl
wn00290 : Base 3 → ⟪ (ℓ "九丏") ⟫ʷ ≈ ⟪ (ℓ "丏九") ⟫ʷ
wn00290 b = lw3 b (ℓ "九丏") (ℓ "丏九") tt tt Eq.refl
wn00291 : Base 3 → ⟪ (ℓ "丨与") ⟫ʷ ≈ ⟪ (ℓ "与丨") ⟫ʷ
wn00291 b = lw3 b (ℓ "丨与") (ℓ "与丨") tt tt Eq.refl
wn00292 : Base 3 → ⟪ (ℓ "丨丏") ⟫ʷ ≈ ⟪ (ℓ "丏丨") ⟫ʷ
wn00292 b = lw3 b (ℓ "丨丏") (ℓ "丏丨") tt tt Eq.refl
wn00293 : Base 3 → ⟪ (ℓ "习丨") ⟫ʷ ≈ ⟪ (ℓ "丨习") ⟫ʷ
wn00293 b = lw3 b (ℓ "习丨") (ℓ "丨习") tt tt Eq.refl
wn00294 : Base 3 → ⟪ (ℓ "丈丶") ⟫ʷ ≈ ⟪ (ℓ "丶丈") ⟫ʷ
wn00294 b = lw3 b (ℓ "丈丶") (ℓ "丶丈") tt tt Eq.refl
wn00295 : Base 3 → ⟪ (ℓ "丈丷") ⟫ʷ ≈ ⟪ (ℓ "丷丈") ⟫ʷ
wn00295 b = lw3 b (ℓ "丈丷") (ℓ "丷丈") tt tt Eq.refl
wn00296 : Base 3 → ⟪ (ℓ "丒丠丒九") ⟫ʷ ≈ ⟪ (ℓ "九丒丠丒") ⟫ʷ
wn00296 b = lw3 b (ℓ "丒丠丒九") (ℓ "九丒丠丒") tt tt Eq.refl
wn00297 : Base 3 → ⟪ (ℓ "丒丠丒丧") ⟫ʷ ≈ ⟪ (ℓ "丧丒丠丒") ⟫ʷ
wn00297 b = lw3 b (ℓ "丒丠丒丧") (ℓ "丧丒丠丒") tt tt Eq.refl
wn00298 : Base 3 → ⟪ (ℓ "丒丠丒丨") ⟫ʷ ≈ ⟪ (ℓ "丨丒丠丒") ⟫ʷ
wn00298 b = lw3 b (ℓ "丒丠丒丨") (ℓ "丨丒丠丒") tt tt Eq.refl
wn00299 : Base 3 → ⟪ (ℓ "丶丘习丘") ⟫ʷ ≈ ⟪ (ℓ "丘习丘丶") ⟫ʷ
wn00299 b = lw3 b (ℓ "丶丘习丘") (ℓ "丘习丘丶") tt tt Eq.refl
wn00300 : Base 3 → ⟪ (ℓ "丷丘习丘") ⟫ʷ ≈ ⟪ (ℓ "丘习丘丷") ⟫ʷ
wn00300 b = lw3 b (ℓ "丷丘习丘") (ℓ "丘习丘丷") tt tt Eq.refl
wn00301 : Base 3 → ⟪ (ℓ "乙丩") ⟫ʷ ≈ ⟪ (ℓ "丩乙") ⟫ʷ
wn00301 b = lw3 b (ℓ "乙丩") (ℓ "丩乙") tt tt Eq.refl
wn00302 : Base 3 → ⟪ (ℓ "丶丩") ⟫ʷ ≈ ⟪ (ℓ "丩丶") ⟫ʷ
wn00302 b = lw3 b (ℓ "丶丩") (ℓ "丩丶") tt tt Eq.refl
wn00303 : Base 3 → ⟪ (ℓ "丷丩") ⟫ʷ ≈ ⟪ (ℓ "丩丷") ⟫ʷ
wn00303 b = lw3 b (ℓ "丷丩") (ℓ "丩丷") tt tt Eq.refl
wn00304 : Base 3 → ⟪ (ℓ "丘丷丘习") ⟫ʷ ≈ ⟪ (ℓ "习丘丷丘") ⟫ʷ
wn00304 b = lw3 b (ℓ "丘丷丘习") (ℓ "习丘丷丘") tt tt Eq.refl
wn00305 : Base 3 → ⟪ (ℓ "习丘习丘") ⟫ʷ ≈ ⟪ (ℓ "丘习丘习") ⟫ʷ
wn00305 b = lw3 b (ℓ "习丘习丘") (ℓ "丘习丘习") tt tt Eq.refl
wn00306 : Base 3 → ⟪ (ℓ "与丽") ⟫ʷ ≈ ⟪ (ℓ "丽与") ⟫ʷ
wn00306 b = lw0 b (ℓ "与丽") (ℓ "丽与") tt tt Eq.refl
wn00307 : Base 3 → ⟪ (ℓ "与举") ⟫ʷ ≈ ⟪ (ℓ "举与") ⟫ʷ
wn00307 b = lw0 b (ℓ "与举") (ℓ "举与") tt tt Eq.refl
wn00308 : Base 3 → ⟪ (ℓ "丏丽") ⟫ʷ ≈ ⟪ (ℓ "丽丏") ⟫ʷ
wn00308 b = lw0 b (ℓ "丏丽") (ℓ "丽丏") tt tt Eq.refl
wn00309 : Base 3 → ⟪ (ℓ "丏举") ⟫ʷ ≈ ⟪ (ℓ "举丏") ⟫ʷ
wn00309 b = lw0 b (ℓ "丏举") (ℓ "举丏") tt tt Eq.refl
wn00310 : Base 3 → ⟪ (ℓ "丧丧丧") ⟫ʷ ≈ ⟪ (ℓ "丨") ⟫ʷ
wn00310 b = lw3 b (ℓ "丧丧丧") (ℓ "丨") tt tt Eq.refl
wn00311 : Base 3 → ⟪ (ℓ "並丈") ⟫ʷ ≈ ⟪ (ℓ "与並") ⟫ʷ
wn00311 b = lw3 b (ℓ "並丈") (ℓ "与並") tt tt Eq.refl
wn00312 : Base 3 → ⟪ (ℓ "並三") ⟫ʷ ≈ ⟪ (ℓ "丏並") ⟫ʷ
wn00312 b = lw3 b (ℓ "並三") (ℓ "丏並") tt tt Eq.refl
wn00313 : Base 3 → ⟪ (ℓ "並下") ⟫ʷ ≈ ⟪ (ℓ "丑並") ⟫ʷ
wn00313 b = lw3 b (ℓ "並下") (ℓ "丑並") tt tt Eq.refl
wn00314 : Base 3 → ⟪ (ℓ "並不") ⟫ʷ ≈ ⟪ (ℓ "专並") ⟫ʷ
wn00314 b = lw3 b (ℓ "並不") (ℓ "专並") tt tt Eq.refl
wn00315 : Base 3 → ⟪ (ℓ "並与") ⟫ʷ ≈ ⟪ (ℓ "丈並") ⟫ʷ
wn00315 b = lw3 b (ℓ "並与") (ℓ "丈並") tt tt Eq.refl
wn00316 : Base 3 → ⟪ (ℓ "並丏") ⟫ʷ ≈ ⟪ (ℓ "三並") ⟫ʷ
wn00316 b = lw3 b (ℓ "並丏") (ℓ "三並") tt tt Eq.refl
wn00317 : Base 3 → ⟪ (ℓ "並丒") ⟫ʷ ≈ ⟪ (ℓ "丌並") ⟫ʷ
wn00317 b = lw3 b (ℓ "並丒") (ℓ "丌並") tt tt Eq.refl
wn00318 : Base 3 → ⟪ (ℓ "並专") ⟫ʷ ≈ ⟪ (ℓ "不並") ⟫ʷ
wn00318 b = lw3 b (ℓ "並专") (ℓ "不並") tt tt Eq.refl
wn00319 : Base 3 → ⟪ (ℓ "並両") ⟫ʷ ≈ ⟪ (ℓ "両並") ⟫ʷ
wn00319 b = lw3 b (ℓ "並両") (ℓ "両並") tt tt Eq.refl
wn00320 : Base 3 → ⟪ (ℓ "並丢") ⟫ʷ ≈ ⟪ (ℓ "丢並") ⟫ʷ
wn00320 b = lw3 b (ℓ "並丢") (ℓ "丢並") tt tt Eq.refl
wn00321 : Base 3 → ⟪ (ℓ "並严") ⟫ʷ ≈ ⟪ (ℓ "丵並") ⟫ʷ
wn00321 b = lw3 b (ℓ "並严") (ℓ "丵並") tt tt Eq.refl
wn00322 : Base 3 → ⟪ (ℓ "並丨") ⟫ʷ ≈ ⟪ (ℓ "丷並") ⟫ʷ
wn00322 b = lw3 b (ℓ "並丨") (ℓ "丷並") tt tt Eq.refl
wn00323 : Base 3 → ⟪ (ℓ "並丩") ⟫ʷ ≈ ⟪ (ℓ "丸並") ⟫ʷ
wn00323 b = lw3 b (ℓ "並丩") (ℓ "丸並") tt tt Eq.refl
wn00324 : Base 3 → ⟪ (ℓ "並丫") ⟫ʷ ≈ ⟪ (ℓ "为並") ⟫ʷ
wn00324 b = lw3 b (ℓ "並丫") (ℓ "为並") tt tt Eq.refl
wn00325 : Base 3 → ⟪ (ℓ "並丬") ⟫ʷ ≈ ⟪ (ℓ "主並") ⟫ʷ
wn00325 b = lw3 b (ℓ "並丬") (ℓ "主並") tt tt Eq.refl
wn00326 : Base 3 → ⟪ (ℓ "並丳") ⟫ʷ ≈ ⟪ (ℓ "丣並") ⟫ʷ
wn00326 b = lw3 b (ℓ "並丳") (ℓ "丣並") tt tt Eq.refl
wn00327 : Base 3 → ⟪ (ℓ "並临") ⟫ʷ ≈ ⟪ (ℓ "两並") ⟫ʷ
wn00327 b = lw3 b (ℓ "並临") (ℓ "两並") tt tt Eq.refl
wn00328 : Base 3 → ⟪ (ℓ "並丵") ⟫ʷ ≈ ⟪ (ℓ "严並") ⟫ʷ
wn00328 b = lw3 b (ℓ "並丵") (ℓ "严並") tt tt Eq.refl
wn00329 : Base 3 → ⟪ (ℓ "並为") ⟫ʷ ≈ ⟪ (ℓ "丫並") ⟫ʷ
wn00329 b = lw3 b (ℓ "並为") (ℓ "丫並") tt tt Eq.refl
wn00330 : Base 3 → ⟪ (ℓ "並主") ⟫ʷ ≈ ⟪ (ℓ "丬並") ⟫ʷ
wn00330 b = lw3 b (ℓ "並主") (ℓ "丬並") tt tt Eq.refl
wn00331 : Base 3 → ⟪ (ℓ "並乃") ⟫ʷ ≈ ⟪ (ℓ "乆並") ⟫ʷ
wn00331 b = lw3 b (ℓ "並乃") (ℓ "乆並") tt tt Eq.refl
wn00332 : Base 3 → ⟪ (ℓ "並久") ⟫ʷ ≈ ⟪ (ℓ "么並") ⟫ʷ
wn00332 b = lw3 b (ℓ "並久") (ℓ "么並") tt tt Eq.refl
wn00333 : Base 3 → ⟪ (ℓ "世丧丳丨丳丶世丁") ⟫ʷ ≈ ⟪ (ℓ "世丶丣丷丣丧世一") ⟫ʷ
wn00333 b = lw3 b (ℓ "世丧丳丨丳丶世丁") (ℓ "世丶丣丷丣丧世一") tt tt Eq.refl
wn00334 : Base 3 → ⟪ (ℓ "世义丹乊丹丽世丁") ⟫ʷ ≈ ⟪ (ℓ "世义丹乊丹丽世丁") ⟫ʷ
wn00334 b = lw0 b (ℓ "世义丹乊丹丽世丁") (ℓ "世义丹乊丹丽世丁") tt tt Eq.refl
wn00335 : Base 3 → ⟪ (ℓ "乏世") ⟫ʷ ≈ ⟪ (ℓ "东乏") ⟫ʷ
wn00335 b = lw0 b (ℓ "乏世") (ℓ "东乏") tt tt Eq.refl
wn00336 : Base 3 → ⟪ (ℓ "乏东") ⟫ʷ ≈ ⟪ (ℓ "世乏") ⟫ʷ
wn00336 b = lw0 b (ℓ "乏东") (ℓ "世乏") tt tt Eq.refl
wn00337 : Base 3 → ⟪ (ℓ "东义丹乊丹丽东丁") ⟫ʷ ≈ ⟪ (ℓ "东义丹乊丹丽东丁") ⟫ʷ
wn00337 b = lw0 b (ℓ "东义丹乊丹丽东丁") (ℓ "东义丹乊丹丽东丁") tt tt Eq.refl
wn00338 : Base 3 → ⟪ (ℓ "丼与") ⟫ʷ ≈ ⟪ (ℓ "且丼") ⟫ʷ
wn00338 b = lw3 b (ℓ "丼与") (ℓ "且丼") tt tt Eq.refl
wn00339 : Base 3 → ⟪ (ℓ "丼丏") ⟫ʷ ≈ ⟪ (ℓ "丕丼") ⟫ʷ
wn00339 b = lw3 b (ℓ "丼丏") (ℓ "丕丼") tt tt Eq.refl
wn00340 : Base 3 → ⟪ (ℓ "丼丐") ⟫ʷ ≈ ⟪ (ℓ "世丼") ⟫ʷ
wn00340 b = lw3 b (ℓ "丼丐") (ℓ "世丼") tt tt Eq.refl
wn00341 : Base 3 → ⟪ (ℓ "丼丑") ⟫ʷ ≈ ⟪ (ℓ "丗丼") ⟫ʷ
wn00341 b = lw3 b (ℓ "丼丑") (ℓ "丗丼") tt tt Eq.refl
wn00342 : Base 3 → ⟪ (ℓ "丼专") ⟫ʷ ≈ ⟪ (ℓ "丙丼") ⟫ʷ
wn00342 b = lw3 b (ℓ "丼专") (ℓ "丙丼") tt tt Eq.refl
wn00343 : Base 3 → ⟪ (ℓ "丼且") ⟫ʷ ≈ ⟪ (ℓ "与丼") ⟫ʷ
wn00343 b = lw3 b (ℓ "丼且") (ℓ "与丼") tt tt Eq.refl
wn00344 : Base 3 → ⟪ (ℓ "丼丕") ⟫ʷ ≈ ⟪ (ℓ "丏丼") ⟫ʷ
wn00344 b = lw3 b (ℓ "丼丕") (ℓ "丏丼") tt tt Eq.refl
wn00345 : Base 3 → ⟪ (ℓ "丼世") ⟫ʷ ≈ ⟪ (ℓ "丐丼") ⟫ʷ
wn00345 b = lw3 b (ℓ "丼世") (ℓ "丐丼") tt tt Eq.refl
wn00346 : Base 3 → ⟪ (ℓ "丼丗") ⟫ʷ ≈ ⟪ (ℓ "丑丼") ⟫ʷ
wn00346 b = lw3 b (ℓ "丼丗") (ℓ "丑丼") tt tt Eq.refl
wn00347 : Base 3 → ⟪ (ℓ "丼丘") ⟫ʷ ≈ ⟪ (ℓ "丒丼") ⟫ʷ
wn00347 b = lw3 b (ℓ "丼丘") (ℓ "丒丼") tt tt Eq.refl
wn00348 : Base 3 → ⟪ (ℓ "丼丙") ⟫ʷ ≈ ⟪ (ℓ "专丼") ⟫ʷ
wn00348 b = lw3 b (ℓ "丼丙") (ℓ "专丼") tt tt Eq.refl
wn00349 : Base 3 → ⟪ (ℓ "丼丸") ⟫ʷ ≈ ⟪ (ℓ "丸丼") ⟫ʷ
wn00349 b = lw3 b (ℓ "丼丸") (ℓ "丸丼") tt tt Eq.refl
wn00350 : Base 3 → ⟪ (ℓ "丼为") ⟫ʷ ≈ ⟪ (ℓ "乇丼") ⟫ʷ
wn00350 b = lw3 b (ℓ "丼为") (ℓ "乇丼") tt tt Eq.refl
wn00351 : Base 3 → ⟪ (ℓ "丼主") ⟫ʷ ≈ ⟪ (ℓ "么丼") ⟫ʷ
wn00351 b = lw3 b (ℓ "丼主") (ℓ "么丼") tt tt Eq.refl
wn00352 : Base 3 → ⟪ (ℓ "丼乁") ⟫ʷ ≈ ⟪ (ℓ "乍丼") ⟫ʷ
wn00352 b = lw0 b (ℓ "丼乁") (ℓ "乍丼") tt tt Eq.refl
wn00353 : Base 3 → ⟪ (ℓ "丼乂") ⟫ʷ ≈ ⟪ (ℓ "乎丼") ⟫ʷ
wn00353 b = lw0 b (ℓ "丼乂") (ℓ "乎丼") tt tt Eq.refl
wn00354 : Base 3 → ⟪ (ℓ "丼乆") ⟫ʷ ≈ ⟪ (ℓ "丹丼") ⟫ʷ
wn00354 b = lw3 b (ℓ "丼乆") (ℓ "丹丼") tt tt Eq.refl
wn00355 : Base 3 → ⟪ (ℓ "丼乇") ⟫ʷ ≈ ⟪ (ℓ "为丼") ⟫ʷ
wn00355 b = lw3 b (ℓ "丼乇") (ℓ "为丼") tt tt Eq.refl
wn00356 : Base 3 → ⟪ (ℓ "丼么") ⟫ʷ ≈ ⟪ (ℓ "主丼") ⟫ʷ
wn00356 b = lw3 b (ℓ "丼么") (ℓ "主丼") tt tt Eq.refl
wn00357 : Base 3 → ⟪ (ℓ "丼乍") ⟫ʷ ≈ ⟪ (ℓ "乁丼") ⟫ʷ
wn00357 b = lw0 b (ℓ "丼乍") (ℓ "乁丼") tt tt Eq.refl
wn00358 : Base 3 → ⟪ (ℓ "丼乎") ⟫ʷ ≈ ⟪ (ℓ "乂丼") ⟫ʷ
wn00358 b = lw0 b (ℓ "丼乎") (ℓ "乂丼") tt tt Eq.refl
wn00359 : Base 3 → ⟪ (ℓ "丼乔") ⟫ʷ ≈ ⟪ (ℓ "乗丼") ⟫ʷ
wn00359 b = lw0 b (ℓ "丼乔") (ℓ "乗丼") tt tt Eq.refl
wn00360 : Base 3 → ⟪ (ℓ "丼乕") ⟫ʷ ≈ ⟪ (ℓ "乘丼") ⟫ʷ
wn00360 b = lw0 b (ℓ "丼乕") (ℓ "乘丼") tt tt Eq.refl
wn00361 : Base 3 → ⟪ (ℓ "丼乗") ⟫ʷ ≈ ⟪ (ℓ "乔丼") ⟫ʷ
wn00361 b = lw0 b (ℓ "丼乗") (ℓ "乔丼") tt tt Eq.refl
wn00362 : Base 3 → ⟪ (ℓ "丼乘") ⟫ʷ ≈ ⟪ (ℓ "乕丼") ⟫ʷ
wn00362 b = lw0 b (ℓ "丼乘") (ℓ "乕丼") tt tt Eq.refl
wn00363 : Base 3 → ⟪ (ℓ "世丶个丷个丠世一") ⟫ʷ ≈ ⟪ (ℓ "世丶丣丷丣丧世一") ⟫ʷ
wn00363 b = lw3 b (ℓ "世丶个丷个丠世一") (ℓ "世丶丣丷丣丧世一") tt tt Eq.refl
wn00364 : Base 3 → ⟪ (ℓ "丼丁") ⟫ʷ ≈ ⟪ (ℓ "丂丼") ⟫ʷ
wn00364 b = lw3 b (ℓ "丼丁") (ℓ "丂丼") tt tt Eq.refl
wn00365 : Base 3 → ⟪ (ℓ "世丽乆举乆义世丂") ⟫ʷ ≈ ⟪ (ℓ "世义丹乊丹丽世丁") ⟫ʷ
wn00365 b = lw0 b (ℓ "世丽乆举乆义世丂") (ℓ "世义丹乊丹丽世丁") tt tt Eq.refl
wn00366 : Base 3 → ⟪ (ℓ "丐丶个丷个丠丐一") ⟫ʷ ≈ ⟪ (ℓ "丐丶丣丷丣丧丐一") ⟫ʷ
wn00366 b = lw3 b (ℓ "丐丶个丷个丠丐一") (ℓ "丐丶丣丷丣丧丐一") tt tt Eq.refl
wn00367 : Base 3 → ⟪ (ℓ "丐丽乆举乆义丐丂") ⟫ʷ ≈ ⟪ (ℓ "丐义丹乊丹丽丐丁") ⟫ʷ
wn00367 b = lw0 b (ℓ "丐丽乆举乆义丐丂") (ℓ "丐义丹乊丹丽丐丁") tt tt Eq.refl
wn00368 : Base 3 → ⟪ (ℓ "世丶丣丷丣丧世一") ⟫ʷ ≈ ⟪ (ℓ "世丶丣丷丣丧世一") ⟫ʷ
wn00368 b = lw3 b (ℓ "世丶丣丷丣丧世一") (ℓ "世丶丣丷丣丧世一") tt tt Eq.refl
wn00369 : Base 3 → ⟪ (ℓ "东丽乆举乆义东丂") ⟫ʷ ≈ ⟪ (ℓ "东义丹乊丹丽东丁") ⟫ʷ
wn00369 b = lw0 b (ℓ "东丽乆举乆义东丂") (ℓ "东义丹乊丹丽东丁") tt tt Eq.refl
wn00370 : Base 3 → ⟪ (ℓ "乏丗") ⟫ʷ ≈ ⟪ (ℓ "丝乏") ⟫ʷ
wn00370 b = lw0 b (ℓ "乏丗") (ℓ "丝乏") tt tt Eq.refl
wn00371 : Base 3 → ⟪ (ℓ "乏丙") ⟫ʷ ≈ ⟪ (ℓ "丟乏") ⟫ʷ
wn00371 b = lw0 b (ℓ "乏丙") (ℓ "丟乏") tt tt Eq.refl
wn00372 : Base 3 → ⟪ (ℓ "乏业") ⟫ʷ ≈ ⟪ (ℓ "且乏") ⟫ʷ
wn00372 b = lw0 b (ℓ "乏业") (ℓ "且乏") tt tt Eq.refl
wn00373 : Base 3 → ⟪ (ℓ "乏丛") ⟫ʷ ≈ ⟪ (ℓ "丕乏") ⟫ʷ
wn00373 b = lw0 b (ℓ "乏丛") (ℓ "丕乏") tt tt Eq.refl
wn00374 : Base 3 → ⟪ (ℓ "乏丝") ⟫ʷ ≈ ⟪ (ℓ "丗乏") ⟫ʷ
wn00374 b = lw0 b (ℓ "乏丝") (ℓ "丗乏") tt tt Eq.refl
wn00375 : Base 3 → ⟪ (ℓ "乏丞") ⟫ʷ ≈ ⟪ (ℓ "丘乏") ⟫ʷ
wn00375 b = lw0 b (ℓ "乏丞") (ℓ "丘乏") tt tt Eq.refl
wn00376 : Base 3 → ⟪ (ℓ "乏丟") ⟫ʷ ≈ ⟪ (ℓ "丙乏") ⟫ʷ
wn00376 b = lw0 b (ℓ "乏丟") (ℓ "丙乏") tt tt Eq.refl
wn00377 : Base 3 → ⟪ (ℓ "乏之") ⟫ʷ ≈ ⟪ (ℓ "之乏") ⟫ʷ
wn00377 b = lw0 b (ℓ "乏之") (ℓ "之乏") tt tt Eq.refl
wn00378 : Base 3 → ⟪ (ℓ "乏乌") ⟫ʷ ≈ ⟪ (ℓ "乖乏") ⟫ʷ
wn00378 b = lw0 b (ℓ "乏乌") (ℓ "乖乏") tt tt Eq.refl
wn00379 : Base 3 → ⟪ (ℓ "乏乍") ⟫ʷ ≈ ⟪ (ℓ "乗乏") ⟫ʷ
wn00379 b = lw0 b (ℓ "乏乍") (ℓ "乗乏") tt tt Eq.refl
wn00380 : Base 3 → ⟪ (ℓ "乏乎") ⟫ʷ ≈ ⟪ (ℓ "乘乏") ⟫ʷ
wn00380 b = lw0 b (ℓ "乏乎") (ℓ "乘乏") tt tt Eq.refl
wn00381 : Base 3 → ⟪ (ℓ "乏乖") ⟫ʷ ≈ ⟪ (ℓ "乌乏") ⟫ʷ
wn00381 b = lw0 b (ℓ "乏乖") (ℓ "乌乏") tt tt Eq.refl
wn00382 : Base 3 → ⟪ (ℓ "乏乗") ⟫ʷ ≈ ⟪ (ℓ "乍乏") ⟫ʷ
wn00382 b = lw0 b (ℓ "乏乗") (ℓ "乍乏") tt tt Eq.refl
wn00383 : Base 3 → ⟪ (ℓ "乏乘") ⟫ʷ ≈ ⟪ (ℓ "乎乏") ⟫ʷ
wn00383 b = lw0 b (ℓ "乏乘") (ℓ "乎乏") tt tt Eq.refl
wn00384 : Base 3 → ⟪ (ℓ "丐义乀乊乀丶丐丁") ⟫ʷ ≈ ⟪ (ℓ "丐义丹乊丹丽丐丁") ⟫ʷ
wn00384 b = lw0 b (ℓ "丐义乀乊乀丶丐丁") (ℓ "丐义丹乊丹丽丐丁") tt tt Eq.refl
wn00385 : Base 3 → ⟪ (ℓ "东义乀乊乀丶东丁") ⟫ʷ ≈ ⟪ (ℓ "东义丹乊丹丽东丁") ⟫ʷ
wn00385 b = lw0 b (ℓ "东义乀乊乀丶东丁") (ℓ "东义丹乊丹丽东丁") tt tt Eq.refl
wn00386 : Base 3 → ⟪ (ℓ "世义乀乊乀丶世丁") ⟫ʷ ≈ ⟪ (ℓ "世义丹乊丹丽世丁") ⟫ʷ
wn00386 b = lw0 b (ℓ "世义乀乊乀丶世丁") (ℓ "世义丹乊丹丽世丁") tt tt Eq.refl
wn00387 : Base 3 → ⟪ (ℓ "丌丌") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00387 b = lw3 b (ℓ "丌丌") [] tt tt Eq.refl
wn00388 : Base 3 → ⟪ (ℓ "丒丒") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00388 b = lw3 b (ℓ "丒丒") [] tt tt Eq.refl
wn00389 : Base 3 → ⟪ (ℓ "丘丘") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00389 b = lw3 b (ℓ "丘丘") [] tt tt Eq.refl
wn00390 : Base 3 → ⟪ (ℓ "丞丞") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wn00390 b = lw0 b (ℓ "丞丞") [] tt tt Eq.refl
wn00391 : Base 3 → ⟪ (ℓ "丌丈上") ⟫ʷ ≈ ⟪ (ℓ "三下丈丈") ⟫ʷ
wn00391 b = lw3 b (ℓ "丌丈上") (ℓ "三下丈丈") tt tt Eq.refl
wn00392 : Base 3 → ⟪ (ℓ "下三丌") ⟫ʷ ≈ ⟪ (ℓ "三三上丈") ⟫ʷ
wn00392 b = lw3 b (ℓ "下三丌") (ℓ "三三上丈") tt tt Eq.refl
wn00393 : Base 3 → ⟪ (ℓ "丘且世") ⟫ʷ ≈ ⟪ (ℓ "丕丗且且") ⟫ʷ
wn00393 b = lw3 b (ℓ "丘且世") (ℓ "丕丗且且") tt tt Eq.refl
wn00394 : Base 3 → ⟪ (ℓ "丗丕丘") ⟫ʷ ≈ ⟪ (ℓ "丕丕世且") ⟫ʷ
wn00394 b = lw3 b (ℓ "丗丕丘") (ℓ "丕丕世且") tt tt Eq.refl
wn00395 : Base 3 → ⟪ (ℓ "丞义丞乥") ⟫ʷ ≈ ⟪ (ℓ "乥丞义丞") ⟫ʷ
wn00395 b = lw0 b (ℓ "丞义丞乥") (ℓ "乥丞义丞") tt tt Eq.refl
wn00396 : Base 3 → ⟪ (ℓ "丞义丞丶") ⟫ʷ ≈ ⟪ (ℓ "丶丞义丞") ⟫ʷ
wn00396 b = lw0 b (ℓ "丞义丞丶") (ℓ "丶丞义丞") tt tt Eq.refl
wn00397 : Base 3 → ⟪ (ℓ "丞义丞丷") ⟫ʷ ≈ ⟪ (ℓ "丷丞义丞") ⟫ʷ
wn00397 b = lw0 b (ℓ "丞义丞丷") (ℓ "丷丞义丞") tt tt Eq.refl
wn00398 : Base 3 → ⟪ (ℓ "世丼") ⟫ʷ ≈ ⟪ (ℓ "丼丐") ⟫ʷ
wn00398 b = lw3 b (ℓ "世丼") (ℓ "丼丐") tt tt Eq.refl
wn00399 : Base 3 → ⟪ (ℓ "丞乗丞乊") ⟫ʷ ≈ ⟪ (ℓ "乊丞乗丞") ⟫ʷ
wn00399 b = lw0 b (ℓ "丞乗丞乊") (ℓ "乊丞乗丞") tt tt Eq.refl
wn00400 : Base 3 → ⟪ (ℓ "丞乊丞乥") ⟫ʷ ≈ ⟪ (ℓ "乥丞乊丞") ⟫ʷ
wn00400 b = lw0 b (ℓ "丞乊丞乥") (ℓ "乥丞乊丞") tt tt Eq.refl
wn00401 : Base 3 → ⟪ (ℓ "丞乊丞丶") ⟫ʷ ≈ ⟪ (ℓ "丶丞乊丞") ⟫ʷ
wn00401 b = lw0 b (ℓ "丞乊丞丶") (ℓ "丶丞乊丞") tt tt Eq.refl
wn00402 : Base 3 → ⟪ (ℓ "丞乊丞丷") ⟫ʷ ≈ ⟪ (ℓ "丷丞乊丞") ⟫ʷ
wn00402 b = lw0 b (ℓ "丞乊丞丷") (ℓ "丷丞乊丞") tt tt Eq.refl
wn00403 : Base 3 → ⟪ (ℓ "丞乊丞乢") ⟫ʷ ≈ ⟪ (ℓ "乢丞乊丞") ⟫ʷ
wn00403 b = lw0 b (ℓ "丞乊丞乢") (ℓ "乢丞乊丞") tt tt Eq.refl
wn00404 : Base 3 → ⟪ (ℓ "丞乘丞乢") ⟫ʷ ≈ ⟪ (ℓ "乢丞乘丞") ⟫ʷ
wn00404 b = lw0 b (ℓ "丞乘丞乢") (ℓ "乢丞乘丞") tt tt Eq.refl
wn00405 : Base 3 → ⟪ (ℓ "丞义丞乢") ⟫ʷ ≈ ⟪ (ℓ "乢丞义丞") ⟫ʷ
wn00405 b = lw0 b (ℓ "丞义丞乢") (ℓ "乢丞义丞") tt tt Eq.refl
wn00406 : Base 3 → ⟪ (ℓ "丶义") ⟫ʷ ≈ ⟪ (ℓ "义丶") ⟫ʷ
wn00406 b = lw0 b (ℓ "丶义") (ℓ "义丶") tt tt Eq.refl
wn00407 : Base 3 → ⟪ (ℓ "乆义") ⟫ʷ ≈ ⟪ (ℓ "义乆") ⟫ʷ
wn00407 b = lw0 b (ℓ "乆义") (ℓ "义乆") tt tt Eq.refl
wn00408 : Base 3 → ⟪ (ℓ "义丈") ⟫ʷ ≈ ⟪ (ℓ "丈义") ⟫ʷ
wn00408 b = lw1 b (ℓ "义丈") (ℓ "丈义") tt tt Eq.refl
