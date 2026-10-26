------------------------------------------------------------------------
-- Presentations of groups
--
-- Windows of the five-wire derivations (literal)
--
-- Each distinct window of the derivations of Five.D, evaluated once
-- (Five.Win).  Written by `scratchpad/five/winlib5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Wins.WL02 where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()

open import Examples.Groups.Clifford+CS.Windows using (Base)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)

wl0247 : Base 4 → ⟪ (ℓ "乇云") ⟫ʷ ≈ ⟪ (ℓ "云乇") ⟫ʷ
wl0247 c4 = lw4 c4 (ℓ "乇云") (ℓ "云乇") tt tt Eq.refl

wl0248 : Base 4 → ⟪ (ℓ "亰亭乇乢亰") ⟫ʷ ≈ ⟪ (ℓ "亭乇乢") ⟫ʷ
wl0248 c4 = lw0 c4 (ℓ "亰亭乇乢亰") (ℓ "亭乇乢") tt tt Eq.refl

wl0249 : Base 4 → ⟪ (ℓ "乢") ⟫ʷ ≈ ⟪ (ℓ "亭乇乢亰亭么亭乇亭么") ⟫ʷ
wl0249 c4 = lw0 c4 (ℓ "乢") (ℓ "亭乇乢亰亭么亭乇亭么") tt tt Eq.refl

wl0250 : Base 4 → ⟪ (ℓ "乶亍") ⟫ʷ ≈ ⟪ (ℓ "亍乶云") ⟫ʷ
wl0250 c4 = lw4 c4 (ℓ "乶亍") (ℓ "亍乶云") tt tt Eq.refl

wl0251 : Base 4 → ⟪ (ℓ "乒亍") ⟫ʷ ≈ ⟪ (ℓ "亍乒") ⟫ʷ
wl0251 c4 = lw4 c4 (ℓ "乒亍") (ℓ "亍乒") tt tt Eq.refl

wl0252 : Base 4 → ⟪ (ℓ "亍云") ⟫ʷ ≈ ⟪ (ℓ "云亍") ⟫ʷ
wl0252 c4 = lw4 c4 (ℓ "亍云") (ℓ "云亍") tt tt Eq.refl

wl0253 : Base 4 → ⟪ (ℓ "乶云云") ⟫ʷ ≈ ⟪ (ℓ "乶") ⟫ʷ
wl0253 c4 = lw4 c4 (ℓ "乶云云") (ℓ "乶") tt tt Eq.refl

wl0254 : Base 4 → ⟪ (ℓ "京") ⟫ʷ ≈ ⟪ (ℓ "乶京乶") ⟫ʷ
wl0254 c4 = lw0 c4 (ℓ "京") (ℓ "乶京乶") tt tt Eq.refl

wl0255 : Base 4 → ⟪ (ℓ "书亍") ⟫ʷ ≈ ⟪ (ℓ "亍书") ⟫ʷ
wl0255 c4 = lw4 c4 (ℓ "书亍") (ℓ "亍书") tt tt Eq.refl

wl0256 : Base 4 → ⟪ (ℓ "亨") ⟫ʷ ≈ ⟪ (ℓ "乩之乪之乕") ⟫ʷ
wl0256 c4 = lw0 c4 (ℓ "亨") (ℓ "乩之乪之乕") tt tt Eq.refl

wl0257 : Base 4 → ⟪ (ℓ "亨") ⟫ʷ ≈ ⟪ (ℓ "书亨书") ⟫ʷ
wl0257 c4 = lw0 c4 (ℓ "亨") (ℓ "书亨书") tt tt Eq.refl

wl0258 : Base 4 → ⟪ (ℓ "书乶书") ⟫ʷ ≈ ⟪ (ℓ "乥") ⟫ʷ
wl0258 c4 = lw4 c4 (ℓ "书乶书") (ℓ "乥") tt tt Eq.refl

wl0259 : Base 4 → ⟪ (ℓ "亨乶") ⟫ʷ ≈ ⟪ (ℓ "乶京亨") ⟫ʷ
wl0259 c4 = lw0 c4 (ℓ "亨乶") (ℓ "乶京亨") tt tt Eq.refl

wl0260 : Base 4 → ⟪ (ℓ "亨书") ⟫ʷ ≈ ⟪ (ℓ "书亨") ⟫ʷ
wl0260 c4 = lw0 c4 (ℓ "亨书") (ℓ "书亨") tt tt Eq.refl

wl0261 : Base 4 → ⟪ (ℓ "京书") ⟫ʷ ≈ ⟪ (ℓ "书亨京") ⟫ʷ
wl0261 c4 = lw0 c4 (ℓ "京书") (ℓ "书亨京") tt tt Eq.refl

wl0262 : Base 4 → ⟪ (ℓ "亨京亨京亨") ⟫ʷ ≈ ⟪ (ℓ "亨") ⟫ʷ
wl0262 c4 = lw0 c4 (ℓ "亨京亨京亨") (ℓ "亨") tt tt Eq.refl

wl0263 : Base 4 → ⟪ (ℓ "亨亨") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0263 c4 = lw0 c4 (ℓ "亨亨") [] tt tt Eq.refl

wl0264 : Base 4 → ⟪ (ℓ "亐乥") ⟫ʷ ≈ ⟪ (ℓ "乥二") ⟫ʷ
wl0264 c4 = lw4 c4 (ℓ "亐乥") (ℓ "乥二") tt tt Eq.refl

wl0265 : Base 4 → ⟪ (ℓ "乥亍") ⟫ʷ ≈ ⟪ (ℓ "云乥") ⟫ʷ
wl0265 c4 = lw4 c4 (ℓ "乥亍") (ℓ "云乥") tt tt Eq.refl

wl0266 : Base 4 → ⟪ (ℓ "二乥") ⟫ʷ ≈ ⟪ (ℓ "乥亐") ⟫ʷ
wl0266 c4 = lw4 c4 (ℓ "二乥") (ℓ "乥亐") tt tt Eq.refl

wl0267 : Base 4 → ⟪ (ℓ "乥互") ⟫ʷ ≈ ⟪ (ℓ "于乥") ⟫ʷ
wl0267 c4 = lw4 c4 (ℓ "乥互") (ℓ "于乥") tt tt Eq.refl

wl0268 : Base 4 → ⟪ (ℓ "二丶") ⟫ʷ ≈ ⟪ (ℓ "丶二") ⟫ʷ
wl0268 c4 = lw4 c4 (ℓ "二丶") (ℓ "丶二") tt tt Eq.refl

wl0269 : Base 4 → ⟪ (ℓ "二") ⟫ʷ ≈ ⟪ (ℓ "亐亓乤亓亐乤") ⟫ʷ
wl0269 c4 = lw4 c4 (ℓ "二") (ℓ "亐亓乤亓亐乤") tt tt Eq.refl

wl0270 : Base 4 → ⟪ (ℓ "二") ⟫ʷ ≈ ⟪ (ℓ "丨也丩也丯") ⟫ʷ
wl0270 c4 = lw4 c4 (ℓ "二") (ℓ "丨也丩也丯") tt tt Eq.refl

wl0271 : Base 4 → ⟪ (ℓ "亨") ⟫ʷ ≈ ⟪ (ℓ "乕也乖也乩") ⟫ʷ
wl0271 c4 = lw0 c4 (ℓ "亨") (ℓ "乕也乖也乩") tt tt Eq.refl

wl0272 : Base 4 → ⟪ (ℓ "亨") ⟫ʷ ≈ ⟪ (ℓ "乒亨乒") ⟫ʷ
wl0272 c4 = lw0 c4 (ℓ "亨") (ℓ "乒亨乒") tt tt Eq.refl

wl0273 : Base 4 → ⟪ (ℓ "乳亍") ⟫ʷ ≈ ⟪ (ℓ "亍乳亙") ⟫ʷ
wl0273 c4 = lw4 c4 (ℓ "乳亍") (ℓ "亍乳亙") tt tt Eq.refl

wl0274 : Base 4 → ⟪ (ℓ "亰") ⟫ʷ ≈ ⟪ (ℓ "乹书乺书乩") ⟫ʷ
wl0274 c4 = lw0 c4 (ℓ "亰") (ℓ "乹书乺书乩") tt tt Eq.refl

wl0275 : Base 4 → ⟪ (ℓ "亍亙") ⟫ʷ ≈ ⟪ (ℓ "亙亍") ⟫ʷ
wl0275 c4 = lw4 c4 (ℓ "亍亙") (ℓ "亙亍") tt tt Eq.refl

wl0276 : Base 4 → ⟪ (ℓ "乳亙亙") ⟫ʷ ≈ ⟪ (ℓ "乳") ⟫ʷ
wl0276 c4 = lw4 c4 (ℓ "乳亙亙") (ℓ "乳") tt tt Eq.refl

wl0277 : Base 4 → ⟪ (ℓ "亰") ⟫ʷ ≈ ⟪ (ℓ "乳亰乳") ⟫ʷ
wl0277 c4 = lw0 c4 (ℓ "亰") (ℓ "乳亰乳") tt tt Eq.refl

wl0278 : Base 4 → ⟪ (ℓ "乒乳乒") ⟫ʷ ≈ ⟪ (ℓ "乑") ⟫ʷ
wl0278 c4 = lw4 c4 (ℓ "乒乳乒") (ℓ "乑") tt tt Eq.refl

wl0279 : Base 4 → ⟪ (ℓ "亨乳") ⟫ʷ ≈ ⟪ (ℓ "乳亰亨") ⟫ʷ
wl0279 c4 = lw0 c4 (ℓ "亨乳") (ℓ "乳亰亨") tt tt Eq.refl

wl0280 : Base 4 → ⟪ (ℓ "亨乒") ⟫ʷ ≈ ⟪ (ℓ "乒亨") ⟫ʷ
wl0280 c4 = lw0 c4 (ℓ "亨乒") (ℓ "乒亨") tt tt Eq.refl

wl0281 : Base 4 → ⟪ (ℓ "亰乒") ⟫ʷ ≈ ⟪ (ℓ "乒亨亰") ⟫ʷ
wl0281 c4 = lw0 c4 (ℓ "亰乒") (ℓ "乒亨亰") tt tt Eq.refl

wl0282 : Base 4 → ⟪ (ℓ "亨亰亨亰亨") ⟫ʷ ≈ ⟪ (ℓ "亨") ⟫ʷ
wl0282 c4 = lw0 c4 (ℓ "亨亰亨亰亨") (ℓ "亨") tt tt Eq.refl

wl0283 : Base 4 → ⟪ (ℓ "亘乑") ⟫ʷ ≈ ⟪ (ℓ "乑二") ⟫ʷ
wl0283 c4 = lw4 c4 (ℓ "亘乑") (ℓ "乑二") tt tt Eq.refl

wl0284 : Base 4 → ⟪ (ℓ "乑亍") ⟫ʷ ≈ ⟪ (ℓ "亙乑") ⟫ʷ
wl0284 c4 = lw4 c4 (ℓ "乑亍") (ℓ "亙乑") tt tt Eq.refl

wl0285 : Base 4 → ⟪ (ℓ "二乑") ⟫ʷ ≈ ⟪ (ℓ "乑亘") ⟫ʷ
wl0285 c4 = lw4 c4 (ℓ "二乑") (ℓ "乑亘") tt tt Eq.refl

wl0286 : Base 4 → ⟪ (ℓ "乑亚") ⟫ʷ ≈ ⟪ (ℓ "亏乑") ⟫ʷ
wl0286 c4 = lw4 c4 (ℓ "乑亚") (ℓ "亏乑") tt tt Eq.refl

wl0287 : Base 4 → ⟪ (ℓ "乑乑") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0287 c4 = lw4 c4 (ℓ "乑乑") [] tt tt Eq.refl

wl0288 : Base 4 → ⟪ (ℓ "二") ⟫ʷ ≈ ⟪ (ℓ "亘些乐些亘乐") ⟫ʷ
wl0288 c4 = lw4 c4 (ℓ "二") (ℓ "亘些乐些亘乐") tt tt Eq.refl

wl0289 : Base 4 → ⟪ (ℓ "亐") ⟫ʷ ≈ ⟪ (ℓ "丶乒丷乒丨") ⟫ʷ
wl0289 c4 = lw4 c4 (ℓ "亐") (ℓ "丶乒丷乒丨") tt tt Eq.refl

wl0290 : Base 4 → ⟪ (ℓ "亐云") ⟫ʷ ≈ ⟪ (ℓ "云亐乐") ⟫ʷ
wl0290 c4 = lw4 c4 (ℓ "亐云") (ℓ "云亐乐") tt tt Eq.refl

wl0291 : Base 4 → ⟪ (ℓ "亐乐云亐") ⟫ʷ ≈ ⟪ (ℓ "云") ⟫ʷ
wl0291 c4 = lw4 c4 (ℓ "亐乐云亐") (ℓ "云") tt tt Eq.refl

wl0292 : Base 4 → ⟪ (ℓ "二亏乤亏二乤") ⟫ʷ ≈ ⟪ (ℓ "亐") ⟫ʷ
wl0292 c4 = lw4 c4 (ℓ "二亏乤亏二乤") (ℓ "亐") tt tt Eq.refl

wl0293 : Base 4 → ⟪ (ℓ "亰") ⟫ʷ ≈ ⟪ (ℓ "乩乽乪乽乢") ⟫ʷ
wl0293 c4 = lw0 c4 (ℓ "亰") (ℓ "乩乽乪乽乢") tt tt Eq.refl

wl0294 : Base 4 → ⟪ (ℓ "二乢") ⟫ʷ ≈ ⟪ (ℓ "乢二") ⟫ʷ
wl0294 c4 = lw4 c4 (ℓ "二乢") (ℓ "乢二") tt tt Eq.refl

wl0295 : Base 4 → ⟪ (ℓ "亰") ⟫ʷ ≈ ⟪ (ℓ "亃亰亃") ⟫ʷ
wl0295 c4 = lw0 c4 (ℓ "亰") (ℓ "亃亰亃") tt tt Eq.refl

wl0296 : Base 4 → ⟪ (ℓ "二云交") ⟫ʷ ≈ ⟪ (ℓ "云二") ⟫ʷ
wl0296 c4 = lw4 c4 (ℓ "二云交") (ℓ "云二") tt tt Eq.refl

wl0297 : Base 4 → ⟪ (ℓ "交") ⟫ʷ ≈ ⟪ (ℓ "乇乳么乳乢") ⟫ʷ
wl0297 c4 = lw4 c4 (ℓ "交") (ℓ "乇乳么乳乢") tt tt Eq.refl

wl0298 : Base 4 → ⟪ (ℓ "二交") ⟫ʷ ≈ ⟪ (ℓ "交二") ⟫ʷ
wl0298 c4 = lw4 c4 (ℓ "二交") (ℓ "交二") tt tt Eq.refl

wl0299 : Base 4 → ⟪ (ℓ "交") ⟫ʷ ≈ ⟪ (ℓ "乙交乙") ⟫ʷ
wl0299 c4 = lw0 c4 (ℓ "交") (ℓ "乙交乙") tt tt Eq.refl

wl0300 : Base 4 → ⟪ (ℓ "亃乙亃") ⟫ʷ ≈ ⟪ (ℓ "乘") ⟫ʷ
wl0300 c4 = lw0 c4 (ℓ "亃乙亃") (ℓ "乘") tt tt Eq.refl

wl0301 : Base 4 → ⟪ (ℓ "亰乙") ⟫ʷ ≈ ⟪ (ℓ "乙交亰") ⟫ʷ
wl0301 c4 = lw0 c4 (ℓ "亰乙") (ℓ "乙交亰") tt tt Eq.refl

wl0302 : Base 4 → ⟪ (ℓ "亰亃") ⟫ʷ ≈ ⟪ (ℓ "亃亰") ⟫ʷ
wl0302 c4 = lw0 c4 (ℓ "亰亃") (ℓ "亃亰") tt tt Eq.refl

wl0303 : Base 4 → ⟪ (ℓ "交亃") ⟫ʷ ≈ ⟪ (ℓ "亃亰交") ⟫ʷ
wl0303 c4 = lw0 c4 (ℓ "交亃") (ℓ "亃亰交") tt tt Eq.refl

wl0304 : Base 4 → ⟪ (ℓ "亰交亰交亰") ⟫ʷ ≈ ⟪ (ℓ "亰") ⟫ʷ
wl0304 c4 = lw0 c4 (ℓ "亰交亰交亰") (ℓ "亰") tt tt Eq.refl

wl0305 : Base 4 → ⟪ (ℓ "亰亰") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0305 c4 = lw0 c4 (ℓ "亰亰") [] tt tt Eq.refl

wl0306 : Base 4 → ⟪ (ℓ "乘乘") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0306 c4 = lw0 c4 (ℓ "乘乘") [] tt tt Eq.refl

wl0307 : Base 4 → ⟪ (ℓ "亘") ⟫ʷ ≈ ⟪ (ℓ "丶书丷书丯") ⟫ʷ
wl0307 c4 = lw4 c4 (ℓ "亘") (ℓ "丶书丷书丯") tt tt Eq.refl

wl0308 : Base 4 → ⟪ (ℓ "亘亙") ⟫ʷ ≈ ⟪ (ℓ "亙亘乤") ⟫ʷ
wl0308 c4 = lw4 c4 (ℓ "亘亙") (ℓ "亙亘乤") tt tt Eq.refl

wl0309 : Base 4 → ⟪ (ℓ "亘乤亙亘") ⟫ʷ ≈ ⟪ (ℓ "亙") ⟫ʷ
wl0309 c4 = lw4 c4 (ℓ "亘乤亙亘") (ℓ "亙") tt tt Eq.refl

wl0310 : Base 4 → ⟪ (ℓ "京") ⟫ʷ ≈ ⟪ (ℓ "乕乽乖乽乎") ⟫ʷ
wl0310 c4 = lw0 c4 (ℓ "京") (ℓ "乕乽乖乽乎") tt tt Eq.refl

wl0311 : Base 4 → ⟪ (ℓ "二乎") ⟫ʷ ≈ ⟪ (ℓ "乎二") ⟫ʷ
wl0311 c4 = lw4 c4 (ℓ "二乎") (ℓ "乎二") tt tt Eq.refl

wl0312 : Base 4 → ⟪ (ℓ "京") ⟫ʷ ≈ ⟪ (ℓ "了京了") ⟫ʷ
wl0312 c4 = lw0 c4 (ℓ "京") (ℓ "了京了") tt tt Eq.refl

wl0313 : Base 4 → ⟪ (ℓ "二亙交") ⟫ʷ ≈ ⟪ (ℓ "亙二") ⟫ʷ
wl0313 c4 = lw4 c4 (ℓ "二亙交") (ℓ "亙二") tt tt Eq.refl

wl0314 : Base 4 → ⟪ (ℓ "交") ⟫ʷ ≈ ⟪ (ℓ "乇乶么乶乎") ⟫ʷ
wl0314 c4 = lw4 c4 (ℓ "交") (ℓ "乇乶么乶乎") tt tt Eq.refl

wl0315 : Base 4 → ⟪ (ℓ "交") ⟫ʷ ≈ ⟪ (ℓ "乭交乭") ⟫ʷ
wl0315 c4 = lw0 c4 (ℓ "交") (ℓ "乭交乭") tt tt Eq.refl

wl0316 : Base 4 → ⟪ (ℓ "了乭了") ⟫ʷ ≈ ⟪ (ℓ "乬") ⟫ʷ
wl0316 c4 = lw0 c4 (ℓ "了乭了") (ℓ "乬") tt tt Eq.refl

wl0317 : Base 4 → ⟪ (ℓ "京乭") ⟫ʷ ≈ ⟪ (ℓ "乭交京") ⟫ʷ
wl0317 c4 = lw0 c4 (ℓ "京乭") (ℓ "乭交京") tt tt Eq.refl

wl0318 : Base 4 → ⟪ (ℓ "京了") ⟫ʷ ≈ ⟪ (ℓ "了京") ⟫ʷ
wl0318 c4 = lw0 c4 (ℓ "京了") (ℓ "了京") tt tt Eq.refl

wl0319 : Base 4 → ⟪ (ℓ "交了") ⟫ʷ ≈ ⟪ (ℓ "了京交") ⟫ʷ
wl0319 c4 = lw0 c4 (ℓ "交了") (ℓ "了京交") tt tt Eq.refl

wl0320 : Base 4 → ⟪ (ℓ "京交京交京") ⟫ʷ ≈ ⟪ (ℓ "京") ⟫ʷ
wl0320 c4 = lw0 c4 (ℓ "京交京交京") (ℓ "京") tt tt Eq.refl

wl0321 : Base 4 → ⟪ (ℓ "京京") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0321 c4 = lw0 c4 (ℓ "京京") [] tt tt Eq.refl

wl0322 : Base 4 → ⟪ (ℓ "乬乬") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0322 c4 = lw0 c4 (ℓ "乬乬") [] tt tt Eq.refl

wl0323 : Base 4 → ⟪ (ℓ "亐") ⟫ʷ ≈ ⟪ (ℓ "丨乳丩乳丶") ⟫ʷ
wl0323 c4 = lw4 c4 (ℓ "亐") (ℓ "丨乳丩乳丶") tt tt Eq.refl

wl0324 : Base 4 → ⟪ (ℓ "亐乢") ⟫ʷ ≈ ⟪ (ℓ "乢亐") ⟫ʷ
wl0324 c4 = lw4 c4 (ℓ "亐乢") (ℓ "乢亐") tt tt Eq.refl

wl0325 : Base 4 → ⟪ (ℓ "亐亍交") ⟫ʷ ≈ ⟪ (ℓ "亍亐") ⟫ʷ
wl0325 c4 = lw4 c4 (ℓ "亐亍交") (ℓ "亍亐") tt tt Eq.refl

wl0326 : Base 4 → ⟪ (ℓ "交") ⟫ʷ ≈ ⟪ (ℓ "乎也乏也乢") ⟫ʷ
wl0326 c4 = lw4 c4 (ℓ "交") (ℓ "乎也乏也乢") tt tt Eq.refl

wl0327 : Base 4 → ⟪ (ℓ "亐交") ⟫ʷ ≈ ⟪ (ℓ "交亐") ⟫ʷ
wl0327 c4 = lw4 c4 (ℓ "亐交") (ℓ "交亐") tt tt Eq.refl

wl0328 : Base 4 → ⟪ (ℓ "二丷") ⟫ʷ ≈ ⟪ (ℓ "丷二") ⟫ʷ
wl0328 c4 = lw4 c4 (ℓ "二丷") (ℓ "丷二") tt tt Eq.refl

wl0329 : Base 4 → ⟪ (ℓ "二乳亘") ⟫ʷ ≈ ⟪ (ℓ "乳二") ⟫ʷ
wl0329 c4 = lw4 c4 (ℓ "二乳亘") (ℓ "乳二") tt tt Eq.refl

wl0330 : Base 4 → ⟪ (ℓ "亰") ⟫ʷ ≈ ⟪ (ℓ "乢争乣争乩") ⟫ʷ
wl0330 c4 = lw0 c4 (ℓ "亰") (ℓ "乢争乣争乩") tt tt Eq.refl

wl0331 : Base 4 → ⟪ (ℓ "二乣") ⟫ʷ ≈ ⟪ (ℓ "乣二") ⟫ʷ
wl0331 c4 = lw4 c4 (ℓ "二乣") (ℓ "乣二") tt tt Eq.refl

wl0332 : Base 4 → ⟪ (ℓ "二亘") ⟫ʷ ≈ ⟪ (ℓ "亘二") ⟫ʷ
wl0332 c4 = lw4 c4 (ℓ "二亘") (ℓ "亘二") tt tt Eq.refl

wl0333 : Base 4 → ⟪ (ℓ "乳亘亘") ⟫ʷ ≈ ⟪ (ℓ "乳") ⟫ʷ
wl0333 c4 = lw4 c4 (ℓ "乳亘亘") (ℓ "乳") tt tt Eq.refl

wl0334 : Base 4 → ⟪ (ℓ "亨") ⟫ʷ ≈ ⟪ (ℓ "乇亃么亃乩") ⟫ʷ
wl0334 c4 = lw0 c4 (ℓ "亨") (ℓ "乇亃么亃乩") tt tt Eq.refl

wl0335 : Base 4 → ⟪ (ℓ "乳乒乳") ⟫ʷ ≈ ⟪ (ℓ "乑") ⟫ʷ
wl0335 c4 = lw4 c4 (ℓ "乳乒乳") (ℓ "乑") tt tt Eq.refl

wl0336 : Base 4 → ⟪ (ℓ "亰乳") ⟫ʷ ≈ ⟪ (ℓ "乳亰") ⟫ʷ
wl0336 c4 = lw0 c4 (ℓ "亰乳") (ℓ "乳亰") tt tt Eq.refl

wl0337 : Base 4 → ⟪ (ℓ "亰亨亰亨亰") ⟫ʷ ≈ ⟪ (ℓ "亰") ⟫ʷ
wl0337 c4 = lw0 c4 (ℓ "亰亨亰亨亰") (ℓ "亰") tt tt Eq.refl

wl0338 : Base 4 → ⟪ (ℓ "二义亍") ⟫ʷ ≈ ⟪ (ℓ "亍二") ⟫ʷ
wl0338 c4 = lw4 c4 (ℓ "二义亍") (ℓ "亍二") tt tt Eq.refl

wl0339 : Base 4 → ⟪ (ℓ "二义") ⟫ʷ ≈ ⟪ (ℓ "亍二亍") ⟫ʷ
wl0339 c4 = lw4 c4 (ℓ "二义") (ℓ "亍二亍") tt tt Eq.refl

wl0340 : Base 4 → ⟪ (ℓ "二") ⟫ʷ ≈ ⟪ (ℓ "义二义") ⟫ʷ
wl0340 c4 = lw4 c4 (ℓ "二") (ℓ "义二义") tt tt Eq.refl

wl0341 : Base 4 → ⟪ (ℓ "二二") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0341 c4 = lw4 c4 (ℓ "二二") [] tt tt Eq.refl

wl0342 : Base 4 → ⟪ (ℓ "亐丰") ⟫ʷ ≈ ⟪ (ℓ "丰亐") ⟫ʷ
wl0342 c4 = lw4 c4 (ℓ "亐丰") (ℓ "丰亐") tt tt Eq.refl

wl0343 : Base 4 → ⟪ (ℓ "亘") ⟫ʷ ≈ ⟪ (ℓ "丯乶丰乶丶") ⟫ʷ
wl0343 c4 = lw4 c4 (ℓ "亘") (ℓ "丯乶丰乶丶") tt tt Eq.refl

wl0344 : Base 4 → ⟪ (ℓ "亐互义互亐义") ⟫ʷ ≈ ⟪ (ℓ "亘") ⟫ʷ
wl0344 c4 = lw4 c4 (ℓ "亐互义互亐义") (ℓ "亘") tt tt Eq.refl

wl0345 : Base 4 → ⟪ (ℓ "二丌") ⟫ʷ ≈ ⟪ (ℓ "丌亍") ⟫ʷ
wl0345 c4 = lw4 c4 (ℓ "二丌") (ℓ "丌亍") tt tt Eq.refl

wl0346 : Base 4 → ⟪ (ℓ "二不") ⟫ʷ ≈ ⟪ (ℓ "不亍") ⟫ʷ
wl0346 c4 = lw4 c4 (ℓ "二不") (ℓ "不亍") tt tt Eq.refl

wl0347 : Base 4 → ⟪ (ℓ "上亍") ⟫ʷ ≈ ⟪ (ℓ "亍上乇二") ⟫ʷ
wl0347 c4 = lw4 c4 (ℓ "上亍") (ℓ "亍上乇二") tt tt Eq.refl

wl0348 : Base 4 → ⟪ (ℓ "二") ⟫ʷ ≈ ⟪ (ℓ "乇丬么丬丯") ⟫ʷ
wl0348 c4 = lw4 c4 (ℓ "二") (ℓ "乇丬么丬丯") tt tt Eq.refl

wl0349 : Base 4 → ⟪ (ℓ "乇亍") ⟫ʷ ≈ ⟪ (ℓ "亍乇") ⟫ʷ
wl0349 c4 = lw4 c4 (ℓ "乇亍") (ℓ "亍乇") tt tt Eq.refl

wl0350 : Base 4 → ⟪ (ℓ "上乇二乇义二") ⟫ʷ ≈ ⟪ (ℓ "上") ⟫ʷ
wl0350 c4 = lw4 c4 (ℓ "上乇二乇义二") (ℓ "上") tt tt Eq.refl

wl0351 : Base 4 → ⟪ (ℓ "下亍") ⟫ʷ ≈ ⟪ (ℓ "亍下么二") ⟫ʷ
wl0351 c4 = lw4 c4 (ℓ "下亍") (ℓ "亍下么二") tt tt Eq.refl

wl0352 : Base 4 → ⟪ (ℓ "么亍") ⟫ʷ ≈ ⟪ (ℓ "亍么") ⟫ʷ
wl0352 c4 = lw4 c4 (ℓ "么亍") (ℓ "亍么") tt tt Eq.refl

wl0353 : Base 4 → ⟪ (ℓ "下么二么义二") ⟫ʷ ≈ ⟪ (ℓ "下") ⟫ʷ
wl0353 c4 = lw4 c4 (ℓ "下么二么义二") (ℓ "下") tt tt Eq.refl

wl0354 : Base 4 → ⟪ (ℓ "丨亍") ⟫ʷ ≈ ⟪ (ℓ "亍丨乇二") ⟫ʷ
wl0354 c4 = lw4 c4 (ℓ "丨亍") (ℓ "亍丨乇二") tt tt Eq.refl

wl0355 : Base 4 → ⟪ (ℓ "丨乇二乇义二") ⟫ʷ ≈ ⟪ (ℓ "丨") ⟫ʷ
wl0355 c4 = lw4 c4 (ℓ "丨乇二乇义二") (ℓ "丨") tt tt Eq.refl

wl0356 : Base 4 → ⟪ (ℓ "丩亍") ⟫ʷ ≈ ⟪ (ℓ "亍丩么二") ⟫ʷ
wl0356 c4 = lw4 c4 (ℓ "丩亍") (ℓ "亍丩么二") tt tt Eq.refl

wl0357 : Base 4 → ⟪ (ℓ "丩么二么义二") ⟫ʷ ≈ ⟪ (ℓ "丩") ⟫ʷ
wl0357 c4 = lw4 c4 (ℓ "丩么二么义二") (ℓ "丩") tt tt Eq.refl

wl0358 : Base 4 → ⟪ (ℓ "个亍") ⟫ʷ ≈ ⟪ (ℓ "亍个义") ⟫ʷ
wl0358 c4 = lw4 c4 (ℓ "个亍") (ℓ "亍个义") tt tt Eq.refl

wl0359 : Base 4 → ⟪ (ℓ "义亍") ⟫ʷ ≈ ⟪ (ℓ "亍义") ⟫ʷ
wl0359 c4 = lw4 c4 (ℓ "义亍") (ℓ "亍义") tt tt Eq.refl

wl0360 : Base 4 → ⟪ (ℓ "个义义") ⟫ʷ ≈ ⟪ (ℓ "个") ⟫ʷ
wl0360 c4 = lw4 c4 (ℓ "个义义") (ℓ "个") tt tt Eq.refl

wl0361 : Base 4 → ⟪ (ℓ "乄亍") ⟫ʷ ≈ ⟪ (ℓ "亍乄") ⟫ʷ
wl0361 c4 = lw4 c4 (ℓ "乄亍") (ℓ "亍乄") tt tt Eq.refl

wl0362 : Base 4 → ⟪ (ℓ "久") ⟫ʷ ≈ ⟪ (ℓ "丩不丩丌丩") ⟫ʷ
wl0362 c4 = lw4 c4 (ℓ "久") (ℓ "丩不丩丌丩") tt tt Eq.refl

wl0363 : Base 4 → ⟪ (ℓ "乆") ⟫ʷ ≈ ⟪ (ℓ "丨不丨丌丨") ⟫ʷ
wl0363 c4 = lw4 c4 (ℓ "乆") (ℓ "丨不丨丌丨") tt tt Eq.refl

wl0364 : Base 4 → ⟪ (ℓ "上丩") ⟫ʷ ≈ ⟪ (ℓ "且丨且") ⟫ʷ
wl0364 c4 = lw4 c4 (ℓ "上丩") (ℓ "且丨且") tt tt Eq.refl

wl0365 : Base 4 → ⟪ (ℓ "下丨") ⟫ʷ ≈ ⟪ (ℓ "且丩且") ⟫ʷ
wl0365 c4 = lw4 c4 (ℓ "下丨") (ℓ "且丩且") tt tt Eq.refl

wl0366 : Base 4 → ⟪ (ℓ "丌乆") ⟫ʷ ≈ ⟪ (ℓ "且久且") ⟫ʷ
wl0366 c4 = lw4 c4 (ℓ "丌乆") (ℓ "且久且") tt tt Eq.refl

wl0367 : Base 4 → ⟪ (ℓ "不久") ⟫ʷ ≈ ⟪ (ℓ "且乆且") ⟫ʷ
wl0367 c4 = lw4 c4 (ℓ "不久") (ℓ "且乆且") tt tt Eq.refl

wl0368 : Base 4 → ⟪ (ℓ "丯亍") ⟫ʷ ≈ ⟪ (ℓ "亍丯乇二") ⟫ʷ
wl0368 c4 = lw4 c4 (ℓ "丯亍") (ℓ "亍丯乇二") tt tt Eq.refl

wl0369 : Base 4 → ⟪ (ℓ "丯乇二乇义二") ⟫ʷ ≈ ⟪ (ℓ "丯") ⟫ʷ
wl0369 c4 = lw4 c4 (ℓ "丯乇二乇义二") (ℓ "丯") tt tt Eq.refl

wl0370 : Base 4 → ⟪ (ℓ "丰亍") ⟫ʷ ≈ ⟪ (ℓ "亍丰么二") ⟫ʷ
wl0370 c4 = lw4 c4 (ℓ "丰亍") (ℓ "亍丰么二") tt tt Eq.refl

wl0371 : Base 4 → ⟪ (ℓ "丰么二么义二") ⟫ʷ ≈ ⟪ (ℓ "丰") ⟫ʷ
wl0371 c4 = lw4 c4 (ℓ "丰么二么义二") (ℓ "丰") tt tt Eq.refl

wl0372 : Base 4 → ⟪ (ℓ "丱亍") ⟫ʷ ≈ ⟪ (ℓ "亍丱义") ⟫ʷ
wl0372 c4 = lw4 c4 (ℓ "丱亍") (ℓ "亍丱义") tt tt Eq.refl

wl0373 : Base 4 → ⟪ (ℓ "丱义义") ⟫ʷ ≈ ⟪ (ℓ "丱") ⟫ʷ
wl0373 c4 = lw4 c4 (ℓ "丱义义") (ℓ "丱") tt tt Eq.refl

wl0374 : Base 4 → ⟪ (ℓ "乜亍") ⟫ʷ ≈ ⟪ (ℓ "亍乜") ⟫ʷ
wl0374 c4 = lw4 c4 (ℓ "乜亍") (ℓ "亍乜") tt tt Eq.refl

wl0375 : Base 4 → ⟪ (ℓ "九") ⟫ʷ ≈ ⟪ (ℓ "丰不丰丌丰") ⟫ʷ
wl0375 c4 = lw4 c4 (ℓ "九") (ℓ "丰不丰丌丰") tt tt Eq.refl

wl0376 : Base 4 → ⟪ (ℓ "乞") ⟫ʷ ≈ ⟪ (ℓ "丯不丯丌丯") ⟫ʷ
wl0376 c4 = lw4 c4 (ℓ "乞") (ℓ "丯不丯丌丯") tt tt Eq.refl

wl0377 : Base 4 → ⟪ (ℓ "上丰") ⟫ʷ ≈ ⟪ (ℓ "业丯业") ⟫ʷ
wl0377 c4 = lw4 c4 (ℓ "上丰") (ℓ "业丯业") tt tt Eq.refl

wl0378 : Base 4 → ⟪ (ℓ "下丯") ⟫ʷ ≈ ⟪ (ℓ "业丰业") ⟫ʷ
wl0378 c4 = lw4 c4 (ℓ "下丯") (ℓ "业丰业") tt tt Eq.refl

wl0379 : Base 4 → ⟪ (ℓ "丌乞") ⟫ʷ ≈ ⟪ (ℓ "业九业") ⟫ʷ
wl0379 c4 = lw4 c4 (ℓ "丌乞") (ℓ "业九业") tt tt Eq.refl

wl0380 : Base 4 → ⟪ (ℓ "不九") ⟫ʷ ≈ ⟪ (ℓ "业乞业") ⟫ʷ
wl0380 c4 = lw4 c4 (ℓ "不九") (ℓ "业乞业") tt tt Eq.refl

wl0381 : Base 4 → ⟪ (ℓ "二为") ⟫ʷ ≈ ⟪ (ℓ "为二") ⟫ʷ
wl0381 c4 = lw4 c4 (ℓ "二为") (ℓ "为二") tt tt Eq.refl

wl0382 : Base 4 → ⟪ (ℓ "二丸") ⟫ʷ ≈ ⟪ (ℓ "丸二") ⟫ʷ
wl0382 c4 = lw4 c4 (ℓ "二丸") (ℓ "丸二") tt tt Eq.refl

wl0383 : Base 4 → ⟪ (ℓ "二买交") ⟫ʷ ≈ ⟪ (ℓ "买二") ⟫ʷ
wl0383 c4 = lw4 c4 (ℓ "二买交") (ℓ "买二") tt tt Eq.refl

wl0384 : Base 4 → ⟪ (ℓ "买交交") ⟫ʷ ≈ ⟪ (ℓ "买") ⟫ʷ
wl0384 c4 = lw4 c4 (ℓ "买交交") (ℓ "买") tt tt Eq.refl

wl0385 : Base 4 → ⟪ (ℓ "乱") ⟫ʷ ≈ ⟪ (ℓ "丷不丷丌丷") ⟫ʷ
wl0385 c4 = lw4 c4 (ℓ "乱") (ℓ "丷不丷丌丷") tt tt Eq.refl

wl0386 : Base 4 → ⟪ (ℓ "乲") ⟫ʷ ≈ ⟪ (ℓ "丶不丶丌丶") ⟫ʷ
wl0386 c4 = lw4 c4 (ℓ "乲") (ℓ "丶不丶丌丶") tt tt Eq.refl

wl0387 : Base 4 → ⟪ (ℓ "上丷") ⟫ʷ ≈ ⟪ (ℓ "丠丶丠") ⟫ʷ
wl0387 c4 = lw4 c4 (ℓ "上丷") (ℓ "丠丶丠") tt tt Eq.refl

wl0388 : Base 4 → ⟪ (ℓ "下丶") ⟫ʷ ≈ ⟪ (ℓ "丠丷丠") ⟫ʷ
wl0388 c4 = lw4 c4 (ℓ "下丶") (ℓ "丠丷丠") tt tt Eq.refl

wl0389 : Base 4 → ⟪ (ℓ "丌乲") ⟫ʷ ≈ ⟪ (ℓ "丠乱丠") ⟫ʷ
wl0389 c4 = lw4 c4 (ℓ "丌乲") (ℓ "丠乱丠") tt tt Eq.refl

wl0390 : Base 4 → ⟪ (ℓ "不乱") ⟫ʷ ≈ ⟪ (ℓ "丠乲丠") ⟫ʷ
wl0390 c4 = lw4 c4 (ℓ "不乱") (ℓ "丠乲丠") tt tt Eq.refl

wl0391 : Base 4 → ⟪ (ℓ "二") ⟫ʷ ≈ ⟪ (ℓ "乇丳么丳丨") ⟫ʷ
wl0391 c4 = lw4 c4 (ℓ "二") (ℓ "乇丳么丳丨") tt tt Eq.refl

wl0392 : Base 4 → ⟪ (ℓ "京么") ⟫ʷ ≈ ⟪ (ℓ "么京") ⟫ʷ
wl0392 c4 = lw0 c4 (ℓ "京么") (ℓ "么京") tt tt Eq.refl

wl0393 : Base 4 → ⟪ (ℓ "京乇") ⟫ʷ ≈ ⟪ (ℓ "乇京") ⟫ʷ
wl0393 c4 = lw0 c4 (ℓ "京乇") (ℓ "乇京") tt tt Eq.refl

wl0394 : Base 4 → ⟪ (ℓ "丒二专") ⟫ʷ ≈ ⟪ (ℓ "于") ⟫ʷ
wl0394 c4 = lw4 c4 (ℓ "丒二专") (ℓ "于") tt tt Eq.refl

wl0395 : Base 4 → ⟪ (ℓ "丒京专") ⟫ʷ ≈ ⟪ (ℓ "亭") ⟫ʷ
wl0395 c4 = lw0 c4 (ℓ "丒京专") (ℓ "亭") tt tt Eq.refl

wl0396 : Base 4 → ⟪ (ℓ "专丒") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0396 c4 = lw4 c4 (ℓ "专丒") [] tt tt Eq.refl

wl0397 : Base 4 → ⟪ (ℓ "丰丐于丑") ⟫ʷ ≈ ⟪ (ℓ "于二") ⟫ʷ
wl0397 c4 = lw4 c4 (ℓ "丰丐于丑") (ℓ "于二") tt tt Eq.refl

wl0398 : Base 4 → ⟪ (ℓ "乺丐亭丑") ⟫ʷ ≈ ⟪ (ℓ "亭京") ⟫ʷ
wl0398 c4 = lw0 c4 (ℓ "乺丐亭丑") (ℓ "亭京") tt tt Eq.refl

wl0399 : Base 4 → ⟪ (ℓ "丑丐") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0399 c4 = lw4 c4 (ℓ "丑丐") [] tt tt Eq.refl

wl0400 : Base 4 → ⟪ (ℓ "丰丐") ⟫ʷ ≈ ⟪ (ℓ "丐丰") ⟫ʷ
wl0400 c4 = lw4 c4 (ℓ "丰丐") (ℓ "丐丰") tt tt Eq.refl

wl0401 : Base 4 → ⟪ (ℓ "丰丑") ⟫ʷ ≈ ⟪ (ℓ "丑丰") ⟫ʷ
wl0401 c4 = lw4 c4 (ℓ "丰丑") (ℓ "丑丰") tt tt Eq.refl

wl0402 : Base 4 → ⟪ (ℓ "亭亭") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0402 c4 = lw0 c4 (ℓ "亭亭") [] tt tt Eq.refl

wl0403 : Base 4 → ⟪ (ℓ "于于") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0403 c4 = lw4 c4 (ℓ "于于") [] tt tt Eq.refl

wl0404 : Base 4 → ⟪ (ℓ "二亙") ⟫ʷ ≈ ⟪ (ℓ "亙二交") ⟫ʷ
wl0404 c4 = lw4 c4 (ℓ "二亙") (ℓ "亙二交") tt tt Eq.refl

wl0405 : Base 4 → ⟪ (ℓ "乭了乭") ⟫ʷ ≈ ⟪ (ℓ "乬") ⟫ʷ
wl0405 c4 = lw0 c4 (ℓ "乭了乭") (ℓ "乬") tt tt Eq.refl

wl0406 : Base 4 → ⟪ (ℓ "交乭") ⟫ʷ ≈ ⟪ (ℓ "乭交") ⟫ʷ
wl0406 c4 = lw0 c4 (ℓ "交乭") (ℓ "乭交") tt tt Eq.refl

wl0407 : Base 4 → ⟪ (ℓ "交京交京交") ⟫ʷ ≈ ⟪ (ℓ "交") ⟫ʷ
wl0407 c4 = lw0 c4 (ℓ "交京交京交") (ℓ "交") tt tt Eq.refl

wl0408 : Base 4 → ⟪ (ℓ "交亭") ⟫ʷ ≈ ⟪ (ℓ "亭交亰") ⟫ʷ
wl0408 c4 = lw0 c4 (ℓ "交亭") (ℓ "亭交亰") tt tt Eq.refl

wl0409 : Base 4 → ⟪ (ℓ "丌乢丳乣丳丶不") ⟫ʷ ≈ ⟪ (ℓ "亙") ⟫ʷ
wl0409 c4 = lw4 c4 (ℓ "丌乢丳乣丳丶不") (ℓ "亙") tt tt Eq.refl

wl0410 : Base 4 → ⟪ (ℓ "乣亭") ⟫ʷ ≈ ⟪ (ℓ "亭乣") ⟫ʷ
wl0410 c4 = lw0 c4 (ℓ "乣亭") (ℓ "亭乣") tt tt Eq.refl

wl0411 : Base 4 → ⟪ (ℓ "二书") ⟫ʷ ≈ ⟪ (ℓ "书二") ⟫ʷ
wl0411 c4 = lw4 c4 (ℓ "二书") (ℓ "书二") tt tt Eq.refl

wl0412 : Base 4 → ⟪ (ℓ "亙交交") ⟫ʷ ≈ ⟪ (ℓ "亙") ⟫ʷ
wl0412 c4 = lw4 c4 (ℓ "亙交交") (ℓ "亙") tt tt Eq.refl

wl0413 : Base 4 → ⟪ (ℓ "亰亭") ⟫ʷ ≈ ⟪ (ℓ "亭亰") ⟫ʷ
wl0413 c4 = lw0 c4 (ℓ "亰亭") (ℓ "亭亰") tt tt Eq.refl

wl0414 : Base 4 → ⟪ (ℓ "亰么") ⟫ʷ ≈ ⟪ (ℓ "么亰") ⟫ʷ
wl0414 c4 = lw0 c4 (ℓ "亰么") (ℓ "么亰") tt tt Eq.refl

wl0415 : Base 4 → ⟪ (ℓ "亰乇") ⟫ʷ ≈ ⟪ (ℓ "乇亰") ⟫ʷ
wl0415 c4 = lw0 c4 (ℓ "亰乇") (ℓ "乇亰") tt tt Eq.refl

wl0416 : Base 4 → ⟪ (ℓ "丘二丙") ⟫ʷ ≈ ⟪ (ℓ "亏") ⟫ʷ
wl0416 c4 = lw4 c4 (ℓ "丘二丙") (ℓ "亏") tt tt Eq.refl

wl0417 : Base 4 → ⟪ (ℓ "丘亰丙") ⟫ʷ ≈ ⟪ (ℓ "亱") ⟫ʷ
wl0417 c4 = lw0 c4 (ℓ "丘亰丙") (ℓ "亱") tt tt Eq.refl

wl0418 : Base 4 → ⟪ (ℓ "丩世亏丗") ⟫ʷ ≈ ⟪ (ℓ "亏二") ⟫ʷ
wl0418 c4 = lw4 c4 (ℓ "丩世亏丗") (ℓ "亏二") tt tt Eq.refl

wl0419 : Base 4 → ⟪ (ℓ "乺世亱丗") ⟫ʷ ≈ ⟪ (ℓ "亱亰") ⟫ʷ
wl0419 c4 = lw0 c4 (ℓ "乺世亱丗") (ℓ "亱亰") tt tt Eq.refl

wl0420 : Base 4 → ⟪ (ℓ "亱亱") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0420 c4 = lw0 c4 (ℓ "亱亱") [] tt tt Eq.refl

wl0421 : Base 4 → ⟪ (ℓ "亏亏") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0421 c4 = lw4 c4 (ℓ "亏亏") [] tt tt Eq.refl

wl0422 : Base 4 → ⟪ (ℓ "二云") ⟫ʷ ≈ ⟪ (ℓ "云二交") ⟫ʷ
wl0422 c4 = lw4 c4 (ℓ "二云") (ℓ "云二交") tt tt Eq.refl

wl0423 : Base 4 → ⟪ (ℓ "乙亃乙") ⟫ʷ ≈ ⟪ (ℓ "乘") ⟫ʷ
wl0423 c4 = lw0 c4 (ℓ "乙亃乙") (ℓ "乘") tt tt Eq.refl

wl0424 : Base 4 → ⟪ (ℓ "交乙") ⟫ʷ ≈ ⟪ (ℓ "乙交") ⟫ʷ
wl0424 c4 = lw0 c4 (ℓ "交乙") (ℓ "乙交") tt tt Eq.refl

wl0425 : Base 4 → ⟪ (ℓ "交亰交亰交") ⟫ʷ ≈ ⟪ (ℓ "交") ⟫ʷ
wl0425 c4 = lw0 c4 (ℓ "交亰交亰交") (ℓ "交") tt tt Eq.refl

wl0426 : Base 4 → ⟪ (ℓ "交亱") ⟫ʷ ≈ ⟪ (ℓ "亱交京") ⟫ʷ
wl0426 c4 = lw0 c4 (ℓ "交亱") (ℓ "亱交京") tt tt Eq.refl

wl0427 : Base 4 → ⟪ (ℓ "丌乎丬乏丬丶不") ⟫ʷ ≈ ⟪ (ℓ "云") ⟫ʷ
wl0427 c4 = lw4 c4 (ℓ "丌乎丬乏丬丶不") (ℓ "云") tt tt Eq.refl

wl0428 : Base 4 → ⟪ (ℓ "乏亱") ⟫ʷ ≈ ⟪ (ℓ "亱乏") ⟫ʷ
wl0428 c4 = lw0 c4 (ℓ "乏亱") (ℓ "亱乏") tt tt Eq.refl

wl0429 : Base 4 → ⟪ (ℓ "乎亱") ⟫ʷ ≈ ⟪ (ℓ "亱乎") ⟫ʷ
wl0429 c4 = lw0 c4 (ℓ "乎亱") (ℓ "亱乎") tt tt Eq.refl

wl0430 : Base 4 → ⟪ (ℓ "云交交") ⟫ʷ ≈ ⟪ (ℓ "云") ⟫ʷ
wl0430 c4 = lw4 c4 (ℓ "云交交") (ℓ "云") tt tt Eq.refl

wl0431 : Base 4 → ⟪ (ℓ "京亱") ⟫ʷ ≈ ⟪ (ℓ "亱京") ⟫ʷ
wl0431 c4 = lw0 c4 (ℓ "京亱") (ℓ "亱京") tt tt Eq.refl

wl0432 : Base 4 → ⟪ (ℓ "亰乏") ⟫ʷ ≈ ⟪ (ℓ "乏亰") ⟫ʷ
wl0432 c4 = lw0 c4 (ℓ "亰乏") (ℓ "乏亰") tt tt Eq.refl

wl0433 : Base 4 → ⟪ (ℓ "亰乎") ⟫ʷ ≈ ⟪ (ℓ "乎亰") ⟫ʷ
wl0433 c4 = lw0 c4 (ℓ "亰乎") (ℓ "乎亰") tt tt Eq.refl

wl0434 : Base 4 → ⟪ (ℓ "丞亐丟") ⟫ʷ ≈ ⟪ (ℓ "亓") ⟫ʷ
wl0434 c4 = lw4 c4 (ℓ "丞亐丟") (ℓ "亓") tt tt Eq.refl

wl0435 : Base 4 → ⟪ (ℓ "丞亰丟") ⟫ʷ ≈ ⟪ (ℓ "亲") ⟫ʷ
wl0435 c4 = lw0 c4 (ℓ "丞亰丟") (ℓ "亲") tt tt Eq.refl

wl0436 : Base 4 → ⟪ (ℓ "丟丞") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0436 c4 = lw4 c4 (ℓ "丟丞") [] tt tt Eq.refl

wl0437 : Base 4 → ⟪ (ℓ "丩东亓丝") ⟫ʷ ≈ ⟪ (ℓ "亓亐") ⟫ʷ
wl0437 c4 = lw4 c4 (ℓ "丩东亓丝") (ℓ "亓亐") tt tt Eq.refl

wl0438 : Base 4 → ⟪ (ℓ "乪东亲丝") ⟫ʷ ≈ ⟪ (ℓ "亲亰") ⟫ʷ
wl0438 c4 = lw0 c4 (ℓ "乪东亲丝") (ℓ "亲亰") tt tt Eq.refl

wl0439 : Base 4 → ⟪ (ℓ "乪丝") ⟫ʷ ≈ ⟪ (ℓ "丝乪") ⟫ʷ
wl0439 c4 = lw0 c4 (ℓ "乪丝") (ℓ "丝乪") tt tt Eq.refl

wl0440 : Base 4 → ⟪ (ℓ "乪东") ⟫ʷ ≈ ⟪ (ℓ "东乪") ⟫ʷ
wl0440 c4 = lw0 c4 (ℓ "乪东") (ℓ "东乪") tt tt Eq.refl

wl0441 : Base 4 → ⟪ (ℓ "丝东") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0441 c4 = lw4 c4 (ℓ "丝东") [] tt tt Eq.refl

wl0442 : Base 4 → ⟪ (ℓ "亲亲") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0442 c4 = lw0 c4 (ℓ "亲亲") [] tt tt Eq.refl

wl0443 : Base 4 → ⟪ (ℓ "亓亓") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0443 c4 = lw4 c4 (ℓ "亓亓") [] tt tt Eq.refl

wl0444 : Base 4 → ⟪ (ℓ "亐丳") ⟫ʷ ≈ ⟪ (ℓ "丳亐") ⟫ʷ
wl0444 c4 = lw4 c4 (ℓ "亐丳") (ℓ "丳亐") tt tt Eq.refl

wl0445 : Base 4 → ⟪ (ℓ "交亲") ⟫ʷ ≈ ⟪ (ℓ "亲交亨") ⟫ʷ
wl0445 c4 = lw0 c4 (ℓ "交亲") (ℓ "亲交亨") tt tt Eq.refl

wl0446 : Base 4 → ⟪ (ℓ "丌乇丬么丬丯不") ⟫ʷ ≈ ⟪ (ℓ "亍") ⟫ʷ
wl0446 c4 = lw4 c4 (ℓ "丌乇丬么丬丯不") (ℓ "亍") tt tt Eq.refl

wl0447 : Base 4 → ⟪ (ℓ "么亲") ⟫ʷ ≈ ⟪ (ℓ "亲么") ⟫ʷ
wl0447 c4 = lw0 c4 (ℓ "么亲") (ℓ "亲么") tt tt Eq.refl

wl0448 : Base 4 → ⟪ (ℓ "亐之") ⟫ʷ ≈ ⟪ (ℓ "之亐") ⟫ʷ
wl0448 c4 = lw4 c4 (ℓ "亐之") (ℓ "之亐") tt tt Eq.refl

wl0449 : Base 4 → ⟪ (ℓ "亍交交") ⟫ʷ ≈ ⟪ (ℓ "亍") ⟫ʷ
wl0449 c4 = lw4 c4 (ℓ "亍交交") (ℓ "亍") tt tt Eq.refl

wl0450 : Base 4 → ⟪ (ℓ "亨亲") ⟫ʷ ≈ ⟪ (ℓ "亲亨") ⟫ʷ
wl0450 c4 = lw0 c4 (ℓ "亨亲") (ℓ "亲亨") tt tt Eq.refl

wl0451 : Base 4 → ⟪ (ℓ "亰乖") ⟫ʷ ≈ ⟪ (ℓ "乖亰") ⟫ʷ
wl0451 c4 = lw0 c4 (ℓ "亰乖") (ℓ "乖亰") tt tt Eq.refl

wl0452 : Base 4 → ⟪ (ℓ "亰乕") ⟫ʷ ≈ ⟪ (ℓ "乕亰") ⟫ʷ
wl0452 c4 = lw0 c4 (ℓ "亰乕") (ℓ "乕亰") tt tt Eq.refl

wl0453 : Base 4 → ⟪ (ℓ "两亰严") ⟫ʷ ≈ ⟪ (ℓ "亳") ⟫ʷ
wl0453 c4 = lw0 c4 (ℓ "两亰严") (ℓ "亳") tt tt Eq.refl

wl0454 : Base 4 → ⟪ (ℓ "严两") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0454 c4 = lw0 c4 (ℓ "严两") [] tt tt Eq.refl

wl0455 : Base 4 → ⟪ (ℓ "乣丢亳丣") ⟫ʷ ≈ ⟪ (ℓ "亳亰") ⟫ʷ
wl0455 c4 = lw0 c4 (ℓ "乣丢亳丣") (ℓ "亳亰") tt tt Eq.refl

wl0456 : Base 4 → ⟪ (ℓ "丣丢") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0456 c4 = lw0 c4 (ℓ "丣丢") [] tt tt Eq.refl

wl0457 : Base 4 → ⟪ (ℓ "亳亳") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0457 c4 = lw0 c4 (ℓ "亳亳") [] tt tt Eq.refl

wl0458 : Base 4 → ⟪ (ℓ "亘") ⟫ʷ ≈ ⟪ (ℓ "乢丳乣丳丶") ⟫ʷ
wl0458 c4 = lw4 c4 (ℓ "亘") (ℓ "乢丳乣丳丶") tt tt Eq.refl

wl0459 : Base 4 → ⟪ (ℓ "亨亳") ⟫ʷ ≈ ⟪ (ℓ "亳交亨") ⟫ʷ
wl0459 c4 = lw0 c4 (ℓ "亨亳") (ℓ "亳交亨") tt tt Eq.refl

wl0460 : Base 4 → ⟪ (ℓ "么亳") ⟫ʷ ≈ ⟪ (ℓ "亳么") ⟫ʷ
wl0460 c4 = lw0 c4 (ℓ "么亳") (ℓ "亳么") tt tt Eq.refl

wl0461 : Base 4 → ⟪ (ℓ "乇亳") ⟫ʷ ≈ ⟪ (ℓ "亳乇") ⟫ʷ
wl0461 c4 = lw0 c4 (ℓ "乇亳") (ℓ "亳乇") tt tt Eq.refl

wl0462 : Base 4 → ⟪ (ℓ "交") ⟫ʷ ≈ ⟪ (ℓ "亨交亨") ⟫ʷ
wl0462 c4 = lw0 c4 (ℓ "交") (ℓ "亨交亨") tt tt Eq.refl

wl0463 : Base 4 → ⟪ (ℓ "交亳") ⟫ʷ ≈ ⟪ (ℓ "亳交") ⟫ʷ
wl0463 c4 = lw0 c4 (ℓ "交亳") (ℓ "亳交") tt tt Eq.refl

wl0464 : Base 4 → ⟪ (ℓ "交亍") ⟫ʷ ≈ ⟪ (ℓ "亍交") ⟫ʷ
wl0464 c4 = lw4 c4 (ℓ "交亍") (ℓ "亍交") tt tt Eq.refl

wl0465 : Base 4 → ⟪ (ℓ "亨享") ⟫ʷ ≈ ⟪ (ℓ "享亨义") ⟫ʷ
wl0465 c4 = lw0 c4 (ℓ "亨享") (ℓ "享亨义") tt tt Eq.refl

wl0466 : Base 4 → ⟪ (ℓ "亨义享亨") ⟫ʷ ≈ ⟪ (ℓ "享") ⟫ʷ
wl0466 c4 = lw0 c4 (ℓ "亨义享亨") (ℓ "享") tt tt Eq.refl

wl0467 : Base 4 → ⟪ (ℓ "两亨严") ⟫ʷ ≈ ⟪ (ℓ "享") ⟫ʷ
wl0467 c4 = lw0 c4 (ℓ "两亨严") (ℓ "享") tt tt Eq.refl

wl0468 : Base 4 → ⟪ (ℓ "么丢享丣") ⟫ʷ ≈ ⟪ (ℓ "享亨") ⟫ʷ
wl0468 c4 = lw0 c4 (ℓ "么丢享丣") (ℓ "享亨") tt tt Eq.refl

wl0469 : Base 4 → ⟪ (ℓ "丷么") ⟫ʷ ≈ ⟪ (ℓ "么丷") ⟫ʷ
wl0469 c4 = lw4 c4 (ℓ "丷么") (ℓ "么丷") tt tt Eq.refl

wl0470 : Base 4 → ⟪ (ℓ "享享") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0470 c4 = lw0 c4 (ℓ "享享") [] tt tt Eq.refl

wl0471 : Base 4 → ⟪ (ℓ "亨乹") ⟫ʷ ≈ ⟪ (ℓ "乹亨") ⟫ʷ
wl0471 c4 = lw0 c4 (ℓ "亨乹") (ℓ "乹亨") tt tt Eq.refl

wl0472 : Base 4 → ⟪ (ℓ "乽享") ⟫ʷ ≈ ⟪ (ℓ "享乽") ⟫ʷ
wl0472 c4 = lw0 c4 (ℓ "乽享") (ℓ "享乽") tt tt Eq.refl

wl0473 : Base 4 → ⟪ (ℓ "交产") ⟫ʷ ≈ ⟪ (ℓ "产交义") ⟫ʷ
wl0473 c4 = lw4 c4 (ℓ "交产") (ℓ "产交义") tt tt Eq.refl

wl0474 : Base 4 → ⟪ (ℓ "交义产交") ⟫ʷ ≈ ⟪ (ℓ "产") ⟫ʷ
wl0474 c4 = lw4 c4 (ℓ "交义产交") (ℓ "产") tt tt Eq.refl

wl0475 : Base 4 → ⟪ (ℓ "亰享") ⟫ʷ ≈ ⟪ (ℓ "享亰交") ⟫ʷ
wl0475 c4 = lw0 c4 (ℓ "亰享") (ℓ "享亰交") tt tt Eq.refl

wl0476 : Base 4 → ⟪ (ℓ "交") ⟫ʷ ≈ ⟪ (ℓ "乜交乜") ⟫ʷ
wl0476 c4 = lw4 c4 (ℓ "交") (ℓ "乜交乜") tt tt Eq.refl

wl0477 : Base 4 → ⟪ (ℓ "亐") ⟫ʷ ≈ ⟪ (ℓ "丶乄丷乄乎") ⟫ʷ
wl0477 c4 = lw4 c4 (ℓ "亐") (ℓ "丶乄丷乄乎") tt tt Eq.refl

wl0478 : Base 4 → ⟪ (ℓ "乎享") ⟫ʷ ≈ ⟪ (ℓ "享乎") ⟫ʷ
wl0478 c4 = lw0 c4 (ℓ "乎享") (ℓ "享乎") tt tt Eq.refl

wl0479 : Base 4 → ⟪ (ℓ "亐") ⟫ʷ ≈ ⟪ (ℓ "丳亐丳") ⟫ʷ
wl0479 c4 = lw4 c4 (ℓ "亐") (ℓ "丳亐丳") tt tt Eq.refl

wl0480 : Base 4 → ⟪ (ℓ "乜丳乜") ⟫ʷ ≈ ⟪ (ℓ "串") ⟫ʷ
wl0480 c4 = lw4 c4 (ℓ "乜丳乜") (ℓ "串") tt tt Eq.refl

wl0481 : Base 4 → ⟪ (ℓ "交丳") ⟫ʷ ≈ ⟪ (ℓ "丳亐交") ⟫ʷ
wl0481 c4 = lw4 c4 (ℓ "交丳") (ℓ "丳亐交") tt tt Eq.refl

wl0482 : Base 4 → ⟪ (ℓ "交乜") ⟫ʷ ≈ ⟪ (ℓ "乜交") ⟫ʷ
wl0482 c4 = lw4 c4 (ℓ "交乜") (ℓ "乜交") tt tt Eq.refl

wl0483 : Base 4 → ⟪ (ℓ "亐乜") ⟫ʷ ≈ ⟪ (ℓ "乜交亐") ⟫ʷ
wl0483 c4 = lw4 c4 (ℓ "亐乜") (ℓ "乜交亐") tt tt Eq.refl

wl0484 : Base 4 → ⟪ (ℓ "交亐交亐交") ⟫ʷ ≈ ⟪ (ℓ "交") ⟫ʷ
wl0484 c4 = lw4 c4 (ℓ "交亐交亐交") (ℓ "交") tt tt Eq.refl

wl0485 : Base 4 → ⟪ (ℓ "串串") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0485 c4 = lw4 c4 (ℓ "串串") [] tt tt Eq.refl

wl0486 : Base 4 → ⟪ (ℓ "亨亩乐亩亨乐") ⟫ʷ ≈ ⟪ (ℓ "亰") ⟫ʷ
wl0486 c4 = lw0 c4 (ℓ "亨亩乐亩亨乐") (ℓ "亰") tt tt Eq.refl

wl0487 : Base 4 → ⟪ (ℓ "丞交丟") ⟫ʷ ≈ ⟪ (ℓ "产") ⟫ʷ
wl0487 c4 = lw4 c4 (ℓ "丞交丟") (ℓ "产") tt tt Eq.refl

wl0488 : Base 4 → ⟪ (ℓ "么东产丝") ⟫ʷ ≈ ⟪ (ℓ "产交") ⟫ʷ
wl0488 c4 = lw4 c4 (ℓ "么东产丝") (ℓ "产交") tt tt Eq.refl

wl0489 : Base 4 → ⟪ (ℓ "产产") ⟫ʷ ≈ ⟪ [] ⟫ʷ
wl0489 c4 = lw4 c4 (ℓ "产产") [] tt tt Eq.refl

wl0490 : Base 4 → ⟪ (ℓ "交丶") ⟫ʷ ≈ ⟪ (ℓ "丶交") ⟫ʷ
wl0490 c4 = lw4 c4 (ℓ "交丶") (ℓ "丶交") tt tt Eq.refl

wl0491 : Base 4 → ⟪ (ℓ "交乺") ⟫ʷ ≈ ⟪ (ℓ "乺交") ⟫ʷ
wl0491 c4 = lw0 c4 (ℓ "交乺") (ℓ "乺交") tt tt Eq.refl

wl0492 : Base 4 → ⟪ (ℓ "交乹") ⟫ʷ ≈ ⟪ (ℓ "乹交") ⟫ʷ
wl0492 c4 = lw0 c4 (ℓ "交乹") (ℓ "乹交") tt tt Eq.refl

wl0493 : Base 4 → ⟪ (ℓ "亐云丱云亐丱") ⟫ʷ ≈ ⟪ (ℓ "交") ⟫ʷ
wl0493 c4 = lw4 c4 (ℓ "亐云丱云亐丱") (ℓ "交") tt tt Eq.refl

wl0494 : Base 4 → ⟪ (ℓ "交") ⟫ʷ ≈ ⟪ (ℓ "京亯乫亯京乫") ⟫ʷ
wl0494 c4 = lw0 c4 (ℓ "交") (ℓ "京亯乫亯京乫") tt tt Eq.refl

wl0495 : Base 4 → ⟪ (ℓ "交丷") ⟫ʷ ≈ ⟪ (ℓ "丷交") ⟫ʷ
wl0495 c4 = lw4 c4 (ℓ "交丷") (ℓ "丷交") tt tt Eq.refl

wl0496 : Base 4 → ⟪ (ℓ "亰产") ⟫ʷ ≈ ⟪ (ℓ "产亨亰") ⟫ʷ
wl0496 c4 = lw0 c4 (ℓ "亰产") (ℓ "产亨亰") tt tt Eq.refl

wl0497 : Base 4 → ⟪ (ℓ "亨亰产") ⟫ʷ ≈ ⟪ (ℓ "产亰") ⟫ʷ
wl0497 c4 = lw0 c4 (ℓ "亨亰产") (ℓ "产亰") tt tt Eq.refl

wl0498 : Base 4 → ⟪ (ℓ "亐产") ⟫ʷ ≈ ⟪ (ℓ "产二亐") ⟫ʷ
wl0498 c4 = lw4 c4 (ℓ "亐产") (ℓ "产二亐") tt tt Eq.refl

wl0499 : Base 4 → ⟪ (ℓ "乕产") ⟫ʷ ≈ ⟪ (ℓ "产乕") ⟫ʷ
wl0499 c4 = lw0 c4 (ℓ "乕产") (ℓ "产乕") tt tt Eq.refl

wl0500 : Base 4 → ⟪ (ℓ "丩产") ⟫ʷ ≈ ⟪ (ℓ "产丩") ⟫ʷ
wl0500 c4 = lw4 c4 (ℓ "丩产") (ℓ "产丩") tt tt Eq.refl

wl0501 : Base 4 → ⟪ (ℓ "丨产") ⟫ʷ ≈ ⟪ (ℓ "产丨") ⟫ʷ
wl0501 c4 = lw4 c4 (ℓ "丨产") (ℓ "产丨") tt tt Eq.refl

wl0502 : Base 4 → ⟪ (ℓ "二") ⟫ʷ ≈ ⟪ (ℓ "亐二亐") ⟫ʷ
wl0502 c4 = lw4 c4 (ℓ "二") (ℓ "亐二亐") tt tt Eq.refl

wl0503 : Base 4 → ⟪ (ℓ "二产") ⟫ʷ ≈ ⟪ (ℓ "产二") ⟫ʷ
wl0503 c4 = lw4 c4 (ℓ "二产") (ℓ "产二") tt tt Eq.refl

wl0504 : Base 4 → ⟪ (ℓ "交义产") ⟫ʷ ≈ ⟪ (ℓ "产交") ⟫ʷ
wl0504 c4 = lw4 c4 (ℓ "交义产") (ℓ "产交") tt tt Eq.refl
