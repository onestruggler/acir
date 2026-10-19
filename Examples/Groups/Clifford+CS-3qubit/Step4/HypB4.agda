------------------------------------------------------------------------
-- Presentations of groups
--
-- Ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 3-qubit Clifford+CS operators"
-- (arXiv:2306.08530, CC BY 2.0).
-- 
-- Part 4 of 5 of the proofs of Step4.Main's hypB that compute normal
-- forms, one lemma per relation of Step 3; in one module they took 41 s.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Presentation.Tactics.Equality as Eq using (_≡_ ; auto)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_)
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Presentation.Tactics.Lists
open import Word.Base
open import Presentation.Tactics.Judgement
open import Presentation.Tactics.Lemmas
open Presentation.Tactics.Lemmas.Derivations
open import Presentation.Tactics.Words

open Monoid-Equational
open Rewriting
open Associative
open InContext

open import Presentation.Tactics.Lists using (MaybeEq ; _=m?_ ; isJust ; fromJust)
open import Examples.Groups.Clifford+CS-3qubit.MaybeEq-Instances
open import Examples.Groups.Clifford+CS-3qubit.CosetNF
open import Examples.Groups.Clifford+CS-3qubit.Gate

import Examples.Groups.Clifford+CS-3qubit.Step3.Rel as L

open import Examples.Groups.Clifford+CS-3qubit.Step4.Rel
open import Examples.Groups.Clifford+CS-3qubit.Step4.S8
open import Examples.Groups.Clifford+CS-3qubit.Step4.S8D
open import Examples.Groups.Clifford+CS-3qubit.Step4.KD
open import Examples.Groups.Clifford+CS-3qubit.Step4.Lemmas

open import Examples.Groups.Clifford+CS-3qubit.Step4.Simple

module Examples.Groups.Clifford+CS-3qubit.Step4.HypB4 where

  hb2142 : Goal L.ax-X2-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CCK'-X2-CX10-CX20-CCX0-S0-S0-S1-S2-S2-S2-CS01-CS02-CS02-CS12-CS12-CCZ
  hb2142 = ListNF.listnfeq' nf-p24k0d auto

  hb2143 : Goal L.ax-X2-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-X2-CX10-CX20-S0-S1-S1-S2-S2-CS01-CS01-CS12-CCZ
  hb2143 = ListNF.listnfeq' nf-p24k0d auto

  hb2144 : Goal L.ax-X2-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CK10-CCK'-X2-CX20-CCX0-S0-S0-S1-S2-S2-S2-CS01-CS02-CS02-CS12-CS12-CS12
  hb2144 = ListNF.listnfeq' nf-p24k0d auto

  hb2145 : Goal L.ax-X2-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-X2-CX20-S0-S1-S2-S2-CS01
  hb2145 = ListNF.listnfeq' nf-p24k0d auto

  hb2146 : Goal L.ax-X2-K0-CK10=K0-CK10-X2
  hb2146 = ListNF.listnfeq' nf-p24k0d auto

  hb2147 : Goal L.ax-X2-K0-CK10-CCK'=K0-CCK'-X2-CS01-CS12-CS12-CS12-CCZ
  hb2147 = ListNF.listnfeq' nf-p24k0d auto

  hb2148 : Goal L.ax-X2-K0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-X2-CCX0-S0-S0-S0-S1-CS01-CS01-CS12-CS12-CCZ
  hb2148 = ListNF.listnfeq' nf-p24k0d auto

  hb2149 : Goal L.ax-X2-K0-CK20=CK20-X2-S2-S2-S2
  hb2149 = ListNF.listnfeq' nf-p24k0d auto

  hb2150 : Goal L.ax-X2-K0-CK20-S0-CK10=CK20-S0-CK10-X2-S2-S2-S2
  hb2150 = ListNF.listnfeq' nf-p24k0d auto

  hb2151 : Goal L.ax-X2-K0-CK20-S0-CK10-CCK'=CK20-CCK'-CCK'-X2-S0-S1-S2-S2-S2-CS01-CS01-CS01-CS12-CS12
  hb2151 = ListNF.listnfeq' nf-p24k0d auto

  hb2152 : Goal L.ax-X2-K0-CK20-S0-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-X2-CX10-CCX0-S0-S1-S1-S2-S2-S2-CS01-CS01-CS12
  hb2152 = ListNF.listnfeq' nf-p24k0d auto

  hb2153 : Goal L.ax-X2-K0-CK20-CK10=CK20-CK10-X2-S2-S2-S2
  hb2153 = ListNF.listnfeq' nf-p24k0d auto

  hb2154 : Goal L.ax-X2-K0-CK20-CK10-CCK'=CK20-CCK'-X2-S2-S2-S2-CS01-CS12-CS12-CS12-CCZ
  hb2154 = ListNF.listnfeq' nf-p24k0d auto

  hb2155 : Goal L.ax-X2-K0-CK20-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-X2-CCX0-S0-S0-S0-S1-S2-S2-S2-CS01-CS01-CS12-CS12-CCZ
  hb2155 = ListNF.listnfeq' nf-p24k0d auto

  hb2156 : Goal L.ax-X2-K0-CK20-CCK'=CK20-CK10-CCK'-X2-S1-S2-S2-S2-CS01-CS12-CS12-CS12-CCZ
  hb2156 = ListNF.listnfeq' nf-p24k0d auto

  hb2157 : Goal L.ax-X2-K0-CK20-CCK'-CCK'=CK20-S0-CK10-CCK'-X2-S0-S0-S0-S1-S2-S2-S2-CS01-CS12-CS12
  hb2157 = ListNF.listnfeq' nf-p24k0d auto

  hb2158 : Goal L.ax-X2-K0-CCK'=K0-CK10-CCK'-X2-S1-CS01-CS12-CS12-CS12-CCZ
  hb2158 = ListNF.listnfeq' nf-p24k0d auto

  hb2159 : Goal L.ax-X2-K0-CCK'-CCK'=K0-S0-CK10-CCK'-X2-S0-S0-S0-S1-CS01-CS12-CS12
  hb2159 = ListNF.listnfeq' nf-p24k0d auto

  hb2160 : Goal L.ax-X2-CK10-CCK'=CCK'-X2-CS01-CS12-CS12-CS12-CCZ
  hb2160 = ListNF.listnfeq' nf-p24k0d auto

  hb2161 : Goal L.ax-X2-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-X2-CCX0-S0-S0-S0-S1-CS01-CS01-CS12-CS12-CCZ
  hb2161 = ListNF.listnfeq' nf-p24k0d auto

  hb2162 : Goal L.ax-X2-CK20=K0-CK20-X2-S2-S2-S2-iI
  hb2162 = ListNF.listnfeq' nf-p24k0d auto

  hb2163 : Goal L.ax-X2-CK20-S0-CK10=K0-CK20-S0-CK10-X2-S2-S2-S2-iI
  hb2163 = ListNF.listnfeq' nf-p24k0d auto

  hb2164 : Goal L.ax-X2-CK20-S0-CK10-CCK'=K0-CK20-CCK'-CCK'-X2-S0-S1-S2-S2-S2-CS01-CS01-CS01-CS12-CS12-iI
  hb2164 = ListNF.listnfeq' nf-p24k0d auto

  hb2165 : Goal L.ax-X2-CK20-S0-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-X2-CX10-CCX0-S0-S1-S1-S2-S2-S2-CS01-CS01-CS12-iI
  hb2165 = ListNF.listnfeq' nf-p24k0d auto

  hb2166 : Goal L.ax-X2-CK20-CK10=K0-CK20-CK10-X2-S2-S2-S2-iI
  hb2166 = ListNF.listnfeq' nf-p24k0d auto

  hb2167 : Goal L.ax-X2-CK20-CK10-CCK'=K0-CK20-CCK'-X2-S2-S2-S2-CS01-CS12-CS12-CS12-CCZ-iI
  hb2167 = ListNF.listnfeq' nf-p24k0d auto

  hb2168 : Goal L.ax-X2-CK20-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-X2-CCX0-S0-S0-S0-S1-S2-S2-S2-CS01-CS01-CS12-CS12-CCZ-iI
  hb2168 = ListNF.listnfeq' nf-p24k0d auto

  hb2169 : Goal L.ax-X2-CK20-CCK'=K0-CK20-CK10-CCK'-X2-S1-S2-S2-S2-CS01-CS12-CS12-CS12-CCZ-iI
  hb2169 = ListNF.listnfeq' nf-p24k0d auto

  hb2170 : Goal L.ax-X2-CK20-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-X2-S0-S0-S0-S1-S2-S2-S2-CS01-CS12-CS12-iI
  hb2170 = ListNF.listnfeq' nf-p24k0d auto

  hb2171 : Goal L.ax-X2-CCK'=CK10-CCK'-X2-S1-CS01-CS12-CS12-CS12-CCZ
  hb2171 = ListNF.listnfeq' nf-p24k0d auto

  hb2172 : Goal L.ax-X2-CCK'-CCK'=S0-CK10-CCK'-X2-S0-S0-S0-S1-CS01-CS12-CS12
  hb2172 = ListNF.listnfeq' nf-p24k0d auto

  hb2173 : Goal L.ax-CX10-S0-K0-S0-CK10=S0-K0-S0-CK10-CS01-CS01
  hb2173 = ListNF.listnfeq' nf-e4 auto

  hb2174 : Goal L.ax-CX10-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK10-CCK'-CCX0-CS01-CS01-CS12
  hb2174 = ListNF.listnfeq' nf-e4 auto

  hb2175 : Goal L.ax-CX10-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-CCX0-CS01-CS01-CCZ
  hb2175 = ListNF.listnfeq' nf-e4 auto

  hb2176 : Goal L.ax-CX10-S0-K0-S0-CK20=S0-K0-S0-CK20-CX10-CCX0-CCZ
  hb2176 = ListNF.listnfeq' nf-e4 auto

  hb2177 : Goal L.ax-CX10-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-CX10-S1-CS01-CS01-CS12-CS12-CS12-CCZ
  hb2177 = ListNF.listnfeq' nf-e4 auto

  hb2178 : Goal L.ax-CX10-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CX10-CCX0-S1-CS01-CS01-CS12-CS12-CS12
  hb2178 = ListNF.listnfeq' nf-e4 auto

  hb2179 : Goal L.ax-CX10-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-CX10-S1-CS01-CS01
  hb2179 = ListNF.listnfeq' nf-e4 auto

  hb2180 : Goal L.ax-CX10-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-CCX0-CS01-CS01-CCZ
  hb2180 = ListNF.listnfeq' nf-e4 auto

  hb2181 : Goal L.ax-CX10-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-CS01-CS01
  hb2181 = ListNF.listnfeq' nf-e4 auto

  hb2182 : Goal L.ax-CX10-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-CCX0-CS01-CS01-CS12
  hb2182 = ListNF.listnfeq' nf-e4 auto

  hb2183 : Goal L.ax-CX10-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CCK'-CX10-CS12-CCZ
  hb2183 = ListNF.listnfeq' nf-e4 auto

  hb2184 : Goal L.ax-CX10-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-CX10
  hb2184 = ListNF.listnfeq' nf-e4 auto

  hb2185 : Goal L.ax-CX10-S0-K0-CK10=S0-K0-CK10-CX10-S1-S1-S1-CS01-CS01
  hb2185 = ListNF.listnfeq' nf-e4 auto

  hb2186 : Goal L.ax-CX10-S0-K0-CK10-CCK'=S0-K0-CK10-CCK'-CX10-S1-S1-S1-CS01-CS01-CS12-CS12-CS12-CCZ
  hb2186 = ListNF.listnfeq' nf-e4 auto

  hb2187 : Goal L.ax-CX10-S0-K0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-CX10-CCX0-S1-S1-S1-CS01-CS01-CS12-CS12-CS12
  hb2187 = ListNF.listnfeq' nf-e4 auto

  hb2188 : Goal L.ax-CX10-S0-K0-CK20=S0-K0-CK20-CX10-S1-CS01-CS01-CS12-CS12
  hb2188 = ListNF.listnfeq' nf-e4 auto

  hb2189 : Goal L.ax-CX10-S0-K0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-CS01-CS01-CS12-CS12
  hb2189 = ListNF.listnfeq' nf-e4 auto

  hb2190 : Goal L.ax-CX10-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCX0-CS01-CS01-CS12-CS12-CS12
  hb2190 = ListNF.listnfeq' nf-e4 auto

  hb2191 : Goal L.ax-CX10-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-CCX0-CS01-CS01-CS12-CS12-CCZ
  hb2191 = ListNF.listnfeq' nf-e4 auto

  hb2192 : Goal L.ax-CX10-S0-K0-CK20-CK10=S0-K0-CK20-CK10-CX10-S1-S1-S1-CS01-CS01-CS12-CS12
  hb2192 = ListNF.listnfeq' nf-e4 auto

  hb2193 : Goal L.ax-CX10-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CX10-S1-S1-S1-CS01-CS01-CS12-CCZ
  hb2193 = ListNF.listnfeq' nf-e4 auto

  hb2194 : Goal L.ax-CX10-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-CX10-CCX0-S1-S1-S1-CS01-CS01-CS12
  hb2194 = ListNF.listnfeq' nf-e4 auto

  hb2195 : Goal L.ax-CX10-S0-K0-CK20-CCK'=S0-K0-CK20-CCK'-CX10-S1-CS01-CS01-CS12-CCZ
  hb2195 = ListNF.listnfeq' nf-e4 auto

  hb2196 : Goal L.ax-CX10-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-CX10-CCX0-S1-CS01-CS01-CS12
  hb2196 = ListNF.listnfeq' nf-e4 auto

  hb2197 : Goal L.ax-CX10-S0-K0-CCK'=S0-K0-CCK'-CX10-S1-CS01-CS01-CS12-CS12-CS12-CCZ
  hb2197 = ListNF.listnfeq' nf-e4 auto

  hb2198 : Goal L.ax-CX10-S0-K0-CCK'-CCK'=S0-K0-CCK'-CCK'-CX10-CCX0-S1-CS01-CS01-CS12-CS12-CS12
  hb2198 = ListNF.listnfeq' nf-e4 auto

  hb2199 : Goal L.ax-CX10-S0-CK10-CCK'=S0-CK10-CCK'-CX10-S1-CS01-CS01-CS12-CS12-CS12-CCZ
  hb2199 = ListNF.listnfeq' nf-e3 auto

  hb2200 : Goal L.ax-CX10-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-CX10-CCX0-S1-CS01-CS01-CS12-CS12-CS12
  hb2200 = ListNF.listnfeq' nf-e3 auto

  hb2201 : Goal L.ax-CX10-S0-CK20-S0-CK10=S0-CK20-S0-CK10-S1-S1-CS01-CS01-CS12-CS12
  hb2201 = ListNF.listnfeq' nf-e3 auto

  hb2202 : Goal L.ax-CX10-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-CCX0-S1-S1-CS01-CS01-CS12-CS12-CS12
  hb2202 = ListNF.listnfeq' nf-e3 auto

  hb2203 : Goal L.ax-CX10-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-CCX0-S1-S1-CS01-CS01-CS12-CS12-CCZ
  hb2203 = ListNF.listnfeq' nf-e3 auto

  hb2204 : Goal L.ax-CX10-S0-CK20-CK10=S0-CK20-CK10-CX10-S1-CS01-CS01-CS12-CS12
  hb2204 = ListNF.listnfeq' nf-e3 auto

  hb2205 : Goal L.ax-CX10-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-CX10-S1-CS01-CS01-CS12-CCZ
  hb2205 = ListNF.listnfeq' nf-e3 auto

  hb2206 : Goal L.ax-CX10-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-CX10-CCX0-S1-CS01-CS01-CS12
  hb2206 = ListNF.listnfeq' nf-e3 auto

  hb2207 : Goal L.ax-CX10-S0-CK20-CCK'=S0-CK20-CCK'-CX10-S1-S1-S1-CS01-CS01-CS12-CCZ
  hb2207 = ListNF.listnfeq' nf-e3 auto

  hb2208 : Goal L.ax-CX10-S0-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-CX10-CCX0-S1-S1-S1-CS01-CS01-CS12
  hb2208 = ListNF.listnfeq' nf-e3 auto

  hb2209 : Goal L.ax-CX10-K0-S0-CK10=K0-S0-CK10-CX10
  hb2209 = ListNF.listnfeq' nf-e4 auto

  hb2210 : Goal L.ax-CX10-K0-S0-CK10-CCK'=K0-S0-CK10-CCK'-CX10-CCX0-CCZ
  hb2210 = ListNF.listnfeq' nf-e4 auto

  hb2211 : Goal L.ax-CX10-K0-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-CX10-CS12-CCZ
  hb2211 = ListNF.listnfeq' nf-e4 auto

  hb2212 : Goal L.ax-CX10-K0-S0-CK20=K0-S0-CK20-CCX0-CS01-CS01-CCZ
  hb2212 = ListNF.listnfeq' nf-e4 auto

  hb2213 : Goal L.ax-CX10-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-CX10-CS12-CCZ
  hb2213 = ListNF.listnfeq' nf-e4 auto

  hb2214 : Goal L.ax-CX10-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-CX10
  hb2214 = ListNF.listnfeq' nf-e4 auto

  hb2215 : Goal L.ax-CX10-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-CX10-CCX0-CCZ
  hb2215 = ListNF.listnfeq' nf-e4 auto

  hb2216 : Goal L.ax-CX10-K0-S0-CK20-CK10=K0-S0-CK20-CK10-CX10-CCX0-CCZ
  hb2216 = ListNF.listnfeq' nf-e4 auto

  hb2217 : Goal L.ax-CX10-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CX10-CS12-CCZ
  hb2217 = ListNF.listnfeq' nf-e4 auto

  hb2218 : Goal L.ax-CX10-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-CX10
  hb2218 = ListNF.listnfeq' nf-e4 auto

  hb2219 : Goal L.ax-CX10-K0-S0-CK20-CCK'=K0-S0-CK20-CCK'-CS01-CS01
  hb2219 = ListNF.listnfeq' nf-e4 auto

  hb2220 : Goal L.ax-CX10-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-CCX0-CS01-CS01-CS12
  hb2220 = ListNF.listnfeq' nf-e4 auto

  hb2221 : Goal L.ax-CX10-K0-CK10=K0-CK10-CX10
  hb2221 = ListNF.listnfeq' nf-e4 auto

  hb2222 : Goal L.ax-CX10-K0-CK10-CCK'=K0-CK10-CCK'-CX10-CCX0-CCZ
  hb2222 = ListNF.listnfeq' nf-e4 auto

  hb2223 : Goal L.ax-CX10-K0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-CX10-CS12-CCZ
  hb2223 = ListNF.listnfeq' nf-e4 auto

  hb2224 : Goal L.ax-CX10-K0-CK20=K0-CK20-CCX0-CS01-CS01-CCZ
  hb2224 = ListNF.listnfeq' nf-e4 auto

  hb2225 : Goal L.ax-CX10-K0-CK20-S0-CK10=K0-CK20-S0-CK10-CX10-CS12-CCZ
  hb2225 = ListNF.listnfeq' nf-e4 auto

  hb2226 : Goal L.ax-CX10-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-CX10
  hb2226 = ListNF.listnfeq' nf-e4 auto

  hb2227 : Goal L.ax-CX10-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-CX10-CCX0-CCZ
  hb2227 = ListNF.listnfeq' nf-e4 auto

  hb2228 : Goal L.ax-CX10-K0-CK20-CK10=K0-CK20-CK10-CX10-CCX0-CCZ
  hb2228 = ListNF.listnfeq' nf-e4 auto

  hb2229 : Goal L.ax-CX10-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-CX10-CS12-CCZ
  hb2229 = ListNF.listnfeq' nf-e4 auto

  hb2230 : Goal L.ax-CX10-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-CX10
  hb2230 = ListNF.listnfeq' nf-e4 auto

  hb2231 : Goal L.ax-CX10-K0-CK20-CCK'=K0-CK20-CCK'-CS01-CS01
  hb2231 = ListNF.listnfeq' nf-e4 auto

  hb2232 : Goal L.ax-CX10-K0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCK'-CCX0-CS01-CS01-CS12
  hb2232 = ListNF.listnfeq' nf-e4 auto

  hb2233 : Goal L.ax-CX10-K0-CCK'=K0-CCK'-CCX0-CS01-CS01-CS12
  hb2233 = ListNF.listnfeq' nf-e4 auto

  hb2234 : Goal L.ax-CX10-K0-CCK'-CCK'=K0-CCK'-CCK'-CCX0-CS01-CS01-CCZ
  hb2234 = ListNF.listnfeq' nf-e4 auto

  hb2235 : Goal L.ax-CX10-CK10-CCK'=CK10-CCK'-CCX0-CS01-CS01-CS12
  hb2235 = ListNF.listnfeq' nf-e3 auto

  hb2236 : Goal L.ax-CX10-CK10-CCK'-CCK'=CK10-CCK'-CCK'-CCX0-CS01-CS01-CCZ
  hb2236 = ListNF.listnfeq' nf-e3 auto

  hb2237 : Goal L.ax-CX10-CK20-S0-CK10=CK20-S0-CK10-CX10-S1-CS01-CS01-CS12-CS12-CS12-CCZ
  hb2237 = ListNF.listnfeq' nf-e3 auto

  hb2238 : Goal L.ax-CX10-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-CX10-CCX0-S1-CS01-CS01-CS12-CS12-CS12
  hb2238 = ListNF.listnfeq' nf-e3 auto

  hb2239 : Goal L.ax-CX10-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-CX10-S1-CS01-CS01
  hb2239 = ListNF.listnfeq' nf-e3 auto

  hb2240 : Goal L.ax-CX10-CK20-CK10=CK20-CK10-CCX0-CS01-CS01-CCZ
  hb2240 = ListNF.listnfeq' nf-e3 auto

  hb2241 : Goal L.ax-CX10-CK20-CK10-CCK'=CK20-CK10-CCK'-CS01-CS01
  hb2241 = ListNF.listnfeq' nf-e3 auto

  hb2242 : Goal L.ax-CX10-CK20-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-CCX0-CS01-CS01-CS12
  hb2242 = ListNF.listnfeq' nf-e3 auto

  hb2243 : Goal L.ax-CX10-CK20-CCK'=CK20-CCK'-CX10-CS12-CCZ
  hb2243 = ListNF.listnfeq' nf-e3 auto

  hb2244 : Goal L.ax-CX10-CK20-CCK'-CCK'=CK20-CCK'-CCK'-CX10
  hb2244 = ListNF.listnfeq' nf-e3 auto

  hb2245 : Goal L.ax-CX12-S0-K0=S0-K0-CX12
  hb2245 = ListNF.listnfeq' nf-p24k0d auto

  hb2246 : Goal L.ax-CX12-S0-K0-S0-CK10=S0-K0-S0-CK10-CX12
  hb2246 = ListNF.listnfeq' nf-p24k0d auto

  hb2247 : Goal L.ax-CX12-S0-K0-S0-CK10-CCK'=S0-K0-CCK'-CCK'-CX12-S0-S1-CS01-CS01-CS01-CS12-CS12
  hb2247 = ListNF.listnfeq' nf-p24k0d auto

  hb2248 : Goal L.ax-CX12-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-CX12-CX10-CCX0-S0-S1-S1-CS01-CS01-CS12
  hb2248 = ListNF.listnfeq' nf-p24k0d auto

  hb2249 : Goal L.ax-CX12-S0-K0-S0-CK20=S0-K0-S0-CK20-CK10-CX12-S1-CS12-CS12-CS12
  hb2249 = ListNF.listnfeq' nf-p24k0d auto

  hb2250 : Goal L.ax-CX12-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-CX12-CX10-S1-CS01-CS01-CS01-CS12-CS12-CS12
  hb2250 = ListNF.listnfeq' nf-p24k0d auto

  hb2251 : Goal L.ax-CX12-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-CX12-S0-S1-S1-CS01-CS01-CS01-CS12
  hb2251 = ListNF.listnfeq' nf-p24k0d auto

  hb2252 : Goal L.ax-CX12-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-CX12-CX10-CCX0-S0-S1-S1-CS01-CS01
  hb2252 = ListNF.listnfeq' nf-p24k0d auto

  hb2253 : Goal L.ax-CX12-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CX12-CS12-CS12-CS12
  hb2253 = ListNF.listnfeq' nf-p24k0d auto

  hb2254 : Goal L.ax-CX12-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-CX12-S1-CS01-CS12-CS12-CCZ
  hb2254 = ListNF.listnfeq' nf-p24k0d auto

  hb2255 : Goal L.ax-CX12-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CX12-S0-S0-S0-S1-CS01-CS12
  hb2255 = ListNF.listnfeq' nf-p24k0d auto

  hb2256 : Goal L.ax-CX12-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CCK'-CX12-S1-CS01-CS12-CS12-CCZ
  hb2256 = ListNF.listnfeq' nf-p24k0d auto

  hb2257 : Goal L.ax-CX12-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-CX12-CCX0-S0-S0-S0-S1-S1-CS01-CS01-CS12-CCZ
  hb2257 = ListNF.listnfeq' nf-p24k0d auto

  hb2258 : Goal L.ax-CX12-S0-K0-CK10=S0-K0-CK10-CX12
  hb2258 = ListNF.listnfeq' nf-p24k0d auto

  hb2259 : Goal L.ax-CX12-S0-K0-CK10-CCK'=S0-K0-CCK'-CX12-CS01-CS12-CS12-CS12-CCZ
  hb2259 = ListNF.listnfeq' nf-p24k0d auto

  hb2260 : Goal L.ax-CX12-S0-K0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-CX12-CCX0-S0-S0-S0-S1-CS01-CS01-CS12-CS12-CCZ
  hb2260 = ListNF.listnfeq' nf-p24k0d auto

  hb2261 : Goal L.ax-CX12-S0-K0-CK20=S0-K0-CK20-CK10-CX12-S1-CS12-CS12-CS12
  hb2261 = ListNF.listnfeq' nf-p24k0d auto

  hb2262 : Goal L.ax-CX12-S0-K0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-CX12-CX10-S1-CS01-CS01-CS01-CS12-CS12-CS12
  hb2262 = ListNF.listnfeq' nf-p24k0d auto

  hb2263 : Goal L.ax-CX12-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-CX12-S0-S1-S1-CS01-CS01-CS01-CS12
  hb2263 = ListNF.listnfeq' nf-p24k0d auto

  hb2264 : Goal L.ax-CX12-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-CX12-CX10-CCX0-S0-S1-S1-CS01-CS01
  hb2264 = ListNF.listnfeq' nf-p24k0d auto

  hb2265 : Goal L.ax-CX12-S0-K0-CK20-CK10=S0-K0-CK20-CX12-CS12-CS12-CS12
  hb2265 = ListNF.listnfeq' nf-p24k0d auto

  hb2266 : Goal L.ax-CX12-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CX12-S1-CS01-CS12-CS12-CCZ
  hb2266 = ListNF.listnfeq' nf-p24k0d auto

  hb2267 : Goal L.ax-CX12-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CX12-S0-S0-S0-S1-CS01-CS12
  hb2267 = ListNF.listnfeq' nf-p24k0d auto

  hb2268 : Goal L.ax-CX12-S0-K0-CK20-CCK'=S0-K0-CK20-CCK'-CX12-S1-CS01-CS12-CS12-CCZ
  hb2268 = ListNF.listnfeq' nf-p24k0d auto

  hb2269 : Goal L.ax-CX12-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-CX12-CCX0-S0-S0-S0-S1-S1-CS01-CS01-CS12-CCZ
  hb2269 = ListNF.listnfeq' nf-p24k0d auto

  hb2270 : Goal L.ax-CX12-S0-K0-CCK'=S0-K0-CK10-CCK'-CX12-S1-CS01-CS12-CS12-CS12-CCZ
  hb2270 = ListNF.listnfeq' nf-p24k0d auto

  hb2271 : Goal L.ax-CX12-S0-K0-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CX12-S0-S0-S0-S1-CS01-CS12-CS12
  hb2271 = ListNF.listnfeq' nf-p24k0d auto

  hb2272 : Goal L.ax-CX12-S0-CK10=S0-CK10-CX12
  hb2272 = ListNF.listnfeq' nf-p24k0d auto

  hb2273 : Goal L.ax-CX12-S0-CK10-CCK'=CCK'-CCK'-CX12-S0-S1-CS01-CS01-CS01-CS12-CS12
  hb2273 = ListNF.listnfeq' nf-p24k0d auto

  hb2274 : Goal L.ax-CX12-S0-CK10-CCK'-CCK'=CK10-CCK'-CCK'-CX12-CX10-CCX0-S0-S1-S1-CS01-CS01-CS12
  hb2274 = ListNF.listnfeq' nf-p24k0d auto

  hb2275 : Goal L.ax-CX12-S0-CK20=S0-CK20-CK10-CX12-S1-CS12-CS12-CS12
  hb2275 = ListNF.listnfeq' nf-p24k0d auto

  hb2276 : Goal L.ax-CX12-S0-CK20-S0-CK10=S0-CK20-S0-CK10-CX12-CX10-S1-CS01-CS01-CS01-CS12-CS12-CS12
  hb2276 = ListNF.listnfeq' nf-p24k0d auto

  hb2277 : Goal L.ax-CX12-S0-CK20-S0-CK10-CCK'=S0-CK20-CK10-CCK'-CCK'-CX12-S0-S1-S1-CS01-CS01-CS01-CS12
  hb2277 = ListNF.listnfeq' nf-p24k0d auto

  hb2278 : Goal L.ax-CX12-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-CCK'-CCK'-CX12-CX10-CCX0-S0-S1-S1-CS01-CS01
  hb2278 = ListNF.listnfeq' nf-p24k0d auto

  hb2279 : Goal L.ax-CX12-S0-CK20-CK10=S0-CK20-CX12-CS12-CS12-CS12
  hb2279 = ListNF.listnfeq' nf-p24k0d auto

  hb2280 : Goal L.ax-CX12-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-CX12-S1-CS01-CS12-CS12-CCZ
  hb2280 = ListNF.listnfeq' nf-p24k0d auto

  hb2281 : Goal L.ax-CX12-S0-CK20-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CX12-S0-S0-S0-S1-CS01-CS12
  hb2281 = ListNF.listnfeq' nf-p24k0d auto

  hb2282 : Goal L.ax-CX12-S0-CK20-CCK'=S0-CK20-CCK'-CX12-S1-CS01-CS12-CS12-CCZ
  hb2282 = ListNF.listnfeq' nf-p24k0d auto

  hb2283 : Goal L.ax-CX12-S0-CK20-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-CX12-CCX0-S0-S0-S0-S1-S1-CS01-CS01-CS12-CCZ
  hb2283 = ListNF.listnfeq' nf-p24k0d auto

  hb2284 : Goal L.ax-CX12-K0-S0-CK10=K0-S0-CK10-CX12
  hb2284 = ListNF.listnfeq' nf-p24k0d auto

  hb2285 : Goal L.ax-CX12-K0-S0-CK10-CCK'=K0-CCK'-CCK'-CX12-S0-S1-CS01-CS01-CS01-CS12-CS12
  hb2285 = ListNF.listnfeq' nf-p24k0d auto

  hb2286 : Goal L.ax-CX12-K0-S0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-CX12-CX10-CCX0-S0-S1-S1-CS01-CS01-CS12
  hb2286 = ListNF.listnfeq' nf-p24k0d auto

  hb2287 : Goal L.ax-CX12-K0-S0-CK20=K0-S0-CK20-CK10-CX12-S1-CS12-CS12-CS12
  hb2287 = ListNF.listnfeq' nf-p24k0d auto

  hb2288 : Goal L.ax-CX12-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-CX12-CX10-S1-CS01-CS01-CS01-CS12-CS12-CS12
  hb2288 = ListNF.listnfeq' nf-p24k0d auto

  hb2289 : Goal L.ax-CX12-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-CX12-S0-S1-S1-CS01-CS01-CS01-CS12
  hb2289 = ListNF.listnfeq' nf-p24k0d auto

  hb2290 : Goal L.ax-CX12-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-CX12-CX10-CCX0-S0-S1-S1-CS01-CS01
  hb2290 = ListNF.listnfeq' nf-p24k0d auto

  hb2291 : Goal L.ax-CX12-K0-S0-CK20-CK10=K0-S0-CK20-CX12-CS12-CS12-CS12
  hb2291 = ListNF.listnfeq' nf-p24k0d auto

  hb2292 : Goal L.ax-CX12-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CX12-S1-CS01-CS12-CS12-CCZ
  hb2292 = ListNF.listnfeq' nf-p24k0d auto

  hb2293 : Goal L.ax-CX12-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CX12-S0-S0-S0-S1-CS01-CS12
  hb2293 = ListNF.listnfeq' nf-p24k0d auto

  hb2294 : Goal L.ax-CX12-K0-S0-CK20-CCK'=K0-S0-CK20-CCK'-CX12-S1-CS01-CS12-CS12-CCZ
  hb2294 = ListNF.listnfeq' nf-p24k0d auto

  hb2295 : Goal L.ax-CX12-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-CX12-CCX0-S0-S0-S0-S1-S1-CS01-CS01-CS12-CCZ
  hb2295 = ListNF.listnfeq' nf-p24k0d auto

  hb2296 : Goal L.ax-CX12-K0-CK10=K0-CK10-CX12
  hb2296 = ListNF.listnfeq' nf-p24k0d auto

  hb2297 : Goal L.ax-CX12-K0-CK10-CCK'=K0-CCK'-CX12-CS01-CS12-CS12-CS12-CCZ
  hb2297 = ListNF.listnfeq' nf-p24k0d auto

  hb2298 : Goal L.ax-CX12-K0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-CX12-CCX0-S0-S0-S0-S1-CS01-CS01-CS12-CS12-CCZ
  hb2298 = ListNF.listnfeq' nf-p24k0d auto

  hb2299 : Goal L.ax-CX12-K0-CK20=K0-CK20-CK10-CX12-S1-CS12-CS12-CS12
  hb2299 = ListNF.listnfeq' nf-p24k0d auto

  hb2300 : Goal L.ax-CX12-K0-CK20-S0-CK10=K0-CK20-S0-CK10-CX12-CX10-S1-CS01-CS01-CS01-CS12-CS12-CS12
  hb2300 = ListNF.listnfeq' nf-p24k0d auto

  hb2301 : Goal L.ax-CX12-K0-CK20-S0-CK10-CCK'=K0-CK20-CK10-CCK'-CCK'-CX12-S0-S1-S1-CS01-CS01-CS01-CS12
  hb2301 = ListNF.listnfeq' nf-p24k0d auto

  hb2302 : Goal L.ax-CX12-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-CCK'-CCK'-CX12-CX10-CCX0-S0-S1-S1-CS01-CS01
  hb2302 = ListNF.listnfeq' nf-p24k0d auto

  hb2303 : Goal L.ax-CX12-K0-CK20-CK10=K0-CK20-CX12-CS12-CS12-CS12
  hb2303 = ListNF.listnfeq' nf-p24k0d auto

  hb2304 : Goal L.ax-CX12-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-CX12-S1-CS01-CS12-CS12-CCZ
  hb2304 = ListNF.listnfeq' nf-p24k0d auto

  hb2305 : Goal L.ax-CX12-K0-CK20-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CX12-S0-S0-S0-S1-CS01-CS12
  hb2305 = ListNF.listnfeq' nf-p24k0d auto

  hb2306 : Goal L.ax-CX12-K0-CK20-CCK'=K0-CK20-CCK'-CX12-S1-CS01-CS12-CS12-CCZ
  hb2306 = ListNF.listnfeq' nf-p24k0d auto

  hb2307 : Goal L.ax-CX12-K0-CK20-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-CX12-CCX0-S0-S0-S0-S1-S1-CS01-CS01-CS12-CCZ
  hb2307 = ListNF.listnfeq' nf-p24k0d auto

  hb2308 : Goal L.ax-CX12-K0-CCK'=K0-CK10-CCK'-CX12-S1-CS01-CS12-CS12-CS12-CCZ
  hb2308 = ListNF.listnfeq' nf-p24k0d auto

  hb2309 : Goal L.ax-CX12-K0-CCK'-CCK'=K0-S0-CK10-CCK'-CX12-S0-S0-S0-S1-CS01-CS12-CS12
  hb2309 = ListNF.listnfeq' nf-p24k0d auto

  hb2310 : Goal L.ax-CX12-CK10-CCK'=CCK'-CX12-CS01-CS12-CS12-CS12-CCZ
  hb2310 = ListNF.listnfeq' nf-p24k0d auto

  hb2311 : Goal L.ax-CX12-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-CX12-CCX0-S0-S0-S0-S1-CS01-CS01-CS12-CS12-CCZ
  hb2311 = ListNF.listnfeq' nf-p24k0d auto

  hb2312 : Goal L.ax-CX12-CK20=CK20-CK10-CX12-S1-CS12-CS12-CS12
  hb2312 = ListNF.listnfeq' nf-p24k0d auto

  hb2313 : Goal L.ax-CX12-CK20-S0-CK10=CK20-S0-CK10-CX12-CX10-S1-CS01-CS01-CS01-CS12-CS12-CS12
  hb2313 = ListNF.listnfeq' nf-p24k0d auto

  hb2314 : Goal L.ax-CX12-CK20-S0-CK10-CCK'=CK20-CK10-CCK'-CCK'-CX12-S0-S1-S1-CS01-CS01-CS01-CS12
  hb2314 = ListNF.listnfeq' nf-p24k0d auto

  hb2315 : Goal L.ax-CX12-CK20-S0-CK10-CCK'-CCK'=CK20-CCK'-CCK'-CX12-CX10-CCX0-S0-S1-S1-CS01-CS01
  hb2315 = ListNF.listnfeq' nf-p24k0d auto

  hb2316 : Goal L.ax-CX12-CK20-CK10=CK20-CX12-CS12-CS12-CS12
  hb2316 = ListNF.listnfeq' nf-p24k0d auto

  hb2317 : Goal L.ax-CX12-CK20-CK10-CCK'=CK20-CK10-CCK'-CX12-S1-CS01-CS12-CS12-CCZ
  hb2317 = ListNF.listnfeq' nf-p24k0d auto

  hb2318 : Goal L.ax-CX12-CK20-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CX12-S0-S0-S0-S1-CS01-CS12
  hb2318 = ListNF.listnfeq' nf-p24k0d auto

  hb2319 : Goal L.ax-CX12-CK20-CCK'=CK20-CCK'-CX12-S1-CS01-CS12-CS12-CCZ
  hb2319 = ListNF.listnfeq' nf-p24k0d auto

  hb2320 : Goal L.ax-CX12-CK20-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-CX12-CCX0-S0-S0-S0-S1-S1-CS01-CS01-CS12-CCZ
  hb2320 = ListNF.listnfeq' nf-p24k0d auto

  hb2321 : Goal L.ax-CX12-CCK'=CK10-CCK'-CX12-S1-CS01-CS12-CS12-CS12-CCZ
  hb2321 = ListNF.listnfeq' nf-p24k0d auto

  hb2322 : Goal L.ax-CX12-CCK'-CCK'=S0-CK10-CCK'-CX12-S0-S0-S0-S1-CS01-CS12-CS12
  hb2322 = ListNF.listnfeq' nf-p24k0d auto

  hb2323 : Goal L.ax-CX20-S0-K0-S0-CK10=S0-K0-S0-CK10-CX20-CCX0-CCZ
  hb2323 = ListNF.listnfeq' nf-e4 auto

  hb2324 : Goal L.ax-CX20-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK10-CCK'-CX20-CS12-CCZ
  hb2324 = ListNF.listnfeq' nf-e4 auto

  hb2325 : Goal L.ax-CX20-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-CX20
  hb2325 = ListNF.listnfeq' nf-e4 auto

  hb2326 : Goal L.ax-CX20-S0-K0-S0-CK20=S0-K0-S0-CK20-CS02-CS02
  hb2326 = ListNF.listnfeq' nf-e4 auto

  hb2327 : Goal L.ax-CX20-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-CCX0-CS02-CS02-CCZ
  hb2327 = ListNF.listnfeq' nf-e4 auto

  hb2328 : Goal L.ax-CX20-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CS02-CS02
  hb2328 = ListNF.listnfeq' nf-e4 auto

  hb2329 : Goal L.ax-CX20-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-CCX0-CS02-CS02-CS12
  hb2329 = ListNF.listnfeq' nf-e4 auto

  hb2330 : Goal L.ax-CX20-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-CCX0-CS02-CS02-CCZ
  hb2330 = ListNF.listnfeq' nf-e4 auto

  hb2331 : Goal L.ax-CX20-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-CS02-CS02
  hb2331 = ListNF.listnfeq' nf-e4 auto

  hb2332 : Goal L.ax-CX20-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-CCX0-CS02-CS02-CS12
  hb2332 = ListNF.listnfeq' nf-e4 auto

  hb2333 : Goal L.ax-CX20-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CCK'-CCX0-CS02-CS02-CS12
  hb2333 = ListNF.listnfeq' nf-e4 auto

  hb2334 : Goal L.ax-CX20-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-CCX0-CS02-CS02-CCZ
  hb2334 = ListNF.listnfeq' nf-e4 auto

  hb2335 : Goal L.ax-CX20-S0-K0-CK10=S0-K0-CK10-CX20-S2-CS02-CS02-CS12-CS12
  hb2335 = ListNF.listnfeq' nf-e4 auto

  hb2336 : Goal L.ax-CX20-S0-K0-CK10-CCK'=S0-K0-CK10-CCK'-CX20-S2-CS02-CS02-CS12-CCZ
  hb2336 = ListNF.listnfeq' nf-e4 auto

  hb2337 : Goal L.ax-CX20-S0-K0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-CX20-CCX0-S2-CS02-CS02-CS12
  hb2337 = ListNF.listnfeq' nf-e4 auto

  hb2338 : Goal L.ax-CX20-S0-K0-CK20=S0-K0-CK20-CX20-S2-S2-S2-CS02-CS02
  hb2338 = ListNF.listnfeq' nf-e4 auto

  hb2339 : Goal L.ax-CX20-S0-K0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-CX20-CCX0-S2-S2-CCZ
  hb2339 = ListNF.listnfeq' nf-e4 auto

  hb2340 : Goal L.ax-CX20-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-CX20-S2-S2-CS12-CCZ
  hb2340 = ListNF.listnfeq' nf-e4 auto

  hb2341 : Goal L.ax-CX20-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-CX20-S2-S2
  hb2341 = ListNF.listnfeq' nf-e4 auto

  hb2342 : Goal L.ax-CX20-S0-K0-CK20-CK10=S0-K0-CK20-CK10-CX20-S2-S2-S2-CS02-CS02-CS12-CS12
  hb2342 = ListNF.listnfeq' nf-e4 auto

  hb2343 : Goal L.ax-CX20-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CX20-S2-S2-S2-CS02-CS02-CS12-CCZ
  hb2343 = ListNF.listnfeq' nf-e4 auto

  hb2344 : Goal L.ax-CX20-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-CX20-CCX0-S2-S2-S2-CS02-CS02-CS12
  hb2344 = ListNF.listnfeq' nf-e4 auto

  hb2345 : Goal L.ax-CX20-S0-K0-CK20-CCK'=S0-K0-CK20-CCK'-CX20-S2-S2-S2-CS02-CS02-CS12-CS12-CS12-CCZ
  hb2345 = ListNF.listnfeq' nf-e4 auto

  hb2346 : Goal L.ax-CX20-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-CX20-CCX0-S2-S2-S2-CS02-CS02-CS12-CS12-CS12
  hb2346 = ListNF.listnfeq' nf-e4 auto

  hb2347 : Goal L.ax-CX20-S0-K0-CCK'=S0-K0-CCK'-CX20-S2-CS02-CS02-CS12-CS12-CS12-CCZ
  hb2347 = ListNF.listnfeq' nf-e4 auto

  hb2348 : Goal L.ax-CX20-S0-K0-CCK'-CCK'=S0-K0-CCK'-CCK'-CX20-CCX0-S2-CS02-CS02-CS12-CS12-CS12
  hb2348 = ListNF.listnfeq' nf-e4 auto

  hb2349 : Goal L.ax-CX20-S0-CK10-CCK'=S0-CK10-CCK'-CX20-S2-S2-S2-CS02-CS02-CS12-CCZ
  hb2349 = ListNF.listnfeq' nf-e3 auto

  hb2350 : Goal L.ax-CX20-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-CX20-CCX0-S2-S2-S2-CS02-CS02-CS12
  hb2350 = ListNF.listnfeq' nf-e3 auto

  hb2351 : Goal L.ax-CX20-S0-CK20-S0-CK10=S0-CK20-S0-CK10-CX20-CCX0-CCZ
  hb2351 = ListNF.listnfeq' nf-e3 auto

  hb2352 : Goal L.ax-CX20-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-CX20-CS12-CCZ
  hb2352 = ListNF.listnfeq' nf-e3 auto

  hb2353 : Goal L.ax-CX20-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-CX20
  hb2353 = ListNF.listnfeq' nf-e3 auto

  hb2354 : Goal L.ax-CX20-S0-CK20-CK10=S0-CK20-CK10-CX20-S2-CS02-CS02-CS12-CS12
  hb2354 = ListNF.listnfeq' nf-e3 auto

  hb2355 : Goal L.ax-CX20-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-CX20-S2-CS02-CS02-CS12-CCZ
  hb2355 = ListNF.listnfeq' nf-e3 auto

  hb2356 : Goal L.ax-CX20-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-CX20-CCX0-S2-CS02-CS02-CS12
  hb2356 = ListNF.listnfeq' nf-e3 auto

  hb2357 : Goal L.ax-CX20-S0-CK20-CCK'=S0-CK20-CCK'-CX20-S2-CS02-CS02-CS12-CS12-CS12-CCZ
  hb2357 = ListNF.listnfeq' nf-e3 auto

  hb2358 : Goal L.ax-CX20-S0-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-CX20-CCX0-S2-CS02-CS02-CS12-CS12-CS12
  hb2358 = ListNF.listnfeq' nf-e3 auto

  hb2359 : Goal L.ax-CX20-K0-S0-CK10=K0-S0-CK10-CCX0-CS02-CS02-CCZ
  hb2359 = ListNF.listnfeq' nf-e4 auto

  hb2360 : Goal L.ax-CX20-K0-S0-CK10-CCK'=K0-S0-CK10-CCK'-CS02-CS02
  hb2360 = ListNF.listnfeq' nf-e4 auto

  hb2361 : Goal L.ax-CX20-K0-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-CCX0-CS02-CS02-CS12
  hb2361 = ListNF.listnfeq' nf-e4 auto

  hb2362 : Goal L.ax-CX20-K0-S0-CK20=K0-S0-CK20-CX20
  hb2362 = ListNF.listnfeq' nf-e4 auto

  hb2363 : Goal L.ax-CX20-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-CX20-S2-S2-S2-CS02-CS02-CS12-CS12
  hb2363 = ListNF.listnfeq' nf-e4 auto

  hb2364 : Goal L.ax-CX20-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-CX20-S2-S2-S2-CS02-CS02-CS12-CCZ
  hb2364 = ListNF.listnfeq' nf-e4 auto

  hb2365 : Goal L.ax-CX20-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-CX20-CCX0-S2-S2-S2-CS02-CS02-CS12
  hb2365 = ListNF.listnfeq' nf-e4 auto

  hb2366 : Goal L.ax-CX20-K0-S0-CK20-CK10=K0-S0-CK20-CK10-CX20-CCX0-CCZ
  hb2366 = ListNF.listnfeq' nf-e4 auto

  hb2367 : Goal L.ax-CX20-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CX20-CS12-CCZ
  hb2367 = ListNF.listnfeq' nf-e4 auto

  hb2368 : Goal L.ax-CX20-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-CX20
  hb2368 = ListNF.listnfeq' nf-e4 auto

  hb2369 : Goal L.ax-CX20-K0-S0-CK20-CCK'=K0-S0-CK20-CCK'-CX20-CCX0-CCZ
  hb2369 = ListNF.listnfeq' nf-e4 auto

  hb2370 : Goal L.ax-CX20-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-CX20-CS12-CCZ
  hb2370 = ListNF.listnfeq' nf-e4 auto

  hb2371 : Goal L.ax-CX20-K0-CK10=K0-CK10-CCX0-CS02-CS02-CCZ
  hb2371 = ListNF.listnfeq' nf-e4 auto

  hb2372 : Goal L.ax-CX20-K0-CK10-CCK'=K0-CK10-CCK'-CS02-CS02
  hb2372 = ListNF.listnfeq' nf-e4 auto

  hb2373 : Goal L.ax-CX20-K0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-CCX0-CS02-CS02-CS12
  hb2373 = ListNF.listnfeq' nf-e4 auto

  hb2374 : Goal L.ax-CX20-K0-CK20=K0-CK20-CX20
  hb2374 = ListNF.listnfeq' nf-e4 auto

  hb2375 : Goal L.ax-CX20-K0-CK20-S0-CK10=K0-CK20-S0-CK10-CX20-S2-S2-S2-CS02-CS02-CS12-CS12
  hb2375 = ListNF.listnfeq' nf-e4 auto

  hb2376 : Goal L.ax-CX20-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-CX20-S2-S2-S2-CS02-CS02-CS12-CCZ
  hb2376 = ListNF.listnfeq' nf-e4 auto

  hb2377 : Goal L.ax-CX20-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-CX20-CCX0-S2-S2-S2-CS02-CS02-CS12
  hb2377 = ListNF.listnfeq' nf-e4 auto

  hb2378 : Goal L.ax-CX20-K0-CK20-CK10=K0-CK20-CK10-CX20-CCX0-CCZ
  hb2378 = ListNF.listnfeq' nf-e4 auto

  hb2379 : Goal L.ax-CX20-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-CX20-CS12-CCZ
  hb2379 = ListNF.listnfeq' nf-e4 auto

  hb2380 : Goal L.ax-CX20-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-CX20
  hb2380 = ListNF.listnfeq' nf-e4 auto

  hb2381 : Goal L.ax-CX20-K0-CK20-CCK'=K0-CK20-CCK'-CX20-CCX0-CCZ
  hb2381 = ListNF.listnfeq' nf-e4 auto

  hb2382 : Goal L.ax-CX20-K0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCK'-CX20-CS12-CCZ
  hb2382 = ListNF.listnfeq' nf-e4 auto

  hb2383 : Goal L.ax-CX20-K0-CCK'=K0-CCK'-CCX0-CS02-CS02-CS12
  hb2383 = ListNF.listnfeq' nf-e4 auto

  hb2384 : Goal L.ax-CX20-K0-CCK'-CCK'=K0-CCK'-CCK'-CCX0-CS02-CS02-CCZ
  hb2384 = ListNF.listnfeq' nf-e4 auto

  hb2385 : Goal L.ax-CX20-CK10-CCK'=CK10-CCK'-CX20-CS12-CCZ
  hb2385 = ListNF.listnfeq' nf-e3 auto

  hb2386 : Goal L.ax-CX20-CK10-CCK'-CCK'=CK10-CCK'-CCK'-CX20
  hb2386 = ListNF.listnfeq' nf-e3 auto

  hb2387 : Goal L.ax-CX20-CK20-S0-CK10=CK20-S0-CK10-CCX0-CS02-CS02-CCZ
  hb2387 = ListNF.listnfeq' nf-e3 auto

  hb2388 : Goal L.ax-CX20-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-CS02-CS02
  hb2388 = ListNF.listnfeq' nf-e3 auto

  hb2389 : Goal L.ax-CX20-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-CCX0-CS02-CS02-CS12
  hb2389 = ListNF.listnfeq' nf-e3 auto

  hb2390 : Goal L.ax-CX20-CK20-CK10=CK20-CK10-CCX0-CS02-CS02-CCZ
  hb2390 = ListNF.listnfeq' nf-e3 auto

  hb2391 : Goal L.ax-CX20-CK20-CK10-CCK'=CK20-CK10-CCK'-CS02-CS02
  hb2391 = ListNF.listnfeq' nf-e3 auto

  hb2392 : Goal L.ax-CX20-CK20-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-CCX0-CS02-CS02-CS12
  hb2392 = ListNF.listnfeq' nf-e3 auto

  hb2393 : Goal L.ax-CX20-CK20-CCK'=CK20-CCK'-CCX0-CS02-CS02-CS12
  hb2393 = ListNF.listnfeq' nf-e3 auto

  hb2394 : Goal L.ax-CX20-CK20-CCK'-CCK'=CK20-CCK'-CCK'-CCX0-CS02-CS02-CCZ
  hb2394 = ListNF.listnfeq' nf-e3 auto

  hb2395 : Goal L.ax-CX21-S0-K0=S0-K0-CX21
  hb2395 = ListNF.listnfeq' nf-p24k0d auto

  hb2396 : Goal L.ax-CX21-S0-K0-S0-CK10=S0-K0-S0-CK20-CK10-CX21-S2-CS12-CS12-CS12
  hb2396 = ListNF.listnfeq' nf-p24k0d auto

  hb2397 : Goal L.ax-CX21-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ
  hb2397 = ListNF.listnfeq' nf-p24k0d auto

  hb2398 : Goal L.ax-CX21-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-CX21-S2-S2-CS02-CS02-CS12
  hb2398 = ListNF.listnfeq' nf-p24k0d auto

  hb2399 : Goal L.ax-CX21-S0-K0-S0-CK20=S0-K0-S0-CK20-CX21
  hb2399 = ListNF.listnfeq' nf-p24k0d auto

  hb2400 : Goal L.ax-CX21-S0-K0-S0-CK20-S0-CK10=S0-K0-CK20-CK10-CCK'-CCK'-CX21-CX10-CCX0-S0-S0-S2-S2-CS01-CS01-CS02-CS02-CS02-CS12-CS12
  hb2400 = ListNF.listnfeq' nf-p24k0d auto

  hb2401 : Goal L.ax-CX21-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ
  hb2401 = ListNF.listnfeq' nf-p24k0d auto

  hb2402 : Goal L.ax-CX21-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-CX21-CX10-CX20-S0-S0-S2-S2-CS01-CS01-CS02-CS02-CCZ
  hb2402 = ListNF.listnfeq' nf-p24k0d auto

  hb2403 : Goal L.ax-CX21-S0-K0-S0-CK20-CK10=S0-K0-S0-CK10-CX21-CS12-CS12-CS12
  hb2403 = ListNF.listnfeq' nf-p24k0d auto

  hb2404 : Goal L.ax-CX21-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ
  hb2404 = ListNF.listnfeq' nf-p24k0d auto

  hb2405 : Goal L.ax-CX21-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CX21-CX20-S2-CS02-CS02-CS02-CCZ
  hb2405 = ListNF.listnfeq' nf-p24k0d auto

  hb2406 : Goal L.ax-CX21-S0-K0-S0-CK20-CCK'=S0-K0-CCK'-CCK'-CX21-S0-S2-CS02-CS02-CS02-CS12-CS12
  hb2406 = ListNF.listnfeq' nf-p24k0d auto

  hb2407 : Goal L.ax-CX21-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-CX21-CX20-CCX0-S0-S2-S2-CS02-CS02-CS12
  hb2407 = ListNF.listnfeq' nf-p24k0d auto

  hb2408 : Goal L.ax-CX21-S0-K0-CK10=S0-K0-CK20-CK10-CX21-S2-CS12-CS12-CS12
  hb2408 = ListNF.listnfeq' nf-p24k0d auto

  hb2409 : Goal L.ax-CX21-S0-K0-CK10-CCK'=S0-K0-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ
  hb2409 = ListNF.listnfeq' nf-p24k0d auto

  hb2410 : Goal L.ax-CX21-S0-K0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-CX21-CX10-S0-S0-S2-S2-CS01-CS01-CS02-CS02-CCZ
  hb2410 = ListNF.listnfeq' nf-p24k0d auto

