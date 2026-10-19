------------------------------------------------------------------------
-- Presentations of groups
--
-- Ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 3-qubit Clifford+CS operators"
-- (arXiv:2306.08530, CC BY 2.0).
-- 
-- Part 5 of 5 of the proofs of Step4.Main's hypB that compute normal
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

module Examples.Groups.Clifford+CS-3qubit.Step4.HypB5 where

  hb2411 : Goal L.ax-CX21-S0-K0-CK20=S0-K0-CK20-CX21
  hb2411 = ListNF.listnfeq' nf-p24k0d auto

  hb2412 : Goal L.ax-CX21-S0-K0-CK20-S0-CK10=S0-K0-S0-CK20-CK10-CCK'-CCK'-CX21-CX20-S2-S2-CS02-CS12-CS12-CCZ
  hb2412 = ListNF.listnfeq' nf-p24k0d auto

  hb2413 : Goal L.ax-CX21-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ
  hb2413 = ListNF.listnfeq' nf-p24k0d auto

  hb2414 : Goal L.ax-CX21-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-CX21-S2-CS02-CS02-CS12
  hb2414 = ListNF.listnfeq' nf-p24k0d auto

  hb2415 : Goal L.ax-CX21-S0-K0-CK20-CK10=S0-K0-CK10-CX21-CS12-CS12-CS12
  hb2415 = ListNF.listnfeq' nf-p24k0d auto

  hb2416 : Goal L.ax-CX21-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ
  hb2416 = ListNF.listnfeq' nf-p24k0d auto

  hb2417 : Goal L.ax-CX21-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CX21-CX10-CCX0-S0-S0-CS01-CS01-CS02-CS02-CS02-CS12-CS12
  hb2417 = ListNF.listnfeq' nf-p24k0d auto

  hb2418 : Goal L.ax-CX21-S0-K0-CK20-CCK'=S0-K0-CCK'-CX21-CS02-CS12-CS12-CS12-CCZ
  hb2418 = ListNF.listnfeq' nf-p24k0d auto

  hb2419 : Goal L.ax-CX21-S0-K0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-CX21-CCX0-S0-S0-S0-S2-CS02-CS02-CS12-CS12-CCZ
  hb2419 = ListNF.listnfeq' nf-p24k0d auto

  hb2420 : Goal L.ax-CX21-S0-K0-CCK'=S0-K0-CK20-CCK'-CX21-S2-CS02-CS12-CS12-CS12-CCZ
  hb2420 = ListNF.listnfeq' nf-p24k0d auto

  hb2421 : Goal L.ax-CX21-S0-K0-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CX21-S0-S0-S0-S2-CS02-CS12-CS12
  hb2421 = ListNF.listnfeq' nf-p24k0d auto

  hb2422 : Goal L.ax-CX21-S0-CK10=S0-CK20-CK10-CX21-S2-CS12-CS12-CS12
  hb2422 = ListNF.listnfeq' nf-p24k0d auto

  hb2423 : Goal L.ax-CX21-S0-CK10-CCK'=S0-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ
  hb2423 = ListNF.listnfeq' nf-p24k0d auto

  hb2424 : Goal L.ax-CX21-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-CX21-S2-S2-CS02-CS02-CS12
  hb2424 = ListNF.listnfeq' nf-p24k0d auto

  hb2425 : Goal L.ax-CX21-S0-CK20=S0-CK20-CX21
  hb2425 = ListNF.listnfeq' nf-p24k0d auto

  hb2426 : Goal L.ax-CX21-S0-CK20-S0-CK10=CK20-CK10-CCK'-CCK'-CX21-CX10-CCX0-S0-S0-S2-S2-CS01-CS01-CS02-CS02-CS02-CS12-CS12
  hb2426 = ListNF.listnfeq' nf-p24k0d auto

  hb2427 : Goal L.ax-CX21-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ
  hb2427 = ListNF.listnfeq' nf-p24k0d auto

  hb2428 : Goal L.ax-CX21-S0-CK20-S0-CK10-CCK'-CCK'=CK10-CCK'-CCK'-CX21-CX10-CX20-S0-S0-S2-S2-CS01-CS01-CS02-CS02-CCZ
  hb2428 = ListNF.listnfeq' nf-p24k0d auto

  hb2429 : Goal L.ax-CX21-S0-CK20-CK10=S0-CK10-CX21-CS12-CS12-CS12
  hb2429 = ListNF.listnfeq' nf-p24k0d auto

  hb2430 : Goal L.ax-CX21-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ
  hb2430 = ListNF.listnfeq' nf-p24k0d auto

  hb2431 : Goal L.ax-CX21-S0-CK20-CK10-CCK'-CCK'=CK20-S0-CK10-CX21-CX20-S2-CS02-CS02-CS02-CCZ
  hb2431 = ListNF.listnfeq' nf-p24k0d auto

  hb2432 : Goal L.ax-CX21-S0-CK20-CCK'=CCK'-CCK'-CX21-S0-S2-CS02-CS02-CS02-CS12-CS12
  hb2432 = ListNF.listnfeq' nf-p24k0d auto

  hb2433 : Goal L.ax-CX21-S0-CK20-CCK'-CCK'=CK20-CCK'-CCK'-CX21-CX20-CCX0-S0-S2-S2-CS02-CS02-CS12
  hb2433 = ListNF.listnfeq' nf-p24k0d auto

  hb2434 : Goal L.ax-CX21-K0-S0-CK10=K0-S0-CK20-CK10-CX21-S2-CS12-CS12-CS12
  hb2434 = ListNF.listnfeq' nf-p24k0d auto

  hb2435 : Goal L.ax-CX21-K0-S0-CK10-CCK'=K0-S0-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ
  hb2435 = ListNF.listnfeq' nf-p24k0d auto

  hb2436 : Goal L.ax-CX21-K0-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-CX21-S2-S2-CS02-CS02-CS12
  hb2436 = ListNF.listnfeq' nf-p24k0d auto

  hb2437 : Goal L.ax-CX21-K0-S0-CK20=K0-S0-CK20-CX21
  hb2437 = ListNF.listnfeq' nf-p24k0d auto

  hb2438 : Goal L.ax-CX21-K0-S0-CK20-S0-CK10=K0-CK20-CK10-CCK'-CCK'-CX21-CX10-CCX0-S0-S0-S2-S2-CS01-CS01-CS02-CS02-CS02-CS12-CS12
  hb2438 = ListNF.listnfeq' nf-p24k0d auto

  hb2439 : Goal L.ax-CX21-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ
  hb2439 = ListNF.listnfeq' nf-p24k0d auto

  hb2440 : Goal L.ax-CX21-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-CX21-CX10-CX20-S0-S0-S2-S2-CS01-CS01-CS02-CS02-CCZ
  hb2440 = ListNF.listnfeq' nf-p24k0d auto

  hb2441 : Goal L.ax-CX21-K0-S0-CK20-CK10=K0-S0-CK10-CX21-CS12-CS12-CS12
  hb2441 = ListNF.listnfeq' nf-p24k0d auto

  hb2442 : Goal L.ax-CX21-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ
  hb2442 = ListNF.listnfeq' nf-p24k0d auto

  hb2443 : Goal L.ax-CX21-K0-S0-CK20-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CX21-CX20-S2-CS02-CS02-CS02-CCZ
  hb2443 = ListNF.listnfeq' nf-p24k0d auto

  hb2444 : Goal L.ax-CX21-K0-S0-CK20-CCK'=K0-CCK'-CCK'-CX21-S0-S2-CS02-CS02-CS02-CS12-CS12
  hb2444 = ListNF.listnfeq' nf-p24k0d auto

  hb2445 : Goal L.ax-CX21-K0-S0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCK'-CX21-CX20-CCX0-S0-S2-S2-CS02-CS02-CS12
  hb2445 = ListNF.listnfeq' nf-p24k0d auto

  hb2446 : Goal L.ax-CX21-K0-CK10=K0-CK20-CK10-CX21-S2-CS12-CS12-CS12
  hb2446 = ListNF.listnfeq' nf-p24k0d auto

  hb2447 : Goal L.ax-CX21-K0-CK10-CCK'=K0-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ
  hb2447 = ListNF.listnfeq' nf-p24k0d auto

  hb2448 : Goal L.ax-CX21-K0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-CX21-CX10-S0-S0-S2-S2-CS01-CS01-CS02-CS02-CCZ
  hb2448 = ListNF.listnfeq' nf-p24k0d auto

  hb2449 : Goal L.ax-CX21-K0-CK20=K0-CK20-CX21
  hb2449 = ListNF.listnfeq' nf-p24k0d auto

  hb2450 : Goal L.ax-CX21-K0-CK20-S0-CK10=K0-S0-CK20-CK10-CCK'-CCK'-CX21-CX20-S2-S2-CS02-CS12-CS12-CCZ
  hb2450 = ListNF.listnfeq' nf-p24k0d auto

  hb2451 : Goal L.ax-CX21-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ
  hb2451 = ListNF.listnfeq' nf-p24k0d auto

  hb2452 : Goal L.ax-CX21-K0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-CX21-S2-CS02-CS02-CS12
  hb2452 = ListNF.listnfeq' nf-p24k0d auto

  hb2453 : Goal L.ax-CX21-K0-CK20-CK10=K0-CK10-CX21-CS12-CS12-CS12
  hb2453 = ListNF.listnfeq' nf-p24k0d auto

  hb2454 : Goal L.ax-CX21-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ
  hb2454 = ListNF.listnfeq' nf-p24k0d auto

  hb2455 : Goal L.ax-CX21-K0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CX21-CX10-CCX0-S0-S0-CS01-CS01-CS02-CS02-CS02-CS12-CS12
  hb2455 = ListNF.listnfeq' nf-p24k0d auto

  hb2456 : Goal L.ax-CX21-K0-CK20-CCK'=K0-CCK'-CX21-CS02-CS12-CS12-CS12-CCZ
  hb2456 = ListNF.listnfeq' nf-p24k0d auto

  hb2457 : Goal L.ax-CX21-K0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-CX21-CCX0-S0-S0-S0-S2-CS02-CS02-CS12-CS12-CCZ
  hb2457 = ListNF.listnfeq' nf-p24k0d auto

  hb2458 : Goal L.ax-CX21-K0-CCK'=K0-CK20-CCK'-CX21-S2-CS02-CS12-CS12-CS12-CCZ
  hb2458 = ListNF.listnfeq' nf-p24k0d auto

  hb2459 : Goal L.ax-CX21-K0-CCK'-CCK'=K0-S0-CK20-CCK'-CX21-S0-S0-S0-S2-CS02-CS12-CS12
  hb2459 = ListNF.listnfeq' nf-p24k0d auto

  hb2460 : Goal L.ax-CX21-CK10=CK20-CK10-CX21-S2-CS12-CS12-CS12
  hb2460 = ListNF.listnfeq' nf-p24k0d auto

  hb2461 : Goal L.ax-CX21-CK10-CCK'=CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ
  hb2461 = ListNF.listnfeq' nf-p24k0d auto

  hb2462 : Goal L.ax-CX21-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-CX21-CX10-S0-S0-S2-S2-CS01-CS01-CS02-CS02-CCZ
  hb2462 = ListNF.listnfeq' nf-p24k0d auto

  hb2463 : Goal L.ax-CX21-CK20-S0-CK10=S0-CK20-CK10-CCK'-CCK'-CX21-CX20-S2-S2-CS02-CS12-CS12-CCZ
  hb2463 = ListNF.listnfeq' nf-p24k0d auto

  hb2464 : Goal L.ax-CX21-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ
  hb2464 = ListNF.listnfeq' nf-p24k0d auto

  hb2465 : Goal L.ax-CX21-CK20-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-CX21-S2-CS02-CS02-CS12
  hb2465 = ListNF.listnfeq' nf-p24k0d auto

  hb2466 : Goal L.ax-CX21-CK20-CK10=CK10-CX21-CS12-CS12-CS12
  hb2466 = ListNF.listnfeq' nf-p24k0d auto

  hb2467 : Goal L.ax-CX21-CK20-CK10-CCK'=CK20-CK10-CCK'-CX21-S2-CS02-CS12-CS12-CCZ
  hb2467 = ListNF.listnfeq' nf-p24k0d auto

  hb2468 : Goal L.ax-CX21-CK20-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CX21-CX10-CCX0-S0-S0-CS01-CS01-CS02-CS02-CS02-CS12-CS12
  hb2468 = ListNF.listnfeq' nf-p24k0d auto

  hb2469 : Goal L.ax-CX21-CK20-CCK'=CCK'-CX21-CS02-CS12-CS12-CS12-CCZ
  hb2469 = ListNF.listnfeq' nf-p24k0d auto

  hb2470 : Goal L.ax-CX21-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-CX21-CCX0-S0-S0-S0-S2-CS02-CS02-CS12-CS12-CCZ
  hb2470 = ListNF.listnfeq' nf-p24k0d auto

  hb2471 : Goal L.ax-CX21-CCK'=CK20-CCK'-CX21-S2-CS02-CS12-CS12-CS12-CCZ
  hb2471 = ListNF.listnfeq' nf-p24k0d auto

  hb2472 : Goal L.ax-CX21-CCK'-CCK'=S0-CK20-CCK'-CX21-S0-S0-S0-S2-CS02-CS12-CS12
  hb2472 = ListNF.listnfeq' nf-p24k0d auto

  hb2473 : Goal L.ax-CCX0-S0-K0-S0-CK10=S0-K0-S0-CK10-CCZ
  hb2473 = ListNF.listnfeq' nf-e4 auto

  hb2474 : Goal L.ax-CCX0-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK10-CCK'-CCX0-CS12-CCZ
  hb2474 = ListNF.listnfeq' nf-e4 auto

  hb2475 : Goal L.ax-CCX0-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-CCX0
  hb2475 = ListNF.listnfeq' nf-e4 auto

  hb2476 : Goal L.ax-CCX0-S0-K0-S0-CK20=S0-K0-S0-CK20-CCZ
  hb2476 = ListNF.listnfeq' nf-e4 auto

  hb2477 : Goal L.ax-CCX0-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-CCX0
  hb2477 = ListNF.listnfeq' nf-e4 auto

  hb2478 : Goal L.ax-CCX0-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCZ
  hb2478 = ListNF.listnfeq' nf-e4 auto

  hb2479 : Goal L.ax-CCX0-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-CCX0-CS12-CCZ
  hb2479 = ListNF.listnfeq' nf-e4 auto

  hb2480 : Goal L.ax-CCX0-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-CCX0
  hb2480 = ListNF.listnfeq' nf-e4 auto

  hb2481 : Goal L.ax-CCX0-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCZ
  hb2481 = ListNF.listnfeq' nf-e4 auto

  hb2482 : Goal L.ax-CCX0-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-CCX0-CS12-CCZ
  hb2482 = ListNF.listnfeq' nf-e4 auto

  hb2483 : Goal L.ax-CCX0-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CCK'-CCX0-CS12-CCZ
  hb2483 = ListNF.listnfeq' nf-e4 auto

  hb2484 : Goal L.ax-CCX0-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-CCX0
  hb2484 = ListNF.listnfeq' nf-e4 auto

  hb2485 : Goal L.ax-CCX0-S0-K0-CK10=S0-K0-CK10-CCX0-CS12-CS12-CS12-CCZ
  hb2485 = ListNF.listnfeq' nf-e4 auto

  hb2486 : Goal L.ax-CCX0-S0-K0-CK10-CCK'=S0-K0-CK10-CCK'-CCX0-CS12-CS12
  hb2486 = ListNF.listnfeq' nf-e4 auto

  hb2487 : Goal L.ax-CCX0-S0-K0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-CS12-CS12-CCZ
  hb2487 = ListNF.listnfeq' nf-e4 auto

  hb2488 : Goal L.ax-CCX0-S0-K0-CK20=S0-K0-CK20-CCX0-CS12-CS12-CS12-CCZ
  hb2488 = ListNF.listnfeq' nf-e4 auto

  hb2489 : Goal L.ax-CCX0-S0-K0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-CS12-CS12-CCZ
  hb2489 = ListNF.listnfeq' nf-e4 auto

  hb2490 : Goal L.ax-CCX0-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCX0-CS12-CS12-CS12-CCZ
  hb2490 = ListNF.listnfeq' nf-e4 auto

  hb2491 : Goal L.ax-CCX0-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-CCX0-CS12-CS12
  hb2491 = ListNF.listnfeq' nf-e4 auto

  hb2492 : Goal L.ax-CCX0-S0-K0-CK20-CK10=S0-K0-CK20-CK10-CCX0-CS12-CCZ
  hb2492 = ListNF.listnfeq' nf-e4 auto

  hb2493 : Goal L.ax-CCX0-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CCX0
  hb2493 = ListNF.listnfeq' nf-e4 auto

  hb2494 : Goal L.ax-CCX0-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-CCZ
  hb2494 = ListNF.listnfeq' nf-e4 auto

  hb2495 : Goal L.ax-CCX0-S0-K0-CK20-CCK'=S0-K0-CK20-CCK'-CCX0-CS12-CS12
  hb2495 = ListNF.listnfeq' nf-e4 auto

  hb2496 : Goal L.ax-CCX0-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-CS12-CS12-CCZ
  hb2496 = ListNF.listnfeq' nf-e4 auto

  hb2497 : Goal L.ax-CCX0-S0-K0-CCK'=S0-K0-CCK'-CCX0
  hb2497 = ListNF.listnfeq' nf-e4 auto

  hb2498 : Goal L.ax-CCX0-S0-K0-CCK'-CCK'=S0-K0-CCK'-CCK'-CCZ
  hb2498 = ListNF.listnfeq' nf-e4 auto

  hb2499 : Goal L.ax-CCX0-S0-CK10-CCK'=S0-CK10-CCK'-CCX0
  hb2499 = ListNF.listnfeq' nf-e3 auto

  hb2500 : Goal L.ax-CCX0-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-CCZ
  hb2500 = ListNF.listnfeq' nf-e3 auto

  hb2501 : Goal L.ax-CCX0-S0-CK20-S0-CK10=S0-CK20-S0-CK10-CCZ
  hb2501 = ListNF.listnfeq' nf-e3 auto

  hb2502 : Goal L.ax-CCX0-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-CCX0-CS12-CCZ
  hb2502 = ListNF.listnfeq' nf-e3 auto

  hb2503 : Goal L.ax-CCX0-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-CCX0
  hb2503 = ListNF.listnfeq' nf-e3 auto

  hb2504 : Goal L.ax-CCX0-S0-CK20-CK10=S0-CK20-CK10-CCX0-CS12-CS12-CS12-CCZ
  hb2504 = ListNF.listnfeq' nf-e3 auto

  hb2505 : Goal L.ax-CCX0-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-CCX0-CS12-CS12
  hb2505 = ListNF.listnfeq' nf-e3 auto

  hb2506 : Goal L.ax-CCX0-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-CS12-CS12-CCZ
  hb2506 = ListNF.listnfeq' nf-e3 auto

  hb2507 : Goal L.ax-CCX0-S0-CK20-CCK'=S0-CK20-CCK'-CCX0
  hb2507 = ListNF.listnfeq' nf-e3 auto

  hb2508 : Goal L.ax-CCX0-S0-CK20-CCK'-CCK'=S0-CK20-CCK'-CCK'-CCZ
  hb2508 = ListNF.listnfeq' nf-e3 auto

  hb2509 : Goal L.ax-CCX0-K0-S0-CK10=K0-S0-CK10-CCX0
  hb2509 = ListNF.listnfeq' nf-e4 auto

  hb2510 : Goal L.ax-CCX0-K0-S0-CK10-CCK'=K0-S0-CK10-CCK'-CCZ
  hb2510 = ListNF.listnfeq' nf-e4 auto

  hb2511 : Goal L.ax-CCX0-K0-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-CCX0-CS12-CCZ
  hb2511 = ListNF.listnfeq' nf-e4 auto

  hb2512 : Goal L.ax-CCX0-K0-S0-CK20=K0-S0-CK20-CCX0
  hb2512 = ListNF.listnfeq' nf-e4 auto

  hb2513 : Goal L.ax-CCX0-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-CCX0-CS12-CCZ
  hb2513 = ListNF.listnfeq' nf-e4 auto

  hb2514 : Goal L.ax-CCX0-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCX0
  hb2514 = ListNF.listnfeq' nf-e4 auto

  hb2515 : Goal L.ax-CCX0-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-CCZ
  hb2515 = ListNF.listnfeq' nf-e4 auto

  hb2516 : Goal L.ax-CCX0-K0-S0-CK20-CK10=K0-S0-CK20-CK10-CCZ
  hb2516 = ListNF.listnfeq' nf-e4 auto

  hb2517 : Goal L.ax-CCX0-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CCX0-CS12-CCZ
  hb2517 = ListNF.listnfeq' nf-e4 auto

  hb2518 : Goal L.ax-CCX0-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-CCX0
  hb2518 = ListNF.listnfeq' nf-e4 auto

  hb2519 : Goal L.ax-CCX0-K0-S0-CK20-CCK'=K0-S0-CK20-CCK'-CCZ
  hb2519 = ListNF.listnfeq' nf-e4 auto

  hb2520 : Goal L.ax-CCX0-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-CCX0-CS12-CCZ
  hb2520 = ListNF.listnfeq' nf-e4 auto

  hb2521 : Goal L.ax-CCX0-K0-CK10=K0-CK10-CCX0
  hb2521 = ListNF.listnfeq' nf-e4 auto

  hb2522 : Goal L.ax-CCX0-K0-CK10-CCK'=K0-CK10-CCK'-CCZ
  hb2522 = ListNF.listnfeq' nf-e4 auto

  hb2523 : Goal L.ax-CCX0-K0-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-CCX0-CS12-CCZ
  hb2523 = ListNF.listnfeq' nf-e4 auto

  hb2524 : Goal L.ax-CCX0-K0-CK20=K0-CK20-CCX0
  hb2524 = ListNF.listnfeq' nf-e4 auto

  hb2525 : Goal L.ax-CCX0-K0-CK20-S0-CK10=K0-CK20-S0-CK10-CCX0-CS12-CCZ
  hb2525 = ListNF.listnfeq' nf-e4 auto

  hb2526 : Goal L.ax-CCX0-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-CCX0
  hb2526 = ListNF.listnfeq' nf-e4 auto

  hb2527 : Goal L.ax-CCX0-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-CCZ
  hb2527 = ListNF.listnfeq' nf-e4 auto

  hb2528 : Goal L.ax-CCX0-K0-CK20-CK10=K0-CK20-CK10-CCZ
  hb2528 = ListNF.listnfeq' nf-e4 auto

  hb2529 : Goal L.ax-CCX0-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-CCX0-CS12-CCZ
  hb2529 = ListNF.listnfeq' nf-e4 auto

  hb2530 : Goal L.ax-CCX0-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-CCX0
  hb2530 = ListNF.listnfeq' nf-e4 auto

  hb2531 : Goal L.ax-CCX0-K0-CK20-CCK'=K0-CK20-CCK'-CCZ
  hb2531 = ListNF.listnfeq' nf-e4 auto

  hb2532 : Goal L.ax-CCX0-K0-CK20-CCK'-CCK'=K0-CK20-CCK'-CCK'-CCX0-CS12-CCZ
  hb2532 = ListNF.listnfeq' nf-e4 auto

  hb2533 : Goal L.ax-CCX0-K0-CCK'=K0-CCK'-CCX0-CS12-CCZ
  hb2533 = ListNF.listnfeq' nf-e4 auto

  hb2534 : Goal L.ax-CCX0-K0-CCK'-CCK'=K0-CCK'-CCK'-CCX0
  hb2534 = ListNF.listnfeq' nf-e4 auto

  hb2535 : Goal L.ax-CCX0-CK10-CCK'=CK10-CCK'-CCX0-CS12-CCZ
  hb2535 = ListNF.listnfeq' nf-e3 auto

  hb2536 : Goal L.ax-CCX0-CK10-CCK'-CCK'=CK10-CCK'-CCK'-CCX0
  hb2536 = ListNF.listnfeq' nf-e3 auto

  hb2537 : Goal L.ax-CCX0-CK20-S0-CK10=CK20-S0-CK10-CCX0
  hb2537 = ListNF.listnfeq' nf-e3 auto

  hb2538 : Goal L.ax-CCX0-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-CCZ
  hb2538 = ListNF.listnfeq' nf-e3 auto

  hb2539 : Goal L.ax-CCX0-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-CCX0-CS12-CCZ
  hb2539 = ListNF.listnfeq' nf-e3 auto

  hb2540 : Goal L.ax-CCX0-CK20-CK10=CK20-CK10-CCX0
  hb2540 = ListNF.listnfeq' nf-e3 auto

  hb2541 : Goal L.ax-CCX0-CK20-CK10-CCK'=CK20-CK10-CCK'-CCZ
  hb2541 = ListNF.listnfeq' nf-e3 auto

  hb2542 : Goal L.ax-CCX0-CK20-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-CCX0-CS12-CCZ
  hb2542 = ListNF.listnfeq' nf-e3 auto

  hb2543 : Goal L.ax-CCX0-CK20-CCK'=CK20-CCK'-CCX0-CS12-CCZ
  hb2543 = ListNF.listnfeq' nf-e3 auto

  hb2544 : Goal L.ax-CCX0-CK20-CCK'-CCK'=CK20-CCK'-CCK'-CCX0
  hb2544 = ListNF.listnfeq' nf-e3 auto

  hb2545 : Goal L.ax-Swap12-S0-K0=S0-K0-Swap12
  hb2545 = mvD3.general-rewrite 50 auto

  hb2546 : Goal L.ax-Swap12-S0-K0-S0-CK10=S0-K0-S0-CK20-Swap12
  hb2546 = mvD3.general-rewrite 50 auto

  hb2547 : Goal L.ax-Swap12-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK20-CCK'-Swap12
  hb2547 = mvD3.general-rewrite 50 auto

  hb2548 : Goal L.ax-Swap12-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-Swap12
  hb2548 = mvD3.general-rewrite 50 auto

  hb2549 : Goal L.ax-Swap12-S0-K0-S0-CK20=S0-K0-S0-CK10-Swap12
  hb2549 = mvD3.general-rewrite 50 auto

  hb2550 : Goal L.ax-Swap12-S0-K0-S0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-CCK'-Swap12-CX10-CCX0-S0-S1-S1-S1-CS12-CS12-CCZ
  hb2550 = ListNF.listnfeq' nf-p24k0d auto

  hb2551 : Goal L.ax-Swap12-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-Swap12-CX10-S0-S1-S1-S1-CS12-CCZ
  hb2551 = ListNF.listnfeq' nf-p24k0d auto

  hb2552 : Goal L.ax-Swap12-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CCK'-Swap12-CX10-CCX0-S0-S1-S1-S1-CS12
  hb2552 = ListNF.listnfeq' nf-p24k0d auto

  hb2553 : Goal L.ax-Swap12-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-Swap12
  hb2553 = mvD3.general-rewrite 50 auto

  hb2554 : Goal L.ax-Swap12-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-Swap12
  hb2554 = mvD3.general-rewrite 50 auto

  hb2555 : Goal L.ax-Swap12-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-Swap12
  hb2555 = mvD3.general-rewrite 50 auto

  hb2556 : Goal L.ax-Swap12-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK10-CCK'-Swap12
  hb2556 = mvD3.general-rewrite 50 auto

  hb2557 : Goal L.ax-Swap12-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-Swap12
  hb2557 = mvD3.general-rewrite 50 auto

  hb2558 : Goal L.ax-Swap12-S0-K0-CK10=S0-K0-CK20-Swap12
  hb2558 = mvD3.general-rewrite 50 auto

  hb2559 : Goal L.ax-Swap12-S0-K0-CK10-CCK'=S0-K0-CK20-CCK'-Swap12
  hb2559 = mvD3.general-rewrite 50 auto

  hb2560 : Goal L.ax-Swap12-S0-K0-CK10-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-Swap12
  hb2560 = mvD3.general-rewrite 50 auto

  hb2561 : Goal L.ax-Swap12-S0-K0-CK20=S0-K0-CK10-Swap12
  hb2561 = mvD3.general-rewrite 50 auto

  hb2562 : Goal L.ax-Swap12-S0-K0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-CCK'-Swap12-CX20-S0-S0-S0-CS02-CS02-CS12-CCZ
  hb2562 = ListNF.listnfeq' nf-p24k0d auto

  hb2563 : Goal L.ax-Swap12-S0-K0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-Swap12-CX20-CCX0-S0-S0-S0-CS02-CS02-CS12-CS12-CS12
  hb2563 = ListNF.listnfeq' nf-p24k0d auto

  hb2564 : Goal L.ax-Swap12-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-Swap12-CX20-CCX0-S0-S0-S0-CS02-CS02-CCZ
  hb2564 = ListNF.listnfeq' nf-p24k0d auto

  hb2565 : Goal L.ax-Swap12-S0-K0-CK20-CK10=S0-K0-CK20-CK10-Swap12
  hb2565 = mvD3.general-rewrite 50 auto

  hb2566 : Goal L.ax-Swap12-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-Swap12
  hb2566 = mvD3.general-rewrite 50 auto

  hb2567 : Goal L.ax-Swap12-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-Swap12
  hb2567 = mvD3.general-rewrite 50 auto

  hb2568 : Goal L.ax-Swap12-S0-K0-CK20-CCK'=S0-K0-CK10-CCK'-Swap12
  hb2568 = mvD3.general-rewrite 50 auto

  hb2569 : Goal L.ax-Swap12-S0-K0-CK20-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-Swap12
  hb2569 = mvD3.general-rewrite 50 auto

  hb2570 : Goal L.ax-Swap12-S0-K0-CCK'=S0-K0-CCK'-Swap12
  hb2570 = mvD3.general-rewrite 50 auto

  hb2571 : Goal L.ax-Swap12-S0-K0-CCK'-CCK'=S0-K0-CCK'-CCK'-Swap12
  hb2571 = mvD3.general-rewrite 50 auto

  hb2572 : Goal L.ax-Swap12-S0-CK10=S0-CK20-Swap12
  hb2572 = mvD3.general-rewrite 50 auto

  hb2573 : Goal L.ax-Swap12-S0-CK10-CCK'=S0-CK20-CCK'-Swap12
  hb2573 = mvD3.general-rewrite 50 auto

  hb2574 : Goal L.ax-Swap12-S0-CK10-CCK'-CCK'=S0-CK20-CCK'-CCK'-Swap12
  hb2574 = mvD3.general-rewrite 50 auto

  hb2575 : Goal L.ax-Swap12-S0-CK20=S0-CK10-Swap12
  hb2575 = mvD3.general-rewrite 50 auto

  hb2576 : Goal L.ax-Swap12-S0-CK20-S0-CK10=CK20-S0-CK10-CCK'-Swap12-CX10-CCX0-S0-S1-S1-S1-CS12-CS12-CCZ
  hb2576 = ListNF.listnfeq' nf-p24k0d auto

  hb2577 : Goal L.ax-Swap12-S0-CK20-S0-CK10-CCK'=CK20-S0-CK10-Swap12-CX10-S0-S1-S1-S1-CS12-CCZ
  hb2577 = ListNF.listnfeq' nf-p24k0d auto

  hb2578 : Goal L.ax-Swap12-S0-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CCK'-Swap12-CX10-CCX0-S0-S1-S1-S1-CS12
  hb2578 = ListNF.listnfeq' nf-p24k0d auto

  hb2579 : Goal L.ax-Swap12-S0-CK20-CK10=S0-CK20-CK10-Swap12
  hb2579 = mvD3.general-rewrite 50 auto

  hb2580 : Goal L.ax-Swap12-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-Swap12
  hb2580 = mvD3.general-rewrite 50 auto

  hb2581 : Goal L.ax-Swap12-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCK'-Swap12
  hb2581 = mvD3.general-rewrite 50 auto

  hb2582 : Goal L.ax-Swap12-S0-CK20-CCK'=S0-CK10-CCK'-Swap12
  hb2582 = mvD3.general-rewrite 50 auto

  hb2583 : Goal L.ax-Swap12-S0-CK20-CCK'-CCK'=S0-CK10-CCK'-CCK'-Swap12
  hb2583 = mvD3.general-rewrite 50 auto

  hb2584 : Goal L.ax-Swap12-K0-S0-CK10=K0-S0-CK20-Swap12
  hb2584 = mvD3.general-rewrite 50 auto

  hb2585 : Goal L.ax-Swap12-K0-S0-CK10-CCK'=K0-S0-CK20-CCK'-Swap12
  hb2585 = mvD3.general-rewrite 50 auto

  hb2586 : Goal L.ax-Swap12-K0-S0-CK10-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-Swap12
  hb2586 = mvD3.general-rewrite 50 auto

  hb2587 : Goal L.ax-Swap12-K0-S0-CK20=K0-S0-CK10-Swap12
  hb2587 = mvD3.general-rewrite 50 auto

  hb2588 : Goal L.ax-Swap12-K0-S0-CK20-S0-CK10=K0-CK20-S0-CK10-CCK'-Swap12-CX10-CCX0-S0-S1-S1-S1-CS12-CS12-CCZ
  hb2588 = ListNF.listnfeq' nf-p24k0d auto

  hb2589 : Goal L.ax-Swap12-K0-S0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-Swap12-CX10-S0-S1-S1-S1-CS12-CCZ
  hb2589 = ListNF.listnfeq' nf-p24k0d auto

  hb2590 : Goal L.ax-Swap12-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-Swap12-CX10-CCX0-S0-S1-S1-S1-CS12
  hb2590 = ListNF.listnfeq' nf-p24k0d auto

  hb2591 : Goal L.ax-Swap12-K0-S0-CK20-CK10=K0-S0-CK20-CK10-Swap12
  hb2591 = mvD3.general-rewrite 50 auto

  hb2592 : Goal L.ax-Swap12-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-Swap12
  hb2592 = mvD3.general-rewrite 50 auto

  hb2593 : Goal L.ax-Swap12-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-Swap12
  hb2593 = mvD3.general-rewrite 50 auto

  hb2594 : Goal L.ax-Swap12-K0-S0-CK20-CCK'=K0-S0-CK10-CCK'-Swap12
  hb2594 = mvD3.general-rewrite 50 auto

  hb2595 : Goal L.ax-Swap12-K0-S0-CK20-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-Swap12
  hb2595 = mvD3.general-rewrite 50 auto

  hb2596 : Goal L.ax-Swap12-K0-CK10=K0-CK20-Swap12
  hb2596 = mvD3.general-rewrite 50 auto

  hb2597 : Goal L.ax-Swap12-K0-CK10-CCK'=K0-CK20-CCK'-Swap12
  hb2597 = mvD3.general-rewrite 50 auto

  hb2598 : Goal L.ax-Swap12-K0-CK10-CCK'-CCK'=K0-CK20-CCK'-CCK'-Swap12
  hb2598 = mvD3.general-rewrite 50 auto

  hb2599 : Goal L.ax-Swap12-K0-CK20=K0-CK10-Swap12
  hb2599 = mvD3.general-rewrite 50 auto

  hb2600 : Goal L.ax-Swap12-K0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-CCK'-Swap12-CX20-S0-S0-S0-CS02-CS02-CS12-CCZ
  hb2600 = ListNF.listnfeq' nf-p24k0d auto

  hb2601 : Goal L.ax-Swap12-K0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-Swap12-CX20-CCX0-S0-S0-S0-CS02-CS02-CS12-CS12-CS12
  hb2601 = ListNF.listnfeq' nf-p24k0d auto

  hb2602 : Goal L.ax-Swap12-K0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-Swap12-CX20-CCX0-S0-S0-S0-CS02-CS02-CCZ
  hb2602 = ListNF.listnfeq' nf-p24k0d auto

  hb2603 : Goal L.ax-Swap12-K0-CK20-CK10=K0-CK20-CK10-Swap12
  hb2603 = mvD3.general-rewrite 50 auto

  hb2604 : Goal L.ax-Swap12-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-Swap12
  hb2604 = mvD3.general-rewrite 50 auto

  hb2605 : Goal L.ax-Swap12-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'-Swap12
  hb2605 = mvD3.general-rewrite 50 auto

  hb2606 : Goal L.ax-Swap12-K0-CK20-CCK'=K0-CK10-CCK'-Swap12
  hb2606 = mvD3.general-rewrite 50 auto

  hb2607 : Goal L.ax-Swap12-K0-CK20-CCK'-CCK'=K0-CK10-CCK'-CCK'-Swap12
  hb2607 = mvD3.general-rewrite 50 auto

  hb2608 : Goal L.ax-Swap12-K0-CCK'=K0-CCK'-Swap12
  hb2608 = mvD3.general-rewrite 50 auto

  hb2609 : Goal L.ax-Swap12-K0-CCK'-CCK'=K0-CCK'-CCK'-Swap12
  hb2609 = mvD3.general-rewrite 50 auto

  hb2610 : Goal L.ax-Swap12-CK10-CCK'=CK20-CCK'-Swap12
  hb2610 = mvD3.general-rewrite 50 auto

  hb2611 : Goal L.ax-Swap12-CK10-CCK'-CCK'=CK20-CCK'-CCK'-Swap12
  hb2611 = mvD3.general-rewrite 50 auto

  hb2612 : Goal L.ax-Swap12-CK20-S0-CK10=S0-CK20-S0-CK10-CCK'-Swap12-CX20-S0-S0-S0-CS02-CS02-CS12-CCZ
  hb2612 = ListNF.listnfeq' nf-p24k0d auto

  hb2613 : Goal L.ax-Swap12-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-Swap12-CX20-CCX0-S0-S0-S0-CS02-CS02-CS12-CS12-CS12
  hb2613 = ListNF.listnfeq' nf-p24k0d auto

  hb2614 : Goal L.ax-Swap12-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-Swap12-CX20-CCX0-S0-S0-S0-CS02-CS02-CCZ
  hb2614 = ListNF.listnfeq' nf-p24k0d auto

  hb2615 : Goal L.ax-Swap12-CK20-CK10=CK20-CK10-Swap12
  hb2615 = mvD3.general-rewrite 50 auto

  hb2616 : Goal L.ax-Swap12-CK20-CK10-CCK'=CK20-CK10-CCK'-Swap12
  hb2616 = mvD3.general-rewrite 50 auto

  hb2617 : Goal L.ax-Swap12-CK20-CK10-CCK'-CCK'=CK20-CK10-CCK'-CCK'-Swap12
  hb2617 = mvD3.general-rewrite 50 auto

  hb2618 : Goal L.ax-Swap12-CK20-CCK'=CK10-CCK'-Swap12
  hb2618 = mvD3.general-rewrite 50 auto

  hb2619 : Goal L.ax-Swap12-CK20-CCK'-CCK'=CK10-CCK'-CCK'-Swap12
  hb2619 = mvD3.general-rewrite 50 auto

  hb2620 : Goal L.ax-Swap12-CCK'-CCK'=CCK'-CCK'-Swap12
  hb2620 = mvD3.general-rewrite 50 auto

  hb2621 : Goal L.ax-CK10-S0-K0-S0-CK10=S0-K0-CK10-S0-CS01
  hb2621 = ListNF.listnfeq' nf-e4 auto

  hb2622 : Goal L.ax-CK10-S0-K0-S0-CK10-CCK'=S0-K0-CK10-CCK'-CCX0-S0-CS01-CS12
  hb2622 = ListNF.listnfeq' nf-e4 auto

  hb2623 : Goal L.ax-CK10-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCK'-CCX0-S0-CS01-CCZ
  hb2623 = ListNF.listnfeq' nf-e4 auto

  hb2624 : Goal L.ax-CK10-S0-K0-S0-CK20=S0-K0-S0-CK20-CCK'-CCK'-CX10-CCX0-S1-S1-S1-CS01-CS12-CS12-CCZ
  hb2624 = ListNF.listnfeq' nf-e4 auto

  hb2625 : Goal L.ax-CK10-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-CK10-CCK'-CX10-CCX0-S0-S1-CS01-CS12-CS12-CS12
  hb2625 = ListNF.listnfeq' nf-e4 auto

  hb2626 : Goal L.ax-CK10-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCK'-CX10-S0-S1-CS01
  hb2626 = ListNF.listnfeq' nf-e4 auto

  hb2627 : Goal L.ax-CK10-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CX10-S0-S1-CS01-CS12-CCZ
  hb2627 = ListNF.listnfeq' nf-e4 auto

  hb2628 : Goal L.ax-CK10-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-CX10-S0-S0-S0-CS01-CS01-CS01-CS12-CCZ
  hb2628 = ListNF.listnfeq' nf-e4 auto

  hb2629 : Goal L.ax-CK10-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CX10-CCX0-S0-S0-S0-CS01-CS01-CS01-CS12-CS12-CS12
  hb2629 = ListNF.listnfeq' nf-e4 auto

  hb2630 : Goal L.ax-CK10-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CX10-S0-S0-S0-CS01-CS01-CS01
  hb2630 = ListNF.listnfeq' nf-e4 auto

  hb2631 : Goal L.ax-CK10-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CCK'-CX10-S1-S1-S1-CS01-CS12-CCZ
  hb2631 = ListNF.listnfeq' nf-e4 auto

  hb2632 : Goal L.ax-CK10-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CX10-CCX0-S1-S1-S1-CS01-CS12-CS12-CS12
  hb2632 = ListNF.listnfeq' nf-e4 auto

  hb2633 : Goal L.ax-CK10-S0-K0-CK10=S0-K0-S0-CK10-S0-S0-S0-S1-S1-S1-CS01-CS01-CS01
  hb2633 = ListNF.listnfeq' nf-e4 auto

  hb2634 : Goal L.ax-CK10-S0-K0-CK10-CCK'=S0-K0-S0-CK10-CCK'-CCX0-S0-S0-S0-S1-S1-S1-CS01-CS01-CS01-CS12
  hb2634 = ListNF.listnfeq' nf-e4 auto

  hb2635 : Goal L.ax-CK10-S0-K0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CCK'-CCK'-CCX0-S0-S0-S0-S1-S1-S1-CS01-CS01-CS01-CCZ
  hb2635 = ListNF.listnfeq' nf-e4 auto

  hb2636 : Goal L.ax-CK10-S0-K0-CK20=S0-K0-CK20-CCK'-CCK'-CX10-CS01-CS01-CS01-CS12-CCZ
  hb2636 = ListNF.listnfeq' nf-e4 auto

  hb2637 : Goal L.ax-CK10-S0-K0-CK20-S0-CK10=S0-K0-CK20-CK10-CCK'-CCX0-S0-CS01-CCZ
  hb2637 = ListNF.listnfeq' nf-e4 auto

  hb2638 : Goal L.ax-CK10-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CCK'-S0-CS01
  hb2638 = ListNF.listnfeq' nf-e4 auto

  hb2639 : Goal L.ax-CK10-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CCX0-S0-CS01-CS12-CS12-CS12
  hb2639 = ListNF.listnfeq' nf-e4 auto

  hb2640 : Goal L.ax-CK10-S0-K0-CK20-CK10=S0-K0-CK20-S0-CK10-CCK'-CCK'-CCX0-S0-S0-S0-S1-S1-S1-CS01-CS01-CS01-CS12-CS12-CS12
  hb2640 = ListNF.listnfeq' nf-e4 auto

  hb2641 : Goal L.ax-CK10-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-S0-CK10-CCX0-S0-S0-S0-S1-S1-S1-CS01-CS01-CS01-CCZ
  hb2641 = ListNF.listnfeq' nf-e4 auto

  hb2642 : Goal L.ax-CK10-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-S0-S0-S0-S1-S1-S1-CS01-CS01-CS01
  hb2642 = ListNF.listnfeq' nf-e4 auto

  hb2643 : Goal L.ax-CK10-S0-K0-CK20-CCK'=S0-K0-CK20-CCK'-CX10-CS01-CS01-CS01-CS12-CCZ
  hb2643 = ListNF.listnfeq' nf-e4 auto

  hb2644 : Goal L.ax-CK10-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-CX10-CS01-CS01-CS01-CS12-CCZ
  hb2644 = ListNF.listnfeq' nf-e4 auto

  hb2645 : Goal L.ax-CK10-S0-K0-CCK'=S0-K0-CCK'-CCK'-CX10-CCX0-CS01-CS01-CS01-CCZ
  hb2645 = ListNF.listnfeq' nf-e4 auto

  hb2646 : Goal L.ax-CK10-S0-K0-CCK'-CCK'=S0-K0-CCK'-CX10-CCX0-CS01-CS01-CS01-CS12-CS12-CS12
  hb2646 = ListNF.listnfeq' nf-e4 auto

  hb2647 : Goal L.ax-CK10-S0-CK10-CCK'=S0-CK10-CCK'-CCK'-CX10-CCX0-CS01-CS01-CS01-CCZ
  hb2647 = ListNF.listnfeq' nf-e3 auto

  hb2648 : Goal L.ax-CK10-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CX10-CCX0-CS01-CS01-CS01-CS12-CS12-CS12
  hb2648 = ListNF.listnfeq' nf-e3 auto

  hb2649 : Goal L.ax-CK10-S0-CK20-S0-CK10=S0-CK20-CCK'-CX10-CCX0-S0-S1-S1-CS12-CS12-CCZ
  hb2649 = ListNF.listnfeq' nf-e3 auto

  hb2650 : Goal L.ax-CK10-S0-CK20-S0-CK10-CCK'=S0-CK20-CX10-S0-S1-S1-CS12-CCZ
  hb2650 = ListNF.listnfeq' nf-e3 auto

  hb2651 : Goal L.ax-CK10-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-CCK'-CCK'-CX10-CCX0-S0-S1-S1-CS12
  hb2651 = ListNF.listnfeq' nf-e3 auto

  hb2652 : Goal L.ax-CK10-S0-CK20-CK10=S0-CK20-CK10-CCK'-CCK'-CX10-CS01-CS01-CS01-CS12-CCZ
  hb2652 = ListNF.listnfeq' nf-e3 auto

  hb2653 : Goal L.ax-CK10-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-CX10-CS01-CS01-CS01-CS12-CCZ
  hb2653 = ListNF.listnfeq' nf-e3 auto

  hb2654 : Goal L.ax-CK10-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CX10-CS01-CS01-CS01-CS12-CCZ
  hb2654 = ListNF.listnfeq' nf-e3 auto

  hb2655 : Goal L.ax-CK10-S0-CK20-CCK'=S0-CK20-S0-CK10-CX10-CCX0-S0-S0-S0-CS01-CS01-CS12-CS12-CS12
  hb2655 = ListNF.listnfeq' nf-e3 auto

  hb2656 : Goal L.ax-CK10-S0-CK20-CCK'-CCK'=S0-CK20-S0-CK10-CCK'-CCK'-CX10-CCX0-S0-S0-S0-CS01-CS01-CCZ
  hb2656 = ListNF.listnfeq' nf-e3 auto

  hb2657 : Goal L.ax-CK10-K0-S0-CK10=K0-S0-CK10-CX10-CS01-CS01-CS01
  hb2657 = ListNF.listnfeq' nf-e4 auto

  hb2658 : Goal L.ax-CK10-K0-S0-CK10-CCK'=K0-S0-CK10-CCK'-CCK'-CX10-CCX0-CS01-CS01-CS01-CCZ
  hb2658 = ListNF.listnfeq' nf-e4 auto

  hb2659 : Goal L.ax-CK10-K0-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CX10-CCX0-CS01-CS01-CS01-CS12-CS12-CS12
  hb2659 = ListNF.listnfeq' nf-e4 auto

  hb2660 : Goal L.ax-CK10-K0-S0-CK20=K0-S0-CK20-S0-CK10-CCK'-CX10-S0-S0-S0-CS01-CS01-CS12-CCZ
  hb2660 = ListNF.listnfeq' nf-e4 auto

  hb2661 : Goal L.ax-CK10-K0-S0-CK20-S0-CK10=K0-S0-CK20-CCK'-CX10-CCX0-S0-S1-S1-CS12-CS12-CCZ
  hb2661 = ListNF.listnfeq' nf-e4 auto

  hb2662 : Goal L.ax-CK10-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-CX10-S0-S1-S1-CS12-CCZ
  hb2662 = ListNF.listnfeq' nf-e4 auto

  hb2663 : Goal L.ax-CK10-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-CCK'-CCK'-CX10-CCX0-S0-S1-S1-CS12
  hb2663 = ListNF.listnfeq' nf-e4 auto

  hb2664 : Goal L.ax-CK10-K0-S0-CK20-CK10=K0-S0-CK20-CK10-CCK'-CCK'-CX10-CS01-CS01-CS01-CS12-CCZ
  hb2664 = ListNF.listnfeq' nf-e4 auto

  hb2665 : Goal L.ax-CK10-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CX10-CS01-CS01-CS01-CS12-CCZ
  hb2665 = ListNF.listnfeq' nf-e4 auto

  hb2666 : Goal L.ax-CK10-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CX10-CS01-CS01-CS01-CS12-CCZ
  hb2666 = ListNF.listnfeq' nf-e4 auto

  hb2667 : Goal L.ax-CK10-K0-S0-CK20-CCK'=K0-S0-CK20-S0-CK10-CX10-CCX0-S0-S0-S0-CS01-CS01-CS12-CS12-CS12
  hb2667 = ListNF.listnfeq' nf-e4 auto

  hb2668 : Goal L.ax-CK10-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCK'-CX10-CCX0-S0-S0-S0-CS01-CS01-CCZ
  hb2668 = ListNF.listnfeq' nf-e4 auto

  hb2669 : Goal L.ax-CK10-K0-CK10=K0-S1-S1-S1
  hb2669 = ListNF.listnfeq' nf-e4 auto

  hb2670 : Goal L.ax-CK10-K0-CK10-CCK'=K0-CCK'-S1-S1-S1
  hb2670 = ListNF.listnfeq' nf-e4 auto

  hb2671 : Goal L.ax-CK10-K0-CK10-CCK'-CCK'=K0-CCK'-CCK'-S1-S1-S1
  hb2671 = ListNF.listnfeq' nf-e4 auto

  hb2672 : Goal L.ax-CK10-K0-CK20=K0-CK20-CK10
  hb2672 = ListNF.listnfeq' nf-e4 auto

  hb2673 : Goal L.ax-CK10-K0-CK20-S0-CK10=K0-CK20-S0-CK10-CX10-CS01-CS01-CS01
  hb2673 = ListNF.listnfeq' nf-e4 auto

  hb2674 : Goal L.ax-CK10-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-CCK'-CX10-CCX0-CS01-CS01-CS01-CCZ
  hb2674 = ListNF.listnfeq' nf-e4 auto

  hb2675 : Goal L.ax-CK10-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CX10-CCX0-CS01-CS01-CS01-CS12-CS12-CS12
  hb2675 = ListNF.listnfeq' nf-e4 auto

  hb2676 : Goal L.ax-CK10-K0-CK20-CK10=K0-CK20-S1-S1-S1
  hb2676 = ListNF.listnfeq' nf-e4 auto

  hb2677 : Goal L.ax-CK10-K0-CK20-CK10-CCK'=K0-CK20-CCK'-S1-S1-S1
  hb2677 = ListNF.listnfeq' nf-e4 auto

  hb2678 : Goal L.ax-CK10-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CCK'-CCK'-S1-S1-S1
  hb2678 = ListNF.listnfeq' nf-e4 auto

  hb2679 : Goal L.ax-CK10-K0-CK20-CCK'=K0-CK20-CK10-CCK'
  hb2679 = ListNF.listnfeq' nf-e4 auto

  hb2680 : Goal L.ax-CK10-K0-CK20-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'
  hb2680 = ListNF.listnfeq' nf-e4 auto

  hb2681 : Goal L.ax-CK10-K0-CCK'=K0-CK10-CCK'
  hb2681 = ListNF.listnfeq' nf-e4 auto

  hb2682 : Goal L.ax-CK10-K0-CCK'-CCK'=K0-CK10-CCK'-CCK'
  hb2682 = ListNF.listnfeq' nf-e4 auto

  hb2683 : Goal L.ax-CK10-CK10-CCK'=CCK'-S1-S1-S1
  hb2683 = ListNF.listnfeq' nf-e3 auto

  hb2684 : Goal L.ax-CK10-CK10-CCK'-CCK'=CCK'-CCK'-S1-S1-S1
  hb2684 = ListNF.listnfeq' nf-e3 auto

  hb2685 : Goal L.ax-CK10-CK20-S0-CK10=CK20-S0-CK10-CX10-CS01-CS01-CS01
  hb2685 = ListNF.listnfeq' nf-e3 auto

  hb2686 : Goal L.ax-CK10-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCK'-CCK'-CX10-CCX0-CS01-CS01-CS01-CCZ
  hb2686 = ListNF.listnfeq' nf-e3 auto

  hb2687 : Goal L.ax-CK10-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CX10-CCX0-CS01-CS01-CS01-CS12-CS12-CS12
  hb2687 = ListNF.listnfeq' nf-e3 auto

  hb2688 : Goal L.ax-CK10-CK20-CK10=CK20-S1-S1-S1
  hb2688 = ListNF.listnfeq' nf-e3 auto

  hb2689 : Goal L.ax-CK10-CK20-CK10-CCK'=CK20-CCK'-S1-S1-S1
  hb2689 = ListNF.listnfeq' nf-e3 auto

  hb2690 : Goal L.ax-CK10-CK20-CK10-CCK'-CCK'=CK20-CCK'-CCK'-S1-S1-S1
  hb2690 = ListNF.listnfeq' nf-e3 auto

  hb2691 : Goal L.ax-CK10-CK20-CCK'=CK20-CK10-CCK'
  hb2691 = ListNF.listnfeq' nf-e3 auto

  hb2692 : Goal L.ax-CK10-CK20-CCK'-CCK'=CK20-CK10-CCK'-CCK'
  hb2692 = ListNF.listnfeq' nf-e3 auto

  hb2693 : Goal L.ax-CK20-S0-K0-S0-CK10=S0-K0-S0-CK10-CCK'-CCK'-CX20-CCX0-S2-S2-S2-CS02-CS12-CS12-CCZ
  hb2693 = ListNF.listnfeq' nf-e4 auto

  hb2694 : Goal L.ax-CK20-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK10-CCK'-CX20-S2-S2-S2-CS02-CS12-CCZ
  hb2694 = ListNF.listnfeq' nf-e4 auto

  hb2695 : Goal L.ax-CK20-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CX20-CCX0-S2-S2-S2-CS02-CS12-CS12-CS12
  hb2695 = ListNF.listnfeq' nf-e4 auto

  hb2696 : Goal L.ax-CK20-S0-K0-S0-CK20=S0-K0-CK20-S0-CS02
  hb2696 = ListNF.listnfeq' nf-e4 auto

  hb2697 : Goal L.ax-CK20-S0-K0-S0-CK20-S0-CK10=S0-K0-CK20-CK10-CCK'-CCK'-CX10-CCX0-S0-S0-CS01-CS01-CS02-CS12
  hb2697 = ListNF.listnfeq' nf-e4 auto

  hb2698 : Goal L.ax-CK20-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CX10-CCX0-S0-S0-CS01-CS01-CS02-CCZ
  hb2698 = ListNF.listnfeq' nf-e4 auto

  hb2699 : Goal L.ax-CK20-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CX10-S0-S0-CS01-CS01-CS02-CS12-CS12-CS12-CCZ
  hb2699 = ListNF.listnfeq' nf-e4 auto

  hb2700 : Goal L.ax-CK20-S0-K0-S0-CK20-CK10=S0-K0-CK20-S0-CK10-CCK'-CCK'-CCX0-CS02-CS12-CS12-CCZ
  hb2700 = ListNF.listnfeq' nf-e4 auto

  hb2701 : Goal L.ax-CK20-S0-K0-S0-CK20-CK10-CCK'=S0-K0-CK20-S0-CK10-CCK'-CS02
  hb2701 = ListNF.listnfeq' nf-e4 auto

  hb2702 : Goal L.ax-CK20-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CS02-CS12-CS12-CS12-CCZ
  hb2702 = ListNF.listnfeq' nf-e4 auto

  hb2703 : Goal L.ax-CK20-S0-K0-S0-CK20-CCK'=S0-K0-CK20-CCK'-CCX0-S0-CS02-CS12
  hb2703 = ListNF.listnfeq' nf-e4 auto

  hb2704 : Goal L.ax-CK20-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCK'-CCX0-S0-CS02-CCZ
  hb2704 = ListNF.listnfeq' nf-e4 auto

  hb2705 : Goal L.ax-CK20-S0-K0-CK10=S0-K0-CK10-CCK'-CCK'-CX20-CS02-CS02-CS02-CS12-CCZ
  hb2705 = ListNF.listnfeq' nf-e4 auto

  hb2706 : Goal L.ax-CK20-S0-K0-CK10-CCK'=S0-K0-CK10-CCK'-CX20-CS02-CS02-CS02-CS12-CCZ
  hb2706 = ListNF.listnfeq' nf-e4 auto

  hb2707 : Goal L.ax-CK20-S0-K0-CK10-CCK'-CCK'=S0-K0-CK10-CX20-CS02-CS02-CS02-CS12-CCZ
  hb2707 = ListNF.listnfeq' nf-e4 auto

  hb2708 : Goal L.ax-CK20-S0-K0-CK20=S0-K0-S0-CK20-S0-S0-S0-S2-S2-S2-CS02-CS02-CS02
  hb2708 = ListNF.listnfeq' nf-e4 auto

  hb2709 : Goal L.ax-CK20-S0-K0-CK20-S0-CK10=S0-K0-S0-CK20-CK10-CCK'-CCK'-S2-S2-S2-CS02-CS02-CS02-CS12-CCZ
  hb2709 = ListNF.listnfeq' nf-e4 auto

  hb2710 : Goal L.ax-CK20-S0-K0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-CK10-CCK'-S2-S2-S2-CS02-CS02-CS02
  hb2710 = ListNF.listnfeq' nf-e4 auto

  hb2711 : Goal L.ax-CK20-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCX0-S2-S2-S2-CS02-CS02-CS02-CS12-CS12-CS12
  hb2711 = ListNF.listnfeq' nf-e4 auto

  hb2712 : Goal L.ax-CK20-S0-K0-CK20-CK10=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'-CX10-S0-S0-S2-S2-S2-CS01-CS01-CS02-CS02-CS02-CS12-CS12
  hb2712 = ListNF.listnfeq' nf-e4 auto

  hb2713 : Goal L.ax-CK20-S0-K0-CK20-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CX10-CCX0-S0-S0-S2-S2-S2-CS01-CS01-CS02-CS02-CS02-CCZ
  hb2713 = ListNF.listnfeq' nf-e4 auto

  hb2714 : Goal L.ax-CK20-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CX10-CCX0-S0-S0-S2-S2-S2-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CS12
  hb2714 = ListNF.listnfeq' nf-e4 auto

  hb2715 : Goal L.ax-CK20-S0-K0-CK20-CCK'=S0-K0-S0-CK20-CCK'-CCX0-S0-S0-S0-S2-S2-S2-CS02-CS02-CS02-CS12
  hb2715 = ListNF.listnfeq' nf-e4 auto

  hb2716 : Goal L.ax-CK20-S0-K0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CCK'-CCK'-CCX0-S0-S0-S0-S2-S2-S2-CS02-CS02-CS02-CCZ
  hb2716 = ListNF.listnfeq' nf-e4 auto

  hb2717 : Goal L.ax-CK20-S0-K0-CCK'=S0-K0-CCK'-CCK'-CX20-CCX0-CS02-CS02-CS02-CCZ
  hb2717 = ListNF.listnfeq' nf-e4 auto

  hb2718 : Goal L.ax-CK20-S0-K0-CCK'-CCK'=S0-K0-CCK'-CX20-CCX0-CS02-CS02-CS02-CS12-CS12-CS12
  hb2718 = ListNF.listnfeq' nf-e4 auto

  hb2719 : Goal L.ax-CK20-S0-CK20-S0-CK10=S0-CK20-S0-CK10-CCK'-CCK'-CX20-CCX0-S2-S2-S2-CS02-CS12-CS12-CCZ
  hb2719 = ListNF.listnfeq' nf-e3 auto

  hb2720 : Goal L.ax-CK20-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-CX20-S2-S2-S2-CS02-CS12-CCZ
  hb2720 = ListNF.listnfeq' nf-e3 auto

  hb2721 : Goal L.ax-CK20-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CX20-CCX0-S2-S2-S2-CS02-CS12-CS12-CS12
  hb2721 = ListNF.listnfeq' nf-e3 auto

  hb2722 : Goal L.ax-CK20-S0-CK20-CK10=S0-CK20-CK10-CCK'-CCK'-CX20-CS02-CS02-CS02-CS12-CCZ
  hb2722 = ListNF.listnfeq' nf-e3 auto

  hb2723 : Goal L.ax-CK20-S0-CK20-CK10-CCK'=S0-CK20-CK10-CCK'-CX20-CS02-CS02-CS02-CS12-CCZ
  hb2723 = ListNF.listnfeq' nf-e3 auto

  hb2724 : Goal L.ax-CK20-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CX20-CS02-CS02-CS02-CS12-CCZ
  hb2724 = ListNF.listnfeq' nf-e3 auto

  hb2725 : Goal L.ax-CK20-S0-CK20-CCK'=S0-CK20-CCK'-CCK'-CX20-CCX0-CS02-CS02-CS02-CCZ
  hb2725 = ListNF.listnfeq' nf-e3 auto

  hb2726 : Goal L.ax-CK20-S0-CK20-CCK'-CCK'=S0-CK20-CCK'-CX20-CCX0-CS02-CS02-CS02-CS12-CS12-CS12
  hb2726 = ListNF.listnfeq' nf-e3 auto

  hb2727 : Goal L.ax-CK20-K0-S0-CK10=K0-CK20-S0-CK10
  hb2727 = ListNF.listnfeq' nf-e4 auto

  hb2728 : Goal L.ax-CK20-K0-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'
  hb2728 = ListNF.listnfeq' nf-e4 auto

  hb2729 : Goal L.ax-CK20-K0-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CCK'-CCK'
  hb2729 = ListNF.listnfeq' nf-e4 auto

  hb2730 : Goal L.ax-CK20-K0-S0-CK20=K0-S0-CK20-CX20-CS02-CS02-CS02
  hb2730 = ListNF.listnfeq' nf-e4 auto

  hb2731 : Goal L.ax-CK20-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-CCK'-CCK'-CX20-CCX0-S2-S2-S2-CS02-CS12-CS12-CCZ
  hb2731 = ListNF.listnfeq' nf-e4 auto

  hb2732 : Goal L.ax-CK20-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCK'-CX20-S2-S2-S2-CS02-CS12-CCZ
  hb2732 = ListNF.listnfeq' nf-e4 auto

  hb2733 : Goal L.ax-CK20-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CX20-CCX0-S2-S2-S2-CS02-CS12-CS12-CS12
  hb2733 = ListNF.listnfeq' nf-e4 auto

  hb2734 : Goal L.ax-CK20-K0-S0-CK20-CK10=K0-S0-CK20-CK10-CCK'-CCK'-CX20-CS02-CS02-CS02-CS12-CCZ
  hb2734 = ListNF.listnfeq' nf-e4 auto

  hb2735 : Goal L.ax-CK20-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CX20-CS02-CS02-CS02-CS12-CCZ
  hb2735 = ListNF.listnfeq' nf-e4 auto

  hb2736 : Goal L.ax-CK20-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CX20-CS02-CS02-CS02-CS12-CCZ
  hb2736 = ListNF.listnfeq' nf-e4 auto

  hb2737 : Goal L.ax-CK20-K0-S0-CK20-CCK'=K0-S0-CK20-CCK'-CCK'-CX20-CCX0-CS02-CS02-CS02-CCZ
  hb2737 = ListNF.listnfeq' nf-e4 auto

  hb2738 : Goal L.ax-CK20-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CX20-CCX0-CS02-CS02-CS02-CS12-CS12-CS12
  hb2738 = ListNF.listnfeq' nf-e4 auto

  hb2739 : Goal L.ax-CK20-K0-CK10=K0-CK20-CK10
  hb2739 = ListNF.listnfeq' nf-e4 auto

  hb2740 : Goal L.ax-CK20-K0-CK10-CCK'=K0-CK20-CK10-CCK'
  hb2740 = ListNF.listnfeq' nf-e4 auto

  hb2741 : Goal L.ax-CK20-K0-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCK'
  hb2741 = ListNF.listnfeq' nf-e4 auto

  hb2742 : Goal L.ax-CK20-K0-CK20=K0-S2-S2-S2
  hb2742 = ListNF.listnfeq' nf-e4 auto

  hb2743 : Goal L.ax-CK20-K0-CK20-S0-CK10=K0-S0-CK10-S2-S2-S2
  hb2743 = ListNF.listnfeq' nf-e4 auto

  hb2744 : Goal L.ax-CK20-K0-CK20-S0-CK10-CCK'=K0-S0-CK10-CCK'-S2-S2-S2
  hb2744 = ListNF.listnfeq' nf-e4 auto

  hb2745 : Goal L.ax-CK20-K0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CCK'-S2-S2-S2
  hb2745 = ListNF.listnfeq' nf-e4 auto

  hb2746 : Goal L.ax-CK20-K0-CK20-CK10=K0-CK10-S2-S2-S2
  hb2746 = ListNF.listnfeq' nf-e4 auto

  hb2747 : Goal L.ax-CK20-K0-CK20-CK10-CCK'=K0-CK10-CCK'-S2-S2-S2
  hb2747 = ListNF.listnfeq' nf-e4 auto

  hb2748 : Goal L.ax-CK20-K0-CK20-CK10-CCK'-CCK'=K0-CK10-CCK'-CCK'-S2-S2-S2
  hb2748 = ListNF.listnfeq' nf-e4 auto

  hb2749 : Goal L.ax-CK20-K0-CK20-CCK'=K0-CCK'-S2-S2-S2
  hb2749 = ListNF.listnfeq' nf-e4 auto

  hb2750 : Goal L.ax-CK20-K0-CK20-CCK'-CCK'=K0-CCK'-CCK'-S2-S2-S2
  hb2750 = ListNF.listnfeq' nf-e4 auto

  hb2751 : Goal L.ax-CK20-K0-CCK'=K0-CK20-CCK'
  hb2751 = ListNF.listnfeq' nf-e4 auto

  hb2752 : Goal L.ax-CK20-K0-CCK'-CCK'=K0-CK20-CCK'-CCK'
  hb2752 = ListNF.listnfeq' nf-e4 auto

  hb2753 : Goal L.ax-CK20-CK20-S0-CK10=S0-CK10-S2-S2-S2
  hb2753 = ListNF.listnfeq' nf-e3 auto

  hb2754 : Goal L.ax-CK20-CK20-S0-CK10-CCK'=S0-CK10-CCK'-S2-S2-S2
  hb2754 = ListNF.listnfeq' nf-e3 auto

  hb2755 : Goal L.ax-CK20-CK20-S0-CK10-CCK'-CCK'=S0-CK10-CCK'-CCK'-S2-S2-S2
  hb2755 = ListNF.listnfeq' nf-e3 auto

  hb2756 : Goal L.ax-CK20-CK20-CK10=CK10-S2-S2-S2
  hb2756 = ListNF.listnfeq' nf-e3 auto

  hb2757 : Goal L.ax-CK20-CK20-CK10-CCK'=CK10-CCK'-S2-S2-S2
  hb2757 = ListNF.listnfeq' nf-e3 auto

  hb2758 : Goal L.ax-CK20-CK20-CK10-CCK'-CCK'=CK10-CCK'-CCK'-S2-S2-S2
  hb2758 = ListNF.listnfeq' nf-e3 auto

  hb2759 : Goal L.ax-CK20-CK20-CCK'=CCK'-S2-S2-S2
  hb2759 = ListNF.listnfeq' nf-e3 auto

  hb2760 : Goal L.ax-CK20-CK20-CCK'-CCK'=CCK'-CCK'-S2-S2-S2
  hb2760 = ListNF.listnfeq' nf-e3 auto

  hb2761 : Goal L.ax-CCK'-S0-K0-S0-CK10=S0-K0-S0-CK10-CCK'
  hb2761 = ListNF.listnfeq' nf-e4 auto

  hb2762 : Goal L.ax-CCK'-S0-K0-S0-CK10-CCK'=S0-K0-S0-CK10-CCK'-CCK'
  hb2762 = ListNF.listnfeq' nf-e4 auto

  hb2763 : Goal L.ax-CCK'-S0-K0-S0-CK10-CCK'-CCK'=S0-K0-S0-CK10-CS12-CS12
  hb2763 = ListNF.listnfeq' nf-e4 auto

  hb2764 : Goal L.ax-CCK'-S0-K0-S0-CK20=S0-K0-S0-CK20-CCK'
  hb2764 = ListNF.listnfeq' nf-e4 auto

  hb2765 : Goal L.ax-CCK'-S0-K0-S0-CK20-S0-CK10=S0-K0-S0-CK20-S0-CK10-CCK'
  hb2765 = ListNF.listnfeq' nf-e4 auto

  hb2766 : Goal L.ax-CCK'-S0-K0-S0-CK20-S0-CK10-CCK'=S0-K0-S0-CK20-S0-CK10-CCK'-CCK'
  hb2766 = ListNF.listnfeq' nf-e4 auto

  hb2767 : Goal L.ax-CCK'-S0-K0-S0-CK20-S0-CK10-CCK'-CCK'=S0-K0-S0-CK20-S0-CK10-CS12-CS12
  hb2767 = ListNF.listnfeq' nf-e4 auto

  hb2768 : Goal L.ax-CCK'-S0-K0-S0-CK20-CK10=S0-K0-S0-CK20-CK10-CCK'-CCK'-CCX0-CS12
  hb2768 = ListNF.listnfeq' nf-e4 auto

  hb2769 : Goal L.ax-CCK'-S0-K0-S0-CK20-CK10-CCK'=S0-K0-S0-CK20-CK10-CS12-CS12-CS12-CCZ
  hb2769 = ListNF.listnfeq' nf-e4 auto

  hb2770 : Goal L.ax-CCK'-S0-K0-S0-CK20-CK10-CCK'-CCK'=S0-K0-S0-CK20-CK10-CCK'-CCX0-CCZ
  hb2770 = ListNF.listnfeq' nf-e4 auto

  hb2771 : Goal L.ax-CCK'-S0-K0-S0-CK20-CCK'=S0-K0-S0-CK20-CCK'-CCK'
  hb2771 = ListNF.listnfeq' nf-e4 auto

  hb2772 : Goal L.ax-CCK'-S0-K0-S0-CK20-CCK'-CCK'=S0-K0-S0-CK20-CS12-CS12
  hb2772 = ListNF.listnfeq' nf-e4 auto

  hb2773 : Goal L.ax-CCK'-S0-K0-CK10=S0-K0-CK10-CCK'-CCK'-CCX0-CS12
  hb2773 = ListNF.listnfeq' nf-e4 auto

  hb2774 : Goal L.ax-CCK'-S0-K0-CK10-CCK'=S0-K0-CK10-CS12-CS12-CS12-CCZ
  hb2774 = ListNF.listnfeq' nf-e4 auto

  hb2775 : Goal L.ax-CCK'-S0-K0-CK10-CCK'-CCK'=S0-K0-CK10-CCK'-CCX0-CCZ
  hb2775 = ListNF.listnfeq' nf-e4 auto

  hb2776 : Goal L.ax-CCK'-S0-K0-CK20=S0-K0-CK20-CCK'-CCK'-CCX0-CS12
  hb2776 = ListNF.listnfeq' nf-e4 auto

  hb2777 : Goal L.ax-CCK'-S0-K0-CK20-S0-CK10=S0-K0-CK20-S0-CK10-CCK'-CCK'-CCX0-CS12-CS12-CCZ
  hb2777 = ListNF.listnfeq' nf-e4 auto

  hb2778 : Goal L.ax-CCK'-S0-K0-CK20-S0-CK10-CCK'=S0-K0-CK20-S0-CK10-CCX0-CS12-CS12-CS12
  hb2778 = ListNF.listnfeq' nf-e4 auto

  hb2779 : Goal L.ax-CCK'-S0-K0-CK20-S0-CK10-CCK'-CCK'=S0-K0-CK20-S0-CK10-CCK'-CS12-CS12-CS12-CCZ
  hb2779 = ListNF.listnfeq' nf-e4 auto

  hb2780 : Goal L.ax-CCK'-S0-K0-CK20-CK10=S0-K0-CK20-CK10-CCK'
  hb2780 = ListNF.listnfeq' nf-e4 auto

  hb2781 : Goal L.ax-CCK'-S0-K0-CK20-CK10-CCK'=S0-K0-CK20-CK10-CCK'-CCK'
  hb2781 = ListNF.listnfeq' nf-e4 auto

  hb2782 : Goal L.ax-CCK'-S0-K0-CK20-CK10-CCK'-CCK'=S0-K0-CK20-CK10-CS12-CS12
  hb2782 = ListNF.listnfeq' nf-e4 auto

  hb2783 : Goal L.ax-CCK'-S0-K0-CK20-CCK'=S0-K0-CK20-CS12-CS12-CS12-CCZ
  hb2783 = ListNF.listnfeq' nf-e4 auto

  hb2784 : Goal L.ax-CCK'-S0-K0-CK20-CCK'-CCK'=S0-K0-CK20-CCK'-CCX0-CCZ
  hb2784 = ListNF.listnfeq' nf-e4 auto

  hb2785 : Goal L.ax-CCK'-S0-K0-CCK'=S0-K0-CCK'-CCK'
  hb2785 = ListNF.listnfeq' nf-e4 auto

  hb2786 : Goal L.ax-CCK'-S0-K0-CCK'-CCK'=S0-K0-CS12-CS12
  hb2786 = ListNF.listnfeq' nf-e4 auto

  hb2787 : Goal L.ax-CCK'-S0-CK10-CCK'=S0-CK10-CCK'-CCK'
  hb2787 = ListNF.listnfeq' nf-e3 auto

  hb2788 : Goal L.ax-CCK'-S0-CK10-CCK'-CCK'=S0-CK10-CS12-CS12
  hb2788 = ListNF.listnfeq' nf-e3 auto

  hb2789 : Goal L.ax-CCK'-S0-CK20-S0-CK10=S0-CK20-S0-CK10-CCK'
  hb2789 = ListNF.listnfeq' nf-e3 auto

  hb2790 : Goal L.ax-CCK'-S0-CK20-S0-CK10-CCK'=S0-CK20-S0-CK10-CCK'-CCK'
  hb2790 = ListNF.listnfeq' nf-e3 auto

  hb2791 : Goal L.ax-CCK'-S0-CK20-S0-CK10-CCK'-CCK'=S0-CK20-S0-CK10-CS12-CS12
  hb2791 = ListNF.listnfeq' nf-e3 auto

  hb2792 : Goal L.ax-CCK'-S0-CK20-CK10=S0-CK20-CK10-CCK'-CCK'-CCX0-CS12
  hb2792 = ListNF.listnfeq' nf-e3 auto

  hb2793 : Goal L.ax-CCK'-S0-CK20-CK10-CCK'=S0-CK20-CK10-CS12-CS12-CS12-CCZ
  hb2793 = ListNF.listnfeq' nf-e3 auto

  hb2794 : Goal L.ax-CCK'-S0-CK20-CK10-CCK'-CCK'=S0-CK20-CK10-CCK'-CCX0-CCZ
  hb2794 = ListNF.listnfeq' nf-e3 auto

  hb2795 : Goal L.ax-CCK'-S0-CK20-CCK'=S0-CK20-CCK'-CCK'
  hb2795 = ListNF.listnfeq' nf-e3 auto

  hb2796 : Goal L.ax-CCK'-S0-CK20-CCK'-CCK'=S0-CK20-CS12-CS12
  hb2796 = ListNF.listnfeq' nf-e3 auto

  hb2797 : Goal L.ax-CCK'-K0-S0-CK10=K0-S0-CK10-CCK'-CCK'-CCX0-CS12-CS12-CCZ
  hb2797 = ListNF.listnfeq' nf-e4 auto

  hb2798 : Goal L.ax-CCK'-K0-S0-CK10-CCK'=K0-S0-CK10-CCX0-CS12-CS12-CS12
  hb2798 = ListNF.listnfeq' nf-e4 auto

  hb2799 : Goal L.ax-CCK'-K0-S0-CK10-CCK'-CCK'=K0-S0-CK10-CCK'-CS12-CS12-CS12-CCZ
  hb2799 = ListNF.listnfeq' nf-e4 auto

  hb2800 : Goal L.ax-CCK'-K0-S0-CK20=K0-S0-CK20-CCK'-CCK'-CCX0-CS12-CS12-CCZ
  hb2800 = ListNF.listnfeq' nf-e4 auto

  hb2801 : Goal L.ax-CCK'-K0-S0-CK20-S0-CK10=K0-S0-CK20-S0-CK10-CCK'-CCK'-CS12-CCZ
  hb2801 = ListNF.listnfeq' nf-e4 auto

  hb2802 : Goal L.ax-CCK'-K0-S0-CK20-S0-CK10-CCK'=K0-S0-CK20-S0-CK10-CCX0-CCZ
  hb2802 = ListNF.listnfeq' nf-e4 auto

  hb2803 : Goal L.ax-CCK'-K0-S0-CK20-S0-CK10-CCK'-CCK'=K0-S0-CK20-S0-CK10-CCK'-CCX0-CS12-CS12-CS12
  hb2803 = ListNF.listnfeq' nf-e4 auto

  hb2804 : Goal L.ax-CCK'-K0-S0-CK20-CK10=K0-S0-CK20-CK10-CCK'-CCX0-CS12
  hb2804 = ListNF.listnfeq' nf-e4 auto

  hb2805 : Goal L.ax-CCK'-K0-S0-CK20-CK10-CCK'=K0-S0-CK20-CK10-CCK'-CCK'-CS12-CCZ
  hb2805 = ListNF.listnfeq' nf-e4 auto

  hb2806 : Goal L.ax-CCK'-K0-S0-CK20-CK10-CCK'-CCK'=K0-S0-CK20-CK10-CCX0-CCZ
  hb2806 = ListNF.listnfeq' nf-e4 auto

  hb2807 : Goal L.ax-CCK'-K0-S0-CK20-CCK'=K0-S0-CK20-CCX0-CS12-CS12-CS12
  hb2807 = ListNF.listnfeq' nf-e4 auto

  hb2808 : Goal L.ax-CCK'-K0-S0-CK20-CCK'-CCK'=K0-S0-CK20-CCK'-CS12-CS12-CS12-CCZ
  hb2808 = ListNF.listnfeq' nf-e4 auto

  hb2809 : Goal L.ax-CCK'-K0-CK10=K0-CK10-CCK'
  hb2809 = ListNF.listnfeq' nf-e4 auto

  hb2810 : Goal L.ax-CCK'-K0-CK10-CCK'=K0-CK10-CCK'-CCK'
  hb2810 = ListNF.listnfeq' nf-e4 auto

  hb2811 : Goal L.ax-CCK'-K0-CK10-CCK'-CCK'=K0-CK10-CS12-CS12
  hb2811 = ListNF.listnfeq' nf-e4 auto

  hb2812 : Goal L.ax-CCK'-K0-CK20=K0-CK20-CCK'
  hb2812 = ListNF.listnfeq' nf-e4 auto

  hb2813 : Goal L.ax-CCK'-K0-CK20-S0-CK10=K0-CK20-S0-CK10-CCK'
  hb2813 = ListNF.listnfeq' nf-e4 auto

  hb2814 : Goal L.ax-CCK'-K0-CK20-S0-CK10-CCK'=K0-CK20-S0-CK10-CCK'-CCK'
  hb2814 = ListNF.listnfeq' nf-e4 auto

  hb2815 : Goal L.ax-CCK'-K0-CK20-S0-CK10-CCK'-CCK'=K0-CK20-S0-CK10-CS12-CS12
  hb2815 = ListNF.listnfeq' nf-e4 auto

  hb2816 : Goal L.ax-CCK'-K0-CK20-CK10=K0-CK20-CK10-CCK'-CCK'-CCX0-CS12
  hb2816 = ListNF.listnfeq' nf-e4 auto

  hb2817 : Goal L.ax-CCK'-K0-CK20-CK10-CCK'=K0-CK20-CK10-CS12-CS12-CS12-CCZ
  hb2817 = ListNF.listnfeq' nf-e4 auto

  hb2818 : Goal L.ax-CCK'-K0-CK20-CK10-CCK'-CCK'=K0-CK20-CK10-CCK'-CCX0-CCZ
  hb2818 = ListNF.listnfeq' nf-e4 auto

  hb2819 : Goal L.ax-CCK'-K0-CK20-CCK'=K0-CK20-CCK'-CCK'
  hb2819 = ListNF.listnfeq' nf-e4 auto

  hb2820 : Goal L.ax-CCK'-K0-CK20-CCK'-CCK'=K0-CK20-CS12-CS12
  hb2820 = ListNF.listnfeq' nf-e4 auto

  hb2821 : Goal L.ax-CCK'-K0-CCK'=K0-CS12-CS12-CS12-CCZ
  hb2821 = ListNF.listnfeq' nf-e4 auto

  hb2822 : Goal L.ax-CCK'-K0-CCK'-CCK'=K0-CCK'-CCX0-CCZ
  hb2822 = ListNF.listnfeq' nf-e4 auto

  hb2823 : Goal L.ax-CCK'-CK10-CCK'=CK10-CS12-CS12-CS12-CCZ
  hb2823 = ListNF.listnfeq' nf-e3 auto

  hb2824 : Goal L.ax-CCK'-CK10-CCK'-CCK'=CK10-CCK'-CCX0-CCZ
  hb2824 = ListNF.listnfeq' nf-e3 auto

  hb2825 : Goal L.ax-CCK'-CK20-S0-CK10=CK20-S0-CK10-CCK'-CCK'-CCX0-CS12-CS12-CCZ
  hb2825 = ListNF.listnfeq' nf-e3 auto

  hb2826 : Goal L.ax-CCK'-CK20-S0-CK10-CCK'=CK20-S0-CK10-CCX0-CS12-CS12-CS12
  hb2826 = ListNF.listnfeq' nf-e3 auto

  hb2827 : Goal L.ax-CCK'-CK20-S0-CK10-CCK'-CCK'=CK20-S0-CK10-CCK'-CS12-CS12-CS12-CCZ
  hb2827 = ListNF.listnfeq' nf-e3 auto

  hb2828 : Goal L.ax-CCK'-CK20-CK10=CK20-CK10-CCK'
  hb2828 = ListNF.listnfeq' nf-e3 auto

  hb2829 : Goal L.ax-CCK'-CK20-CK10-CCK'=CK20-CK10-CCK'-CCK'
  hb2829 = ListNF.listnfeq' nf-e3 auto

  hb2830 : Goal L.ax-CCK'-CK20-CK10-CCK'-CCK'=CK20-CK10-CS12-CS12
  hb2830 = ListNF.listnfeq' nf-e3 auto

  hb2831 : Goal L.ax-CCK'-CK20-CCK'=CK20-CS12-CS12-CS12-CCZ
  hb2831 = ListNF.listnfeq' nf-e3 auto

  hb2832 : Goal L.ax-CCK'-CK20-CCK'-CCK'=CK20-CCK'-CCX0-CCZ
  hb2832 = ListNF.listnfeq' nf-e3 auto

