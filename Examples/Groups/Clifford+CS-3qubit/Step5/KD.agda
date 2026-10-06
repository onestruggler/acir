------------------------------------------------------------------------
-- Presentations of groups
--
-- Ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 3-qubit Clifford+CS operators"
-- (arXiv:2306.08530, CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Presentation.Tactics.Equality as Eq using (_≡_ ; auto)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; _∨_)
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

open import Examples.Groups.Clifford+CS-3qubit.Step5.Rel
open import Examples.Groups.Clifford+CS-3qubit.Step5.S8
open import Examples.Groups.Clifford+CS-3qubit.Step5.Comm
open import Examples.Groups.Clifford+CS-3qubit.Step5.Order
open import Examples.Groups.Clifford+CS-3qubit.Step5.Basis-Change
open import Examples.Groups.Clifford+CS-3qubit.Step5.S8D

module Examples.Groups.Clifford+CS-3qubit.Step5.KD where

  spd-conj : let X = Gate in let Γ = Rel in (h n : X) -> Maybe (∃ λ (n' : List X) -> Γ ⊢ [ h ]ʷ • [ n ]ʷ === word-of-list n' • [ h ]ʷ)
  spd-conj X0-gen S0-gen = just ( S0-gen ∷ S0-gen ∷ S0-gen ∷ iI-gen ∷ [] , up-to-assoc auto (axiom ax-X0-S0=S0-S0-S0-iI-X0) )
  spd-conj X0-gen S1-gen = just ( S1-gen ∷ [] , up-to-assoc auto (axiom ax-X0-S1=S1-X0) )
  spd-conj X0-gen S2-gen = just ( S2-gen ∷ [] , up-to-assoc auto (axiom ax-X0-S2=S2-X0) )
  spd-conj X0-gen CS01-gen = just ( S1-gen ∷ CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ [] , up-to-assoc auto (axiom ax-X0-CS01=S1-CS01-CS01-CS01-X0) )
  spd-conj X0-gen CS02-gen = just ( S2-gen ∷ CS02-gen ∷ CS02-gen ∷ CS02-gen ∷ [] , up-to-assoc auto (axiom ax-X0-CS02=S2-CS02-CS02-CS02-X0) )
  spd-conj X0-gen CS12-gen = just ( CS12-gen ∷ [] , up-to-assoc auto (axiom ax-X0-CS12=CS12-X0) )
  spd-conj X0-gen CCZ-gen = just ( CS12-gen ∷ CS12-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-X0-CCZ=CS12-CS12-CCZ-X0) )
  spd-conj X0-gen iI-gen = just ( iI-gen ∷ [] , up-to-assoc auto (axiom ax-X0-iI=iI-X0) )
  spd-conj CX10-gen S0-gen = just ( S0-gen ∷ S1-gen ∷ CS01-gen ∷ CS01-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-S0=S0-S1-CS01-CS01-CX10) )
  spd-conj CX10-gen S1-gen = just ( S1-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-S1=S1-CX10) )
  spd-conj CX10-gen S2-gen = just ( S2-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-S2=S2-CX10) )
  spd-conj CX10-gen CS01-gen = just ( S1-gen ∷ CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-CS01=S1-CS01-CS01-CS01-CX10) )
  spd-conj CX10-gen CS02-gen = just ( CS02-gen ∷ CS12-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-CS02=CS02-CS12-CCZ-CX10) )
  spd-conj CX10-gen CS12-gen = just ( CS12-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-CS12=CS12-CX10) )
  spd-conj CX10-gen CCZ-gen = just ( CS12-gen ∷ CS12-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-CCZ=CS12-CS12-CCZ-CX10) )
  spd-conj CX10-gen iI-gen = just ( iI-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-iI=iI-CX10) )
  spd-conj CX20-gen S0-gen = just ( S0-gen ∷ S2-gen ∷ CS02-gen ∷ CS02-gen ∷ [] , up-to-assoc auto (axiom ax-CX20-S0=S0-S2-CS02-CS02-CX20) )
  spd-conj CX20-gen S1-gen = just ( S1-gen ∷ [] , up-to-assoc auto (axiom ax-CX20-S1=S1-CX20) )
  spd-conj CX20-gen S2-gen = just ( S2-gen ∷ [] , up-to-assoc auto (axiom ax-CX20-S2=S2-CX20) )
  spd-conj CX20-gen CS01-gen = just ( CS01-gen ∷ CS12-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CX20-CS01=CS01-CS12-CCZ-CX20) )
  spd-conj CX20-gen CS02-gen = just ( S2-gen ∷ CS02-gen ∷ CS02-gen ∷ CS02-gen ∷ [] , up-to-assoc auto (axiom ax-CX20-CS02=S2-CS02-CS02-CS02-CX20) )
  spd-conj CX20-gen CS12-gen = just ( CS12-gen ∷ [] , up-to-assoc auto (axiom ax-CX20-CS12=CS12-CX20) )
  spd-conj CX20-gen CCZ-gen = just ( CS12-gen ∷ CS12-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CX20-CCZ=CS12-CS12-CCZ-CX20) )
  spd-conj CX20-gen iI-gen = just ( iI-gen ∷ [] , up-to-assoc auto (axiom ax-CX20-iI=iI-CX20) )
  spd-conj CCX0-gen S0-gen = just ( S0-gen ∷ CS12-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-S0=S0-CS12-CCZ-CCX0) )
  spd-conj CCX0-gen S1-gen = just ( S1-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-S1=S1-CCX0) )
  spd-conj CCX0-gen S2-gen = just ( S2-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-S2=S2-CCX0) )
  spd-conj CCX0-gen CS01-gen = just ( CS01-gen ∷ CS12-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-CS01=CS01-CS12-CCZ-CCX0) )
  spd-conj CCX0-gen CS02-gen = just ( CS02-gen ∷ CS12-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-CS02=CS02-CS12-CCZ-CCX0) )
  spd-conj CCX0-gen CS12-gen = just ( CS12-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-CS12=CS12-CCX0) )
  spd-conj CCX0-gen CCZ-gen = just ( CS12-gen ∷ CS12-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-CCZ=CS12-CS12-CCZ-CCX0) )
  spd-conj CCX0-gen iI-gen = just ( iI-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-iI=iI-CCX0) )
  spd-conj _ _ = nothing

  module SPD = SemiDirect isP16 isD nfp16 nfd group-like spd-conj


  p24-spde4-conj : let X = Gate in let Γ = Rel in (h n : X) -> Maybe (∃ λ (n' : List X) -> Γ ⊢ [ h ]ʷ • [ n ]ʷ === word-of-list n' • [ h ]ʷ)
  p24-spde4-conj X1-gen K0-gen = just ( K0-gen ∷ [] , up-to-assoc auto (axiom ax-X1-K0=K0-X1) )
  p24-spde4-conj X1-gen X0-gen = just ( X0-gen ∷ [] , up-to-assoc auto (axiom ax-X1-X0=X0-X1) )
  p24-spde4-conj X1-gen CX10-gen = just ( X0-gen ∷ CX10-gen ∷ [] , up-to-assoc auto (axiom ax-X1-CX10=X0-CX10-X1) )
  p24-spde4-conj X1-gen CX20-gen = just ( CX20-gen ∷ [] , up-to-assoc auto (axiom ax-X1-CX20=CX20-X1) )
  p24-spde4-conj X1-gen CCX0-gen = just ( CX20-gen ∷ CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-X1-CCX0=CX20-CCX0-X1) )
  p24-spde4-conj X1-gen S0-gen = just ( S0-gen ∷ [] , up-to-assoc auto (axiom ax-X1-S0=S0-X1) )
  p24-spde4-conj X1-gen S1-gen = just ( S1-gen ∷ S1-gen ∷ S1-gen ∷ iI-gen ∷ [] , up-to-assoc auto (axiom ax-X1-S1=S1-S1-S1-iI-X1) )
  p24-spde4-conj X1-gen S2-gen = just ( S2-gen ∷ [] , up-to-assoc auto (axiom ax-X1-S2=S2-X1) )
  p24-spde4-conj X1-gen CS01-gen = just ( S0-gen ∷ CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ [] , up-to-assoc auto (axiom ax-X1-CS01=S0-CS01-CS01-CS01-X1) )
  p24-spde4-conj X1-gen CS02-gen = just ( CS02-gen ∷ [] , up-to-assoc auto (axiom ax-X1-CS02=CS02-X1) )
  p24-spde4-conj X1-gen CS12-gen = just ( S2-gen ∷ CS12-gen ∷ CS12-gen ∷ CS12-gen ∷ [] , up-to-assoc auto (axiom ax-X1-CS12=S2-CS12-CS12-CS12-X1) )
  p24-spde4-conj X1-gen CCZ-gen = just ( CS02-gen ∷ CS02-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-X1-CCZ=CS02-CS02-CCZ-X1) )
  p24-spde4-conj X1-gen iI-gen = just ( iI-gen ∷ [] , up-to-assoc auto (axiom ax-X1-iI=iI-X1) )
  p24-spde4-conj X2-gen K0-gen = just ( K0-gen ∷ [] , up-to-assoc auto (axiom ax-X2-K0=K0-X2) )
  p24-spde4-conj X2-gen X0-gen = just ( X0-gen ∷ [] , up-to-assoc auto (axiom ax-X2-X0=X0-X2) )
  p24-spde4-conj X2-gen CX10-gen = just ( CX10-gen ∷ [] , up-to-assoc auto (axiom ax-X2-CX10=CX10-X2) )
  p24-spde4-conj X2-gen CX20-gen = just ( X0-gen ∷ CX20-gen ∷ [] , up-to-assoc auto (axiom ax-X2-CX20=X0-CX20-X2) )
  p24-spde4-conj X2-gen CCX0-gen = just ( CX10-gen ∷ CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-X2-CCX0=CX10-CCX0-X2) )
  p24-spde4-conj X2-gen S0-gen = just ( S0-gen ∷ [] , up-to-assoc auto (axiom ax-X2-S0=S0-X2) )
  p24-spde4-conj X2-gen S1-gen = just ( S1-gen ∷ [] , up-to-assoc auto (axiom ax-X2-S1=S1-X2) )
  p24-spde4-conj X2-gen S2-gen = just ( S2-gen ∷ S2-gen ∷ S2-gen ∷ iI-gen ∷ [] , up-to-assoc auto (axiom ax-X2-S2=S2-S2-S2-iI-X2) )
  p24-spde4-conj X2-gen CS01-gen = just ( CS01-gen ∷ [] , up-to-assoc auto (axiom ax-X2-CS01=CS01-X2) )
  p24-spde4-conj X2-gen CS02-gen = just ( S0-gen ∷ CS02-gen ∷ CS02-gen ∷ CS02-gen ∷ [] , up-to-assoc auto (axiom ax-X2-CS02=S0-CS02-CS02-CS02-X2) )
  p24-spde4-conj X2-gen CS12-gen = just ( S1-gen ∷ CS12-gen ∷ CS12-gen ∷ CS12-gen ∷ [] , up-to-assoc auto (axiom ax-X2-CS12=S1-CS12-CS12-CS12-X2) )
  p24-spde4-conj X2-gen CCZ-gen = just ( CS01-gen ∷ CS01-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-X2-CCZ=CS01-CS01-CCZ-X2) )
  p24-spde4-conj X2-gen iI-gen = just ( iI-gen ∷ [] , up-to-assoc auto (axiom ax-X2-iI=iI-X2) )
  p24-spde4-conj CX12-gen K0-gen = just ( K0-gen ∷ [] , up-to-assoc auto (axiom ax-CX12-K0=K0-CX12) )
  p24-spde4-conj CX12-gen X0-gen = just ( X0-gen ∷ [] , up-to-assoc auto (axiom ax-CX12-X0=X0-CX12) )
  p24-spde4-conj CX12-gen CX10-gen = just ( CX10-gen ∷ [] , up-to-assoc auto (axiom ax-CX12-CX10=CX10-CX12) )
  p24-spde4-conj CX12-gen CX20-gen = just ( CX10-gen ∷ CX20-gen ∷ [] , up-to-assoc auto (axiom ax-CX12-CX20=CX10-CX20-CX12) )
  p24-spde4-conj CX12-gen CCX0-gen = just ( CX10-gen ∷ CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CX12-CCX0=CX10-CCX0-CX12) )
  p24-spde4-conj CX12-gen S0-gen = just ( S0-gen ∷ [] , up-to-assoc auto (axiom ax-CX12-S0=S0-CX12) )
  p24-spde4-conj CX12-gen S1-gen = just ( S1-gen ∷ [] , up-to-assoc auto (axiom ax-CX12-S1=S1-CX12) )
  p24-spde4-conj CX12-gen S2-gen = just ( S1-gen ∷ S2-gen ∷ CS12-gen ∷ CS12-gen ∷ [] , up-to-assoc auto (axiom ax-CX12-S2=S1-S2-CS12-CS12-CX12) )
  p24-spde4-conj CX12-gen CS01-gen = just ( CS01-gen ∷ [] , up-to-assoc auto (axiom ax-CX12-CS01=CS01-CX12) )
  p24-spde4-conj CX12-gen CS02-gen = just ( CS01-gen ∷ CS02-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CX12-CS02=CS01-CS02-CCZ-CX12) )
  p24-spde4-conj CX12-gen CS12-gen = just ( S1-gen ∷ CS12-gen ∷ CS12-gen ∷ CS12-gen ∷ [] , up-to-assoc auto (axiom ax-CX12-CS12=S1-CS12-CS12-CS12-CX12) )
  p24-spde4-conj CX12-gen CCZ-gen = just ( CS01-gen ∷ CS01-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CX12-CCZ=CS01-CS01-CCZ-CX12) )
  p24-spde4-conj CX12-gen iI-gen = just ( iI-gen ∷ [] , up-to-assoc auto (axiom ax-CX12-iI=iI-CX12) )
  p24-spde4-conj CX21-gen K0-gen = just ( K0-gen ∷ [] , up-to-assoc auto (axiom ax-CX21-K0=K0-CX21) )
  p24-spde4-conj CX21-gen X0-gen = just ( X0-gen ∷ [] , up-to-assoc auto (axiom ax-CX21-X0=X0-CX21) )
  p24-spde4-conj CX21-gen CX10-gen = just ( CX10-gen ∷ CX20-gen ∷ [] , up-to-assoc auto (axiom ax-CX21-CX10=CX10-CX20-CX21) )
  p24-spde4-conj CX21-gen CX20-gen = just ( CX20-gen ∷ [] , up-to-assoc auto (axiom ax-CX21-CX20=CX20-CX21) )
  p24-spde4-conj CX21-gen CCX0-gen = just ( CX20-gen ∷ CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CX21-CCX0=CX20-CCX0-CX21) )
  p24-spde4-conj CX21-gen S0-gen = just ( S0-gen ∷ [] , up-to-assoc auto (axiom ax-CX21-S0=S0-CX21) )
  p24-spde4-conj CX21-gen S1-gen = just ( S1-gen ∷ S2-gen ∷ CS12-gen ∷ CS12-gen ∷ [] , up-to-assoc auto (axiom ax-CX21-S1=S1-S2-CS12-CS12-CX21) )
  p24-spde4-conj CX21-gen S2-gen = just ( S2-gen ∷ [] , up-to-assoc auto (axiom ax-CX21-S2=S2-CX21) )
  p24-spde4-conj CX21-gen CS01-gen = just ( CS01-gen ∷ CS02-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CX21-CS01=CS01-CS02-CCZ-CX21) )
  p24-spde4-conj CX21-gen CS02-gen = just ( CS02-gen ∷ [] , up-to-assoc auto (axiom ax-CX21-CS02=CS02-CX21) )
  p24-spde4-conj CX21-gen CS12-gen = just ( S2-gen ∷ CS12-gen ∷ CS12-gen ∷ CS12-gen ∷ [] , up-to-assoc auto (axiom ax-CX21-CS12=S2-CS12-CS12-CS12-CX21) )
  p24-spde4-conj CX21-gen CCZ-gen = just ( CS02-gen ∷ CS02-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CX21-CCZ=CS02-CS02-CCZ-CX21) )
  p24-spde4-conj CX21-gen iI-gen = just ( iI-gen ∷ [] , up-to-assoc auto (axiom ax-CX21-iI=iI-CX21) )
  p24-spde4-conj Swap12-gen K0-gen = just ( K0-gen ∷ [] , up-to-assoc auto (axiom ax-Swap12-K0=K0-Swap12) )
  p24-spde4-conj Swap12-gen X0-gen = just ( X0-gen ∷ [] , up-to-assoc auto (axiom ax-Swap12-X0=X0-Swap12) )
  p24-spde4-conj Swap12-gen CX10-gen = just ( CX20-gen ∷ [] , up-to-assoc auto (axiom ax-Swap12-CX10=CX20-Swap12) )
  p24-spde4-conj Swap12-gen CX20-gen = just ( CX10-gen ∷ [] , up-to-assoc auto (axiom ax-Swap12-CX20=CX10-Swap12) )
  p24-spde4-conj Swap12-gen CCX0-gen = just ( CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-Swap12-CCX0=CCX0-Swap12) )
  p24-spde4-conj Swap12-gen S0-gen = just ( S0-gen ∷ [] , up-to-assoc auto (axiom ax-Swap12-S0=S0-Swap12) )
  p24-spde4-conj Swap12-gen S1-gen = just ( S2-gen ∷ [] , up-to-assoc auto (axiom ax-Swap12-S1=S2-Swap12) )
  p24-spde4-conj Swap12-gen S2-gen = just ( S1-gen ∷ [] , up-to-assoc auto (axiom ax-Swap12-S2=S1-Swap12) )
  p24-spde4-conj Swap12-gen CS01-gen = just ( CS02-gen ∷ [] , up-to-assoc auto (axiom ax-Swap12-CS01=CS02-Swap12) )
  p24-spde4-conj Swap12-gen CS02-gen = just ( CS01-gen ∷ [] , up-to-assoc auto (axiom ax-Swap12-CS02=CS01-Swap12) )
  p24-spde4-conj Swap12-gen CS12-gen = just ( CS12-gen ∷ [] , up-to-assoc auto (axiom ax-Swap12-CS12=CS12-Swap12) )
  p24-spde4-conj Swap12-gen CCZ-gen = just ( CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-Swap12-CCZ=CCZ-Swap12) )
  p24-spde4-conj Swap12-gen iI-gen = just ( iI-gen ∷ [] , up-to-assoc auto (axiom ax-Swap12-iI=iI-Swap12) )

  p24-spde4-conj _ _ = nothing

  p24-step : Step-Function Gate Rel
  p24-step (X1-gen ∷ X1-gen ∷ xs) = just (xs , at-head (axiom ax-X1-X1=ε))
  p24-step (X2-gen ∷ X2-gen ∷ xs) = just (xs , at-head (axiom ax-X2-X2=ε))
  p24-step (CX12-gen ∷ CX12-gen ∷ xs) = just (xs , at-head (axiom ax-CX12-CX12=ε))
  p24-step (CX21-gen ∷ CX21-gen ∷ xs) = just (xs , at-head (axiom ax-CX21-CX21=ε))
  p24-step (Swap12-gen ∷ Swap12-gen ∷ xs) = just (xs , at-head (axiom ax-Swap12-Swap12=ε))
  p24-step (Swap12-gen ∷ X1-gen ∷ xs) = just (X2-gen ∷ Swap12-gen ∷ xs , at-head (axiom ax-Swap12-X1=X2-Swap12))
  p24-step (Swap12-gen ∷ X2-gen ∷ xs) = just (X1-gen ∷ Swap12-gen ∷ xs , at-head (axiom ax-Swap12-X2=X1-Swap12))
  p24-step (Swap12-gen ∷ CX12-gen ∷ xs) = just (CX21-gen ∷ Swap12-gen ∷ xs , at-head (axiom ax-Swap12-CX12=CX21-Swap12))
  p24-step (Swap12-gen ∷ CX21-gen ∷ xs) = just (CX12-gen ∷ Swap12-gen ∷ xs , at-head (axiom ax-Swap12-CX21=CX12-Swap12))
  p24-step (CX21-gen ∷ X1-gen ∷ xs) = just (X1-gen ∷ CX21-gen ∷ xs , at-head (axiom ax-CX21-X1=X1-CX21))
  p24-step (CX12-gen ∷ X2-gen ∷ xs) = just (X2-gen ∷ CX12-gen ∷ xs , at-head (axiom ax-CX12-X2=X2-CX12))
  p24-step (CX12-gen ∷ X1-gen ∷ xs) = just (X1-gen ∷ X2-gen ∷ CX12-gen ∷ xs , at-head (axiom ax-CX12-X1=X1-X2-CX12))
  p24-step (CX21-gen ∷ X2-gen ∷ xs) = just (X1-gen ∷ X2-gen ∷ CX21-gen ∷ xs , at-head (axiom ax-CX21-X2=X1-X2-CX21))
  p24-step (X2-gen ∷ X1-gen ∷ xs) = just (X1-gen ∷ X2-gen ∷ xs , at-head (axiom ax-X2-X1=X1-X2))
  p24-step (CX12-gen ∷ CX21-gen ∷ CX12-gen ∷ xs) = just (Swap12-gen ∷ xs , at-head (axiom ax-CX12-CX21-CX12=Swap12))
  p24-step (CX21-gen ∷ CX12-gen ∷ CX21-gen ∷ xs) = just (Swap12-gen ∷ xs , at-head (axiom ax-CX21-CX12-CX21=Swap12))
  p24-step (CX12-gen ∷ Swap12-gen ∷ xs) = just (CX21-gen ∷ CX12-gen ∷ xs , at-head (axiom ax-CX12-Swap12=CX21-CX12))
  p24-step (CX21-gen ∷ Swap12-gen ∷ xs) = just (CX12-gen ∷ CX21-gen ∷ xs , at-head (axiom ax-CX21-Swap12=CX12-CX21))
  p24-step _ = nothing

  module P24 = Rewriting.Step (step-cong p24-step)
  
  isP24 : Gate -> Bool
  isP24 CX12-gen = true
  isP24 CX21-gen = true
  isP24 X1-gen = true
  isP24 X2-gen = true
  isP24 Swap12-gen = true
  isP24 _ = false

  isk0spd : Gate -> Bool
  isk0spd CCX0-gen = true
  isk0spd CX10-gen = true
  isk0spd CX20-gen = true
  isk0spd X0-gen = true
  isk0spd K0-gen = true
  isk0spd x = isD x

  isPD : Gate -> Bool
  isPD x = isP x ∨ isD x


  nf-spd : ListNF Rel
  nf-spd = record { listnf = SPD.nfnh' ; lemma-listnf = SPD.lemma-nfnh' }

  nf-spde : ListNF Rel
  nf-spde = extend-nf (\x -> isP16 x ∨ isD x) nf-spd


  nfp24 : ListNF Rel
  nfp24 = record { listnf = P24.multistep 1000 ; lemma-listnf = P24.lemma-multistep 1000 }

  


  lemma-K0-CS01-K0-CS02-K0-CS01-CS02-K0=S0-CS01-K0-CS02-K0-S0-S0-S0-CS01-CS02-CS01-CS01-CCZ-iI-iI-iI-CX10-CCX0 : Rel ⊢ K0 • CS01 • K0 • CS02 • K0 • S0 • CS01 • CS02 • K0 === S0 • K0 • S0 • CS01 • K0 • CS02 • K0 • CS01 • CS01 • CS01 • CS02 • CCZ • iI • iI • iI • X0 • CX10 • CCX0
  lemma-K0-CS01-K0-CS02-K0-CS01-CS02-K0=S0-CS01-K0-CS02-K0-S0-S0-S0-CS01-CS02-CS01-CS01-CCZ-iI-iI-iI-CX10-CCX0 =
    equational K0 • CS01 • K0 • CS02 • K0 • S0 • CS01 • CS02 • K0
      by right right right lemma-CS02-K0-S0-CS01-CS02-K0=CS01-K0-S0-CS01-CS02-K0-S1-S1-S1-S2-CS01-CS02-CS02-CS02
    equals K0 • CS01 • K0 • CS01 • K0 • S0 • CS01 • CS02 • K0 • S1 • S1 • S1 • S2 • CS01 • CS02 • CS02 • CS02
      by general-assoc auto
    equals K0 • (CS01 • K0 • CS01 • K0) • S0 • CS01 • CS02 • K0 • S1 • S1 • S1 • S2 • CS01 • CS02 • CS02 • CS02
      by right left lemma-CS01-K0-CS01-K0=S0-K0-CS01-K0-CS01-S0-S0-S0
    equals K0 • (S0 • K0 • CS01 • K0 • CS01 • S0 • S0 • S0) • S0 • CS01 • CS02 • K0 • S1 • S1 • S1 • S2 • CS01 • CS02 • CS02 • CS02
      by ListNF.listnfeq' nf-spde auto
    equals K0 • (S0 • K0 • CS01 • K0 • CS02) • (CS01 • CS01 • K0) • S1 • S1 • S1 • S2 • CS01 • CS02 • CS02 • CS02
      by mvKL.general-rewrite 100 auto
    equals (S0 • K0 • X0 • S0 • S0 • S0 • CS01 • K0 • CS02 • K0 • CX10) • S1 • S1 • S1 • S2 • CS01 • CS02 • CS02 • CS02
      by ListNF.listnfeq' nf-spde auto
    equals (S0 • K0 • S0 • S1 • CS01 • CS01 • CS01 • iI ^ 3 • X0 • K0 • CS02 • K0 • CX10) • S1 • S1 • S1 • S2 • CS01 • CS02 • CS02 • CS02
      by mvKL.general-rewrite 100 auto
    equals S0 • K0 • S0 • CS01 • K0 • S1 • CX10 • iI ^ 3 • CS02 • K0 • X0 • CX10 • S1 • S1 • S1 • S2 • CS01 • CS02 • CS02 • CS02
      by right right right right right ListNF.listnfeq' nf-spde auto
    equals S0 • K0 • S0 • CS01 • K0 • S1 • CS02 • CS12 • CCZ • iI ^ 3 • CX10 • K0 • X0 • CX10 • S1 • S1 • S1 • S2 • CS01 • CS02 • CS02 • CS02
      by mvKL.general-rewrite 100 auto
    equals S0 • K0 • S0 • CS01 • K0 • CS02 • K0 • S1 • CS12 • CCX0 • iI ^ 3 • CS01 • CS01 • X0 • CX10 • S1 • S1 • S1 • S2 • CS01 • CS02 • CS02 • CS02
      by right right right right right ListNF.listnfeq' nf-spde auto
    equals S0 • K0 • S0 • CS01 • K0 • CS02 • K0 • CS01 • CS01 • CS01 • CS02 • CCZ • iI • iI • iI • X0 • CX10 • CCX0



  lemma-K0-CS02-K0-CS01-K0-S0-CS01-CS02-K0=S0-K0-S0-CS02-K0-CS01-K0-CS01-CS02-CS02-CS02-CCZ-iI-iI-iI-X0-CX20-CCX0 : Rel ⊢ K0 • CS02 • K0 • CS01 • K0 • S0 • CS01 • CS02 • K0 === S0 • K0 • S0 • CS02 • K0 • CS01 • K0 • CS01 • CS02 • CS02 • CS02 • CCZ • iI • iI • iI • X0 • CX20 • CCX0
  lemma-K0-CS02-K0-CS01-K0-S0-CS01-CS02-K0=S0-K0-S0-CS02-K0-CS01-K0-CS01-CS02-CS02-CS02-CCZ-iI-iI-iI-X0-CX20-CCX0 =
    equational K0 • CS02 • K0 • CS01 • K0 • S0 • CS01 • CS02 • K0
      by right right right lemma-CS01-K0-S0-CS01-CS02-K0=CS02-K0-S0-CS01-CS02-K0-S2-S2-S2-S1-CS01-CS02-CS01-CS01
    equals K0 • CS02 • K0 • CS02 • K0 • S0 • CS01 • CS02 • K0 • S1 • S2 • S2 • S2 • CS01 • CS01 • CS01 • CS02
      by general-assoc auto
    equals K0 • (CS02 • K0 • CS02 • K0) • S0 • CS01 • CS02 • K0 • S1 • S2 • S2 • S2 • CS01 • CS01 • CS01 • CS02
      by right left lemma-CS02-K0-CS02-K0=S0-K0-CS02-K0-CS02-S0-S0-S0
    equals K0 • (S0 • K0 • CS02 • K0 • CS02 • S0 • S0 • S0) • S0 • CS01 • CS02 • K0 • S1 • S2 • S2 • S2 • CS01 • CS01 • CS01 • CS02
      by ListNF.listnfeq' nf-spde auto
    equals K0 • (S0 • K0 • CS02 • K0 • CS01) • (CS02 • CS02 • K0) • S2 • S2 • S2 • S1 • CS01 • CS02 • CS01 • CS01
      by mvKL.general-rewrite 200 auto
    equals (S0 • K0 • X0 • S0 • S0 • S0 • CS02 • K0 • CS01 • K0 • CX20) • S2 • S2 • S2 • S1 • CS01 • CS02 • CS01 • CS01
      by ListNF.listnfeq' nf-spde auto
    equals (S0 • K0 • S0 • S2 • CS02 • CS02 • CS02 • iI ^ 3 • X0 • K0 • CS01 • K0 • CX20) • S2 • S2 • S2 • S1 • CS01 • CS02 • CS01 • CS01
      by mvKL.general-rewrite 200 auto
    equals S0 • K0 • S0 • CS02 • K0 • S2 • CX20 • iI ^ 3 • CS01 • K0 • X0 • CX20 • S2 • S2 • S2 • S1 • CS01 • CS02 • CS01 • CS01
      by right right right right right ListNF.listnfeq' nf-spde auto
    equals S0 • K0 • S0 • CS02 • K0 • S2 • CS01 • CS12 • CCZ • iI ^ 3 • CX20 • K0 • X0 • CX20 • S2 • S2 • S2 • S1 • CS01 • CS02 • CS01 • CS01
      by mvKL.general-rewrite 200 auto
    equals S0 • K0 • S0 • CS02 • K0 • CS01 • K0 • S2 • CS12 • CCX0 • iI ^ 3 • CS02 • CS02 • X0 • CX20 • S2 • S2 • S2 • S1 • CS01 • CS02 • CS01 • CS01
      by right right right right right ListNF.listnfeq' nf-spde auto
    equals S0 • K0 • S0 • CS02 • K0 • CS01 • K0 • CS01 • CS02 • CS02 • CS02 • CCZ • iI • iI • iI • X0 • CX20 • CCX0


  lemma-K0-CS01-K0-CS02-K0-S0-CS01-CS02-K0=S0-K0-S0-CS01-K0-CS02-K0-CS01-CS01-CS01-CS02-CCZ-iI-iI-iI-X0-CX10-CCX0 : Rel ⊢ K0 • CS01 • K0 • CS02 • K0 • S0 • CS01 • CS02 • K0 === S0 • K0 • S0 • CS01 • K0 • CS02 • K0 • CS01 • CS01 • CS01 • CS02 • CCZ • iI • iI • iI • X0 • CX10 • CCX0
  lemma-K0-CS01-K0-CS02-K0-S0-CS01-CS02-K0=S0-K0-S0-CS01-K0-CS02-K0-CS01-CS01-CS01-CS02-CCZ-iI-iI-iI-X0-CX10-CCX0 =
    equational K0 • CS01 • K0 • CS02 • K0 • S0 • CS01 • CS02 • K0
      by right right right lemma-CS02-K0-S0-CS01-CS02-K0=CS01-K0-S0-CS01-CS02-K0-S1-S1-S1-S2-CS01-CS02-CS02-CS02
    equals K0 • CS01 • K0 • CS01 • K0 • S0 • CS01 • CS02 • K0 • S1 • S1 • S1 • S2 • CS01 • CS02 • CS02 • CS02
      by general-assoc auto
    equals K0 • (CS01 • K0 • CS01 • K0) • S0 • CS01 • CS02 • K0 • S1 • S1 • S1 • S2 • CS01 • CS02 • CS02 • CS02
      by right left lemma-CS01-K0-CS01-K0=S0-K0-CS01-K0-CS01-S0-S0-S0
    equals K0 • (S0 • K0 • CS01 • K0 • CS01 • S0 • S0 • S0) • S0 • CS01 • CS02 • K0 • S1 • S1 • S1 • S2 • CS01 • CS02 • CS02 • CS02
      by ListNF.listnfeq' nf-spde auto
    equals K0 • (S0 • K0 • CS01 • K0 • CS02) • (CS01 • CS01 • K0) • S1 • S1 • S1 • S2 • CS01 • CS02 • CS02 • CS02
      by mvKL.general-rewrite 100 auto
    equals (S0 • K0 • X0 • S0 • S0 • S0 • CS01 • K0 • CS02 • K0 • CX10) • S1 • S1 • S1 • S2 • CS01 • CS02 • CS02 • CS02
      by ListNF.listnfeq' nf-spde auto
    equals (S0 • K0 • S0 • S1 • CS01 • CS01 • CS01 • iI ^ 3 • X0 • K0 • CS02 • K0 • CX10) • S1 • S1 • S1 • S2 • CS01 • CS02 • CS02 • CS02
      by mvKL.general-rewrite 100 auto
    equals S0 • K0 • S0 • CS01 • K0 • S1 • CX10 • iI ^ 3 • CS02 • K0 • X0 • CX10 • S1 • S1 • S1 • S2 • CS01 • CS02 • CS02 • CS02
      by right right right right right ListNF.listnfeq' nf-spde auto
    equals S0 • K0 • S0 • CS01 • K0 • S1 • CS02 • CS12 • CCZ • iI ^ 3 • CX10 • K0 • X0 • CX10 • S1 • S1 • S1 • S2 • CS01 • CS02 • CS02 • CS02
      by mvKL.general-rewrite 100 auto
    equals S0 • K0 • S0 • CS01 • K0 • CS02 • K0 • S1 • CS12 • CCX0 • iI ^ 3 • CS01 • CS01 • X0 • CX10 • S1 • S1 • S1 • S2 • CS01 • CS02 • CS02 • CS02
      by right right right right right ListNF.listnfeq' nf-spde auto
    equals S0 • K0 • S0 • CS01 • K0 • CS02 • K0 • CS01 • CS01 • CS01 • CS02 • CCZ • iI • iI • iI • X0 • CX10 • CCX0

  lemma-K0•CS02•K0•CS02 : Rel ⊢ K0 • CS02 • K0 • CS02 === S0 ^ 3 • CS02 • K0 • CS02 • K0 • S0
  lemma-K0•CS02•K0•CS02 =
    equational K0 • CS02 • K0 • CS02
      by  ListNF.listnfeq' nf-spde auto
    equals S0 ^ 3 • (S0 • K0 • CS02 • K0 • CS02 • S0 ^ 3) • S0
      by right left symm (lemma-CS02-K0-CS02-K0=S0-K0-CS02-K0-CS02-S0-S0-S0)
    equals S0 ^ 3 • (CS02 • K0 • CS02 • K0) • S0
      by general-assoc auto
     equals S0 ^ 3 • CS02 • K0 • CS02 • K0 • S0

  module mvKL0 = Step-With-Standardization (step-cong (mvKL-step)) (ListNF.listnf nf-spde) (ListNF.lemma-listnf nf-spde)

  nf-e40 : ListNF Rel
  nf-e40 = record { listnf = mvKL0.multistep 2000 ; lemma-listnf = mvKL0.lemma-multistep 2000 }

  module P24K0D0 = SemiDirect isP24 isk0spd nfp24 nf-e40 group-like p24-spde4-conj


  nf-p24k0d0 : ListNF Rel
  nf-p24k0d0 = record { listnf = P24K0D0.nfnh' ; lemma-listnf = P24K0D0.lemma-nfnh' }


  lemma-K0-CS02-K0-S0-CS01-K0-S0-CS01-CS02-K0=S0-CS02-K0-S0-CS01-K0-S1-CS01-CS01-CS01-CS02-iI-iI-iI : Rel ⊢ K0 • CS02 • K0 • S0 • CS01 • K0 • S0 • CS01 • CS02 • K0 === S0 • CS02 • K0 • S0 • CS01 • K0 • S1 • CS01 • CS01 • CS01 • CS02 • iI • iI • iI
  lemma-K0-CS02-K0-S0-CS01-K0-S0-CS01-CS02-K0=S0-CS02-K0-S0-CS01-K0-S1-CS01-CS01-CS01-CS02-iI-iI-iI =
    equational K0 • CS02 • K0 • S0 • CS01 • K0 • S0 • CS01 • CS02 • K0
      by right right right right lemma-CS01-K0-S0-CS01-CS02-K0=CS02-K0-S0-CS01-CS02-K0-S2-S2-S2-S1-CS01-CS02-CS01-CS01
    equals K0 • CS02 • K0 • S0 • CS02 • K0 • S0 • CS01 • CS02 • K0 • S1 • S2 • S2 • S2 • CS01 • CS01 • CS01 • CS02
      by  ListNF.listnfeq' nf-spde auto
    equals (K0 • CS02 • K0 • CS02) • S0 • K0 • S0 • CS01 • CS02 • K0 • S1 • S2 • S2 • S2 • CS01 • CS01 • CS01 • CS02
      by left lemma-K0•CS02•K0•CS02
    equals (S0 ^ 3 • CS02 • K0 • CS02 • K0 • S0) • S0 • K0 • S0 • CS01 • CS02 • K0 • S1 • S2 • S2 • S2 • CS01 • CS01 • CS01 • CS02
      by mvKL.general-rewrite 100 auto
    equals S0 ^ 3 • CS02 • K0 • CS02 • iI ^ 3 • X0 • S0 • CS01 • CS02 • K0 • S1 • S2 • S2 • S2 • CS01 • CS01 • CS01 • CS02
      by ListNF.listnfeq' nf-spde auto
    equals S0 ^ 3 • CS02 • K0 • S0 • S0 • S0 • S1 • S2 • CS01 • CS01 • CS01 • X0 • K0 • S1 • S2 • S2 • S2 • CS01 • CS01 • CS01 • CS02
      by  ListNF.listnfeq' nf-p24k0d0 auto
    equals S0 • CS02 • K0 • X0 • S0 • CS01 • K0 • X0 • S1 • S2 • CX10 • S0 • S0 • S1 • S2 • S2 • S2 • CS01 • CS01 • CS01 • CS02
      by ListNF.listnfeq' nf-spde auto
    equals S0 • CS02 • K0 • S0 • S0 • S0 • S1 • CS01 • CS01 • CS01 • iI • X0 • K0 • X0 • S1 • S2 • CX10 • S0 • S0 • S1 • S2 • S2 • S2 • CS01 • CS01 • CS01 • CS02
      by  right right right right ListNF.listnfeq' nf-p24k0d0 auto
    equals S0 • CS02 • K0 • S0 • CS01 • K0 • X0 • S1  • CX10 • iI • S0 • S0 • X0 • S1 • S2 • CX10 • S0 • S0 • S1 • S2 • S2 • S2 • CS01 • CS01 • CS01 • CS02
      by  right right right right ListNF.listnfeq' nf-spde auto
    equals S0 • CS02 • K0 • S0 • CS01 • K0 • S1 • CS01 • CS01 • CS01 • CS02 • iI • iI • iI


  lemma-K0-CS01-K0-CS02-K0-CS01-CS02-K0=S0-CS01-K0-CS02-K0-S0-S0-S0-CS01-CS01-CS01-CS02-CCZ-iI-iI-iI-CX10-CCX0 : Rel ⊢ K0 • CS01 • K0 • CS02 • K0 • CS01 • CS02 • K0 === S0 • CS01 • K0 • CS02 • K0 • S0 • S0 • S0 • CS01 • CS01 • CS01 • CS02 • CCZ • iI • iI • iI • CX10 • CCX0
  lemma-K0-CS01-K0-CS02-K0-CS01-CS02-K0=S0-CS01-K0-CS02-K0-S0-S0-S0-CS01-CS01-CS01-CS02-CCZ-iI-iI-iI-CX10-CCX0 =
    equational K0 • CS01 • K0 • CS02 • K0 • CS01 • CS02 • K0
      by ListNF.listnfeq' nf-p24k0d0 auto
    equals (K0 • CS01 • K0 • CS01 ^ 3) • CS01 • CS02 • K0 • CS01 • CS02 • K0
      by right lemma-CS01-CS02-K0-CS01-CS02-K0=S0-K0-CS01-CS02-K0-S0-S0-S0-CS01-CS02-CS12-CCZ
    equals (K0 • CS01 • K0 • CS01 ^ 3) • S0 • K0 • CS01 • CS02 • K0 • S0 • S0 • S0 • CS01 • CS02 • CS12 • CCZ
      by ListNF.listnfeq' nf-p24k0d0 auto
    equals S0 • CS01 • K0 • CS02 • K0 • S0 • S0 • S0 • CS01 • CS01 • CS01 • CS02 • CCZ • iI • iI • iI • CX10 • CCX0


  lemma-K0-S0-CS01-K0-S0-CS02-K0-S0-CS01-CS02-K0-S0-CS01-CS02-K0=S0-K0-CS01-K0-CS02-K0-S0-S1-S2-CS01-CS01-CCZ-iI-iI-iI-X0-CX10-CCX0 : Rel ⊢ K0 • S0 • CS01 • K0 • S0 • CS02 • K0 • S0 • CS01 • CS02 • K0 • S0 • CS01 • CS02 • K0 === S0 • K0 • CS01 • K0 • CS02 • K0 • S0 • S1 • S2 • CS01 • CS01 • CCZ • iI • iI • iI • X0 • CX10 • CCX0
  lemma-K0-S0-CS01-K0-S0-CS02-K0-S0-CS01-CS02-K0-S0-CS01-CS02-K0=S0-K0-CS01-K0-CS02-K0-S0-S1-S2-CS01-CS01-CCZ-iI-iI-iI-X0-CX10-CCX0 =
    equational K0 • S0 • CS01 • K0 • S0 • CS02 • K0 • S0 • CS01 • CS02 • K0 • S0 • CS01 • CS02 • K0
      by general-assoc auto
    equals (K0 • S0 • CS01 • K0 • S0) • (CS02 • K0 • S0 • CS01 • CS02 • K0) • S0 • CS01 • CS02 • K0
      by right left lemma-CS02-K0-S0-CS01-CS02-K0=CS01-K0-S0-CS01-CS02-K0-S1-S1-S1-S2-CS01-CS02-CS02-CS02
    equals (K0 • S0 • CS01 • K0 • S0) • (CS01 • K0 • S0 • CS01 • CS02 • K0 • S1 • S1 • S1 • S2 • CS01 • CS02 • CS02 • CS02) • S0 • CS01 • CS02 • K0
      by general-assoc auto
    equals (K0 • S0 • CS01 • K0 • S0 • CS01 • K0 • S0 • CS01 • CS02 • K0) • S1 • S1 • S1 • S2 • CS01 • CS02 • CS02 • CS02 • S0 • CS01 • CS02 • K0
      by ListNF.listnfeq' nf-p24k0d0 auto
    equals (K0 • S0 • CS01 • K0 • S0 • CS02 ^ 3) • (CS01 • CS02 • K0 • CS01 • CS02 • K0) • X0 • X0 • S0 • S0 • S0 • S1 • S1 • S1 • S2 • CX10
      by right left lemma-CS01-CS02-K0-CS01-CS02-K0=S0-K0-CS01-CS02-K0-S0-S0-S0-CS01-CS02-CS12-CCZ
    equals (K0 • S0 • CS01 • K0 • S0 • CS02 ^ 3) • (S0 • K0 • CS01 • CS02 • K0 • S0 • S0 • S0 • CS01 • CS02 • CS12 • CCZ) • X0 • X0 • S0 • S0 • S0 • S1 • S1 • S1 • S2 • CX10
      by ListNF.listnfeq' nf-p24k0d0 auto
    equals (K0 • S0 • CS01 • K0 • CS02 ^ 3) • (K0 • X0 • CS01 • CS02 • K0 • S0 • S0 • S0 • CS01 • CS02 • CS12 • CCZ) • X0 • X0 • S0 • S0 • S0 • S1 • S1 • S1 • S2 • CX10
      by ListNF.listnfeq' nf-p24k0d0 auto
    equals (K0 • S0 • CS01 • K0 • CS01 ^ 3) • (CS01 • CS02 • K0 • CS01 • CS02 • K0) • S1 • S2 • CS01 • CS01 • CS01 • CS02 • CS02 • CS02 • CS12 • CS12 • CS12 • CCX0
      by right left lemma-CS01-CS02-K0-CS01-CS02-K0=S0-K0-CS01-CS02-K0-S0-S0-S0-CS01-CS02-CS12-CCZ
    equals (K0 • S0 • CS01 • K0 • CS01 ^ 3) • (S0 • K0 • CS01 • CS02 • K0 • S0 • S0 • S0 • CS01 • CS02 • CS12 • CCZ) • S1 • S2 • CS01 • CS01 • CS01 • CS02 • CS02 • CS02 • CS12 • CS12 • CS12 • CCX0
      by ListNF.listnfeq' nf-p24k0d0 auto
    equals S0 • K0 • CS01 • K0 • CS02 • K0 • S0 • S1 • S2 • CS01 • CS01 • CCZ • iI • iI • iI • X0 • CX10 • CCX0



  lemma-K0-S0-CS02-K0-S0-CS01-K0-S0-CS01-CS02-K0=S0-K0-CS02-K0-S0-CS01-K0-CS01-CS02-CS02-CS02-CCZ-X0-CX20-CCX0 : Rel ⊢ K0 • S0 • CS02 • K0 • S0 • CS01 • K0 • S0 • CS01 • CS02 • K0 === S0 • K0 • CS02 • K0 • S0 • CS01 • K0 • CS01 • CS02 • CS02 • CS02 • CCZ • X0 • CX20 • CCX0
  lemma-K0-S0-CS02-K0-S0-CS01-K0-S0-CS01-CS02-K0=S0-K0-CS02-K0-S0-CS01-K0-CS01-CS02-CS02-CS02-CCZ-X0-CX20-CCX0 =
    equational K0 • S0 • CS02 • K0 • S0 • CS01 • K0 • S0 • CS01 • CS02 • K0
      by right right right right right lemma-CS01-K0-S0-CS01-CS02-K0=CS02-K0-S0-CS01-CS02-K0-S2-S2-S2-S1-CS01-CS02-CS01-CS01
    equals K0 • S0 • CS02 • K0 • S0 • CS02 • K0 • S0 • CS01 • CS02 • K0 • S1 • S2 • S2 • S2 • CS01 • CS01 • CS01 • CS02
      by ListNF.listnfeq' nf-p24k0d0 auto
    equals S0 • K0 • CS02 • K0 • S0 • CS01 • K0 • CS01 • CS02 • CS02 • CS02 • CCZ • X0 • CX20 • CCX0

  lemma-K0-CS02-K0-CS01-K0-CS01-CS02-K0=S0-CS02-K0-CS01-K0-S0-S0-S0-CS01-CS02-CS02-CS02-CCZ-iI-iI-iI-CX20-CCX0 : Rel ⊢  K0 • CS02 • K0 • CS01 • K0 • CS01 • CS02 • K0 === S0 • CS02 • K0 • CS01 • K0 • S0 • S0 • S0 • CS01 • CS02 • CS02 • CS02 • CCZ • iI • iI • iI • CX20 • CCX0
  lemma-K0-CS02-K0-CS01-K0-CS01-CS02-K0=S0-CS02-K0-CS01-K0-S0-S0-S0-CS01-CS02-CS02-CS02-CCZ-iI-iI-iI-CX20-CCX0 =
    equational K0 • CS02 • K0 • CS01 • K0 • CS01 • CS02 • K0
      by ListNF.listnfeq' nf-p24k0d0 auto
    equals (K0 • CS02 • K0 • CS02 ^ 3) • CS01 • CS02 • K0 • CS01 • CS02 • K0
      by right lemma-CS01-CS02-K0-CS01-CS02-K0=S0-K0-CS01-CS02-K0-S0-S0-S0-CS01-CS02-CS12-CCZ
    equals (K0 • CS02 • K0 • CS02 ^ 3) • S0 • K0 • CS01 • CS02 • K0 • S0 • S0 • S0 • CS01 • CS02 • CS12 • CCZ
      by  ListNF.listnfeq' nf-p24k0d0 auto
    equals S0 • CS02 • K0 • CS01 • K0 • S0 • S0 • S0 • CS01 • CS02 • CS02 • CS02 • CCZ • iI • iI • iI • CX20 • CCX0

  lemma-K0-CS01-K0-CS02-K0-S0-CS01-K0-S0-CS02-K0=S0-K0-S0-CS01-K0-CS02-K0-S0-CS01-K0-S0-S0-S1-S2-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CS12-CCZ-iI-iI-X0 : Rel ⊢ K0 • CS01 • K0 • CS02 • K0 • S0 • CS01 • K0 • S0 • CS02 • K0 === S0 • K0 • S0 • CS01 • K0 • CS02 • K0 • S0 • CS01 • K0 • S0 • S0 • S1 • S2 • CS01 • CS01 • CS02 • CS02 • CS02 • CS12 • CS12 • CS12 • CCZ • iI • iI • X0
  lemma-K0-CS01-K0-CS02-K0-S0-CS01-K0-S0-CS02-K0=S0-K0-S0-CS01-K0-CS02-K0-S0-CS01-K0-S0-S0-S1-S2-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CS12-CCZ-iI-iI-X0 =
    equational K0 • CS01 • K0 • CS02 • K0 • S0 • CS01 • K0 • S0 • CS02 • K0
      by general-assoc auto
    equals (K0 • CS01 • K0 • CS02 • K0 • S0) • CS01 • K0 • S0 • CS02 • K0
      by right ListNF.listnfeq' nf-p24k0d0 auto
    equals (K0 • CS01 • K0 • CS02 • K0 • S0) • S0 • K0 • CS01 • (CS01 • K0 • S0 • CS01 • CS02 • K0 • S1 • S1 • S1 • S2 • CS01 • CS02 • CS02 • CS02) • S0 • CS01 • K0 • S0 • S0 • S1 • S1 • S1 • CS02 • CS02 • CS02 • CS12 • CS12 • CS12 • CCZ • X0
      by ListNF.listnfeq' nf-p24k0d0 auto
    equals K0 • CS01 • K0 • (CS02 • K0 • S0 • CS01 • CS02 • K0) • X0 • S1 • S1 • CS12 • CCX0 • CS01 • CS01 • iI ^ 3 • S1 • S1 • S1 • S2 • CS01 • CS02 • CS02 • CS02 • S0 • CS01 • K0 • S0 • S0 • S1 • S1 • S1 • CS02 • CS02 • CS02 • CS12 • CS12 • CS12 • CCZ • X0
      by right right right left lemma-CS02-K0-S0-CS01-CS02-K0=CS01-K0-S0-CS01-CS02-K0-S1-S1-S1-S2-CS01-CS02-CS02-CS02
    equals K0 • CS01 • K0 • (CS01 • K0 • S0 • CS01 • CS02 • K0 • S1 • S1 • S1 • S2 • CS01 • CS02 • CS02 • CS02) • X0 • S1 • S1 • CS12 • CCX0 • CS01 • CS01 • iI ^ 3 • S1 • S1 • S1 • S2 • CS01 • CS02 • CS02 • CS02 • S0 • CS01 • K0 • S0 • S0 • S1 • S1 • S1 • CS02 • CS02 • CS02 • CS12 • CS12 • CS12 • CCZ • X0
      by ListNF.listnfeq' nf-p24k0d0 auto
    equals S0 • K0 • S0 • CS01 • K0 • CS02 • K0 • S0 • CS01 • K0 • S0 • S0 • S1 • S2 • CS01 • CS01 • CS02 • CS02 • CS02 • CS12 • CS12 • CS12 • CCZ • iI • iI • X0

  lemma-CS02-K0-S0-CS01-K0-CS02-K0=S0-CS01-K0-CS02-K0-S0-CS01-K0-S0-S0-S0-S1-S1-S1-S2-S2-S2-CS01-CS01-CS01-CS02-CS12-iI-X0-CX10-CX20-CCX0 : Rel ⊢ CS02 • K0 • S0 • CS01 • K0 • CS02 • K0 === S0 • CS01 • K0 • CS02 • K0 • S0 • CS01 • K0 • S0 • S0 • S0 • S1 • S1 • S1 • S2 • S2 • S2 • CS01 • CS01 • CS01 • CS02 • CS12 • iI • X0 • CX10 • CX20 • CCX0
  lemma-CS02-K0-S0-CS01-K0-CS02-K0=S0-CS01-K0-CS02-K0-S0-CS01-K0-S0-S0-S0-S1-S1-S1-S2-S2-S2-CS01-CS01-CS01-CS02-CS12-iI-X0-CX10-CX20-CCX0 =
    equational CS02 • K0 • S0 • CS01 • K0 • CS02 • K0
      by ListNF.listnfeq' nf-p24k0d0 auto
    equals CS02 • (K0 • S0 • CS01 • K0 • S1 • CS01 • CS01 • CS01) • CS01 • CS02 • K0 • S1 • S1 • S1
      by right left symm (lemma-CS01-K0-S0-CS01-K0=K0-S0-CS01-K0-S1-CS01-CS01-CS01)
    equals CS02 • (CS01 • K0 • S0 • CS01 • K0) • CS01 • CS02 • K0 • S1 • S1 • S1
      by ListNF.listnfeq' nf-p24k0d0 auto
    equals (CS02 • CS01 • K0 • CS01 ^ 3) • (S0 • K0 • CS01 • CS02 • K0 • S0 • S0 • S0 • CS01 • CS02 • CS12 • CCZ) • S0 • S1 • S1 • CS01 • CS02 • CS02 • CS02 • CS12 • CS12 • CCZ • CX10 • CCX0
      by right left symm (lemma-CS01-CS02-K0-CS01-CS02-K0=S0-K0-CS01-CS02-K0-S0-S0-S0-CS01-CS02-CS12-CCZ)
    equals (CS02 • CS01 •  K0 • CS01 ^ 3) • (CS01 • CS02 • K0 • CS01 • CS02 • K0) • S0 • S1 • S1 • CS01 • CS02 • CS02 • CS02 • CS12 • CS12 • CCZ • CX10 • CCX0
      by ListNF.listnfeq' nf-p24k0d0 auto
    equals (S0 • CS01 • CS02 ^ 3) • (S0 • K0 • CS02 • K0 • CS02 • S0 • S0 • S0) • S0 • CS01 • K0 • S0 • S0 • S0 • S1 • S1 • S1 • S2 • S2 • S2 • CS01 • CS01 • CS01 • CS02 • CS12 • iI • X0 • CX10 • CX20 • CCX0
      by right left symm (lemma-CS02-K0-CS02-K0=S0-K0-CS02-K0-CS02-S0-S0-S0)
    equals (S0 • CS01 • CS02 ^ 3) • (CS02 • K0 • CS02 • K0) • S0 • CS01 • K0 • S0 • S0 • S0 • S1 • S1 • S1 • S2 • S2 • S2 • CS01 • CS01 • CS01 • CS02 • CS12 • iI • X0 • CX10 • CX20 • CCX0
      by ListNF.listnfeq' nf-spde auto
    equals S0 • CS01 • K0 • CS02 • K0 • S0 • CS01 • K0 • S0 • S0 • S0 • S1 • S1 • S1 • S2 • S2 • S2 • CS01 • CS01 • CS01 • CS02 • CS12 • iI • X0 • CX10 • CX20 • CCX0


  lemma-K0-S0-CS02-K0-S0-CS01-K0-CS02-K0-CS01-K0=S0-K0-S0-CS01-K0-CS02-K0-S0-CS01-K0-S0-S0-S1-S1-S2-CS02-CS02-CS02-CS12-CS12-CS12-CCZ-iI-iI-X0 : Rel ⊢ K0 • S0 • CS02 • K0 • S0 • CS01 • K0 • CS02 • K0 • CS01 • K0 === S0 • K0 • S0 • CS01 • K0 • CS02 • K0 • S0 • CS01 • K0 • S0 • S0 • S1 • S1 • S2 • CS02 • CS02 • CS02 • CS12 • CS12 • CS12 • CCZ • iI • iI • X0
  lemma-K0-S0-CS02-K0-S0-CS01-K0-CS02-K0-CS01-K0=S0-K0-S0-CS01-K0-CS02-K0-S0-CS01-K0-S0-S0-S1-S1-S2-CS02-CS02-CS02-CS12-CS12-CS12-CCZ-iI-iI-X0 =
    equational K0 • S0 • CS02 • K0 • S0 • CS01 • K0 • CS02 • K0 • CS01 • K0
      by ListNF.listnfeq' nf-p24k0d0 auto
    equals (K0 • S0 • CS02 • K0 • S0) • (CS01 • K0 • CS02 • K0 • CS01 • K0 • S1 • CS01 • CS01 • CS01 • CS02 • CS02 • CS02 • CS12 • CS12 • CS12 • CCZ • CX10 • CX20) • CX20 • CX10 • CCZ • CS12 • CS02 • CS01 • S1 • S1 • S1
      by right left symm (lemma-CS02-K0-CS01-K0-CS02-K0=CS01-K0-CS02-K0-CS01-K0-S1-CS01-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CS12-CCZ-CX10-CX20)
    equals (K0 • S0 • CS02 • K0 • S0) • (CS02 • K0 • CS01 • K0 • CS02 • K0) • CX20 • CX10 • CCZ • CS12 • CS02 • CS01 • S1 • S1 • S1
      by ListNF.listnfeq' nf-p24k0d0 auto
    equals S0 • K0 • (CS02 • K0 • S0 • CS01 • K0 • CS02 • K0) • S0 • S2 • S2 • S2 • CS01 • CS01 • CS01 • CS12 • CX10 • CX20 • CCX0
      by right right left (lemma-CS02-K0-S0-CS01-K0-CS02-K0=S0-CS01-K0-CS02-K0-S0-CS01-K0-S0-S0-S0-S1-S1-S1-S2-S2-S2-CS01-CS01-CS01-CS02-CS12-iI-X0-CX10-CX20-CCX0)
    equals S0 • K0 • (S0 • CS01 • K0 • CS02 • K0 • S0 • CS01 • K0 • S0 • S0 • S0 • S1 • S1 • S1 • S2 • S2 • S2 • CS01 • CS01 • CS01 • CS02 • CS12 • iI • X0 • CX10 • CX20 • CCX0) • S0 • S2 • S2 • S2 • CS01 • CS01 • CS01 • CS12 • CX10 • CX20 • CCX0
      by ListNF.listnfeq' nf-p24k0d0 auto
    equals S0 • K0 • S0 • CS01 • K0 • CS02 • K0 • S0 • CS01 • K0 • S0 • S0 • S1 • S1 • S2 • CS02 • CS02 • CS02 • CS12 • CS12 • CS12 • CCZ • iI • iI • X0
      by ListNF.listnfeq' nf-p24k0d0 auto
    equals S0 • K0 • S0 • CS01 • K0 • CS02 • K0 • S0 • CS01 • K0 • S0 • S0 • S1 • S1 • S2 • CS02 • CS02 • CS02 • CS12 • CS12 • CS12 • CCZ • iI • iI • X0


  lemma-K0-CS01-K0-CS02-K0-CS01-K0-S0-CS02-K0=S0-CS01-K0-CS02-K0-CS01-K0-S1-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CS12-CCZ-iI-iI-iI-CX20 : Rel ⊢ K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • S0 • CS02 • K0 === S0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • S1 • CS01 • CS01 • CS02 • CS02 • CS02 • CS12 • CS12 • CS12 • CCZ • iI • iI • iI • CX20
  lemma-K0-CS01-K0-CS02-K0-CS01-K0-S0-CS02-K0=S0-CS01-K0-CS02-K0-CS01-K0-S1-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CS12-CCZ-iI-iI-iI-CX20 =
    equational K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • S0 • CS02 • K0
      by ListNF.listnfeq' nf-spde auto
    equals (K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CS02) • S0 • K0
      by left (lemma-K0-CS01-K0-CS02-K0-CS01-K0-CS02=S0-CS01-K0-CS02-K0-CS01-K0-CS02-K0-S0-S0-S0-S2-CS01-CS01-CCZ-CX10-CX20-CCX0)
    equals (S0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CS02 • K0 • S0 • S0 • S0 • S2 • CS01 • CS01 • CCZ • CX10 • CX20 • CCX0) • S0 • K0
      by ListNF.listnfeq' nf-p24k0d0 auto
    equals S0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • S1 • CS01 • CS01 • CS02 • CS02 • CS02 • CS12 • CS12 • CS12 • CCZ • iI • iI • iI • CX20



  lemma-nice2 : Rel ⊢ CS01 • K0 • S0 • CS02 • K0 • CS01 • CS02 • K0 === S0 • K0 • CS01 • K0 • S0 • CS02 • K0 • S0 • S0 • S0 • S1 • S1 • S1 • CS01 • CS02 • CS02 • CS02 • CS12 • iI • X0 • CX10 • CX20 • CCX0
  lemma-nice2 =
    equational CS01 • K0 • S0 • CS02 • K0 • CS01 • CS02 • K0
      by ListNF.listnfeq' nf-spde auto
    equals (CS01 • K0 • S0 • CS01 ^ 3) • CS01 • CS02 • K0 • CS01 • CS02 • K0
      by right lemma-CS01-CS02-K0-CS01-CS02-K0=S0-K0-CS01-CS02-K0-S0-S0-S0-CS01-CS02-CS12-CCZ
    equals (CS01 • K0 • S0 • CS01 ^ 3) • S0 • K0 • CS01 • CS02 • K0 • S0 • S0 • S0 • CS01 • CS02 • CS12 • CCZ
      by ListNF.listnfeq' nf-p24k0d0 auto
    equals S0 • K0 • CS01 • K0 • S0 • CS02 • K0 • S0 • S0 • S0 • S1 • S1 • S1 • CS01 • CS02 • CS02 • CS02 • CS12 • iI • X0 • CX10 • CX20 • CCX0

  lemma-nice3 : Rel ⊢ CS01 • K0 • S0 • CS02 • K0 • CS01 • K0 • S0 • CS02 • K0 === S0 • K0 • CS01 • K0 • S0 • CS02 • K0 • CS01 • K0 • S0 • S0 • CS01 • CS01 • CS02 • CS02 • CS02 • CCZ • X0 • CX10 • CX20 • CCX0
  lemma-nice3 =
    equational CS01 • K0 • S0 • CS02 • K0 • CS01 • K0 • S0 • CS02 • K0
      by ListNF.listnfeq' nf-p24k0d0 auto
    equals (CS01 • K0 • S0 • CS02 • K0 • CS01 • K0 • S0) • (CS02 • K0 • CS02 • K0) • CX20 • iI • K0 • CS02
      by right left lemma-CS02-K0-CS02-K0=S0-K0-CS02-K0-CS02-S0-S0-S0
    equals (CS01 • K0 • S0 • CS02 • K0 • CS01 • K0 • S0) • (S0 • K0 • CS02 • K0 • CS02 • S0 • S0 • S0) • CX20 • iI • K0 • CS02
      by ListNF.listnfeq' nf-p24k0d0 auto
    equals (CS01 • K0 • S0 • CS02 • K0 • CS01 • CS02 • K0) • S0 • S2 • S2 • S2 • CS02 • K0 • CS02
      by left lemma-nice2
    equals (S0 • K0 • CS01 • K0 • S0 • CS02 • K0 • S0 • S0 • S0 • S1 • S1 • S1 • CS01 • CS02 • CS02 • CS02 • CS12 • iI • X0 • CX10 • CX20 • CCX0) • S0 • S2 • S2 • S2 • CS02 • K0 • CS02
      by ListNF.listnfeq' nf-p24k0d0 auto
    equals S0 • K0 • CS01 • K0 • S0 • CS02 • K0 • CS01 • X0 • CX10 • CX20 • CCX0 • S0 • S0 • CS01 • CS01 • CS02 • CS02 • CCZ • K0 • CS02
      by ListNF.listnfeq' nf-p24k0d0 auto
    equals S0 • K0 • CS01 • K0 • S0 • CS02 • K0 • CS01 • K0 • S0 • S0 • CS01 • CS01 • CS02 • CS02 • CS02 • CCZ • X0 • CX10 • CX20 • CCX0



  lemma-CS02-K0-CS01-K0-CS02-K0-CS01-K0-CS02-K0-CS01-K0=K0-CS01-K0-CS02-K0-CS01-K0-CS02-K0-CS01-K0-CS02 : Rel ⊢ CS02 • K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 === K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CS02
  lemma-CS02-K0-CS01-K0-CS02-K0-CS01-K0-CS02-K0-CS01-K0=K0-CS01-K0-CS02-K0-CS01-K0-CS02-K0-CS01-K0-CS02 =
    equational CS02 • K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CS02 • K0 • CS01 • K0
      by general-assoc auto
    equals CS02 • (K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CS02) • K0 • CS01 • K0
      by right left (lemma-K0-CS01-K0-CS02-K0-CS01-K0-CS02=S0-CS01-K0-CS02-K0-CS01-K0-CS02-K0-S0-S0-S0-S2-CS01-CS01-CCZ-CX10-CX20-CCX0)
    equals CS02 • (S0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CS02 • K0 • S0 • S0 • S0 • S2 • CS01 • CS01 • CCZ • CX10 • CX20 • CCX0) • K0 • CS01 • K0
      by general-assoc auto
    equals (CS02 • S0 • CS01 • K0 • CS02) • K0 • CS01 • K0 • CS02 • K0 • S0 • S0 • S0 • S2 • CS01 • CS01 • CCZ • CX10 • CX20 • CCX0 • K0 • CS01 • K0
      by ListNF.listnfeq' nf-p24k0d0 auto
    equals (CS01 • K0 • CS02 • K0 • S0 • CS01 • K0 • S0) • (CS02 • K0 • S0 • CS01 • CS02 • K0) • S1 • S1 • S1 • S2 • S2 • CS01 • CS01 • CS02 • CS02 • CS12 • CCZ • iI • iI • iI • CX20
      by right left lemma-CS02-K0-S0-CS01-CS02-K0=CS01-K0-S0-CS01-CS02-K0-S1-S1-S1-S2-CS01-CS02-CS02-CS02
    equals (CS01 • K0 • CS02 • K0 • S0 • CS01 • K0 • S0) • (CS01 • K0 • S0 • CS01 • CS02 • K0 • S1 • S1 • S1 • S2 • CS01 • CS02 • CS02 • CS02) • S1 • S1 • S1 • S2 • S2 • CS01 • CS01 • CS02 • CS02 • CS12 • CCZ • iI • iI • iI • CX20
      by ListNF.listnfeq' nf-p24k0d0 auto
    equals (CS01 • K0 • S0 • CS02 • K0 • CS01 • K0 • S0 • CS02 • K0) • S1 • S1 • S1 • CS01 • CS02 • CS02 • CS02 • CS12 • iI • iI • iI • X0 • CX10 • CX20 • CCX0
      by left lemma-nice3
    equals (S0 • K0 • CS01 • K0 • S0 • CS02 • K0 • CS01 • K0 • S0 • S0 • CS01 • CS01 • CS02 • CS02 • CS02 • CCZ • X0 • CX10 • CX20 • CCX0) • S1 • S1 • S1 • CS01 • CS02 • CS02 • CS02 • CS12 • iI • iI • iI • X0 • CX10 • CX20 • CCX0
      by ListNF.listnfeq' nf-p24k0d0 auto
    equals S0 • K0 • CS01 • K0 • S0 • CS02 • K0 • CS01 • K0 • S0 • S0 • S1 • S1 • S1 • CS01 • CS01 • CS01 • CS02 • CS02 • CS12 • CCZ • iI • iI • iI
      by ListNF.listnfeq' nf-p24k0d0 auto
    equals (S0 • K0 • S0 • CS01 • K0) • (S0 • K0 • CS02 • K0 • CS02 • S0 • S0 • S0) • S0 • CS01 • CS02 • K0 • S1 • S2 • S2 • S2 • CS01 • CS01 • CS01 • CS02 • S1 • S1 • S2 • S2 • S2 • CS01 • CS01 • CS02 • iI • iI • iI • CX10 • CX20
      by right left symm (lemma-CS02-K0-CS02-K0=S0-K0-CS02-K0-CS02-S0-S0-S0)
    equals (S0 • K0 • S0 • CS01 • K0) • (CS02 • K0 • CS02 • K0) • S0 • CS01 • CS02 • K0 • S1 • S2 • S2 • S2 • CS01 • CS01 • CS01 • CS02 • S1 • S1 • S2 • S2 • S2 • CS01 • CS01 • CS02 • iI • iI • iI • CX10 • CX20
      by general-assoc auto
    equals (S0 • K0 • S0 • CS01 • K0 • CS02 • K0) • (CS02 • K0 • S0 • CS01 • CS02 • K0 • S1 • S2 • S2 • S2 • CS01 • CS01 • CS01 • CS02) • S1 • S1 • S2 • S2 • S2 • CS01 • CS01 • CS02 • iI • iI • iI • CX10 • CX20
      by right left symm lemma-CS01-K0-S0-CS01-CS02-K0=CS02-K0-S0-CS01-CS02-K0-S2-S2-S2-S1-CS01-CS02-CS01-CS01
    equals (S0 • K0 • S0 • CS01 • K0 • CS02 • K0) • (CS01 • K0 • S0 • CS01 • CS02 • K0) • S1 • S1 • S2 • S2 • S2 • CS01 • CS01 • CS02 • iI • iI • iI • CX10 • CX20
      by ListNF.listnfeq' nf-p24k0d0 auto
    equals (K0 • CS01 • K0 • CS02) • S0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CS02 • K0 • S0 • S0 • S0 • S2 • CS01 • CS01 • CCZ • CX10 • CX20 • CCX0
      by right symm (lemma-K0-CS01-K0-CS02-K0-CS01-K0-CS02=S0-CS01-K0-CS02-K0-CS01-K0-CS02-K0-S0-S0-S0-S2-CS01-CS01-CCZ-CX10-CX20-CCX0)
    equals (K0 • CS01 • K0 • CS02) • (K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CS02)
      by general-assoc auto
    equals K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CS02 • K0 • CS01 • K0 • CS02


  mvKL2-step : Step-Function Gate Rel
  mvKL2-step (CS02-gen ∷ K0-gen ∷ CS01-gen ∷ K0-gen ∷ CS02-gen ∷ K0-gen ∷ CS01-gen ∷ K0-gen ∷ CS02-gen ∷ K0-gen ∷ CS01-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ CS01-gen ∷ K0-gen ∷ CS02-gen ∷ K0-gen ∷ CS01-gen ∷ K0-gen ∷ CS02-gen ∷ K0-gen ∷ CS01-gen ∷ K0-gen ∷ CS02-gen ∷ xs , at-head (lemma-CS02-K0-CS01-K0-CS02-K0-CS01-K0-CS02-K0-CS01-K0=K0-CS01-K0-CS02-K0-CS01-K0-CS02-K0-CS01-K0-CS02))

  mvKL2-step (CS02-gen ∷ K0-gen ∷ CS01-gen ∷ K0-gen ∷ CS02-gen ∷ K0-gen ∷ xs) = just (CS01-gen ∷ K0-gen ∷ CS02-gen ∷ K0-gen ∷ CS01-gen ∷ K0-gen ∷ S1-gen ∷ CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ CS02-gen ∷ CS02-gen ∷ CS02-gen ∷ CS12-gen ∷ CS12-gen ∷ CS12-gen ∷ CCZ-gen ∷ CX10-gen ∷ CX20-gen ∷ xs , at-head (lemma-CS02-K0-CS01-K0-CS02-K0=CS01-K0-CS02-K0-CS01-K0-S1-CS01-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CS12-CCZ-CX10-CX20))
  mvKL2-step (K0-gen ∷ CS01-gen ∷ K0-gen ∷ CS02-gen ∷ K0-gen ∷ CS01-gen ∷ K0-gen ∷ S0-gen ∷ CS02-gen ∷ K0-gen ∷ xs) = just (S0-gen ∷ CS01-gen ∷ K0-gen ∷ CS02-gen ∷ K0-gen ∷ CS01-gen ∷ K0-gen ∷ S1-gen ∷ CS01-gen ∷ CS01-gen ∷ CS02-gen ∷ CS02-gen ∷ CS02-gen ∷ CS12-gen ∷ CS12-gen ∷ CS12-gen ∷ CCZ-gen ∷ iI-gen ∷ iI-gen ∷ iI-gen ∷ CX20-gen ∷ xs , at-head (lemma-K0-CS01-K0-CS02-K0-CS01-K0-S0-CS02-K0=S0-CS01-K0-CS02-K0-CS01-K0-S1-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CS12-CCZ-iI-iI-iI-CX20))
  mvKL2-step (K0-gen ∷ S0-gen ∷ CS01-gen ∷ K0-gen ∷ S0-gen ∷ CS02-gen ∷ K0-gen ∷ S0-gen ∷ CS01-gen ∷ CS02-gen ∷ K0-gen ∷ S0-gen ∷ CS01-gen ∷ CS02-gen ∷ K0-gen ∷ xs) = just (S0-gen ∷ K0-gen ∷ CS01-gen ∷ K0-gen ∷ CS02-gen ∷ K0-gen ∷ S0-gen ∷ S1-gen ∷ S2-gen ∷ CS01-gen ∷ CS01-gen ∷ CCZ-gen ∷ iI-gen ∷ iI-gen ∷ iI-gen ∷ X0-gen ∷ CX10-gen ∷ CCX0-gen ∷ xs , at-head (lemma-K0-S0-CS01-K0-S0-CS02-K0-S0-CS01-CS02-K0-S0-CS01-CS02-K0=S0-K0-CS01-K0-CS02-K0-S0-S1-S2-CS01-CS01-CCZ-iI-iI-iI-X0-CX10-CCX0))
  mvKL2-step (K0-gen ∷ CS01-gen ∷ K0-gen ∷ CS02-gen ∷ K0-gen ∷ CS01-gen ∷ CS02-gen ∷ K0-gen ∷ xs) = just (S0-gen ∷ CS01-gen ∷ K0-gen ∷ CS02-gen ∷ K0-gen ∷ S0-gen ∷ S0-gen ∷ S0-gen ∷ CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ CS02-gen ∷ CCZ-gen ∷ iI-gen ∷ iI-gen ∷ iI-gen ∷ CX10-gen ∷ CCX0-gen ∷ xs , at-head (lemma-K0-CS01-K0-CS02-K0-CS01-CS02-K0=S0-CS01-K0-CS02-K0-S0-S0-S0-CS01-CS01-CS01-CS02-CCZ-iI-iI-iI-CX10-CCX0))

  mvKL2-step (K0-gen ∷ CS01-gen ∷ K0-gen ∷ CS02-gen ∷ K0-gen ∷ S0-gen ∷ CS01-gen ∷ K0-gen ∷ S0-gen ∷ CS02-gen ∷ K0-gen ∷ xs) = just (S0-gen ∷ K0-gen ∷ S0-gen ∷ CS01-gen ∷ K0-gen ∷ CS02-gen ∷ K0-gen ∷ S0-gen ∷ CS01-gen ∷ K0-gen ∷ S0-gen ∷ S0-gen ∷ S1-gen ∷ S2-gen ∷ CS01-gen ∷ CS01-gen ∷ CS02-gen ∷ CS02-gen ∷ CS02-gen ∷ CS12-gen ∷ CS12-gen ∷ CS12-gen ∷ CCZ-gen ∷ iI-gen ∷ iI-gen ∷ X0-gen ∷ xs , at-head (lemma-K0-CS01-K0-CS02-K0-S0-CS01-K0-S0-CS02-K0=S0-K0-S0-CS01-K0-CS02-K0-S0-CS01-K0-S0-S0-S1-S2-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CS12-CCZ-iI-iI-X0))
  mvKL2-step (K0-gen ∷ S0-gen ∷ CS02-gen ∷ K0-gen ∷ S0-gen ∷ CS01-gen ∷ K0-gen ∷ S0-gen ∷ CS01-gen ∷ CS02-gen ∷ K0-gen ∷ xs) = just (S0-gen ∷ K0-gen ∷ CS02-gen ∷ K0-gen ∷ S0-gen ∷ CS01-gen ∷ K0-gen ∷ CS01-gen ∷ CS02-gen ∷ CS02-gen ∷ CS02-gen ∷ CCZ-gen ∷ X0-gen ∷ CX20-gen ∷ CCX0-gen ∷ xs , at-head (lemma-K0-S0-CS02-K0-S0-CS01-K0-S0-CS01-CS02-K0=S0-K0-CS02-K0-S0-CS01-K0-CS01-CS02-CS02-CS02-CCZ-X0-CX20-CCX0))
  mvKL2-step (K0-gen ∷ CS02-gen ∷ K0-gen ∷ CS01-gen ∷ K0-gen ∷ S0-gen ∷ CS01-gen ∷ CS02-gen ∷ K0-gen ∷ xs) = just (S0-gen ∷ K0-gen ∷ S0-gen ∷ CS02-gen ∷ K0-gen ∷ CS01-gen ∷ K0-gen ∷ CS01-gen ∷ CS02-gen ∷ CS02-gen ∷ CS02-gen ∷ CCZ-gen ∷ iI-gen ∷ iI-gen ∷ iI-gen ∷ X0-gen ∷ CX20-gen ∷ CCX0-gen ∷ xs , at-head (lemma-K0-CS02-K0-CS01-K0-S0-CS01-CS02-K0=S0-K0-S0-CS02-K0-CS01-K0-CS01-CS02-CS02-CS02-CCZ-iI-iI-iI-X0-CX20-CCX0))
  mvKL2-step (K0-gen ∷ CS01-gen ∷ K0-gen ∷ CS02-gen ∷ K0-gen ∷ S0-gen ∷ CS01-gen ∷ CS02-gen ∷ K0-gen ∷ xs) = just (S0-gen ∷ K0-gen ∷ S0-gen ∷ CS01-gen ∷ K0-gen ∷ CS02-gen ∷ K0-gen ∷ CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ CS02-gen ∷ CCZ-gen ∷ iI-gen ∷ iI-gen ∷ iI-gen ∷ X0-gen ∷ CX10-gen ∷ CCX0-gen ∷ xs , at-head (lemma-K0-CS01-K0-CS02-K0-S0-CS01-CS02-K0=S0-K0-S0-CS01-K0-CS02-K0-CS01-CS01-CS01-CS02-CCZ-iI-iI-iI-X0-CX10-CCX0))
  mvKL2-step (K0-gen ∷ S0-gen ∷ CS02-gen ∷ K0-gen ∷ S0-gen ∷ CS01-gen ∷ K0-gen ∷ CS02-gen ∷ K0-gen ∷ CS01-gen ∷ K0-gen ∷ xs) = just (S0-gen ∷ K0-gen ∷ S0-gen ∷ CS01-gen ∷ K0-gen ∷ CS02-gen ∷ K0-gen ∷ S0-gen ∷ CS01-gen ∷ K0-gen ∷ S0-gen ∷ S0-gen ∷ S1-gen ∷ S1-gen ∷ S2-gen ∷ CS02-gen ∷ CS02-gen ∷ CS02-gen ∷ CS12-gen ∷ CS12-gen ∷ CS12-gen ∷ CCZ-gen ∷ iI-gen ∷ iI-gen ∷ X0-gen ∷ xs , at-head (lemma-K0-S0-CS02-K0-S0-CS01-K0-CS02-K0-CS01-K0=S0-K0-S0-CS01-K0-CS02-K0-S0-CS01-K0-S0-S0-S1-S1-S2-CS02-CS02-CS02-CS12-CS12-CS12-CCZ-iI-iI-X0))
  mvKL2-step (K0-gen ∷ CS02-gen ∷ K0-gen ∷ CS01-gen ∷ K0-gen ∷ CS01-gen ∷ CS02-gen ∷ K0-gen ∷ xs) = just (S0-gen ∷ CS02-gen ∷ K0-gen ∷ CS01-gen ∷ K0-gen ∷ S0-gen ∷ S0-gen ∷ S0-gen ∷ CS01-gen ∷ CS02-gen ∷ CS02-gen ∷ CS02-gen ∷ CCZ-gen ∷ iI-gen ∷ iI-gen ∷ iI-gen ∷ CX20-gen ∷ CCX0-gen ∷ xs , at-head (lemma-K0-CS02-K0-CS01-K0-CS01-CS02-K0=S0-CS02-K0-CS01-K0-S0-S0-S0-CS01-CS02-CS02-CS02-CCZ-iI-iI-iI-CX20-CCX0))
  mvKL2-step (K0-gen ∷ CS02-gen ∷ K0-gen ∷ S0-gen ∷ CS01-gen ∷ K0-gen ∷ S0-gen ∷ CS01-gen ∷ CS02-gen ∷ K0-gen ∷ xs) = just (S0-gen ∷ CS02-gen ∷ K0-gen ∷ S0-gen ∷ CS01-gen ∷ K0-gen ∷ S1-gen ∷ CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ CS02-gen ∷ iI-gen ∷ iI-gen ∷ iI-gen ∷ xs , at-head (lemma-K0-CS02-K0-S0-CS01-K0-S0-CS01-CS02-K0=S0-CS02-K0-S0-CS01-K0-S1-CS01-CS01-CS01-CS02-iI-iI-iI))

  mvKL2-step _ = nothing


  mvKL2b-step : Step-Function Gate Rel
  mvKL2b-step (CS02-gen ∷ K0-gen ∷ CS01-gen ∷ K0-gen ∷ CS02-gen ∷ K0-gen ∷ CS01-gen ∷ K0-gen ∷ CS02-gen ∷ K0-gen ∷ CS01-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ CS01-gen ∷ K0-gen ∷ CS02-gen ∷ K0-gen ∷ CS01-gen ∷ K0-gen ∷ CS02-gen ∷ K0-gen ∷ CS01-gen ∷ K0-gen ∷ CS02-gen ∷ xs , at-head (lemma-CS02-K0-CS01-K0-CS02-K0-CS01-K0-CS02-K0-CS01-K0=K0-CS01-K0-CS02-K0-CS01-K0-CS02-K0-CS01-K0-CS02))
  mvKL2b-step _ = nothing


  mvKL4-step : Step-Function Gate Rel
  mvKL4-step (K0-gen ∷ CS01-gen ∷ K0-gen ∷ CS02-gen ∷ K0-gen ∷ CS01-gen ∷ CS02-gen ∷ K0-gen ∷ xs) = just (S0-gen ∷ CS01-gen ∷ K0-gen ∷ CS02-gen ∷ K0-gen ∷ S0-gen ∷ S0-gen ∷ S0-gen ∷ CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ CS02-gen ∷ CCZ-gen ∷ iI-gen ∷ iI-gen ∷ iI-gen ∷ CX10-gen ∷ CCX0-gen ∷ xs , at-head (lemma-K0-CS01-K0-CS02-K0-CS01-CS02-K0=S0-CS01-K0-CS02-K0-S0-S0-S0-CS01-CS01-CS01-CS02-CCZ-iI-iI-iI-CX10-CCX0))

  mvKL4-step (CS02-gen ∷ K0-gen ∷ CS01-gen ∷ K0-gen ∷ CS02-gen ∷ K0-gen ∷ xs) = just (CS01-gen ∷ K0-gen ∷ CS02-gen ∷ K0-gen ∷ CS01-gen ∷ K0-gen ∷ S1-gen ∷ CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ CS02-gen ∷ CS02-gen ∷ CS02-gen ∷ CS12-gen ∷ CS12-gen ∷ CS12-gen ∷ CCZ-gen ∷ CX10-gen ∷ CX20-gen ∷ xs , at-head (lemma-CS02-K0-CS01-K0-CS02-K0=CS01-K0-CS02-K0-CS01-K0-S1-CS01-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CS12-CCZ-CX10-CX20))
  mvKL4-step (K0-gen ∷ CS01-gen ∷ K0-gen ∷ CS02-gen ∷ K0-gen ∷ CS01-gen ∷ K0-gen ∷ S0-gen ∷ CS02-gen ∷ K0-gen ∷ xs) = just (S0-gen ∷ CS01-gen ∷ K0-gen ∷ CS02-gen ∷ K0-gen ∷ CS01-gen ∷ K0-gen ∷ S1-gen ∷ CS01-gen ∷ CS01-gen ∷ CS02-gen ∷ CS02-gen ∷ CS02-gen ∷ CS12-gen ∷ CS12-gen ∷ CS12-gen ∷ CCZ-gen ∷ iI-gen ∷ iI-gen ∷ iI-gen ∷ CX20-gen ∷ xs , at-head (lemma-K0-CS01-K0-CS02-K0-CS01-K0-S0-CS02-K0=S0-CS01-K0-CS02-K0-CS01-K0-S1-CS01-CS01-CS02-CS02-CS02-CS12-CS12-CS12-CCZ-iI-iI-iI-CX20))

  mvKL4-step (K0-gen ∷ S0-gen ∷ CS01-gen ∷ K0-gen ∷ S0-gen ∷ CS02-gen ∷ K0-gen ∷ S0-gen ∷ CS01-gen ∷ CS02-gen ∷ K0-gen ∷ S0-gen ∷ CS01-gen ∷ CS02-gen ∷ K0-gen ∷ xs) = just (S0-gen ∷ K0-gen ∷ CS01-gen ∷ K0-gen ∷ CS02-gen ∷ K0-gen ∷ S0-gen ∷ S1-gen ∷ S2-gen ∷ CS01-gen ∷ CS01-gen ∷ CCZ-gen ∷ iI-gen ∷ iI-gen ∷ iI-gen ∷ X0-gen ∷ CX10-gen ∷ CCX0-gen ∷ xs , at-head (lemma-K0-S0-CS01-K0-S0-CS02-K0-S0-CS01-CS02-K0-S0-CS01-CS02-K0=S0-K0-CS01-K0-CS02-K0-S0-S1-S2-CS01-CS01-CCZ-iI-iI-iI-X0-CX10-CCX0))

  mvKL4-step _ = nothing



  module mvKL2' = Step-With-Standardization (step-cong ( mvKL-step then order-K0-step)) (ListNF.listnf nf-spde) (ListNF.lemma-listnf nf-spde)
  module mvKL2'' = Step-With-Standardization (step-cong (mvKL-step then  mvKL2b-step then order-K0-step)) (ListNF.listnf nf-spde) (ListNF.lemma-listnf nf-spde)

  module mvKL3 = Step-With-Standardization (step-cong (mvKL2-step then mvKL-step then order-K0-step)) (ListNF.listnf nf-spde) (ListNF.lemma-listnf nf-spde)

  module mvKL4 = Step-With-Standardization (step-cong (mvKL4-step then mvKL-step then order-K0-step)) (ListNF.listnf nf-spde) (ListNF.lemma-listnf nf-spde)

  nf-e4 : ListNF Rel
  nf-e4 = record { listnf = mvKL3.multistep 2000 ; lemma-listnf = mvKL3.lemma-multistep 2000 }

  module P24K0D = SemiDirect isP24 isk0spd nfp24 nf-e4 group-like p24-spde4-conj

  nf-p24k0d : ListNF Rel
  nf-p24k0d = record { listnf = P24K0D.nfnh' ; lemma-listnf = P24K0D.lemma-nfnh' }

  nf-e4' : ListNF Rel
  nf-e4' = record { listnf = mvKL2'.multistep 2000 ; lemma-listnf = mvKL2'.lemma-multistep 2000 }

  nf-e4'b : ListNF Rel
  nf-e4'b = record { listnf = mvKL2''.multistep 2000 ; lemma-listnf = mvKL2''.lemma-multistep 2000 }

  module P24K0D' = SemiDirect isP24 isk0spd nfp24 nf-e4' group-like p24-spde4-conj

  nf-p24k0d' : ListNF Rel
  nf-p24k0d' = record { listnf = P24K0D'.nfnh' ; lemma-listnf = P24K0D'.lemma-nfnh' }

  module P24K0D'' = SemiDirect isP24 isk0spd nfp24 nf-e4'b group-like p24-spde4-conj

  nf-p24k0d'' : ListNF Rel
  nf-p24k0d'' = record { listnf = P24K0D''.nfnh' ; lemma-listnf = P24K0D''.lemma-nfnh' }


  nf-e44 : ListNF Rel
  nf-e44 = record { listnf = mvKL4.multistep 2000 ; lemma-listnf = mvKL4.lemma-multistep 2000 }

  module P24K0D4 = SemiDirect isP24 isk0spd nfp24 nf-e44 group-like p24-spde4-conj

  nf-p24k0d4 : ListNF Rel
  nf-p24k0d4 = record { listnf = P24K0D4.nfnh' ; lemma-listnf = P24K0D4.lemma-nfnh' }

  nf-kpd : ListNF Rel
  nf-kpd = rep 3 (extend-nf isk0spd nf-p24k0d ∘ extend-nf isPD nf-pd)

  nf-de : ListNF Rel
  nf-de = extend-nf isD nfd
