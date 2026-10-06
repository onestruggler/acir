------------------------------------------------------------------------
-- Presentations of groups
--
-- Ported from the Agda code accompanying Bian and Selinger,
-- "Generators and relations for 3-qubit Clifford+CS operators"
-- (arXiv:2306.08530, CC BY 2.0).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Presentation.Tactics.Equality as Eq using (_≡_ ; auto)
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_)
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
open import Examples.Groups.Clifford+CS-3qubit.Gate
open import Examples.Groups.Clifford+CS-3qubit.CosetNF as CosetNF
open CosetNF.Legacy

open import Examples.Groups.Clifford+CS-3qubit.Step3.Rel
open import Examples.Groups.Clifford+CS-3qubit.Step3.PD3
open import Examples.Groups.Clifford+CS-3qubit.Step3.PD4

module Examples.Groups.Clifford+CS-3qubit.Step3.PD5 where

  pd-conj : let X = Gate in let Γ = Rel in (h n : X) -> Maybe (∃ λ (n' : Word X) -> Γ ⊢ [ h ]ʷ • [ n ]ʷ === n' • [ h ]ʷ)
  pd-conj Swap01-gen S0-gen = just ( S1 , axiom ax-Swap01-S0=S1-Swap01 )
  pd-conj Swap01-gen S1-gen = just ( S0 , axiom ax-Swap01-S1=S0-Swap01 )
  pd-conj Swap01-gen S2-gen = just ( S2 , axiom ax-Swap01-S2=S2-Swap01 )
  pd-conj Swap01-gen CS01-gen = just ( CS01 , axiom ax-Swap01-CS01=CS01-Swap01 )
  pd-conj Swap01-gen CS02-gen = just ( CS12 , axiom ax-Swap01-CS02=CS12-Swap01 )
  pd-conj Swap01-gen CS12-gen = just ( CS02 , axiom ax-Swap01-CS12=CS02-Swap01 )
  pd-conj Swap01-gen CCZ-gen = just ( CCZ , axiom ax-Swap01-CCZ=CCZ-Swap01 )
  pd-conj Swap01-gen iI-gen = just ( iI , axiom ax-Swap01-iI=iI-Swap01 )
  pd-conj CX01-gen S0-gen = just ( S0 , axiom ax-CX01-S0=S0-CX01 )
  pd-conj CX01-gen S1-gen = just ( S0 • S1 • CS01 • CS01 , up-to-assoc auto (axiom ax-CX01-S1=S0-S1-CS01-CS01-CX01) )
  pd-conj CX01-gen S2-gen = just ( S2 , axiom ax-CX01-S2=S2-CX01 )
  pd-conj CX01-gen CS01-gen = just ( S0 • CS01 • CS01 • CS01 , up-to-assoc auto (axiom ax-CX01-CS01=S0-CS01-CS01-CS01-CX01) )
  pd-conj CX01-gen CS02-gen = just ( CS02 , axiom ax-CX01-CS02=CS02-CX01 )
  pd-conj CX01-gen CS12-gen = just ( CS02 • CS12 • CCZ , up-to-assoc auto (axiom ax-CX01-CS12=CS02-CS12-CCZ-CX01) )
  pd-conj CX01-gen CCZ-gen = just ( CS02 • CS02 • CCZ , up-to-assoc auto (axiom ax-CX01-CCZ=CS02-CS02-CCZ-CX01) )
  pd-conj CX01-gen iI-gen = just ( iI , axiom ax-CX01-iI=iI-CX01 )
  pd-conj CX02-gen S0-gen = just ( S0 , axiom ax-CX02-S0=S0-CX02 )
  pd-conj CX02-gen S1-gen = just ( S1 , axiom ax-CX02-S1=S1-CX02 )
  pd-conj CX02-gen S2-gen = just ( S0 • S2 • CS02 • CS02 , up-to-assoc auto (axiom ax-CX02-S2=S0-S2-CS02-CS02-CX02) )
  pd-conj CX02-gen CS01-gen = just ( CS01 , axiom ax-CX02-CS01=CS01-CX02 )
  pd-conj CX02-gen CS02-gen = just ( S0 • CS02 • CS02 • CS02 , up-to-assoc auto (axiom ax-CX02-CS02=S0-CS02-CS02-CS02-CX02) )
  pd-conj CX02-gen CS12-gen = just ( CS01 • CS12 • CCZ , up-to-assoc auto (axiom ax-CX02-CS12=CS01-CS12-CCZ-CX02) )
  pd-conj CX02-gen CCZ-gen = just ( CS01 • CS01 • CCZ , up-to-assoc auto (axiom ax-CX02-CCZ=CS01-CS01-CCZ-CX02) )
  pd-conj CX02-gen iI-gen = just ( iI , axiom ax-CX02-iI=iI-CX02 )
  pd-conj CCX1-gen S0-gen = just ( S0 , axiom ax-CCX1-S0=S0-CCX1 )
  pd-conj CCX1-gen S1-gen = just ( S1 • CS02 • CCZ , up-to-assoc auto (axiom ax-CCX1-S1=S1-CS02-CCZ-CCX1) )
  pd-conj CCX1-gen S2-gen = just ( S2 , axiom ax-CCX1-S2=S2-CCX1 )
  pd-conj CCX1-gen CS01-gen = just ( CS01 • CS02 • CCZ , up-to-assoc auto (axiom ax-CCX1-CS01=CS01-CS02-CCZ-CCX1) )
  pd-conj CCX1-gen CS02-gen = just ( CS02 , axiom ax-CCX1-CS02=CS02-CCX1 )
  pd-conj CCX1-gen CS12-gen = just ( CS02 • CS12 • CCZ , up-to-assoc auto (axiom ax-CCX1-CS12=CS02-CS12-CCZ-CCX1) )
  pd-conj CCX1-gen CCZ-gen = just ( CS02 • CS02 • CCZ , up-to-assoc auto (axiom ax-CCX1-CCZ=CS02-CS02-CCZ-CCX1) )
  pd-conj CCX1-gen iI-gen = just ( iI , axiom ax-CCX1-iI=iI-CCX1 )
  pd-conj CCX2-gen S0-gen = just ( S0 , axiom ax-CCX2-S0=S0-CCX2 )
  pd-conj CCX2-gen S1-gen = just ( S1 , axiom ax-CCX2-S1=S1-CCX2 )
  pd-conj CCX2-gen S2-gen = just ( S2 • CS01 • CCZ , up-to-assoc auto (axiom ax-CCX2-S2=S2-CS01-CCZ-CCX2) )
  pd-conj CCX2-gen CS01-gen = just ( CS01 , axiom ax-CCX2-CS01=CS01-CCX2 )
  pd-conj CCX2-gen CS02-gen = just ( CS01 • CS02 • CCZ , up-to-assoc auto (axiom ax-CCX2-CS02=CS01-CS02-CCZ-CCX2) )
  pd-conj CCX2-gen CS12-gen = just ( CS01 • CS12 • CCZ , up-to-assoc auto (axiom ax-CCX2-CS12=CS01-CS12-CCZ-CCX2) )
  pd-conj CCX2-gen CCZ-gen = just ( CS01 • CS01 • CCZ , up-to-assoc auto (axiom ax-CCX2-CCZ=CS01-CS01-CCZ-CCX2) )
  pd-conj CCX2-gen iI-gen = just ( iI , axiom ax-CCX2-iI=iI-CCX2 )
  pd-conj X1-gen S0-gen = just ( S0 , axiom ax-X1-S0=S0-X1 )
  pd-conj X1-gen S1-gen = just ( S1 • S1 • S1 • iI , up-to-assoc auto (axiom ax-X1-S1=S1-S1-S1-iI-X1) )
  pd-conj X1-gen S2-gen = just ( S2 , axiom ax-X1-S2=S2-X1 )
  pd-conj X1-gen CS01-gen = just ( S0 • CS01 • CS01 • CS01 , up-to-assoc auto (axiom ax-X1-CS01=S0-CS01-CS01-CS01-X1) )
  pd-conj X1-gen CS02-gen = just ( CS02 , axiom ax-X1-CS02=CS02-X1 )
  pd-conj X1-gen CS12-gen = just ( S2 • CS12 • CS12 • CS12 , up-to-assoc auto (axiom ax-X1-CS12=S2-CS12-CS12-CS12-X1) )
  pd-conj X1-gen CCZ-gen = just ( CS02 • CS02 • CCZ , up-to-assoc auto (axiom ax-X1-CCZ=CS02-CS02-CCZ-X1) )
  pd-conj X1-gen iI-gen = just ( iI , axiom ax-X1-iI=iI-X1 )
  pd-conj X2-gen S0-gen = just ( S0 , axiom ax-X2-S0=S0-X2 )
  pd-conj X2-gen S1-gen = just ( S1 , axiom ax-X2-S1=S1-X2 )
  pd-conj X2-gen S2-gen = just ( S2 • S2 • S2 • iI , up-to-assoc auto (axiom ax-X2-S2=S2-S2-S2-iI-X2) )
  pd-conj X2-gen CS01-gen = just ( CS01 , axiom ax-X2-CS01=CS01-X2 )
  pd-conj X2-gen CS02-gen = just ( S0 • CS02 • CS02 • CS02 , up-to-assoc auto (axiom ax-X2-CS02=S0-CS02-CS02-CS02-X2) )
  pd-conj X2-gen CS12-gen = just ( S1 • CS12 • CS12 • CS12 , up-to-assoc auto (axiom ax-X2-CS12=S1-CS12-CS12-CS12-X2) )
  pd-conj X2-gen CCZ-gen = just ( CS01 • CS01 • CCZ , up-to-assoc auto (axiom ax-X2-CCZ=CS01-CS01-CCZ-X2) )
  pd-conj X2-gen iI-gen = just ( iI , axiom ax-X2-iI=iI-X2 )
  pd-conj CX12-gen S0-gen = just ( S0 , axiom ax-CX12-S0=S0-CX12 )
  pd-conj CX12-gen S1-gen = just ( S1 , axiom ax-CX12-S1=S1-CX12 )
  pd-conj CX12-gen S2-gen = just ( S1 • S2 • CS12 • CS12 , up-to-assoc auto (axiom ax-CX12-S2=S1-S2-CS12-CS12-CX12) )
  pd-conj CX12-gen CS01-gen = just ( CS01 , axiom ax-CX12-CS01=CS01-CX12 )
  pd-conj CX12-gen CS02-gen = just ( CS01 • CS02 • CCZ , up-to-assoc auto (axiom ax-CX12-CS02=CS01-CS02-CCZ-CX12) )
  pd-conj CX12-gen CS12-gen = just ( S1 • CS12 • CS12 • CS12 , up-to-assoc auto (axiom ax-CX12-CS12=S1-CS12-CS12-CS12-CX12) )
  pd-conj CX12-gen CCZ-gen = just ( CS01 • CS01 • CCZ , up-to-assoc auto (axiom ax-CX12-CCZ=CS01-CS01-CCZ-CX12) )
  pd-conj CX12-gen iI-gen = just ( iI , axiom ax-CX12-iI=iI-CX12 )
  pd-conj CX21-gen S0-gen = just ( S0 , axiom ax-CX21-S0=S0-CX21 )
  pd-conj CX21-gen S1-gen = just ( S1 • S2 • CS12 • CS12 , up-to-assoc auto (axiom ax-CX21-S1=S1-S2-CS12-CS12-CX21) )
  pd-conj CX21-gen S2-gen = just ( S2 , axiom ax-CX21-S2=S2-CX21 )
  pd-conj CX21-gen CS01-gen = just ( CS01 • CS02 • CCZ , up-to-assoc auto (axiom ax-CX21-CS01=CS01-CS02-CCZ-CX21) )
  pd-conj CX21-gen CS02-gen = just ( CS02 , axiom ax-CX21-CS02=CS02-CX21 )
  pd-conj CX21-gen CS12-gen = just ( S2 • CS12 • CS12 • CS12 , up-to-assoc auto (axiom ax-CX21-CS12=S2-CS12-CS12-CS12-CX21) )
  pd-conj CX21-gen CCZ-gen = just ( CS02 • CS02 • CCZ , up-to-assoc auto (axiom ax-CX21-CCZ=CS02-CS02-CCZ-CX21) )
  pd-conj CX21-gen iI-gen = just ( iI , axiom ax-CX21-iI=iI-CX21 )
  pd-conj Swap12-gen S0-gen = just ( S0 , axiom ax-Swap12-S0=S0-Swap12 )
  pd-conj Swap12-gen S1-gen = just ( S2 , axiom ax-Swap12-S1=S2-Swap12 )
  pd-conj Swap12-gen S2-gen = just ( S1 , axiom ax-Swap12-S2=S1-Swap12 )
  pd-conj Swap12-gen CS01-gen = just ( CS02 , axiom ax-Swap12-CS01=CS02-Swap12 )
  pd-conj Swap12-gen CS02-gen = just ( CS01 , axiom ax-Swap12-CS02=CS01-Swap12 )
  pd-conj Swap12-gen CS12-gen = just ( CS12 , axiom ax-Swap12-CS12=CS12-Swap12 )
  pd-conj Swap12-gen CCZ-gen = just ( CCZ , axiom ax-Swap12-CCZ=CCZ-Swap12 )
  pd-conj Swap12-gen iI-gen = just ( iI , axiom ax-Swap12-iI=iI-Swap12 )
  pd-conj X0-gen S0-gen = just ( S0 • S0 • S0 • iI , up-to-assoc auto (axiom ax-X0-S0=S0-S0-S0-iI-X0) )
  pd-conj X0-gen S1-gen = just ( S1 , axiom ax-X0-S1=S1-X0 )
  pd-conj X0-gen S2-gen = just ( S2 , axiom ax-X0-S2=S2-X0 )
  pd-conj X0-gen CS01-gen = just ( S1 • CS01 • CS01 • CS01 , up-to-assoc auto (axiom ax-X0-CS01=S1-CS01-CS01-CS01-X0) )
  pd-conj X0-gen CS02-gen = just ( S2 • CS02 • CS02 • CS02 , up-to-assoc auto (axiom ax-X0-CS02=S2-CS02-CS02-CS02-X0) )
  pd-conj X0-gen CS12-gen = just ( CS12 , axiom ax-X0-CS12=CS12-X0 )
  pd-conj X0-gen CCZ-gen = just ( CS12 • CS12 • CCZ , up-to-assoc auto (axiom ax-X0-CCZ=CS12-CS12-CCZ-X0) )
  pd-conj X0-gen iI-gen = just ( iI , axiom ax-X0-iI=iI-X0 )
  pd-conj CX10-gen S0-gen = just ( S0 • S1 • CS01 • CS01 , up-to-assoc auto (axiom ax-CX10-S0=S0-S1-CS01-CS01-CX10) )
  pd-conj CX10-gen S1-gen = just ( S1 , axiom ax-CX10-S1=S1-CX10 )
  pd-conj CX10-gen S2-gen = just ( S2 , axiom ax-CX10-S2=S2-CX10 )
  pd-conj CX10-gen CS01-gen = just ( S1 • CS01 • CS01 • CS01 , up-to-assoc auto (axiom ax-CX10-CS01=S1-CS01-CS01-CS01-CX10) )
  pd-conj CX10-gen CS02-gen = just ( CS02 • CS12 • CCZ , up-to-assoc auto (axiom ax-CX10-CS02=CS02-CS12-CCZ-CX10) )
  pd-conj CX10-gen CS12-gen = just ( CS12 , axiom ax-CX10-CS12=CS12-CX10 )
  pd-conj CX10-gen CCZ-gen = just ( CS12 • CS12 • CCZ , up-to-assoc auto (axiom ax-CX10-CCZ=CS12-CS12-CCZ-CX10) )
  pd-conj CX10-gen iI-gen = just ( iI , axiom ax-CX10-iI=iI-CX10 )
  pd-conj CX20-gen S0-gen = just ( S0 • S2 • CS02 • CS02 , up-to-assoc auto (axiom ax-CX20-S0=S0-S2-CS02-CS02-CX20) )
  pd-conj CX20-gen S1-gen = just ( S1 , axiom ax-CX20-S1=S1-CX20 )
  pd-conj CX20-gen S2-gen = just ( S2 , axiom ax-CX20-S2=S2-CX20 )
  pd-conj CX20-gen CS01-gen = just ( CS01 • CS12 • CCZ , up-to-assoc auto (axiom ax-CX20-CS01=CS01-CS12-CCZ-CX20) )
  pd-conj CX20-gen CS02-gen = just ( S2 • CS02 • CS02 • CS02 , up-to-assoc auto (axiom ax-CX20-CS02=S2-CS02-CS02-CS02-CX20) )
  pd-conj CX20-gen CS12-gen = just ( CS12 , axiom ax-CX20-CS12=CS12-CX20 )
  pd-conj CX20-gen CCZ-gen = just ( CS12 • CS12 • CCZ , up-to-assoc auto (axiom ax-CX20-CCZ=CS12-CS12-CCZ-CX20) )
  pd-conj CX20-gen iI-gen = just ( iI , axiom ax-CX20-iI=iI-CX20 )
  pd-conj CCX0-gen S0-gen = just ( S0 • CS12 • CCZ , up-to-assoc auto (axiom ax-CCX0-S0=S0-CS12-CCZ-CCX0) )
  pd-conj CCX0-gen S1-gen = just ( S1 , axiom ax-CCX0-S1=S1-CCX0 )
  pd-conj CCX0-gen S2-gen = just ( S2 , axiom ax-CCX0-S2=S2-CCX0 )
  pd-conj CCX0-gen CS01-gen = just ( CS01 • CS12 • CCZ , up-to-assoc auto (axiom ax-CCX0-CS01=CS01-CS12-CCZ-CCX0) )
  pd-conj CCX0-gen CS02-gen = just ( CS02 • CS12 • CCZ , up-to-assoc auto (axiom ax-CCX0-CS02=CS02-CS12-CCZ-CCX0) )
  pd-conj CCX0-gen CS12-gen = just ( CS12 , axiom ax-CCX0-CS12=CS12-CCX0 )
  pd-conj CCX0-gen CCZ-gen = just ( CS12 • CS12 • CCZ , up-to-assoc auto (axiom ax-CCX0-CCZ=CS12-CS12-CCZ-CCX0) )
  pd-conj CCX0-gen iI-gen = just ( iI , axiom ax-CCX0-iI=iI-CCX0 )
  pd-conj _ _ = nothing

  nfp : NF Rel
  nfp = record { nf = P.lactnf ; lemma-nf = P.lemma-lactnf }

  nfd : NF Rel
  nfd = record { nf = f-of-listf (Diag.multistep 1000) ; lemma-nf = lemma-f-of-listf (Diag.lemma-multistep 1000) }

  isP : Gate -> Bool
  isP CCX0-gen = true
  isP CCX1-gen = true
  isP CCX2-gen = true
  isP CX01-gen = true
  isP CX10-gen = true
  isP CX12-gen = true
  isP CX21-gen = true
  isP CX02-gen = true
  isP CX20-gen = true
  isP X0-gen = true
  isP X1-gen = true
  isP X2-gen = true
  isP Swap01-gen = true
  isP Swap12-gen = true
  isP _ = false

  isD : Gate -> Bool
  isD S0-gen = true
  isD S1-gen = true
  isD S2-gen = true
  isD CS01-gen = true
  isD CS12-gen = true
  isD CS02-gen = true
  isD CCZ-gen = true
  isD iI-gen = true
  isD _ = false
  
  module PD = SemiDirect' isP isD nfp nfd group-like pd-conj

  isK0D : Gate -> Bool
  isK0D CCX0-gen = true
  isK0D CX10-gen = true
  isK0D CX20-gen = true
  isK0D X0-gen = true
  isK0D S0-gen = true
  isK0D S1-gen = true
  isK0D S2-gen = true
  isK0D CS01-gen = true
  isK0D CS12-gen = true
  isK0D CS02-gen = true
  isK0D CCZ-gen = true
  isK0D iI-gen = true
  isK0D CCK'-gen = true
  isK0D CK10-gen = true
  isK0D CK20-gen = true
  isK0D K0-gen = true
  isK0D _ = false
 
