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
open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; _∨_)
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
open import Examples.Groups.Clifford+CS-3qubit.Step3.PD5
open import Examples.Groups.Clifford+CS-3qubit.Step3.PD6

module Examples.Groups.Clifford+CS-3qubit.Step3.PD7 where

  mvKL-step : Step-Function Gate Rel
  mvKL-step (CCX2-gen ∷ K0-gen ∷ CK10-gen ∷ xs) = just (K0-gen ∷ CK10-gen ∷ CCX2-gen ∷ xs , at-head (axiom ax-CCX2-K0-CK10=K0-CK10-CCX2))
  mvKL-step (CCX2-gen ∷ CK20-gen ∷ CCK'-gen ∷ xs) = just (CK20-gen ∷ CCK'-gen ∷ CCX2-gen ∷ CS01-gen ∷ CS01-gen ∷ xs , at-head (axiom ax-CCX2-CK20-CCK'=CK20-CCK'-CCX2-CS01-CS01))
  mvKL-step (CCX1-gen ∷ CK10-gen ∷ CCK'-gen ∷ xs) = just (CK10-gen ∷ CCK'-gen ∷ CCX1-gen ∷ CS02-gen ∷ CS02-gen ∷ xs , at-head (axiom ax-CCX1-CK10-CCK'=CK10-CCK'-CCX1-CS02-CS02))
  mvKL-step (CCX2-gen ∷ K0-gen ∷ CK20-gen ∷ CK10-gen ∷ CCK'-gen ∷ xs) = just (K0-gen ∷ CK20-gen ∷ CK10-gen ∷ CCK'-gen ∷ CCX2-gen ∷ CS01-gen ∷ CS01-gen ∷ xs , at-head (axiom ax-CCX2-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-CCX2-CS01-CS01))
  mvKL-step (CCX1-gen ∷ K0-gen ∷ CK20-gen ∷ CK10-gen ∷ CCK'-gen ∷ xs) = just (K0-gen ∷ CK20-gen ∷ CK10-gen ∷ CCK'-gen ∷ CCX1-gen ∷ CS02-gen ∷ CS02-gen ∷ xs , at-head (axiom ax-CCX1-K0-CK20-CK10-CCK'=K0-CK20-CK10-CCK'-CCX1-CS02-CS02))
  mvKL-step (CCX2-gen ∷ CX02-gen ∷ K0-gen ∷ CK10-gen ∷ xs) = just (CK10-gen ∷ CCX2-gen ∷ CX02-gen ∷ K0-gen ∷ xs , at-head (axiom ax-CCX2-CX02-K0-CK10=CK10-CCX2-CX02-K0))
  mvKL-step (CCX1-gen ∷ CX01-gen ∷ CCK'-gen ∷ xs) = just (CCK'-gen ∷ CCX1-gen ∷ CX01-gen ∷ xs , at-head (axiom ax-CCX1-CX01-CCK'=CCK'-CCX1-CX01))
  mvKL-step (CCX2-gen ∷ CCX1-gen ∷ CX02-gen ∷ CCK'-gen ∷ xs) = just (CCK'-gen ∷ CCX2-gen ∷ CCX1-gen ∷ CX02-gen ∷ xs , at-head (axiom ax-CCX2-CCX1-CX02-CCK'=CCK'-CCX2-CCX1-CX02))
  mvKL-step (CCX2-gen ∷ Swap01-gen ∷ CK20-gen ∷ CCK'-gen ∷ xs) = just (Swap01-gen ∷ CK20-gen ∷ CCK'-gen ∷ CCX2-gen ∷ CS01-gen ∷ CS01-gen ∷ xs , at-head (axiom ax-CCX2-Swap01-CK20-CCK'=Swap01-CK20-CCK'-CCX2-CS01-CS01))
  mvKL-step (CCX1-gen ∷ CX01-gen ∷ CK20-gen ∷ xs) = just (CK20-gen ∷ CCX1-gen ∷ CX01-gen ∷ xs , at-head (axiom ax-CCX1-CX01-CK20=CK20-CCX1-CX01))
  mvKL-step (CCX2-gen ∷ K0-gen ∷ CCX2-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ CCX2-gen ∷ K0-gen ∷ CCX2-gen ∷ CX12-gen ∷ xs , at-head (axiom ax-CCX2-K0-CCX2-K0=K0-CCX2-K0-CCX2-CX12))
  mvKL-step (CCX2-gen ∷ CX02-gen ∷ K0-gen ∷ CCX2-gen ∷ CX02-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ CCX2-gen ∷ CX02-gen ∷ K0-gen ∷ CCX2-gen ∷ CX02-gen ∷ CX12-gen ∷ X2-gen ∷ xs , at-head (axiom ax-CCX2-CX02-K0-CCX2-CX02-K0=K0-CCX2-CX02-K0-CCX2-CX02-CX12-X2))
  mvKL-step (CCX2-gen ∷ CX02-gen ∷ CK10-gen ∷ xs) = just (CK10-gen ∷ CCX2-gen ∷ CX02-gen ∷ xs , at-head (axiom ax-CCX2-CX02-CK10=CK10-CCX2-CX02))
  mvKL-step (CK10-gen ∷ CCK'-gen ∷ CCX1-gen ∷ CK20-gen ∷ CCK'-gen ∷ xs) = just (CCX1-gen ∷ CK20-gen ∷ CK10-gen ∷ CX20-gen ∷ CCX0-gen ∷ CS12-gen ∷ CS12-gen ∷ CS12-gen ∷ xs , at-head (axiom ax-CK10-CCK'-CCX1-CK20-CCK'=CCX1-CK20-CK10-CX20-CCX0-CS12-CS12-CS12))
  mvKL-step (K0-gen ∷ CK20-gen ∷ CK10-gen ∷ CCK'-gen ∷ CX01-gen ∷ CCX0-gen ∷ Swap01-gen ∷ CK20-gen ∷ CCK'-gen ∷ xs) = just (K0-gen ∷ CK10-gen ∷ CX01-gen ∷ CCX0-gen ∷ Swap01-gen ∷ S2-gen ∷ S2-gen ∷ S2-gen ∷ CS12-gen ∷ CS12-gen ∷ xs , at-head (axiom ax-K0-CK20-CK10-CCK'-CX01-CCX0-Swap01-CK20-CCK'=K0-CK10-CX01-CCX0-Swap01-S2-S2-S2-CS12-CS12))
  mvKL-step _ = nothing

  module mvKL = Rewriting.Step (step-cong mvKL-step)

  OrderNF : ListNF Rel
  OrderNF = record { listnf = Order.multistep 4000 ; lemma-listnf = Order.lemma-multistep 4000 }

  PDNF : ListNF Rel
  PDNF = record { listnf = listf-of-f PD.nfhn' ; lemma-listnf = lemma-listf-of-f PD.lemma-nfhn' }

  K0QDNF : ListNF Rel
  K0QDNF = record { listnf = listf-of-f K0QD.lactnf ; lemma-listnf = lemma-listf-of-f K0QD.lemma-lactnf }

  mvKLNF : ListNF Rel
  mvKLNF = record { listnf = mvKL.multistep 4000 ; lemma-listnf = mvKL.lemma-multistep 4000 }

  isPD : Gate -> Bool
  isPD x = isP x ∨ isD x

  isP24K0D : Gate -> Bool
  isP24K0D x = isK0D x ∨ isP24 x
  
  ANF = rep 10 (mvKLNF ∘ extend-nf isP24K0D K0QDNF ∘ extend-nf isPD PDNF ∘ OrderNF)
  ANF20 = rep 20 (mvKLNF ∘ extend-nf isP24K0D K0QDNF ∘ extend-nf isPD PDNF ∘ OrderNF)
