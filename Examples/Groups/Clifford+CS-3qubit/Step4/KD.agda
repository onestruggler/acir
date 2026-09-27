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
open import Examples.Groups.Clifford+CS-3qubit.Step4.Rel
open import Examples.Groups.Clifford+CS-3qubit.Step4.S8
open import Examples.Groups.Clifford+CS-3qubit.Step4.S8D

module Examples.Groups.Clifford+CS-3qubit.Step4.KD where


  p16-step : Step-Function Gate Rel
  p16-step (X0-gen ∷ X0-gen ∷ xs) = just (xs , at-head (axiom ax-X0-X0=ε))
  p16-step (CX10-gen ∷ CX10-gen ∷ xs) = just (xs , at-head (axiom ax-CX10-CX10=ε))
  p16-step (CX20-gen ∷ CX20-gen ∷ xs) = just (xs , at-head (axiom ax-CX20-CX20=ε))
  p16-step (CCX0-gen ∷ CCX0-gen ∷ xs) = just (xs , at-head (axiom ax-CCX0-CCX0=ε))
  p16-step (CX10-gen ∷ X0-gen ∷ xs) = just (X0-gen ∷ CX10-gen ∷ xs , at-head (axiom ax-CX10-X0=X0-CX10))
  p16-step (CX20-gen ∷ X0-gen ∷ xs) = just (X0-gen ∷ CX20-gen ∷ xs , at-head (axiom ax-CX20-X0=X0-CX20))
  p16-step (CX20-gen ∷ CX10-gen ∷ xs) = just (CX10-gen ∷ CX20-gen ∷ xs , at-head (axiom ax-CX20-CX10=CX10-CX20))
  p16-step (CCX0-gen ∷ X0-gen ∷ xs) = just (X0-gen ∷ CCX0-gen ∷ xs , at-head (axiom ax-CCX0-X0=X0-CCX0))
  p16-step (CCX0-gen ∷ CX10-gen ∷ xs) = just (CX10-gen ∷ CCX0-gen ∷ xs , at-head (axiom ax-CCX0-CX10=CX10-CCX0))
  p16-step (CCX0-gen ∷ CX20-gen ∷ xs) = just (CX20-gen ∷ CCX0-gen ∷ xs , at-head (axiom ax-CCX0-CX20=CX20-CCX0))
  p16-step _ = nothing

  module P16 = Rewriting.Step (step-cong p16-step)
  nfp16 : ListNF Rel
  nfp16 = record { listnf = P16.multistep 1000 ; lemma-listnf = P16.lemma-multistep 1000 }

  isP16 : Gate -> Bool
  isP16 CCX0-gen = true
  isP16 CX10-gen = true
  isP16 CX20-gen = true
  isP16 X0-gen = true
  isP16 _ = false


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


  spde1-act : let X = Gate in let Γ = Rel in (g : X) -> (rep : List X) ->  Maybe (∃ λ (rep' : List X) -> ∃ λ (g' : List X) -> Γ ⊢ [ g ]ʷ • word-of-list rep === word-of-list (rep' ++ g'))
  spde1-act CCK'-gen [] = just ( CCK'-gen ∷ [] , [] , refl )
  spde1-act CCK'-gen (CCK'-gen ∷ [] ) = just ( CCK'-gen ∷ CCK'-gen ∷ [] , [] , refl )
  spde1-act CCK'-gen (CCK'-gen ∷ CCK'-gen ∷ [] ) = just ( [] , CS12-gen ∷ CS12-gen ∷ [] , up-to-assoc auto (axiom ax-CCK'-CCK'-CCK'=CS12-CS12) )
  spde1-act X0-gen [] = just ( [] , X0-gen ∷ [] , refl )
  spde1-act X0-gen (CCK'-gen ∷ [] ) = just ( CCK'-gen ∷ [] , X0-gen ∷ CCX0-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-X0-CCK'=CCK'-X0-CCX0-CCZ) )
  spde1-act X0-gen (CCK'-gen ∷ CCK'-gen ∷ [] ) = just ( CCK'-gen ∷ CCK'-gen ∷ [] , X0-gen ∷ CS12-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-X0-CCK'-CCK'=CCK'-CCK'-X0-CS12-CCZ) )
  spde1-act CX10-gen [] = just ( [] , CX10-gen ∷ [] , refl )
  spde1-act CX10-gen (CCK'-gen ∷ [] ) = just ( CCK'-gen ∷ [] , CX10-gen ∷ CCX0-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-CCK'=CCK'-CX10-CCX0-CCZ) )
  spde1-act CX10-gen (CCK'-gen ∷ CCK'-gen ∷ [] ) = just ( CCK'-gen ∷ CCK'-gen ∷ [] , CX10-gen ∷ CS12-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-CCK'-CCK'=CCK'-CCK'-CX10-CS12-CCZ) )
  spde1-act CX20-gen [] = just ( [] , CX20-gen ∷ [] , refl )
  spde1-act CX20-gen (CCK'-gen ∷ [] ) = just ( CCK'-gen ∷ [] , CX20-gen ∷ CCX0-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CX20-CCK'=CCK'-CX20-CCX0-CCZ) )
  spde1-act CX20-gen (CCK'-gen ∷ CCK'-gen ∷ [] ) = just ( CCK'-gen ∷ CCK'-gen ∷ [] , CX20-gen ∷ CS12-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CX20-CCK'-CCK'=CCK'-CCK'-CX20-CS12-CCZ) )
  spde1-act CCX0-gen [] = just ( [] , CCX0-gen ∷ [] , refl )
  spde1-act CCX0-gen (CCK'-gen ∷ [] ) = just ( CCK'-gen ∷ [] , CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-CCK'=CCK'-CCZ) )
  spde1-act CCX0-gen (CCK'-gen ∷ CCK'-gen ∷ [] ) = just ( CCK'-gen ∷ CCK'-gen ∷ [] , CCX0-gen ∷ CS12-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-CCK'-CCK'=CCK'-CCK'-CCX0-CS12-CCZ) )
  spde1-act S0-gen [] = just ( [] , S0-gen ∷ [] , refl )
  spde1-act S0-gen (CCK'-gen ∷ [] ) = just ( CCK'-gen ∷ CCK'-gen ∷ [] , S0-gen ∷ CS12-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-S0-CCK'=CCK'-CCK'-S0-CS12-CCZ) )
  spde1-act S0-gen (CCK'-gen ∷ CCK'-gen ∷ [] ) = just ( CCK'-gen ∷ [] , CCX0-gen ∷ S0-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-S0-CCK'-CCK'=CCK'-CCX0-S0-CCZ) )
  spde1-act S1-gen [] = just ( [] , S1-gen ∷ [] , refl )
  spde1-act S1-gen (CCK'-gen ∷ [] ) = just ( CCK'-gen ∷ [] , S1-gen ∷ [] , up-to-assoc auto (axiom ax-S1-CCK'=CCK'-S1) )
  spde1-act S1-gen (CCK'-gen ∷ CCK'-gen ∷ [] ) = just ( CCK'-gen ∷ CCK'-gen ∷ [] , S1-gen ∷ [] , up-to-assoc auto (axiom ax-S1-CCK'-CCK'=CCK'-CCK'-S1) )
  spde1-act S2-gen [] = just ( [] , S2-gen ∷ [] , refl )
  spde1-act S2-gen (CCK'-gen ∷ [] ) = just ( CCK'-gen ∷ [] , S2-gen ∷ [] , up-to-assoc auto (axiom ax-S2-CCK'=CCK'-S2) )
  spde1-act S2-gen (CCK'-gen ∷ CCK'-gen ∷ [] ) = just ( CCK'-gen ∷ CCK'-gen ∷ [] , S2-gen ∷ [] , up-to-assoc auto (axiom ax-S2-CCK'-CCK'=CCK'-CCK'-S2) )
  spde1-act CS01-gen [] = just ( [] , CS01-gen ∷ [] , refl )
  spde1-act CS01-gen (CCK'-gen ∷ [] ) = just ( CCK'-gen ∷ CCK'-gen ∷ [] , CS01-gen ∷ CS12-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CS01-CCK'=CCK'-CCK'-CS01-CS12-CCZ) )
  spde1-act CS01-gen (CCK'-gen ∷ CCK'-gen ∷ [] ) = just ( CCK'-gen ∷ [] , CCX0-gen ∷ CS01-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CS01-CCK'-CCK'=CCK'-CCX0-CS01-CCZ) )
  spde1-act CS02-gen [] = just ( [] , CS02-gen ∷ [] , refl )
  spde1-act CS02-gen (CCK'-gen ∷ [] ) = just ( CCK'-gen ∷ CCK'-gen ∷ [] , CS02-gen ∷ CS12-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CS02-CCK'=CCK'-CCK'-CS02-CS12-CCZ) )
  spde1-act CS02-gen (CCK'-gen ∷ CCK'-gen ∷ [] ) = just ( CCK'-gen ∷ [] , CCX0-gen ∷ CS02-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CS02-CCK'-CCK'=CCK'-CCX0-CS02-CCZ) )
  spde1-act CS12-gen [] = just ( [] , CS12-gen ∷ [] , refl )
  spde1-act CS12-gen (CCK'-gen ∷ [] ) = just ( CCK'-gen ∷ [] , CS12-gen ∷ [] , up-to-assoc auto (axiom ax-CS12-CCK'=CCK'-CS12) )
  spde1-act CS12-gen (CCK'-gen ∷ CCK'-gen ∷ [] ) = just ( CCK'-gen ∷ CCK'-gen ∷ [] , CS12-gen ∷ [] , up-to-assoc auto (axiom ax-CS12-CCK'-CCK'=CCK'-CCK'-CS12) )
  spde1-act CCZ-gen [] = just ( [] , CCZ-gen ∷ [] , refl )
  spde1-act CCZ-gen (CCK'-gen ∷ [] ) = just ( CCK'-gen ∷ [] , CCX0-gen ∷ CS12-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CCZ-CCK'=CCK'-CCX0-CS12-CCZ) )
  spde1-act CCZ-gen (CCK'-gen ∷ CCK'-gen ∷ [] ) = just ( CCK'-gen ∷ CCK'-gen ∷ [] , CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CCZ-CCK'-CCK'=CCK'-CCK'-CCX0) )
  spde1-act iI-gen [] = just ( [] , iI-gen ∷ [] , refl )
  spde1-act iI-gen (CCK'-gen ∷ [] ) = just ( CCK'-gen ∷ [] , iI-gen ∷ [] , up-to-assoc auto (axiom ax-iI-CCK'=CCK'-iI) )
  spde1-act iI-gen (CCK'-gen ∷ CCK'-gen ∷ [] ) = just ( CCK'-gen ∷ CCK'-gen ∷ [] , iI-gen ∷ [] , up-to-assoc auto (axiom ax-iI-CCK'-CCK'=CCK'-CCK'-iI) )
  spde1-act _ _ = nothing


  module E1 = CosAct (record { listnf = SPD.nfnh' ; lemma-listnf = SPD.lemma-nfnh' }) spde1-act (\ x y -> nothing)

  spde2-act : let X = Gate in let Γ = Rel in (g : X) -> (rep : List X) ->  Maybe (∃ λ (rep' : List X) -> ∃ λ (g' : List X) -> Γ ⊢ [ g ]ʷ • word-of-list rep === word-of-list (rep' ++ g'))
  spde2-act CK10-gen [] = just ( CK10-gen ∷ [] , [] , refl )
  spde2-act CK10-gen (CK10-gen ∷ [] ) = just ( [] , S1-gen ∷ S1-gen ∷ S1-gen ∷ [] , up-to-assoc auto (axiom ax-CK10-CK10=S1-S1-S1) )
  spde2-act CK10-gen (S0-gen ∷ CK10-gen ∷ [] ) = just ( S0-gen ∷ CK10-gen ∷ [] , CX10-gen ∷ CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ [] , up-to-assoc auto (axiom ax-CK10-S0-CK10=S0-CK10-CX10-CS01-CS01-CS01) )
  spde2-act CCK'-gen [] = just ( [] , CCK'-gen ∷ [] , refl )
  spde2-act CCK'-gen (CK10-gen ∷ [] ) = just ( CK10-gen ∷ [] , CCK'-gen ∷ CCK'-gen ∷ CCX0-gen ∷ CS12-gen ∷ [] , up-to-assoc auto (axiom ax-CCK'-CK10=CK10-CCK'-CCK'-CCX0-CS12) )
  spde2-act CCK'-gen (S0-gen ∷ CK10-gen ∷ [] ) = just ( S0-gen ∷ CK10-gen ∷ [] , CCK'-gen ∷ [] , up-to-assoc auto (axiom ax-CCK'-S0-CK10=S0-CK10-CCK') )
  spde2-act X0-gen [] = just ( [] , X0-gen ∷ [] , refl )
  spde2-act X0-gen (CK10-gen ∷ [] ) = just ( CK10-gen ∷ [] , X0-gen ∷ CX10-gen ∷ CS01-gen ∷ CS01-gen ∷ [] , up-to-assoc auto (axiom ax-X0-CK10=CK10-X0-CX10-CS01-CS01) )
  spde2-act X0-gen (S0-gen ∷ CK10-gen ∷ [] ) = just ( S0-gen ∷ CK10-gen ∷ [] , X0-gen ∷ S0-gen ∷ S0-gen ∷ S1-gen ∷ S1-gen ∷ iI-gen ∷ iI-gen ∷ iI-gen ∷ [] , up-to-assoc auto (axiom ax-X0-S0-CK10=S0-CK10-X0-S0-S0-S1-S1-iI-iI-iI) )
  spde2-act CX10-gen [] = just ( [] , CX10-gen ∷ [] , refl )
  spde2-act CX10-gen (CK10-gen ∷ [] ) = just ( CK10-gen ∷ [] , CS01-gen ∷ CS01-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-CK10=CK10-CS01-CS01) )
  spde2-act CX10-gen (S0-gen ∷ CK10-gen ∷ [] ) = just ( S0-gen ∷ CK10-gen ∷ [] , CX10-gen ∷ S1-gen ∷ CS01-gen ∷ CS01-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-S0-CK10=S0-CK10-CX10-S1-CS01-CS01) )
  spde2-act CX20-gen [] = just ( [] , CX20-gen ∷ [] , refl )
  spde2-act CX20-gen (CK10-gen ∷ [] ) = just ( CK10-gen ∷ [] , CX20-gen ∷ CCX0-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CX20-CK10=CK10-CX20-CCX0-CCZ) )
  spde2-act CX20-gen (S0-gen ∷ CK10-gen ∷ [] ) = just ( S0-gen ∷ CK10-gen ∷ [] , CX20-gen ∷ S2-gen ∷ S2-gen ∷ S2-gen ∷ CS02-gen ∷ CS02-gen ∷ CS12-gen ∷ CS12-gen ∷ [] , up-to-assoc auto (axiom ax-CX20-S0-CK10=S0-CK10-CX20-S2-S2-S2-CS02-CS02-CS12-CS12) )
  spde2-act CCX0-gen [] = just ( [] , CCX0-gen ∷ [] , refl )
  spde2-act CCX0-gen (CK10-gen ∷ [] ) = just ( CK10-gen ∷ [] , CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-CK10=CK10-CCZ) )
  spde2-act CCX0-gen (S0-gen ∷ CK10-gen ∷ [] ) = just ( S0-gen ∷ CK10-gen ∷ [] , CCX0-gen ∷ CS12-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-S0-CK10=S0-CK10-CCX0-CS12-CCZ) )
  spde2-act S0-gen [] = just ( [] , S0-gen ∷ [] , refl )
  spde2-act S0-gen (CK10-gen ∷ [] ) = just ( S0-gen ∷ CK10-gen ∷ [] , [] , refl )
  spde2-act S0-gen (S0-gen ∷ CK10-gen ∷ [] ) = just ( CK10-gen ∷ [] , CX10-gen ∷ S0-gen ∷ S0-gen ∷ CS01-gen ∷ CS01-gen ∷ [] , up-to-assoc auto (axiom ax-S0-S0-CK10=CK10-CX10-S0-S0-CS01-CS01) )
  spde2-act S1-gen [] = just ( [] , S1-gen ∷ [] , refl )
  spde2-act S1-gen (CK10-gen ∷ [] ) = just ( CK10-gen ∷ [] , S1-gen ∷ [] , up-to-assoc auto (axiom ax-S1-CK10=CK10-S1) )
  spde2-act S1-gen (S0-gen ∷ CK10-gen ∷ [] ) = just ( S0-gen ∷ CK10-gen ∷ [] , S1-gen ∷ [] , up-to-assoc auto (axiom ax-S1-S0-CK10=S0-CK10-S1) )
  spde2-act S2-gen [] = just ( [] , S2-gen ∷ [] , refl )
  spde2-act S2-gen (CK10-gen ∷ [] ) = just ( CK10-gen ∷ [] , S2-gen ∷ [] , up-to-assoc auto (axiom ax-S2-CK10=CK10-S2) )
  spde2-act S2-gen (S0-gen ∷ CK10-gen ∷ [] ) = just ( S0-gen ∷ CK10-gen ∷ [] , S2-gen ∷ [] , up-to-assoc auto (axiom ax-S2-S0-CK10=S0-CK10-S2) )
  spde2-act CS01-gen [] = just ( [] , CS01-gen ∷ [] , refl )
  spde2-act CS01-gen (CK10-gen ∷ [] ) = just ( S0-gen ∷ CK10-gen ∷ [] , S0-gen ∷ S0-gen ∷ S0-gen ∷ CS01-gen ∷ [] , up-to-assoc auto (axiom ax-CS01-CK10=S0-CK10-S0-S0-S0-CS01) )
  spde2-act CS01-gen (S0-gen ∷ CK10-gen ∷ [] ) = just ( CK10-gen ∷ [] , CX10-gen ∷ S0-gen ∷ CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ [] , up-to-assoc auto (axiom ax-CS01-S0-CK10=CK10-CX10-S0-CS01-CS01-CS01) )
  spde2-act CS02-gen [] = just ( [] , CS02-gen ∷ [] , refl )
  spde2-act CS02-gen (CK10-gen ∷ [] ) = just ( CK10-gen ∷ [] , CCK'-gen ∷ CCK'-gen ∷ CCX0-gen ∷ CS12-gen ∷ CS12-gen ∷ CS02-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CS02-CK10=CK10-CCK'-CCK'-CCX0-CS12-CS12-CS02-CCZ) )
  spde2-act CS02-gen (S0-gen ∷ CK10-gen ∷ [] ) = just ( S0-gen ∷ CK10-gen ∷ [] , CCK'-gen ∷ CCK'-gen ∷ CCX0-gen ∷ CS12-gen ∷ CS12-gen ∷ CS02-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CS02-S0-CK10=S0-CK10-CCK'-CCK'-CCX0-CS12-CS12-CS02-CCZ) )
  spde2-act CS12-gen [] = just ( [] , CS12-gen ∷ [] , refl )
  spde2-act CS12-gen (CK10-gen ∷ [] ) = just ( CK10-gen ∷ [] , CS12-gen ∷ [] , up-to-assoc auto (axiom ax-CS12-CK10=CK10-CS12) )
  spde2-act CS12-gen (S0-gen ∷ CK10-gen ∷ [] ) = just ( S0-gen ∷ CK10-gen ∷ [] , CS12-gen ∷ [] , up-to-assoc auto (axiom ax-CS12-S0-CK10=S0-CK10-CS12) )
  spde2-act CCZ-gen [] = just ( [] , CCZ-gen ∷ [] , refl )
  spde2-act CCZ-gen (CK10-gen ∷ [] ) = just ( CK10-gen ∷ [] , CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CCZ-CK10=CK10-CCX0) )
  spde2-act CCZ-gen (S0-gen ∷ CK10-gen ∷ [] ) = just ( S0-gen ∷ CK10-gen ∷ [] , CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CCZ-S0-CK10=S0-CK10-CCX0) )
  spde2-act iI-gen [] = just ( [] , iI-gen ∷ [] , refl )
  spde2-act iI-gen (CK10-gen ∷ [] ) = just ( CK10-gen ∷ [] , iI-gen ∷ [] , up-to-assoc auto (axiom ax-iI-CK10=CK10-iI) )
  spde2-act iI-gen (S0-gen ∷ CK10-gen ∷ [] ) = just ( S0-gen ∷ CK10-gen ∷ [] , iI-gen ∷ [] , up-to-assoc auto (axiom ax-iI-S0-CK10=S0-CK10-iI) )
  spde2-act _ _ = nothing

  module E2 = CosAct (record { listnf = E1.lactnf ; lemma-listnf = E1.lemma-lactnf }) spde2-act (\ x y -> nothing)

  spde3-act : let X = Gate in let Γ = Rel in (g : X) -> (rep : List X) ->  Maybe (∃ λ (rep' : List X) -> ∃ λ (g' : List X) -> Γ ⊢ [ g ]ʷ • word-of-list rep === word-of-list (rep' ++ g'))
  spde3-act CK20-gen [] = just ( CK20-gen ∷ [] , [] , refl )
  spde3-act CK20-gen (CK20-gen ∷ [] ) = just ( [] , S2-gen ∷ S2-gen ∷ S2-gen ∷ [] , up-to-assoc auto (axiom ax-CK20-CK20=S2-S2-S2) )
  spde3-act CK20-gen (S0-gen ∷ CK20-gen ∷ [] ) = just ( S0-gen ∷ CK20-gen ∷ [] , CX20-gen ∷ CS02-gen ∷ CS02-gen ∷ CS02-gen ∷ [] , up-to-assoc auto (axiom ax-CK20-S0-CK20=S0-CK20-CX20-CS02-CS02-CS02) )
  spde3-act CK10-gen [] = just ( [] , CK10-gen ∷ [] , refl )
  spde3-act CK10-gen (CK20-gen ∷ [] ) = just ( CK20-gen ∷ [] , CK10-gen ∷ [] , up-to-assoc auto (axiom ax-CK10-CK20=CK20-CK10) )
  spde3-act CK10-gen (S0-gen ∷ CK20-gen ∷ [] ) = just ( S0-gen ∷ CK20-gen ∷ [] , S0-gen ∷ CK10-gen ∷ CCK'-gen ∷ CX10-gen ∷ S0-gen ∷ S0-gen ∷ S0-gen ∷ CS01-gen ∷ CS01-gen ∷ CS12-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CK10-S0-CK20=S0-CK20-S0-CK10-CCK'-CX10-S0-S0-S0-CS01-CS01-CS12-CCZ) )
  spde3-act CCK'-gen [] = just ( [] , CCK'-gen ∷ [] , refl )
  spde3-act CCK'-gen (CK20-gen ∷ [] ) = just ( CK20-gen ∷ [] , CCK'-gen ∷ CCK'-gen ∷ CCX0-gen ∷ CS12-gen ∷ [] , up-to-assoc auto (axiom ax-CCK'-CK20=CK20-CCK'-CCK'-CCX0-CS12) )
  spde3-act CCK'-gen (S0-gen ∷ CK20-gen ∷ [] ) = just ( S0-gen ∷ CK20-gen ∷ [] , CCK'-gen ∷ [] , up-to-assoc auto (axiom ax-CCK'-S0-CK20=S0-CK20-CCK') )
  spde3-act X0-gen [] = just ( [] , X0-gen ∷ [] , refl )
  spde3-act X0-gen (CK20-gen ∷ [] ) = just ( CK20-gen ∷ [] , X0-gen ∷ CX20-gen ∷ CS02-gen ∷ CS02-gen ∷ [] , up-to-assoc auto (axiom ax-X0-CK20=CK20-X0-CX20-CS02-CS02) )
  spde3-act X0-gen (S0-gen ∷ CK20-gen ∷ [] ) = just ( S0-gen ∷ CK20-gen ∷ [] , X0-gen ∷ S0-gen ∷ S0-gen ∷ S2-gen ∷ S2-gen ∷ iI-gen ∷ iI-gen ∷ iI-gen ∷ [] , up-to-assoc auto (axiom ax-X0-S0-CK20=S0-CK20-X0-S0-S0-S2-S2-iI-iI-iI) )
  spde3-act CX10-gen [] = just ( [] , CX10-gen ∷ [] , refl )
  spde3-act CX10-gen (CK20-gen ∷ [] ) = just ( CK20-gen ∷ [] , CX10-gen ∷ CCX0-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-CK20=CK20-CX10-CCX0-CCZ) )
  spde3-act CX10-gen (S0-gen ∷ CK20-gen ∷ [] ) = just ( S0-gen ∷ CK20-gen ∷ [] , CX10-gen ∷ S1-gen ∷ S1-gen ∷ S1-gen ∷ CS01-gen ∷ CS01-gen ∷ CS12-gen ∷ CS12-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-S0-CK20=S0-CK20-CX10-S1-S1-S1-CS01-CS01-CS12-CS12) )
  spde3-act CX20-gen [] = just ( [] , CX20-gen ∷ [] , refl )
  spde3-act CX20-gen (CK20-gen ∷ [] ) = just ( CK20-gen ∷ [] , CS02-gen ∷ CS02-gen ∷ [] , up-to-assoc auto (axiom ax-CX20-CK20=CK20-CS02-CS02) )
  spde3-act CX20-gen (S0-gen ∷ CK20-gen ∷ [] ) = just ( S0-gen ∷ CK20-gen ∷ [] , CX20-gen ∷ S2-gen ∷ CS02-gen ∷ CS02-gen ∷ [] , up-to-assoc auto (axiom ax-CX20-S0-CK20=S0-CK20-CX20-S2-CS02-CS02) )
  spde3-act CCX0-gen [] = just ( [] , CCX0-gen ∷ [] , refl )
  spde3-act CCX0-gen (CK20-gen ∷ [] ) = just ( CK20-gen ∷ [] , CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-CK20=CK20-CCZ) )
  spde3-act CCX0-gen (S0-gen ∷ CK20-gen ∷ [] ) = just ( S0-gen ∷ CK20-gen ∷ [] , CCX0-gen ∷ CS12-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-S0-CK20=S0-CK20-CCX0-CS12-CCZ) )
  spde3-act S0-gen [] = just ( [] , S0-gen ∷ [] , refl )
  spde3-act S0-gen (CK20-gen ∷ [] ) = just ( S0-gen ∷ CK20-gen ∷ [] , [] , refl )
  spde3-act S0-gen (S0-gen ∷ CK20-gen ∷ [] ) = just ( CK20-gen ∷ [] , CX20-gen ∷ S0-gen ∷ S0-gen ∷ CS02-gen ∷ CS02-gen ∷ [] , up-to-assoc auto (axiom ax-S0-S0-CK20=CK20-CX20-S0-S0-CS02-CS02) )
  spde3-act S1-gen [] = just ( [] , S1-gen ∷ [] , refl )
  spde3-act S1-gen (CK20-gen ∷ [] ) = just ( CK20-gen ∷ [] , S1-gen ∷ [] , up-to-assoc auto (axiom ax-S1-CK20=CK20-S1) )
  spde3-act S1-gen (S0-gen ∷ CK20-gen ∷ [] ) = just ( S0-gen ∷ CK20-gen ∷ [] , S1-gen ∷ [] , up-to-assoc auto (axiom ax-S1-S0-CK20=S0-CK20-S1) )
  spde3-act S2-gen [] = just ( [] , S2-gen ∷ [] , refl )
  spde3-act S2-gen (CK20-gen ∷ [] ) = just ( CK20-gen ∷ [] , S2-gen ∷ [] , up-to-assoc auto (axiom ax-S2-CK20=CK20-S2) )
  spde3-act S2-gen (S0-gen ∷ CK20-gen ∷ [] ) = just ( S0-gen ∷ CK20-gen ∷ [] , S2-gen ∷ [] , up-to-assoc auto (axiom ax-S2-S0-CK20=S0-CK20-S2) )
  spde3-act CS01-gen [] = just ( [] , CS01-gen ∷ [] , refl )
  spde3-act CS01-gen (CK20-gen ∷ [] ) = just ( CK20-gen ∷ [] , CCK'-gen ∷ CCK'-gen ∷ CCX0-gen ∷ CS12-gen ∷ CS12-gen ∷ CS01-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CS01-CK20=CK20-CCK'-CCK'-CCX0-CS12-CS12-CS01-CCZ) )
  spde3-act CS01-gen (S0-gen ∷ CK20-gen ∷ [] ) = just ( S0-gen ∷ CK20-gen ∷ [] , CCK'-gen ∷ CCK'-gen ∷ CCX0-gen ∷ CS12-gen ∷ CS12-gen ∷ CS01-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CS01-S0-CK20=S0-CK20-CCK'-CCK'-CCX0-CS12-CS12-CS01-CCZ) )
  spde3-act CS02-gen [] = just ( [] , CS02-gen ∷ [] , refl )
  spde3-act CS02-gen (CK20-gen ∷ [] ) = just ( S0-gen ∷ CK20-gen ∷ [] , S0-gen ∷ S0-gen ∷ S0-gen ∷ CS02-gen ∷ [] , up-to-assoc auto (axiom ax-CS02-CK20=S0-CK20-S0-S0-S0-CS02) )
  spde3-act CS02-gen (S0-gen ∷ CK20-gen ∷ [] ) = just ( CK20-gen ∷ [] , CX20-gen ∷ S0-gen ∷ CS02-gen ∷ CS02-gen ∷ CS02-gen ∷ [] , up-to-assoc auto (axiom ax-CS02-S0-CK20=CK20-CX20-S0-CS02-CS02-CS02) )
  spde3-act CS12-gen [] = just ( [] , CS12-gen ∷ [] , refl )
  spde3-act CS12-gen (CK20-gen ∷ [] ) = just ( CK20-gen ∷ [] , CS12-gen ∷ [] , up-to-assoc auto (axiom ax-CS12-CK20=CK20-CS12) )
  spde3-act CS12-gen (S0-gen ∷ CK20-gen ∷ [] ) = just ( S0-gen ∷ CK20-gen ∷ [] , CS12-gen ∷ [] , up-to-assoc auto (axiom ax-CS12-S0-CK20=S0-CK20-CS12) )
  spde3-act CCZ-gen [] = just ( [] , CCZ-gen ∷ [] , refl )
  spde3-act CCZ-gen (CK20-gen ∷ [] ) = just ( CK20-gen ∷ [] , CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CCZ-CK20=CK20-CCX0) )
  spde3-act CCZ-gen (S0-gen ∷ CK20-gen ∷ [] ) = just ( S0-gen ∷ CK20-gen ∷ [] , CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CCZ-S0-CK20=S0-CK20-CCX0) )
  spde3-act iI-gen [] = just ( [] , iI-gen ∷ [] , refl )
  spde3-act iI-gen (CK20-gen ∷ [] ) = just ( CK20-gen ∷ [] , iI-gen ∷ [] , up-to-assoc auto (axiom ax-iI-CK20=CK20-iI) )
  spde3-act iI-gen (S0-gen ∷ CK20-gen ∷ [] ) = just ( S0-gen ∷ CK20-gen ∷ [] , iI-gen ∷ [] , up-to-assoc auto (axiom ax-iI-S0-CK20=S0-CK20-iI) )
  spde3-act _ _ = nothing

  module E3 = CosAct (record { listnf = E2.lactnf ; lemma-listnf = E2.lemma-lactnf }) spde3-act (\ x y -> nothing)

  spde4-act : let X = Gate in let Γ = Rel in (g : X) -> (rep : List X) ->  Maybe (∃ λ (rep' : List X) -> ∃ λ (g' : List X) -> Γ ⊢ [ g ]ʷ • word-of-list rep === word-of-list (rep' ++ g'))
  spde4-act K0-gen [] = just ( K0-gen ∷ [] , [] , refl )
  spde4-act K0-gen (K0-gen ∷ [] ) = just ( [] , iI-gen ∷ iI-gen ∷ iI-gen ∷ [] , up-to-assoc auto (axiom ax-K0-K0=iI-iI-iI) )
  spde4-act K0-gen (S0-gen ∷ K0-gen ∷ [] ) = just ( S0-gen ∷ K0-gen ∷ [] , X0-gen ∷ S0-gen ∷ S0-gen ∷ S0-gen ∷ [] , up-to-assoc auto (axiom ax-K0-S0-K0=S0-K0-X0-S0-S0-S0) )
  spde4-act CK20-gen [] = just ( [] , CK20-gen ∷ [] , refl )
  spde4-act CK20-gen (K0-gen ∷ [] ) = just ( K0-gen ∷ [] , CK20-gen ∷ [] , up-to-assoc auto (axiom ax-CK20-K0=K0-CK20) )
  spde4-act CK20-gen (S0-gen ∷ K0-gen ∷ [] ) = just ( S0-gen ∷ K0-gen ∷ [] , CX20-gen ∷ CS02-gen ∷ CS02-gen ∷ CS02-gen ∷ [] , up-to-assoc auto (axiom ax-CK20-S0-K0=S0-K0-CX20-CS02-CS02-CS02) )
  spde4-act CK10-gen [] = just ( [] , CK10-gen ∷ [] , refl )
  spde4-act CK10-gen (K0-gen ∷ [] ) = just ( K0-gen ∷ [] , CK10-gen ∷ [] , up-to-assoc auto (axiom ax-CK10-K0=K0-CK10) )
  spde4-act CK10-gen (S0-gen ∷ K0-gen ∷ [] ) = just ( S0-gen ∷ K0-gen ∷ [] , CX10-gen ∷ CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ [] , up-to-assoc auto (axiom ax-CK10-S0-K0=S0-K0-CX10-CS01-CS01-CS01) )
  spde4-act CCK'-gen [] = just ( [] , CCK'-gen ∷ [] , refl )
  spde4-act CCK'-gen (K0-gen ∷ [] ) = just ( K0-gen ∷ [] , CCK'-gen ∷ CCK'-gen ∷ CCX0-gen ∷ CS12-gen ∷ [] , up-to-assoc auto (axiom ax-CCK'-K0=K0-CCK'-CCK'-CCX0-CS12) )
  spde4-act CCK'-gen (S0-gen ∷ K0-gen ∷ [] ) = just ( S0-gen ∷ K0-gen ∷ [] , CCK'-gen ∷ [] , up-to-assoc auto (axiom ax-CCK'-S0-K0=S0-K0-CCK') )
  spde4-act X0-gen [] = just ( [] , X0-gen ∷ [] , refl )
  spde4-act X0-gen (K0-gen ∷ [] ) = just ( K0-gen ∷ [] , S0-gen ∷ S0-gen ∷ [] , up-to-assoc auto (axiom ax-X0-K0=K0-S0-S0) )
  spde4-act X0-gen (S0-gen ∷ K0-gen ∷ [] ) = just ( S0-gen ∷ K0-gen ∷ [] , X0-gen ∷ S0-gen ∷ S0-gen ∷ iI-gen ∷ [] , up-to-assoc auto (axiom ax-X0-S0-K0=S0-K0-X0-S0-S0-iI) )
  spde4-act CX10-gen [] = just ( [] , CX10-gen ∷ [] , refl )
  spde4-act CX10-gen (K0-gen ∷ [] ) = just ( K0-gen ∷ [] , CS01-gen ∷ CS01-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-K0=K0-CS01-CS01) )
  spde4-act CX10-gen (S0-gen ∷ K0-gen ∷ [] ) = just ( S0-gen ∷ K0-gen ∷ [] , CX10-gen ∷ S1-gen ∷ CS01-gen ∷ CS01-gen ∷ [] , up-to-assoc auto (axiom ax-CX10-S0-K0=S0-K0-CX10-S1-CS01-CS01) )
  spde4-act CX20-gen [] = just ( [] , CX20-gen ∷ [] , refl )
  spde4-act CX20-gen (K0-gen ∷ [] ) = just ( K0-gen ∷ [] , CS02-gen ∷ CS02-gen ∷ [] , up-to-assoc auto (axiom ax-CX20-K0=K0-CS02-CS02) )
  spde4-act CX20-gen (S0-gen ∷ K0-gen ∷ [] ) = just ( S0-gen ∷ K0-gen ∷ [] , CX20-gen ∷ S2-gen ∷ CS02-gen ∷ CS02-gen ∷ [] , up-to-assoc auto (axiom ax-CX20-S0-K0=S0-K0-CX20-S2-CS02-CS02) )
  spde4-act CCX0-gen [] = just ( [] , CCX0-gen ∷ [] , refl )
  spde4-act CCX0-gen (K0-gen ∷ [] ) = just ( K0-gen ∷ [] , CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-K0=K0-CCZ) )
  spde4-act CCX0-gen (S0-gen ∷ K0-gen ∷ [] ) = just ( S0-gen ∷ K0-gen ∷ [] , CCX0-gen ∷ CS12-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CCX0-S0-K0=S0-K0-CCX0-CS12-CCZ) )
  spde4-act S0-gen [] = just ( [] , S0-gen ∷ [] , refl )
  spde4-act S0-gen (K0-gen ∷ [] ) = just ( S0-gen ∷ K0-gen ∷ [] , [] , refl )
  spde4-act S0-gen (S0-gen ∷ K0-gen ∷ [] ) = just ( K0-gen ∷ [] , X0-gen ∷ [] , up-to-assoc auto (axiom ax-S0-S0-K0=K0-X0) )
  spde4-act S1-gen [] = just ( [] , S1-gen ∷ [] , refl )
  spde4-act S1-gen (K0-gen ∷ [] ) = just ( K0-gen ∷ [] , S1-gen ∷ [] , up-to-assoc auto (axiom ax-S1-K0=K0-S1) )
  spde4-act S1-gen (S0-gen ∷ K0-gen ∷ [] ) = just ( S0-gen ∷ K0-gen ∷ [] , S1-gen ∷ [] , up-to-assoc auto (axiom ax-S1-S0-K0=S0-K0-S1) )
  spde4-act S2-gen [] = just ( [] , S2-gen ∷ [] , refl )
  spde4-act S2-gen (K0-gen ∷ [] ) = just ( K0-gen ∷ [] , S2-gen ∷ [] , up-to-assoc auto (axiom ax-S2-K0=K0-S2) )
  spde4-act S2-gen (S0-gen ∷ K0-gen ∷ [] ) = just ( S0-gen ∷ K0-gen ∷ [] , S2-gen ∷ [] , up-to-assoc auto (axiom ax-S2-S0-K0=S0-K0-S2) )
  spde4-act CS01-gen [] = just ( [] , CS01-gen ∷ [] , refl )
  spde4-act CS01-gen (K0-gen ∷ [] ) = just ( K0-gen ∷ [] , S0-gen ∷ CK10-gen ∷ CX10-gen ∷ S0-gen ∷ S0-gen ∷ S0-gen ∷ S1-gen ∷ [] , up-to-assoc auto (axiom ax-CS01-K0=K0-S0-CK10-CX10-S0-S0-S0-S1) )
  spde4-act CS01-gen (S0-gen ∷ K0-gen ∷ [] ) = just ( S0-gen ∷ K0-gen ∷ [] , S0-gen ∷ CK10-gen ∷ CX10-gen ∷ S0-gen ∷ S0-gen ∷ S0-gen ∷ S1-gen ∷ [] , up-to-assoc auto (axiom ax-CS01-S0-K0=S0-K0-S0-CK10-CX10-S0-S0-S0-S1) )
  spde4-act CS02-gen [] = just ( [] , CS02-gen ∷ [] , refl )
  spde4-act CS02-gen (K0-gen ∷ [] ) = just ( K0-gen ∷ [] , S0-gen ∷ CK20-gen ∷ CX20-gen ∷ S0-gen ∷ S0-gen ∷ S0-gen ∷ S2-gen ∷ [] , up-to-assoc auto (axiom ax-CS02-K0=K0-S0-CK20-CX20-S0-S0-S0-S2) )
  spde4-act CS02-gen (S0-gen ∷ K0-gen ∷ [] ) = just ( S0-gen ∷ K0-gen ∷ [] , S0-gen ∷ CK20-gen ∷ CX20-gen ∷ S0-gen ∷ S0-gen ∷ S0-gen ∷ S2-gen ∷ [] , up-to-assoc auto (axiom ax-CS02-S0-K0=S0-K0-S0-CK20-CX20-S0-S0-S0-S2) )
  spde4-act CS12-gen [] = just ( [] , CS12-gen ∷ [] , refl )
  spde4-act CS12-gen (K0-gen ∷ [] ) = just ( K0-gen ∷ [] , CS12-gen ∷ [] , up-to-assoc auto (axiom ax-CS12-K0=K0-CS12) )
  spde4-act CS12-gen (S0-gen ∷ K0-gen ∷ [] ) = just ( S0-gen ∷ K0-gen ∷ [] , CS12-gen ∷ [] , up-to-assoc auto (axiom ax-CS12-S0-K0=S0-K0-CS12) )
  spde4-act CCZ-gen [] = just ( [] , CCZ-gen ∷ [] , refl )
  spde4-act CCZ-gen (K0-gen ∷ [] ) = just ( K0-gen ∷ [] , CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CCZ-K0=K0-CCX0) )
  spde4-act CCZ-gen (S0-gen ∷ K0-gen ∷ [] ) = just ( S0-gen ∷ K0-gen ∷ [] , CCX0-gen ∷ [] , up-to-assoc auto (axiom ax-CCZ-S0-K0=S0-K0-CCX0) )
  spde4-act iI-gen [] = just ( [] , iI-gen ∷ [] , refl )
  spde4-act iI-gen (K0-gen ∷ [] ) = just ( K0-gen ∷ [] , iI-gen ∷ [] , up-to-assoc auto (axiom ax-iI-K0=K0-iI) )
  spde4-act iI-gen (S0-gen ∷ K0-gen ∷ [] ) = just ( S0-gen ∷ K0-gen ∷ [] , iI-gen ∷ [] , up-to-assoc auto (axiom ax-iI-S0-K0=S0-K0-iI) )
  spde4-act _ _ = nothing

  module E4 = CosAct (record { listnf = E3.lactnf ; lemma-listnf = E3.lemma-lactnf }) spde4-act (\ x y -> nothing)
  

  p24-spde4-conj : let X = Gate in let Γ = Rel in (h n : X) -> Maybe (∃ λ (n' : List X) -> Γ ⊢ [ h ]ʷ • [ n ]ʷ === word-of-list n' • [ h ]ʷ)
  p24-spde4-conj X1-gen K0-gen = just ( K0-gen ∷ [] , up-to-assoc auto (axiom ax-X1-K0=K0-X1) )
  p24-spde4-conj X1-gen CK20-gen = just ( CK20-gen ∷ [] , up-to-assoc auto (axiom ax-X1-CK20=CK20-X1) )
  p24-spde4-conj X1-gen CK10-gen = just ( K0-gen ∷ CK10-gen ∷ S1-gen ∷ [] , up-to-assoc auto (axiom ax-X1-CK10=K0-CK10-S1-X1) )
  p24-spde4-conj X1-gen CCK'-gen = just ( CK20-gen ∷ CCK'-gen ∷ CS02-gen ∷ CS02-gen ∷ CS02-gen ∷ CS12-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-X1-CCK'=CK20-CCK'-CS02-CS02-CS02-CS12-CCZ-X1) )
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
  p24-spde4-conj X2-gen CK20-gen = just ( K0-gen ∷ CK20-gen ∷ S2-gen ∷ [] , up-to-assoc auto (axiom ax-X2-CK20=K0-CK20-S2-X2) )
  p24-spde4-conj X2-gen CK10-gen = just ( CK10-gen ∷ [] , up-to-assoc auto (axiom ax-X2-CK10=CK10-X2) )
  p24-spde4-conj X2-gen CCK'-gen = just ( CK10-gen ∷ CCK'-gen ∷ CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ CS12-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-X2-CCK'=CK10-CCK'-CS01-CS01-CS01-CS12-CCZ-X2) )
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
  p24-spde4-conj CX12-gen CK20-gen = just ( CK20-gen ∷ CK10-gen ∷ CS12-gen ∷ [] , up-to-assoc auto (axiom ax-CX12-CK20=CK20-CK10-CS12-CX12) )
  p24-spde4-conj CX12-gen CK10-gen = just ( CK10-gen ∷ [] , up-to-assoc auto (axiom ax-CX12-CK10=CK10-CX12) )
  p24-spde4-conj CX12-gen CCK'-gen = just ( CK10-gen ∷ CCK'-gen ∷ CS01-gen ∷ CS01-gen ∷ CS01-gen ∷ CS12-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CX12-CCK'=CK10-CCK'-CS01-CS01-CS01-CS12-CCZ-CX12) )
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
  p24-spde4-conj CX21-gen CK20-gen = just ( CK20-gen ∷ [] , up-to-assoc auto (axiom ax-CX21-CK20=CK20-CX21) )
  p24-spde4-conj CX21-gen CK10-gen = just ( CK20-gen ∷ CK10-gen ∷ CS12-gen ∷ [] , up-to-assoc auto (axiom ax-CX21-CK10=CK20-CK10-CS12-CX21) )
  p24-spde4-conj CX21-gen CCK'-gen = just ( CK20-gen ∷ CCK'-gen ∷ CS02-gen ∷ CS02-gen ∷ CS02-gen ∷ CS12-gen ∷ CCZ-gen ∷ [] , up-to-assoc auto (axiom ax-CX21-CCK'=CK20-CCK'-CS02-CS02-CS02-CS12-CCZ-CX21) )
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
  p24-spde4-conj Swap12-gen CK20-gen = just ( CK10-gen ∷ [] , up-to-assoc auto (axiom ax-Swap12-CK20=CK10-Swap12) )
  p24-spde4-conj Swap12-gen CK10-gen = just ( CK20-gen ∷ [] , up-to-assoc auto (axiom ax-Swap12-CK10=CK20-Swap12) )
  p24-spde4-conj Swap12-gen CCK'-gen = just ( CCK'-gen ∷ [] , up-to-assoc auto (axiom ax-Swap12-CCK'=CCK'-Swap12) )
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

  mvD3-step : Step-Function Gate Rel
  mvD3-step (S1-gen ∷ S0-gen ∷ xs) = just (S0-gen ∷ S1-gen ∷ xs , at-head (axiom ax-S1-S0=S0-S1))
  mvD3-step (S1-gen ∷ CK10-gen ∷ xs) = just (CK10-gen ∷ S1-gen ∷ xs , at-head (axiom ax-S1-CK10=CK10-S1))
  mvD3-step (S1-gen ∷ CK20-gen ∷ xs) = just (CK20-gen ∷ S1-gen ∷ xs , at-head (axiom ax-S1-CK20=CK20-S1))
  mvD3-step (S1-gen ∷ CCK'-gen ∷ xs) = just (CCK'-gen ∷ S1-gen ∷ xs , at-head (axiom ax-S1-CCK'=CCK'-S1))
  mvD3-step (S1-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ S1-gen ∷ xs , at-head (axiom ax-S1-K0=K0-S1))
  mvD3-step (S2-gen ∷ S0-gen ∷ xs) = just (S0-gen ∷ S2-gen ∷ xs , at-head (axiom ax-S2-S0=S0-S2))
  mvD3-step (S2-gen ∷ CK10-gen ∷ xs) = just (CK10-gen ∷ S2-gen ∷ xs , at-head (axiom ax-S2-CK10=CK10-S2))
  mvD3-step (S2-gen ∷ CK20-gen ∷ xs) = just (CK20-gen ∷ S2-gen ∷ xs , at-head (axiom ax-S2-CK20=CK20-S2))
  mvD3-step (S2-gen ∷ CCK'-gen ∷ xs) = just (CCK'-gen ∷ S2-gen ∷ xs , at-head (axiom ax-S2-CCK'=CCK'-S2))
  mvD3-step (S2-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ S2-gen ∷ xs , at-head (axiom ax-S2-K0=K0-S2))
  mvD3-step (CS12-gen ∷ S0-gen ∷ xs) = just (S0-gen ∷ CS12-gen ∷ xs , at-head (axiom ax-CS12-S0=S0-CS12))
  mvD3-step (CS12-gen ∷ CK10-gen ∷ xs) = just (CK10-gen ∷ CS12-gen ∷ xs , at-head (axiom ax-CS12-CK10=CK10-CS12))
  mvD3-step (CS12-gen ∷ CK20-gen ∷ xs) = just (CK20-gen ∷ CS12-gen ∷ xs , at-head (axiom ax-CS12-CK20=CK20-CS12))
  mvD3-step (CS12-gen ∷ CCK'-gen ∷ xs) = just (CCK'-gen ∷ CS12-gen ∷ xs , at-head (axiom ax-CS12-CCK'=CCK'-CS12))
  mvD3-step (CS12-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ CS12-gen ∷ xs , at-head (axiom ax-CS12-K0=K0-CS12))
  mvD3-step (Swap12-gen ∷ S0-gen ∷ xs) = just (S0-gen ∷ Swap12-gen ∷ xs , at-head (axiom ax-Swap12-S0=S0-Swap12))
  mvD3-step (Swap12-gen ∷ CCK'-gen ∷ xs) = just (CCK'-gen ∷ Swap12-gen ∷ xs , at-head (axiom ax-Swap12-CCK'=CCK'-Swap12))
  mvD3-step (Swap12-gen ∷ K0-gen ∷ xs) = just (K0-gen ∷ Swap12-gen ∷ xs , at-head (axiom ax-Swap12-K0=K0-Swap12))
  mvD3-step (Swap12-gen ∷ CK10-gen ∷ xs) = just (CK20-gen ∷ Swap12-gen ∷ xs , at-head (axiom ax-Swap12-CK10=CK20-Swap12))
  mvD3-step (Swap12-gen ∷ CK20-gen ∷ xs) = just (CK10-gen ∷ Swap12-gen ∷ xs , at-head (axiom ax-Swap12-CK20=CK10-Swap12))
  mvD3-step (CK10-gen ∷ CK20-gen ∷ xs) = just (CK20-gen ∷ CK10-gen ∷ xs , at-head (axiom ax-CK10-CK20=CK20-CK10))
  mvD3-step _ = nothing

  module mvD3 = Rewriting.Step (step-cong mvD3-step)

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
  isk0spd CCK'-gen = true
  isk0spd CK10-gen = true
  isk0spd CK20-gen = true
  isk0spd K0-gen = true
  isk0spd x = isD x

  isPD : Gate -> Bool
  isPD x = isP x ∨ isD x

  nfp24 : ListNF Rel
  nfp24 = record { listnf = P24.multistep 1000 ; lemma-listnf = P24.lemma-multistep 1000 }

  nfk0spd : ListNF Rel
  nfk0spd = record { listnf = E4.lactnf ; lemma-listnf = E4.lemma-lactnf }

  module P24K0D = SemiDirect isP24 isk0spd nfp24 nfk0spd group-like p24-spde4-conj

  nf-p24k0d : ListNF Rel
  nf-p24k0d = record { listnf = P24K0D.nfnh' ; lemma-listnf = P24K0D.lemma-nfnh' }

  nf-kpd : ListNF Rel
  nf-kpd = rep 3 (extend-nf isk0spd nf-p24k0d ∘ extend-nf isPD nf-pd)

  nf-de : ListNF Rel
  nf-de = extend-nf isD nfd


  nf-e4 : ListNF Rel
  nf-e4 = record { listnf = E4.lactnf ; lemma-listnf = E4.lemma-lactnf }

  nf-e3 : ListNF Rel
  nf-e3 = record { listnf = E3.lactnf ; lemma-listnf = E3.lemma-lactnf }

  nf-e2 : ListNF Rel
  nf-e2 = record { listnf = E2.lactnf ; lemma-listnf = E2.lemma-lactnf }

  nf-e1 : ListNF Rel
  nf-e1 = record { listnf = E1.lactnf ; lemma-listnf = E1.lemma-lactnf }

  isSPD : Gate -> Bool
  isSPD CCX0-gen = true
  isSPD CX10-gen = true
  isSPD CX20-gen = true
  isSPD X0-gen = true
  isSPD x = isD x

  isE1 : Gate -> Bool
  isE1 CCK'-gen = true
  isE1 x = isSPD x

  isE2 : Gate -> Bool
  isE2 CK10-gen = true
  isE2 x = isE1 x

  isE3 : Gate -> Bool
  isE3 CK20-gen = true
  isE3 x = isE2 x

  isE4 : Gate -> Bool
  isE4 K0-gen = true
  isE4 x = isE3 x

  nf-e4e : ListNF Rel
  nf-e4e = extend-nf isE4 nf-e4

  nf-e3e : ListNF Rel
  nf-e3e = extend-nf isE3 nf-e3


