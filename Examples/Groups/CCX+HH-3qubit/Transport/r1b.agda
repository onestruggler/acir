{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Transport.r1b where

open import Data.Empty using (⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Nat.Base using (s≤s ; z≤n)
import Data.Nat.Properties as NP
import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.FrameWords
open import Examples.Groups.CCX+HH-3qubit.TransportCases.r1b_B00 using (module r1b_ij0 ; module r1b_ij1 ; module r1b_ij2 ; module r1b_ij3 ; module r1b_ij4 ; module r1b_ij5 ; module r1b_ij6 ; module r1b_ij7)

translate : (a : Fin 8) →
  (dM a) • (dM a) ≈ ε
translate (zero) = r1b_ij0.proved
translate (suc (zero)) = r1b_ij1.proved
translate (suc (suc (zero))) = r1b_ij2.proved
translate (suc (suc (suc (zero)))) = r1b_ij3.proved
translate (suc (suc (suc (suc (zero))))) = r1b_ij4.proved
translate (suc (suc (suc (suc (suc (zero)))))) = r1b_ij5.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) = r1b_ij6.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = r1b_ij7.proved
