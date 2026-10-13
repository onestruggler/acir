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
import Examples.Groups.CCX+HH-3qubit.TransportCases.r1b_ij0 as C0
import Examples.Groups.CCX+HH-3qubit.TransportCases.r1b_ij1 as C1
import Examples.Groups.CCX+HH-3qubit.TransportCases.r1b_ij2 as C2
import Examples.Groups.CCX+HH-3qubit.TransportCases.r1b_ij3 as C3
import Examples.Groups.CCX+HH-3qubit.TransportCases.r1b_ij4 as C4
import Examples.Groups.CCX+HH-3qubit.TransportCases.r1b_ij5 as C5
import Examples.Groups.CCX+HH-3qubit.TransportCases.r1b_ij6 as C6
import Examples.Groups.CCX+HH-3qubit.TransportCases.r1b_ij7 as C7

translate : (a : Fin 8) →
  (dM a) • (dM a) ≈ ε
translate (zero) = C0.proved
translate (suc (zero)) = C1.proved
translate (suc (suc (zero))) = C2.proved
translate (suc (suc (suc (zero)))) = C3.proved
translate (suc (suc (suc (suc (zero))))) = C4.proved
translate (suc (suc (suc (suc (suc (zero)))))) = C5.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) = C6.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) = C7.proved
