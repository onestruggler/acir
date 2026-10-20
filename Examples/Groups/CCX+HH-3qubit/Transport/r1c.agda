{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Transport.r1c where

open import Data.Empty using (⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Nat.Base using (s≤s ; z≤n)
import Data.Nat.Properties as NP
import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.FrameWords
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r1c.P0 as P0
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r1c.P1 as P1
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r1c.P2 as P2
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r1c.P3 as P3
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r1c.P4 as P4
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r1c.P5 as P5
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r1c.P6 as P6
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r1c.P7 as P7

translate : (a b c d : Fin 8) →
  .(p0 : a < b) →
  .(p1 : b < c) →
  .(p2 : c < d) →
  (dK a b c d) • (dK a b c d) ≈ ε
translate (zero) b c d p0 p1 p2 = P0.translate b c d p0 p1 p2
translate (suc (zero)) b c d p0 p1 p2 = P1.translate b c d p0 p1 p2
translate (suc (suc (zero))) b c d p0 p1 p2 = P2.translate b c d p0 p1 p2
translate (suc (suc (suc (zero)))) b c d p0 p1 p2 = P3.translate b c d p0 p1 p2
translate (suc (suc (suc (suc (zero))))) b c d p0 p1 p2 = P4.translate b c d p0 p1 p2
translate (suc (suc (suc (suc (suc (zero)))))) b c d p0 p1 p2 = P5.translate b c d p0 p1 p2
translate (suc (suc (suc (suc (suc (suc (zero))))))) b c d p0 p1 p2 = P6.translate b c d p0 p1 p2
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) b c d p0 p1 p2 = P7.translate b c d p0 p1 p2
