{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Transport.r4c where

open import Data.Empty using (⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Nat.Base using (s≤s ; z≤n)
import Data.Nat.Properties as NP
import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.FrameWords
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r4c.P0 as P0
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r4c.P1 as P1
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r4c.P2 as P2
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r4c.P3 as P3
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r4c.P4 as P4
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r4c.P5 as P5
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r4c.P6 as P6
import Examples.Groups.CCX+HH-3qubit.TransportChunks.r4c.P7 as P7

translate : (a b c d : Fin 8) →
  .(p0 : a < b) →
  .(p1 : b < c) →
  .(p2 : c < d) →
  .(p3 : b < d) →
  (dX c d) • (dK a b c d) ≈ (dK a b c d) • (dX b d)
translate (zero) b c d p0 p1 p2 p3 = P0.translate b c d p0 p1 p2 p3
translate (suc (zero)) b c d p0 p1 p2 p3 = P1.translate b c d p0 p1 p2 p3
translate (suc (suc (zero))) b c d p0 p1 p2 p3 = P2.translate b c d p0 p1 p2 p3
translate (suc (suc (suc (zero)))) b c d p0 p1 p2 p3 = P3.translate b c d p0 p1 p2 p3
translate (suc (suc (suc (suc (zero))))) b c d p0 p1 p2 p3 = P4.translate b c d p0 p1 p2 p3
translate (suc (suc (suc (suc (suc (zero)))))) b c d p0 p1 p2 p3 = P5.translate b c d p0 p1 p2 p3
translate (suc (suc (suc (suc (suc (suc (zero))))))) b c d p0 p1 p2 p3 = P6.translate b c d p0 p1 p2 p3
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) b c d p0 p1 p2 p3 = P7.translate b c d p0 p1 p2 p3
