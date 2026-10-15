{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportChunks.r6a.P0126 where

open import Data.Empty using (⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Nat.Base using (s≤s ; z≤n)
import Data.Nat.Properties as NP
import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.FrameWords

private
  a b c d : Fin 8
  a = (zero)
  b = (suc (zero))
  c = (suc (suc (zero)))
  d = (suc (suc (suc (suc (suc (suc (zero)))))))

translate : (e f g h : Fin 8) →
  .(p0 : a < b) →
  .(p1 : b < c) →
  .(p2 : c < d) →
  .(p3 : d < e) →
  .(p4 : e < f) →
  .(p5 : f < g) →
  .(p6 : g < h) →
  .(p7 : a < e) →
  (dM a) • (dM e) • (dX a e) • (dK e f g h) • (dK a b c d) • (dX d e) • (dK a b c d) • (dK e f g h) • (dX a e) • (dM a) • (dM e) ≈ (dK e f g h) • (dK a b c d) • (dX d e) • (dK a b c d) • (dK e f g h)
translate (zero) f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p3)
translate (suc (zero)) f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p3)
translate (suc (suc (zero))) f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p3)
translate (suc (suc (suc (zero)))) f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p3)
translate (suc (suc (suc (suc (zero))))) f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p3)
translate (suc (suc (suc (suc (suc (zero)))))) f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p3)
translate (suc (suc (suc (suc (suc (suc (zero))))))) f g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p3)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ z≤n p4)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p4)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p4)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p4)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p4)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p4)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p4)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) g h p0 p1 p2 p3 p4 p5 p6 p7 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p4)
