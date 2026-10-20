{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportChunks.r2a.P4 where

open import Data.Empty using (⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Nat.Base using (s≤s ; z≤n)
import Data.Nat.Properties as NP
import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.FrameWords
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4501 as C4501
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4502 as C4502
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4503 as C4503
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4506 as C4506
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4507 as C4507
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4512 as C4512
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4513 as C4513
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4516 as C4516
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4517 as C4517
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4523 as C4523
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4526 as C4526
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4527 as C4527
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4536 as C4536
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4537 as C4537
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4567 as C4567
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4601 as C4601
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4602 as C4602
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4603 as C4603
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4605 as C4605
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4607 as C4607
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4612 as C4612
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4613 as C4613
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4615 as C4615
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4617 as C4617
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4623 as C4623
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4625 as C4625
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4627 as C4627
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4635 as C4635
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4637 as C4637
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4657 as C4657
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4701 as C4701
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4702 as C4702
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4703 as C4703
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4705 as C4705
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4706 as C4706
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4712 as C4712
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4713 as C4713
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4715 as C4715
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4716 as C4716
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4723 as C4723
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4725 as C4725
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4726 as C4726
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4735 as C4735
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4736 as C4736
import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_ij4756 as C4756

private
  a : Fin 8
  a = (suc (suc (suc (suc (zero)))))

translate : (b c d : Fin 8) →
  .(p0 : a < b) →
  .(p1 : c < d) →
  (ne0 : a Eq.≢ c) →
  (ne1 : a Eq.≢ d) →
  (ne2 : b Eq.≢ c) →
  (ne3 : b Eq.≢ d) →
  (dX a b) • (dX c d) ≈ (dX c d) • (dX a b)
translate (zero) c d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p0)
translate (suc (zero)) c d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p0)
translate (suc (suc (zero))) c d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p0)
translate (suc (suc (suc (zero)))) c d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p0)
translate (suc (suc (suc (suc (zero))))) c d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p0)
translate (suc (suc (suc (suc (suc (zero)))))) (zero) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (zero)))))) (zero) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = C4501.proved
translate (suc (suc (suc (suc (suc (zero)))))) (zero) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = C4502.proved
translate (suc (suc (suc (suc (suc (zero)))))) (zero) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = C4503.proved
translate (suc (suc (suc (suc (suc (zero)))))) (zero) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (zero)))))) (zero) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (zero)))))) (zero) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = C4506.proved
translate (suc (suc (suc (suc (suc (zero)))))) (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = C4507.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = C4512.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = C4513.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = C4516.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = C4517.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = C4523.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = C4526.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = C4527.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = C4536.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = C4537.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne2 Eq.refl)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = C4567.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = C4601.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = C4602.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = C4603.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = C4605.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = C4607.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = C4612.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = C4613.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = C4615.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = C4617.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = C4623.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = C4625.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = C4627.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = C4635.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = C4637.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = C4657.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne2 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = C4701.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = C4702.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = C4703.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = C4705.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = C4706.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = C4712.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = C4713.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = C4715.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = C4716.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = C4723.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = C4725.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = C4726.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = C4735.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = C4736.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = C4756.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne2 Eq.refl)
