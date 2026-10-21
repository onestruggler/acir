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
open import Examples.Groups.CCX+HH-3qubit.TransportCases.r2a_B02 using (module r2a_ij4501 ; module r2a_ij4502 ; module r2a_ij4503 ; module r2a_ij4506 ; module r2a_ij4507 ; module r2a_ij4512 ; module r2a_ij4513 ; module r2a_ij4516 ; module r2a_ij4517 ; module r2a_ij4523 ; module r2a_ij4526 ; module r2a_ij4527 ; module r2a_ij4536 ; module r2a_ij4537 ; module r2a_ij4567 ; module r2a_ij4601 ; module r2a_ij4602 ; module r2a_ij4603 ; module r2a_ij4605 ; module r2a_ij4607 ; module r2a_ij4612 ; module r2a_ij4613 ; module r2a_ij4615 ; module r2a_ij4617 ; module r2a_ij4623 ; module r2a_ij4625 ; module r2a_ij4627 ; module r2a_ij4635 ; module r2a_ij4637 ; module r2a_ij4657 ; module r2a_ij4701 ; module r2a_ij4702 ; module r2a_ij4703 ; module r2a_ij4705 ; module r2a_ij4706 ; module r2a_ij4712 ; module r2a_ij4713 ; module r2a_ij4715 ; module r2a_ij4716 ; module r2a_ij4723 ; module r2a_ij4725 ; module r2a_ij4726 ; module r2a_ij4735 ; module r2a_ij4736 ; module r2a_ij4756)

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
translate (suc (suc (suc (suc (suc (zero)))))) (zero) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4501.proved
translate (suc (suc (suc (suc (suc (zero)))))) (zero) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4502.proved
translate (suc (suc (suc (suc (suc (zero)))))) (zero) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4503.proved
translate (suc (suc (suc (suc (suc (zero)))))) (zero) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (zero)))))) (zero) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (zero)))))) (zero) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4506.proved
translate (suc (suc (suc (suc (suc (zero)))))) (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4507.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4512.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4513.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4516.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4517.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4523.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4526.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4527.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4536.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4537.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne2 Eq.refl)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4567.proved
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))) p1)
translate (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4601.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4602.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4603.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4605.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4607.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4612.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4613.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4615.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4617.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4623.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4625.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4627.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4635.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4637.proved
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (zero))))) d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (zero))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4657.proved
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
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4701.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4702.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4703.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4705.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4706.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (zero) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4712.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4713.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4715.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4716.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (zero)) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4723.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4725.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4726.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (zero))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne1 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4735.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4736.proved
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (zero)))) (suc (suc (suc (suc (suc (suc (suc (zero)))))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne3 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (zero))))) d p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim (ne0 Eq.refl)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) (zero) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ z≤n p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (zero)) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s z≤n) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (zero))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s z≤n)) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (zero)))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s z≤n))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (zero))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s z≤n)))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (zero)))))) p0 p1 ne0 ne1 ne2 ne3 = ⊥-elim-irr (NP.≤⇒≯ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) p1)
translate (suc (suc (suc (suc (suc (suc (suc (zero)))))))) (suc (suc (suc (suc (suc (zero)))))) (suc (suc (suc (suc (suc (suc (zero))))))) p0 p1 ne0 ne1 ne2 ne3 = r2a_ij4756.proved
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
