------------------------------------------------------------------------
-- Presentations of groups
--
-- The hybrid facts at four wires that Lemma88.HybridRules asks for:
-- far-p, far-l, far-k at the top pair, the shifts, the pair scalar
--
-- Each instance is its decoded letters as blocks (Bridges, HBridges),
-- carried by a transport to a hybrid class fact (HClasses).  Generated
-- by scratchpad/four/factsgen_hyb.py.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.Facts.H1 where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.List using (List ; [] ; _∷_ ; _++_ ; map)
open import Data.Nat using (ℕ ; zero ; suc ; _≤_ ; _<_ ; s≤s ; z≤n)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_ ; _^_)

open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Examples.Groups.Clifford+CS.Four.Chain
open import Examples.Groups.Clifford+CS.Four.TransportTables
open import Examples.Groups.Clifford+CS.Four.Transport
open import Examples.Groups.Clifford+CS.Decoding 0 using (dPP₁ ; dPP₁′ ; lo₁ ; hi₁ ; dKI₁)
open import Examples.Groups.Clifford+CS.Four.Facts.Bridges
open import Examples.Groups.Clifford+CS.Four.Facts.HBridges
open import Examples.Groups.Clifford+CS.Four.Facts.Classes using (Resp ; []ʳ ; same ; re ; resp)
open import Examples.Groups.Clifford+CS.Four.Facts.HClasses
open import Examples.Groups.Clifford+CS.Four.D.D447 using (lem-respell-hyb-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02---⟶-CS02-CS02-CK20-CS02-CX21-CS01-CS01-CS01- ; lem-respell-hyb-CS02-CS02-CK20-CS02-CX21-CS01-CS01-CS01---⟶-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02- ; lem-respell-hyb-CS12-CS12-CK21-CS12-CX20-CS01-CS01-CS01---⟶-CS01-CS01-CK01-CS01-CX02-CS12-CS12-CS12-)
open import Examples.Groups.Clifford+CS.Four.D.D450 using (lem-respell-hyb-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03---⟶-CS03-CS03-CK30-CS03-CX31-CS01-CS01-CS01-)
open import Examples.Groups.Clifford+CS.Four.D.D451 using (lem-respell-hyb-CS02-CS02-CK20-CS02-CX23-CS03-CS03-CS03---⟶-CS03-CS03-CK30-CS03-CX32-CS02-CS02-CS02-)
open import Examples.Groups.Clifford+CS.Four.D.D452 using (lem-respell-hyb-CS01-CS01-CK01-CS01-CX03-CS13-CS13-CS13---⟶-CS13-CS13-CK31-CS13-CX30-CS01-CS01-CS01-)
open import Examples.Groups.Clifford+CS.Four.D.D453 using (lem-respell-hyb-CS03-CS03-CK30-CS03-CX31-CS01-CS01-CS01---⟶-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-)
open import Examples.Groups.Clifford+CS.Four.D.D454 using (lem-respell-hyb-CS23-CS23-CK32-CS23-CX30-CS02-CS02-CS02---⟶-CS02-CS02-CK02-CS02-CX03-CS23-CS23-CS23-)
open import Examples.Groups.Clifford+CS.Four.D.D668 using (lem-respell-hyb-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02---⟶-CS03-CS03-CK30-CS03-CX31-CS01-CS01-CS01-)
open import Examples.Groups.Clifford+CS.Four.D.D670 using (lem-respell-hyb-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02---⟶-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-)
open import Examples.Groups.Clifford+CS.Four.D.D684 using (lem-resp-TOFF013-CS02-TOFF013-CSd02)
open import Examples.Groups.Clifford+CS.Four.D.D699 using (lem-respell-hyb-CS02-CS02-CK20-CS02-CX21-CS01-CS01-CS01---⟶-CS03-CS03-CK30-CS03-CX32-CS02-CS02-CS02-)
open import Examples.Groups.Clifford+CS.Four.D.D700 using (lem-respell-hyb-CS01-CS01-CK01-CS01-CX02-CS12-CS12-CS12---⟶-CS13-CS13-CK31-CS13-CX30-CS01-CS01-CS01- ; lem-respell-hyb-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02---⟶-CS02-CS02-CK20-CS02-CX23-CS03-CS03-CS03- ; lem-respell-hyb-CS02-CS02-CK20-CS02-CX21-CS01-CS01-CS01---⟶-CS02-CS02-CK20-CS02-CX23-CS03-CS03-CS03- ; lem-respell-hyb-CS12-CS12-CK21-CS12-CX20-CS01-CS01-CS01---⟶-CS01-CS01-CK01-CS01-CX03-CS13-CS13-CS13-)
open import Examples.Groups.Clifford+CS.Four.D.D703 using (lem-resp-S0-K0-CS02-TOFF013-CSd02-TOFF013-Kd0-Sd0 ; lem-resp-TOFF023-CS01-TOFF023-CSd01)
open import Examples.Groups.Clifford+CS.Four.D.D707 using (lem-respell-hyb-CS13-CS13-CK31-CS13-CX32-CS12-CS12-CS12---⟶-CS01-CS01-CK01-CS01-CX03-CS13-CS13-CS13-)
open import Examples.Groups.Clifford+CS.Four.D.D709 using (lem-respell-hyb-CS02-CS02-CK20-CS02-CX23-CS03-CS03-CS03---⟶-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-)
open import Examples.Groups.Clifford+CS.Four.D.D710 using (lem-resp-TOFF103-CS12-TOFF103-CSd12 ; lem-resp-TOFF203-CS12-TOFF203-CSd12 ; lem-respell-hyb-CS12-CS12-CK12-CS12-CX13-CS23-CS23-CS23---⟶-CS02-CS02-CK02-CS02-CX03-CS23-CS23-CS23-)
open import Examples.Groups.Clifford+CS.Four.D.D715 using (lem-resp-S0-K0-CS01-TOFF023-CSd01-TOFF023-Kd0-Sd0 ; lem-resp-S1-K1-CS01-TOFF123-CSd01-TOFF123-Kd1-Sd1 ; lem-resp-S1-K1-CS12-TOFF103-CSd12-TOFF103-Kd1-Sd1 ; lem-resp-S2-K2-CS12-TOFF203-CSd12-TOFF203-Kd2-Sd2)

i-far-p-0 : dKI₁ 14 • dPP₁ 0 ≈ dPP₁ 0 • dKI₁ 14
i-far-p-0 = trans (trans (cong br-k-14 br-p-0) (sym (++≈ (flatB B-k-14) (flat (B-p-0 ∷ [])))))
  (trans (transport (col w₁ ∷ col w₂ ∷ []) (TF (col w₂ ∷ col w₁ ∷ []) (B-k-14 ∷ B-p-0 ∷ [])) (TF (col w₂ ∷ col w₁ ∷ []) (B-p-0 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-p-0 br-k-14) (sym (++≈ (flatB B-p-0) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₂ ∷ col w₁ ∷ []) (B-k-14 ∷ B-p-0 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₂ ∷ col w₁ ∷ []) (B-p-0 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₂ ∷ col w₁ ∷ []) (B-k-14 ∷ B-p-0 ∷ [])} {(HC0-0 ∷ HC0-1 ∷ [])} (re lem-respell-hyb-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02---⟶-CS03-CS03-CK30-CS03-CX31-CS01-CS01-CS01- (same ([]ʳ))))
      (trans hcls-0 (sym (resp {TF (col w₂ ∷ col w₁ ∷ []) (B-p-0 ∷ B-k-14 ∷ [])} {(HC0-2 ∷ HC0-3 ∷ [])} (same (re lem-respell-hyb-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02---⟶-CS03-CS03-CK30-CS03-CX31-CS01-CS01-CS01- ([]ʳ))))))

i-far-l-0 : dKI₁ 14 • lo₁ 0 ≈ lo₁ 0 • dKI₁ 14
i-far-l-0 = trans (trans (cong br-k-14 br-l-0) (sym (++≈ (flatB B-k-14) (flat (B-l-0 ∷ [])))))
  (trans (transport (col w₁ ∷ col w₂ ∷ []) (TF (col w₂ ∷ col w₁ ∷ []) (B-k-14 ∷ B-l-0 ∷ [])) (TF (col w₂ ∷ col w₁ ∷ []) (B-l-0 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-l-0 br-k-14) (sym (++≈ (flatB B-l-0) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₂ ∷ col w₁ ∷ []) (B-k-14 ∷ B-l-0 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₂ ∷ col w₁ ∷ []) (B-l-0 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₂ ∷ col w₁ ∷ []) (B-k-14 ∷ B-l-0 ∷ [])} {(HC1-0 ∷ HC1-1 ∷ [])} (re lem-respell-hyb-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02---⟶-CS03-CS03-CK30-CS03-CX31-CS01-CS01-CS01- (same ([]ʳ))))
      (trans hcls-1 (sym (resp {TF (col w₂ ∷ col w₁ ∷ []) (B-l-0 ∷ B-k-14 ∷ [])} {(HC1-2 ∷ HC1-3 ∷ [])} (same (re lem-respell-hyb-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02---⟶-CS03-CS03-CK30-CS03-CX31-CS01-CS01-CS01- ([]ʳ))))))

i-far-k-0 : dKI₁ 14 • dKI₁ 0 ≈ dKI₁ 0 • dKI₁ 14
i-far-k-0 = trans (trans (cong br-k-14 br-k-0) (sym (++≈ (flatB B-k-14) (flat (B-k-0 ∷ [])))))
  (trans (transport (col w₁ ∷ col w₂ ∷ []) (TF (col w₂ ∷ col w₁ ∷ []) (B-k-14 ∷ B-k-0 ∷ [])) (TF (col w₂ ∷ col w₁ ∷ []) (B-k-0 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-k-0 br-k-14) (sym (++≈ (flatB B-k-0) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₂ ∷ col w₁ ∷ []) (B-k-14 ∷ B-k-0 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₂ ∷ col w₁ ∷ []) (B-k-0 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₂ ∷ col w₁ ∷ []) (B-k-14 ∷ B-k-0 ∷ [])} {(HC2-0 ∷ HC2-1 ∷ [])} (re lem-respell-hyb-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02---⟶-CS03-CS03-CK30-CS03-CX31-CS01-CS01-CS01- (re lem-respell-hyb-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02---⟶-CS03-CS03-CK30-CS03-CX31-CS01-CS01-CS01- ([]ʳ))))
      (trans hcls-2 (sym (resp {TF (col w₂ ∷ col w₁ ∷ []) (B-k-0 ∷ B-k-14 ∷ [])} {(HC2-2 ∷ HC2-3 ∷ [])} (re lem-respell-hyb-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02---⟶-CS03-CS03-CK30-CS03-CX31-CS01-CS01-CS01- (re lem-respell-hyb-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02---⟶-CS03-CS03-CK30-CS03-CX31-CS01-CS01-CS01- ([]ʳ))))))

i-far-p-1 : dKI₁ 14 • dPP₁ 1 ≈ dPP₁ 1 • dKI₁ 14
i-far-p-1 = trans (trans (cong br-k-14 br-p-1) (sym (++≈ (flatB B-k-14) (flat (B-p-1 ∷ [])))))
  (trans (transport (rel s₁ ∷ col w₁ ∷ col w₂ ∷ []) (TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-p-1 ∷ [])) (TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-p-1 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-p-1 br-k-14) (sym (++≈ (flatB B-p-1) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-p-1 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-p-1 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-p-1 ∷ [])} {(HC3-0 ∷ HC3-1 ∷ [])} (re lem-respell-hyb-CS02-CS02-CK20-CS02-CX21-CS01-CS01-CS01---⟶-CS03-CS03-CK30-CS03-CX32-CS02-CS02-CS02- (same ([]ʳ))))
      (trans hcls-3 (sym (resp {TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-p-1 ∷ B-k-14 ∷ [])} {(HC3-2 ∷ HC3-3 ∷ [])} (same (re lem-respell-hyb-CS02-CS02-CK20-CS02-CX21-CS01-CS01-CS01---⟶-CS03-CS03-CK30-CS03-CX32-CS02-CS02-CS02- ([]ʳ))))))

i-far-l-1 : dKI₁ 14 • lo₁ 1 ≈ lo₁ 1 • dKI₁ 14
i-far-l-1 = trans (trans (cong br-k-14 br-l-1) (sym (++≈ (flatB B-k-14) (flat (B-l-1 ∷ [])))))
  (trans (transport (rel s₁ ∷ col w₁ ∷ col w₂ ∷ []) (TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-l-1 ∷ [])) (TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-l-1 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-l-1 br-k-14) (sym (++≈ (flatB B-l-1) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-l-1 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-l-1 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-l-1 ∷ [])} {(HC4-0 ∷ HC4-1 ∷ [])} (re lem-respell-hyb-CS02-CS02-CK20-CS02-CX21-CS01-CS01-CS01---⟶-CS03-CS03-CK30-CS03-CX32-CS02-CS02-CS02- (same ([]ʳ))))
      (trans hcls-4 (sym (resp {TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-l-1 ∷ B-k-14 ∷ [])} {(HC4-2 ∷ HC4-3 ∷ [])} (same (re lem-respell-hyb-CS02-CS02-CK20-CS02-CX21-CS01-CS01-CS01---⟶-CS03-CS03-CK30-CS03-CX32-CS02-CS02-CS02- ([]ʳ))))))

i-far-k-1 : dKI₁ 14 • dKI₁ 1 ≈ dKI₁ 1 • dKI₁ 14
i-far-k-1 = trans (trans (cong br-k-14 br-k-1) (sym (++≈ (flatB B-k-14) (flat (B-k-1 ∷ [])))))
  (trans (transport (col w₁ ∷ col w₂ ∷ []) (TF (col w₂ ∷ col w₁ ∷ []) (B-k-14 ∷ B-k-1 ∷ [])) (TF (col w₂ ∷ col w₁ ∷ []) (B-k-1 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-k-1 br-k-14) (sym (++≈ (flatB B-k-1) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₂ ∷ col w₁ ∷ []) (B-k-14 ∷ B-k-1 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₂ ∷ col w₁ ∷ []) (B-k-1 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₂ ∷ col w₁ ∷ []) (B-k-14 ∷ B-k-1 ∷ [])} {(HC5-0 ∷ HC5-1 ∷ [])} (re lem-respell-hyb-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02---⟶-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03- (re lem-respell-hyb-CS01-CS01-CK01-CS01-CX02-CS12-CS12-CS12---⟶-CS13-CS13-CK31-CS13-CX30-CS01-CS01-CS01- ([]ʳ))))
      (trans hcls-5 (sym (resp {TF (col w₂ ∷ col w₁ ∷ []) (B-k-1 ∷ B-k-14 ∷ [])} {(HC5-2 ∷ HC5-3 ∷ [])} (re lem-respell-hyb-CS01-CS01-CK01-CS01-CX02-CS12-CS12-CS12---⟶-CS13-CS13-CK31-CS13-CX30-CS01-CS01-CS01- (re lem-respell-hyb-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02---⟶-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03- ([]ʳ))))))

i-far-p-2 : dKI₁ 14 • dPP₁ 2 ≈ dPP₁ 2 • dKI₁ 14
i-far-p-2 = trans (trans (cong br-k-14 br-p-2) (sym (++≈ (flatB B-k-14) (flat (B-p-2 ∷ [])))))
  (trans (transport (rel s₁ ∷ col w₁ ∷ col w₂ ∷ []) (TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-p-2 ∷ [])) (TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-p-2 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-p-2 br-k-14) (sym (++≈ (flatB B-p-2) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-p-2 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-p-2 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-p-2 ∷ [])} {(HC6-0 ∷ HC6-1 ∷ [])} (re lem-respell-hyb-CS02-CS02-CK20-CS02-CX21-CS01-CS01-CS01---⟶-CS02-CS02-CK20-CS02-CX23-CS03-CS03-CS03- (same ([]ʳ))))
      (trans hcls-6 (sym (resp {TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-p-2 ∷ B-k-14 ∷ [])} {(HC6-2 ∷ HC6-3 ∷ [])} (same (re lem-respell-hyb-CS02-CS02-CK20-CS02-CX21-CS01-CS01-CS01---⟶-CS02-CS02-CK20-CS02-CX23-CS03-CS03-CS03- ([]ʳ))))))

i-far-l-2 : dKI₁ 14 • lo₁ 2 ≈ lo₁ 2 • dKI₁ 14
i-far-l-2 = trans (trans (cong br-k-14 br-l-2) (sym (++≈ (flatB B-k-14) (flat (B-l-2 ∷ [])))))
  (trans (transport (rel s₁ ∷ col w₁ ∷ col w₂ ∷ []) (TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-l-2 ∷ [])) (TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-l-2 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-l-2 br-k-14) (sym (++≈ (flatB B-l-2) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-l-2 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-l-2 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-l-2 ∷ [])} {(HC7-0 ∷ HC7-1 ∷ [])} (re lem-respell-hyb-CS02-CS02-CK20-CS02-CX21-CS01-CS01-CS01---⟶-CS02-CS02-CK20-CS02-CX23-CS03-CS03-CS03- (same ([]ʳ))))
      (trans hcls-7 (sym (resp {TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-l-2 ∷ B-k-14 ∷ [])} {(HC7-2 ∷ HC7-3 ∷ [])} (same (re lem-respell-hyb-CS02-CS02-CK20-CS02-CX21-CS01-CS01-CS01---⟶-CS02-CS02-CK20-CS02-CX23-CS03-CS03-CS03- ([]ʳ))))))

i-far-k-2 : dKI₁ 14 • dKI₁ 2 ≈ dKI₁ 2 • dKI₁ 14
i-far-k-2 = trans (trans (cong br-k-14 br-k-2) (sym (++≈ (flatB B-k-14) (flat (B-k-2 ∷ [])))))
  (trans (transport (rel s₁ ∷ col w₁ ∷ col w₂ ∷ []) (TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-k-2 ∷ [])) (TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-k-2 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-k-2 br-k-14) (sym (++≈ (flatB B-k-2) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-k-2 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-k-2 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-k-2 ∷ [])} {(HC8-0 ∷ HC8-1 ∷ [])} (re lem-respell-hyb-CS02-CS02-CK20-CS02-CX21-CS01-CS01-CS01---⟶-CS02-CS02-CK20-CS02-CX23-CS03-CS03-CS03- (re lem-respell-hyb-CS02-CS02-CK20-CS02-CX21-CS01-CS01-CS01---⟶-CS02-CS02-CK20-CS02-CX23-CS03-CS03-CS03- ([]ʳ))))
      (trans hcls-8 (sym (resp {TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-k-2 ∷ B-k-14 ∷ [])} {(HC8-2 ∷ HC8-3 ∷ [])} (re lem-respell-hyb-CS02-CS02-CK20-CS02-CX21-CS01-CS01-CS01---⟶-CS02-CS02-CK20-CS02-CX23-CS03-CS03-CS03- (re lem-respell-hyb-CS02-CS02-CK20-CS02-CX21-CS01-CS01-CS01---⟶-CS02-CS02-CK20-CS02-CX23-CS03-CS03-CS03- ([]ʳ))))))

i-far-p-3 : dKI₁ 14 • dPP₁ 3 ≈ dPP₁ 3 • dKI₁ 14
i-far-p-3 = trans (trans (cong br-k-14 br-p-3) (sym (++≈ (flatB B-k-14) (flat (B-p-3 ∷ [])))))
  (trans (transport (rel s₁ ∷ col w₁ ∷ col w₂ ∷ []) (TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-p-3 ∷ [])) (TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-p-3 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-p-3 br-k-14) (sym (++≈ (flatB B-p-3) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-p-3 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-p-3 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-p-3 ∷ [])} {(HC9-0 ∷ HC9-1 ∷ [])} (re lem-respell-hyb-CS02-CS02-CK20-CS02-CX21-CS01-CS01-CS01---⟶-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02- (same ([]ʳ))))
      (trans hcls-9 (sym (resp {TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-p-3 ∷ B-k-14 ∷ [])} {(HC9-2 ∷ HC9-3 ∷ [])} (same (re lem-respell-hyb-CS02-CS02-CK20-CS02-CX21-CS01-CS01-CS01---⟶-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02- ([]ʳ))))))

i-far-l-3 : dKI₁ 14 • lo₁ 3 ≈ lo₁ 3 • dKI₁ 14
i-far-l-3 = trans (trans (cong br-k-14 br-l-3) (sym (++≈ (flatB B-k-14) (flat (B-l-3 ∷ [])))))
  (trans (transport (rel s₁ ∷ col w₁ ∷ col w₂ ∷ []) (TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-l-3 ∷ [])) (TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-l-3 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-l-3 br-k-14) (sym (++≈ (flatB B-l-3) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-l-3 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-l-3 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-l-3 ∷ [])} {(HC10-0 ∷ HC10-1 ∷ [])} (re lem-respell-hyb-CS02-CS02-CK20-CS02-CX21-CS01-CS01-CS01---⟶-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02- (same ([]ʳ))))
      (trans hcls-10 (sym (resp {TF (col w₂ ∷ col w₁ ∷ rel s₁ ∷ []) (B-l-3 ∷ B-k-14 ∷ [])} {(HC10-2 ∷ HC10-3 ∷ [])} (same (re lem-respell-hyb-CS02-CS02-CK20-CS02-CX21-CS01-CS01-CS01---⟶-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02- ([]ʳ))))))

i-far-k-3 : dKI₁ 14 • dKI₁ 3 ≈ dKI₁ 3 • dKI₁ 14
i-far-k-3 = trans (trans (cong br-k-14 br-k-3) (sym (++≈ (flatB B-k-14) (flat (B-k-3 ∷ [])))))
  (trans (transport (rel s₁ ∷ rel s₀ ∷ col w₀ ∷ col w₁ ∷ col w₃ ∷ []) (TF (col w₃ ∷ col w₁ ∷ col w₀ ∷ rel s₀ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-k-3 ∷ [])) (TF (col w₃ ∷ col w₁ ∷ col w₀ ∷ rel s₀ ∷ rel s₁ ∷ []) (B-k-3 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-k-3 br-k-14) (sym (++≈ (flatB B-k-3) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₃ ∷ col w₁ ∷ col w₀ ∷ rel s₀ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-k-3 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₃ ∷ col w₁ ∷ col w₀ ∷ rel s₀ ∷ rel s₁ ∷ []) (B-k-3 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₃ ∷ col w₁ ∷ col w₀ ∷ rel s₀ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-k-3 ∷ [])} {(HC11-2 ∷ HC11-3 ∷ [])} (re lem-respell-hyb-CS12-CS12-CK21-CS12-CX20-CS01-CS01-CS01---⟶-CS01-CS01-CK01-CS01-CX02-CS12-CS12-CS12- (same ([]ʳ))))
      (trans (sym hcls-11) (sym (resp {TF (col w₃ ∷ col w₁ ∷ col w₀ ∷ rel s₀ ∷ rel s₁ ∷ []) (B-k-3 ∷ B-k-14 ∷ [])} {(HC11-0 ∷ HC11-1 ∷ [])} (same (re lem-respell-hyb-CS12-CS12-CK21-CS12-CX20-CS01-CS01-CS01---⟶-CS01-CS01-CK01-CS01-CX02-CS12-CS12-CS12- ([]ʳ))))))

i-far-p-4 : dKI₁ 14 • dPP₁ 4 ≈ dPP₁ 4 • dKI₁ 14
i-far-p-4 = trans (trans (cong br-k-14 br-p-4) (sym (++≈ (flatB B-k-14) (flat (B-p-4 ∷ [])))))
  (trans (transport (col w₁ ∷ col w₂ ∷ []) (TF (col w₂ ∷ col w₁ ∷ []) (B-k-14 ∷ B-p-4 ∷ [])) (TF (col w₂ ∷ col w₁ ∷ []) (B-p-4 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-p-4 br-k-14) (sym (++≈ (flatB B-p-4) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₂ ∷ col w₁ ∷ []) (B-k-14 ∷ B-p-4 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₂ ∷ col w₁ ∷ []) (B-p-4 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₂ ∷ col w₁ ∷ []) (B-k-14 ∷ B-p-4 ∷ [])} {(HC12-0 ∷ HC12-1 ∷ [])} (same (same ([]ʳ))))
      (trans hcls-12 (sym (resp {TF (col w₂ ∷ col w₁ ∷ []) (B-p-4 ∷ B-k-14 ∷ [])} {(HC12-2 ∷ HC12-3 ∷ [])} (same (same ([]ʳ))))))

i-far-l-4 : dKI₁ 14 • lo₁ 4 ≈ lo₁ 4 • dKI₁ 14
i-far-l-4 = trans (trans (cong br-k-14 br-l-4) (sym (++≈ (flatB B-k-14) (flat (B-l-4 ∷ [])))))
  (trans (transport (col w₁ ∷ col w₂ ∷ []) (TF (col w₂ ∷ col w₁ ∷ []) (B-k-14 ∷ B-l-4 ∷ [])) (TF (col w₂ ∷ col w₁ ∷ []) (B-l-4 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-l-4 br-k-14) (sym (++≈ (flatB B-l-4) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₂ ∷ col w₁ ∷ []) (B-k-14 ∷ B-l-4 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₂ ∷ col w₁ ∷ []) (B-l-4 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₂ ∷ col w₁ ∷ []) (B-k-14 ∷ B-l-4 ∷ [])} {(HC13-0 ∷ HC13-1 ∷ [])} (same (same ([]ʳ))))
      (trans hcls-13 (sym (resp {TF (col w₂ ∷ col w₁ ∷ []) (B-l-4 ∷ B-k-14 ∷ [])} {(HC13-2 ∷ HC13-3 ∷ [])} (same (same ([]ʳ))))))

i-far-k-4 : dKI₁ 14 • dKI₁ 4 ≈ dKI₁ 4 • dKI₁ 14
i-far-k-4 = trans (trans (cong br-k-14 br-k-4) (sym (++≈ (flatB B-k-14) (flat (B-k-4 ∷ [])))))
  (trans (transport (col w₀ ∷ col w₃ ∷ []) (TF (col w₃ ∷ col w₀ ∷ []) (B-k-14 ∷ B-k-4 ∷ [])) (TF (col w₃ ∷ col w₀ ∷ []) (B-k-4 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-k-4 br-k-14) (sym (++≈ (flatB B-k-4) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₃ ∷ col w₀ ∷ []) (B-k-14 ∷ B-k-4 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₃ ∷ col w₀ ∷ []) (B-k-4 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₃ ∷ col w₀ ∷ []) (B-k-14 ∷ B-k-4 ∷ [])} {(HC14-2 ∷ HC14-3 ∷ [])} (same (same ([]ʳ))))
      (trans (sym hcls-14) (sym (resp {TF (col w₃ ∷ col w₀ ∷ []) (B-k-4 ∷ B-k-14 ∷ [])} {(HC14-0 ∷ HC14-1 ∷ [])} (same (same ([]ʳ))))))

i-far-p-5 : dKI₁ 14 • dPP₁ 5 ≈ dPP₁ 5 • dKI₁ 14
i-far-p-5 = trans (trans (cong br-k-14 br-p-5) (sym (++≈ (flatB B-k-14) (flat (B-p-5 ∷ [])))))
  (trans (transport (col w₁ ∷ col w₂ ∷ []) (TF (col w₂ ∷ col w₁ ∷ []) (B-k-14 ∷ B-p-5 ∷ [])) (TF (col w₂ ∷ col w₁ ∷ []) (B-p-5 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-p-5 br-k-14) (sym (++≈ (flatB B-p-5) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₂ ∷ col w₁ ∷ []) (B-k-14 ∷ B-p-5 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₂ ∷ col w₁ ∷ []) (B-p-5 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₂ ∷ col w₁ ∷ []) (B-k-14 ∷ B-p-5 ∷ [])} {(HC15-0 ∷ HC15-1 ∷ [])} (re lem-respell-hyb-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02---⟶-CS02-CS02-CK20-CS02-CX21-CS01-CS01-CS01- (same ([]ʳ))))
      (trans hcls-15 (sym (resp {TF (col w₂ ∷ col w₁ ∷ []) (B-p-5 ∷ B-k-14 ∷ [])} {(HC15-2 ∷ HC15-3 ∷ [])} (same (re lem-respell-hyb-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02---⟶-CS02-CS02-CK20-CS02-CX21-CS01-CS01-CS01- ([]ʳ))))))

i-far-l-5 : dKI₁ 14 • lo₁ 5 ≈ lo₁ 5 • dKI₁ 14
i-far-l-5 = trans (trans (cong br-k-14 br-l-5) (sym (++≈ (flatB B-k-14) (flat (B-l-5 ∷ [])))))
  (trans (transport (col w₁ ∷ col w₂ ∷ []) (TF (col w₂ ∷ col w₁ ∷ []) (B-k-14 ∷ B-l-5 ∷ [])) (TF (col w₂ ∷ col w₁ ∷ []) (B-l-5 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-l-5 br-k-14) (sym (++≈ (flatB B-l-5) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₂ ∷ col w₁ ∷ []) (B-k-14 ∷ B-l-5 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₂ ∷ col w₁ ∷ []) (B-l-5 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₂ ∷ col w₁ ∷ []) (B-k-14 ∷ B-l-5 ∷ [])} {(HC16-0 ∷ HC16-1 ∷ [])} (re lem-respell-hyb-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02---⟶-CS02-CS02-CK20-CS02-CX21-CS01-CS01-CS01- (same ([]ʳ))))
      (trans hcls-16 (sym (resp {TF (col w₂ ∷ col w₁ ∷ []) (B-l-5 ∷ B-k-14 ∷ [])} {(HC16-2 ∷ HC16-3 ∷ [])} (same (re lem-respell-hyb-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02---⟶-CS02-CS02-CK20-CS02-CX21-CS01-CS01-CS01- ([]ʳ))))))

i-far-k-5 : dKI₁ 14 • dKI₁ 5 ≈ dKI₁ 5 • dKI₁ 14
i-far-k-5 = trans (trans (cong br-k-14 br-k-5) (sym (++≈ (flatB B-k-14) (flat (B-k-5 ∷ [])))))
  (trans (transport (col w₁ ∷ col w₂ ∷ []) (TF (col w₂ ∷ col w₁ ∷ []) (B-k-14 ∷ B-k-5 ∷ [])) (TF (col w₂ ∷ col w₁ ∷ []) (B-k-5 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-k-5 br-k-14) (sym (++≈ (flatB B-k-5) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₂ ∷ col w₁ ∷ []) (B-k-14 ∷ B-k-5 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₂ ∷ col w₁ ∷ []) (B-k-5 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₂ ∷ col w₁ ∷ []) (B-k-14 ∷ B-k-5 ∷ [])} {(HC11-0 ∷ HC11-1 ∷ [])} (same (same ([]ʳ))))
      (trans hcls-11 (sym (resp {TF (col w₂ ∷ col w₁ ∷ []) (B-k-5 ∷ B-k-14 ∷ [])} {(HC11-2 ∷ HC11-3 ∷ [])} (same (same ([]ʳ))))))

i-far-p-6 : dKI₁ 14 • dPP₁ 6 ≈ dPP₁ 6 • dKI₁ 14
i-far-p-6 = trans (trans (cong br-k-14 br-p-6) (sym (++≈ (flatB B-k-14) (flat (B-p-6 ∷ [])))))
  (trans (transport (col w₁ ∷ col w₂ ∷ []) (TF (col w₂ ∷ col w₁ ∷ []) (B-k-14 ∷ B-p-6 ∷ [])) (TF (col w₂ ∷ col w₁ ∷ []) (B-p-6 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-p-6 br-k-14) (sym (++≈ (flatB B-p-6) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₂ ∷ col w₁ ∷ []) (B-k-14 ∷ B-p-6 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₂ ∷ col w₁ ∷ []) (B-p-6 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₂ ∷ col w₁ ∷ []) (B-k-14 ∷ B-p-6 ∷ [])} {(HC6-0 ∷ HC6-1 ∷ [])} (re lem-respell-hyb-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02---⟶-CS02-CS02-CK20-CS02-CX23-CS03-CS03-CS03- (same ([]ʳ))))
      (trans hcls-6 (sym (resp {TF (col w₂ ∷ col w₁ ∷ []) (B-p-6 ∷ B-k-14 ∷ [])} {(HC6-2 ∷ HC6-3 ∷ [])} (same (re lem-respell-hyb-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02---⟶-CS02-CS02-CK20-CS02-CX23-CS03-CS03-CS03- ([]ʳ))))))

i-far-l-6 : dKI₁ 14 • lo₁ 6 ≈ lo₁ 6 • dKI₁ 14
i-far-l-6 = trans (trans (cong br-k-14 br-l-6) (sym (++≈ (flatB B-k-14) (flat (B-l-6 ∷ [])))))
  (trans (transport (col w₁ ∷ col w₂ ∷ []) (TF (col w₂ ∷ col w₁ ∷ []) (B-k-14 ∷ B-l-6 ∷ [])) (TF (col w₂ ∷ col w₁ ∷ []) (B-l-6 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-l-6 br-k-14) (sym (++≈ (flatB B-l-6) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₂ ∷ col w₁ ∷ []) (B-k-14 ∷ B-l-6 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₂ ∷ col w₁ ∷ []) (B-l-6 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₂ ∷ col w₁ ∷ []) (B-k-14 ∷ B-l-6 ∷ [])} {(HC7-0 ∷ HC7-1 ∷ [])} (re lem-respell-hyb-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02---⟶-CS02-CS02-CK20-CS02-CX23-CS03-CS03-CS03- (same ([]ʳ))))
      (trans hcls-7 (sym (resp {TF (col w₂ ∷ col w₁ ∷ []) (B-l-6 ∷ B-k-14 ∷ [])} {(HC7-2 ∷ HC7-3 ∷ [])} (same (re lem-respell-hyb-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02---⟶-CS02-CS02-CK20-CS02-CX23-CS03-CS03-CS03- ([]ʳ))))))

i-far-k-6 : dKI₁ 14 • dKI₁ 6 ≈ dKI₁ 6 • dKI₁ 14
i-far-k-6 = trans (trans (cong br-k-14 br-k-6) (sym (++≈ (flatB B-k-14) (flat (B-k-6 ∷ [])))))
  (trans (transport (col w₁ ∷ col w₂ ∷ []) (TF (col w₂ ∷ col w₁ ∷ []) (B-k-14 ∷ B-k-6 ∷ [])) (TF (col w₂ ∷ col w₁ ∷ []) (B-k-6 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-k-6 br-k-14) (sym (++≈ (flatB B-k-6) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₂ ∷ col w₁ ∷ []) (B-k-14 ∷ B-k-6 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₂ ∷ col w₁ ∷ []) (B-k-6 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₂ ∷ col w₁ ∷ []) (B-k-14 ∷ B-k-6 ∷ [])} {(HC8-0 ∷ HC8-1 ∷ [])} (re lem-respell-hyb-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02---⟶-CS02-CS02-CK20-CS02-CX23-CS03-CS03-CS03- (re lem-respell-hyb-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02---⟶-CS02-CS02-CK20-CS02-CX23-CS03-CS03-CS03- ([]ʳ))))
      (trans hcls-8 (sym (resp {TF (col w₂ ∷ col w₁ ∷ []) (B-k-6 ∷ B-k-14 ∷ [])} {(HC8-2 ∷ HC8-3 ∷ [])} (re lem-respell-hyb-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02---⟶-CS02-CS02-CK20-CS02-CX23-CS03-CS03-CS03- (re lem-respell-hyb-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02---⟶-CS02-CS02-CK20-CS02-CX23-CS03-CS03-CS03- ([]ʳ))))))

i-far-p-7 : dKI₁ 14 • dPP₁ 7 ≈ dPP₁ 7 • dKI₁ 14
i-far-p-7 = trans (trans (cong br-k-14 br-p-7) (sym (++≈ (flatB B-k-14) (flat (B-p-7 ∷ [])))))
  (trans (transport (rel s₂ ∷ rel s₁ ∷ col w₂ ∷ col w₃ ∷ []) (TF (col w₃ ∷ col w₂ ∷ rel s₁ ∷ rel s₂ ∷ []) (B-k-14 ∷ B-p-7 ∷ [])) (TF (col w₃ ∷ col w₂ ∷ rel s₁ ∷ rel s₂ ∷ []) (B-p-7 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-p-7 br-k-14) (sym (++≈ (flatB B-p-7) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₃ ∷ col w₂ ∷ rel s₁ ∷ rel s₂ ∷ []) (B-k-14 ∷ B-p-7 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₃ ∷ col w₂ ∷ rel s₁ ∷ rel s₂ ∷ []) (B-p-7 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₃ ∷ col w₂ ∷ rel s₁ ∷ rel s₂ ∷ []) (B-k-14 ∷ B-p-7 ∷ [])} {(HC17-0 ∷ HC17-1 ∷ [])} (re lem-respell-hyb-CS02-CS02-CK20-CS02-CX23-CS03-CS03-CS03---⟶-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03- (same ([]ʳ))))
      (trans hcls-17 (sym (resp {TF (col w₃ ∷ col w₂ ∷ rel s₁ ∷ rel s₂ ∷ []) (B-p-7 ∷ B-k-14 ∷ [])} {(HC17-2 ∷ HC17-3 ∷ [])} (same (re lem-respell-hyb-CS02-CS02-CK20-CS02-CX23-CS03-CS03-CS03---⟶-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03- ([]ʳ))))))

i-far-l-7 : dKI₁ 14 • lo₁ 7 ≈ lo₁ 7 • dKI₁ 14
i-far-l-7 = trans (trans (cong br-k-14 br-l-7) (sym (++≈ (flatB B-k-14) (flat (B-l-7 ∷ [])))))
  (trans (transport (rel s₂ ∷ rel s₁ ∷ col w₂ ∷ col w₃ ∷ []) (TF (col w₃ ∷ col w₂ ∷ rel s₁ ∷ rel s₂ ∷ []) (B-k-14 ∷ B-l-7 ∷ [])) (TF (col w₃ ∷ col w₂ ∷ rel s₁ ∷ rel s₂ ∷ []) (B-l-7 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-l-7 br-k-14) (sym (++≈ (flatB B-l-7) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₃ ∷ col w₂ ∷ rel s₁ ∷ rel s₂ ∷ []) (B-k-14 ∷ B-l-7 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₃ ∷ col w₂ ∷ rel s₁ ∷ rel s₂ ∷ []) (B-l-7 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₃ ∷ col w₂ ∷ rel s₁ ∷ rel s₂ ∷ []) (B-k-14 ∷ B-l-7 ∷ [])} {(HC18-0 ∷ HC18-1 ∷ [])} (re lem-respell-hyb-CS02-CS02-CK20-CS02-CX23-CS03-CS03-CS03---⟶-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03- (same ([]ʳ))))
      (trans hcls-18 (sym (resp {TF (col w₃ ∷ col w₂ ∷ rel s₁ ∷ rel s₂ ∷ []) (B-l-7 ∷ B-k-14 ∷ [])} {(HC18-2 ∷ HC18-3 ∷ [])} (same (re lem-respell-hyb-CS02-CS02-CK20-CS02-CX23-CS03-CS03-CS03---⟶-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03- ([]ʳ))))))

i-far-k-7 : dKI₁ 14 • dKI₁ 7 ≈ dKI₁ 7 • dKI₁ 14
i-far-k-7 = trans (trans (cong br-k-14 br-k-7) (sym (++≈ (flatB B-k-14) (flat (B-k-7 ∷ [])))))
  (trans (transport (rel s₀ ∷ rel s₂ ∷ rel s₁ ∷ rel s₀ ∷ col w₀ ∷ col w₁ ∷ col w₂ ∷ []) (TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ rel s₀ ∷ rel s₁ ∷ rel s₂ ∷ rel s₀ ∷ []) (B-k-14 ∷ B-k-7 ∷ [])) (TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ rel s₀ ∷ rel s₁ ∷ rel s₂ ∷ rel s₀ ∷ []) (B-k-7 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-k-7 br-k-14) (sym (++≈ (flatB B-k-7) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ rel s₀ ∷ rel s₁ ∷ rel s₂ ∷ rel s₀ ∷ []) (B-k-14 ∷ B-k-7 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ rel s₀ ∷ rel s₁ ∷ rel s₂ ∷ rel s₀ ∷ []) (B-k-7 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ rel s₀ ∷ rel s₁ ∷ rel s₂ ∷ rel s₀ ∷ []) (B-k-14 ∷ B-k-7 ∷ [])} {(HC19-2 ∷ HC19-3 ∷ [])} (re lem-respell-hyb-CS12-CS12-CK12-CS12-CX13-CS23-CS23-CS23---⟶-CS02-CS02-CK02-CS02-CX03-CS23-CS23-CS23- (re lem-respell-hyb-CS02-CS02-CK20-CS02-CX21-CS01-CS01-CS01---⟶-CS02-CS02-CK20-CS02-CX23-CS03-CS03-CS03- ([]ʳ))))
      (trans (sym hcls-19) (sym (resp {TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ rel s₀ ∷ rel s₁ ∷ rel s₂ ∷ rel s₀ ∷ []) (B-k-7 ∷ B-k-14 ∷ [])} {(HC19-0 ∷ HC19-1 ∷ [])} (re lem-respell-hyb-CS02-CS02-CK20-CS02-CX21-CS01-CS01-CS01---⟶-CS02-CS02-CK20-CS02-CX23-CS03-CS03-CS03- (re lem-respell-hyb-CS12-CS12-CK12-CS12-CX13-CS23-CS23-CS23---⟶-CS02-CS02-CK02-CS02-CX03-CS23-CS23-CS23- ([]ʳ))))))

i-far-p-8 : dKI₁ 14 • dPP₁ 8 ≈ dPP₁ 8 • dKI₁ 14
i-far-p-8 = trans (trans (cong br-k-14 br-p-8) (sym (++≈ (flatB B-k-14) (flat (B-p-8 ∷ [])))))
  (trans (transport (rel s₂ ∷ col w₁ ∷ col w₃ ∷ []) (TF (col w₃ ∷ col w₁ ∷ rel s₂ ∷ []) (B-k-14 ∷ B-p-8 ∷ [])) (TF (col w₃ ∷ col w₁ ∷ rel s₂ ∷ []) (B-p-8 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-p-8 br-k-14) (sym (++≈ (flatB B-p-8) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₃ ∷ col w₁ ∷ rel s₂ ∷ []) (B-k-14 ∷ B-p-8 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₃ ∷ col w₁ ∷ rel s₂ ∷ []) (B-p-8 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₃ ∷ col w₁ ∷ rel s₂ ∷ []) (B-k-14 ∷ B-p-8 ∷ [])} {(HC0-0 ∷ HC0-1 ∷ [])} (re lem-respell-hyb-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03---⟶-CS03-CS03-CK30-CS03-CX31-CS01-CS01-CS01- (re lem-resp-TOFF013-CS02-TOFF013-CSd02 ([]ʳ))))
      (trans hcls-0 (sym (resp {TF (col w₃ ∷ col w₁ ∷ rel s₂ ∷ []) (B-p-8 ∷ B-k-14 ∷ [])} {(HC0-2 ∷ HC0-3 ∷ [])} (re lem-resp-TOFF013-CS02-TOFF013-CSd02 (re lem-respell-hyb-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03---⟶-CS03-CS03-CK30-CS03-CX31-CS01-CS01-CS01- ([]ʳ))))))

i-far-l-8 : dKI₁ 14 • lo₁ 8 ≈ lo₁ 8 • dKI₁ 14
i-far-l-8 = trans (trans (cong br-k-14 br-l-8) (sym (++≈ (flatB B-k-14) (flat (B-l-8 ∷ [])))))
  (trans (transport (rel s₂ ∷ col w₁ ∷ col w₃ ∷ []) (TF (col w₃ ∷ col w₁ ∷ rel s₂ ∷ []) (B-k-14 ∷ B-l-8 ∷ [])) (TF (col w₃ ∷ col w₁ ∷ rel s₂ ∷ []) (B-l-8 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-l-8 br-k-14) (sym (++≈ (flatB B-l-8) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₃ ∷ col w₁ ∷ rel s₂ ∷ []) (B-k-14 ∷ B-l-8 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₃ ∷ col w₁ ∷ rel s₂ ∷ []) (B-l-8 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₃ ∷ col w₁ ∷ rel s₂ ∷ []) (B-k-14 ∷ B-l-8 ∷ [])} {(HC1-0 ∷ HC1-1 ∷ [])} (re lem-respell-hyb-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03---⟶-CS03-CS03-CK30-CS03-CX31-CS01-CS01-CS01- (re lem-resp-S0-K0-CS02-TOFF013-CSd02-TOFF013-Kd0-Sd0 ([]ʳ))))
      (trans hcls-1 (sym (resp {TF (col w₃ ∷ col w₁ ∷ rel s₂ ∷ []) (B-l-8 ∷ B-k-14 ∷ [])} {(HC1-2 ∷ HC1-3 ∷ [])} (re lem-resp-S0-K0-CS02-TOFF013-CSd02-TOFF013-Kd0-Sd0 (re lem-respell-hyb-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03---⟶-CS03-CS03-CK30-CS03-CX31-CS01-CS01-CS01- ([]ʳ))))))

i-far-k-8 : dKI₁ 14 • dKI₁ 8 ≈ dKI₁ 8 • dKI₁ 14
i-far-k-8 = trans (trans (cong br-k-14 br-k-8) (sym (++≈ (flatB B-k-14) (flat (B-k-8 ∷ [])))))
  (trans (transport (rel s₂ ∷ col w₀ ∷ col w₁ ∷ []) (TF (col w₁ ∷ col w₀ ∷ rel s₂ ∷ []) (B-k-14 ∷ B-k-8 ∷ [])) (TF (col w₁ ∷ col w₀ ∷ rel s₂ ∷ []) (B-k-8 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-k-8 br-k-14) (sym (++≈ (flatB B-k-8) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₁ ∷ col w₀ ∷ rel s₂ ∷ []) (B-k-14 ∷ B-k-8 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₁ ∷ col w₀ ∷ rel s₂ ∷ []) (B-k-8 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₁ ∷ col w₀ ∷ rel s₂ ∷ []) (B-k-14 ∷ B-k-8 ∷ [])} {(HC2-2 ∷ HC2-3 ∷ [])} (re lem-respell-hyb-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03---⟶-CS03-CS03-CK30-CS03-CX31-CS01-CS01-CS01- (re lem-respell-hyb-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03---⟶-CS03-CS03-CK30-CS03-CX31-CS01-CS01-CS01- ([]ʳ))))
      (trans (sym hcls-2) (sym (resp {TF (col w₁ ∷ col w₀ ∷ rel s₂ ∷ []) (B-k-8 ∷ B-k-14 ∷ [])} {(HC2-0 ∷ HC2-1 ∷ [])} (re lem-respell-hyb-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03---⟶-CS03-CS03-CK30-CS03-CX31-CS01-CS01-CS01- (re lem-respell-hyb-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03---⟶-CS03-CS03-CK30-CS03-CX31-CS01-CS01-CS01- ([]ʳ))))))

i-far-p-9 : dKI₁ 14 • dPP₁ 9 ≈ dPP₁ 9 • dKI₁ 14
i-far-p-9 = trans (trans (cong br-k-14 br-p-9) (sym (++≈ (flatB B-k-14) (flat (B-p-9 ∷ [])))))
  (trans (transport (rel s₂ ∷ rel s₁ ∷ col w₂ ∷ col w₃ ∷ []) (TF (col w₃ ∷ col w₂ ∷ rel s₁ ∷ rel s₂ ∷ []) (B-k-14 ∷ B-p-9 ∷ [])) (TF (col w₃ ∷ col w₂ ∷ rel s₁ ∷ rel s₂ ∷ []) (B-p-9 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-p-9 br-k-14) (sym (++≈ (flatB B-p-9) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₃ ∷ col w₂ ∷ rel s₁ ∷ rel s₂ ∷ []) (B-k-14 ∷ B-p-9 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₃ ∷ col w₂ ∷ rel s₁ ∷ rel s₂ ∷ []) (B-p-9 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₃ ∷ col w₂ ∷ rel s₁ ∷ rel s₂ ∷ []) (B-k-14 ∷ B-p-9 ∷ [])} {(HC3-0 ∷ HC3-1 ∷ [])} (re lem-respell-hyb-CS02-CS02-CK20-CS02-CX23-CS03-CS03-CS03---⟶-CS03-CS03-CK30-CS03-CX32-CS02-CS02-CS02- (re lem-resp-TOFF203-CS12-TOFF203-CSd12 ([]ʳ))))
      (trans hcls-3 (sym (resp {TF (col w₃ ∷ col w₂ ∷ rel s₁ ∷ rel s₂ ∷ []) (B-p-9 ∷ B-k-14 ∷ [])} {(HC3-2 ∷ HC3-3 ∷ [])} (re lem-resp-TOFF203-CS12-TOFF203-CSd12 (re lem-respell-hyb-CS02-CS02-CK20-CS02-CX23-CS03-CS03-CS03---⟶-CS03-CS03-CK30-CS03-CX32-CS02-CS02-CS02- ([]ʳ))))))

i-far-l-9 : dKI₁ 14 • lo₁ 9 ≈ lo₁ 9 • dKI₁ 14
i-far-l-9 = trans (trans (cong br-k-14 br-l-9) (sym (++≈ (flatB B-k-14) (flat (B-l-9 ∷ [])))))
  (trans (transport (rel s₂ ∷ rel s₁ ∷ col w₂ ∷ col w₃ ∷ []) (TF (col w₃ ∷ col w₂ ∷ rel s₁ ∷ rel s₂ ∷ []) (B-k-14 ∷ B-l-9 ∷ [])) (TF (col w₃ ∷ col w₂ ∷ rel s₁ ∷ rel s₂ ∷ []) (B-l-9 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-l-9 br-k-14) (sym (++≈ (flatB B-l-9) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₃ ∷ col w₂ ∷ rel s₁ ∷ rel s₂ ∷ []) (B-k-14 ∷ B-l-9 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₃ ∷ col w₂ ∷ rel s₁ ∷ rel s₂ ∷ []) (B-l-9 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₃ ∷ col w₂ ∷ rel s₁ ∷ rel s₂ ∷ []) (B-k-14 ∷ B-l-9 ∷ [])} {(HC4-0 ∷ HC4-1 ∷ [])} (re lem-respell-hyb-CS02-CS02-CK20-CS02-CX23-CS03-CS03-CS03---⟶-CS03-CS03-CK30-CS03-CX32-CS02-CS02-CS02- (re lem-resp-S2-K2-CS12-TOFF203-CSd12-TOFF203-Kd2-Sd2 ([]ʳ))))
      (trans hcls-4 (sym (resp {TF (col w₃ ∷ col w₂ ∷ rel s₁ ∷ rel s₂ ∷ []) (B-l-9 ∷ B-k-14 ∷ [])} {(HC4-2 ∷ HC4-3 ∷ [])} (re lem-resp-S2-K2-CS12-TOFF203-CSd12-TOFF203-Kd2-Sd2 (re lem-respell-hyb-CS02-CS02-CK20-CS02-CX23-CS03-CS03-CS03---⟶-CS03-CS03-CK30-CS03-CX32-CS02-CS02-CS02- ([]ʳ))))))

i-far-k-9 : dKI₁ 14 • dKI₁ 9 ≈ dKI₁ 9 • dKI₁ 14
i-far-k-9 = trans (trans (cong br-k-14 br-k-9) (sym (++≈ (flatB B-k-14) (flat (B-k-9 ∷ [])))))
  (trans (transport (rel s₀ ∷ rel s₂ ∷ col w₀ ∷ []) (TF (col w₀ ∷ rel s₂ ∷ rel s₀ ∷ []) (B-k-14 ∷ B-k-9 ∷ [])) (TF (col w₀ ∷ rel s₂ ∷ rel s₀ ∷ []) (B-k-9 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-k-9 br-k-14) (sym (++≈ (flatB B-k-9) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₀ ∷ rel s₂ ∷ rel s₀ ∷ []) (B-k-14 ∷ B-k-9 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₀ ∷ rel s₂ ∷ rel s₀ ∷ []) (B-k-9 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₀ ∷ rel s₂ ∷ rel s₀ ∷ []) (B-k-14 ∷ B-k-9 ∷ [])} {(HC5-2 ∷ HC5-3 ∷ [])} (re lem-respell-hyb-CS01-CS01-CK01-CS01-CX03-CS13-CS13-CS13---⟶-CS13-CS13-CK31-CS13-CX30-CS01-CS01-CS01- (same ([]ʳ))))
      (trans (sym hcls-5) (sym (resp {TF (col w₀ ∷ rel s₂ ∷ rel s₀ ∷ []) (B-k-9 ∷ B-k-14 ∷ [])} {(HC5-0 ∷ HC5-1 ∷ [])} (same (re lem-respell-hyb-CS01-CS01-CK01-CS01-CX03-CS13-CS13-CS13---⟶-CS13-CS13-CK31-CS13-CX30-CS01-CS01-CS01- ([]ʳ))))))

i-far-p-10 : dKI₁ 14 • dPP₁ 10 ≈ dPP₁ 10 • dKI₁ 14
i-far-p-10 = trans (trans (cong br-k-14 br-p-10) (sym (++≈ (flatB B-k-14) (flat (B-p-10 ∷ [])))))
  (trans (transport (rel s₂ ∷ rel s₁ ∷ col w₂ ∷ col w₃ ∷ []) (TF (col w₃ ∷ col w₂ ∷ rel s₁ ∷ rel s₂ ∷ []) (B-k-14 ∷ B-p-10 ∷ [])) (TF (col w₃ ∷ col w₂ ∷ rel s₁ ∷ rel s₂ ∷ []) (B-p-10 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-p-10 br-k-14) (sym (++≈ (flatB B-p-10) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₃ ∷ col w₂ ∷ rel s₁ ∷ rel s₂ ∷ []) (B-k-14 ∷ B-p-10 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₃ ∷ col w₂ ∷ rel s₁ ∷ rel s₂ ∷ []) (B-p-10 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₃ ∷ col w₂ ∷ rel s₁ ∷ rel s₂ ∷ []) (B-k-14 ∷ B-p-10 ∷ [])} {(HC6-0 ∷ HC6-1 ∷ [])} (same (re lem-resp-TOFF023-CS01-TOFF023-CSd01 ([]ʳ))))
      (trans hcls-6 (sym (resp {TF (col w₃ ∷ col w₂ ∷ rel s₁ ∷ rel s₂ ∷ []) (B-p-10 ∷ B-k-14 ∷ [])} {(HC6-2 ∷ HC6-3 ∷ [])} (re lem-resp-TOFF023-CS01-TOFF023-CSd01 (same ([]ʳ))))))

i-far-l-10 : dKI₁ 14 • lo₁ 10 ≈ lo₁ 10 • dKI₁ 14
i-far-l-10 = trans (trans (cong br-k-14 br-l-10) (sym (++≈ (flatB B-k-14) (flat (B-l-10 ∷ [])))))
  (trans (transport (rel s₂ ∷ rel s₁ ∷ col w₂ ∷ col w₃ ∷ []) (TF (col w₃ ∷ col w₂ ∷ rel s₁ ∷ rel s₂ ∷ []) (B-k-14 ∷ B-l-10 ∷ [])) (TF (col w₃ ∷ col w₂ ∷ rel s₁ ∷ rel s₂ ∷ []) (B-l-10 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-l-10 br-k-14) (sym (++≈ (flatB B-l-10) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₃ ∷ col w₂ ∷ rel s₁ ∷ rel s₂ ∷ []) (B-k-14 ∷ B-l-10 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₃ ∷ col w₂ ∷ rel s₁ ∷ rel s₂ ∷ []) (B-l-10 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₃ ∷ col w₂ ∷ rel s₁ ∷ rel s₂ ∷ []) (B-k-14 ∷ B-l-10 ∷ [])} {(HC7-0 ∷ HC7-1 ∷ [])} (same (re lem-resp-S0-K0-CS01-TOFF023-CSd01-TOFF023-Kd0-Sd0 ([]ʳ))))
      (trans hcls-7 (sym (resp {TF (col w₃ ∷ col w₂ ∷ rel s₁ ∷ rel s₂ ∷ []) (B-l-10 ∷ B-k-14 ∷ [])} {(HC7-2 ∷ HC7-3 ∷ [])} (re lem-resp-S0-K0-CS01-TOFF023-CSd01-TOFF023-Kd0-Sd0 (same ([]ʳ))))))

i-far-k-10 : dKI₁ 14 • dKI₁ 10 ≈ dKI₁ 10 • dKI₁ 14
i-far-k-10 = trans (trans (cong br-k-14 br-k-10) (sym (++≈ (flatB B-k-14) (flat (B-k-10 ∷ [])))))
  (trans (transport (rel s₂ ∷ rel s₁ ∷ []) (TF (rel s₁ ∷ rel s₂ ∷ []) (B-k-14 ∷ B-k-10 ∷ [])) (TF (rel s₁ ∷ rel s₂ ∷ []) (B-k-10 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-k-10 br-k-14) (sym (++≈ (flatB B-k-10) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (rel s₁ ∷ rel s₂ ∷ []) (B-k-14 ∷ B-k-10 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (rel s₁ ∷ rel s₂ ∷ []) (B-k-10 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (rel s₁ ∷ rel s₂ ∷ []) (B-k-14 ∷ B-k-10 ∷ [])} {(HC8-2 ∷ HC8-3 ∷ [])} (same (same ([]ʳ))))
      (trans (sym hcls-8) (sym (resp {TF (rel s₁ ∷ rel s₂ ∷ []) (B-k-10 ∷ B-k-14 ∷ [])} {(HC8-0 ∷ HC8-1 ∷ [])} (same (same ([]ʳ))))))

i-far-p-11 : dKI₁ 14 • dPP₁ 11 ≈ dPP₁ 11 • dKI₁ 14
i-far-p-11 = trans (trans (cong br-k-14 br-p-11) (sym (++≈ (flatB B-k-14) (flat (B-p-11 ∷ [])))))
  (trans (transport (rel s₁ ∷ rel s₂ ∷ col w₁ ∷ col w₃ ∷ []) (TF (col w₃ ∷ col w₁ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-p-11 ∷ [])) (TF (col w₃ ∷ col w₁ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-p-11 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-p-11 br-k-14) (sym (++≈ (flatB B-p-11) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₃ ∷ col w₁ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-p-11 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₃ ∷ col w₁ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-p-11 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₃ ∷ col w₁ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-p-11 ∷ [])} {(HC17-0 ∷ HC17-1 ∷ [])} (re lem-respell-hyb-CS03-CS03-CK30-CS03-CX31-CS01-CS01-CS01---⟶-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03- (re lem-resp-TOFF103-CS12-TOFF103-CSd12 ([]ʳ))))
      (trans hcls-17 (sym (resp {TF (col w₃ ∷ col w₁ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-p-11 ∷ B-k-14 ∷ [])} {(HC17-2 ∷ HC17-3 ∷ [])} (re lem-resp-TOFF103-CS12-TOFF103-CSd12 (re lem-respell-hyb-CS03-CS03-CK30-CS03-CX31-CS01-CS01-CS01---⟶-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03- ([]ʳ))))))

i-far-l-11 : dKI₁ 14 • lo₁ 11 ≈ lo₁ 11 • dKI₁ 14
i-far-l-11 = trans (trans (cong br-k-14 br-l-11) (sym (++≈ (flatB B-k-14) (flat (B-l-11 ∷ [])))))
  (trans (transport (rel s₁ ∷ rel s₂ ∷ col w₁ ∷ col w₃ ∷ []) (TF (col w₃ ∷ col w₁ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-l-11 ∷ [])) (TF (col w₃ ∷ col w₁ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-l-11 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-l-11 br-k-14) (sym (++≈ (flatB B-l-11) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₃ ∷ col w₁ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-l-11 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₃ ∷ col w₁ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-l-11 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₃ ∷ col w₁ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-l-11 ∷ [])} {(HC18-0 ∷ HC18-1 ∷ [])} (re lem-respell-hyb-CS03-CS03-CK30-CS03-CX31-CS01-CS01-CS01---⟶-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03- (re lem-resp-S1-K1-CS12-TOFF103-CSd12-TOFF103-Kd1-Sd1 ([]ʳ))))
      (trans hcls-18 (sym (resp {TF (col w₃ ∷ col w₁ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-l-11 ∷ B-k-14 ∷ [])} {(HC18-2 ∷ HC18-3 ∷ [])} (re lem-resp-S1-K1-CS12-TOFF103-CSd12-TOFF103-Kd1-Sd1 (re lem-respell-hyb-CS03-CS03-CK30-CS03-CX31-CS01-CS01-CS01---⟶-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03- ([]ʳ))))))

i-far-k-11 : dKI₁ 14 • dKI₁ 11 ≈ dKI₁ 11 • dKI₁ 14
i-far-k-11 = trans (trans (cong br-k-14 br-k-11) (sym (++≈ (flatB B-k-14) (flat (B-k-11 ∷ [])))))
  (trans (transport (rel s₁ ∷ rel s₀ ∷ rel s₂ ∷ rel s₁ ∷ col w₂ ∷ []) (TF (col w₂ ∷ rel s₁ ∷ rel s₂ ∷ rel s₀ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-k-11 ∷ [])) (TF (col w₂ ∷ rel s₁ ∷ rel s₂ ∷ rel s₀ ∷ rel s₁ ∷ []) (B-k-11 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-k-11 br-k-14) (sym (++≈ (flatB B-k-11) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₂ ∷ rel s₁ ∷ rel s₂ ∷ rel s₀ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-k-11 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₂ ∷ rel s₁ ∷ rel s₂ ∷ rel s₀ ∷ rel s₁ ∷ []) (B-k-11 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₂ ∷ rel s₁ ∷ rel s₂ ∷ rel s₀ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-k-11 ∷ [])} {(HC19-2 ∷ HC19-3 ∷ [])} (re lem-respell-hyb-CS23-CS23-CK32-CS23-CX30-CS02-CS02-CS02---⟶-CS02-CS02-CK02-CS02-CX03-CS23-CS23-CS23- (same ([]ʳ))))
      (trans (sym hcls-19) (sym (resp {TF (col w₂ ∷ rel s₁ ∷ rel s₂ ∷ rel s₀ ∷ rel s₁ ∷ []) (B-k-11 ∷ B-k-14 ∷ [])} {(HC19-0 ∷ HC19-1 ∷ [])} (same (re lem-respell-hyb-CS23-CS23-CK32-CS23-CX30-CS02-CS02-CS02---⟶-CS02-CS02-CK02-CS02-CX03-CS23-CS23-CS23- ([]ʳ))))))

i-far-p-12 : dKI₁ 14 • dPP₁ 12 ≈ dPP₁ 12 • dKI₁ 14
i-far-p-12 = trans (trans (cong br-k-14 br-p-12) (sym (++≈ (flatB B-k-14) (flat (B-p-12 ∷ [])))))
  (trans (transport (rel s₁ ∷ rel s₂ ∷ col w₁ ∷ col w₃ ∷ []) (TF (col w₃ ∷ col w₁ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-p-12 ∷ [])) (TF (col w₃ ∷ col w₁ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-p-12 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-p-12 br-k-14) (sym (++≈ (flatB B-p-12) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₃ ∷ col w₁ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-p-12 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₃ ∷ col w₁ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-p-12 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₃ ∷ col w₁ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-p-12 ∷ [])} {(HC0-0 ∷ HC0-1 ∷ [])} (same (re lem-resp-TOFF013-CS02-TOFF013-CSd02 ([]ʳ))))
      (trans hcls-0 (sym (resp {TF (col w₃ ∷ col w₁ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-p-12 ∷ B-k-14 ∷ [])} {(HC0-2 ∷ HC0-3 ∷ [])} (re lem-resp-TOFF013-CS02-TOFF013-CSd02 (same ([]ʳ))))))

i-far-l-12 : dKI₁ 14 • lo₁ 12 ≈ lo₁ 12 • dKI₁ 14
i-far-l-12 = trans (trans (cong br-k-14 br-l-12) (sym (++≈ (flatB B-k-14) (flat (B-l-12 ∷ [])))))
  (trans (transport (rel s₁ ∷ rel s₂ ∷ col w₁ ∷ col w₃ ∷ []) (TF (col w₃ ∷ col w₁ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-l-12 ∷ [])) (TF (col w₃ ∷ col w₁ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-l-12 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-l-12 br-k-14) (sym (++≈ (flatB B-l-12) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₃ ∷ col w₁ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-l-12 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₃ ∷ col w₁ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-l-12 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₃ ∷ col w₁ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-l-12 ∷ [])} {(HC1-0 ∷ HC1-1 ∷ [])} (same (re lem-resp-S0-K0-CS02-TOFF013-CSd02-TOFF013-Kd0-Sd0 ([]ʳ))))
      (trans hcls-1 (sym (resp {TF (col w₃ ∷ col w₁ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-l-12 ∷ B-k-14 ∷ [])} {(HC1-2 ∷ HC1-3 ∷ [])} (re lem-resp-S0-K0-CS02-TOFF013-CSd02-TOFF013-Kd0-Sd0 (same ([]ʳ))))))

i-far-k-12 : dKI₁ 14 • dKI₁ 12 ≈ dKI₁ 12 • dKI₁ 14
i-far-k-12 = trans (trans (cong br-k-14 br-k-12) (sym (++≈ (flatB B-k-14) (flat (B-k-12 ∷ [])))))
  (trans (transport (rel s₁ ∷ rel s₂ ∷ col w₀ ∷ col w₁ ∷ []) (TF (col w₁ ∷ col w₀ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-k-12 ∷ [])) (TF (col w₁ ∷ col w₀ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-k-12 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-k-12 br-k-14) (sym (++≈ (flatB B-k-12) (flat (B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₁ ∷ col w₀ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-k-12 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₁ ∷ col w₀ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-k-12 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₁ ∷ col w₀ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-k-14 ∷ B-k-12 ∷ [])} {(HC2-2 ∷ HC2-3 ∷ [])} (same (same ([]ʳ))))
      (trans (sym hcls-2) (sym (resp {TF (col w₁ ∷ col w₀ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-k-12 ∷ B-k-14 ∷ [])} {(HC2-0 ∷ HC2-1 ∷ [])} (same (same ([]ʳ))))))

i-shift-0 : lo₁ 0 • lo₁ 1 • dKI₁ 0 ≈ dKI₁ 1 • lo₁ 0 • lo₁ 1
i-shift-0 = trans (trans (cong br-l-0 (trans (cong br-l-1 br-k-0) (sym (++≈ (flatB B-l-1) (flat (B-k-0 ∷ [])))))) (sym (++≈ (flatB B-l-0) (flat (B-l-1 ∷ B-k-0 ∷ [])))))
  (trans (transport (rel s₂ ∷ col w₁ ∷ col w₂ ∷ col w₃ ∷ []) (TF (col w₃ ∷ col w₂ ∷ col w₁ ∷ rel s₂ ∷ []) (B-l-0 ∷ B-l-1 ∷ B-k-0 ∷ [])) (TF (col w₃ ∷ col w₂ ∷ col w₁ ∷ rel s₂ ∷ []) (B-k-1 ∷ B-l-0 ∷ B-l-1 ∷ [])) tt tt e)
         (sym (trans (cong br-k-1 (trans (cong br-l-0 br-l-1) (sym (++≈ (flatB B-l-0) (flat (B-l-1 ∷ [])))))) (sym (++≈ (flatB B-k-1) (flat (B-l-0 ∷ B-l-1 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₃ ∷ col w₂ ∷ col w₁ ∷ rel s₂ ∷ []) (B-l-0 ∷ B-l-1 ∷ B-k-0 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₃ ∷ col w₂ ∷ col w₁ ∷ rel s₂ ∷ []) (B-k-1 ∷ B-l-0 ∷ B-l-1 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₃ ∷ col w₂ ∷ col w₁ ∷ rel s₂ ∷ []) (B-l-0 ∷ B-l-1 ∷ B-k-0 ∷ [])} {(HC20-0 ∷ HC20-1 ∷ HC20-2 ∷ [])} (re lem-resp-S0-K0-CS02-TOFF013-CSd02-TOFF013-Kd0-Sd0 (re lem-resp-S1-K1-CS12-TOFF103-CSd12-TOFF103-Kd1-Sd1 (same ([]ʳ)))))
      (trans hcls-20 (sym (resp {TF (col w₃ ∷ col w₂ ∷ col w₁ ∷ rel s₂ ∷ []) (B-k-1 ∷ B-l-0 ∷ B-l-1 ∷ [])} {(HC20-3 ∷ HC20-4 ∷ HC20-5 ∷ [])} (same (re lem-resp-S0-K0-CS02-TOFF013-CSd02-TOFF013-Kd0-Sd0 (re lem-resp-S1-K1-CS12-TOFF103-CSd12-TOFF103-Kd1-Sd1 ([]ʳ)))))))

i-shift-1 : lo₁ 1 • lo₁ 2 • dKI₁ 1 ≈ dKI₁ 2 • lo₁ 1 • lo₁ 2
i-shift-1 = trans (trans (cong br-l-1 (trans (cong br-l-2 br-k-1) (sym (++≈ (flatB B-l-2) (flat (B-k-1 ∷ [])))))) (sym (++≈ (flatB B-l-1) (flat (B-l-2 ∷ B-k-1 ∷ [])))))
  (trans (transport (rel s₀ ∷ rel s₂ ∷ col w₂ ∷ col w₃ ∷ []) (TF (col w₃ ∷ col w₂ ∷ rel s₂ ∷ rel s₀ ∷ []) (B-l-1 ∷ B-l-2 ∷ B-k-1 ∷ [])) (TF (col w₃ ∷ col w₂ ∷ rel s₂ ∷ rel s₀ ∷ []) (B-k-2 ∷ B-l-1 ∷ B-l-2 ∷ [])) tt tt e)
         (sym (trans (cong br-k-2 (trans (cong br-l-1 br-l-2) (sym (++≈ (flatB B-l-1) (flat (B-l-2 ∷ [])))))) (sym (++≈ (flatB B-k-2) (flat (B-l-1 ∷ B-l-2 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₃ ∷ col w₂ ∷ rel s₂ ∷ rel s₀ ∷ []) (B-l-1 ∷ B-l-2 ∷ B-k-1 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₃ ∷ col w₂ ∷ rel s₂ ∷ rel s₀ ∷ []) (B-k-2 ∷ B-l-1 ∷ B-l-2 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₃ ∷ col w₂ ∷ rel s₂ ∷ rel s₀ ∷ []) (B-l-1 ∷ B-l-2 ∷ B-k-1 ∷ [])} {(HC20-0 ∷ HC20-1 ∷ HC20-2 ∷ [])} (re lem-resp-S0-K0-CS02-TOFF013-CSd02-TOFF013-Kd0-Sd0 (re lem-resp-S1-K1-CS12-TOFF103-CSd12-TOFF103-Kd1-Sd1 (same ([]ʳ)))))
      (trans hcls-20 (sym (resp {TF (col w₃ ∷ col w₂ ∷ rel s₂ ∷ rel s₀ ∷ []) (B-k-2 ∷ B-l-1 ∷ B-l-2 ∷ [])} {(HC20-3 ∷ HC20-4 ∷ HC20-5 ∷ [])} (same (re lem-resp-S0-K0-CS02-TOFF013-CSd02-TOFF013-Kd0-Sd0 (re lem-resp-S1-K1-CS12-TOFF103-CSd12-TOFF103-Kd1-Sd1 ([]ʳ)))))))

i-shift-2 : lo₁ 2 • lo₁ 3 • dKI₁ 2 ≈ dKI₁ 3 • lo₁ 2 • lo₁ 3
i-shift-2 = trans (trans (cong br-l-2 (trans (cong br-l-3 br-k-2) (sym (++≈ (flatB B-l-3) (flat (B-k-2 ∷ [])))))) (sym (++≈ (flatB B-l-2) (flat (B-l-3 ∷ B-k-2 ∷ [])))))
  (trans (transport (rel s₁ ∷ rel s₂ ∷ col w₀ ∷ col w₁ ∷ col w₂ ∷ []) (TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-l-2 ∷ B-l-3 ∷ B-k-2 ∷ [])) (TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-k-3 ∷ B-l-2 ∷ B-l-3 ∷ [])) tt tt e)
         (sym (trans (cong br-k-3 (trans (cong br-l-2 br-l-3) (sym (++≈ (flatB B-l-2) (flat (B-l-3 ∷ [])))))) (sym (++≈ (flatB B-k-3) (flat (B-l-2 ∷ B-l-3 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-l-2 ∷ B-l-3 ∷ B-k-2 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-k-3 ∷ B-l-2 ∷ B-l-3 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-l-2 ∷ B-l-3 ∷ B-k-2 ∷ [])} {(HC20-0 ∷ HC20-1 ∷ HC20-2 ∷ [])} (re lem-resp-S0-K0-CS02-TOFF013-CSd02-TOFF013-Kd0-Sd0 (re lem-resp-S1-K1-CS12-TOFF103-CSd12-TOFF103-Kd1-Sd1 (re lem-respell-hyb-CS03-CS03-CK30-CS03-CX31-CS01-CS01-CS01---⟶-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03- ([]ʳ)))))
      (trans hcls-20 (sym (resp {TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-k-3 ∷ B-l-2 ∷ B-l-3 ∷ [])} {(HC20-3 ∷ HC20-4 ∷ HC20-5 ∷ [])} (same (re lem-resp-S0-K0-CS02-TOFF013-CSd02-TOFF013-Kd0-Sd0 (re lem-resp-S1-K1-CS12-TOFF103-CSd12-TOFF103-Kd1-Sd1 ([]ʳ)))))))

i-shift-3 : lo₁ 3 • lo₁ 4 • dKI₁ 3 ≈ dKI₁ 4 • lo₁ 3 • lo₁ 4
i-shift-3 = trans (trans (cong br-l-3 (trans (cong br-l-4 br-k-3) (sym (++≈ (flatB B-l-4) (flat (B-k-3 ∷ [])))))) (sym (++≈ (flatB B-l-3) (flat (B-l-4 ∷ B-k-3 ∷ [])))))
  (trans (transport (rel s₁ ∷ rel s₀ ∷ col w₁ ∷ col w₃ ∷ []) (TF (col w₃ ∷ col w₁ ∷ rel s₀ ∷ rel s₁ ∷ []) (B-l-3 ∷ B-l-4 ∷ B-k-3 ∷ [])) (TF (col w₃ ∷ col w₁ ∷ rel s₀ ∷ rel s₁ ∷ []) (B-k-4 ∷ B-l-3 ∷ B-l-4 ∷ [])) tt tt e)
         (sym (trans (cong br-k-4 (trans (cong br-l-3 br-l-4) (sym (++≈ (flatB B-l-3) (flat (B-l-4 ∷ [])))))) (sym (++≈ (flatB B-k-4) (flat (B-l-3 ∷ B-l-4 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₃ ∷ col w₁ ∷ rel s₀ ∷ rel s₁ ∷ []) (B-l-3 ∷ B-l-4 ∷ B-k-3 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₃ ∷ col w₁ ∷ rel s₀ ∷ rel s₁ ∷ []) (B-k-4 ∷ B-l-3 ∷ B-l-4 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₃ ∷ col w₁ ∷ rel s₀ ∷ rel s₁ ∷ []) (B-l-3 ∷ B-l-4 ∷ B-k-3 ∷ [])} {(HC20-0 ∷ HC20-1 ∷ HC20-2 ∷ [])} (same (same (re lem-respell-hyb-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02---⟶-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03- ([]ʳ)))))
      (trans hcls-20 (sym (resp {TF (col w₃ ∷ col w₁ ∷ rel s₀ ∷ rel s₁ ∷ []) (B-k-4 ∷ B-l-3 ∷ B-l-4 ∷ [])} {(HC20-3 ∷ HC20-4 ∷ HC20-5 ∷ [])} (re lem-respell-hyb-CS12-CS12-CK21-CS12-CX20-CS01-CS01-CS01---⟶-CS01-CS01-CK01-CS01-CX03-CS13-CS13-CS13- (same (same ([]ʳ)))))))

i-shift-4 : lo₁ 4 • lo₁ 5 • dKI₁ 4 ≈ dKI₁ 5 • lo₁ 4 • lo₁ 5
i-shift-4 = trans (trans (cong br-l-4 (trans (cong br-l-5 br-k-4) (sym (++≈ (flatB B-l-5) (flat (B-k-4 ∷ [])))))) (sym (++≈ (flatB B-l-4) (flat (B-l-5 ∷ B-k-4 ∷ [])))))
  (trans (transport (rel s₂ ∷ col w₂ ∷ []) (TF (col w₂ ∷ rel s₂ ∷ []) (B-l-4 ∷ B-l-5 ∷ B-k-4 ∷ [])) (TF (col w₂ ∷ rel s₂ ∷ []) (B-k-5 ∷ B-l-4 ∷ B-l-5 ∷ [])) tt tt e)
         (sym (trans (cong br-k-5 (trans (cong br-l-4 br-l-5) (sym (++≈ (flatB B-l-4) (flat (B-l-5 ∷ [])))))) (sym (++≈ (flatB B-k-5) (flat (B-l-4 ∷ B-l-5 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₂ ∷ rel s₂ ∷ []) (B-l-4 ∷ B-l-5 ∷ B-k-4 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₂ ∷ rel s₂ ∷ []) (B-k-5 ∷ B-l-4 ∷ B-l-5 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₂ ∷ rel s₂ ∷ []) (B-l-4 ∷ B-l-5 ∷ B-k-4 ∷ [])} {(HC20-0 ∷ HC20-1 ∷ HC20-2 ∷ [])} (re lem-resp-S0-K0-CS02-TOFF013-CSd02-TOFF013-Kd0-Sd0 (re lem-resp-S1-K1-CS12-TOFF103-CSd12-TOFF103-Kd1-Sd1 (same ([]ʳ)))))
      (trans hcls-20 (sym (resp {TF (col w₂ ∷ rel s₂ ∷ []) (B-k-5 ∷ B-l-4 ∷ B-l-5 ∷ [])} {(HC20-3 ∷ HC20-4 ∷ HC20-5 ∷ [])} (same (re lem-resp-S0-K0-CS02-TOFF013-CSd02-TOFF013-Kd0-Sd0 (re lem-resp-S1-K1-CS12-TOFF103-CSd12-TOFF103-Kd1-Sd1 ([]ʳ)))))))

i-shift-5 : lo₁ 5 • lo₁ 6 • dKI₁ 5 ≈ dKI₁ 6 • lo₁ 5 • lo₁ 6
i-shift-5 = trans (trans (cong br-l-5 (trans (cong br-l-6 br-k-5) (sym (++≈ (flatB B-l-6) (flat (B-k-5 ∷ [])))))) (sym (++≈ (flatB B-l-5) (flat (B-l-6 ∷ B-k-5 ∷ [])))))
  (trans (transport (rel s₀ ∷ rel s₂ ∷ col w₀ ∷ col w₂ ∷ []) (TF (col w₂ ∷ col w₀ ∷ rel s₂ ∷ rel s₀ ∷ []) (B-l-5 ∷ B-l-6 ∷ B-k-5 ∷ [])) (TF (col w₂ ∷ col w₀ ∷ rel s₂ ∷ rel s₀ ∷ []) (B-k-6 ∷ B-l-5 ∷ B-l-6 ∷ [])) tt tt e)
         (sym (trans (cong br-k-6 (trans (cong br-l-5 br-l-6) (sym (++≈ (flatB B-l-5) (flat (B-l-6 ∷ [])))))) (sym (++≈ (flatB B-k-6) (flat (B-l-5 ∷ B-l-6 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₂ ∷ col w₀ ∷ rel s₂ ∷ rel s₀ ∷ []) (B-l-5 ∷ B-l-6 ∷ B-k-5 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₂ ∷ col w₀ ∷ rel s₂ ∷ rel s₀ ∷ []) (B-k-6 ∷ B-l-5 ∷ B-l-6 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₂ ∷ col w₀ ∷ rel s₂ ∷ rel s₀ ∷ []) (B-l-5 ∷ B-l-6 ∷ B-k-5 ∷ [])} {(HC20-0 ∷ HC20-1 ∷ HC20-2 ∷ [])} (re lem-resp-S0-K0-CS02-TOFF013-CSd02-TOFF013-Kd0-Sd0 (re lem-resp-S1-K1-CS12-TOFF103-CSd12-TOFF103-Kd1-Sd1 (same ([]ʳ)))))
      (trans hcls-20 (sym (resp {TF (col w₂ ∷ col w₀ ∷ rel s₂ ∷ rel s₀ ∷ []) (B-k-6 ∷ B-l-5 ∷ B-l-6 ∷ [])} {(HC20-3 ∷ HC20-4 ∷ HC20-5 ∷ [])} (same (re lem-resp-S0-K0-CS02-TOFF013-CSd02-TOFF013-Kd0-Sd0 (re lem-resp-S1-K1-CS12-TOFF103-CSd12-TOFF103-Kd1-Sd1 ([]ʳ)))))))

i-shift-6 : lo₁ 6 • lo₁ 7 • dKI₁ 6 ≈ dKI₁ 7 • lo₁ 6 • lo₁ 7
i-shift-6 = trans (trans (cong br-l-6 (trans (cong br-l-7 br-k-6) (sym (++≈ (flatB B-l-7) (flat (B-k-6 ∷ [])))))) (sym (++≈ (flatB B-l-6) (flat (B-l-7 ∷ B-k-6 ∷ [])))))
  (trans (transport (rel s₁ ∷ rel s₂ ∷ rel s₁ ∷ col w₀ ∷ col w₁ ∷ col w₃ ∷ []) (TF (col w₃ ∷ col w₁ ∷ col w₀ ∷ rel s₁ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-l-6 ∷ B-l-7 ∷ B-k-6 ∷ [])) (TF (col w₃ ∷ col w₁ ∷ col w₀ ∷ rel s₁ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-k-7 ∷ B-l-6 ∷ B-l-7 ∷ [])) tt tt e)
         (sym (trans (cong br-k-7 (trans (cong br-l-6 br-l-7) (sym (++≈ (flatB B-l-6) (flat (B-l-7 ∷ [])))))) (sym (++≈ (flatB B-k-7) (flat (B-l-6 ∷ B-l-7 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₃ ∷ col w₁ ∷ col w₀ ∷ rel s₁ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-l-6 ∷ B-l-7 ∷ B-k-6 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₃ ∷ col w₁ ∷ col w₀ ∷ rel s₁ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-k-7 ∷ B-l-6 ∷ B-l-7 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₃ ∷ col w₁ ∷ col w₀ ∷ rel s₁ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-l-6 ∷ B-l-7 ∷ B-k-6 ∷ [])} {(HC21-0 ∷ HC21-1 ∷ HC21-2 ∷ [])} (re lem-resp-S0-K0-CS01-TOFF023-CSd01-TOFF023-Kd0-Sd0 (re lem-resp-S1-K1-CS12-TOFF103-CSd12-TOFF103-Kd1-Sd1 (same ([]ʳ)))))
      (trans hcls-21 (sym (resp {TF (col w₃ ∷ col w₁ ∷ col w₀ ∷ rel s₁ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-k-7 ∷ B-l-6 ∷ B-l-7 ∷ [])} {(HC21-3 ∷ HC21-4 ∷ HC21-5 ∷ [])} (same (re lem-resp-S0-K0-CS01-TOFF023-CSd01-TOFF023-Kd0-Sd0 (re lem-resp-S1-K1-CS12-TOFF103-CSd12-TOFF103-Kd1-Sd1 ([]ʳ)))))))

i-shift-7 : lo₁ 7 • lo₁ 8 • dKI₁ 7 ≈ dKI₁ 8 • lo₁ 7 • lo₁ 8
i-shift-7 = trans (trans (cong br-l-7 (trans (cong br-l-8 br-k-7) (sym (++≈ (flatB B-l-8) (flat (B-k-7 ∷ [])))))) (sym (++≈ (flatB B-l-7) (flat (B-l-8 ∷ B-k-7 ∷ [])))))
  (trans (transport (rel s₁ ∷ rel s₂ ∷ rel s₁ ∷ rel s₀ ∷ col w₁ ∷ col w₃ ∷ []) (TF (col w₃ ∷ col w₁ ∷ rel s₀ ∷ rel s₁ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-l-7 ∷ B-l-8 ∷ B-k-7 ∷ [])) (TF (col w₃ ∷ col w₁ ∷ rel s₀ ∷ rel s₁ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-k-8 ∷ B-l-7 ∷ B-l-8 ∷ [])) tt tt e)
         (sym (trans (cong br-k-8 (trans (cong br-l-7 br-l-8) (sym (++≈ (flatB B-l-7) (flat (B-l-8 ∷ [])))))) (sym (++≈ (flatB B-k-8) (flat (B-l-7 ∷ B-l-8 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₃ ∷ col w₁ ∷ rel s₀ ∷ rel s₁ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-l-7 ∷ B-l-8 ∷ B-k-7 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₃ ∷ col w₁ ∷ rel s₀ ∷ rel s₁ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-k-8 ∷ B-l-7 ∷ B-l-8 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₃ ∷ col w₁ ∷ rel s₀ ∷ rel s₁ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-l-7 ∷ B-l-8 ∷ B-k-7 ∷ [])} {(HC20-0 ∷ HC20-1 ∷ HC20-2 ∷ [])} (re lem-resp-S0-K0-CS02-TOFF013-CSd02-TOFF013-Kd0-Sd0 (re lem-resp-S1-K1-CS01-TOFF123-CSd01-TOFF123-Kd1-Sd1 (same ([]ʳ)))))
      (trans hcls-20 (sym (resp {TF (col w₃ ∷ col w₁ ∷ rel s₀ ∷ rel s₁ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-k-8 ∷ B-l-7 ∷ B-l-8 ∷ [])} {(HC20-3 ∷ HC20-4 ∷ HC20-5 ∷ [])} (re lem-respell-hyb-CS13-CS13-CK31-CS13-CX32-CS12-CS12-CS12---⟶-CS01-CS01-CK01-CS01-CX03-CS13-CS13-CS13- (re lem-resp-S0-K0-CS02-TOFF013-CSd02-TOFF013-Kd0-Sd0 (re lem-resp-S1-K1-CS01-TOFF123-CSd01-TOFF123-Kd1-Sd1 ([]ʳ)))))))

i-shift-8 : lo₁ 8 • lo₁ 9 • dKI₁ 8 ≈ dKI₁ 9 • lo₁ 8 • lo₁ 9
i-shift-8 = trans (trans (cong br-l-8 (trans (cong br-l-9 br-k-8) (sym (++≈ (flatB B-l-9) (flat (B-k-8 ∷ [])))))) (sym (++≈ (flatB B-l-8) (flat (B-l-9 ∷ B-k-8 ∷ [])))))
  (trans (transport (rel s₂ ∷ col w₁ ∷ []) (TF (col w₁ ∷ rel s₂ ∷ []) (B-l-8 ∷ B-l-9 ∷ B-k-8 ∷ [])) (TF (col w₁ ∷ rel s₂ ∷ []) (B-k-9 ∷ B-l-8 ∷ B-l-9 ∷ [])) tt tt e)
         (sym (trans (cong br-k-9 (trans (cong br-l-8 br-l-9) (sym (++≈ (flatB B-l-8) (flat (B-l-9 ∷ [])))))) (sym (++≈ (flatB B-k-9) (flat (B-l-8 ∷ B-l-9 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₁ ∷ rel s₂ ∷ []) (B-l-8 ∷ B-l-9 ∷ B-k-8 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₁ ∷ rel s₂ ∷ []) (B-k-9 ∷ B-l-8 ∷ B-l-9 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₁ ∷ rel s₂ ∷ []) (B-l-8 ∷ B-l-9 ∷ B-k-8 ∷ [])} {(HC20-0 ∷ HC20-1 ∷ HC20-2 ∷ [])} (re lem-resp-S0-K0-CS02-TOFF013-CSd02-TOFF013-Kd0-Sd0 (re lem-resp-S1-K1-CS12-TOFF103-CSd12-TOFF103-Kd1-Sd1 (same ([]ʳ)))))
      (trans hcls-20 (sym (resp {TF (col w₁ ∷ rel s₂ ∷ []) (B-k-9 ∷ B-l-8 ∷ B-l-9 ∷ [])} {(HC20-3 ∷ HC20-4 ∷ HC20-5 ∷ [])} (same (re lem-resp-S0-K0-CS02-TOFF013-CSd02-TOFF013-Kd0-Sd0 (re lem-resp-S1-K1-CS12-TOFF103-CSd12-TOFF103-Kd1-Sd1 ([]ʳ)))))))

i-shift-9 : lo₁ 9 • lo₁ 10 • dKI₁ 9 ≈ dKI₁ 10 • lo₁ 9 • lo₁ 10
i-shift-9 = trans (trans (cong br-l-9 (trans (cong br-l-10 br-k-9) (sym (++≈ (flatB B-l-10) (flat (B-k-9 ∷ [])))))) (sym (++≈ (flatB B-l-9) (flat (B-l-10 ∷ B-k-9 ∷ [])))))
  (trans (transport (rel s₀ ∷ rel s₂ ∷ []) (TF (rel s₂ ∷ rel s₀ ∷ []) (B-l-9 ∷ B-l-10 ∷ B-k-9 ∷ [])) (TF (rel s₂ ∷ rel s₀ ∷ []) (B-k-10 ∷ B-l-9 ∷ B-l-10 ∷ [])) tt tt e)
         (sym (trans (cong br-k-10 (trans (cong br-l-9 br-l-10) (sym (++≈ (flatB B-l-9) (flat (B-l-10 ∷ [])))))) (sym (++≈ (flatB B-k-10) (flat (B-l-9 ∷ B-l-10 ∷ [])))))))
  where
  e : ⟪ flat (TF (rel s₂ ∷ rel s₀ ∷ []) (B-l-9 ∷ B-l-10 ∷ B-k-9 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (rel s₂ ∷ rel s₀ ∷ []) (B-k-10 ∷ B-l-9 ∷ B-l-10 ∷ [])) ⟫ʷ
  e = trans (resp {TF (rel s₂ ∷ rel s₀ ∷ []) (B-l-9 ∷ B-l-10 ∷ B-k-9 ∷ [])} {(HC20-0 ∷ HC20-1 ∷ HC20-2 ∷ [])} (re lem-resp-S0-K0-CS02-TOFF013-CSd02-TOFF013-Kd0-Sd0 (re lem-resp-S1-K1-CS12-TOFF103-CSd12-TOFF103-Kd1-Sd1 (same ([]ʳ)))))
      (trans hcls-20 (sym (resp {TF (rel s₂ ∷ rel s₀ ∷ []) (B-k-10 ∷ B-l-9 ∷ B-l-10 ∷ [])} {(HC20-3 ∷ HC20-4 ∷ HC20-5 ∷ [])} (same (re lem-resp-S0-K0-CS02-TOFF013-CSd02-TOFF013-Kd0-Sd0 (re lem-resp-S1-K1-CS12-TOFF103-CSd12-TOFF103-Kd1-Sd1 ([]ʳ)))))))

i-shift-10 : lo₁ 10 • lo₁ 11 • dKI₁ 10 ≈ dKI₁ 11 • lo₁ 10 • lo₁ 11
i-shift-10 = trans (trans (cong br-l-10 (trans (cong br-l-11 br-k-10) (sym (++≈ (flatB B-l-11) (flat (B-k-10 ∷ [])))))) (sym (++≈ (flatB B-l-10) (flat (B-l-11 ∷ B-k-10 ∷ [])))))
  (trans (transport (rel s₁ ∷ rel s₂ ∷ col w₀ ∷ []) (TF (col w₀ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-l-10 ∷ B-l-11 ∷ B-k-10 ∷ [])) (TF (col w₀ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-k-11 ∷ B-l-10 ∷ B-l-11 ∷ [])) tt tt e)
         (sym (trans (cong br-k-11 (trans (cong br-l-10 br-l-11) (sym (++≈ (flatB B-l-10) (flat (B-l-11 ∷ [])))))) (sym (++≈ (flatB B-k-11) (flat (B-l-10 ∷ B-l-11 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₀ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-l-10 ∷ B-l-11 ∷ B-k-10 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₀ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-k-11 ∷ B-l-10 ∷ B-l-11 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₀ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-l-10 ∷ B-l-11 ∷ B-k-10 ∷ [])} {(HC20-0 ∷ HC20-1 ∷ HC20-2 ∷ [])} (re lem-resp-S0-K0-CS02-TOFF013-CSd02-TOFF013-Kd0-Sd0 (re lem-resp-S1-K1-CS12-TOFF103-CSd12-TOFF103-Kd1-Sd1 (re lem-respell-hyb-CS03-CS03-CK30-CS03-CX31-CS01-CS01-CS01---⟶-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03- ([]ʳ)))))
      (trans hcls-20 (sym (resp {TF (col w₀ ∷ rel s₂ ∷ rel s₁ ∷ []) (B-k-11 ∷ B-l-10 ∷ B-l-11 ∷ [])} {(HC20-3 ∷ HC20-4 ∷ HC20-5 ∷ [])} (same (re lem-resp-S0-K0-CS02-TOFF013-CSd02-TOFF013-Kd0-Sd0 (re lem-resp-S1-K1-CS12-TOFF103-CSd12-TOFF103-Kd1-Sd1 ([]ʳ)))))))

i-shift-11 : lo₁ 11 • lo₁ 12 • dKI₁ 11 ≈ dKI₁ 12 • lo₁ 11 • lo₁ 12
i-shift-11 = trans (trans (cong br-l-11 (trans (cong br-l-12 br-k-11) (sym (++≈ (flatB B-l-12) (flat (B-k-11 ∷ [])))))) (sym (++≈ (flatB B-l-11) (flat (B-l-12 ∷ B-k-11 ∷ [])))))
  (trans (transport (rel s₁ ∷ rel s₀ ∷ col w₀ ∷ col w₁ ∷ []) (TF (col w₁ ∷ col w₀ ∷ rel s₀ ∷ rel s₁ ∷ []) (B-l-11 ∷ B-l-12 ∷ B-k-11 ∷ [])) (TF (col w₁ ∷ col w₀ ∷ rel s₀ ∷ rel s₁ ∷ []) (B-k-12 ∷ B-l-11 ∷ B-l-12 ∷ [])) tt tt e)
         (sym (trans (cong br-k-12 (trans (cong br-l-11 br-l-12) (sym (++≈ (flatB B-l-11) (flat (B-l-12 ∷ [])))))) (sym (++≈ (flatB B-k-12) (flat (B-l-11 ∷ B-l-12 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₁ ∷ col w₀ ∷ rel s₀ ∷ rel s₁ ∷ []) (B-l-11 ∷ B-l-12 ∷ B-k-11 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₁ ∷ col w₀ ∷ rel s₀ ∷ rel s₁ ∷ []) (B-k-12 ∷ B-l-11 ∷ B-l-12 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₁ ∷ col w₀ ∷ rel s₀ ∷ rel s₁ ∷ []) (B-l-11 ∷ B-l-12 ∷ B-k-11 ∷ [])} {(HC20-0 ∷ HC20-1 ∷ HC20-2 ∷ [])} (same (same (re lem-respell-hyb-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02---⟶-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03- ([]ʳ)))))
      (trans hcls-20 (sym (resp {TF (col w₁ ∷ col w₀ ∷ rel s₀ ∷ rel s₁ ∷ []) (B-k-12 ∷ B-l-11 ∷ B-l-12 ∷ [])} {(HC20-3 ∷ HC20-4 ∷ HC20-5 ∷ [])} (re lem-respell-hyb-CS12-CS12-CK21-CS12-CX20-CS01-CS01-CS01---⟶-CS01-CS01-CK01-CS01-CX03-CS13-CS13-CS13- (same (same ([]ʳ)))))))

i-shift-12 : lo₁ 12 • lo₁ 13 • dKI₁ 12 ≈ dKI₁ 13 • lo₁ 12 • lo₁ 13
i-shift-12 = trans (trans (cong br-l-12 (trans (cong br-l-13 br-k-12) (sym (++≈ (flatB B-l-13) (flat (B-k-12 ∷ [])))))) (sym (++≈ (flatB B-l-12) (flat (B-l-13 ∷ B-k-12 ∷ [])))))
  (trans (transport (rel s₂ ∷ col w₃ ∷ []) (TF (col w₃ ∷ rel s₂ ∷ []) (B-l-12 ∷ B-l-13 ∷ B-k-12 ∷ [])) (TF (col w₃ ∷ rel s₂ ∷ []) (B-k-13 ∷ B-l-12 ∷ B-l-13 ∷ [])) tt tt e)
         (sym (trans (cong br-k-13 (trans (cong br-l-12 br-l-13) (sym (++≈ (flatB B-l-12) (flat (B-l-13 ∷ [])))))) (sym (++≈ (flatB B-k-13) (flat (B-l-12 ∷ B-l-13 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₃ ∷ rel s₂ ∷ []) (B-l-12 ∷ B-l-13 ∷ B-k-12 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₃ ∷ rel s₂ ∷ []) (B-k-13 ∷ B-l-12 ∷ B-l-13 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₃ ∷ rel s₂ ∷ []) (B-l-12 ∷ B-l-13 ∷ B-k-12 ∷ [])} {(HC20-0 ∷ HC20-1 ∷ HC20-2 ∷ [])} (re lem-resp-S0-K0-CS02-TOFF013-CSd02-TOFF013-Kd0-Sd0 (re lem-resp-S1-K1-CS12-TOFF103-CSd12-TOFF103-Kd1-Sd1 (same ([]ʳ)))))
      (trans hcls-20 (sym (resp {TF (col w₃ ∷ rel s₂ ∷ []) (B-k-13 ∷ B-l-12 ∷ B-l-13 ∷ [])} {(HC20-3 ∷ HC20-4 ∷ HC20-5 ∷ [])} (same (re lem-resp-S0-K0-CS02-TOFF013-CSd02-TOFF013-Kd0-Sd0 (re lem-resp-S1-K1-CS12-TOFF103-CSd12-TOFF103-Kd1-Sd1 ([]ʳ)))))))

i-shift-13 : lo₁ 13 • lo₁ 14 • dKI₁ 13 ≈ dKI₁ 14 • lo₁ 13 • lo₁ 14
i-shift-13 = trans (trans (cong br-l-13 (trans (cong br-l-14 br-k-13) (sym (++≈ (flatB B-l-14) (flat (B-k-13 ∷ [])))))) (sym (++≈ (flatB B-l-13) (flat (B-l-14 ∷ B-k-13 ∷ [])))))
  (trans (transport (rel s₀ ∷ rel s₂ ∷ col w₀ ∷ col w₃ ∷ []) (TF (col w₃ ∷ col w₀ ∷ rel s₂ ∷ rel s₀ ∷ []) (B-l-13 ∷ B-l-14 ∷ B-k-13 ∷ [])) (TF (col w₃ ∷ col w₀ ∷ rel s₂ ∷ rel s₀ ∷ []) (B-k-14 ∷ B-l-13 ∷ B-l-14 ∷ [])) tt tt e)
         (sym (trans (cong br-k-14 (trans (cong br-l-13 br-l-14) (sym (++≈ (flatB B-l-13) (flat (B-l-14 ∷ [])))))) (sym (++≈ (flatB B-k-14) (flat (B-l-13 ∷ B-l-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₃ ∷ col w₀ ∷ rel s₂ ∷ rel s₀ ∷ []) (B-l-13 ∷ B-l-14 ∷ B-k-13 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₃ ∷ col w₀ ∷ rel s₂ ∷ rel s₀ ∷ []) (B-k-14 ∷ B-l-13 ∷ B-l-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₃ ∷ col w₀ ∷ rel s₂ ∷ rel s₀ ∷ []) (B-l-13 ∷ B-l-14 ∷ B-k-13 ∷ [])} {(HC20-0 ∷ HC20-1 ∷ HC20-2 ∷ [])} (re lem-resp-S0-K0-CS02-TOFF013-CSd02-TOFF013-Kd0-Sd0 (re lem-resp-S1-K1-CS12-TOFF103-CSd12-TOFF103-Kd1-Sd1 (same ([]ʳ)))))
      (trans hcls-20 (sym (resp {TF (col w₃ ∷ col w₀ ∷ rel s₂ ∷ rel s₀ ∷ []) (B-k-14 ∷ B-l-13 ∷ B-l-14 ∷ [])} {(HC20-3 ∷ HC20-4 ∷ HC20-5 ∷ [])} (same (re lem-resp-S0-K0-CS02-TOFF013-CSd02-TOFF013-Kd0-Sd0 (re lem-resp-S1-K1-CS12-TOFF103-CSd12-TOFF103-Kd1-Sd1 ([]ʳ)))))))

i-sc-14 : dPP₁′ 13 • dPP₁′ 13 • dPP₁′ 14 • dKI₁ 14 ≈ dKI₁ 14 • dPP₁′ 13 • dPP₁′ 13 • dPP₁′ 14
i-sc-14 = trans (trans (cong br-p′-13 (trans (cong br-p′-13 (trans (cong br-p′-14 br-k-14) (sym (++≈ (flatB B-p′-14) (flat (B-k-14 ∷ [])))))) (sym (++≈ (flatB B-p′-13) (flat (B-p′-14 ∷ B-k-14 ∷ [])))))) (sym (++≈ (flatB B-p′-13) (flat (B-p′-13 ∷ B-p′-14 ∷ B-k-14 ∷ [])))))
  (trans (transport (col w₀ ∷ col w₁ ∷ col w₂ ∷ []) (TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ []) (B-p′-13 ∷ B-p′-13 ∷ B-p′-14 ∷ B-k-14 ∷ [])) (TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ []) (B-k-14 ∷ B-p′-13 ∷ B-p′-13 ∷ B-p′-14 ∷ [])) tt tt e)
         (sym (trans (cong br-k-14 (trans (cong br-p′-13 (trans (cong br-p′-13 br-p′-14) (sym (++≈ (flatB B-p′-13) (flat (B-p′-14 ∷ [])))))) (sym (++≈ (flatB B-p′-13) (flat (B-p′-13 ∷ B-p′-14 ∷ [])))))) (sym (++≈ (flatB B-k-14) (flat (B-p′-13 ∷ B-p′-13 ∷ B-p′-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ []) (B-p′-13 ∷ B-p′-13 ∷ B-p′-14 ∷ B-k-14 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ []) (B-k-14 ∷ B-p′-13 ∷ B-p′-13 ∷ B-p′-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ []) (B-p′-13 ∷ B-p′-13 ∷ B-p′-14 ∷ B-k-14 ∷ [])} {(HC22-4 ∷ HC22-5 ∷ HC22-6 ∷ HC22-7 ∷ [])} (same (same (same (same ([]ʳ))))))
      (trans (sym hcls-22) (sym (resp {TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ []) (B-k-14 ∷ B-p′-13 ∷ B-p′-13 ∷ B-p′-14 ∷ [])} {(HC22-0 ∷ HC22-1 ∷ HC22-2 ∷ HC22-3 ∷ [])} (same (same (same (same ([]ʳ))))))))

i-cp-14 : dKI₁ 14 • dPP₁ 14 ≈ dPP₁ 14 • hi₁ 14 • dKI₁ 14
i-cp-14 = trans (trans (cong br-k-14 br-p-14) (sym (++≈ (flatB B-k-14) (flat (B-p-14 ∷ [])))))
  (trans (transport (col w₀ ∷ col w₁ ∷ col w₂ ∷ []) (TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ []) (B-k-14 ∷ B-p-14 ∷ [])) (TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ []) (B-p-14 ∷ B-h-14 ∷ B-k-14 ∷ [])) tt tt e)
         (sym (trans (cong br-p-14 (trans (cong br-h-14 br-k-14) (sym (++≈ (flatB B-h-14) (flat (B-k-14 ∷ [])))))) (sym (++≈ (flatB B-p-14) (flat (B-h-14 ∷ B-k-14 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ []) (B-k-14 ∷ B-p-14 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ []) (B-p-14 ∷ B-h-14 ∷ B-k-14 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ []) (B-k-14 ∷ B-p-14 ∷ [])} {(HC23-0 ∷ HC23-1 ∷ [])} (same (same ([]ʳ))))
      (trans hcls-23 (sym (resp {TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ []) (B-p-14 ∷ B-h-14 ∷ B-k-14 ∷ [])} {(HC23-2 ∷ HC23-3 ∷ HC23-4 ∷ [])} (same (same (same ([]ʳ)))))))

i-c3-14 : dKI₁ 14 • dKI₁ 14 • dKI₁ 14 ≈ ε
i-c3-14 = trans (trans (cong br-k-14 (trans (cong br-k-14 br-k-14) (sym (++≈ (flatB B-k-14) (flat (B-k-14 ∷ [])))))) (sym (++≈ (flatB B-k-14) (flat (B-k-14 ∷ B-k-14 ∷ [])))))
  (trans (transport (col w₀ ∷ col w₁ ∷ col w₂ ∷ []) (TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ []) (B-k-14 ∷ B-k-14 ∷ B-k-14 ∷ [])) (TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ []) []) tt tt e)
         (sym refl))
  where
  e : ⟪ flat (TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ []) (B-k-14 ∷ B-k-14 ∷ B-k-14 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ []) []) ⟫ʷ
  e = trans (resp {TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ []) (B-k-14 ∷ B-k-14 ∷ B-k-14 ∷ [])} {(HC24-0 ∷ HC24-1 ∷ HC24-2 ∷ [])} (same (same (same ([]ʳ)))))
      (trans hcls-24 (sym (resp {TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ []) []} {[]} ([]ʳ))))

i-sq-14 : dKI₁ 14 • dPP₁′ 13 • dKI₁ 14 • dPP₁′ 13 • dPP₁′ 13 • dPP₁′ 13 • dPP₁′ 14 ≈ ε
i-sq-14 = trans (trans (cong br-k-14 (trans (cong br-p′-13 (trans (cong br-k-14 (trans (cong br-p′-13 (trans (cong br-p′-13 (trans (cong br-p′-13 br-p′-14) (sym (++≈ (flatB B-p′-13) (flat (B-p′-14 ∷ [])))))) (sym (++≈ (flatB B-p′-13) (flat (B-p′-13 ∷ B-p′-14 ∷ [])))))) (sym (++≈ (flatB B-p′-13) (flat (B-p′-13 ∷ B-p′-13 ∷ B-p′-14 ∷ [])))))) (sym (++≈ (flatB B-k-14) (flat (B-p′-13 ∷ B-p′-13 ∷ B-p′-13 ∷ B-p′-14 ∷ [])))))) (sym (++≈ (flatB B-p′-13) (flat (B-k-14 ∷ B-p′-13 ∷ B-p′-13 ∷ B-p′-13 ∷ B-p′-14 ∷ [])))))) (sym (++≈ (flatB B-k-14) (flat (B-p′-13 ∷ B-k-14 ∷ B-p′-13 ∷ B-p′-13 ∷ B-p′-13 ∷ B-p′-14 ∷ [])))))
  (trans (transport (col w₀ ∷ col w₁ ∷ col w₂ ∷ []) (TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ []) (B-k-14 ∷ B-p′-13 ∷ B-k-14 ∷ B-p′-13 ∷ B-p′-13 ∷ B-p′-13 ∷ B-p′-14 ∷ [])) (TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ []) []) tt tt e)
         (sym refl))
  where
  e : ⟪ flat (TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ []) (B-k-14 ∷ B-p′-13 ∷ B-k-14 ∷ B-p′-13 ∷ B-p′-13 ∷ B-p′-13 ∷ B-p′-14 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ []) []) ⟫ʷ
  e = trans (resp {TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ []) (B-k-14 ∷ B-p′-13 ∷ B-k-14 ∷ B-p′-13 ∷ B-p′-13 ∷ B-p′-13 ∷ B-p′-14 ∷ [])} {(HC25-0 ∷ HC25-1 ∷ HC25-2 ∷ HC25-3 ∷ HC25-4 ∷ HC25-5 ∷ HC25-6 ∷ [])} (same (same (same (same (same (same (same ([]ʳ)))))))))
      (trans hcls-25 (sym (resp {TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ []) []} {[]} ([]ʳ))))

i-yb-14 : dKI₁ 12 • dPP₁′ 11 • dKI₁ 14 • dPP₁′ 11 • dPP₁′ 12 • dPP₁′ 13 • hi₁ 12 • dKI₁ 13 • lo₁ 12 • dPP₁′ 11 • hi₁ 13 • dKI₁ 14 • lo₁ 13 • dPP₁′ 11 • dPP₁′ 12 ≈ hi₁ 12 • dKI₁ 13 • lo₁ 12 • dPP₁′ 11 • hi₁ 13 • dKI₁ 14 • lo₁ 13 • dPP₁′ 11 • dPP₁′ 12 • dKI₁ 12 • dPP₁′ 11 • dKI₁ 14 • dPP₁′ 11 • dPP₁′ 12 • dPP₁′ 13
i-yb-14 = trans (trans (cong br-k-12 (trans (cong br-p′-11 (trans (cong br-k-14 (trans (cong br-p′-11 (trans (cong br-p′-12 (trans (cong br-p′-13 (trans (cong br-h-12 (trans (cong br-k-13 (trans (cong br-l-12 (trans (cong br-p′-11 (trans (cong br-h-13 (trans (cong br-k-14 (trans (cong br-l-13 (trans (cong br-p′-11 br-p′-12) (sym (++≈ (flatB B-p′-11) (flat (B-p′-12 ∷ [])))))) (sym (++≈ (flatB B-l-13) (flat (B-p′-11 ∷ B-p′-12 ∷ [])))))) (sym (++≈ (flatB B-k-14) (flat (B-l-13 ∷ B-p′-11 ∷ B-p′-12 ∷ [])))))) (sym (++≈ (flatB B-h-13) (flat (B-k-14 ∷ B-l-13 ∷ B-p′-11 ∷ B-p′-12 ∷ [])))))) (sym (++≈ (flatB B-p′-11) (flat (B-h-13 ∷ B-k-14 ∷ B-l-13 ∷ B-p′-11 ∷ B-p′-12 ∷ [])))))) (sym (++≈ (flatB B-l-12) (flat (B-p′-11 ∷ B-h-13 ∷ B-k-14 ∷ B-l-13 ∷ B-p′-11 ∷ B-p′-12 ∷ [])))))) (sym (++≈ (flatB B-k-13) (flat (B-l-12 ∷ B-p′-11 ∷ B-h-13 ∷ B-k-14 ∷ B-l-13 ∷ B-p′-11 ∷ B-p′-12 ∷ [])))))) (sym (++≈ (flatB B-h-12) (flat (B-k-13 ∷ B-l-12 ∷ B-p′-11 ∷ B-h-13 ∷ B-k-14 ∷ B-l-13 ∷ B-p′-11 ∷ B-p′-12 ∷ [])))))) (sym (++≈ (flatB B-p′-13) (flat (B-h-12 ∷ B-k-13 ∷ B-l-12 ∷ B-p′-11 ∷ B-h-13 ∷ B-k-14 ∷ B-l-13 ∷ B-p′-11 ∷ B-p′-12 ∷ [])))))) (sym (++≈ (flatB B-p′-12) (flat (B-p′-13 ∷ B-h-12 ∷ B-k-13 ∷ B-l-12 ∷ B-p′-11 ∷ B-h-13 ∷ B-k-14 ∷ B-l-13 ∷ B-p′-11 ∷ B-p′-12 ∷ [])))))) (sym (++≈ (flatB B-p′-11) (flat (B-p′-12 ∷ B-p′-13 ∷ B-h-12 ∷ B-k-13 ∷ B-l-12 ∷ B-p′-11 ∷ B-h-13 ∷ B-k-14 ∷ B-l-13 ∷ B-p′-11 ∷ B-p′-12 ∷ [])))))) (sym (++≈ (flatB B-k-14) (flat (B-p′-11 ∷ B-p′-12 ∷ B-p′-13 ∷ B-h-12 ∷ B-k-13 ∷ B-l-12 ∷ B-p′-11 ∷ B-h-13 ∷ B-k-14 ∷ B-l-13 ∷ B-p′-11 ∷ B-p′-12 ∷ [])))))) (sym (++≈ (flatB B-p′-11) (flat (B-k-14 ∷ B-p′-11 ∷ B-p′-12 ∷ B-p′-13 ∷ B-h-12 ∷ B-k-13 ∷ B-l-12 ∷ B-p′-11 ∷ B-h-13 ∷ B-k-14 ∷ B-l-13 ∷ B-p′-11 ∷ B-p′-12 ∷ [])))))) (sym (++≈ (flatB B-k-12) (flat (B-p′-11 ∷ B-k-14 ∷ B-p′-11 ∷ B-p′-12 ∷ B-p′-13 ∷ B-h-12 ∷ B-k-13 ∷ B-l-12 ∷ B-p′-11 ∷ B-h-13 ∷ B-k-14 ∷ B-l-13 ∷ B-p′-11 ∷ B-p′-12 ∷ [])))))
  (trans (transport (col w₀ ∷ col w₁ ∷ col w₂ ∷ []) (TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ []) (B-k-12 ∷ B-p′-11 ∷ B-k-14 ∷ B-p′-11 ∷ B-p′-12 ∷ B-p′-13 ∷ B-h-12 ∷ B-k-13 ∷ B-l-12 ∷ B-p′-11 ∷ B-h-13 ∷ B-k-14 ∷ B-l-13 ∷ B-p′-11 ∷ B-p′-12 ∷ [])) (TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ []) (B-h-12 ∷ B-k-13 ∷ B-l-12 ∷ B-p′-11 ∷ B-h-13 ∷ B-k-14 ∷ B-l-13 ∷ B-p′-11 ∷ B-p′-12 ∷ B-k-12 ∷ B-p′-11 ∷ B-k-14 ∷ B-p′-11 ∷ B-p′-12 ∷ B-p′-13 ∷ [])) tt tt e)
         (sym (trans (cong br-h-12 (trans (cong br-k-13 (trans (cong br-l-12 (trans (cong br-p′-11 (trans (cong br-h-13 (trans (cong br-k-14 (trans (cong br-l-13 (trans (cong br-p′-11 (trans (cong br-p′-12 (trans (cong br-k-12 (trans (cong br-p′-11 (trans (cong br-k-14 (trans (cong br-p′-11 (trans (cong br-p′-12 br-p′-13) (sym (++≈ (flatB B-p′-12) (flat (B-p′-13 ∷ [])))))) (sym (++≈ (flatB B-p′-11) (flat (B-p′-12 ∷ B-p′-13 ∷ [])))))) (sym (++≈ (flatB B-k-14) (flat (B-p′-11 ∷ B-p′-12 ∷ B-p′-13 ∷ [])))))) (sym (++≈ (flatB B-p′-11) (flat (B-k-14 ∷ B-p′-11 ∷ B-p′-12 ∷ B-p′-13 ∷ [])))))) (sym (++≈ (flatB B-k-12) (flat (B-p′-11 ∷ B-k-14 ∷ B-p′-11 ∷ B-p′-12 ∷ B-p′-13 ∷ [])))))) (sym (++≈ (flatB B-p′-12) (flat (B-k-12 ∷ B-p′-11 ∷ B-k-14 ∷ B-p′-11 ∷ B-p′-12 ∷ B-p′-13 ∷ [])))))) (sym (++≈ (flatB B-p′-11) (flat (B-p′-12 ∷ B-k-12 ∷ B-p′-11 ∷ B-k-14 ∷ B-p′-11 ∷ B-p′-12 ∷ B-p′-13 ∷ [])))))) (sym (++≈ (flatB B-l-13) (flat (B-p′-11 ∷ B-p′-12 ∷ B-k-12 ∷ B-p′-11 ∷ B-k-14 ∷ B-p′-11 ∷ B-p′-12 ∷ B-p′-13 ∷ [])))))) (sym (++≈ (flatB B-k-14) (flat (B-l-13 ∷ B-p′-11 ∷ B-p′-12 ∷ B-k-12 ∷ B-p′-11 ∷ B-k-14 ∷ B-p′-11 ∷ B-p′-12 ∷ B-p′-13 ∷ [])))))) (sym (++≈ (flatB B-h-13) (flat (B-k-14 ∷ B-l-13 ∷ B-p′-11 ∷ B-p′-12 ∷ B-k-12 ∷ B-p′-11 ∷ B-k-14 ∷ B-p′-11 ∷ B-p′-12 ∷ B-p′-13 ∷ [])))))) (sym (++≈ (flatB B-p′-11) (flat (B-h-13 ∷ B-k-14 ∷ B-l-13 ∷ B-p′-11 ∷ B-p′-12 ∷ B-k-12 ∷ B-p′-11 ∷ B-k-14 ∷ B-p′-11 ∷ B-p′-12 ∷ B-p′-13 ∷ [])))))) (sym (++≈ (flatB B-l-12) (flat (B-p′-11 ∷ B-h-13 ∷ B-k-14 ∷ B-l-13 ∷ B-p′-11 ∷ B-p′-12 ∷ B-k-12 ∷ B-p′-11 ∷ B-k-14 ∷ B-p′-11 ∷ B-p′-12 ∷ B-p′-13 ∷ [])))))) (sym (++≈ (flatB B-k-13) (flat (B-l-12 ∷ B-p′-11 ∷ B-h-13 ∷ B-k-14 ∷ B-l-13 ∷ B-p′-11 ∷ B-p′-12 ∷ B-k-12 ∷ B-p′-11 ∷ B-k-14 ∷ B-p′-11 ∷ B-p′-12 ∷ B-p′-13 ∷ [])))))) (sym (++≈ (flatB B-h-12) (flat (B-k-13 ∷ B-l-12 ∷ B-p′-11 ∷ B-h-13 ∷ B-k-14 ∷ B-l-13 ∷ B-p′-11 ∷ B-p′-12 ∷ B-k-12 ∷ B-p′-11 ∷ B-k-14 ∷ B-p′-11 ∷ B-p′-12 ∷ B-p′-13 ∷ [])))))))
  where
  e : ⟪ flat (TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ []) (B-k-12 ∷ B-p′-11 ∷ B-k-14 ∷ B-p′-11 ∷ B-p′-12 ∷ B-p′-13 ∷ B-h-12 ∷ B-k-13 ∷ B-l-12 ∷ B-p′-11 ∷ B-h-13 ∷ B-k-14 ∷ B-l-13 ∷ B-p′-11 ∷ B-p′-12 ∷ [])) ⟫ʷ ≈ ⟪ flat (TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ []) (B-h-12 ∷ B-k-13 ∷ B-l-12 ∷ B-p′-11 ∷ B-h-13 ∷ B-k-14 ∷ B-l-13 ∷ B-p′-11 ∷ B-p′-12 ∷ B-k-12 ∷ B-p′-11 ∷ B-k-14 ∷ B-p′-11 ∷ B-p′-12 ∷ B-p′-13 ∷ [])) ⟫ʷ
  e = trans (resp {TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ []) (B-k-12 ∷ B-p′-11 ∷ B-k-14 ∷ B-p′-11 ∷ B-p′-12 ∷ B-p′-13 ∷ B-h-12 ∷ B-k-13 ∷ B-l-12 ∷ B-p′-11 ∷ B-h-13 ∷ B-k-14 ∷ B-l-13 ∷ B-p′-11 ∷ B-p′-12 ∷ [])} {(HC26-0 ∷ HC26-1 ∷ HC26-2 ∷ HC26-3 ∷ HC26-4 ∷ HC26-5 ∷ HC26-6 ∷ HC26-7 ∷ HC26-8 ∷ HC26-9 ∷ HC26-10 ∷ HC26-11 ∷ HC26-12 ∷ HC26-13 ∷ HC26-14 ∷ [])} (same (same (same (same (same (same (same (same (same (same (same (same (same (same (same ([]ʳ)))))))))))))))))
      (trans hcls-26 (sym (resp {TF (col w₂ ∷ col w₁ ∷ col w₀ ∷ []) (B-h-12 ∷ B-k-13 ∷ B-l-12 ∷ B-p′-11 ∷ B-h-13 ∷ B-k-14 ∷ B-l-13 ∷ B-p′-11 ∷ B-p′-12 ∷ B-k-12 ∷ B-p′-11 ∷ B-k-14 ∷ B-p′-11 ∷ B-p′-12 ∷ B-p′-13 ∷ [])} {(HC26-15 ∷ HC26-16 ∷ HC26-17 ∷ HC26-18 ∷ HC26-19 ∷ HC26-20 ∷ HC26-21 ∷ HC26-22 ∷ HC26-23 ∷ HC26-24 ∷ HC26-25 ∷ HC26-26 ∷ HC26-27 ∷ HC26-28 ∷ HC26-29 ∷ [])} (same (same (same (same (same (same (same (same (same (same (same (same (same (same (same ([]ʳ)))))))))))))))))))

d-far-p : ∀ j → suc (suc j) ≤ 14 → dKI₁ 14 • dPP₁ j ≈ dPP₁ j • dKI₁ 14
d-far-p 0 _ = i-far-p-0
d-far-p 1 _ = i-far-p-1
d-far-p 2 _ = i-far-p-2
d-far-p 3 _ = i-far-p-3
d-far-p 4 _ = i-far-p-4
d-far-p 5 _ = i-far-p-5
d-far-p 6 _ = i-far-p-6
d-far-p 7 _ = i-far-p-7
d-far-p 8 _ = i-far-p-8
d-far-p 9 _ = i-far-p-9
d-far-p 10 _ = i-far-p-10
d-far-p 11 _ = i-far-p-11
d-far-p 12 _ = i-far-p-12
d-far-p (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc k))))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ()))))))))))))))

d-far-l : ∀ j → suc (suc j) ≤ 14 → dKI₁ 14 • lo₁ j ≈ lo₁ j • dKI₁ 14
d-far-l 0 _ = i-far-l-0
d-far-l 1 _ = i-far-l-1
d-far-l 2 _ = i-far-l-2
d-far-l 3 _ = i-far-l-3
d-far-l 4 _ = i-far-l-4
d-far-l 5 _ = i-far-l-5
d-far-l 6 _ = i-far-l-6
d-far-l 7 _ = i-far-l-7
d-far-l 8 _ = i-far-l-8
d-far-l 9 _ = i-far-l-9
d-far-l 10 _ = i-far-l-10
d-far-l 11 _ = i-far-l-11
d-far-l 12 _ = i-far-l-12
d-far-l (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc k))))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ()))))))))))))))

d-far-k : ∀ j → suc (suc j) ≤ 14 → dKI₁ 14 • dKI₁ j ≈ dKI₁ j • dKI₁ 14
d-far-k 0 _ = i-far-k-0
d-far-k 1 _ = i-far-k-1
d-far-k 2 _ = i-far-k-2
d-far-k 3 _ = i-far-k-3
d-far-k 4 _ = i-far-k-4
d-far-k 5 _ = i-far-k-5
d-far-k 6 _ = i-far-k-6
d-far-k 7 _ = i-far-k-7
d-far-k 8 _ = i-far-k-8
d-far-k 9 _ = i-far-k-9
d-far-k 10 _ = i-far-k-10
d-far-k 11 _ = i-far-k-11
d-far-k 12 _ = i-far-k-12
d-far-k (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc k))))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ()))))))))))))))

d-shift : ∀ j → suc (suc j) < 16 → (lo₁ j • lo₁ (suc j)) • dKI₁ j ≈ dKI₁ (suc j) • (lo₁ j • lo₁ (suc j))
d-shift 0 _ = trans assoc i-shift-0
d-shift 1 _ = trans assoc i-shift-1
d-shift 2 _ = trans assoc i-shift-2
d-shift 3 _ = trans assoc i-shift-3
d-shift 4 _ = trans assoc i-shift-4
d-shift 5 _ = trans assoc i-shift-5
d-shift 6 _ = trans assoc i-shift-6
d-shift 7 _ = trans assoc i-shift-7
d-shift 8 _ = trans assoc i-shift-8
d-shift 9 _ = trans assoc i-shift-9
d-shift 10 _ = trans assoc i-shift-10
d-shift 11 _ = trans assoc i-shift-11
d-shift 12 _ = trans assoc i-shift-12
d-shift 13 _ = trans assoc i-shift-13
d-shift (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc k)))))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ()))))))))))))))))

d-sc : (dPP₁′ 13 • dPP₁′ 13 • dPP₁′ 14) • dKI₁ 14 ≈ dKI₁ 14 • (dPP₁′ 13 • dPP₁′ 13 • dPP₁′ 14)
d-sc = trans (trans assoc (back (dPP₁′ 13) assoc)) i-sc-14
