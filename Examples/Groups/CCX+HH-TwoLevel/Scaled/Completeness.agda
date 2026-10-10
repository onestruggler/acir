------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness for ℱₙ, n = 2(k + 1) (Theorem 5.7).
--
-- Write the two words as G (I⊗H)^ℓ and G′ (I⊗H)^ℓ′ (Corollary 5.6).
-- If ℓ = ℓ′, G and G′ have the same matrix in ℤ[1/√2], hence in
-- ℤ[1/2] (the embedding is injective), and G ≈ G′ by Theorem 4.10.
-- Otherwise I ⊗ H would have the matrix of a word over 𝒢ₙ, whose
-- entries have no √2 part, but its entry (0, 0) is 1/√2.  (The paper
-- compares least denominator exponents instead.)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; suc)

module Examples.Groups.CCX+HH-TwoLevel.Scaled.Completeness (k : ℕ) where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Product.Base using (_,_)
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_)

open import Quantum.Synthesis.Matrix using (Matrix ; _·*·_)

open import Word.Base
import Presentation.Base as PB
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics using (Gen)
open import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics
open import Examples.Groups.CCX+HH-TwoLevel.Scaled.Normal k using (n ; HH ; Hᵇ ; nf ; NF)
import Examples.Groups.CCX+HH-TwoLevel.Ring as R1
import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring as R2
open import Examples.Groups.CCX+HH-TwoLevel.Scaled.Ring using (D ; e ; √2-part ; √2-part-e ; e-injective ; √½)
open import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics
import Examples.Groups.CCX+HH-TwoLevel.Semantics as S1
import Examples.Groups.CCX+HH-TwoLevel.MainLemma as ML
import Examples.Groups.CCX+HH-TwoLevel.Derived as Der

open Dim (suc k)

private
  module P = PB (_===ᴸ_ {n})

  sem : ∀ {w v} → w P.≈ v → ⟦ w ⟧ᴸ ≡ ⟦ v ⟧ᴸ
  sem = soundness (suc k)

  HbHb : ∀ ℓ → Hᵇ ℓ • Hᵇ ℓ P.≈ ε
  HbHb true = HH
  HbHb false = P.left-unit

  -- From w ≈ G (I⊗H)^ℓ to G ≈ w (I⊗H)^ℓ.
  back : ∀ {w G} ℓ → w P.≈ ⌊ G ⌋ʷ • Hᵇ ℓ → ⌊ G ⌋ʷ P.≈ w • Hᵇ ℓ
  back ℓ h = P.sym (P.trans (P.cong h P.refl) (P.trans P.assoc (P.trans (P.cong P.refl (HbHb ℓ)) P.right-unit)))

  same : ∀ {u v G G′} ℓ → u P.≈ ⌊ G ⌋ʷ • Hᵇ ℓ → v P.≈ ⌊ G′ ⌋ʷ • Hᵇ ℓ → ⟦ u ⟧ᴸ ≡ ⟦ v ⟧ᴸ → u P.≈ v
  same {u} {v} {G} {G′} ℓ eu ev eq = P.trans eu (P.trans (P.cong (⌊⌋-cong (ML.completeness G≡)) P.refl) (P.sym ev))
    where
    m≡ : ⟦ ⌊ G ⌋ʷ ⟧ᴸ ≡ ⟦ ⌊ G′ ⌋ʷ ⟧ᴸ
    m≡ = ≡.trans (sem (back ℓ eu)) (≡.trans (⟦•⟧ᴸ u (Hᵇ ℓ))
           (≡.trans (≡.cong (_·*· ⟦ Hᵇ ℓ ⟧ᴸ) eq) (≡.trans (≡.sym (⟦•⟧ᴸ v (Hᵇ ℓ))) (≡.sym (sem (back ℓ ev))))))
    G≡ : S1.⟦ G ⟧ᵐ ≡ S1.⟦ G′ ⟧ᵐ
    G≡ = Tr.mapM-injective e-injective (≡.trans (≡.sym (⟦⌊⌋⟧ (suc k) G)) (≡.trans m≡ (⟦⌊⌋⟧ (suc k) G′)))

  -- The entry (0, 0) of I ⊗ H has a √2 part.
  opaque
    unfolding R2._+ᴰ_ R2._*ᴰ_

    √2-part-H : √2-part (ent ⟦ H ⟧ᴸ zero zero) ≡ R1.½ᴰ
    √2-part-H = ≡.cong √2-part (≡.trans (≡.cong (λ M → ent M zero zero) (⟦g⟧ᴸ≡ IH)) (ent-mk (coefIH (suc k)) zero zero))

  ½≢0 : R1.½ᴰ ≡ R1.0ᴰ → ⊥
  ½≢0 ()

  -- I ⊗ H is not the matrix of a word over 𝒢ₙ.
  apart : ∀ {G G′ : Word (Gen n)} → ⟦ ⌊ G ⌋ʷ ⟧ᴸ ≡ ⟦ ⌊ G′ ⌋ʷ • H ⟧ᴸ → ⊥
  apart {G} {G′} eq = ½≢0 (≡.trans (≡.sym √2-part-H) (≡.trans (≡.cong (λ M → √2-part (ent M zero zero)) Hm)
                                                       (≡.cong √2-part (ent-mapM S1.⟦ G′ Der.⁻¹ • G ⟧ᵐ zero zero))))
    where
    G′⁻ = G′ Der.⁻¹
    Hm : ⟦ H ⟧ᴸ ≡ mapM S1.⟦ G′⁻ • G ⟧ᵐ
    Hm = ≡.trans (sem {H} {⌊ G′⁻ ⌋ʷ • (⌊ G′ ⌋ʷ • H)} (P.sym (P.trans (P.sym P.assoc) (P.trans (P.cong (⌊⌋-cong (Der.inverseˡ {g = G′})) P.refl) P.left-unit))))
           (≡.trans (⟦•⟧ᴸ ⌊ G′⁻ ⌋ʷ (⌊ G′ ⌋ʷ • H))
             (≡.trans (≡.cong (⟦ ⌊ G′⁻ ⌋ʷ ⟧ᴸ ·*·_) (≡.sym eq))
               (≡.trans (≡.sym (⟦•⟧ᴸ ⌊ G′⁻ ⌋ʷ ⌊ G ⌋ʷ)) (⟦⌊⌋⟧ (suc k) (G′⁻ • G)))))

------------------------------------------------------------------------
-- Theorem 5.7

completeness : ∀ {u v : Word (Genᴸ n)} → ⟦ u ⟧ᴸ ≡ ⟦ v ⟧ᴸ → u P.≈ v
completeness {u} {v} eq = by (nf u) (nf v)
  where
  by : NF u → NF v → u P.≈ v
  by (G , true , eu) (G′ , true , ev) = same true eu ev eq
  by (G , false , eu) (G′ , false , ev) = same false eu ev eq
  by (G , false , eu) (G′ , true , ev) =
    ⊥-elim (apart {G} {G′} (≡.trans (≡.sym (sem (P.trans eu P.right-unit))) (≡.trans eq (sem ev))))
  by (G , true , eu) (G′ , false , ev) =
    ⊥-elim (apart {G′} {G} (≡.trans (≡.sym (sem (P.trans ev P.right-unit))) (≡.trans (≡.sym eq) (sem eu))))
