------------------------------------------------------------------------
-- Presentations of groups
--
-- Expanding HH into two H gates preserves ordinary physical matrices.
-- The dyadic scalar inclusion is injective, so this also reflects
-- physical circuit equality at every width, including width zero.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.GeneralN.HadamardEmbedding where

open import Data.Nat.Base using (ℕ ; zero ; suc ; _*_) renaming (_^_ to _^ℕ_)
import Data.Nat.Properties as NP
open import Relation.Binary.PropositionalEquality
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Quantum.Synthesis.Matrix using (Matrix ; _·*·_)
import Examples.Groups.CCX+HH.Syntactics as HH
import Examples.Groups.CCX+HH.Semantics as Q
import Examples.Groups.CCX+HH.StructuralEncoding as DE
import Examples.Groups.CCX+H.Syntactics as H
import Examples.Groups.CCX+H.GeneralN.Semantics as S
import Examples.Groups.CCX+H.GeneralN.PhysicalSemantics as P
open import Examples.Groups.CCX+H.GeneralN.HadamardEmbedding public using (e ; embed)
import Examples.Groups.CCX+H.GeneralN.HadamardEmbedding as E
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as U
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as M
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Ring as R
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (D ; RingD ; AdjointD)

embed-shift : ∀ {n} (w : HH.Circuit n) → embed (w HH.↑) ≡ embed w H.↑
embed-shift [ g ]ʷ = refl
embed-shift ε = refl
embed-shift (u • v) = cong₂ _•_ (embed-shift u) (embed-shift v)

private
  cast-cancel : ∀ {j k} (p : j ≡ k) (A : Matrix j j D) →
    P.cast-matrix (sym p) (P.cast-matrix p A) ≡ A
  cast-cancel refl A = refl

  lift-cast : ∀ {N} k (p : N ≡ k * 2) (w : Word (U.Gen N)) →
    M.Dim.⟦_⟧ᴸ k (S.cast-word p T.⌊ w ⌋ʷ) ≡ P.cast-matrix p M.⟦ w ⟧ᵐ
  lift-cast k refl w = M.actMᴸʷ-⌊⌋ k w M.𝕀

  empty-correct : ∀ (w : HH.Circuit 0) → P.interpret (embed w) ≡ M.mapM (Q.interpret w)
  empty-correct [ HH.gate₀ () ]ʷ
  empty-correct ε = sym M.mapM-𝕀
  empty-correct (u • v) = trans (cong₂ _·*·_ (empty-correct u) (empty-correct v))
    (sym (M.mapM-·*· (Q.interpret u) (Q.interpret v)))

  positive : ∀ n (w : HH.Circuit (suc n)) → P.interpret (embed w) ≡ M.mapM (Q.interpret w)
  positive n w = trans (sym (P.At.correct n (embed w)))
    (trans (cong (P.cast-matrix (sym dimension)) (E.At.encoding-correct n w))
      (trans (cong (P.cast-matrix (sym dimension)) (lift-cast k dimension (DE.encode w)))
        (trans (cast-cancel dimension M.⟦ DE.encode w ⟧ᵐ)
          (trans (M.Tr.⟦⟧-map (DE.encode w)) (cong M.mapM (Q.encoding-correct w))))))
    where
    k = 2 ^ℕ n
    dimension : 2 ^ℕ suc n ≡ k * 2
    dimension = NP.*-comm 2 k

physical-correct : ∀ {n} (w : HH.Circuit n) → P.interpret (embed w) ≡ M.mapM (Q.interpret w)
physical-correct {zero} = empty-correct
physical-correct {suc n} = positive n

preserve : ∀ {n} {u v : HH.Circuit n} → Q.interpret u ≡ Q.interpret v →
  P.interpret (embed u) ≡ P.interpret (embed v)
preserve {u = u} {v} eq = trans (physical-correct u)
  (trans (cong M.mapM eq) (sym (physical-correct v)))

reflect : ∀ {n} {u v : HH.Circuit n} → P.interpret (embed u) ≡ P.interpret (embed v) →
  Q.interpret u ≡ Q.interpret v
reflect {u = u} {v} eq = M.Tr.mapM-injective R.e-injective
  (trans (sym (physical-correct u)) (trans eq (physical-correct v)))
