------------------------------------------------------------------------
-- Presentations of groups
--
-- The semantics of ℱ₂ₖ in ℤ[1/√2] (Scaled.Action at 𝔻[√2], h = 1/2,
-- s = 1/√2), and soundness (Theorem 5.4).
--
-- A word over 𝒢₂ₖ has as matrix the image of its matrix in Oₙ(ℤ[1/2])
-- (⟦⌊⌋⟧, by Scaled.Transfer), so Table 1 holds by the soundness of
-- Oₙ(ℤ[1/2]); Table 2 holds by Scaled.Table2.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics where

open import Data.Fin.Base using (Fin ; zero ; suc ; toℕ ; _<_)
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
open import Relation.Binary.PropositionalEquality

open import Quantum.Synthesis.Matrix using (Matrix ; _·*·_)

open import Word.Base
import Presentation.Base as PB
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics using (Gen ; M-gen ; X-gen ; K-gen)
open import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics
import Examples.Groups.CCX+HH-TwoLevel.Ring as R1
import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring as R2
open import Examples.Groups.CCX+HH-TwoLevel.Scaled.Ring
import Examples.Groups.CCX+HH-TwoLevel.Semantics as S1
import Examples.Groups.CCX+HH-TwoLevel.Soundness as Sound1
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Action as SA
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Table2 as T2
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Transfer as TR

-- The action at 𝔻[√2].
open SA {D} ⦃ R2.RingD ⦄ ⦃ R2.AdjointD ⦄ isCommutativeRing-D adj-D ½ ½-self ½-quarter √½ √½-self √½-sq √½-half public
open T2 {D} ⦃ R2.RingD ⦄ ⦃ R2.AdjointD ⦄ isCommutativeRing-D adj-D ½ ½-self ½-quarter √½ √½-self √½-sq √½-half
  using (r7a-act ; r7b-act ; r7c-act ; r7d₀-act ; r7d₁-act)

-- From 𝔻 to 𝔻[√2].
module Tr = TR {R1.D} {D} ⦃ R1.RingD ⦄ ⦃ R1.AdjointD ⦄ ⦃ R2.RingD ⦄ ⦃ R2.AdjointD ⦄
              R1.isCommutativeRing-D R1.adj-D R1.½ᴰ isCommutativeRing-D adj-D ½
              e e-+ e-* e-neg e-0 e-1 refl e-adj

open Tr public using (mapM ; mapM-·*· ; mapM-adjoint ; mapM-𝕀 ; ent-mapM)

------------------------------------------------------------------------
-- Words over 𝒢₂ₖ

module _ (k : ℕ) where

  open Dim k

  private
    n = k ℕ.* 2

  actMᴸʷ-⌊⌋ : ∀ {m} (w : Word (Gen n)) (M : Matrix n m D) → actMᴸʷ ⌊ w ⌋ʷ M ≡ actMʷ w M
  actMᴸʷ-⌊⌋ [ g ]ʷ M = refl
  actMᴸʷ-⌊⌋ ε M = refl
  actMᴸʷ-⌊⌋ (u • w) M = trans (cong (actMᴸʷ ⌊ u ⌋ʷ) (actMᴸʷ-⌊⌋ w M)) (actMᴸʷ-⌊⌋ u (actMʷ w M))

  -- The matrix of a word over 𝒢₂ₖ is that of Oₙ(ℤ[1/2]), embedded.
  ⟦⌊⌋⟧ : (w : Word (Gen n)) → ⟦ ⌊ w ⌋ʷ ⟧ᴸ ≡ mapM S1.⟦ w ⟧ᵐ
  ⟦⌊⌋⟧ w = trans (actMᴸʷ-⌊⌋ w 𝕀) (Tr.⟦⟧-map w)

  ----------------------------------------------------------------------
  -- Soundness (Theorem 5.4)

  private
    -- Table 2 on its first blocks, at the indices the relation names.
    r7b-at : ∀ {a b c d : Fin n} .(p : a < b) .(q : b < c) .(r : c < d) →
             toℕ a ≡ 0 → toℕ b ≡ 1 → toℕ c ≡ 2 → toℕ d ≡ 3 → ∀ u →
             actIH k (actV (K-gen a b c d p q r) (actIH k u)) ≡ actV (K-gen a b c d p q r) u
    r7b-at = go k
      where
      go : ∀ k {a b c d : Fin (k ℕ.* 2)} .(p : a < b) .(q : b < c) .(r : c < d) →
           toℕ a ≡ 0 → toℕ b ≡ 1 → toℕ c ≡ 2 → toℕ d ≡ 3 → ∀ u →
           actIH k (actV (K-gen a b c d p q r) (actIH k u)) ≡ actV (K-gen a b c d p q r) u
      go (suc (suc k)) {zero} {suc zero} {suc (suc zero)} {suc (suc (suc zero))} p q r refl refl refl refl u = r7b-act k u
      go zero {()}
      go (suc zero) {_} {_} {suc (suc ())}
      go (suc (suc k)) {suc _} p q r () tb tc td u
      go (suc (suc k)) {zero} {zero} p q r ta () tc td u
      go (suc (suc k)) {zero} {suc (suc _)} p q r ta () tc td u
      go (suc (suc k)) {zero} {suc zero} {zero} p q r ta tb () td u
      go (suc (suc k)) {zero} {suc zero} {suc zero} p q r ta tb () td u
      go (suc (suc k)) {zero} {suc zero} {suc (suc (suc _))} p q r ta tb () td u
      go (suc (suc k)) {zero} {suc zero} {suc (suc zero)} {zero} p q r ta tb tc () u
      go (suc (suc k)) {zero} {suc zero} {suc (suc zero)} {suc zero} p q r ta tb tc () u
      go (suc (suc k)) {zero} {suc zero} {suc (suc zero)} {suc (suc zero)} p q r ta tb tc () u
      go (suc (suc k)) {zero} {suc zero} {suc (suc zero)} {suc (suc (suc (suc _)))} p q r ta tb tc () u

    r7c-at : ∀ {a b : Fin n} .(p : a < b) → toℕ a ≡ 0 → toℕ b ≡ 1 → ∀ u →
             actIH k (actV (M-gen a) (actIH k u)) ≡ actV (M-gen a) (actV (X-gen a b p) (actV (M-gen a) u))
    r7c-at = go k
      where
      go : ∀ k {a b : Fin (k ℕ.* 2)} .(p : a < b) → toℕ a ≡ 0 → toℕ b ≡ 1 → ∀ u →
           actIH k (actV (M-gen a) (actIH k u)) ≡ actV (M-gen a) (actV (X-gen a b p) (actV (M-gen a) u))
      go (suc k) {zero} {suc zero} p refl refl u = r7c-act k u
      go zero {()}
      go (suc k) {suc _} p () tb u
      go (suc k) {zero} {zero} p ta () u
      go (suc k) {zero} {suc (suc _)} p ta () u

  sound-axiom : ∀ {w v : Word (Genᴸ n)} → w ===ᴸ v → ⟦ w ⟧ᴸ ≡ ⟦ v ⟧ᴸ
  sound-axiom (table1 {w} {v} h) = trans (⟦⌊⌋⟧ w) (trans (cong mapM (Sound1.sound-axiom h)) (sym (⟦⌊⌋⟧ v)))
  sound-axiom r7a = same-matrixᴸ (H • H) ε (r7a-act k)
  sound-axiom (r7b {a} {b} {c} {d} p q r ta tb tc td) =
    same-matrixᴸ (H • Kᴸ a b c d p q r • H) (Kᴸ a b c d p q r) (r7b-at p q r ta tb tc td)
  sound-axiom (r7c {a} {b} p ta tb) = same-matrixᴸ (H • Mᴸ a • H) (Mᴸ a • Xᴸ a b p • Mᴸ a) (r7c-at p ta tb)
  sound-axiom (r7d₀ {x} {y} p ty px) = same-matrixᴸ (H • Xᴸ x y p • H) (Mᴸ y) (r7d₀-act k x y p ty px)
  sound-axiom (r7d₁ {w} {x} {y} {z} p q r tx ty tz px) =
    same-matrixᴸ (H • Xᴸ x y q • H) (Xᴸ x y q • Kᴸ w x y z p q r) (r7d₁-act k w x y z p q r tx ty tz px)

  private
    module P = PB (_===ᴸ_ {n})

    ·*·-congˡ : ∀ {m} (A B : Matrix n n D) (M : Matrix n m D) → A ≡ B → A ·*· M ≡ B ·*· M
    ·*·-congˡ A B M refl = refl

  -- Derivable equations act alike.
  sound-act : ∀ {w v : Word (Genᴸ n)} → w P.≈ v → ∀ {m} (M : Matrix n m D) → actMᴸʷ w M ≡ actMᴸʷ v M
  sound-act P.refl M = refl
  sound-act (P.sym h) M = sym (sound-act h M)
  sound-act (P.trans h h′) M = trans (sound-act h M) (sound-act h′ M)
  sound-act (P.cong {w} {w′} {v} {v′} h h′) M = trans (cong (actMᴸʷ w) (sound-act h′ M)) (sound-act h (actMᴸʷ v′ M))
  sound-act P.assoc M = refl
  sound-act P.left-unit M = refl
  sound-act P.right-unit M = refl
  sound-act (P.axiom {w} {v} a) M =
    trans (actMᴸʷ≡ w M) (trans (·*·-congˡ ⟦ w ⟧ᴸ ⟦ v ⟧ᴸ M (sound-axiom a)) (sym (actMᴸʷ≡ v M)))

  -- Theorem 5.4.
  soundness : ∀ {w v : Word (Genᴸ n)} → w P.≈ v → ⟦ w ⟧ᴸ ≡ ⟦ v ⟧ᴸ
  soundness h = sound-act h 𝕀
