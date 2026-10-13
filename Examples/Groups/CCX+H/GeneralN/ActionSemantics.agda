------------------------------------------------------------------------
-- Presentations of groups
--
-- Equality of physical matrices is exactly equality of their actions
-- on arbitrary state vectors.  The proof uses the established encoder
-- bridge and matrix multiplication, with no circuit completeness input.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.GeneralN.ActionSemantics where

open import Data.Nat.Base using (ℕ ; zero ; suc ; _*_) renaming (_^_ to _^ℕ_)
import Data.Nat.Properties as NP
import Data.Fin.Base as Fin
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Quantum.Synthesis.Matrix using (Matrix ; Matrix' ; _·*·_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (D ; RingD)
open import Examples.Groups.CCX+H.Syntactics
import Examples.Groups.CCX+H.GeneralN.Semantics as S
import Examples.Groups.CCX+H.GeneralN.PhysicalSemantics as P
import Examples.Groups.CCX+H.GeneralN.SmallPhysicalSemantics as Small
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as Source

private
  cast-injective : ∀ {j l} (p : j ≡ l) {u v : Vec D j} →
    S.cast-vector p u ≡ S.cast-vector p v → u ≡ v
  cast-injective refl eq = eq

  zero-action : ∀ (w : Circuit 0) v → S.action w v ≡ v
  zero-action [ gate₀ () ]ʷ v
  zero-action ε v = refl
  zero-action (u • w) v = trans (cong (S.action u) (zero-action w v)) (zero-action u v)

  module Even (k : ℕ) where
    module M = Source.Dim k

    column : Vec D (k * 2) → Matrix (k * 2) 1 D
    column v = Matrix' (v ∷ [])

    matrix-action : ∀ (u w : Word (T.Genᴸ (k * 2))) →
      M.⟦ u ⟧ᴸ ≡ M.⟦ w ⟧ᴸ → ∀ v → M.actVᴸʷ u v ≡ M.actVᴸʷ w v
    matrix-action u w eq v = trans (sym (M.col-actMᴸʷ u (column v) Fin.zero))
      (trans (cong (λ A → Source.col A Fin.zero)
        (trans (M.actMᴸʷ≡ u (column v))
          (trans (cong (_·*· column v) eq) (sym (M.actMᴸʷ≡ w (column v))))))
        (M.col-actMᴸʷ w (column v) Fin.zero))

  module Positive (n : ℕ) where
    k = 2 ^ℕ n
    dimension : 2 ^ℕ suc n ≡ k * 2
    dimension = NP.*-comm 2 k
    module C = S.At n
    module M = Source.Dim k

    action⇒matrix : ∀ {u w : Circuit (suc n)} →
      (∀ v → S.action u v ≡ S.action w v) → P.interpret u ≡ P.interpret w
    action⇒matrix {u} {w} eq = P.At.forward n {u} {w}
      (trans (sym (C.encoding-correct u))
        (trans (M.same-matrixᴸ (C.compile u) (C.compile w) same)
          (C.encoding-correct w)))
      where
      same : ∀ v → M.actVᴸʷ (C.compile u) v ≡ M.actVᴸʷ (C.compile w) v
      same v = trans (C.word-action-correct u v)
        (trans (cong (S.cast-vector dimension) (eq (S.cast-vector (sym dimension) v)))
          (sym (C.word-action-correct w v)))

    matrix⇒action : ∀ {u w : Circuit (suc n)} → P.interpret u ≡ P.interpret w →
      ∀ v → S.action u v ≡ S.action w v
    matrix⇒action {u} {w} eq v = cast-injective dimension
      (trans (sym (C.preserves-word-action u v))
        (trans (Even.matrix-action k (C.compile u) (C.compile w) source-eq
          (S.cast-vector dimension v)) (C.preserves-word-action w v)))
      where
      source-eq : M.⟦ C.compile u ⟧ᴸ ≡ M.⟦ C.compile w ⟧ᴸ
      source-eq = trans (C.encoding-correct u)
        (trans (P.At.backward n {u} {w} eq) (sym (C.encoding-correct w)))

action⇒matrix : ∀ {n} {u w : Circuit n} →
  (∀ v → S.action u v ≡ S.action w v) → P.interpret u ≡ P.interpret w
action⇒matrix {zero} {u} {w} eq = trans (Small.zero-identity u) (sym (Small.zero-identity w))
action⇒matrix {suc n} = Positive.action⇒matrix n

matrix⇒action : ∀ {n} {u w : Circuit n} → P.interpret u ≡ P.interpret w →
  ∀ v → S.action u v ≡ S.action w v
matrix⇒action {zero} {u} {w} eq v = trans (zero-action u v) (sym (zero-action w v))
matrix⇒action {suc n} = Positive.matrix⇒action n
