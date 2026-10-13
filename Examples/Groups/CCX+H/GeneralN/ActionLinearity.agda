------------------------------------------------------------------------
-- Presentations of groups
--
-- The independent physical actions preserve arbitrary linear
-- combinations.  This follows from their source matrix realization,
-- without using the circuit presentation or its completeness theorem.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.GeneralN.ActionLinearity where

open import Data.Nat.Base using (ℕ ; zero ; suc ; _*_) renaming (_^_ to _^ℕ_)
import Data.Nat.Properties as NP
import Data.Fin.Base as Fin
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Quantum.Synthesis.Matrix using (Matrix ; Matrix')
import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring as R2
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Ring as R
open import Examples.Groups.CCX+H.Syntactics
import Examples.Groups.CCX+H.GeneralN.Semantics as S
import Examples.Groups.CCX+H.GeneralN.VectorLinearity as V
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as Source

open V {R.D} {{R2.RingD}} {{R2.AdjointD}} R.isCommutativeRing-D R.adj-D public
  using (combine ; combine-! ; Linear ; plus ; minus)
private
  module L = V {R.D} {{R2.RingD}} {{R2.AdjointD}} R.isCommutativeRing-D R.adj-D

  cast-combine : ∀ {j l} (p : j ≡ l) a b (u v : Vec R.D j) →
    S.cast-vector p (combine a b u v) ≡ combine a b (S.cast-vector p u) (S.cast-vector p v)
  cast-combine refl a b u v = refl

  cast-injective : ∀ {j l} (p : j ≡ l) {u v : Vec R.D j} →
    S.cast-vector p u ≡ S.cast-vector p v → u ≡ v
  cast-injective refl eq = eq

  module Even (k : ℕ) where
    module M = Source.Dim k

    column : Vec R.D (k * 2) → Matrix (k * 2) 1 R.D
    column v = Matrix' (v ∷ [])

    row : ∀ (w : Word (T.Genᴸ (k * 2))) v r →
      Source._!_ (M.actVᴸʷ w v) r ≡
      Source.sum (λ i → R2._*ᴰ_ (Source.ent M.⟦ w ⟧ᴸ r i) (Source._!_ v i))
    row w v r = trans (sym (cong (λ x → Source._!_ x r) (M.col-actMᴸʷ w (column v) Fin.zero)))
      (trans (cong (λ A → Source.ent A r Fin.zero) (M.actMᴸʷ≡ w (column v)))
        (Source.ent-·*· M.⟦ w ⟧ᴸ (column v) r Fin.zero))

    linear : ∀ w → Linear (M.actVᴸʷ w)
    linear w = L.by-matrix M.⟦ w ⟧ᴸ (M.actVᴸʷ w) (row w)

  positive : ∀ n (w : Circuit (suc n)) → Linear (S.action w)
  positive n w a b u v = cast-injective dimension
    (trans (sym (C.preserves-word-action w (combine a b u v)))
      (trans (cong (M.actVᴸʷ (C.compile w)) (cast-combine dimension a b u v))
        (trans (Even.linear k (C.compile w) a b (S.cast-vector dimension u) (S.cast-vector dimension v))
          (trans (cong₂ (combine a b) (C.preserves-word-action w u) (C.preserves-word-action w v))
            (sym (cast-combine dimension a b (S.action w u) (S.action w v)))))))
    where
    k = 2 ^ℕ n
    dimension : 2 ^ℕ suc n ≡ k * 2
    dimension = NP.*-comm 2 k
    module C = S.At n
    module M = Source.Dim k

gate-linear : ∀ {n} (g : Gen n) → Linear (S.gate-action g)
gate-linear {zero} (gate₀ ())
gate-linear {suc n} g = positive n [ g ]ʷ

action-linear : ∀ {n} (w : Circuit n) → Linear (S.action w)
action-linear [ g ]ʷ = gate-linear g
action-linear ε a b u v = refl
action-linear (u • v) = L.compose (S.action u) (S.action v) (action-linear u) (action-linear v)

plus-linear : ∀ {n} (w : Circuit n) a u v →
  S.action w (plus a u v) ≡ plus a (S.action w u) (S.action w v)
plus-linear w = L.plus-linear (S.action w) (action-linear w)

minus-linear : ∀ {n} (w : Circuit n) a u v →
  S.action w (minus a u v) ≡ minus a (S.action w u) (S.action w v)
minus-linear w = L.minus-linear (S.action w) (action-linear w)
