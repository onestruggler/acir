------------------------------------------------------------------------
-- Presentations of groups
--
-- Expand every physical HH into H on its upper and then lower wire.
-- The expansion preserves the independent vector semantics at every
-- width and wire placement, including all spectator coordinates.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.GeneralN.HadamardEmbedding where

open import Data.Nat.Base using (ℕ ; zero ; suc ; _*_) renaming (_^_ to _^ℕ_)
import Data.Nat.Properties as NP
open import Data.Sum.Base using (inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)
import Examples.Groups.CCX+HH.Syntactics as D
import Examples.Groups.CCX+HH.StructuralEncoding as DE
import Examples.Groups.CCX+HH.Semantics as DS
import Examples.Groups.CCX+H.Syntactics as H
import Examples.Groups.CCX+H.GeneralN.Semantics as S
import Examples.Groups.CCX+H.GeneralN.StructuralEncoding as E
import Examples.Groups.CCX+H.GeneralN.HadamardKernel as Kernel
import Examples.Groups.CCX+HH.EncodingSemantics.Structural as Dyadic
import Examples.Groups.CCX+HH.EncodingSemantics.Blocks as Blocks
open import Examples.Groups.CCX+HH.EncodingSemantics.Binary using (alternating)
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Ring as R
import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring as R2
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as U
import Examples.Groups.CCX+HH-TwoLevel.Semantics as US
import Examples.Groups.CCX+HH-TwoLevel.MainLemma as Complete
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as TS
import Presentation.Base as PB

private
  module K = Kernel {R.D} {{R2.RingD}} {{R2.AdjointD}}
    R.isCommutativeRing-D R.adj-D R.½ R.√½ R.√½-sq R.√½-half
  module Q = Dyadic {R.D} {{R2.RingD}} {{R2.AdjointD}}
    R.isCommutativeRing-D R.adj-D R.½
  module B = Blocks {R.D} {{R2.RingD}} {{R2.AdjointD}}
    R.isCommutativeRing-D R.adj-D R.½

e : ∀ {n} → D.Gen n → H.Circuit n
e (D.gate₀ ())
e (D.gate₁ D.X-gate) = H.X
e (D.gate₂ D.CX-gate) = H.CX
e (D.gate₂ D.HH-gate) = (H.H H.↑) • H.H
e (D.gate₃ D.CCX-gate) = H.CCX
e (g D.↥) = e g H.↑

embed : ∀ {n} → D.Circuit n → H.Circuit n
embed = e ʷ

private
  gate-shift : ∀ {n} (g : H.Gen n) v →
    S.gate-action (g H.↥) v ≡ Q.bottom {n} (S.gate-action g) v
  gate-shift {zero} g v with E.classify g
  ... | inj₁ dg = refl
  ... | inj₂ ()
  gate-shift {suc n} g v with E.classify g
  ... | inj₁ dg = refl
  ... | inj₂ p = refl

  shift : ∀ {n} (w : H.Circuit n) v →
    S.action (w H.↑) v ≡ Q.bottom {n} (S.action w) v
  shift [ g ]ʷ = gate-shift g
  shift {n} ε v = sym (B.parallel-id (alternating (2 ^ℕ n)) v)
  shift {n} (u • w) v = trans (shift u (S.action (w H.↑) v))
    (trans (cong (Q.bottom {n} (S.action u)) (shift w v))
      (B.parallel-compose (alternating (2 ^ℕ n))
        (S.action u) (S.action u) (S.action w) (S.action w) v))

gate-correct : ∀ {n} (g : D.Gen n) v → S.action (e g) v ≡ Q.gate-action g v
gate-correct (D.gate₀ ()) v
gate-correct (D.gate₁ D.X-gate) v = refl
gate-correct (D.gate₂ D.CX-gate) v = refl
gate-correct (D.gate₂ {n} D.HH-gate) v = sym (K.hh-tensor n v)
gate-correct (D.gate₃ D.CCX-gate) v = refl
gate-correct (D._↥ {n} g) v = trans (shift (e g) v)
  (B.parallel-cong (alternating (2 ^ℕ n)) (gate-correct g) (gate-correct g) v)

correct : ∀ {n} (w : D.Circuit n) v → S.action (embed w) v ≡ K.run w v
correct [ g ]ʷ = gate-correct g
correct ε v = refl
correct (u • w) v = trans (cong (S.action (embed u)) (correct w v))
  (correct u (K.run w v))

module At (n : ℕ) where
  private
    k = 2 ^ℕ n
    dimension : 2 ^ℕ suc n ≡ k * 2
    dimension = NP.*-comm 2 k
    module C = S.At n
    module M = TS.Dim k

    cast-right : ∀ {j l} (p : j ≡ l) v →
      S.cast-vector p (S.cast-vector (sym p) v) ≡ v
    cast-right refl v = refl

  dyadic-compile : D.Circuit (suc n) → Word (T.Genᴸ (k * 2))
  dyadic-compile w = S.cast-word dimension T.⌊ DE.encode w ⌋ʷ

  private
    agrees-cast : ∀ w v →
      M.actVᴸʷ (C.compile (embed w)) (S.cast-vector dimension v) ≡
      M.actVᴸʷ (dyadic-compile w) (S.cast-vector dimension v)
    agrees-cast w v = trans (C.preserves-word-action (embed w) v)
      (trans (cong (S.cast-vector dimension)
          (trans (correct w v) (sym (K.run-correct w v))))
        (sym (C.preserves-dyadic-action (DE.encode w) v)))

    agrees : ∀ w v → M.actVᴸʷ (C.compile (embed w)) v ≡
      M.actVᴸʷ (dyadic-compile w) v
    agrees w v = trans (cong (M.actVᴸʷ (C.compile (embed w)))
        (sym (cast-right dimension v)))
      (trans (agrees-cast w (S.cast-vector (sym dimension) v))
        (cong (M.actVᴸʷ (dyadic-compile w)) (cast-right dimension v)))

  encoding-correct : ∀ w → C.interpret (embed w) ≡ M.⟦ dyadic-compile w ⟧ᴸ
  encoding-correct w = trans (sym (C.encoding-correct (embed w)))
    (M.same-matrixᴸ (C.compile (embed w)) (dyadic-compile w) (agrees w))

  private
    cast-cong : ∀ {j l} (p : j ≡ l) {u v : Word (T.Genᴸ j)} →
      PB._≈_ T._===ᴸ_ u v → PB._≈_ T._===ᴸ_ (S.cast-word p u) (S.cast-word p v)
    cast-cong refl eq = eq

  -- Any dyadic physical realization can now be reused in H circuits.
  -- The complete auxiliary dyadic theory transports the matrix equality
  -- across the scalar embedding and the dimension equality.
  realises : ∀ (w : D.Circuit (suc n)) (u : Word (U.Gen (2 ^ℕ suc n))) →
    DS.interpret w ≡ US.⟦ u ⟧ᵐ →
    C.interpret (embed w) ≡ M.⟦ S.cast-word dimension T.⌊ u ⌋ʷ ⟧ᴸ
  realises w u eq = trans (encoding-correct w)
    (TS.soundness k (cast-cong dimension (T.⌊⌋-cong
      (Complete.completeness {u = DE.encode w} {v = u}
        (trans (DS.encoding-correct w) eq)))))
