------------------------------------------------------------------------
-- Presentations of groups
--
-- The structural CCX+H compiler preserves independent tensor semantics
-- at every positive width.  Only equality of the two natural-number
-- spellings 2^(n+1) and (2^n)*2 is transported; basis order is unchanged.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.GeneralN.Semantics where

open import Data.Nat.Base using (ℕ ; zero ; suc ; _*_) renaming (_^_ to _^ℕ_)
import Data.Nat.Properties as NP
open import Data.Fin.Base using (Fin)
open import Data.Sum.Base using (inj₁ ; inj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; tabulate)
open import Relation.Binary.PropositionalEquality
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)
open import Quantum.Synthesis.Matrix using (Matrix ; Matrix' ; _·*·_)

open import Examples.Groups.CCX+H.Syntactics
import Examples.Groups.CCX+H.GeneralN.StructuralEncoding as E
import Examples.Groups.CCX+H.GeneralN.HadamardKernel as Kernel
import Examples.Groups.CCX+H.GeneralN.PairBlocks as PairBlocks
import Examples.Groups.CCX+HH.StructuralEncoding as DE
import Examples.Groups.CCX+HH.EncodingSemantics.Structural as Dyadic
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as U
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as S
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Ring as R
import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring as R2
open R2 using (RingD ; AdjointD)
open import Instances using (_+_ ; -_) renaming (_*_ to _*ᴰ_)

private
  module K = Kernel {R.D} {{R2.RingD}} {{R2.AdjointD}}
    R.isCommutativeRing-D R.adj-D R.½ R.√½ R.√½-sq R.√½-half
  module D = Dyadic {R.D} {{R2.RingD}} {{R2.AdjointD}}
    R.isCommutativeRing-D R.adj-D R.½
  module Pairs = PairBlocks {R.D}
    (λ a b → R.√½ *ᴰ (a + b)) (λ a b → R.√½ *ᴰ (a + - b))

State : ℕ → Set
State n = Vec R.D (2 ^ℕ n)

-- This definition uses only the gate kind, its indexed wire position,
-- and the independently specified Boolean/Hadamard tensor kernels.
gate-action : ∀ {n} → Gen n → State n → State n
gate-action g with E.classify g
... | inj₁ dg = D.gate-action dg
... | inj₂ p = K.hwire p

action : ∀ {n} → Circuit n → State n → State n
action [ g ]ʷ = gate-action g
action ε v = v
action (u • w) v = action u (action w v)

cast-vector : ∀ {m n} → m ≡ n → Vec R.D m → Vec R.D n
cast-vector = Pairs.cast

cast-word : ∀ {m n} → m ≡ n → Word (T.Genᴸ m) → Word (T.Genᴸ n)
cast-word refl w = w

cast-dyadic : ∀ {m n} → m ≡ n → Word (U.Gen m) → Word (U.Gen n)
cast-dyadic refl w = w

cast-product : ∀ {m n} (p : m ≡ n) u v →
  cast-word p (u • v) ≡ cast-word p u • cast-word p v
cast-product refl u v = refl

cast-empty : ∀ {m n} (p : m ≡ n) → cast-word p ε ≡ ε
cast-empty refl = refl

private
  cast-lift : ∀ {m n} (p : m ≡ n) w →
    cast-word p T.⌊ w ⌋ʷ ≡ T.⌊ cast-dyadic p w ⌋ʷ
  cast-lift refl w = refl

  cast-H : ∀ {m n} (p : m ≡ n) → cast-word p T.H ≡ T.H
  cast-H refl = refl

  cast-action : ∀ {m n} (p : m ≡ n) w v →
    Pairs.cast p (S.actVʷ w v) ≡ S.actVʷ (cast-dyadic p w) (Pairs.cast p v)
  cast-action refl w v = refl

  cast-right : ∀ {m n} (p : m ≡ n) v → Pairs.cast p (Pairs.cast (sym p) v) ≡ v
  cast-right refl v = refl

  flat-source : ∀ k v → Pairs.flat k v ≡ S.actIH k v
  flat-source zero [] = refl
  flat-source (suc k) (a ∷ b ∷ v) =
    cong (λ w → R.√½ *ᴰ (a + b) ∷ R.√½ *ᴰ (a + - b) ∷ w) (flat-source k v)

  lift-action : ∀ k w v → (S.Dim.actVᴸʷ k) T.⌊ w ⌋ʷ v ≡ S.actVʷ w v
  lift-action k [ g ]ʷ v = refl
  lift-action k ε v = refl
  lift-action k (u • w) v = trans
    (cong (S.Dim.actVᴸʷ k T.⌊ u ⌋ʷ) (lift-action k w v))
    (lift-action k u (S.actVʷ w v))

module At (n : ℕ) where
  private
    k = 2 ^ℕ n
    dimension : 2 ^ℕ suc n ≡ k * 2
    dimension = NP.*-comm 2 k
    module M = S.Dim k

  compile-gen : Gen (suc n) → Word (T.Genᴸ (k * 2))
  compile-gen g = cast-word dimension (E.e g)

  compile : Circuit (suc n) → Word (T.Genᴸ (k * 2))
  compile = compile-gen ʷ

  compile-cast : ∀ w → compile w ≡ cast-word dimension (E.encode w)
  compile-cast [ g ]ʷ = refl
  compile-cast ε = sym (cast-empty dimension)
  compile-cast (u • v) = trans (cong₂ _•_ (compile-cast u) (compile-cast v))
    (sym (cast-product dimension (E.encode u) (E.encode v)))

  private
    lift-correct : ∀ w v →
      M.actVᴸʷ (cast-word dimension T.⌊ w ⌋ʷ) (Pairs.cast dimension v) ≡
      Pairs.cast dimension (S.actVʷ w v)
    lift-correct w v = trans
      (cong (λ z → M.actVᴸʷ z (Pairs.cast dimension v)) (cast-lift dimension w))
      (trans (lift-action k (cast-dyadic dimension w) (Pairs.cast dimension v))
        (sym (cast-action dimension w v)))

    H-correct : ∀ (p : Fin (suc n)) v →
      M.actVᴸʷ (cast-word dimension (T.⌊ DE.encode (E.prefix p) ⌋ʷ • T.H))
        (Pairs.cast dimension v) ≡ Pairs.cast dimension (K.hwire p v)
    H-correct p v = trans
      (cong (λ w → M.actVᴸʷ w (Pairs.cast dimension v))
        (cast-product dimension T.⌊ DE.encode (E.prefix p) ⌋ʷ T.H))
      (trans (cong (λ w → M.actVᴸʷ (cast-word dimension T.⌊ DE.encode (E.prefix p) ⌋ʷ)
        (M.actVᴸʷ w (Pairs.cast dimension v))) (cast-H dimension))
        (trans (cong (M.actVᴸʷ (cast-word dimension T.⌊ DE.encode (E.prefix p) ⌋ʷ))
          (sym (trans (K.hbase-flat n dimension v) (flat-source k (Pairs.cast dimension v)))))
          (trans (lift-correct (DE.encode (E.prefix p)) (K.hbase n v))
            (cong (Pairs.cast dimension)
              (trans (K.run-correct (E.prefix p) (K.hbase n v)) (K.prefix-correct p v))))))

  preserves-action : ∀ g v → M.actVᴸʷ (compile-gen g) (Pairs.cast dimension v) ≡
    Pairs.cast dimension (gate-action g v)
  preserves-action g v with E.classify g
  ... | inj₁ dg = trans (lift-correct (DE.e dg) v)
    (cong (Pairs.cast dimension) (D.encoding-correct-action dg v))
  ... | inj₂ p = H-correct p v

  preserves-dyadic-action : ∀ w v →
    M.actVᴸʷ (cast-word dimension T.⌊ w ⌋ʷ) (cast-vector dimension v) ≡
    cast-vector dimension (S.actVʷ w v)
  preserves-dyadic-action = lift-correct

  -- Express the same physical action in the source's definitionally
  -- even dimension.  Transport is along equality, never a permutation.
  physical-action : Gen (suc n) → Vec R.D (k * 2) → Vec R.D (k * 2)
  physical-action g v = Pairs.cast dimension (gate-action g (Pairs.cast (sym dimension) v))

  action-correct : ∀ g v → M.actVᴸʷ (compile-gen g) v ≡ physical-action g v
  action-correct g v = trans
    (cong (M.actVᴸʷ (compile-gen g)) (sym (cast-right dimension v)))
    (preserves-action g (Pairs.cast (sym dimension) v))

  preserves-word-action : ∀ w v →
    M.actVᴸʷ (compile w) (Pairs.cast dimension v) ≡ Pairs.cast dimension (action w v)
  preserves-word-action [ g ]ʷ = preserves-action g
  preserves-word-action ε v = refl
  preserves-word-action (u • w) v = trans
    (cong (M.actVᴸʷ (compile u)) (preserves-word-action w v))
    (preserves-word-action u (action w v))

  word-action-correct : ∀ w v → M.actVᴸʷ (compile w) v ≡
    Pairs.cast dimension (action w (Pairs.cast (sym dimension) v))
  word-action-correct w v = trans
    (cong (M.actVᴸʷ (compile w)) (sym (cast-right dimension v)))
    (preserves-word-action w (Pairs.cast (sym dimension) v))

  gate-matrix : Gen (suc n) → Matrix (k * 2) (k * 2) R.D
  gate-matrix g = Matrix' (tabulate λ j → physical-action g (S.col S.𝕀 j))

  interpret : Circuit (suc n) → Matrix (k * 2) (k * 2) R.D
  interpret [ g ]ʷ = gate-matrix g
  interpret ε = S.𝕀
  interpret (u • v) = interpret u ·*· interpret v

  gate-correct : ∀ g → M.⟦ compile-gen g ⟧ᴸ ≡ gate-matrix g
  gate-correct g = S.col-ext λ j → trans (M.col-actMᴸʷ (compile-gen g) S.𝕀 j)
    (trans (action-correct g (S.col S.𝕀 j))
      (sym (S.!-tabulate (λ i → physical-action g (S.col S.𝕀 i)) j)))

  encoding-correct : ∀ w → M.⟦ compile w ⟧ᴸ ≡ interpret w
  encoding-correct [ g ]ʷ = gate-correct g
  encoding-correct ε = refl
  encoding-correct (u • v) = trans (M.⟦•⟧ᴸ (compile u) (compile v))
    (cong₂ _·*·_ (encoding-correct u) (encoding-correct v))
