------------------------------------------------------------------------
-- Presentations of groups
--
-- Every physical X,CX,CCX,H generator is an involution at every width.
-- The vector proof uses only Boolean permutations and Hadamard kernels;
-- the structural encoder transfers it to the ordinary physical matrix.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.GeneralN.GateInvolutions where

open import Data.Nat.Base using (ℕ ; zero ; suc ; s≤s ; z≤n) renaming (_^_ to _^ℕ_)
import Data.Nat.Properties as NP
import Data.Fin.Base as Fin
open import Data.Sum.Base using (inj₁ ; inj₂)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality
open import Word.Base using ([_]ʷ ; ε ; _•_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (D ; RingD ; AdjointD)
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Ring as R
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as M
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
import Examples.Groups.CCX+HH.Syntactics as HH
import Examples.Groups.CCX+H.Syntactics as H
import Examples.Groups.CCX+H.GeneralN.StructuralEncoding as E
import Examples.Groups.CCX+H.GeneralN.Semantics as Q
import Examples.Groups.CCX+H.GeneralN.PhysicalSemantics as P
import Examples.Groups.CCX+HH.EncodingSemantics.Structural as Structural
import Examples.Groups.CCX+H.GeneralN.HadamardKernel as Kernel
open import Examples.Groups.CCX+HH.EncodingSemantics.Partition using (Partition)
open import Examples.Groups.CCX+HH.EncodingSemantics.Binary using (contiguous ; alternating)
open import Examples.Groups.CCX+HH.EncodingSemantics.Blocks
  R.isCommutativeRing-D R.adj-D R.½
  using (parallel ; parallel-compose ; parallel-cong ; parallel-id)

private
  module DQ = Structural R.isCommutativeRing-D R.adj-D R.½
  module K = Kernel R.isCommutativeRing-D R.adj-D R.½ R.√½ R.√½-sq R.√½-half

parallel-involutive : ∀ {m n} (p : Partition m n) (f : Vec D m → Vec D m) →
  (∀ v → f (f v) ≡ v) → ∀ v → parallel p f f (parallel p f f v) ≡ v
parallel-involutive p f inv v = trans (parallel-compose p f f f f v)
  (trans (parallel-cong p {f′ = λ x → x} {g′ = λ x → x} inv inv v) (parallel-id p v))

private
  x-involutive : ∀ n v → DQ.x n (DQ.x n v) ≡ v
  x-involutive zero (a ∷ b ∷ []) = refl
  x-involutive (suc n) = parallel-involutive (contiguous _) (DQ.x n) (x-involutive n)

  cx-involutive : ∀ n v → DQ.cx n (DQ.cx n v) ≡ v
  cx-involutive zero (a ∷ b ∷ c ∷ d ∷ []) = refl
  cx-involutive (suc n) = parallel-involutive (contiguous _) (DQ.cx n) (cx-involutive n)

  ccx-involutive : ∀ n v → DQ.ccx n (DQ.ccx n v) ≡ v
  ccx-involutive zero (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []) = refl
  ccx-involutive (suc n) = parallel-involutive (contiguous _) (DQ.ccx n) (ccx-involutive n)

  K₀ : T.Gen 4
  K₀ = T.K-gen Fin.zero (Fin.suc Fin.zero) (Fin.suc (Fin.suc Fin.zero))
    (Fin.suc (Fin.suc (Fin.suc Fin.zero)))
    (s≤s z≤n) (s≤s (s≤s z≤n)) (s≤s (s≤s (s≤s z≤n)))

  opaque
    unfolding M.actV M.set₁ M.set₂

    hh₀-action : ∀ v → M.actV K₀ v ≡ DQ.hh₀ v
    hh₀-action (a ∷ b ∷ c ∷ d ∷ []) = refl

  hh-involutive : ∀ n v → DQ.hh n (DQ.hh n v) ≡ v
  hh-involutive zero v = trans (sym (hh₀-action (DQ.hh₀ v)))
    (trans (cong (M.actV K₀) (sym (hh₀-action v))) (M.actV-invol K₀ v))
  hh-involutive (suc n) = parallel-involutive (contiguous _) (DQ.hh n) (hh-involutive n)

  dyadic-involutive : ∀ {n} (g : HH.Gen n) v → DQ.gate-action g (DQ.gate-action g v) ≡ v
  dyadic-involutive (HH.gate₀ ())
  dyadic-involutive (HH.gate₁ {n} HH.X-gate) = x-involutive n
  dyadic-involutive (HH.gate₂ {n} HH.CX-gate) = cx-involutive n
  dyadic-involutive (HH.gate₂ {n} HH.HH-gate) = hh-involutive n
  dyadic-involutive (HH.gate₃ {n} HH.CCX-gate) = ccx-involutive n
  dyadic-involutive (HH._↥ {n} g) = parallel-involutive (alternating (2 ^ℕ n))
    (DQ.gate-action g) (dyadic-involutive g)

  hwire-involutive : ∀ {n} (p : Fin.Fin n) v → K.hwire p (K.hwire p v) ≡ v
  hwire-involutive {suc n} Fin.zero = K.hbase-invol n
  hwire-involutive {suc zero} (Fin.suc ())
  hwire-involutive {suc (suc n)} (Fin.suc p) =
    parallel-involutive (alternating (2 ^ℕ suc n)) (K.hwire p) (hwire-involutive p)

action-involutive : ∀ {n} (g : H.Gen n) v → Q.gate-action g (Q.gate-action g v) ≡ v
action-involutive g v with E.classify g
... | inj₁ dg = dyadic-involutive dg v
... | inj₂ p = hwire-involutive p v

private
  cast-right : ∀ {j k} (p : j ≡ k) v → Q.cast-vector p (Q.cast-vector (sym p) v) ≡ v
  cast-right refl v = refl

  positive : ∀ n (g : H.Gen (suc n)) →
    P.interpret ([ g ]ʷ • [ g ]ʷ) ≡ P.interpret {suc n} ε
  positive n g = P.At.forward n {u = [ g ]ʷ • [ g ]ʷ} {v = ε}
    (trans (sym (C.encoding-correct ([ g ]ʷ • [ g ]ʷ)))
    (trans (SM.same-matrixᴸ (C.compile ([ g ]ʷ • [ g ]ʷ)) ε inv) (C.encoding-correct ε)))
    where
    module C = Q.At n
    module SM = M.Dim (2 ^ℕ n)
    inv : ∀ v → SM.actVᴸʷ (C.compile ([ g ]ʷ • [ g ]ʷ)) v ≡ v
    inv v = trans (C.word-action-correct ([ g ]ʷ • [ g ]ʷ) v)
      (trans (cong (Q.cast-vector (NP.*-comm 2 (2 ^ℕ n))) (action-involutive g _))
        (cast-right (NP.*-comm 2 (2 ^ℕ n)) v))

matrix-involutive : ∀ {n} (g : H.Gen n) →
  P.interpret ([ g ]ʷ • [ g ]ʷ) ≡ P.interpret {n} ε
matrix-involutive {zero} (H.gate₀ ())
matrix-involutive {suc n} g = positive n g
