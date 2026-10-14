------------------------------------------------------------------------
-- Presentations of groups
--
-- The coset action of the Reidemeister–Schreier method
--
-- The method's third datum slides a two-level generator past a coset:
-- `act c y = (w , c′)` means, as matrices,
--
--     rep c · y  =  w · rep c′,      rep c = i_[0]^c,
--
-- with w of determinant 1 — a word over P′ — and c′ = c + deg y:
--
--     i_[a]          i_[a] i_[0]⁻¹, at every coset;
--     X_[b,c], b ≠ 0 (−1)_[0] X_[b,c], at every coset;
--     X_[0,c]        (−1)_[c] X_[0,c] (i_[c] i_[0]⁻¹)^k at ⟨k⟩;
--     K_[d,e]        (i_[0] i_[t]⁻¹)^k · K_[d,e] i_[t]⁻¹ · (i_[t] i_[0]⁻¹)^(k+1)
--                    at ⟨k⟩, t the first numeral off 0, d and e.
--
-- The K row conjugates the hybrid letter at the sink t by i_[0]^k
-- i_[t]^-k, which i_[t] makes uniform: no case on whether d is 0, and
-- no relation (16) — conjugating K_[0,e] by i_[0] itself would need it.
-- Checked on exact matrices at every generator and coset
-- (scratchpad/tKI.py: 256/256 at N = 8).  A phase pair on one index is
-- ε by the rules, so the phase row needs no case for a = 0.
--
-- Index 0 is `zero`, the width being a successor, so the case split of
-- the exchange row is a pattern match; a generator's second index
-- exceeds its first, so only the first can be 0.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; suc ; _≤_)

module Examples.Groups.Clifford+CS.Auxiliary.CosetAction
  (N′ : ℕ) (big : 16 ≤ suc N′) where

open import Data.Fin using (Fin ; zero ; suc ; toℕ) renaming (_<_ to _<ᶠ_)
open import Data.List using (List ; [] ; _∷_)
open import Data.Nat using (z≤n ; s≤s)
open import Data.Product using (_×_ ; _,_ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; ε ; _•_ ; [_]ʷ ; _ᵗ)

import Examples.Groups.Clifford+CS-TwoLevel.Syntactics as TL
open TL using (i-gen ; X-gen ; K-gen)

open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP)
open import Examples.Groups.Clifford+CS.Auxiliary.Fragment using (pw ; xw)
open import Examples.Groups.Clifford+CS.Auxiliary.Rules using (kiw)
open import Examples.Groups.Clifford+CS.Auxiliary.Cosets
  using (Coset ; ⟨0⟩ ; ⟨1⟩ ; ⟨2⟩ ; ⟨3⟩ ; inc ; inc² ; pows)
open import Examples.Groups.Clifford+CS.Auxiliary.Fresh (suc N′) big
  using (Off ; Fresh3 ; fresh3)

private
  N : ℕ
  N = suc N′

  W : Set
  W = Word (GenP N)

------------------------------------------------------------------------
-- The representatives

-- Index 0, named: Fin's ordering is heterogeneous in the widths, so
-- `zero <ᶠ x` alone would leave the width of `zero` open.
𝟎 : Fin N
𝟎 = zero

rep : Coset → Word (TL.Gen N)
rep c = pows c (TL.i zero)

------------------------------------------------------------------------
-- The sink of a K row

-- The first numerals off 0 and the K's indices.
fr : (d e : Fin N) → Fresh3 (zero ∷ d ∷ e ∷ [])
fr d e = fresh3 _ (s≤s (s≤s (s≤s z≤n)))

sink : (d e : Fin N) → Fin N
sink d e = Fresh3.f₁ (fr d e)

sink-off : (d e : Fin N) → Off (zero ∷ d ∷ e ∷ []) (sink d e)
sink-off d e = Fresh3.off₁ (fr d e)

-- i_[0]^c K_[d,e] i_[0]^-(c+1), through the sink t.
Krow : Coset → (d e : Fin N) → .(d <ᶠ e) → W
Krow c d e de =
  pows c (pw 𝟎 (sink d e))
  • (kiw d e (sink d e) de • pows (inc c) (pw (sink d e) 𝟎))

------------------------------------------------------------------------
-- The action

Step : Set
Step = W × Coset

act : Coset → TL.Gen N → Step
act c (i-gen a)           = pw a zero , inc c
act c (X-gen zero b p)    = xw b zero b p • pows c (pw b zero) , inc² c
act c (X-gen (suc a) b p) = xw zero (suc a) b p , inc² c
act c (K-gen d e p)       = Krow c d e p , inc c

------------------------------------------------------------------------
-- The coset reached
--
-- The degree of a generator decides the coset it moves to, whatever
-- its indices; `run-cos` follows that along a word.

dstep : TL.Gen N → Coset → Coset
dstep (i-gen _)     = inc
dstep (X-gen _ _ _) = inc²
dstep (K-gen _ _ _) = inc

nxt : ∀ (c : Coset) (y : TL.Gen N) → proj₂ (act c y) ≡ dstep y c
nxt c (i-gen a)           = Eq.refl
nxt c (X-gen zero b p)    = Eq.refl
nxt c (X-gen (suc a) b p) = Eq.refl
nxt c (K-gen d e p)       = Eq.refl

cos : Coset → Word (TL.Gen N) → Coset
cos c [ y ]ʷ  = dstep y c
cos c ε       = c
cos c (u • v) = cos (cos c u) v

run-cos : ∀ (c : Coset) (u : Word (TL.Gen N)) → proj₂ ((act ᵗ) c u) ≡ cos c u
run-cos c [ y ]ʷ  = nxt c y
run-cos c ε       = Eq.refl
run-cos c (u • v) =
  Eq.trans (run-cos (proj₂ ((act ᵗ) c u)) v)
           (Eq.cong (λ d → cos d v) (run-cos c u))
