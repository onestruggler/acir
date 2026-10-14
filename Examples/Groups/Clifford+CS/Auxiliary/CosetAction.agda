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
-- with w of determinant 1 — a word over P′ — and c′ = c + deg y.  The
-- table is scratchpad/four-wire-notes.md's, checked there on exact
-- matrices for every generator at every coset (tP.py: 256/256 cases
-- at N = 8, 1024/1024 at N = 16):
--
--     i_[a]                    i_[a] i_[0]⁻¹, at every coset;
--     X_[b,c], b ≠ 0           (−1)_[0] X_[b,c], at every coset;
--     X_[0,c]                  (−1)_[c] X_[0,c] (i_[c] i_[0]⁻¹)^k at ⟨k⟩;
--     K_[d,e], d ≠ 0           K_[d,e] K_[0,z]⁻¹ · Q(z), at every coset;
--     K_[0,e]                  one of four words, by the coset.
--
-- Q(z) spells K_[0,z] i_[0]⁻¹, which has determinant 1 but is no
-- letter: it is a phase pair around the commutator of a phase pair
-- and a K pair, relation (16) of the two-level presentation in
-- disguise, and it needs a fresh phase index w and a fresh K pair
-- (u , v) — on four indices no such word exists.  The fresh indices
-- are the first numerals 0 … 15 off the generator's indices and 0
-- (`Fresh`).  A phase pair on one index is ε by the rules, so the
-- phase row needs no case for a = 0.
--
-- Index 0 is `zero`, the width being a successor, so the case splits
-- are pattern matches; a generator's second index exceeds its first,
-- so only the first can be 0.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; suc ; _≤_)

module Examples.Groups.Clifford+CS.Auxiliary.CosetAction
  (N′ : ℕ) (big : 16 ≤ suc N′) where

open import Data.Fin using (Fin ; zero ; suc ; toℕ) renaming (_<_ to _<ᶠ_)
open import Data.Fin.Properties using (toℕ-injective)
open import Data.List using (List ; [] ; _∷_)
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.Nat using (z≤n ; s≤s)
open import Data.Nat.Properties using (n≢0⇒n>0)
open import Data.Product using (_×_ ; _,_ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; ε ; _•_ ; [_]ʷ ; _ᵗ)

import Examples.Groups.Clifford+CS-TwoLevel.Syntactics as TL
open TL using (i-gen ; X-gen ; K-gen)

open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP)
open import Examples.Groups.Clifford+CS.Auxiliary.Fragment using (pw ; xw)
open import Examples.Groups.Clifford+CS.Auxiliary.Rules using (kw)
open import Examples.Groups.Clifford+CS.Auxiliary.Cosets
  using (Coset ; ⟨0⟩ ; ⟨1⟩ ; ⟨2⟩ ; ⟨3⟩ ; inc ; inc² ; pows)
open import Examples.Groups.Clifford+CS.Auxiliary.Fresh (suc N′) big
  using (Off ; Fresh3 ; Fresh4 ; fresh3 ; fresh4)

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
-- Fresh indices

-- The first numerals off 0 and the generator's indices.
fr3 : (e : Fin N) → Fresh3 (zero ∷ e ∷ [])
fr3 e = fresh3 _ (s≤s (s≤s z≤n))

fr4 : (d e : Fin N) → Fresh4 (zero ∷ d ∷ e ∷ [])
fr4 d e = fresh4 _ (s≤s (s≤s (s≤s z≤n)))

-- An index off a list is off its head.
first : ∀ {x b : Fin N} {bs : List (Fin N)} → Off (b ∷ bs) x → x ≢ b
first (p ∷ _) = p

-- An index other than 0 is above it.
pos : ∀ {x : Fin N} → x ≢ zero → 𝟎 <ᶠ x
pos ne = n≢0⇒n>0 (λ e → ne (toℕ-injective e))

------------------------------------------------------------------------
-- The two spelled words

-- Q(z) = K_[0,z] i_[0]⁻¹, on the fresh w and (u , v).
Qw : (z w u v : Fin N) → .(𝟎 <ᶠ z) → .(u <ᶠ v) → W
Qw z w u v 0z uv =
  pw z zero • (pw w zero • (kw zero z u v 0z uv
              • (pw zero w • kw u v zero z uv 0z)))

-- i_[0]^c K_[0,e] i_[0]^-(c+1), on the fresh w and (u , v): the four
-- patterns tP.py tabulates.
K0w : Coset → (e w u v : Fin N) → .(𝟎 <ᶠ e) → .(u <ᶠ v) → W
K0w ⟨0⟩ e w u v 0e uv =
  pw e zero • (pw w zero • (kw zero e u v 0e uv
              • (pw zero w • kw u v zero e uv 0e)))
K0w ⟨1⟩ e w u v 0e uv =
  pw e zero • (kw zero e u v 0e uv
              • (pw zero w • (kw u v zero e uv 0e • pw w zero)))
K0w ⟨2⟩ e w u v 0e uv =
  pw e zero • (pw w zero • (kw zero e u v 0e uv
              • (pw e w • kw u v zero e uv 0e)))
K0w ⟨3⟩ e w u v 0e uv =
  pw e zero • (kw zero e u v 0e uv
              • (pw w zero • (kw u v zero e uv 0e • pw e w)))

------------------------------------------------------------------------
-- The rows of K

-- K_[0,e], at the coset c.
K0row : Coset → (e : Fin N) → .(𝟎 <ᶠ e) → W
K0row c e 0e = K0w c e f₁ f₂ f₃ 0e f₂<f₃
  where open Fresh3 (fr3 e)

-- K_[d,e] with d ≠ 0: K_[d,e] K_[0,z]⁻¹ · K_[0,z] i_[0]⁻¹.
Krow : (d e : Fin N) → .(d <ᶠ e) → W
Krow d e de = kw d e zero f₁ de 0z • Qw f₁ f₂ f₃ f₄ 0z f₃<f₄
  where
  open Fresh4 (fr4 d e)

  0z : 𝟎 <ᶠ f₁
  0z = pos (first off₁)

------------------------------------------------------------------------
-- The action

Step : Set
Step = W × Coset

act : Coset → TL.Gen N → Step
act c (i-gen a)           = pw a zero , inc c
act c (X-gen zero b p)    = xw b zero b p • pows c (pw b zero) , inc² c
act c (X-gen (suc a) b p) = xw zero (suc a) b p , inc² c
act c (K-gen zero e p)    = K0row c e p , inc c
act c (K-gen (suc d) e p) = Krow (suc d) e p , inc c

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
nxt c (K-gen zero e p)    = Eq.refl
nxt c (K-gen (suc d) e p) = Eq.refl

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
