------------------------------------------------------------------------
-- Presentations of groups
--
-- The Figure-8 gates as matrices, and the fifteen relations they satisfy
--
-- The gates, over ℤ/17ℤ, with i = 4 and 1/√2 = 14 (so −1/√2 = 3):
--
--     ω  ↦ 2 · I        S ↦ diag(1 , i)      H ↦ (1/√2) [1  1 ]
--                                                        [1 −1 ]
--     CZ ↦ diag(1 , 1 , 1 , −1)
--
-- A circuit is read twice.  ⟦_⟧ lands in Op and is the interpretation
-- the presentation is proved sound for — it is uniform in the width, so
-- the structural rules can be proved once.  ⟦_⟧M lands in Mat and is the
-- same reading stored as a trie: it tabulates after every letter, so a
-- product of twenty gates costs twenty matrix multiplications instead of
-- 8²⁰ entry lookups.  The fifteen relations are checked there.
--
-- `localise` is what connects them.  A Figure-8 relation is stated at
-- every width, but its two sides only ever mention the bottom one, two
-- or three wires: the relator at width k + n is literally the relator at
-- width k with idle wires padded on top (_↓ᵏ_, which is the identity on
-- gates).  So
--
--     ⟦ w ↓ᵏ n ⟧ ≐ emb ⟦ w ⟧M,
--
-- and an axiom at any width follows from ONE equation of matrices at the
-- width the axiom is written for.  Without it each relation would have
-- to be re-assembled letter by letter at the ambient width.
--
-- The relations below are exactly Selinger's, with the width pinned:
-- C1 lives at width 0 (the scalar is 0-ary), C2–C4 at width 1, C5–C11 at
-- width 2 and C12–C15 at width 3.  Each is Eq.refl — a computation on
-- tries, and the last three are products of about twenty 8 × 8 matrices,
-- which is where this module spends its time.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Clifford.Qubit.Model.Gates where

open import Data.Bool using (Bool ; true ; false)
open import Data.Vec using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)

open import ForStdlib.Data.Fin.Mod.Prime.Two using (p-2 ; p-prime)

open import Examples.Groups.Clifford.Qubit.Model.Algebra
open import Examples.Groups.Clifford.Qubit.Model.Local

import Examples.Groups.Clifford.Qubit.Selinger.Figure8 p-2 p-prime as F8
open F8
  using ( ExactGate ; ω-gate ; H-gate ; S-gate ; CZ-gate
        ; Gen ; Circuit ; gate₀ ; gate₁ ; gate₂ ; _↥ ; _↑ ; _↓
        ; ω ; S ; H ; CZ ; SH ; X ; Z ; ω⁻¹ ; ₕ|ₕ ; ʰ|ʰ ; ⊥⊤ ; ⊤⊥)

-- _↓ᵏ_ is the padding Figure 8 does not re-export: it widens a circuit
-- by idle wires on top, and is the identity on every gate.
open import Circuit.Base ExactGate using (_↓ᵏ_ ; _↧ᵏ_)

private
  variable
    k n : ℕ

------------------------------------------------------------------------
-- The gate matrices

private
  -- (1/√2) [[1 , 1] , [1 , −1]].
  hval : Bool → Bool → 𝔽
  hval true true = 3
  hval _    _    = 14

  -- diag(1 , i).
  sval : Bool → Bool → 𝔽
  sval false false = 1
  sval true  true  = 4
  sval _     _     = 0

  -- The controlled-Z phase: −1 = 16 on |11⟩.
  czval : Bool → Bool → 𝔽
  czval true true = 16
  czval _    _    = 1

hM sM : Mat 1
hM = matOf (λ { (x ∷ []) (y ∷ []) → hval x y })
sM = matOf (λ { (x ∷ []) (y ∷ []) → sval x y })

czM : Mat 2
czM = matOf (λ { (x ∷ x' ∷ []) y → czval x x' * δb (x ∷ x' ∷ []) y })

------------------------------------------------------------------------
-- The two readings of a circuit

valOp : Gen n → Op n
valOp (gate₀ ω-gate)  = scal 2
valOp (gate₁ H-gate)  = emb hM
valOp (gate₁ S-gate)  = emb sM
valOp (gate₂ CZ-gate) = emb czM
valOp (g ↥)           = up (valOp g)

⟦_⟧ : Circuit n → Op n
⟦ [ g ]ʷ ⟧ = valOp g
⟦ ε ⟧      = Idₒ
⟦ w • v ⟧  = ⟦ w ⟧ ⊙ ⟦ v ⟧

valMat : Gen k → Mat k
valMat (gate₀ ω-gate)  = scalM 2
valMat (gate₁ H-gate)  = tenM hM idM
valMat (gate₁ S-gate)  = tenM sM idM
valMat (gate₂ CZ-gate) = tenM czM idM
valMat (g ↥)           = tenM (idM {1}) (valMat g)

⟦_⟧M : Circuit k → Mat k
⟦ [ g ]ʷ ⟧M = valMat g
⟦ ε ⟧M      = idM
⟦ w • v ⟧M  = mulM ⟦ w ⟧M ⟦ v ⟧M

------------------------------------------------------------------------
-- Localisation
--
-- A circuit written at width k, read at width k + n, is its own matrix
-- acting on the bottom k wires.

localise-gen : (g : Gen k) → valOp (g ↧ᵏ n) ≐ emb {k} {n} (valMat g)
localise-gen {k} {n} (gate₀ ω-gate) = scal-emb {k} {n} 2
localise-gen (gate₁ H-gate)  = emb-pad₁ hM
localise-gen (gate₁ S-gate)  = emb-pad₁ sM
localise-gen (gate₂ CZ-gate) = emb-pad₂ czM
localise-gen (g ↥)           =
  ≐-trans (up-cong (localise-gen g)) (up-emb (valMat g))

localise : (w : Circuit k) → ⟦ w ↓ᵏ n ⟧ ≐ emb {k} {n} ⟦ w ⟧M
localise [ g ]ʷ      = localise-gen g
localise {k} {n} ε   = ≐-sym (emb-id {k} {n})
localise (w • v) =
  ≐-trans (⊙-cong (localise w) (localise v)) (emb-⊙ ⟦ w ⟧M ⟦ v ⟧M)

------------------------------------------------------------------------
-- The relators, at the width each is written for
--
-- Named rather than inlined so that the relation checks below and the
-- soundness proof that uses them cannot drift apart.

-- (a) width 0: the scalar
c1ˡ c1ʳ : Circuit 0
c1ˡ = ω ^ 8
c1ʳ = ε

-- (b) width 1
c2ˡ c2ʳ c3ˡ c3ʳ c4ˡ c4ʳ : Circuit 1
c2ˡ = H ^ 2
c2ʳ = ε
c3ˡ = S ^ 4
c3ʳ = ε
c4ˡ = SH ^ 3
c4ʳ = ω

-- (c) width 2
c5ˡ c5ʳ c6ˡ c6ʳ c7ˡ c7ʳ c8ˡ c8ʳ c9ˡ c9ʳ c10ˡ c10ʳ c11ˡ c11ʳ : Circuit 2
c5ˡ  = CZ ^ 2
c5ʳ  = ε
c6ˡ  = S ↓ • CZ
c6ʳ  = CZ • S ↓
c7ˡ  = S ↑ • CZ
c7ʳ  = CZ • S ↑
c8ˡ  = X ↓ • CZ
c8ʳ  = CZ • X ↓ • Z ↑
c9ˡ  = X ↑ • CZ
c9ʳ  = CZ • X ↑ • Z ↓
c10ˡ = CZ • H ↑ • CZ
c10ʳ = SH ↑ • CZ • (S • H • S) ↑ • S ↓ • ω⁻¹
c11ˡ = CZ • H ↓ • CZ
c11ʳ = SH ↓ • CZ • (S • H • S) ↓ • S ↑ • ω⁻¹

-- (d) width 3
c12ˡ c12ʳ c13ˡ c13ʳ c14ˡ c14ʳ c15ˡ c15ʳ : Circuit 3
c12ˡ = CZ ↑ • CZ
c12ʳ = CZ • CZ ↑
c13ˡ = ⊤⊥ ↑ • CZ ↓ • ⊥⊤ ↑
c13ʳ = ⊥⊤ ↓ • CZ ↑ • ⊤⊥ ↓
c14ˡ = (⊤⊥ ↑ • CZ ↓) ^ 3
c14ʳ = ε
c15ˡ = (⊥⊤ ↓ • CZ ↑) ^ 3
c15ʳ = ε

------------------------------------------------------------------------
-- The fifteen relations, as matrix identities

r1 : ⟦ c1ˡ ⟧M ≡ ⟦ c1ʳ ⟧M
r1 = Eq.refl

r2 : ⟦ c2ˡ ⟧M ≡ ⟦ c2ʳ ⟧M
r2 = Eq.refl

r3 : ⟦ c3ˡ ⟧M ≡ ⟦ c3ʳ ⟧M
r3 = Eq.refl

r4 : ⟦ c4ˡ ⟧M ≡ ⟦ c4ʳ ⟧M
r4 = Eq.refl

r5 : ⟦ c5ˡ ⟧M ≡ ⟦ c5ʳ ⟧M
r5 = Eq.refl

r6 : ⟦ c6ˡ ⟧M ≡ ⟦ c6ʳ ⟧M
r6 = Eq.refl

r7 : ⟦ c7ˡ ⟧M ≡ ⟦ c7ʳ ⟧M
r7 = Eq.refl

r8 : ⟦ c8ˡ ⟧M ≡ ⟦ c8ʳ ⟧M
r8 = Eq.refl

r9 : ⟦ c9ˡ ⟧M ≡ ⟦ c9ʳ ⟧M
r9 = Eq.refl

r10 : ⟦ c10ˡ ⟧M ≡ ⟦ c10ʳ ⟧M
r10 = Eq.refl

r11 : ⟦ c11ˡ ⟧M ≡ ⟦ c11ʳ ⟧M
r11 = Eq.refl

r12 : ⟦ c12ˡ ⟧M ≡ ⟦ c12ʳ ⟧M
r12 = Eq.refl

r13 : ⟦ c13ˡ ⟧M ≡ ⟦ c13ʳ ⟧M
r13 = Eq.refl

r14 : ⟦ c14ˡ ⟧M ≡ ⟦ c14ʳ ⟧M
r14 = Eq.refl

r15 : ⟦ c15ˡ ⟧M ≡ ⟦ c15ʳ ⟧M
r15 = Eq.refl
