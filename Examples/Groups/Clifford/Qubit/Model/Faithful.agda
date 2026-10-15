------------------------------------------------------------------------
-- Presentations of groups
--
-- ω has order 8 in Figure 8, at every width
--
-- Qubit.ExactExtension.ExactData is a one-field record: ω-faithful, the
-- statement that Figure 8 does not collapse the scalars.  Its two
-- companions are theorems (Selinger.Soundness.sound and
-- ExactExtension.scalars), and this one cannot join them by any
-- syntactic route:
--
--   * no abelian invariant reaches it — a homomorphism to ℤ/8 with
--     ω ↦ 1 would need 3(s + h) = 1 on the abelianisation, and C2 and C3
--     force 2h = 4s = 0, so 3(s + h) is never odd.  The same computation
--     kills the weaker ℤ/2-valued "global sign", ω⁴ ↦ 12(s + h) = 0;
--   * the P4-action is blind to it by construction (ExactExtension.
--     action-blind);
--   * and the coset route is circular, Reidemeister–Schreier's
--     left-embedding faithfulness being ω-faithful itself.
--
-- So it wants a MODEL, and the model is the defining representation,
-- reduced modulo 17: a Clifford operator on n qubits is a 2ⁿ × 2ⁿ matrix
-- over ℤ[1/√2, i], and over ℤ/17ℤ the constants i, √2 and ω all survive
-- as residues, ω becoming 2, whose order there is exactly 8.  The model
-- therefore still sees the scalar, which is the one thing asked of it.
--
-- This module is the soundness proof.  Model.Gates has already checked
-- the fifteen relations as matrix identities at widths 0 to 3; what is
-- left is
--
--   * to lift each of them to every width, which is Gates.localise: a
--     relator at width k + n is the relator at width k with idle wires
--     on top, so one matrix identity settles all widths at once;
--   * the structural rules, which are the tensor calculus of Model.Local
--     rather than computations — comm₁ and comm₂ are both the mixed
--     product law, cong↑ is functoriality of I₂ ⊗ −, and ω↑=ω is that a
--     scalar does not depend on the width (centrality of a scalar,
--     comm₀, is a theorem of these in Circuit.Base, so needs no case);
--   * and faithfulness itself, which is `log`: the eight powers of 2 in
--     ℤ/17ℤ are distinct, so the exponent can be read back off.
--
-- Nothing here is width-specific, so `exact-data` gives ExactData n for
-- every n, and Qubit.Presentation.presentation becomes unconditional.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.Model.Faithful where

open import Data.Bool using (Bool ; true ; false)
open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

-- Only the numerals ForStdlib.Data.Fin.Mod does not already re-export
-- (it gives ₀ to ₄); the rest name residues of 17 and exponents mod 8.
open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₅ ; ₆ ; ₇ ; ₈ ; ₉ ; ₁₃ ; ₁₅)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)

import Presentation.Base as PB

open import ForStdlib.Data.Fin.Mod.Prime.Two using (p-2 ; p-prime)

open import Examples.Groups.Clifford.Qubit.Model.Algebra
open import Examples.Groups.Clifford.Qubit.Model.Local
open import Examples.Groups.Clifford.Qubit.Model.Gates

import Examples.Groups.Clifford.Qubit.Selinger.Figure8 p-2 p-prime as F8
open F8
  using ( Gen ; Circuit ; gate₀ ; gate₁ ; gate₂ ; _↥ ; _↑ ; _≈ᶠ_
        ; ω-gate ; H-gate ; S-gate ; CZ-gate ; ω
        ; _CRel,_===_ ; srel ; cong↑ ; comm₁ ; comm₂ ; ω↑=ω
        ; c1 ; c2 ; c3 ; c4 ; c5 ; c6 ; c7 ; c8
        ; c9 ; c10 ; c11 ; c12 ; c13 ; c14 ; c15)

open import Circuit.Base F8.ExactGate using (_↓ᵏ_)

import Examples.Groups.Clifford.Qubit.ExactExtension as EE

private
  variable
    k n : ℕ

------------------------------------------------------------------------
-- Reading a relator at any width

private

  emb-≡ : {M N : Mat k} → M ≡ N → emb {k} {n} M ≐ emb N
  emb-≡ {M = M} Eq.refl = ≐-refl (emb M)

  -- One matrix identity, at every width: this is what makes the fifteen
  -- computations of Model.Gates enough.
  by-matrix : (u v : Circuit k) → ⟦ u ⟧M ≡ ⟦ v ⟧M →
              ⟦ u ↓ᵏ n ⟧ ≐ ⟦ v ↓ᵏ n ⟧
  by-matrix u v eq =
    ≐-trans (localise u) (≐-trans (emb-≡ eq) (≐-sym (localise v)))

  -- by-matrix with the relator as the axiom spells it.  Each clause of
  -- axiom-sound binds the axiom's own two words and passes them in, so
  -- the result has the expected type on the nose, and the respelling
  -- u ↓ᵏ n ≡ w is checked on words.  One lemma per arity, so that the
  -- width is the axiom's `₃₊ n` and not `3 + n`: two readings of a word
  -- that differ in that hidden width are compared as operators, a sum
  -- over every intermediate index (this module took 24 minutes so).
  by-matrix₀ : (u v : Circuit 0) → ⟦ u ⟧M ≡ ⟦ v ⟧M → (w w′ : Circuit n) →
               u ↓ᵏ n ≡ w → v ↓ᵏ n ≡ w′ → ⟦ w ⟧ ≐ ⟦ w′ ⟧
  by-matrix₀ {n} u v eq _ _ Eq.refl Eq.refl = by-matrix {n = n} u v eq

  by-matrix₁ : (u v : Circuit 1) → ⟦ u ⟧M ≡ ⟦ v ⟧M → (w w′ : Circuit (₁₊ n)) →
               u ↓ᵏ n ≡ w → v ↓ᵏ n ≡ w′ → ⟦ w ⟧ ≐ ⟦ w′ ⟧
  by-matrix₁ {n} u v eq _ _ Eq.refl Eq.refl = by-matrix {n = n} u v eq

  by-matrix₂ : (u v : Circuit 2) → ⟦ u ⟧M ≡ ⟦ v ⟧M → (w w′ : Circuit (₂₊ n)) →
               u ↓ᵏ n ≡ w → v ↓ᵏ n ≡ w′ → ⟦ w ⟧ ≐ ⟦ w′ ⟧
  by-matrix₂ {n} u v eq _ _ Eq.refl Eq.refl = by-matrix {n = n} u v eq

  by-matrix₃ : (u v : Circuit 3) → ⟦ u ⟧M ≡ ⟦ v ⟧M → (w w′ : Circuit (₃₊ n)) →
               u ↓ᵏ n ≡ w → v ↓ᵏ n ≡ w′ → ⟦ w ⟧ ≐ ⟦ w′ ⟧
  by-matrix₃ {n} u v eq _ _ Eq.refl Eq.refl = by-matrix {n = n} u v eq

  -- Shifting a circuit is tensoring with I₂ on the new wire.
  up-word : (w : Circuit n) → ⟦ w ↑ ⟧ ≐ up ⟦ w ⟧
  up-word [ g ]ʷ  = ≐-refl (up (valOp g))
  up-word ε       = ≐-sym up-Id
  up-word (w • v) =
    ≐-trans (⊙-cong (up-word w) (up-word v)) (up-⊙ ⟦ w ⟧ ⟦ v ⟧)

------------------------------------------------------------------------
-- Soundness of the axioms
--
-- The fifteen relators go through by-matrix; the structural rules are
-- the tensor lemmas of Model.Local.

axiom-sound : {w v : Circuit n} → n CRel, w === v → ⟦ w ⟧ ≐ ⟦ v ⟧
axiom-sound {w = w} {v} (srel c1)  = by-matrix₀ c1ˡ  c1ʳ  r1  w v Eq.refl Eq.refl
axiom-sound {w = w} {v} (srel c2)  = by-matrix₁ c2ˡ  c2ʳ  r2  w v Eq.refl Eq.refl
axiom-sound {w = w} {v} (srel c3)  = by-matrix₁ c3ˡ  c3ʳ  r3  w v Eq.refl Eq.refl
axiom-sound {w = w} {v} (srel c4)  = by-matrix₁ c4ˡ  c4ʳ  r4  w v Eq.refl Eq.refl
axiom-sound {w = w} {v} (srel c5)  = by-matrix₂ c5ˡ  c5ʳ  r5  w v Eq.refl Eq.refl
axiom-sound {w = w} {v} (srel c6)  = by-matrix₂ c6ˡ  c6ʳ  r6  w v Eq.refl Eq.refl
axiom-sound {w = w} {v} (srel c7)  = by-matrix₂ c7ˡ  c7ʳ  r7  w v Eq.refl Eq.refl
axiom-sound {w = w} {v} (srel c8)  = by-matrix₂ c8ˡ  c8ʳ  r8  w v Eq.refl Eq.refl
axiom-sound {w = w} {v} (srel c9)  = by-matrix₂ c9ˡ  c9ʳ  r9  w v Eq.refl Eq.refl
axiom-sound {w = w} {v} (srel c10) = by-matrix₂ c10ˡ c10ʳ r10 w v Eq.refl Eq.refl
axiom-sound {w = w} {v} (srel c11) = by-matrix₂ c11ˡ c11ʳ r11 w v Eq.refl Eq.refl
axiom-sound {w = w} {v} (srel c12) = by-matrix₃ c12ˡ c12ʳ r12 w v Eq.refl Eq.refl
axiom-sound {w = w} {v} (srel c13) = by-matrix₃ c13ˡ c13ʳ r13 w v Eq.refl Eq.refl
axiom-sound {w = w} {v} (srel c14) = by-matrix₃ c14ˡ c14ʳ r14 w v Eq.refl Eq.refl
axiom-sound {w = w} {v} (srel c15) = by-matrix₃ c15ˡ c15ʳ r15 w v Eq.refl Eq.refl

-- The derivation moves up a wire, and so does its operator.
axiom-sound (cong↑ {w = w} {v = v} r) =
  ≐-trans (up-word w)
          (≐-trans (up-cong (axiom-sound r)) (≐-sym (up-word v)))

-- comm₁ and comm₂ are both the mixed product law: a gate on the bottom
-- wires and an operator shifted past them are A ⊗ B either way round.
axiom-sound (comm₁ H-gate g) = ≐-sym (emb-up-comm hM (valOp g))
axiom-sound (comm₁ S-gate g) = ≐-sym (emb-up-comm sM (valOp g))
axiom-sound (comm₂ CZ-gate g) =
  ≐-trans (⊙-cong (up-up (valOp g)) (≐-refl (emb czM)))
    (≐-trans (≐-sym (emb-up-comm czM (valOp g)))
             (⊙-cong (≐-refl (emb czM)) (≐-sym (up-up (valOp g)))))

-- The scalar is the same on every wire.
axiom-sound (ω↑=ω ω-gate) = up-scal 2

------------------------------------------------------------------------
-- Soundness of the congruence

sound : {w v : Circuit n} → w ≈ᶠ v → ⟦ w ⟧ ≐ ⟦ v ⟧
sound PB.refl        = ≐-refl _
sound (PB.sym e)     = ≐-sym (sound e)
sound (PB.trans e f) = ≐-trans (sound e) (sound f)
sound (PB.cong e f)  = ⊙-cong (sound e) (sound f)
sound (PB.assoc {w = w} {v = v} {u = u}) = ⊙-assoc ⟦ w ⟧ ⟦ v ⟧ ⟦ u ⟧
sound (PB.left-unit {w = w})  = ⊙-identityˡ ⟦ w ⟧
sound (PB.right-unit {w = w}) = ⊙-identityʳ ⟦ w ⟧
sound (PB.axiom r)   = axiom-sound r

------------------------------------------------------------------------
-- ω has order 8
--
-- ⟦ ωᵏ ⟧ is the scalar 2ᵏ, and the eight powers of 2 in ℤ/17ℤ — 1, 2, 4,
-- 8, 16, 15, 13, 9 — are distinct.  Rather than compare them pairwise,
-- `log` reads the exponent back; the nine other residues are never
-- looked at.

private

  zeros : Bits n
  zeros {₀}    = []
  zeros {₁₊ n} = false ∷ zeros

  δb-refl : (x : Bits n) → δb x x ≡ 1
  δb-refl []           = Eq.refl
  δb-refl (true ∷ xs)  = δb-refl xs
  δb-refl (false ∷ xs) = δb-refl xs

  -- Two scalars that agree as operators agree as residues: read off the
  -- diagonal, where the delta is 1.
  scal-inj : {a b : 𝔽} → scal {n} a ≐ scal b → a ≡ b
  scal-inj {n} {a} {b} e =
    Eq.trans (Eq.sym (Eq.trans (Eq.cong (a *_) (δb-refl (zeros {n})))
                               (*-identityʳ a)))
      (Eq.trans (e zeros zeros)
                (Eq.trans (Eq.cong (b *_) (δb-refl (zeros {n})))
                          (*-identityʳ b)))

  pow-val : (j : ℕ) → ⟦ ω ^ j ⟧ ≐ scal {n} (2 ^′ j)
  pow-val ₀       = ≐-sym scal-1
  pow-val (₁₊ ₀)  = ≐-refl (scal 2)
  pow-val (₂₊ j)  =
    ≐-trans (⊙-cong (≐-refl (scal 2)) (pow-val (₁₊ j)))
            (scal-⊙ 2 (2 ^′ (₁₊ j)))

  -- The discrete logarithm of a power of 2, base 2.
  log : 𝔽 → ℤ 8
  log ₁         = ₀
  log ₂         = ₁
  log ₄         = ₂
  log ₈         = ₃
  log (₁₊ ₁₅)  = ₄
  log ₁₅        = ₅
  log ₁₃        = ₆
  log ₉         = ₇
  log _         = ₀

  log-pow : (j : ℤ 8) → log (2 ^′ toℕ j) ≡ j
  log-pow ₀ = Eq.refl
  log-pow ₁ = Eq.refl
  log-pow ₂ = Eq.refl
  log-pow ₃ = Eq.refl
  log-pow ₄ = Eq.refl
  log-pow ₅ = Eq.refl
  log-pow ₆ = Eq.refl
  log-pow ₇ = Eq.refl

ω-faithful : {j k : ℤ 8} → EE.scalar {n} j ≈ᶠ EE.scalar k → j ≡ k
ω-faithful {n} {j} {k} e =
  Eq.trans (Eq.sym (log-pow j))
    (Eq.trans (Eq.cong log
                (scal-inj {n} (≐-trans (≐-sym (pow-val (toℕ j)))
                                (≐-trans (sound e) (pow-val (toℕ k))))))
              (log-pow k))

------------------------------------------------------------------------
-- The ExactData, at every width

exact-data : (n : ℕ) → EE.ExactData n
exact-data n = record { ω-faithful = ω-faithful }
