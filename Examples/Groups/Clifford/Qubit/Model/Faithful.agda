------------------------------------------------------------------------
-- Presentations of groups
--
-- ω has order 8 in Figure 8, at widths 0 and 1
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
-- So it wants a MODEL, and this file builds one: the defining
-- representation, reduced modulo 17.  A Clifford operator on one qubit
-- is a 2 × 2 matrix over ℤ[1/√2, i]; over ℤ/17ℤ the constants i, √2 and
-- ω all survive as residues (Model.Mat2), ω becoming 2, whose order in
-- ℤ/17ℤ is exactly 8.  So the model still sees the scalar, which is the
-- one thing asked of it.
--
--     ω ↦ 2 · I         S ↦ diag(1 , i)         H ↦ (1/√2) [1  1 ]
--                                                          [1 −1 ]
--
-- Two widths are covered, which are the two where Figure 8 has no CZ:
--
--   width 0   the alphabet is the scalar alone (Gen 0 is the singleton
--             gate₀ ω-gate, gate₁ and gate₂ needing wires and _↥ a width
--             below), and the only axiom in scope is C1.  So width 0 is
--             ⟨ ω ∣ ω⁸ ⟩ ≅ ℤ/8 and the model is not really needed — but
--             it is what the width-1 cong↑ case recurses into, so it is
--             proved first and reused;
--
--   width 1   the alphabet adds H and S, and the axioms in scope are C1
--             to C4 — C5 to C15 all mention CZ, hence live at ₂₊ n or
--             above, and Agda discards them here by unification.
--
-- Width ≥ 2 is exactly what this file does not do: CZ is a 4 × 4 matrix,
-- so the model has to become 2ⁿ × 2ⁿ with Kronecker products, _↑ read as
-- I₂ ⊗ −, and comm₁ / comm₂ read as the mixed-product law.  That is the
-- rest of the same model, not a different one.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.Model.Faithful where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

import Presentation.Base as PB

open import ForStdlib.Data.Fin.Mod using (ℤ)
open import ForStdlib.Data.Fin.Mod.Prime.Two using (p-2 ; p-prime)

open import Examples.Groups.Clifford.Qubit.Model.Mat2
  using (𝔽 ; M2 ; ⟪_,_,_,_⟫ ; m₁₁ ; _⊙_ ; Id
        ; ⊙-assoc ; ⊙-identityˡ ; ⊙-identityʳ)

import Examples.Groups.Clifford.Qubit.Selinger.Figure8 p-2 p-prime as F8
open F8
  using ( Gen ; Circuit ; gate₀ ; gate₁ ; _↥ ; _↑ ; _≈ᶠ_
        ; ω-gate ; H-gate ; S-gate
        ; _CRel,_===_ ; srel ; cong↑ ; comm₀ ; comm₁ ; ω↑=ω
        ; c1 ; c2 ; c3 ; c4)

import Examples.Groups.Clifford.Qubit.ExactExtension as EE

------------------------------------------------------------------------
-- The gate matrices
--
-- Written with the Fin numerals rather than overloaded literals, so
-- that nothing here depends on the Number instances.  In ℤ/17ℤ the
-- constants are i = 4, √2 = 11 and 1/√2 = 14, and −14 = 3.

-- ω · I, the scalar.  ω = 2 has order exactly 8, since 2⁴ = 16 = −1.
Ω : M2
Ω = ⟪ ₂ , ₀ , ₀ , ₂ ⟫

-- diag(1 , i).
S₂ : M2
S₂ = ⟪ ₁ , ₀ , ₀ , ₄ ⟫

-- (1/√2) · [[1 , 1] , [1 , −1]].
H₂ : M2
H₂ = ⟪ ₁₄ , ₁₄ , ₁₄ , ₃ ⟫

------------------------------------------------------------------------
-- The interpretation
--
-- A generator goes to its matrix and a circuit to the product, ε to the
-- identity.  At width 1 a shifted generator is one of width 0 — the
-- scalar, which is the same matrix there — so the two levels agree on
-- shifts, which is what lift-⟦⟧ below records.

val₀ : Gen 0 → M2
val₀ (gate₀ ω-gate) = Ω

val₁ : Gen 1 → M2
val₁ (gate₀ ω-gate) = Ω
val₁ (gate₁ H-gate) = H₂
val₁ (gate₁ S-gate) = S₂
val₁ (g ↥)          = val₀ g

⟦_⟧₀ : Circuit 0 → M2
⟦ [ g ]ʷ ⟧₀ = val₀ g
⟦ ε ⟧₀      = Id
⟦ w • v ⟧₀  = ⟦ w ⟧₀ ⊙ ⟦ v ⟧₀

⟦_⟧₁ : Circuit 1 → M2
⟦ [ g ]ʷ ⟧₁ = val₁ g
⟦ ε ⟧₁      = Id
⟦ w • v ⟧₁  = ⟦ w ⟧₁ ⊙ ⟦ v ⟧₁

------------------------------------------------------------------------
-- Soundness at width 0
--
-- The alphabet is the scalar alone, so C1 (ω⁸ = ε, i.e. 2⁸ = 1 in
-- ℤ/17ℤ) and one instance of comm₀ are the whole axiom list: cong↑ and
-- ω↑=ω conclude at ₁₊ n and comm₁ / comm₂ at ₁₊ n / ₂₊ n, so Agda has
-- nothing to ask for at width 0.

ax₀ : {w v : Circuit 0} → 0 CRel, w === v → ⟦ w ⟧₀ ≡ ⟦ v ⟧₀
ax₀ (srel c1)                     = Eq.refl
ax₀ (comm₀ ω-gate (gate₀ ω-gate)) = Eq.refl

sound₀ : {w v : Circuit 0} → w ≈ᶠ v → ⟦ w ⟧₀ ≡ ⟦ v ⟧₀
-- The matrices are a record type, so a metavariable of matrix type
-- eta-expands and the product then reduces on its entries; the three
-- monoid-law cases therefore name their words rather than leaving the
-- arguments of ⊙-assoc and friends to be inferred.
sound₀ PB.refl        = Eq.refl
sound₀ (PB.sym e)     = Eq.sym (sound₀ e)
sound₀ (PB.trans e f) = Eq.trans (sound₀ e) (sound₀ f)
sound₀ (PB.cong e f)  = Eq.cong₂ _⊙_ (sound₀ e) (sound₀ f)
sound₀ (PB.assoc {w = w} {v = v} {u = u}) =
  ⊙-assoc ⟦ w ⟧₀ ⟦ v ⟧₀ ⟦ u ⟧₀
sound₀ (PB.left-unit {w = w})  = ⊙-identityˡ ⟦ w ⟧₀
sound₀ (PB.right-unit {w = w}) = ⊙-identityʳ ⟦ w ⟧₀
sound₀ (PB.axiom r)   = ax₀ r

------------------------------------------------------------------------
-- Soundness at width 1
--
-- C1–C4 hold in the model by computation, which is the whole content of
-- the choice of residues: 2⁸ = 1, H² = I, S⁴ = I, and (SH)³ = 2 · I,
-- that last being C4, the relation that names the scalar.  The
-- structural rules are equally computational — comm₀ and comm₁ hold
-- because 2 · I is central, and ω↑=ω because val₁ reads a shifted
-- scalar as val₀ does.

-- A shifted circuit reads the same at either width.
lift-⟦⟧ : (w : Circuit 0) → ⟦ w ↑ ⟧₁ ≡ ⟦ w ⟧₀
lift-⟦⟧ [ g ]ʷ  = Eq.refl
lift-⟦⟧ ε       = Eq.refl
lift-⟦⟧ (w • v) = Eq.cong₂ _⊙_ (lift-⟦⟧ w) (lift-⟦⟧ v)

ax₁ : {w v : Circuit 1} → 1 CRel, w === v → ⟦ w ⟧₁ ≡ ⟦ v ⟧₁
ax₁ (srel c1) = Eq.refl
ax₁ (srel c2) = Eq.refl
ax₁ (srel c3) = Eq.refl
ax₁ (srel c4) = Eq.refl
ax₁ (cong↑ {w = w} {v = v} r) =
  Eq.trans (lift-⟦⟧ w) (Eq.trans (ax₀ r) (Eq.sym (lift-⟦⟧ v)))
ax₁ (comm₀ ω-gate (gate₀ ω-gate))  = Eq.refl
ax₁ (comm₀ ω-gate (gate₁ H-gate))  = Eq.refl
ax₁ (comm₀ ω-gate (gate₁ S-gate))  = Eq.refl
ax₁ (comm₀ ω-gate (gate₀ ω-gate ↥)) = Eq.refl
ax₁ (comm₁ H-gate (gate₀ ω-gate))  = Eq.refl
ax₁ (comm₁ S-gate (gate₀ ω-gate))  = Eq.refl
ax₁ (ω↑=ω ω-gate)                  = Eq.refl

sound₁ : {w v : Circuit 1} → w ≈ᶠ v → ⟦ w ⟧₁ ≡ ⟦ v ⟧₁
sound₁ PB.refl        = Eq.refl
sound₁ (PB.sym e)     = Eq.sym (sound₁ e)
sound₁ (PB.trans e f) = Eq.trans (sound₁ e) (sound₁ f)
sound₁ (PB.cong e f)  = Eq.cong₂ _⊙_ (sound₁ e) (sound₁ f)
sound₁ (PB.assoc {w = w} {v = v} {u = u}) =
  ⊙-assoc ⟦ w ⟧₁ ⟦ v ⟧₁ ⟦ u ⟧₁
sound₁ (PB.left-unit {w = w})  = ⊙-identityˡ ⟦ w ⟧₁
sound₁ (PB.right-unit {w = w}) = ⊙-identityʳ ⟦ w ⟧₁
sound₁ (PB.axiom r)   = ax₁ r

------------------------------------------------------------------------
-- ω has order 8
--
-- The eight powers of 2 in ℤ/17ℤ are 1, 2, 4, 8, 16, 15, 13, 9 — all
-- distinct, which is the order-8 statement.  Rather than compare them
-- pairwise (64 cases), invert: `log` is a left inverse of k ↦ 2ᵏ on
-- those eight residues, so it recovers the exponent from the top-left
-- entry of the interpreted scalar word, and faithfulness is a
-- congruence.  The value on the other nine residues is never looked at.

log : 𝔽 → ℤ 8
log ₁        = ₀
log ₂        = ₁
log ₄        = ₂
log ₈        = ₃
log (₁₊ ₁₅) = ₄
log ₁₅       = ₅
log ₁₃       = ₆
log ₉        = ₇
log _        = ₀

-- ωᵏ is read as the matrix 2ᵏ · I, whose top-left entry logs back to k.
scalar-log₀ : (j : ℤ 8) → log (m₁₁ ⟦ EE.scalar {0} j ⟧₀) ≡ j
scalar-log₀ ₀ = Eq.refl
scalar-log₀ ₁ = Eq.refl
scalar-log₀ ₂ = Eq.refl
scalar-log₀ ₃ = Eq.refl
scalar-log₀ ₄ = Eq.refl
scalar-log₀ ₅ = Eq.refl
scalar-log₀ ₆ = Eq.refl
scalar-log₀ ₇ = Eq.refl

scalar-log₁ : (j : ℤ 8) → log (m₁₁ ⟦ EE.scalar {1} j ⟧₁) ≡ j
scalar-log₁ ₀ = Eq.refl
scalar-log₁ ₁ = Eq.refl
scalar-log₁ ₂ = Eq.refl
scalar-log₁ ₃ = Eq.refl
scalar-log₁ ₄ = Eq.refl
scalar-log₁ ₅ = Eq.refl
scalar-log₁ ₆ = Eq.refl
scalar-log₁ ₇ = Eq.refl

ω-faithful₀ : {j k : ℤ 8} → EE.scalar {0} j ≈ᶠ EE.scalar k → j ≡ k
ω-faithful₀ {j} {k} e =
  Eq.trans (Eq.sym (scalar-log₀ j))
    (Eq.trans (Eq.cong (λ M → log (m₁₁ M)) (sound₀ e)) (scalar-log₀ k))

ω-faithful₁ : {j k : ℤ 8} → EE.scalar {1} j ≈ᶠ EE.scalar k → j ≡ k
ω-faithful₁ {j} {k} e =
  Eq.trans (Eq.sym (scalar-log₁ j))
    (Eq.trans (Eq.cong (λ M → log (m₁₁ M)) (sound₁ e)) (scalar-log₁ k))

------------------------------------------------------------------------
-- The ExactData of the two widths

exact-data₀ : EE.ExactData 0
exact-data₀ = record { ω-faithful = ω-faithful₀ }

exact-data₁ : EE.ExactData 1
exact-data₁ = record { ω-faithful = ω-faithful₁ }
