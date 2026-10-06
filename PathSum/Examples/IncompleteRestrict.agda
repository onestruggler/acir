------------------------------------------------------------------------
-- Presentations of groups
--
-- Section 4's irreducible identity under the isometry restriction of
-- section 4.1
--
-- PathSum.Examples.Incomplete formalises the witness of section 4 of
-- Amy's QPL 2018 paper: the two-qubit Clifford+T identity SB (over
-- {H, X, CNOT, T, T†}, PathSum.CRK.WithX) whose path-sum, with eight
-- path variables, is irreducible under all of figure 2.  It leaves
-- open what the heuristic of section 4.1 -- restrict to the paths
-- with f(x, y) = x, reifying the restriction by substitution -- does
-- for it.  This module answers, at the examples' precision M₀ = 0.
--
-- * The restriction step.  The outputs of ⟦ SB ⟧ are x1 and y8 (the
--   last Hadamard's variable), so section 4.1 substitutes y8 ← x2 and
--   removes y8: one step of PathSum.Gauss's elimination, a restriction
--   step in the sense of PathSum.Restrict (SB-restricts, by
--   PathSum.Restrict.Linear.gauss-restricts), and coefficient by
--   coefficient PathSum.Restrict.Pivot's substitution itself
--   (ρ-is-substitution: the output y8 has a pivot, and the reduct of a
--   step is unique).  What it leaves, ρ, has
--   seven path variables, and its phase is, coefficient by coefficient
--   modulo 1, the paper's P with y8 replaced by x2 (ρ-printed: the
--   terms 4y7y8 and 7y8 become 4x2y7 and 7x2, the latter cancelling
--   the x2 already there modulo 1).
--
-- * What it buys.  Every output of ρ reads its input on every path
--   (ρ-solved): the restriction is reified completely, nothing is
--   "ignored".  ⟦ SB ⟧ is well formed (PathSum.CRK.WithX.WellFormed),
--   so by lemma 4.1 along the step it is the identity exactly when ρ is
--   (SB⇔ρ, PathSum.Restrict.restriction-solved), and ρ is the identity
--   (ρ-id).  One path variable fewer, and a diagonal path-sum -- but
--   no rule of figure 2 applies to ρ either, at any variable or pair
--   (ρ-irreducible, PathSum.Full.Obstruction's certificate read off
--   the cheap copy of the phase, PathSum.Gauss.Single).
--
-- * Nothing else helps (SB-stuck-restricted): no chain of restriction
--   steps and rules of figure 2, in any order, at any wires and path
--   variables, takes ⟦ SB ⟧ to a path-sum without path variables.  No
--   rule applies to ⟦ SB ⟧ (Incomplete.SB-irreducible); a restriction
--   step can only be the one above (x1 is solved and the other wire
--   reads y8 alone), whose reduct is unique coefficient by coefficient
--   (PathSum.Restrict.Pivot.restricts-unique), so every such reduct is
--   irreducible and solved, and from there nothing moves
--   (PathSum.Restrict.Stuck).  So for this identity the verdict of
--   section 4.1 is still never syntactic: it needs the expansion the
--   paper proposes (here, ρ-id comes from the 4×4 matrix of SB, through
--   SB⇔ρ).
--
-- Every fact is first proved of ξ₀, the path-sum of SB's
-- interpretation state, and carried to ⟦ SB ⟧ by SB-state (the two are
-- the same term); the instances are PathSum.Examples.Incomplete's (I.CX,
-- I.D).  Two lemmas are stated for every circuit and only then applied
-- to SB: that the state's path-sum is the circuit's (⟦⟧ᵉ-state), and
-- lemma 4.1 along a solved chain (solved-⇔).  Applied to the closed SB
-- directly, the well-formedness lemma's type names ⟦ SB ⟧ through
-- another instance of PathSum.CRK.WithX, and Agda matched the two by
-- unfolding the amplitudes: a first version of this module did not
-- finish in 15 minutes; as written it checks in under a minute.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Examples.IncompleteRestrict where

open import Data.Fin using (#_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Integer.Base using (+_; _-_)
open import Data.Integer.Divisibility.Signed using (_∣_)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_; _,_; proj₂)
open import Data.Unit.Base using (tt)
open import Function.Bundles using (_⇔_; Equivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary.Decidable using (toWitness)
open import Relation.Nullary.Negation using (¬_; contradiction)

open import PathSum.Base using (PathSum; ⟨_,_⟩; phase; out; idPS)
open import PathSum.Examples.Base using (_⋆_)
open import PathSum.Full.Match 3 using (Irreducibleᶠ)
open import PathSum.Linear using (varᴸ; valᴸ; valᴸ-var)
open import PathSum.Order 3 using (pow)
open import PathSum.Polynomial using
  (Poly; Mon; 1ᵐ; μ; x[_]; y[_]; ⟪_⟫; _∪ᵐ_; _+ᴾ_; _≈[_]_)
open import PathSum.Polynomial.Decidable using (_≈?[_]_)

import PathSum.Congruence as Cg
import PathSum.CRK.Amp as Am
import PathSum.CRK.Circuit as KC
import PathSum.CRK.WithX.WellFormed as XW
import PathSum.Examples.Incomplete as I
import PathSum.Full.Obstruction as Ob
import PathSum.Gauss as G
import PathSum.Gauss.Single as GS
import PathSum.Restrict as R
import PathSum.Restrict.Linear as RL
import PathSum.Restrict.Pivot as P
import PathSum.Restrict.Stuck as St

open I.D using (_≋_)


------------------------------------------------------------------------
-- The circuit's state and the restriction step

-- The wires: x1 is solved, the second wire reads y8.

w₁ w₂ : Fin 2
w₁ = zero
w₂ = suc zero

-- A circuit's interpretation state and its path-sum, at a number of
-- path variables given by an equation, and the fact that the path-sum
-- is the state's -- proved for every circuit, so that at SB it is
-- never checked by computing the two sides (comparing the closed
-- path-sum with the closed state's unfolds both phases, which ran for
-- over ten minutes).

private
  variable
    n m : ℕ

stᵉ : (C : I.CX.Circuit n) → I.CX.paths C ≡ m → KC.State 3 n m
stᵉ {n} C e = subst (KC.State 3 n) e (proj₂ (I.CX.run C (KC.init 3)))

⟦_⟧ᵉ : (C : I.CX.Circuit n) → I.CX.paths C ≡ m → PathSum n (I.CX.norm C) m
⟦_⟧ᵉ {n} C e = subst (PathSum n (I.CX.norm C)) e I.CX.⟦ C ⟧

⟦⟧ᵉ-state : (C : I.CX.Circuit n) (e : I.CX.paths C ≡ m) →
            ⟦ C ⟧ᵉ e ≡ Am.toPS 0 (stᵉ C e)
⟦⟧ᵉ-state C refl = refl

-- SB's state, its eight path variables newest first (the paper's y8 is
-- the variable zero), and its path-sum, which is ⟦ SB ⟧ itself.

e₈ : I.CX.paths I.SB ≡ 8
e₈ = refl

st : KC.State 3 2 8
st = stᵉ I.SB e₈

ξ₀ : PathSum 2 (I.CX.norm I.SB) 8
ξ₀ = Am.toPS 0 st

SB-state : I.CX.⟦ I.SB ⟧ ≡ ξ₀
SB-state = ⟦⟧ᵉ-state I.SB e₈

-- One elimination step at the second wire and y8, i.e. y8 ← x2.

ρ : PathSum 2 (I.CX.norm I.SB) 7
ρ = Am.toPS 0 (G.step 0 st w₂ zero)

private
  r₀ : R.Restricts 0 ξ₀ w₂ zero ρ
  r₀ = RL.gauss-restricts 0 {k = I.CX.norm I.SB} st w₂ zero refl

SB-restricts : R.Restricts 0 I.CX.⟦ I.SB ⟧ w₂ zero ρ
SB-restricts = subst (λ ξ → R.Restricts 0 ξ w₂ zero ρ) (sym SB-state) r₀

SB-chain : R._⇝*_ 0 I.CX.⟦ I.SB ⟧ ρ
SB-chain = R.restrict (R.step w₂ zero SB-restricts) R.◅⇝ R.ε⇝

-- The second wire's output is y8 ⊕ Q with Q = 0, so the step is
-- section 4.1's substitution: ρ is PathSum.Restrict.Pivot's restrictᴾ,
-- coefficient by coefficient (the reduct of a step is unique).

ρ-is-substitution :
  phase ρ ≈[ pow 3 ] phase (P.restrictᴾ 0 ξ₀ w₂ zero) ×
  (∀ v → out ρ v ≈[ + 2 ] out (P.restrictᴾ 0 ξ₀ w₂ zero) v)
ρ-is-substitution =
  P.restricts≈restrictᴾ 0 {ξ = ξ₀} {w = w₂} {j = zero} {ρ = ρ} piv r₀
  where
  piv : P.Pivot 0 ξ₀ w₂ zero
  piv = toWitness {a? = P.pivot? 0 ξ₀ w₂ zero} tt


------------------------------------------------------------------------
-- The outputs

-- Before the step: x1 on the first wire, y8 on the second.  After it:
-- the inputs.

private
  sig₀ : KC.sig st w₁ ≡ varᴸ x[ w₁ ]
  sig₀ = refl

  sig₂ : KC.sig st w₂ ≡ varᴸ y[ zero ]
  sig₂ = refl

  sig-step : ∀ w → KC.sig (G.step 0 st w₂ zero) w ≡ varᴸ x[ w ]
  sig-step zero       = refl
  sig-step (suc zero) = refl

-- Wire x1 of ξ₀ is solved; its second wire reads y8.

ξ₀-solved₁ : R.Solved 0 ξ₀ w₁
ξ₀-solved₁ x y =
  trans (Am.outBit-liftᴸ 0 ξ₀ x y w₁ (KC.sig st w₁) refl)
        (trans (cong (λ l → valᴸ l x y) sig₀) (valᴸ-var x[ w₁ ] x y))

ξ₀-reads : ∀ x y → I.D.outBit ξ₀ x y w₂ ≡ y zero
ξ₀-reads x y =
  trans (Am.outBit-liftᴸ 0 ξ₀ x y w₂ (KC.sig st w₂) refl)
        (trans (cong (λ l → valᴸ l x y) sig₂) (valᴸ-var y[ zero ] x y))

-- Every output of ρ is solved: the restriction is reified completely.

ρ-solved : ∀ w → R.Solved 0 ρ w
ρ-solved w x g =
  trans (Am.outBit-liftᴸ 0 ρ x g w (KC.sig (G.step 0 st w₂ zero) w) refl)
        (trans (cong (λ l → valᴸ l x g) (sig-step w)) (valᴸ-var x[ w ] x g))


------------------------------------------------------------------------
-- No rule applies to the restriction

-- The step solves y8 = x2, so its phase is read cheaply
-- (PathSum.Gauss.Single.fast-step), and the certificate is computed on
-- that copy at the input x1.

private
  sol-x : G.sol 0 st w₂ zero ≡ varᴸ x[ w₂ ]
  sol-x = refl

  fast : PathSum 2 0 7
  fast = GS.fast-step 0 {k = 0} st w₂ zero

  fast≗ρ : ∀ γ → phase ρ γ ≡ phase fast γ
  fast≗ρ = GS.step-phase 0 {k = I.CX.norm I.SB} {k′ = 0} st w₂ zero sol-x

  fast-obstructed : Ob.Obstructed 3 w₁ fast
  fast-obstructed = toWitness {a? = Ob.obstructed? 3 w₁ fast} tt

ρ-obstructed : Ob.Obstructed 3 w₁ ρ
ρ-obstructed = GS.Obstructed-≗ 0 w₁ ρ fast fast≗ρ fast-obstructed

ρ-irreducible : Irreducibleᶠ ρ
ρ-irreducible = Ob.obstructed⇒irreducible 3 w₁ ρ ρ-obstructed


------------------------------------------------------------------------
-- The restriction, as printed

-- The paper's P with y8 ← x2, its y1 … y7 being ρ's path variables
-- 6 … 0.

X₁ X₂ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : Mon 2 7
X₁ = ⟪ x[ w₁ ] ⟫
X₂ = ⟪ x[ w₂ ] ⟫
y₁ = ⟪ y[ # 6 ] ⟫
y₂ = ⟪ y[ # 5 ] ⟫
y₃ = ⟪ y[ # 4 ] ⟫
y₄ = ⟪ y[ # 3 ] ⟫
y₅ = ⟪ y[ # 2 ] ⟫
y₆ = ⟪ y[ # 1 ] ⟫
y₇ = ⟪ y[ # 0 ] ⟫

Pᴿ : Poly 2 7
Pᴿ =
  (+ 2) ⋆ 1ᵐ +ᴾ (+ 6) ⋆ (X₁ ∪ᵐ X₂) +ᴾ (+ 1) ⋆ X₂ +ᴾ
  (+ 1) ⋆ y₁ +ᴾ (+ 4) ⋆ (y₁ ∪ᵐ X₁) +ᴾ (+ 4) ⋆ (y₁ ∪ᵐ X₂) +ᴾ
  (+ 4) ⋆ (y₁ ∪ᵐ y₂) +ᴾ
  (+ 6) ⋆ y₂ +ᴾ (+ 4) ⋆ (y₂ ∪ᵐ y₃) +ᴾ (+ 2) ⋆ (y₂ ∪ᵐ X₁) +ᴾ
  (+ 3) ⋆ y₃ +ᴾ (+ 4) ⋆ (y₃ ∪ᵐ X₁) +ᴾ (+ 4) ⋆ (y₃ ∪ᵐ y₄) +ᴾ
  (+ 4) ⋆ (y₄ ∪ᵐ y₅) +ᴾ (+ 6) ⋆ (y₄ ∪ᵐ X₁) +ᴾ
  (+ 1) ⋆ y₅ +ᴾ (+ 4) ⋆ (y₅ ∪ᵐ X₁) +ᴾ (+ 4) ⋆ (y₅ ∪ᵐ y₆) +ᴾ
  (+ 6) ⋆ y₆ +ᴾ (+ 4) ⋆ (y₆ ∪ᵐ y₇) +ᴾ (+ 2) ⋆ (y₆ ∪ᵐ X₁) +ᴾ
  (+ 3) ⋆ y₇ +ᴾ (+ 4) ⋆ (y₇ ∪ᵐ X₁) +ᴾ (+ 4) ⋆ (y₇ ∪ᵐ X₂) +ᴾ
  (+ 7) ⋆ X₂

ρᴾ : PathSum 2 8 7
ρᴾ = ⟨ Pᴿ , (λ w → μ x[ w ]) ⟩

-- Coefficient by coefficient: the outputs modulo 2, from the forms;
-- the phase modulo 1, through the cheap copy.

private
  outs-printed : ∀ w → out ρ w ≈[ + 2 ] μ x[ w ]
  outs-printed zero       =
    toWitness {a? = out ρ zero ≈?[ + 2 ] μ x[ zero ]} tt
  outs-printed (suc zero) =
    toWitness {a? = out ρ (suc zero) ≈?[ + 2 ] μ x[ suc zero ]} tt

  fast-printed : phase fast ≈[ pow 3 ] Pᴿ
  fast-printed = toWitness {a? = phase fast ≈?[ pow 3 ] Pᴿ} tt

ρ-printed : Cg.Congruent 0 ρ ρᴾ
ρ-printed = outs-printed , λ γ →
  subst (λ a → pow 3 ∣ (a - Pᴿ γ)) (sym (fast≗ρ γ)) (fast-printed γ)


------------------------------------------------------------------------
-- What the restriction buys

-- Lemma 4.1 along a chain ending with every output solved, for any
-- circuit over {H, X, CNOT, R_k, R_k†}.  (Stated for every circuit: at
-- the closed SB, the well-formedness lemma's type names the circuit's
-- path-sum through another instance of the module, and Agda matched
-- the two by unfolding the amplitudes -- over fifteen minutes.)

solved-⇔ : (C : I.CX.Circuit n) {k′ m′ : ℕ} (ρ′ : PathSum n k′ m′) →
           R._⇝*_ 0 I.CX.⟦ C ⟧ ρ′ → (∀ w → R.Solved 0 ρ′ w) →
           (I.CX.⟦ C ⟧ ≋ idPS) ⇔ (ρ′ ≋ idPS)
solved-⇔ C ρ′ chain solved =
  R.restriction-solved 0 I.CX.⟦ C ⟧ ρ′ (XW.circuit-WellFormed 0 C)
    chain solved

-- Lemma 4.1 along the step: SB is the identity exactly when ρ is.

SB⇔ρ : (I.CX.⟦ I.SB ⟧ ≋ idPS) ⇔ (ρ ≋ idPS)
SB⇔ρ = solved-⇔ I.SB ρ SB-chain ρ-solved

-- And it is: ρ is an irreducible identity with seven path variables.

ρ-id : ρ ≋ idPS
ρ-id = Equivalence.to SB⇔ρ I.SB-id

restriction-SB :
  R.Restricts 0 I.CX.⟦ I.SB ⟧ w₂ zero ρ × (∀ w → R.Solved 0 ρ w) ×
  Irreducibleᶠ ρ × ρ ≋ idPS
restriction-SB = SB-restricts , ρ-solved , ρ-irreducible , ρ-id


------------------------------------------------------------------------
-- No chain of restriction steps and rules reaches a path-sum without
-- path variables

private
  -- A restriction step from ξ₀ is at the second wire and y8.

  others : ∀ v → v ≢ w₂ → R.Solved 0 ξ₀ v
  others zero       _  = ξ₀-solved₁
  others (suc zero) ne = contradiction refl ne

  ξ₀-irreducible : Irreducibleᶠ ξ₀
  ξ₀-irreducible = subst Irreducibleᶠ SB-state I.SB-irreducible

  ξ₀-stuck : ∀ {k′} {ζ : PathSum 2 k′ 0} → ¬ (R._⇝*_ 0 ξ₀ ζ)
  ξ₀-stuck = St.stuck-after-one 0 ξ₀ ξ₀-irreducible
    (St.any-step-dead 0 ξ₀ w₂ others ξ₀-reads r₀ w₁ ρ-obstructed ρ-solved)

SB-stuck-restricted : ∀ {k′} {ζ : PathSum 2 k′ 0} →
                      ¬ (R._⇝*_ 0 I.CX.⟦ I.SB ⟧ ζ)
SB-stuck-restricted {ζ = ζ} =
  subst (λ ξ → ¬ (R._⇝*_ 0 ξ ζ)) (sym SB-state) ξ₀-stuck
