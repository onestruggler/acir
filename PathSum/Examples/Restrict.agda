------------------------------------------------------------------------
-- Presentations of groups
--
-- Section 4.1's isometry restriction on closed examples: a
-- specification miter, and circuits with X gates
--
-- All at the examples' precision M₀ = 0 (eighths: ½ is 4, T is 1).
--
-- * The seven-T Toffoli gate against its specification
--   (toffoli-by-restriction).  C is PathSum.Toffoli.Gate's tof on
--   wires 0, 1, 2 and spec the classical path-sum
--   |x₁x₂x₃⟩ ↦ |x₁x₂(x₃ ⊕ x₁x₂)⟩ (toffoliˢ), whose output on the
--   target is the lift x₃ + x₁x₂ − 2x₁x₂x₃.  The miter of section 3,
--   ⟦ C† ⟧ ∘ᴾ spec, is a composite (definition 2.6), not a circuit, so
--   PathSum.Gauss does not apply to it, and its polynomials are built
--   by substitution and never computed.  Its outputs read x₁, x₂ and
--   the last Hadamard's variable y₀; the non-linear x₁x₂ of the
--   specification has gone into the phase, through the first
--   Hadamard of C† on the target.  One restriction step solves the
--   target, y₀ ← x₃ (keep), checked by PathSum.Restrict.Spec's
--   restricts-after on ⟦ C† ⟧'s values at the inputs the specification
--   sends x to: the outputs symbolically, the phase at the 16 points
--   (x, y₁) by computation (phase-vanishes).  The reduct ρ₁ has one
--   path variable, the identity's outputs and the phase 0 modulo 1:
--   ½y₁(x₃ ⊕ x₁x₂) − ½x₁x₂y₁ + ½y₁y₀ at y₀ = x₃ is y₁x₃ − y₁x₁x₂x₃.
--   [Elim] removes y₁, what is left is the identity, and by lemma 4.1
--   at the well-formed miter ⟦ C ⟧ ≋ spec.  That is section 5.2's
--   route -- restriction, reduction, the syntactic test -- carried
--   out on a miter the paper does not print.
--
-- * A circuit over {H, X, CNOT, R_k} with an affine output
--   (HZHX-by-restriction): H; Z; H; X on one qubit (Z = R_1), the
--   identity since H Z H = X.  Its output is 1 ⊕ y₀, so the
--   restriction substitutes y₀ ← ¬x (Q = 1, an affine constant), after
--   which the phase ½xy₁ + ½y₁ + ½y₁y₀ is y₁ ≡ 0 modulo 1, and [Elim]
--   leaves the identity.  Well-formedness is PathSum.CRK.WithX.
--   WellFormed's circuit-WellFormed.
--
-- * Refutations.  H; X; H is Z, not the identity: restricted at y₀ ← x
--   its phase is ½x, which [Elim] keeps and the syntactic test rejects
--   (HXH-not-id).  X alone has the output 1 ⊕ x, free of path
--   variables and not x: the refutation rule applies with no step
--   (X-not-id).
--
-- The reducts are written out (ρ₁, ρ₃, ρ₅) and checked against the
-- semantic conditions of a restriction step (PathSum.Restrict's
-- Restricts); computing the paper's substitution itself is out of reach
-- (it lifts and multiplies dense polynomials).  That a reduct checked
-- this way is the paper's substitution, coefficient by coefficient,
-- is PathSum.Restrict.Pivot.restricts-unique, which needs a Pivot at
-- the step: it is instantiated in PathSum.Examples.Restrict.NonLinear
-- (restricts₂-is-substitution), not for ρ₁, ρ₃ and ρ₅ here.  Every closed verdict goes through a lemma stated for
-- an arbitrary circuit (by-restriction, withX-by-restriction,
-- withX-refuted, withX-refuted-out), so that the module's instances of
-- the denotation and of the gate sets meet those of the lemmas only at
-- variables (CLAUDE.md, closed circuits).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Examples.Restrict where

open import Data.Bool.Base using (Bool; true; false; not; _xor_; _∧_)
open import Data.Bool.Properties using (not-involutive)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Subset.Properties using (∉⊥)
open import Data.Integer.Base using (ℤ; 0ℤ; +_; -_; _+_; _-_)
open import Data.Integer.Divisibility.Signed using (_∣_; _∣?_; ∣m⇒∣-m)
open import Data.Integer.Properties using (+-identityˡ)
open import Data.List.Base using ([]; _∷_)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Product.Base using (_×_; _,_; proj₂)
open import Data.Unit.Base using (tt)
open import Function.Bundles using (Equivalence)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (toWitness)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Assign using (_[_≔_]; ≔-there; ≔-cong)
open import PathSum.Base using (PathSum; ⟨_,_⟩; phase; out; idPS; head-part)
open import PathSum.Compose using (_∘ᴾ_)
open import PathSum.Examples.Base using (_⋆_; x₁)
open import PathSum.Linear using (valᴸ; varᴸ; liftᴸ; valᴸ-var)
open import PathSum.Order 3 using (pow)
open import PathSum.Polynomial using
  (Poly; Var; μ; x[_]; y[_]; 0ᴾ; eval; _≈[_]_; NoVar)
open import PathSum.Polynomial.Decidable using
  (all-points?; by-eval; refute-by-eval)
open import PathSum.Polynomial.Product using (eval-0ᴾ)
open import PathSum.Polynomial.Properties using (eval-cong; valᵛ; i∣0)
open import PathSum.Polynomial.Substitution using (Absent-μ; Absent⇒NoVar)
open import PathSum.Reorder using (insertᵃ)

import PathSum.Classical
import PathSum.CRK.Adjoint
import PathSum.CRK.Amp
import PathSum.CRK.Circuit
import PathSum.CRK.WithX
import PathSum.CRK.WithX.WellFormed
import PathSum.Denotation
import PathSum.Full
import PathSum.Reduction
import PathSum.Restrict
import PathSum.Restrict.Pivot
import PathSum.Restrict.Spec
import PathSum.Toffoli.Gate

-- The instances every statement below is made with.

module D   = PathSum.Denotation 0
module R   = PathSum.Restrict 0
module P   = PathSum.Restrict.Pivot 0
module S   = PathSum.Restrict.Spec 0
module K   = PathSum.CRK.Circuit 3
module KA  = PathSum.CRK.Adjoint 3
module Am  = PathSum.CRK.Amp 0
module TG  = PathSum.Toffoli.Gate 0
module CL  = PathSum.Classical 0
module Rd  = PathSum.Reduction 3
module F   = PathSum.Full 3
module CX  = PathSum.CRK.WithX 0
module CXW = PathSum.CRK.WithX.WellFormed 0

open D using (Assign; outBit; _≋_)

private
  variable
    n k′ : ℕ


------------------------------------------------------------------------
-- The verdicts, for arbitrary circuits

-- A chain from the miter of a circuit against a specification without
-- path variables, ending without path variables at the identity's
-- polynomials, proves the circuit meets the specification.

by-restriction : (C : K.Circuit n) (ξ : PathSum n 0 0) (ρ : PathSum n k′ 0) →
                 (K.⟦ C KA.† ⟧ ∘ᴾ ξ) R.⇝* ρ →
                 (k′ ≡ 0 × (∀ w → out ρ w ≈[ + 2 ] μ x[ w ]) ×
                  phase ρ ≈[ pow 3 ] 0ᴾ) →
                 K.⟦ C ⟧ ≋ ξ
by-restriction C ξ ρ steps h = Equivalence.from
  (S.spec-restriction-syntactic C ξ ρ (R.noPaths-WellFormed ξ) steps) h

-- The same for a circuit with X gates against the identity, and the
-- two refutations.

withX-by-restriction : (C : CX.Circuit n) (ρ : PathSum n k′ 0) →
                       CX.⟦ C ⟧ R.⇝* ρ →
                       (k′ ≡ 0 × (∀ w → out ρ w ≈[ + 2 ] μ x[ w ]) ×
                        phase ρ ≈[ pow 3 ] 0ᴾ) →
                       CX.⟦ C ⟧ ≋ idPS
withX-by-restriction C ρ steps h = Equivalence.from
  (R.restriction-syntactic CX.⟦ C ⟧ ρ (CXW.circuit-WellFormed C) steps) h

withX-refuted : (C : CX.Circuit n) (ρ : PathSum n k′ 0) →
                CX.⟦ C ⟧ R.⇝* ρ → ¬ (phase ρ ≈[ pow 3 ] 0ᴾ) →
                ¬ (CX.⟦ C ⟧ ≋ idPS)
withX-refuted C ρ steps ne eq = ne (proj₂ (proj₂ (Equivalence.to
  (R.restriction-syntactic CX.⟦ C ⟧ ρ (CXW.circuit-WellFormed C) steps)
  eq)))

withX-refuted-out : (C : CX.Circuit n) (w : Fin n) →
                    (∀ j → NoVar (+ 2) y[ j ] (out CX.⟦ C ⟧ w)) →
                    ¬ (out CX.⟦ C ⟧ w ≈[ + 2 ] μ x[ w ]) →
                    ¬ (CX.⟦ C ⟧ ≋ idPS)
withX-refuted-out C w noy ne =
  P.restriction-refutes-syntactic CX.⟦ C ⟧ CX.⟦ C ⟧ R.ε⇝ w noy ne


------------------------------------------------------------------------
-- The seven-T Toffoli gate against its specification

c₁ c₂ t : Fin 3
c₁ = zero
c₂ = suc zero
t  = suc (suc zero)

C : K.Circuit 3
C = TG.tof c₁ c₂ t (λ ()) (λ ()) (λ ())

spec : PathSum 3 0 0
spec = TG.toffoliˢ c₁ c₂ t

-- ⟦ C† ⟧'s outputs: the two controls, and the last Hadamard's variable
-- on the target.

out†-c₁ : out K.⟦ C KA.† ⟧ c₁ ≡ liftᴸ (varᴸ x[ c₁ ])
out†-c₁ = refl

out†-c₂ : out K.⟦ C KA.† ⟧ c₂ ≡ liftᴸ (varᴸ x[ c₂ ])
out†-c₂ = refl

out†-t : out K.⟦ C KA.† ⟧ t ≡ liftᴸ (varᴸ y[ zero ])
out†-t = refl

private
  -- Along a path, they read their values.

  read† : (w : Fin 3) (v : Var 3 2) →
          out K.⟦ C KA.† ⟧ w ≡ liftᴸ (varᴸ v) →
          (x′ : Assign 3) (Y : Assign 2) →
          outBit K.⟦ C KA.† ⟧ x′ Y w ≡ valᵛ v x′ Y
  read† w v eq x′ Y = trans (Am.outBit-liftᴸ K.⟦ C KA.† ⟧ x′ Y w (varᴸ v) eq)
                            (valᴸ-var v x′ Y)

  tof-≗ : ∀ {x x′ : Assign 3} → (∀ i → x i ≡ x′ i) →
          ∀ w → TG.toffoli c₁ c₂ t x w ≡ TG.toffoli c₁ c₂ t x′ w
  tof-≗ {x} {x′} x≗ w =
    trans (≔-cong t (x t xor (x c₁ ∧ x c₂)) x≗ w)
          (cong (λ b → (x′ [ t ≔ b ]) w)
                (cong₂ _xor_ (x≗ t) (cong₂ _∧_ (x≗ c₁) (x≗ c₂))))

-- The reduct: one path variable, the identity's outputs, phase 0.

ρ₁ : PathSum 3 2 1
ρ₁ = ⟨ 0ᴾ , (λ w → μ x[ w ]) ⟩

-- The phase of ⟦ C† ⟧ along the kept paths, at the inputs the
-- specification sends x to, vanishes modulo 1: checked at all 16
-- points.

E : Assign 3 → Assign 1 → ℤ
E x g = eval (phase K.⟦ C KA.† ⟧) (TG.toffoli c₁ c₂ t x)
             (insertᵃ zero (x t) g)

private
  E-resp : ∀ {x x′ : Assign 3} {g g′ : Assign 1} →
           (∀ i → x i ≡ x′ i) → (∀ j → g j ≡ g′ j) →
           pow 3 ∣ E x g → pow 3 ∣ E x′ g′
  E-resp {x} {x′} {g} {g′} x≗ g≗ = subst (pow 3 ∣_)
    (eval-cong (phase K.⟦ C KA.† ⟧)
      {TG.toffoli c₁ c₂ t x} {TG.toffoli c₁ c₂ t x′}
      {insertᵃ zero (x t) g} {insertᵃ zero (x′ t) g′}
      (tof-≗ x≗) ins-≗)
    where
    ins-≗ : ∀ i → insertᵃ zero (x t) g i ≡ insertᵃ zero (x′ t) g′ i
    ins-≗ zero    = x≗ t
    ins-≗ (suc i) = g≗ i

phase-vanishes : ∀ (x : Assign 3) (g : Assign 1) → pow 3 ∣ E x g
phase-vanishes = toWitness
  {a? = all-points? {B = λ x g → pow 3 ∣ E x g} E-resp
                    (λ x g → pow 3 ∣? E x g)} tt

-- The restriction step: y₀ ← x₃ on the target.  The specification
-- computes the Toffoli function and has phase 0.

restricts₁ : R.Restricts (K.⟦ C KA.† ⟧ ∘ᴾ spec) t zero ρ₁
restricts₁ = S.restricts-after K.⟦ C KA.† ⟧ spec (TG.toffoli c₁ c₂ t)
  (λ _ → 0ℤ) (TG.fun-toffoliˢ c₁ c₂ t) (λ x → eval-0ᴾ {3} {0} x CL.none)
  t zero ρ₁ (λ x g → x t) miss outs solves ph
  where
  miss : ∀ (x : Assign 3) (g : Assign 1) →
         outBit K.⟦ C KA.† ⟧ (TG.toffoli c₁ c₂ t x)
                (insertᵃ zero (not (x t)) g) t ≡ not (x t)
  miss x g = read† t y[ zero ] out†-t (TG.toffoli c₁ c₂ t x)
                   (insertᵃ zero (not (x t)) g)

  outs : ∀ (x : Assign 3) (g : Assign 1) v → outBit ρ₁ x g v ≡
         outBit K.⟦ C KA.† ⟧ (TG.toffoli c₁ c₂ t x)
                (insertᵃ zero (x t) g) v
  outs x g zero = trans (D.outBit-μ ρ₁ x g zero x[ zero ] refl)
    (sym (trans (read† c₁ x[ c₁ ] out†-c₁ (TG.toffoli c₁ c₂ t x)
                       (insertᵃ zero (x t) g))
                (≔-there x {t} {c₁} (x t xor (x c₁ ∧ x c₂)) (λ ()))))
  outs x g (suc zero) = trans (D.outBit-μ ρ₁ x g c₂ x[ c₂ ] refl)
    (sym (trans (read† c₂ x[ c₂ ] out†-c₂ (TG.toffoli c₁ c₂ t x)
                       (insertᵃ zero (x t) g))
                (≔-there x {t} {c₂} (x t xor (x c₁ ∧ x c₂)) (λ ()))))
  outs x g (suc (suc zero)) = trans (D.outBit-μ ρ₁ x g t x[ t ] refl)
    (sym (read† t y[ zero ] out†-t (TG.toffoli c₁ c₂ t x)
                (insertᵃ zero (x t) g)))

  solves : ∀ (x : Assign 3) (g : Assign 1) → outBit ρ₁ x g t ≡ x t
  solves x g = D.outBit-μ ρ₁ x g t x[ t ] refl

  ph : ∀ (x : Assign 3) (g : Assign 1) →
       pow 3 ∣ (eval 0ᴾ x g - (0ℤ + E x g))
  ph x g = subst (pow 3 ∣_) (sym shape) (∣m⇒∣-m (phase-vanishes x g))
    where
    shape : eval 0ᴾ x g - (0ℤ + E x g) ≡ - E x g
    shape = trans (cong (λ a → a - (0ℤ + E x g)) (eval-0ᴾ x g))
      (trans (cong (λ s → 0ℤ - s) (+-identityˡ (E x g)))
             (+-identityˡ (- E x g)))

-- [Elim] then removes the remaining path variable, which no output
-- mentions.

private
  outs-internal : ∀ {n k m} (ρ : PathSum n k (suc m)) →
                  (∀ w → out ρ w ≡ μ x[ w ]) →
                  ∀ w → NoVar (+ 2) y[ zero ] (out ρ w)
  outs-internal ρ eq w = subst (NoVar (+ 2) y[ zero ]) (sym (eq w))
    (Absent⇒NoVar {c = + 2} {v = y[ zero ]} {P = μ x[ w ]}
                  (Absent-μ x[ w ] y[ zero ] ∉⊥))

elim₁ : ρ₁ Rd.⟶ Rd.elim-reduct ρ₁
elim₁ = Rd.elim ρ₁ (λ _ → i∣0) (outs-internal ρ₁ (λ _ → refl))

ρ₂ : PathSum 3 0 0
ρ₂ = Rd.elim-reduct ρ₁

chain₁ : (K.⟦ C KA.† ⟧ ∘ᴾ spec) R.⇝* ρ₂
chain₁ = R.restrict (R.step t zero restricts₁) R.◅⇝
         (R.rule (F.⟶⇒⟶ᶠ elim₁) R.◅⇝ R.ε⇝)

-- What is left is the identity, syntactically.

outs₂ : ∀ w → out ρ₂ w ≈[ + 2 ] μ x[ w ]
outs₂ zero             = by-eval (out ρ₂ zero) (+ 2) (μ x[ zero ])
outs₂ (suc zero)       = by-eval (out ρ₂ (suc zero)) (+ 2) (μ x[ suc zero ])
outs₂ (suc (suc zero)) =
  by-eval (out ρ₂ (suc (suc zero))) (+ 2) (μ x[ suc (suc zero) ])

phase₂ : phase ρ₂ ≈[ pow 3 ] 0ᴾ
phase₂ = by-eval (phase ρ₂) (pow 3) 0ᴾ

-- Hence the circuit meets its specification.

toffoli-by-restriction : K.⟦ C ⟧ ≋ spec
toffoli-by-restriction = by-restriction C spec ρ₂ chain₁ (refl , outs₂ , phase₂)


------------------------------------------------------------------------
-- H; Z; H; X, with an affine output

HZHX : CX.Circuit 1
HZHX = CX.H zero ∷ CX.R 1 zero ∷ CX.H zero ∷ CX.X zero ∷ []

-- Its output is 1 ⊕ y₀.

outZ-form : out CX.⟦ HZHX ⟧ zero ≡ liftᴸ (CX.notᴸ (varᴸ y[ zero ]))
outZ-form = refl

private
  readZ : (x : Assign 1) (Y : Assign 2) →
          outBit CX.⟦ HZHX ⟧ x Y zero ≡ not (Y zero)
  readZ x Y = trans
    (Am.outBit-liftᴸ CX.⟦ HZHX ⟧ x Y zero (CX.notᴸ (varᴸ y[ zero ])) outZ-form)
    (trans (CX.valᴸ-not (varᴸ y[ zero ]) x Y)
           (cong not (valᴸ-var y[ zero ] x Y)))

ρ₃ : PathSum 1 2 1
ρ₃ = ⟨ 0ᴾ , (λ w → μ x[ w ]) ⟩

private
  EZ : Assign 1 → Assign 1 → ℤ
  EZ x g = eval 0ᴾ x g -
           eval (phase CX.⟦ HZHX ⟧) x (insertᵃ zero (not (x zero)) g)

  EZ-resp : ∀ {x x′ : Assign 1} {g g′ : Assign 1} →
            (∀ i → x i ≡ x′ i) → (∀ j → g j ≡ g′ j) →
            pow 3 ∣ EZ x g → pow 3 ∣ EZ x′ g′
  EZ-resp {x} {x′} {g} {g′} x≗ g≗ = subst (pow 3 ∣_)
    (cong₂ _-_ (eval-cong 0ᴾ x≗ g≗)
      (eval-cong (phase CX.⟦ HZHX ⟧)
        {x} {x′} {insertᵃ zero (not (x zero)) g}
        {insertᵃ zero (not (x′ zero)) g′} x≗ ins-≗))
    where
    ins-≗ : ∀ i → insertᵃ zero (not (x zero)) g i ≡
                  insertᵃ zero (not (x′ zero)) g′ i
    ins-≗ zero    = cong not (x≗ zero)
    ins-≗ (suc i) = g≗ i

  phaseZ : ∀ (x : Assign 1) (g : Assign 1) → pow 3 ∣ EZ x g
  phaseZ = toWitness
    {a? = all-points? {B = λ x g → pow 3 ∣ EZ x g} EZ-resp
                      (λ x g → pow 3 ∣? EZ x g)} tt

-- The restriction step: y₀ ← ¬x₁.

restricts₃ : R.Restricts CX.⟦ HZHX ⟧ zero zero ρ₃
restricts₃ = record
  { keep   = λ x g → not (x zero)
  ; miss   = λ x g → trans (readZ x (insertᵃ zero (not (not (x zero))) g))
                           (cong not (not-involutive (x zero)))
  ; outs   = outs
  ; solves = λ x g → D.outBit-μ ρ₃ x g zero x[ zero ] refl
  ; phase≡ = phaseZ
  }
  where
  outs : ∀ x g v → outBit ρ₃ x g v ≡
                   outBit CX.⟦ HZHX ⟧ x (insertᵃ zero (not (x zero)) g) v
  outs x g zero = trans (D.outBit-μ ρ₃ x g zero x[ zero ] refl)
    (sym (trans (readZ x (insertᵃ zero (not (x zero)) g))
                (not-involutive (x zero))))

elim₃ : ρ₃ Rd.⟶ Rd.elim-reduct ρ₃
elim₃ = Rd.elim ρ₃ (λ _ → i∣0) (outs-internal ρ₃ (λ _ → refl))

ρ₄ : PathSum 1 0 0
ρ₄ = Rd.elim-reduct ρ₃

chain₃ : CX.⟦ HZHX ⟧ R.⇝* ρ₄
chain₃ = R.restrict (R.step zero zero restricts₃) R.◅⇝
         (R.rule (F.⟶⇒⟶ᶠ elim₃) R.◅⇝ R.ε⇝)

HZHX-by-restriction : CX.⟦ HZHX ⟧ ≋ idPS
HZHX-by-restriction = withX-by-restriction HZHX ρ₄ chain₃
  (refl , (λ { zero → by-eval (out ρ₄ zero) (+ 2) (μ x[ zero ]) }) ,
   by-eval (phase ρ₄) (pow 3) 0ᴾ)


------------------------------------------------------------------------
-- Refutations

-- H; X; H is Z.  Its output is y₀; restricted at y₀ ← x₁ its phase is
-- ½x₁, which no further step removes.

HXH : CX.Circuit 1
HXH = CX.H zero ∷ CX.X zero ∷ CX.H zero ∷ []

outX-form : out CX.⟦ HXH ⟧ zero ≡ liftᴸ (varᴸ y[ zero ])
outX-form = refl

private
  readX : (x : Assign 1) (Y : Assign 2) →
          outBit CX.⟦ HXH ⟧ x Y zero ≡ Y zero
  readX x Y = trans
    (Am.outBit-liftᴸ CX.⟦ HXH ⟧ x Y zero (varᴸ y[ zero ]) outX-form)
    (valᴸ-var y[ zero ] x Y)

ρ₅ : PathSum 1 2 1
ρ₅ = ⟨ (+ 4) ⋆ x₁ , (λ w → μ x[ w ]) ⟩

private
  EX : Assign 1 → Assign 1 → ℤ
  EX x g = eval ((+ 4) ⋆ x₁) x g -
           eval (phase CX.⟦ HXH ⟧) x (insertᵃ zero (x zero) g)

  EX-resp : ∀ {x x′ : Assign 1} {g g′ : Assign 1} →
            (∀ i → x i ≡ x′ i) → (∀ j → g j ≡ g′ j) →
            pow 3 ∣ EX x g → pow 3 ∣ EX x′ g′
  EX-resp {x} {x′} {g} {g′} x≗ g≗ = subst (pow 3 ∣_)
    (cong₂ _-_ (eval-cong ((+ 4) ⋆ x₁) x≗ g≗)
      (eval-cong (phase CX.⟦ HXH ⟧)
        {x} {x′} {insertᵃ zero (x zero) g}
        {insertᵃ zero (x′ zero) g′} x≗ ins-≗))
    where
    ins-≗ : ∀ i → insertᵃ zero (x zero) g i ≡ insertᵃ zero (x′ zero) g′ i
    ins-≗ zero    = x≗ zero
    ins-≗ (suc i) = g≗ i

  phaseX : ∀ (x : Assign 1) (g : Assign 1) → pow 3 ∣ EX x g
  phaseX = toWitness
    {a? = all-points? {B = λ x g → pow 3 ∣ EX x g} EX-resp
                      (λ x g → pow 3 ∣? EX x g)} tt

restricts₅ : R.Restricts CX.⟦ HXH ⟧ zero zero ρ₅
restricts₅ = record
  { keep   = λ x g → x zero
  ; miss   = λ x g → readX x (insertᵃ zero (not (x zero)) g)
  ; outs   = outs
  ; solves = λ x g → D.outBit-μ ρ₅ x g zero x[ zero ] refl
  ; phase≡ = phaseX
  }
  where
  outs : ∀ x g v → outBit ρ₅ x g v ≡
                   outBit CX.⟦ HXH ⟧ x (insertᵃ zero (x zero) g) v
  outs x g zero = trans (D.outBit-μ ρ₅ x g zero x[ zero ] refl)
    (sym (readX x (insertᵃ zero (x zero) g)))

elim₅ : ρ₅ Rd.⟶ Rd.elim-reduct ρ₅
elim₅ = Rd.elim ρ₅ (by-eval (head-part (phase ρ₅)) (pow 3) 0ᴾ)
  (outs-internal ρ₅ (λ _ → refl))

ρ₆ : PathSum 1 0 0
ρ₆ = Rd.elim-reduct ρ₅

chain₅ : CX.⟦ HXH ⟧ R.⇝* ρ₆
chain₅ = R.restrict (R.step zero zero restricts₅) R.◅⇝
         (R.rule (F.⟶⇒⟶ᶠ elim₅) R.◅⇝ R.ε⇝)

HXH-not-id : ¬ (CX.⟦ HXH ⟧ ≋ idPS)
HXH-not-id = withX-refuted HXH ρ₆ chain₅
  (refute-by-eval (phase ρ₆) (pow 3) 0ᴾ)

-- X alone: its output 1 ⊕ x₁ has no path variable and is not x₁.

Xc : CX.Circuit 1
Xc = CX.X zero ∷ []

X-not-id : ¬ (CX.⟦ Xc ⟧ ≋ idPS)
X-not-id = withX-refuted-out Xc zero (λ ())
  (refute-by-eval (out CX.⟦ Xc ⟧ zero) (+ 2) (μ x[ zero ]))
