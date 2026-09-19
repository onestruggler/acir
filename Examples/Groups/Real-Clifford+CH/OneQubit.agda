------------------------------------------------------------------------
-- Presentations of groups
--
-- One-qubit completeness (Clément, Lemma 7.1)
--
-- On one wire the theory has three axioms, H² = ε, Z² = ε and
-- (HZ)⁸ = ε, and the paper's proof is a normal form: every one-wire
-- circuit is equal to (HZ)ᵏ or (HZ)ᵏ H with k < 8, and distinct normal
-- forms denote distinct matrices.  (The presented group is the
-- dihedral group of order 16, HZ being the rotation by π/4.)
--
-- The normal form is computed by a sixteen-state automaton reading the
-- circuit letter by letter (`run`); that it is a normal form for the
-- congruence is that the automaton respects the three axioms
-- (run-cong) and that its states read back as the circuits that reach
-- them (run-sound).  Uniqueness is decided: the sixteen matrices are
-- compared pairwise by computation.  Completeness — the interpretation
-- is injective on the presented monoid — is then the library's
-- by-normalization, packaged by StarPresentation.MonoidSem as a
-- sub-monoid presentation of the matrices over ℤ[1/√2].
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.OneQubit where

open import Algebra.Bundles using (Monoid)
open import Algebra.Morphism.Structures using (module MonoidMorphisms)
open import Data.Bool using (Bool ; true ; false ; if_then_else_)
open import Data.Fin using (Fin ; toℕ)
open import Data.Nat using (ℕ ; suc)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Function.Definitions using (Injective)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary.Decidable
  using (Dec ; yes ; no ; True ; toWitness ; map′ ; _→?_ ; _×?_ ; dec-true)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)

import Data.Bool.Properties as BoolP
import Data.Fin.Properties as FinP
import Data.Product.Properties as ProdP
import Relation.Binary.Reasoning.Setoid as SR

open import Notations
import Normalization.NormalForm.Propositional as NFBase
import Normalization.NormalForm.Setoid as SNF
import Normalization.NormalForm.Uniqueness.Propositional as NFU
open import Normalization.StarPresentation
open import Presentation.Definitions using (_IsSubMonoidPresentationOf_)
import Presentation.Base as PB
import Presentation.Properties as PP

open import Examples.Groups.Real-Clifford+CH.Semantics hiding (_^_ ; ^-+)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation
open import Examples.Groups.Real-Clifford+CH.Soundness using (axiom-soundᴱ)

-- The one-wire theory: Figure 4 restricted to width 1, which is the
-- three axioms (1)–(3).
Γ₁ : _
Γ₁ = 1 VRel,_===_

open PB Γ₁ using (_≈_ ; refl ; refl' ; sym ; trans ; cong ; assoc ; left-unit ; right-unit ; axiom)
open PP Γ₁ using (word-setoid ; ^-+)

------------------------------------------------------------------------
-- Normal forms: (HZ)ᵏ, or (HZ)ᵏ followed by H

NF : Set
NF = Fin 8 × Bool

HZ : Circuit 1
HZ = H • Z

[_] : NF → Circuit 1
[ k , b ] = HZ ^ toℕ k • (if b then H else ε)

-- Successor and predecessor modulo 8.
sucF predF : Fin 8 → Fin 8
sucF ₀ = ₁
sucF ₁ = ₂
sucF ₂ = ₃
sucF ₃ = ₄
sucF ₄ = ₅
sucF ₅ = ₆
sucF ₆ = ₇
sucF ₇ = ₀
predF ₀ = ₇
predF ₁ = ₀
predF ₂ = ₁
predF ₃ = ₂
predF ₄ = ₃
predF ₅ = ₄
predF ₆ = ₅
predF ₇ = ₆

------------------------------------------------------------------------
-- The automaton
--
-- Reading H toggles the trailing H; reading Z after (HZ)ᵏ H completes a
-- further HZ, and reading Z after (HZ)ᵏ borrows one: (HZ)ᵏ Z =
-- (HZ)ᵏ⁻¹ H Z Z = (HZ)ᵏ⁻¹ H.

step : Gen 1 → NF → NF
step H-gen (k , b)     = k , Data.Bool.not b
step Z-gen (k , true)  = sucF k , false
step Z-gen (k , false) = predF k , true
step (gate₀ ()) _
step (gate₀ () ↥) _

run : NF → Circuit 1 → NF
run s [ g ]ʷ  = step g s
run s ε       = s
run s (w • v) = run (run s w) v

nf : Circuit 1 → NF
nf = run (₀ , false)

------------------------------------------------------------------------
-- The states read back as the circuits reaching them

private
  -- (HZ)ⁿ⁺¹ appends one more HZ.
  ^-suc : ∀ n → HZ ^ suc n ≈ HZ ^ n • HZ
  ^-suc n = trans (refl' (Eq.cong (HZ ^_) (NP.+-comm 1 n))) (^-+ HZ n 1)
    where import Data.Nat.Properties as NP

  step-H-false : ∀ k → [ k , true ] ≈ [ k , false ] • H
  step-H-false k = begin
    HZ ^ toℕ k • H          ≈⟨ cong (sym right-unit) refl ⟩
    (HZ ^ toℕ k • ε) • H    ∎
    where open SR word-setoid

  step-H-true : ∀ k → [ k , false ] ≈ [ k , true ] • H
  step-H-true k = begin
    HZ ^ toℕ k • ε          ≈⟨ cong refl (sym (axiom (srel order-H))) ⟩
    HZ ^ toℕ k • (H • H)    ≈⟨ sym assoc ⟩
    (HZ ^ toℕ k • H) • H    ∎
    where open SR word-setoid

  -- Completing a further HZ.
  step-up : ∀ n → HZ ^ suc n • ε ≈ (HZ ^ n • H) • Z
  step-up n = begin
    HZ ^ suc n • ε          ≈⟨ right-unit ⟩
    HZ ^ suc n              ≈⟨ ^-suc n ⟩
    HZ ^ n • (H • Z)        ≈⟨ sym assoc ⟩
    (HZ ^ n • H) • Z        ∎
    where open SR word-setoid

  -- Borrowing an HZ.
  step-down : ∀ n → HZ ^ n • H ≈ (HZ ^ suc n • ε) • Z
  step-down n = begin
    HZ ^ n • H              ≈⟨ sym right-unit ⟩
    (HZ ^ n • H) • ε        ≈⟨ cong refl (sym (axiom (srel order-Z))) ⟩
    (HZ ^ n • H) • (Z • Z)  ≈⟨ sym assoc ⟩
    ((HZ ^ n • H) • Z) • Z  ≈⟨ cong (sym (step-up n)) refl ⟩
    (HZ ^ suc n • ε) • Z    ∎
    where open SR word-setoid

  step-Z-true : ∀ k → [ sucF k , false ] ≈ [ k , true ] • Z
  step-Z-true ₀ = step-up 0
  step-Z-true ₁ = step-up 1
  step-Z-true ₂ = step-up 2
  step-Z-true ₃ = step-up 3
  step-Z-true ₄ = step-up 4
  step-Z-true ₅ = step-up 5
  step-Z-true ₆ = step-up 6
  step-Z-true ₇ = begin
    ε • ε                   ≈⟨ left-unit ⟩
    ε                       ≈⟨ sym (axiom (srel order-HZ)) ⟩
    HZ ^ 8                  ≈⟨ ^-suc 7 ⟩
    HZ ^ 7 • (H • Z)        ≈⟨ sym assoc ⟩
    (HZ ^ 7 • H) • Z        ∎
    where open SR word-setoid

  step-Z-false : ∀ k → [ predF k , true ] ≈ [ k , false ] • Z
  step-Z-false ₀ = begin
    HZ ^ 7 • H              ≈⟨ step-down 7 ⟩
    (HZ ^ 8 • ε) • Z        ≈⟨ cong (cong (axiom (srel order-HZ)) refl) refl ⟩
    (ε • ε) • Z             ∎
    where open SR word-setoid
  step-Z-false ₁ = step-down 0
  step-Z-false ₂ = step-down 1
  step-Z-false ₃ = step-down 2
  step-Z-false ₄ = step-down 3
  step-Z-false ₅ = step-down 4
  step-Z-false ₆ = step-down 5
  step-Z-false ₇ = step-down 6

  step-sound : ∀ (g : Gen 1) s → [ step g s ] ≈ [ s ] • [ g ]ʷ
  step-sound H-gen (k , false) = step-H-false k
  step-sound H-gen (k , true)  = step-H-true k
  step-sound Z-gen (k , true)  = step-Z-true k
  step-sound Z-gen (k , false) = step-Z-false k
  step-sound (gate₀ ()) _
  step-sound (gate₀ () ↥) _

run-sound : ∀ s w → [ run s w ] ≈ [ s ] • w
run-sound s [ g ]ʷ  = step-sound g s
run-sound s ε       = sym right-unit
run-sound s (w • v) = begin
  [ run (run s w) v ]     ≈⟨ run-sound (run s w) v ⟩
  [ run s w ] • v         ≈⟨ cong (run-sound s w) refl ⟩
  ([ s ] • w) • v         ≈⟨ assoc ⟩
  [ s ] • (w • v)         ∎
  where open SR word-setoid

-- Every circuit equals its normal form.
nf-sound : ∀ w → [ nf w ] ≈ w
nf-sound w = trans (run-sound (₀ , false) w) (trans (cong left-unit refl) left-unit)

------------------------------------------------------------------------
-- The automaton respects the axioms

private
  sucF-predF : ∀ k → sucF (predF k) ≡ k
  sucF-predF ₀ = Eq.refl
  sucF-predF ₁ = Eq.refl
  sucF-predF ₂ = Eq.refl
  sucF-predF ₃ = Eq.refl
  sucF-predF ₄ = Eq.refl
  sucF-predF ₅ = Eq.refl
  sucF-predF ₆ = Eq.refl
  sucF-predF ₇ = Eq.refl

  predF-sucF : ∀ k → predF (sucF k) ≡ k
  predF-sucF ₀ = Eq.refl
  predF-sucF ₁ = Eq.refl
  predF-sucF ₂ = Eq.refl
  predF-sucF ₃ = Eq.refl
  predF-sucF ₄ = Eq.refl
  predF-sucF ₅ = Eq.refl
  predF-sucF ₆ = Eq.refl
  predF-sucF ₇ = Eq.refl

  -- Eight rotations are the identity.
  run-HZ⁸ : ∀ s → run s (HZ ^ 8) ≡ s
  run-HZ⁸ (₀ , false) = Eq.refl
  run-HZ⁸ (₁ , false) = Eq.refl
  run-HZ⁸ (₂ , false) = Eq.refl
  run-HZ⁸ (₃ , false) = Eq.refl
  run-HZ⁸ (₄ , false) = Eq.refl
  run-HZ⁸ (₅ , false) = Eq.refl
  run-HZ⁸ (₆ , false) = Eq.refl
  run-HZ⁸ (₇ , false) = Eq.refl
  run-HZ⁸ (₀ , true)  = Eq.refl
  run-HZ⁸ (₁ , true)  = Eq.refl
  run-HZ⁸ (₂ , true)  = Eq.refl
  run-HZ⁸ (₃ , true)  = Eq.refl
  run-HZ⁸ (₄ , true)  = Eq.refl
  run-HZ⁸ (₅ , true)  = Eq.refl
  run-HZ⁸ (₆ , true)  = Eq.refl
  run-HZ⁸ (₇ , true)  = Eq.refl

  axiom-run : ∀ {w v : Circuit 1} → 1 VRel, w === v → ∀ s → run s w ≡ run s v
  axiom-run (srel order-H)  (k , true)  = Eq.refl
  axiom-run (srel order-H)  (k , false) = Eq.refl
  axiom-run (srel order-Z)  (k , true)  = Eq.cong (_, true) (predF-sucF k)
  axiom-run (srel order-Z)  (k , false) = Eq.cong (_, false) (sucF-predF k)
  axiom-run (srel order-HZ) s           = run-HZ⁸ s
  axiom-run (cong↑ (srel ()))
  axiom-run (comm₁ _ (gate₀ ()))
  axiom-run (ω↑=ω ())

run-cong : ∀ {w v} → w ≈ v → ∀ s → run s w ≡ run s v
run-cong refl          s = Eq.refl
run-cong (sym e)       s = Eq.sym (run-cong e s)
run-cong (trans e f)   s = Eq.trans (run-cong e s) (run-cong f s)
run-cong (cong {w} {w'} {v} {v'} e f) s =
  Eq.trans (run-cong f (run s w)) (Eq.cong (λ t → run t v') (run-cong e s))
run-cong assoc         s = Eq.refl
run-cong left-unit     s = Eq.refl
run-cong right-unit    s = Eq.refl
run-cong (axiom r)     s = axiom-run r s

------------------------------------------------------------------------
-- The normal form

open NFBase Γ₁ NF using (NormalForm)

nfp' : NormalForm
nfp' = record
  { rightInverse = record
      { to        = nf
      ; from      = [_]
      ; to-cong   = λ e → run-cong e (₀ , false)
      ; from-cong = λ { Eq.refl → refl }
      ; inverseʳ  = λ { Eq.refl → nf-sound _ }
      }
  }

------------------------------------------------------------------------
-- Uniqueness: distinct normal forms denote distinct matrices
--
-- Decided by computation on the sixteen stored matrices: the scaled
-- comparison of Interpretation.by-matrix, for every pair.

private
  _≟NF_ : DecidableEquality NF
  _≟NF_ = ProdP.≡-dec FinP._≟_ BoolP._≟_

  Sameᴹ : NF → NF → Set
  Sameᴹ u v = scaleM (√2^ len [ v ]) ⟦ [ u ] ⟧M ≡ scaleM (√2^ len [ u ] ) ⟦ [ v ] ⟧M

  -- Quantifying over the finite state space.
  ∀Bool : {P : Bool → Set} → (∀ b → Dec (P b)) → Dec (∀ b → P b)
  ∀Bool d = map′ (λ { (pt , pf) → λ { true → pt ; false → pf } })
                 (λ f → f true , f false) (d true ×? d false)

  ∀NF : {P : NF → Set} → (∀ s → Dec (P s)) → Dec (∀ s → P s)
  ∀NF d = map′ (λ f → λ { (k , b) → f k b }) (λ f k b → f (k , b))
               (FinP.all? (λ k → ∀Bool (λ b → d (k , b))))

  distinct? : Dec (∀ u v → Sameᴹ u v → u ≡ v)
  distinct? = ∀NF (λ u → ∀NF (λ v → mat-dec _ _ →? u ≟NF v))

  distinct : ∀ u v → Sameᴹ u v → u ≡ v
  distinct = toWitness {a? = distinct?} _

  -- From operators to stored matrices.
  to-trie : ∀ u v → ⟦ [ u ] ⟧ ~ ⟦ [ v ] ⟧ → Sameᴹ u v
  to-trie u v e = mat-ext
    (≐-trans (ix-scaleM _ _)
      (≐-trans (·-cong Eq.refl (≐-sym (⟦⟧-ix [ u ])))
        (≐-trans e
          (≐-trans (·-cong Eq.refl (⟦⟧-ix [ v ])) (≐-sym (ix-scaleM _ _))))))

unique : ∀ {u v} → ⟦ [ u ] ⟧ ~ ⟦ [ v ] ⟧ → u ≡ v
unique {u} {v} e = distinct u v (to-trie u v e)

------------------------------------------------------------------------
-- Completeness (Lemma 7.1)

private
  module MS = MonoidSem Γ₁ (Eq.setoid NF) (Scaled-monoid 1) (λ g → 1 , ⟦ g ⟧ᵍ)

  -- The library reads a circuit through the monoid (MS.⟦_⟧); that
  -- reading is ⟦_⟧ (Interpretation.⟦⟧ᴱ-def), so the witnesses transfer.
  unfp : NFU.UniqueNormalForm Γ₁ NF (Monoid.setoid (Scaled-monoid 1)) MS.⟦_⟧
           (SNF.NormalForm.inv-nf nfp')
  unfp = record { unique = λ {u} {v} e → unique (~-⟦⟧ᴱ {w = [ u ]} {[ v ]} e) }

  module Sub = MS.GetSubPresentation axiom-soundᴱ nfp' unfp

-- On one wire, Figure 4 presents its image: a sub-monoid of the
-- matrices over ℤ[1/√2].
subpresentation : Γ₁ IsSubMonoidPresentationOf Scaled-monoid 1
subpresentation = Sub.monoidSubPres

-- Two one-qubit circuits with the same matrix are equal in QC.
complete : ∀ {w v : Circuit 1} → ⟦ w ⟧ ~ ⟦ v ⟧ → 1 ⊢ w ≈ v
complete {w} {v} e = MonoidMorphisms.IsMonoidMonomorphism.injective
  (_IsSubMonoidPresentationOf_.mono subpresentation) {w} {v} (⟦⟧ᴱ-~ {w = w} {v} e)
