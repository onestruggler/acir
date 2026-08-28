------------------------------------------------------------------------
-- Presentations of groups
--
-- The two models of the projective qubit Clifford group agree:
--
--     CMS n  ≅  VSp n.
--
-- CMS n (Qubit.CliffordGroup) is the SYNTACTIC model: Clifford words over
-- the generators H, S, CZ, quotiented by equality of their sign-tracking
-- action on the phased Pauli group P4 n = ℤ/4 × Pauli n.  VSp n
-- (Qubit.Semantics.VSp) is the STRUCTURAL model: pairs (S , φ) of a symplectic map
-- and a ℤ/4 phase function refining its twist.
--
-- The isomorphism is the denotation ⟦_⟧ᵛ that VSp already defines on
-- circuits.  Everything follows from one observation (cact-⟦⟧ᵛ): the P4
-- action of a word is exactly its VSp element read as an action,
--
--     cact w (s , P) = (s + phase ⟦ w ⟧ᵛ P , ap (symp ⟦ w ⟧ᵛ) P),
--
-- so two words act alike iff their pairs agree — well-definedness and
-- injectivity at once.  Surjectivity uses the exactness of VSp: a
-- circuit realises the symplectic part (surj-nf), the leftover lies in
-- the Pauli kernel, and Pauli conjugations are themselves words
-- (CliffordGroup.pauliWord).
--
-- The two developments were built independently — VSp re-derives the
-- commutation cocycle rather than importing SignedPauli — so the phase
-- conventions have to be matched by hand; that is what inc≗incl, ι≗ι
-- and φᵍ≗δ do.  They are all identities of tables at p = 2.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.ProjectiveClifford.Qubit.Iso2 where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures
  using (module MonoidMorphisms ; module GroupMorphisms)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_ ; proj₁ ; proj₂ ; Σ-syntax)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations
open import ForStdlib.Data.Fin.Mod
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import ForStdlib.Algebra.Morphism.Consequences
  using (isMonoidHomomorphism⇒isGroupHomomorphism)

-- The structural model, opened wholesale: it supplies Φ, ι, inc, Cliff,
-- _≈ᵛ_, _∙ᵛ_, εᵛ, _⁻¹ᵛ, incl, φᵍ, ⟦_⟧ᵛ, symp-⟦⟧ᵛ, ker⊆im-incl and the
-- group bundle.
open import Examples.Groups.ProjectiveClifford.Qubit.Semantics.VSp

open import ForStdlib.Data.Fin.Mod.Prime.Two using (p-2 ; p-prime)

open PrimeModulus p-2 p-prime

open import Examples.Groups.ProjectivePauli.Semantics p-2 p-prime using (Pauli ; sform)
open import Examples.Groups.Symplectic.Semantics p-2 p-prime
  using (Symplectic ; _≈ˢ_ ; εˢ)
open Symplectic using (ap ; ap⁻¹ ; invˡ ; invʳ)
import Examples.Groups.Symplectic.Semantics p-2 p-prime as SympSem
open SympSem.Interpretation using (actg)
import Examples.Groups.Symplectic.Syntactics p-2 p-prime as Syn
open Syn.Symplectic
  using (Gen ; Circuit ; gate₁ ; gate₂ ; H-gate ; S-gate ; CZ-gate ; _↥)
open import Examples.Groups.Symplectic.Surjectivity p-2 p-prime using (surj-nf)

import Examples.Groups.Pauli.Qubit.SignedPauli as SP
import Examples.Groups.ProjectiveClifford.Qubit.CliffordAction as CA
import Examples.Groups.ProjectiveClifford.Qubit.CliffordGroup as CG

private
  variable
    n : ℕ

-- Reflexivity and transitivity of _≈ᵛ_, with the endpoints explicit:
-- _≈ᵛ_ unfolds to a pair of pointwise equations, so Agda can never solve
-- them from the type of an argument.
≈ᵛ-refl : (X : Cliff n) → X ≈ᵛ X
≈ᵛ-refl X = (λ _ → Eq.refl) , (λ _ → Eq.refl)

≈ᵛ-trans : (X Y Z : Cliff n) → X ≈ᵛ Y → Y ≈ᵛ Z → X ≈ᵛ Z
≈ᵛ-trans X Y Z (s , f) (s' , f') =
  (λ P → Eq.trans (s P) (s' P)) , (λ P → Eq.trans (f P) (f' P))

------------------------------------------------------------------------
-- Matching the phase conventions
--
-- VSp's ι / inc and CliffordAction's ι / incl are the same two maps
-- ℤ/2 → ℤ/4, defined twice.

ι≗ι : (x : ℤ ₚ) → ι x ≡ SP.ι x
ι≗ι ₀ = auto
ι≗ι ₁ = auto

inc≗incl : (x : ℤ ₚ) → inc x ≡ CA.incl x
inc≗incl ₀ = auto
inc≗incl ₁ = auto

-- Hence the generator phase functions coincide.
φᵍ≗δ : (g : Gen n) (P : Pauli n) → φᵍ g P ≡ CA.δ g P
φᵍ≗δ (gate₁ H-gate)  ((a , b) ∷ vs)             = ι≗ι (a * b)
φᵍ≗δ (gate₁ S-gate)  ((a , b) ∷ vs)             = inc≗incl a
φᵍ≗δ (gate₂ CZ-gate) ((a , b) ∷ (a' , b') ∷ vs) = ι≗ι (a * a')
φᵍ≗δ (g ↥)           (x ∷ vs)                   = φᵍ≗δ g vs

------------------------------------------------------------------------
-- The P4 action of a word, read off its VSp element
--
-- This is the bridge: the ℤ/4 component moves by the phase function and
-- the Pauli component by the symplectic map.

cact-⟦⟧ᵛ : (w : Circuit n) (s : Φ) (P : Pauli n) →
           CA.cact w (s , P) ≡ (s + phase ⟦ w ⟧ᵛ P , ap (symp ⟦ w ⟧ᵛ) P)
cact-⟦⟧ᵛ [ g ]ʷ s P =
  Eq.cong (λ □ → (s + □) , actg g P) (Eq.sym (φᵍ≗δ g P))
cact-⟦⟧ᵛ ε      s P = Eq.cong (_, P) (Eq.sym (+-identityʳ s))
cact-⟦⟧ᵛ (w • v) s P = begin
  CA.cact w (CA.cact v (s , P))
    ≡⟨ Eq.cong (CA.cact w) (cact-⟦⟧ᵛ v s P) ⟩
  CA.cact w (s + phase ⟦ v ⟧ᵛ P , ap (symp ⟦ v ⟧ᵛ) P)
    ≡⟨ cact-⟦⟧ᵛ w (s + phase ⟦ v ⟧ᵛ P) (ap (symp ⟦ v ⟧ᵛ) P) ⟩
  ((s + phase ⟦ v ⟧ᵛ P) + phase ⟦ w ⟧ᵛ (ap (symp ⟦ v ⟧ᵛ) P))
    , ap (symp ⟦ w ⟧ᵛ) (ap (symp ⟦ v ⟧ᵛ) P)
    ≡⟨ Eq.cong (_, ap (symp ⟦ w ⟧ᵛ) (ap (symp ⟦ v ⟧ᵛ) P))
               (+-assoc s (phase ⟦ v ⟧ᵛ P)
                          (phase ⟦ w ⟧ᵛ (ap (symp ⟦ v ⟧ᵛ) P))) ⟩
  (s + phase ⟦ w • v ⟧ᵛ P) , ap (symp ⟦ w • v ⟧ᵛ) P   ∎
  where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- Well-definedness and injectivity
--
-- Both directions of "same action ⟺ same pair", by probing the action at
-- phase ₀ and cancelling it.

⟦⟧ᵛ-cong : {w v : Circuit n} → w CG.≈ᶜ v → ⟦ w ⟧ᵛ ≈ᵛ ⟦ v ⟧ᵛ
⟦⟧ᵛ-cong {n} {w = w} {v} w≈v =
    (λ P → Eq.cong proj₂ (probe P))
  , (λ P → Eq.trans (Eq.sym (+-identityˡ (phase ⟦ w ⟧ᵛ P)))
             (Eq.trans (Eq.cong proj₁ (probe P))
                       (+-identityˡ (phase ⟦ v ⟧ᵛ P))))
  where
  probe : (P : Pauli n) →
          (₀ + phase ⟦ w ⟧ᵛ P , ap (symp ⟦ w ⟧ᵛ) P)
            ≡ (₀ + phase ⟦ v ⟧ᵛ P , ap (symp ⟦ v ⟧ᵛ) P)
  probe P = Eq.trans (Eq.sym (cact-⟦⟧ᵛ w ₀ P))
                     (Eq.trans (w≈v (₀ , P)) (cact-⟦⟧ᵛ v ₀ P))

⟦⟧ᵛ-injective : {w v : Circuit n} → ⟦ w ⟧ᵛ ≈ᵛ ⟦ v ⟧ᵛ → w CG.≈ᶜ v
⟦⟧ᵛ-injective {w = w} {v} (s , f) (t , P) = begin
  CA.cact w (t , P)
    ≡⟨ cact-⟦⟧ᵛ w t P ⟩
  (t + phase ⟦ w ⟧ᵛ P) , ap (symp ⟦ w ⟧ᵛ) P
    ≡⟨ Eq.cong₂ _,_ (Eq.cong (t +_) (f P)) (s P) ⟩
  (t + phase ⟦ v ⟧ᵛ P) , ap (symp ⟦ v ⟧ᵛ) P
    ≡⟨ Eq.sym (cact-⟦⟧ᵛ v t P) ⟩
  CA.cact v (t , P)   ∎
  where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- Pauli words denote Pauli conjugations

pauliWord-incl : (u : Pauli n) → ⟦ CG.pauliWord u ⟧ᵛ ≈ᵛ incl u
pauliWord-incl {n} u =
    (λ Q → Eq.cong proj₂ (probe Q))
  , (λ Q → Eq.trans (Eq.sym (+-identityˡ (phase ⟦ CG.pauliWord u ⟧ᵛ Q)))
             (Eq.trans (Eq.cong proj₁ (probe Q))
               (Eq.trans (+-identityˡ (SP.ι (sform u Q)))
                         (Eq.sym (ι≗ι (sform u Q))))))
  where
  probe : (Q : Pauli n) →
          (₀ + phase ⟦ CG.pauliWord u ⟧ᵛ Q , ap (symp ⟦ CG.pauliWord u ⟧ᵛ) Q)
            ≡ (₀ + SP.ι (sform u Q) , Q)
  probe Q = Eq.trans (Eq.sym (cact-⟦⟧ᵛ (CG.pauliWord u) ₀ Q))
                     (CG.cact-pauliWord u ₀ Q)

------------------------------------------------------------------------
-- Surjectivity
--
-- Realise the symplectic part by a circuit, divide it out, land in the
-- Pauli kernel, and put the Pauli back as a word.

⟦⟧ᵛ-surjective : (X : Cliff n) → Σ[ w ∈ Circuit n ] (⟦ w ⟧ᵛ ≈ᵛ X)
⟦⟧ᵛ-surjective {n} X with surj-nf (symp X)
... | w₀ , e₀ = CG.pauliWord u • w₀ , final
  where
  open Eq.≡-Reasoning
  W  = symp ⟦ w₀ ⟧ᵛ
  φ₀ = phase ⟦ w₀ ⟧ᵛ

  e : W ≈ˢ symp X
  e P = Eq.trans (symp-⟦⟧ᵛ w₀ P) (e₀ P)

  -- The leftover, once the symplectic part is divided out.
  Y : Cliff n
  Y = X ∙ᵛ (⟦ w₀ ⟧ᵛ ⁻¹ᵛ)

  Y-triv : symp Y ≈ˢ εˢ
  Y-triv P = Eq.trans (Eq.sym (e (ap⁻¹ W P))) (invʳ W P)

  u : Pauli n
  u = proj₁ (ker⊆im-incl Y Y-triv)

  incl-u : incl u ≈ᵛ Y
  incl-u = proj₂ (ker⊆im-incl Y Y-triv)

  -- Multiplying the circuit back on the right undoes the division.
  cancel : (Y ∙ᵛ ⟦ w₀ ⟧ᵛ) ≈ᵛ X
  cancel = (λ P → Eq.cong (ap (symp X)) (invˡ W P)) , cancel-phase
    where
    cancel-phase : (P : Pauli n) → phase (Y ∙ᵛ ⟦ w₀ ⟧ᵛ) P ≡ phase X P
    cancel-phase P = begin
      φ₀ P + ((- φ₀ (ap⁻¹ W (ap W P))) + phase X (ap⁻¹ W (ap W P)))
        ≡⟨ Eq.cong (λ □ → φ₀ P + ((- φ₀ □) + phase X □)) (invˡ W P) ⟩
      φ₀ P + ((- φ₀ P) + phase X P)
        ≡⟨ Eq.sym (+-assoc (φ₀ P) (- φ₀ P) (phase X P)) ⟩
      (φ₀ P + - φ₀ P) + phase X P
        ≡⟨ Eq.cong (_+ phase X P) (+-inverseʳ (φ₀ P)) ⟩
      ₀ + phase X P
        ≡⟨ +-identityˡ (phase X P) ⟩
      phase X P   ∎

  final : ⟦ CG.pauliWord u • w₀ ⟧ᵛ ≈ᵛ X
  final = ≈ᵛ-trans ⟦ CG.pauliWord u • w₀ ⟧ᵛ (Y ∙ᵛ ⟦ w₀ ⟧ᵛ) X
    (∙ᵛ-cong {X = ⟦ CG.pauliWord u ⟧ᵛ} {Y} {⟦ w₀ ⟧ᵛ} {⟦ w₀ ⟧ᵛ}
             (≈ᵛ-trans ⟦ CG.pauliWord u ⟧ᵛ (incl u) Y (pauliWord-incl u) incl-u)
             (≈ᵛ-refl ⟦ w₀ ⟧ᵛ))
    cancel

------------------------------------------------------------------------
-- The isomorphism

module _ (n : ℕ) where

  open MonoidMorphisms (Group.rawMonoid (CG.CMS-group n))
                       (Group.rawMonoid (VSp-group n))
    using (IsMonoidHomomorphism)
  open GroupMorphisms (Group.rawGroup (CG.CMS-group n))
                      (Group.rawGroup (VSp-group n))
    using (IsGroupIsomorphism)

  -- Concatenation of words is multiplication of pairs, on the nose.
  ⟦⟧ᵛ-isMonoidHomomorphism : IsMonoidHomomorphism ⟦_⟧ᵛ
  ⟦⟧ᵛ-isMonoidHomomorphism = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = λ {w} {v} → ⟦⟧ᵛ-cong {n} {w} {v} }
      ; homo              = λ w v → ≈ᵛ-refl ⟦ w • v ⟧ᵛ
      }
    ; ε-homo = ≈ᵛ-refl (εᵛ {n})
    }

  CMS≅VSp : IsGroupIsomorphism ⟦_⟧ᵛ
  CMS≅VSp = record
    { isGroupMonomorphism = record
      { isGroupHomomorphism = isMonoidHomomorphism⇒isGroupHomomorphism
          (CG.CMS-group n) (VSp-group n) ⟦⟧ᵛ-isMonoidHomomorphism
      ; injective = λ {w} {v} → ⟦⟧ᵛ-injective {n} {w} {v}
      }
    ; surjective = λ X → proj₁ (⟦⟧ᵛ-surjective X)
                       , λ {z} z≈w →
                           ≈ᵛ-trans ⟦ z ⟧ᵛ ⟦ proj₁ (⟦⟧ᵛ-surjective X) ⟧ᵛ X
                             (⟦⟧ᵛ-cong {n} {z} {proj₁ (⟦⟧ᵛ-surjective X)} z≈w)
                             (proj₂ (⟦⟧ᵛ-surjective X))
    }
