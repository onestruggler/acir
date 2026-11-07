------------------------------------------------------------------------
-- Presentations of groups
--
-- Groups of matrices over a subring of 𝔻[ω], as subgroups of Uₙ(𝔻[ω])
--
-- An injective ring homomorphism ι : A → 𝔻[ω] that commutes with the
-- conjugation (EucDomain's Quantum.Synthesis.Ring.Properties.Embedding
-- has those of 𝔻, 𝔻[i] and 𝔻[√2]) maps matrices entrywise
-- (EucDomain's Quantum.Synthesis.Matrix.Map): injectively, and
-- preserving products, adjoints and the identity, so unitary matrices
-- over A to unitary matrices over 𝔻[ω] (embed-unitary).  So a group G
-- of unitary matrices over A — Oₙ(𝔻), Uₙ(𝔻[i]), Oₙ(𝔻[√2]), the scaled
-- dyadic group Lₙ — embeds in Uₙ(𝔻[ω]) (Group-Embedding.mono), and a
-- presentation of G is a sub-presentation of Uₙ(𝔻[ω]), whose
-- interpretation is ι applied to the entries of the old one, with the
-- same soundness and completeness (Presentation.Embedding.along).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Instances using (Ring ; Adjoint ; adj ; _+_ ; _*_ ; -_ ; 0# ; 1#)
open import Quantum.Synthesis.Ring.Properties.Hom using (IsInvolutiveRingEndo)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring using (D ; SemiRingD ; RingD ; AdjointD)

module Examples.Groups.Clifford+T-2qubit-TwoLevel.Subring
  {A : Set} {{RA : Ring A}} {{AA : Adjoint A}}
  (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
  (adjI : IsInvolutiveRingEndo {A} adj)
  (ι : A → D)
  (ι-+ : ∀ x y → ι (x + y) ≡ ι x + ι y)
  (ι-* : ∀ x y → ι (x * y) ≡ ι x * ι y)
  (ι-0 : ι 0# ≡ 0#)
  (ι-1 : ι 1# ≡ 1#)
  (ι-adj : ∀ x → ι (adj x) ≡ adj (ι x))
  (ι-injective : ∀ {x y} → ι x ≡ ι y → x ≡ y)
  where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module MonoidMorphisms ; module GroupMorphisms)
open import Data.Fin.Base using (Fin)
import Data.Fin.Properties as FinP
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_ ; _,_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (refl ; cong ; sym ; trans)
open import Relation.Nullary using (Dec ; yes ; no)

open import Quantum.Synthesis.Matrix using (Matrix ; matrix-map ; _·*·_ ; adjoint)
import Quantum.Synthesis.Matrix.Map as Map
open import ForStdlib.Algebra.Morphism.Consequences using (isMonoidHomomorphism⇒isGroupHomomorphism)

open import Word.Base using (WRel)
open import Presentation.Definitions using (_IsPresentationOf_ ; _IsSubPresentationOf_)
import Presentation.Embedding as PE

import Examples.Groups.Clifford+CS-TwoLevel.MatrixAlgebra as MatrixAlgebra
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics
  using (U ; UMat ; Unitary ; 𝕀 ; ent ; mat-ext ; ent-𝕀 ; δ ; δ-refl ; δ-≢)

-- The matrices over A.
module MA = MatrixAlgebra isCR adjI

private
  variable
    m n p : ℕ

------------------------------------------------------------------------
-- Matrices

embed : Matrix m n A → Matrix m n D
embed = matrix-map ι

ent-embed : (M : Matrix m n A) (r : Fin m) (c : Fin n) → ent (embed M) r c ≡ ι (MA.ent M r c)
ent-embed = Map.matrix-map-lookup ι

embed-injective : {M N : Matrix m n A} → embed M ≡ embed N → M ≡ N
embed-injective = Map.matrix-map-injective ι-injective

embed-·*· : (M : Matrix m n A) (N : Matrix n p A) → embed (M ·*· N) ≡ embed M ·*· embed N
embed-·*· = Map.matrix-map-·*· ι ι-+ ι-* ι-0

embed-adjoint : (M : Matrix m n A) → embed (adjoint M) ≡ adjoint (embed M)
embed-adjoint = Map.matrix-map-adjoint ι ι-adj

embed-𝕀 : embed (MA.𝕀 {n}) ≡ 𝕀
embed-𝕀 = mat-ext λ r c → trans (ent-embed MA.𝕀 r c) (trans (cong ι (MA.ent-𝕀 r c)) (trans (ι-δ r c) (sym (ent-𝕀 r c))))
  where
  ι-δ : (r c : Fin n) → ι (MA.δ r c) ≡ δ r c
  ι-δ r c = by (r FinP.≟ c)
    where
    by : Dec (r ≡ c) → ι (MA.δ r c) ≡ δ r c
    by (yes refl) = trans (cong ι (MA.δ-refl r)) (trans ι-1 (sym (δ-refl r)))
    by (no ne) = trans (cong ι (MA.δ-≢ ne)) (trans ι-0 (sym (δ-≢ ne)))

-- Unitary matrices over A, as in Clifford+CS-TwoLevel.Unitary.
UnitaryA : Matrix n n A → Set
UnitaryA M = (adjoint M ·*· M ≡ MA.𝕀) × (M ·*· adjoint M ≡ MA.𝕀)

embed-unitary : {M : Matrix n n A} → UnitaryA M → Unitary (embed M)
embed-unitary {M = M} (u₁ , u₂) =
  trans (cong (_·*· embed M) (sym (embed-adjoint M)))
        (trans (sym (embed-·*· (adjoint M) M)) (trans (cong embed u₁) embed-𝕀)) ,
  trans (cong (embed M ·*·_) (sym (embed-adjoint M)))
        (trans (sym (embed-·*· M (adjoint M))) (trans (cong embed u₂) embed-𝕀))

------------------------------------------------------------------------
-- Groups

-- A group G whose elements are read as unitary N × N matrices over A,
-- faithfully and multiplicatively, is a subgroup of U_N(𝔻[ω]).
module Group-Embedding
  (G : Group 0ℓ 0ℓ) (N : ℕ)
  (mat : Group.Carrier G → Matrix N N A)
  (unitary : ∀ x → UnitaryA (mat x))
  (≈⇒≡ : ∀ {x y} → Group._≈_ G x y → mat x ≡ mat y)
  (≡⇒≈ : ∀ {x y} → mat x ≡ mat y → Group._≈_ G x y)
  (mat-∙ : ∀ x y → mat (Group._∙_ G x y) ≡ mat x ·*· mat y)
  (mat-ε : mat (Group.ε G) ≡ MA.𝕀)
  where

  -- The matrix of an element of G, over 𝔻[ω].
  φ : Group.Carrier G → UMat N
  φ x = embed (mat x) , embed-unitary (unitary x)

  open MonoidMorphisms (Group.rawMonoid G) (Group.rawMonoid (U N)) using (IsMonoidHomomorphism)
  open GroupMorphisms (Group.rawGroup G) (Group.rawGroup (U N)) using (IsGroupMonomorphism)

  mono : IsGroupMonomorphism φ
  mono = record
    { isGroupHomomorphism = isMonoidHomomorphism⇒isGroupHomomorphism G (U N) hom
    ; injective = λ e → ≡⇒≈ (embed-injective e)
    }
    where
    hom : IsMonoidHomomorphism φ
    hom = record
      { isMagmaHomomorphism = record
        { isRelHomomorphism = record { cong = λ e → cong embed (≈⇒≡ e) }
        ; homo = λ x y → trans (cong embed (mat-∙ x y)) (embed-·*· (mat x) (mat y))
        }
      ; ε-homo = trans (cong embed mat-ε) embed-𝕀
      }

  -- A (sub-)presentation of G is a sub-presentation of U_N(𝔻[ω]).
  module _ {X : Set} {_===_ : WRel X} where

    along : _===_ IsSubPresentationOf G → _===_ IsSubPresentationOf U N
    along = PE.along mono

    along-presentation : _===_ IsPresentationOf G → _===_ IsSubPresentationOf U N
    along-presentation = PE.along-presentation mono
