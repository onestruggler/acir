------------------------------------------------------------------------
-- Presentations of groups
--
-- R1–R16 present the real Clifford group (the paper's main theorem)
--
-- Take any nontrivial commutative ring A with an involution adj that
-- fixes an element s with s s + s s = 1 (s = 1/√2 in ℝ or ℂ).  A real
-- Clifford circuit on n wires denotes a unitary 2ⁿ × 2ⁿ matrix over A:
-- −1, H = s [[1 , 1] , [1 , −1]], Z and CZ have entries that adj fixes
-- and are symmetric, so the conjugate transpose of the matrix of a
-- circuit is the matrix of the circuit reversed, its inverse.  Then
--
-- * sound: related circuits have the same matrix (Soundness);
-- * complete: circuits with the same matrix are related (Completeness);
--
-- so R1–R16 present the subgroup of U_{2ⁿ}(A) that −1, H, Z and CZ
-- generate: the real Clifford group on n qubits.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_)
open import Instances using (Ring ; Adjoint ; adj ; _+_ ; _*_ ; -_ ; 0# ; 1#)
open import Quantum.Synthesis.Ring.Properties.Hom using (IsInvolutiveRingEndo)

module Examples.Groups.Real-Clifford.Presentation
  {A : Set} {{RA : Ring A}} {{AA : Adjoint A}}
  (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
  (adjI : IsInvolutiveRingEndo {A} adj)
  (s : A) (s-half : s * s + s * s ≡ 1#) (adj-s : adj s ≡ s)
  (nontrivial : 1# ≢ 0#)
  where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module MonoidMorphisms)
open import Data.Bool.Base using (true)
open import Data.Integer.Base as ℤ using (ℤ ; +_ ; -[1+_])
open import Data.Nat.Base using (ℕ ; zero ; suc ; _^_)
open import Data.Product.Base using (_,_)
import Relation.Binary.PropositionalEquality as Eq

open import ForStdlib.Algebra.Morphism.Consequences using (isMonoidHomomorphism⇒isGroupHomomorphism)
open import Presentation.GroupLike using (module Group-Lemmas)
open import Presentation.Definitions using (_IsSubPresentationOf_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Examples.Groups.Real-Clifford.Syntactics
open import Examples.Groups.Real-Clifford.Pauli using (inv)
open import Examples.Groups.Real-Clifford.Semantics.Laws isCR hiding (mat)
open import Examples.Groups.Real-Clifford.Semantics.Interpretation isCR s s-half
  using (ι ; module ZS ; module ZI ; ιO ; scale ; hZ ; zZ ; czZ ; valA ; ⟦_⟧ᴬ ; check ; check-sound)
open import Examples.Groups.Real-Clifford.Semantics.Soundness isCR s s-half using (sound)
open import Examples.Groups.Real-Clifford.Semantics.Completeness isCR s s-half nontrivial
  using (inv-r ; completeness)
open import Examples.Groups.Real-Clifford.Semantics.Matrix isCR adjI
  using ( mat ; mat-≐ ; mat-⊙ ; mat-Id ; mat-injective ; UMat ; U ; Unitary-mat
        ; Symmetric ; adj-⊙ ; δb-sym ; tensor-sym )
open import Examples.Groups.Clifford+CS-TwoLevel.MatrixAlgebra isCR adjI
  using (adj-+ ; adj-* ; adj-0 ; adj-1 ; adj-neg)

private
  variable
    k n : ℕ

------------------------------------------------------------------------
-- The gates are symmetric, with entries that adj fixes

private
  adj-ι⁺ : (n : ℕ) → adj (ι (+ n)) ≡ ι (+ n)
  adj-ι⁺ zero    = adj-0
  adj-ι⁺ (suc n) = Eq.trans (Eq.cong adj (ZS.+-homoℤ (+ 1) (+ n)))
    (Eq.trans (adj-+ (ι (+ 1)) (ι (+ n)))
    (Eq.trans (Eq.cong₂ _+_ adj-1 (adj-ι⁺ n)) (Eq.sym (ZS.+-homoℤ (+ 1) (+ n)))))

  adj-ι : (k : ℤ) → adj (ι k) ≡ ι k
  adj-ι (+ n)    = adj-ι⁺ n
  adj-ι -[1+ n ] = Eq.trans (Eq.cong adj (ZS.-‿homoℤ (+ suc n)))
    (Eq.trans (adj-neg (ι (+ suc n)))
    (Eq.trans (Eq.cong -_ (adj-ι⁺ (suc n))) (Eq.sym (ZS.-‿homoℤ (+ suc n)))))

  -- A symmetric integer matrix, checked by evaluation.
  symℤ : (M : ZI.Mat k) → check 0 M (ZI.matOf λ x y → ZI.ix M y x) ≡ true →
         ∀ x y → ZI.ix M x y ≡ ZI.ix M y x
  symℤ M e x y = Eq.trans (check-sound 0 M _ e x y) (ZI.ix-matOf (λ x y → ZI.ix M y x) x y)

  ιO-sym : (M : ZI.Mat k) → (∀ x y → ZI.ix M x y ≡ ZI.ix M y x) → Symmetric (ιO (ZI.ix M))
  ιO-sym M e x y = Eq.trans (adj-ι (ZI.ix M x y)) (Eq.cong ι (e x y))

  scale-sym : {M : Op k} → Symmetric M → Symmetric (scale s M)
  scale-sym {M = M} e x y = Eq.trans (adj-* s (M x y)) (Eq.cong₂ _*_ adj-s (e x y))

valA-sym : (g : Gen n) → Symmetric (valA g)
valA-sym (gate₀ neg-gate) x y =
  Eq.trans (adj-* (- 1#) (δb x y)) (Eq.cong₂ _*_ (Eq.trans (adj-neg 1#) (Eq.cong -_ adj-1)) (δb-sym x y))
valA-sym (gate₁ H-gate) = tensor-sym {M = scale s (ιO (ZI.ix hZ))} {N = Idₒ}
  (scale-sym {M = ιO (ZI.ix hZ)} (ιO-sym hZ (symℤ hZ Eq.refl))) δb-sym
valA-sym (gate₁ Z-gate) = tensor-sym {M = ιO (ZI.ix zZ)} {N = Idₒ} (ιO-sym zZ (symℤ zZ Eq.refl)) δb-sym
valA-sym (gate₂ CZ-gate) = tensor-sym {M = ιO (ZI.ix czZ)} {N = Idₒ} (ιO-sym czZ (symℤ czZ Eq.refl)) δb-sym
valA-sym (g ↥) = tensor-sym {M = Idₒ {1}} {N = valA g} δb-sym (valA-sym g)

-- The conjugate transpose of the matrix of a circuit is the matrix of
-- the circuit reversed.
⟦⟧-adj : (w : Circuit n) → ∀ x y → adj (⟦ w ⟧ᴬ x y) ≡ ⟦ inv w ⟧ᴬ y x
⟦⟧-adj [ g ]ʷ  = valA-sym g
⟦⟧-adj ε       = δb-sym
⟦⟧-adj (w • v) = adj-⊙ ⟦ w ⟧ᴬ ⟦ v ⟧ᴬ ⟦ inv w ⟧ᴬ ⟦ inv v ⟧ᴬ (⟦⟧-adj w) (⟦⟧-adj v)

-- The circuit reversed is the inverse on either side.
private
  inv-inv : (w : Circuit n) → inv (inv w) ≡ w
  inv-inv [ g ]ʷ  = Eq.refl
  inv-inv ε       = Eq.refl
  inv-inv (w • v) = Eq.cong₂ _•_ (inv-inv w) (inv-inv v)

inv-l : (w : Circuit n) → n ⊢ inv w • w ≈ ε
inv-l {n} w = Eq.subst (λ u → n ⊢ inv w • u ≈ ε) (inv-inv w) (inv-r (inv w))

------------------------------------------------------------------------
-- The matrix of a circuit

-- It is unitary, its inverse being the matrix of the circuit reversed.
⟦_⟧ᵘ : {n : ℕ} → Circuit n → UMat (2 ^ n)
⟦_⟧ᵘ w = mat ⟦ w ⟧ᴬ , Unitary-mat ⟦ w ⟧ᴬ ⟦ inv w ⟧ᴬ (⟦⟧-adj w) (sound (inv-l w)) (sound (inv-r w))

------------------------------------------------------------------------
-- The presentation

-- ⟦_⟧ᵘ is a group monomorphism from the circuits modulo R1–R16 to
-- U_{2ⁿ}(A).
presentation : {n : ℕ} → (n VRel,_===_) IsSubPresentationOf U (2 ^ n)
presentation {n} = record
  { gl = grouplike
  ; ⟦_⟧ = ⟦_⟧ᵘ
  ; mono = record
    { isGroupHomomorphism =
        isMonoidHomomorphism⇒isGroupHomomorphism GL.•-ε-group (U (2 ^ n)) isMonoidHomomorphism
    ; injective = λ {w} {v} e → completeness (mat-injective {M = ⟦ w ⟧ᴬ} {N = ⟦ v ⟧ᴬ} e)
    }
  }
  where
  module GL = Group-Lemmas (n VRel,_===_) grouplike
  open MonoidMorphisms (Group.rawMonoid GL.•-ε-group) (Group.rawMonoid (U (2 ^ n)))
  isMonoidHomomorphism : IsMonoidHomomorphism ⟦_⟧ᵘ
  isMonoidHomomorphism = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = λ e → mat-≐ (sound e) }
      ; homo = λ w v → mat-⊙ ⟦ w ⟧ᴬ ⟦ v ⟧ᴬ
      }
    ; ε-homo = mat-Id {n}
    }
