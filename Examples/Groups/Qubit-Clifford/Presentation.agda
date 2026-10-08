------------------------------------------------------------------------
-- Presentations of groups
--
-- C1–C15 present the Clifford group (the paper's Proposition 7.1)
--
-- Take any nontrivial commutative ring A with an involution adj, an
-- element s with s s + s s = 1 that adj fixes (s = 1/√2 in ℂ), and an
-- element i with i i = −1 that adj negates.  A Clifford circuit on n
-- wires denotes a unitary 2ⁿ × 2ⁿ matrix over A: the conjugate
-- transpose of the matrix of a circuit is the matrix of its inverse
-- word (Inverse), since H and CZ are symmetric with entries that adj
-- fixes, the conjugate transpose of S is S³, and adj ω = ω⁷.  Then
--
-- * sound: related circuits have the same matrix (Soundness);
-- * complete: circuits with the same matrix are related (Completeness);
--
-- so C1–C15 present the subgroup of U_{2ⁿ}(A) that ω, H, S and CZ
-- generate: the Clifford group on n qubits.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_)
open import Instances using (Ring ; Adjoint ; adj ; _+_ ; _*_ ; -_ ; 0# ; 1#)
open import Quantum.Synthesis.Ring.Properties.Hom using (IsInvolutiveRingEndo)

module Examples.Groups.Qubit-Clifford.Presentation
  {A : Set} {{RA : Ring A}} {{AA : Adjoint A}}
  (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
  (adjI : IsInvolutiveRingEndo {A} adj)
  (s : A) (s-half : s * s + s * s ≡ 1#) (adj-s : adj s ≡ s)
  (i : A) (i² : i * i ≡ - 1#) (adj-i : adj i ≡ - i)
  (nontrivial : 1# ≢ 0#)
  where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module MonoidMorphisms)
open import Data.Bool.Base using (Bool ; true ; false ; _∧_)
open import Data.Integer.Base as ℤ using (ℤ ; +_ ; -[1+_])
open import Data.Nat.Base using (ℕ ; zero ; suc ; _^_)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (refl)
open import Relation.Nullary using (yes ; no ; does)

open import ForStdlib.Algebra.Morphism.Consequences using (isMonoidHomomorphism⇒isGroupHomomorphism)
open import Presentation.GroupLike using (module Group-Lemmas)
open import Presentation.Definitions using (_IsSubPresentationOf_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_) renaming (_^_ to _^ʷ_)

open import Examples.Groups.Qubit-Clifford.Syntactics
open import Examples.Groups.Qubit-Clifford.Inverse using (invL ; inv ; inv-l ; inv-r)
open import Examples.Groups.Qubit-Clifford.Semantics.Gauss using (ℤi ; _+i_ ; conjᵍ ; _≟ᵍ_)
open import Examples.Groups.Qubit-Clifford.Semantics.Interpretation isCR s s-half i i²
  hiding (mat) renaming (_^_ to _^ᴬ_)
open ZS using (solve ; _:=_ ; _:+_ ; _:*_ ; :-_ ; con)
open import Examples.Groups.Qubit-Clifford.Semantics.Soundness isCR s s-half i i² using (sound ; ⟦↑⟧)
open import Examples.Groups.Qubit-Clifford.Semantics.Completeness isCR s s-half i i² nontrivial
  using (completeness)
open import Examples.Groups.Qubit-Clifford.Semantics.Scalars isCR s s-half i i² using (ω̂-even ; ⟦ω^⟧)
open import Examples.Groups.Real-Clifford.Semantics.Matrix isCR adjI
  using ( mat ; mat-≐ ; mat-⊙ ; mat-Id ; mat-injective ; UMat ; U ; Unitary-mat
        ; adj-⊙ ; δb-sym ; tensor-adj )
open import Examples.Groups.Clifford+CS-TwoLevel.MatrixAlgebra isCR adjI
  using (adj-+ ; adj-* ; adj-0 ; adj-1 ; adj-neg)

private
  variable
    k n : ℕ

------------------------------------------------------------------------
-- adj on the images of integers and Gaussian integers

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

  adj-ιᵍ : (z : ℤi) → adj (ιᵍ z) ≡ ιᵍ (conjᵍ z)
  adj-ιᵍ (a +i b) = begin
    adj (ι a + i * ι b)             ≡⟨ adj-+ (ι a) (i * ι b) ⟩
    adj (ι a) + adj (i * ι b)       ≡⟨ Eq.cong (λ u → adj (ι a) + u) (adj-* i (ι b)) ⟩
    adj (ι a) + adj i * adj (ι b)   ≡⟨ Eq.cong₂ (λ u v → u + v * adj (ι b)) (adj-ι a) adj-i ⟩
    ι a + (- i) * adj (ι b)         ≡⟨ Eq.cong (λ u → ι a + (- i) * u) (adj-ι b) ⟩
    ι a + (- i) * ι b               ≡⟨ solve 3 (λ a i b → a :+ (:- i) :* b := a :+ i :* (:- b)) refl (ι a) i (ι b) ⟩
    ι a + i * (- ι b)               ≡⟨ Eq.cong (λ u → ι a + i * u) (Eq.sym (ZS.-‿homoℤ b)) ⟩
    ι a + i * ι (ℤ.- b)             ∎
    where open Eq.≡-Reasoning

  -- Gaussian matrices, one the conjugate transpose of the other,
  -- checked by evaluation.
  cadj? : GI.Mat k → GI.Mat k → Bool
  cadj? {k} M N = allBits k λ x → allBits k λ y → does (conjᵍ (GI.ix M x y) ≟ᵍ GI.ix N y x)

  cadj-sound : (M N : GI.Mat k) → cadj? M N ≡ true → ∀ x y → conjᵍ (GI.ix M x y) ≡ GI.ix N y x
  cadj-sound {k} M N e x y with conjᵍ (GI.ix M x y) ≟ᵍ GI.ix N y x
      | allBits-sound k _ (allBits-sound k _ e x) y
  ... | yes p | _  = p
  ... | no _  | ()

  gauss-adj : (M N : GI.Mat k) → cadj? M N ≡ true → ∀ x y → adj (ιO (GI.ix M) x y) ≡ ιO (GI.ix N) y x
  gauss-adj M N e x y = Eq.trans (adj-ιᵍ (GI.ix M x y)) (Eq.cong ιᵍ (cadj-sound M N e x y))

  ιO-mul : (M N : GI.Mat k) → ιO (GI.ix (GI.mulM M N)) ≐ (ιO (GI.ix M) ⊙ ιO (GI.ix N))
  ιO-mul M N x y = Eq.trans (Eq.cong ιᵍ (GI.ix-matOf (GI.ix M GI.⊙ GI.ix N) x y)) (ιO-⊙ (GI.ix M) (GI.ix N) x y)

------------------------------------------------------------------------
-- The conjugate transposes of the gates

private
  -- adj ω = ω⁷.
  adj-ω̂ : adj ω̂ ≡ ω̂ ^ᴬ 7
  adj-ω̂ = begin
    adj (s * (1# + i))                ≡⟨ adj-* s (1# + i) ⟩
    adj s * adj (1# + i)              ≡⟨ Eq.cong₂ _*_ adj-s (Eq.trans (adj-+ 1# i) (Eq.cong₂ _+_ adj-1 adj-i)) ⟩
    s * (1# + - i)                    ≡⟨ solve 2 (λ s i → s :* (con (+ 1) :+ :- i)
                                              := s :* (con (+ 1) :+ i) :* (con (+ 0) :+ i :* :- con (+ 1))
                                                 :+ s :* (i :* i :+ con (+ 1)))
                                           refl s i ⟩
    ω̂ * (0# + i * - 1#) + s * (i * i + 1#)
                                      ≡⟨ Eq.cong (λ u → ω̂ * (0# + i * - 1#) + s * u) i²+1 ⟩
    ω̂ * (0# + i * - 1#) + s * 0#      ≡⟨ solve 3 (λ w i s → w :* (con (+ 0) :+ i :* :- con (+ 1)) :+ s :* con (+ 0)
                                              := w :* (con (+ 0) :+ i :* :- con (+ 1)))
                                           refl ω̂ i s ⟩
    ω̂ * (0# + i * - 1#)               ≡⟨ Eq.cong (ω̂ *_) (Eq.sym (ω̂-even 3)) ⟩
    ω̂ ^ᴬ 7                            ∎
    where open Eq.≡-Reasoning

  H₁ S₁ : Op 1
  H₁ = scale s (ιO (GI.ix hG))
  S₁ = ιO (GI.ix sG)

  CZ₂ : Op 2
  CZ₂ = ιO (GI.ix czG)

  adj-H₁ : ∀ x y → adj (H₁ x y) ≡ H₁ y x
  adj-H₁ x y = Eq.trans (adj-* s _) (Eq.cong₂ _*_ adj-s (gauss-adj hG hG refl x y))

  -- S³ = S⁻¹, as an operator on one wire.
  S₃ : Op 1
  S₃ = S₁ ⊙ (S₁ ⊙ S₁)

  adj-S₁ : ∀ x y → adj (S₁ x y) ≡ S₃ y x
  adj-S₁ x y = Eq.trans (gauss-adj sG (GI.mulM sG (GI.mulM sG sG)) refl x y)
    (≐-trans (ιO-mul sG (GI.mulM sG sG)) (⊙-cong (≐-refl S₁) (ιO-mul sG sG)) y x)

  ⟦S³⟧ : ⟦ S {n} • S • S ⟧ᴬ ≐ emb {1} {n} S₃
  ⟦S³⟧ = ≐-trans (⊙-cong (≐-refl (emb S₁)) (emb-⊙ S₁ S₁)) (emb-⊙ S₁ (S₁ ⊙ S₁))

valA-adj : (g : Gen n) → ∀ x y → adj (valA g x y) ≡ ⟦ invL g ⟧ᴬ y x
valA-adj (gate₀ ω-gate) x y = begin
  adj (ω̂ * δb x y)          ≡⟨ adj-* ω̂ (δb x y) ⟩
  adj ω̂ * adj (δb x y)      ≡⟨ Eq.cong₂ _*_ adj-ω̂ (δb-sym x y) ⟩
  ω̂ ^ᴬ 7 * δb y x           ≡⟨ Eq.sym (⟦ω^⟧ 7 y x) ⟩
  ⟦ ω ^ʷ 7 ⟧ᴬ y x           ∎
  where open Eq.≡-Reasoning
valA-adj (gate₁ H-gate) = tensor-adj {M = H₁} {M' = H₁} {N = Idₒ} {N' = Idₒ} adj-H₁ δb-sym
valA-adj (gate₁ S-gate) x y = Eq.trans (tensor-adj {M = S₁} {M' = S₃} {N = Idₒ} {N' = Idₒ} adj-S₁ δb-sym x y)
  (Eq.sym (⟦S³⟧ y x))
valA-adj (gate₂ CZ-gate) = tensor-adj {M = CZ₂} {M' = CZ₂} {N = Idₒ} {N' = Idₒ} (gauss-adj czG czG refl) δb-sym
valA-adj (g ↥) x y =
  Eq.trans (tensor-adj {M = Idₒ {1}} {M' = Idₒ} {N = valA g} {N' = ⟦ invL g ⟧ᴬ} δb-sym (valA-adj g) x y)
    (Eq.sym (⟦↑⟧ (invL g) y x))

-- The conjugate transpose of the matrix of a circuit is the matrix of
-- its inverse.
⟦⟧-adj : (w : Circuit n) → ∀ x y → adj (⟦ w ⟧ᴬ x y) ≡ ⟦ inv w ⟧ᴬ y x
⟦⟧-adj [ g ]ʷ  = valA-adj g
⟦⟧-adj ε       = δb-sym
⟦⟧-adj (w • v) = adj-⊙ ⟦ w ⟧ᴬ ⟦ v ⟧ᴬ ⟦ inv w ⟧ᴬ ⟦ inv v ⟧ᴬ (⟦⟧-adj w) (⟦⟧-adj v)

------------------------------------------------------------------------
-- The matrix of a circuit

-- It is unitary, its inverse being the matrix of the inverse word.
⟦_⟧ᵘ : {n : ℕ} → Circuit n → UMat (2 ^ n)
⟦_⟧ᵘ w = mat ⟦ w ⟧ᴬ , Unitary-mat ⟦ w ⟧ᴬ ⟦ inv w ⟧ᴬ (⟦⟧-adj w) (sound (inv-l w)) (sound (inv-r w))

------------------------------------------------------------------------
-- The presentation

-- ⟦_⟧ᵘ is a group monomorphism from the circuits modulo C1–C15 to
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
