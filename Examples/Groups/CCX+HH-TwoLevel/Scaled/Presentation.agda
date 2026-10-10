------------------------------------------------------------------------
-- Presentations of groups
--
-- The relations of Tables 1 and 2 present Lₙ, the group of orthogonal
-- scaled dyadic matrices (Definition 5.1), for n = 2(k + 1)
-- (Theorems 5.4 and 5.7).
--
-- * ⟦_⟧ᴸ is a homomorphism, and respects the relations (Theorem 5.4);
-- * it is onto: a scaled dyadic M = N / √2ʲ with j even is the image
--   of an orthogonal matrix over ℤ[1/2], hence the matrix of a word
--   over 𝒢ₙ by Algorithm 1; with j odd, M (I⊗H) is scaled dyadic with
--   exponent j + 1, so M is the matrix of such a word times I ⊗ H;
-- * it is one-to-one on words modulo the relations (Theorem 5.7).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)

module Examples.Groups.CCX+HH-TwoLevel.Scaled.Presentation (k : ℕ) where

open import Algebra.Bundles using (Group)
open import Data.Product.Base using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
import Data.Nat.Properties as ℕP
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality

open import Quantum.Synthesis.Matrix using (Matrix ; _·*·_ ; adjoint)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
import Presentation.Base as PB
open import Presentation.Definitions
  using (_IsMonoidPresentationOf_ ; _IsPresentationOf_ ; monoidPresentation⇒presentation)
open import Presentation.GroupLike using (Grouplike)
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics using (Gen)
open import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics
open import Examples.Groups.CCX+HH-TwoLevel.Scaled.Normal k using (n)
import Examples.Groups.CCX+HH-TwoLevel.Ring as R1
import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring as R2
open import Examples.Groups.CCX+HH-TwoLevel.Scaled.Ring using (D ; e ; e-* ; e-injective ; module DR)
open import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics
open import Examples.Groups.CCX+HH-TwoLevel.Scaled.Dyadic
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Completeness k as C
import Examples.Groups.CCX+HH-TwoLevel.Semantics as S1
import Examples.Groups.CCX+HH-TwoLevel.Scale as Sc
import Examples.Groups.CCX+HH-TwoLevel.Presentation as P1
import Examples.Groups.CCX+HH-TwoLevel.Derived as Der

open Dim (suc k)

------------------------------------------------------------------------
-- The group Lₙ

LMat : Set
LMat = Σ (Matrix n n D) λ M → Unitary M × ScaledDyadic M

L : Group 0ℓ 0ℓ
L = record
  { Carrier = LMat
  ; _≈_     = λ A B → proj₁ A ≡ proj₁ B
  ; _∙_     = λ A B → proj₁ A ·*· proj₁ B , Unitary-·*· (proj₁ (proj₂ A)) (proj₁ (proj₂ B)) ,
                      SD-·*· {M = proj₁ A} {N = proj₁ B} (proj₂ (proj₂ A)) (proj₂ (proj₂ B))
  ; ε       = 𝕀 , Unitary-𝕀 , SD-𝕀
  ; _⁻¹     = λ A → adjoint (proj₁ A) , Unitary-adjoint (proj₁ (proj₂ A)) , SD-adjoint {M = proj₁ A} (proj₂ (proj₂ A))
  ; isGroup = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = record { refl = refl ; sym = sym ; trans = trans }
          ; ∙-cong = cong₂ _·*·_
          }
        ; assoc = λ A B C → ·*·-assoc (proj₁ A) (proj₁ B) (proj₁ C)
        }
      ; identity = (λ A → ·*·-identityˡ (proj₁ A)) , (λ A → ·*·-identityʳ (proj₁ A))
      }
    ; inverse = (λ A → proj₁ (proj₁ (proj₂ A))) , (λ A → proj₂ (proj₁ (proj₂ A)))
    ; ⁻¹-cong = cong adjoint
    }
  }

------------------------------------------------------------------------
-- Every element of Lₙ is the matrix of a word

private
  half : ∀ j → Σ ℕ (λ t → j ≡ dbl t) ⊎ Σ ℕ (λ t → j ≡ suc (dbl t))
  half zero = inj₁ (0 , refl)
  half (suc zero) = inj₂ (0 , refl)
  half (suc (suc j)) with half j
  ... | inj₁ (t , eq) = inj₁ (suc t , cong (λ m → suc (suc m)) eq)
  ... | inj₂ (t , eq) = inj₂ (suc t , cong (λ m → suc (suc m)) eq)

  -- With an even exponent: an orthogonal matrix over ℤ[1/2], embedded.
  even : (M : Matrix n n D) → Unitary M → ∀ t → (∀ r c → ent M r c ∈ₛ dbl t) →
         Σ (Word (Gen n)) λ w → ⟦ ⌊ w ⌋ʷ ⟧ᴸ ≡ M
  even M uM t f = w , trans (⟦⌊⌋⟧ (suc k) w) (trans (cong mapM (P1.word-of-correct (N , uN))) MN)
    where
    g : _ → _ → R1.D
    g r c = R1.ι (_∈ₛ_.num (f r c)) R1.DR.* (R1.½ᴰ Sc.^ᴰ t)
    N : Matrix n n R1.D
    N = S1.mk g
    MN : mapM N ≡ M
    MN = mat-ext λ r c →
      trans (ent-mapM N r c)
        (trans (cong e (S1.ent-mk g r c))
          (trans (e-* _ _) (trans (cong (ιᴰ (_∈ₛ_.num (f r c)) DR.*_) (e-½^ t)) (sym (_∈ₛ_.is (f r c))))))
    inj = Tr.mapM-injective e-injective
    uN : S1.Unitary N
    uN = inj (trans (mapM-·*· (adjoint N) N)
               (trans (cong₂ _·*·_ (trans (mapM-adjoint N) (cong adjoint MN)) MN) (trans (proj₁ uM) (sym mapM-𝕀)))) ,
         inj (trans (mapM-·*· N (adjoint N))
               (trans (cong₂ _·*·_ MN (trans (mapM-adjoint N) (cong adjoint MN))) (trans (proj₂ uM) (sym mapM-𝕀))))
    w = P1.word-of (N , uN)

  surj : (A : LMat) → Σ (Word (Genᴸ n)) λ w → ⟦ w ⟧ᴸ ≡ proj₁ A
  surj (M , uM , j , f) = by (half j)
    where
    by : Σ ℕ (λ t → j ≡ dbl t) ⊎ Σ ℕ (λ t → j ≡ suc (dbl t)) → Σ (Word (Genᴸ n)) λ w → ⟦ w ⟧ᴸ ≡ M
    by (inj₁ (t , eq)) = ⌊ proj₁ E ⌋ʷ , proj₂ E
      where
      E = even M uM t (λ r c → subst (ent M r c ∈ₛ_) eq (f r c))
    by (inj₂ (t , eq)) = (⌊ proj₁ E ⌋ʷ • H) , (begin
      ⟦ ⌊ proj₁ E ⌋ʷ • H ⟧ᴸ                  ≡⟨ ⟦•⟧ᴸ ⌊ proj₁ E ⌋ʷ H ⟩
      ⟦ ⌊ proj₁ E ⌋ʷ ⟧ᴸ ·*· ⟦ H ⟧ᴸ            ≡⟨ cong₂ _·*·_ (proj₂ E) (⟦g⟧ᴸ≡ IH) ⟩
      (M ·*· gmatIH) ·*· gmatIH              ≡⟨ ·*·-assoc M gmatIH gmatIH ⟩
      M ·*· (gmatIH ·*· gmatIH)              ≡⟨ cong (M ·*·_) gmatIH-invol ⟩
      M ·*· 𝕀                                ≡⟨ ·*·-identityʳ M ⟩
      M                                      ∎)
      where
      open ≡-Reasoning
      M′ = M ·*· gmatIH
      sd : ScaledDyadic M′
      sd = SD-·*· {M = M} {N = gmatIH} (j , f) (SD-gmatIH (suc k))
      exp : proj₁ sd ≡ dbl (suc t)
      exp = trans (cong (ℕ._+ 1) eq) (ℕP.+-comm (suc (dbl t)) 1)
      E = even M′ (Unitary-·*· uM Unitary-gmatIH) (suc t) (λ r c → subst (ent M′ r c ∈ₛ_) exp (proj₂ sd r c))

------------------------------------------------------------------------
-- The presentation

grouplikeᴸ : Grouplike (_===ᴸ_ {n})
grouplikeᴸ ⌊ g ⌋ = [ ⌊ g ⌋ ]ʷ , ⌊⌋-cong (Der.gen-gen g)
grouplikeᴸ IH = H , PB.axiom r7a

⟦_⟧ˡ : Word (Genᴸ n) → LMat
⟦ w ⟧ˡ = ⟦ w ⟧ᴸ , Unitary-⟦⟧ᴸ w , SD-⟦⟧ (suc k) w

monoidPresentation : (_===ᴸ_ {n}) IsMonoidPresentationOf (Group.monoid L)
monoidPresentation = record
  { ⟦_⟧ = ⟦_⟧ˡ
  ; iso = record
    { isMonoidMonomorphism = record
      { isMonoidHomomorphism = record
        { isMagmaHomomorphism = record
          { isRelHomomorphism = record { cong = soundness (suc k) }
          ; homo = ⟦•⟧ᴸ
          }
        ; ε-homo = refl
        }
      ; injective = C.completeness
      }
    ; surjective = λ A → proj₁ (surj A) , λ z≈ → trans (soundness (suc k) z≈) (proj₂ (surj A))
    }
  }

-- Tables 1 and 2 present Lₙ.
presentation : (_===ᴸ_ {n}) IsPresentationOf L
presentation = monoidPresentation⇒presentation monoidPresentation grouplikeᴸ
