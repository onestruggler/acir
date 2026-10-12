------------------------------------------------------------------------
-- Presentations of groups
--
-- Figure 4 presents a subgroup of O_{2ⁿ}(ℤ[1/√2])
--
-- CompletenessInduction states Theorem 8.9 as a sub-presentation of the
-- monoid Scaled-monoid n: a circuit is read as a scaled matrix
-- (ℓ , M), which denotes (1/√2)^ℓ · M, and that monoid has no
-- inverses.  Here the same theorem is a group sub-presentation into
-- the orthogonal group O (2 ^ n) of Real-Clifford+CH-TwoLevel, the
-- group that Hadamard-Pi's Figure 6 presents.
--
-- * A circuit's matrix is read over ℤ[1/√2] by the bridge's Φ
--   (Auxiliary.Bridge.Matrix), the basis vectors numbered in binary
--   (Real-Clifford's bits and idx).
-- * The matrix of each gate is symmetric, the involution of ℤ[1/√2] is
--   the identity, and each gate is its own inverse (order-H, order-Z,
--   order-CZ, order-CH), so the matrix of a gate is orthogonal; that of
--   a circuit is the product of its gates', and orthogonal too.
-- * Φ is injective up to _~_, since ι is injective and √2 is a unit,
--   so completeness, the module parameter, makes the reading
--   injective.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)
open import Examples.Groups.Real-Clifford+CH.Syntactics using (Circuit ; _⊢_≈_)
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)
open import Examples.Groups.Real-Clifford+CH.Semantics.Scaled using (_~_)

module Examples.Groups.Real-Clifford+CH.Orthogonal
  (complete : ∀ n {w v : Circuit n} → ⟦ w ⟧ ~ ⟦ v ⟧ → n ⊢ w ≈ v)
  where

open import Algebra.Bundles using (Group)
open import Data.Bool.Base using (true)
open import Data.Nat.Base using (zero ; suc ; _^_) renaming (_+_ to _+ℕ_)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_ ; refl ; cong ; cong₂ ; trans ; sym ; subst₂ ; module ≡-Reasoning)
open import Word.Base using ([_]ʷ ; ε ; _•_)

import Presentation.Base as PB
open import Presentation.GroupLike using (module Group-Lemmas)
open import Presentation.Definitions
  using (_IsSubPresentationOf_ ; _IsSubMonoidPresentationOf_ ; subMonoidPresentation⇒subPresentation)

open import Quantum.Synthesis.Matrix using (Matrix ; _·*·_ ; adjoint)

import Examples.Groups.Real-Clifford+CH.Semantics as S
import Examples.Groups.Real-Clifford+CH.Semantics.Ring as R
open import Examples.Groups.Real-Clifford+CH.Semantics.Decide using (eqM ; eqM-sound)
open import Examples.Groups.Real-Clifford+CH.Syntactics
  using (Gen ; gate₀ ; H-gen ; Z-gen ; CZ-gen ; CH-gen ; _↥ ; _VRel,_===_ ; grouplike)
open import Examples.Groups.Real-Clifford+CH.Interpretation
  using (⟦_⟧ᵍ ; ⟦_⟧ₒ ; len ; ⟦⟧ₒ-gen ; ⟦⟧ₒ-ε ; ⟦⟧ₒ-•)
open import Examples.Groups.Real-Clifford+CH.Soundness using (sound)
open import Examples.Groups.Real-Clifford+CH.Reverse using (rev≈⁻¹)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bridge.Ring
  using (toZ ; ι ; ι-* ; ι-√2^ ; √½^ ; √2^ᴰ ; √½√2^)
import Examples.Groups.Real-Clifford+CH.Auxiliary.Bridge.Matrix as BMatrix

open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring
  using ( D ; module DR ; SemiRingD ; RingD ; AdjointD ; isCommutativeRing-D ; adj-D
        ; adjᴰ-id ; emb-injective )
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics
  using (O ; Unitary ; Unitary-𝕀 ; Unitary-·*· ; ent ; mat-ext ; ent-adjoint ; 𝕀)
import Examples.Groups.Real-Clifford.Semantics.Matrix as RCMatrix

private
  variable
    k m : ℕ

  -- The binary numbering of the basis vectors, and the bridge with it.
  module RM = RCMatrix {A = D} {{RingD}} {{AdjointD}} isCommutativeRing-D adj-D
  module BM (n : ℕ) = BMatrix n (RM.bits n) (RM.idx {n}) (RM.bits-idx {n}) (RM.idx-bits n)

------------------------------------------------------------------------
-- The reading is injective

private
  toZ-inj : ∀ {x y} → toZ x ≡ toZ y → x ≡ y
  toZ-inj {_ R.+√2 _} {_ R.+√2 _} refl = refl

  ι-inj : ∀ {x y} → ι x ≡ ι y → x ≡ y
  ι-inj e = toZ-inj (emb-injective e)

  -- From u U = 1, v V = 1 and u a = v b, V a = U b.
  uncancel : ∀ u U v V a b → u DR.* U ≡ DR.1# → v DR.* V ≡ DR.1# →
             u DR.* a ≡ v DR.* b → V DR.* a ≡ U DR.* b
  uncancel u U v V a b uU vV e = begin
    V DR.* a
      ≡⟨ cong (V DR.*_) (sym (trans (cong (DR._* a) uU) (DR.*-identityˡ a))) ⟩
    V DR.* ((u DR.* U) DR.* a)
      ≡⟨ cong (V DR.*_) (trans (cong (DR._* a) (DR.*-comm u U)) (DR.*-assoc U u a)) ⟩
    V DR.* (U DR.* (u DR.* a))
      ≡⟨ swap V U (u DR.* a) ⟩
    U DR.* (V DR.* (u DR.* a))
      ≡⟨ cong (λ t → U DR.* (V DR.* t)) e ⟩
    U DR.* (V DR.* (v DR.* b))
      ≡⟨ cong (U DR.*_) (trans (sym (DR.*-assoc V v b)) (cong (DR._* b) (DR.*-comm V v))) ⟩
    U DR.* ((v DR.* V) DR.* b)
      ≡⟨ cong (U DR.*_) (trans (cong (DR._* b) vV) (DR.*-identityˡ b)) ⟩
    U DR.* b ∎
    where
    open ≡-Reasoning
    swap : ∀ p q t → p DR.* (q DR.* t) ≡ q DR.* (p DR.* t)
    swap p q t = trans (sym (DR.*-assoc p q t))
      (trans (cong (DR._* t) (DR.*-comm p q)) (DR.*-assoc q p t))

-- Φ identifies only localised-equal pairs.
Φ-inj : ∀ n {s t : S.Scaled n} → BM.Φ n s ≡ BM.Φ n t → s ~ t
Φ-inj n {ℓ , M} {ℓ′ , M′} e x y =
  subst₂ (λ u v → R.√2^ ℓ′ R.* M u v ≡ R.√2^ ℓ R.* M′ u v)
         (RM.bits-idx x) (RM.bits-idx y) (at (RM.idx x) (RM.idx y))
  where
  open BM n using (ent-Φ)
  open ≡-Reasoning
  at : ∀ r c → R.√2^ ℓ′ R.* M (RM.bits n r) (RM.bits n c) ≡ R.√2^ ℓ R.* M′ (RM.bits n r) (RM.bits n c)
  at r c = ι-inj (begin
    ι (R.√2^ ℓ′ R.* M (RM.bits n r) (RM.bits n c))
      ≡⟨ ι-* (R.√2^ ℓ′) (M (RM.bits n r) (RM.bits n c)) ⟩
    ι (R.√2^ ℓ′) DR.* ι (M (RM.bits n r) (RM.bits n c))
      ≡⟨ cong (DR._* ι (M (RM.bits n r) (RM.bits n c))) (ι-√2^ ℓ′) ⟩
    √2^ᴰ ℓ′ DR.* ι (M (RM.bits n r) (RM.bits n c))
      ≡⟨ uncancel (√½^ ℓ) (√2^ᴰ ℓ) (√½^ ℓ′) (√2^ᴰ ℓ′) _ _ (√½√2^ ℓ) (√½√2^ ℓ′)
           (trans (sym (ent-Φ (ℓ , M) r c))
             (trans (cong (λ A → ent A r c) e) (ent-Φ (ℓ′ , M′) r c))) ⟩
    √2^ᴰ ℓ DR.* ι (M′ (RM.bits n r) (RM.bits n c))
      ≡⟨ cong (DR._* ι (M′ (RM.bits n r) (RM.bits n c))) (sym (ι-√2^ ℓ)) ⟩
    ι (R.√2^ ℓ) DR.* ι (M′ (RM.bits n r) (RM.bits n c))
      ≡⟨ sym (ι-* (R.√2^ ℓ) (M′ (RM.bits n r) (RM.bits n c))) ⟩
    ι (R.√2^ ℓ R.* M′ (RM.bits n r) (RM.bits n c)) ∎)

------------------------------------------------------------------------
-- The gates are symmetric

private
  Sym : S.Op m → Set
  Sym M = ∀ x y → M x y ≡ M y x

  tensor-swap : {M M′ : S.Op m} {N N′ : S.Op k} →
                (∀ u v → M u v ≡ M′ v u) → (∀ u v → N u v ≡ N′ v u) →
                ∀ x y → S.tensor M N x y ≡ S.tensor M′ N′ y x
  tensor-swap {zero}  e f x       y       = cong₂ R._*_ (e [] []) (f x y)
  tensor-swap {suc m} {M = M} {M′} e f (a ∷ x) (b ∷ y) =
    tensor-swap {m} {M = λ u v → M (a ∷ u) (b ∷ v)} {M′ = λ u v → M′ (b ∷ u) (a ∷ v)}
                (λ u v → e (a ∷ u) (b ∷ v)) f x y

  tensor-sym : {M : S.Op m} {N : S.Op k} → Sym M → Sym N → Sym (S.tensor M N)
  tensor-sym {M = M} {N} = tensor-swap {M = M} {M′ = M} {N = N} {N′ = N}

  -- A stored matrix equal to its transpose, decided by evaluation.
  symM : (M : S.Mat m) → eqM M (S.matOf (λ x y → S.ix M y x)) ≡ true → Sym (S.ix M)
  symM M h x y = trans (cong (λ A → S.ix A x y) (eqM-sound M _ h))
                       (S.ix-matOf (λ u v → S.ix M v u) x y)

  sym-gen : ∀ {n} (g : Gen n) → Sym ⟦ g ⟧ᵍ
  sym-gen (gate₀ ())
  sym-gen H-gen  = tensor-sym {M = S.ix S.hM}  {N = S.Idₒ} (symM S.hM refl)  S.δb-sym
  sym-gen Z-gen  = tensor-sym {M = S.ix S.zM}  {N = S.Idₒ} (symM S.zM refl)  S.δb-sym
  sym-gen CZ-gen = tensor-sym {M = S.ix S.czM} {N = S.Idₒ} (symM S.czM refl) S.δb-sym
  sym-gen CH-gen = tensor-sym {M = S.ix S.chM} {N = S.Idₒ} (symM S.chM refl) S.δb-sym
  sym-gen (g ↥)  = tensor-sym {M = S.Idₒ {1}} {N = ⟦ g ⟧ᵍ} S.δb-sym (sym-gen g)

------------------------------------------------------------------------
-- The matrix of a circuit is orthogonal

module _ {n : ℕ} where
  private
    open BM n using (Φ ; ent-Φ ; Φ-≐ ; Φ-ε ; Φ-∙ ; Φ-~)
    open PB (n VRel,_===_) using () renaming (refl to ≈-refl ; trans to ≈-trans ; cong to ≈-cong)
    open Group-Lemmas (n VRel,_===_) grouplike using (inverseʳ)

    -- A symmetric scaled matrix is its own transpose.
    adj-Φ : ∀ ℓ (M : S.Op n) → Sym M → adjoint (Φ (ℓ , M)) ≡ Φ (ℓ , M)
    adj-Φ ℓ M sM = mat-ext λ r c →
      trans (ent-adjoint (Φ (ℓ , M)) r c)
        (trans (adjᴰ-id (ent (Φ (ℓ , M)) c r))
          (trans (ent-Φ (ℓ , M) c r)
            (trans (cong (λ z → √½^ ℓ DR.* ι z) (sM (RM.bits n c) (RM.bits n r)))
              (sym (ent-Φ (ℓ , M) r c)))))

    mat-ε : Φ ⟦ ε ⟧ ≡ 𝕀
    mat-ε = trans (Φ-≐ {0} {⟦ ε ⟧ₒ} {S.Idₒ} ⟦⟧ₒ-ε) Φ-ε

    mat-• : ∀ w v → Φ ⟦ w • v ⟧ ≡ Φ ⟦ w ⟧ ·*· Φ ⟦ v ⟧
    mat-• w v = trans (Φ-≐ {len w +ℕ len v} {⟦ w • v ⟧ₒ} {⟦ w ⟧ₒ S.⊙ ⟦ v ⟧ₒ} (⟦⟧ₒ-• w v))
                      (Φ-∙ ⟦ w ⟧ ⟦ v ⟧)

    -- Each generator is its own inverse.
    gg : (g : Gen n) → n ⊢ [ g ]ʷ • [ g ]ʷ ≈ ε
    gg g = ≈-trans (≈-cong ≈-refl (rev≈⁻¹ [ g ]ʷ)) inverseʳ

    sq : (g : Gen n) → Φ ⟦ [ g ]ʷ ⟧ ·*· Φ ⟦ [ g ]ʷ ⟧ ≡ 𝕀
    sq g = trans (sym (mat-• [ g ]ʷ [ g ]ʷ))
                 (trans (Φ-~ {⟦ [ g ]ʷ • [ g ]ʷ ⟧} {⟦ ε ⟧} (sound (gg g))) mat-ε)

    unitary-gen : (g : Gen n) → Unitary (Φ ⟦ [ g ]ʷ ⟧)
    unitary-gen g = trans (cong (_·*· Φ ⟦ [ g ]ʷ ⟧) t) (sq g)
                  , trans (cong (Φ ⟦ [ g ]ʷ ⟧ ·*·_) t) (sq g)
      where
      t : adjoint (Φ ⟦ [ g ]ʷ ⟧) ≡ Φ ⟦ [ g ]ʷ ⟧
      t = adj-Φ 1 ⟦ [ g ]ʷ ⟧ₒ
            (λ x y → trans (⟦⟧ₒ-gen g x y) (trans (sym-gen g x y) (sym (⟦⟧ₒ-gen g y x))))

  -- The matrix of a circuit, as an element of O (2 ^ n).
  ⟦_⟧ᴼ : Circuit n → Group.Carrier (O (2 ^ n))
  ⟦ [ g ]ʷ ⟧ᴼ = Φ ⟦ [ g ]ʷ ⟧ , unitary-gen g
  ⟦ ε ⟧ᴼ     = 𝕀 , Unitary-𝕀
  ⟦ w • v ⟧ᴼ  = proj₁ ⟦ w ⟧ᴼ ·*· proj₁ ⟦ v ⟧ᴼ , Unitary-·*· (proj₂ ⟦ w ⟧ᴼ) (proj₂ ⟦ v ⟧ᴼ)

  -- It is the matrix Φ reads off the scaled matrix.
  mat-ᴼ : ∀ w → proj₁ ⟦ w ⟧ᴼ ≡ BM.Φ n ⟦ w ⟧
  mat-ᴼ [ g ]ʷ  = refl
  mat-ᴼ ε       = sym mat-ε
  mat-ᴼ (w • v) = trans (cong₂ _·*·_ (mat-ᴼ w) (mat-ᴼ v)) (sym (mat-• w v))

  private
    smp : (n VRel,_===_) IsSubMonoidPresentationOf Group.monoid (O (2 ^ n))
    smp = record
      { ⟦_⟧  = ⟦_⟧ᴼ
      ; mono = record
        { isMonoidHomomorphism = record
          { isMagmaHomomorphism = record
            { isRelHomomorphism = record
              { cong = λ {u} {v} e →
                  trans (mat-ᴼ u)
                    (trans (BM.Φ-~ n {⟦ u ⟧} {⟦ v ⟧} (sound e)) (sym (mat-ᴼ v))) }
            ; homo = λ w v → refl
            }
          ; ε-homo = refl
          }
        ; injective = λ {u} {v} e →
            complete n {u} {v}
              (Φ-inj n {⟦ u ⟧} {⟦ v ⟧} (trans (sym (mat-ᴼ u)) (trans e (mat-ᴼ v))))
        }
      }

  -- Figure 4 presents the subgroup of O_{2ⁿ}(ℤ[1/√2]) that the
  -- circuits on n wires generate.
  subpresentationᴼ : (n VRel,_===_) IsSubPresentationOf O (2 ^ n)
  subpresentationᴼ = subMonoidPresentation⇒subPresentation smp grouplike
