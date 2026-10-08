------------------------------------------------------------------------
-- Presentations of groups
--
-- The single-qubit Clifford group: 24 elements up to phase, each a
-- product of H and S
--
-- The paper says that "for k ≤ 3 the above gates suffice to generate
-- C_k".  At k = 2 and one qubit that is the classical fact that the
-- single-qubit Clifford group, modulo global phases, has 24 elements,
-- all products of H and S.  Here it is proved for the operators of
-- PathSum.Hierarchy.Operator, at every precision M:
--
--   * 24 words over {H, S} (words), each in 𝒞 2 (word-𝒞₂);
--   * every U ∈ 𝒞 2 on one qubit is one of them times a unitary
--     scalar V (classify): U ≈ W_i · V, V unitary, and V's matrix is
--     a multiple of the identity (Scalar);
--   * such a product is again in 𝒞 2 (scalar-𝒞₂, with 𝒞₂-·);
--   * no two of the words are equal up to a unitary scalar (distinct).
--
-- So the classes of 𝒞 2 on one qubit modulo global phases are exactly
-- the 24 words.  A global phase here is a unitary scalar operator: its
-- one entry is an element of Z[ζ, 1/√2] of modulus 1.  That it is a
-- root of unity ζ^e is not proved (it needs the arithmetic of Z[ζ]
-- above 2, which is not formalised).
--
-- The proof is by finite computation on Pauli codes.  A single-qubit
-- Pauli is i^a X^x Z^z: a Code is a, x and z, and a normalised code
-- (nc) has a ∈ {0, 1, 2, 3}.  Two Paulis with normalised codes are
-- equal exactly when the codes are (code-inj).  H and S act on codes
-- (actᴳ, from their images of X and Z: X ↦ Z ↦ X under H, X ↦ Y,
-- Z ↦ Z under S), a word by composing, and a word W conjugates the
-- Pauli of c to the Pauli of actW W c (word-act).  For U ∈ 𝒞 2, the
-- codes c₁, c₂ of U X U† and U Z U† satisfy three conditions (ok):
-- each is Hermitian (it is the conjugate of a Hermitian operator),
-- neither is a multiple of I (X and Z are not), and they are not
-- multiples of each other (X and Z are not).  A computation over all
-- 256 pairs of normalised codes (check-table) finds, for each pair
-- satisfying them, the word W among the 24 whose conjugates of X and
-- Z are c₁ and c₂.  Then V = W† U commutes with X and with Z, and an
-- operator on one qubit commuting with both is a scalar (schur).
-- Distinctness: words equal up to a unitary scalar conjugate X and Z
-- alike, and a second computation (check-inverse) shows that the 24
-- pairs of codes they conjugate X and Z to are distinct.
--
-- The parts: PathSum.Hierarchy.OneQubit.Code (codes, code-inj),
-- .Words (H, S, the words, word-act), .Table (the two computations),
-- .Scalar (schur), and this module (classify, distinct), which
-- re-exports them.  Operator-level reasoning at one qubit is written as
-- single applications of lemmas stated for every width (Words's
-- chain₂ … conj-decomp, ScalarBy), with the operators given
-- explicitly: at n = 1 Agda's sums over assignments compute, and a
-- chain of congruences through products whose operators it must infer
-- costs minutes (one such chain took 141 s; as an application of
-- conj-decomp, 8 s).
--
-- This is the charitable reading of the paper's "for k ≤ 3 the above
-- gates suffice to generate C_k" (every element of C_k is a product of
-- the gates, up to a global phase), at n = 1 and k = 2, with the 24
-- words; PathSum.Hierarchy.Generation gives it at k = 2 for every n,
-- modulo unitary scalars, without the count.  Read
-- literally (C_k the group the gates generate) the sentence fails at
-- k = 3, C₃ not being a group (PathSum.Hierarchy.NotClosed), and at
-- k = 1, H not being a Pauli (PathSum.Hierarchy.Levels).
--
-- What is not formalised: anything about generating C₃, and whether
-- every element of C_k is a product of the gates for k ≥ 4, which the
-- paper leaves open.  (Generation of the n-qubit Clifford group for
-- n ≥ 2 is PathSum.Hierarchy.Generation.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Hierarchy.OneQubit (M₀ : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; not; if_then_else_; _∧_; _∨_; _xor_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Integer.Base using
  (ℤ; 0ℤ; 1ℤ; -1ℤ; +_; -_; -[1+_]; _+_; _-_; _*_; _%_; _/_)
open import Data.Integer.DivMod using (a≡a%n+[a/n]*n; n%d<d)
open import Data.Integer.Divisibility.Signed using (_∣_; _∣?_)
open import Data.Integer.Properties using
  (_≟_; *-zeroʳ; *-identityʳ; +-identityˡ; +-identityʳ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (zero; _<_; z≤n; s≤s)
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Vec.Base using (Vec; lookup)
  renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst₂)
open import Relation.Nullary.Decidable using
  (⌊_⌋; yes; no; False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬_)

import Data.Fin.Properties as Fin
import Data.Nat.Properties as ℕ

open import PathSum.Assign using
  ([_]ᶻ; _=ᵇ_; =ᵇ-refl; =ᵇ-true; same; same-≗; ≔-here)
open import PathSum.Compose.Matrix M₀ using (if-⊛; ⊛-if)
open import PathSum.Compose.Sum M₀ using (Σᴮ-δ; if-cong; zpow-≡; scale-exp)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; -ᴬ_; _≐_; Σᴮ-cong; zpow; rot; rot-exp; rot-0; rot-anti;
   scale-injective; N)
  renaming (H to Hᶻ)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.Hierarchy M₀
open import PathSum.Hierarchy.Gates M₀
open import PathSum.Hierarchy.Levels M₀
open import PathSum.Hierarchy.Operator M₀
open import PathSum.Hierarchy.Pauli M₀
open import PathSum.RelativePhase M₀ using
  (_≡ᴺ_; ≡ᴺ-refl; ≡ᴺ-≡; ≡ᴺ-sym; ≡ᴺ-trans; ≡ᴺ-+; ≡ᴺ--; ≡ᴺ-N)
open import PathSum.Ring M₀ using (_⊛_; ⊛-cong)
open import PathSum.Ring.Laws M₀ using (⊛-comm)

open +-*-Solver using (solve; con; _:+_; _:-_; :-_; _:*_; _:=_)

open import PathSum.Hierarchy.OneQubit.Code M₀ public
open import PathSum.Hierarchy.OneQubit.Scalar M₀ public
open import PathSum.Hierarchy.OneQubit.Table M₀ public
open import PathSum.Hierarchy.OneQubit.Words M₀ public

private
  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-refl : {a : Amp} → a ≐ a
  ≐-refl _ = refl

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)


------------------------------------------------------------------------
-- Every Clifford is a word times a global phase

-- The normalised code of U P U†, for P the Pauli of c.

raw : (U : Op 1) → 𝒞 2 U → Code → Code
raw U u c = toC (proj₁ (proj₂ u ⟦ c ⟧ᶜ))

image-≈ : (U : Op 1) (u : 𝒞 2 U) (c : Code) →
          U · pauli ⟦ c ⟧ᶜ · U † ≈ pauli ⟦ nc (raw U u c) ⟧ᶜ
image-≈ U u c =
  chain₄ (U · pauli ⟦ c ⟧ᶜ · U †) (pauli (proj₁ (proj₂ u ⟦ c ⟧ᶜ)))
         (pauli ⟦ toC (proj₁ (proj₂ u ⟦ c ⟧ᶜ)) ⟧ᶜ)
         (pauli ⟦ nc (toC (proj₁ (proj₂ u ⟦ c ⟧ᶜ))) ⟧ᶜ)
         (pauli ⟦ nc (raw U u c) ⟧ᶜ)
    (proj₂ (proj₂ u ⟦ c ⟧ᶜ))
    (toC-≈ (proj₁ (proj₂ u ⟦ c ⟧ᶜ)))
    (nc-≈ (toC (proj₁ (proj₂ u ⟦ c ⟧ᶜ))))
    (code≡ (nc (toC (proj₁ (proj₂ u ⟦ c ⟧ᶜ)))) (nc (raw U u c)) refl)

-- If two conjugates have the same letters, so do the conjugated.

back : (U : Op 1) → Unitary U → (c d c′ d′ : Code) →
       U · pauli ⟦ c ⟧ᶜ · U † ≈ pauli ⟦ c′ ⟧ᶜ →
       U · pauli ⟦ d ⟧ᶜ · U † ≈ pauli ⟦ d′ ⟧ᶜ →
       cx c′ ≡ cx d′ → cz c′ ≡ cz d′ → (cx c ≡ cx d) × (cz c ≡ cz d)
back U uU c d c′ d′ hc hd ex ez =
  letters (shiftᶜ (cph d′ - cph c′) c) d
    (≈-sym (chain₂ (pauli ⟦ d ⟧ᶜ) ((¼ * (cph d′ - cph c′)) ◃ pauli ⟦ c ⟧ᶜ)
                   (pauli ⟦ shiftᶜ (cph d′ - cph c′) c ⟧ᶜ)
              (back-gen U (pauli ⟦ c ⟧ᶜ) (pauli ⟦ d ⟧ᶜ) (pauli ⟦ c′ ⟧ᶜ)
                        (pauli ⟦ d′ ⟧ᶜ) (¼ * (cph d′ - cph c′)) uU hc hd d′≈)
              (◃-code (cph d′ - cph c′) c)))
  where
  shift-eq : ∀ a b → b ≡ a + (b - a)
  shift-eq = solve 2 (λ a b → b := a :+ (b :- a)) refl

  d′≈ : pauli ⟦ d′ ⟧ᶜ ≈ (¼ * (cph d′ - cph c′)) ◃ pauli ⟦ c′ ⟧ᶜ
  d′≈ = pauli-≈ ⟦ d′ ⟧ᶜ ⟦ shiftᶜ (cph d′ - cph c′) c′ ⟧ᶜ
          (≡ᴺ-≡ (cong (¼ *_) (shift-eq (cph c′) (cph d′))))
          (λ _ → sym ex) (λ _ → sym ez)
        ⟨≈⟩ ≈-sym (◃-code (cph d′ - cph c′) c′)

-- The three conditions hold for the images of X and Z.

private
  X-herm : pauli ⟦ cX ⟧ᶜ † ≈ pauli ⟦ cX ⟧ᶜ
  X-herm = †-code cX ⟨≈⟩ code≡ (invᶜ cX) cX refl

  Z-herm : pauli ⟦ cZ ⟧ᶜ † ≈ pauli ⟦ cZ ⟧ᶜ
  Z-herm = †-code cZ ⟨≈⟩ code≡ (invᶜ cZ) cZ refl

  herm-image : (U : Op 1) (u : 𝒞 2 U) (c : Code) →
               pauli ⟦ c ⟧ᶜ † ≈ pauli ⟦ c ⟧ᶜ → herm (nc (raw U u c)) ≡ true
  herm-image U u c e =
    trans (cong (_=ᶜ nc (raw U u c))
                (nc-inj (invᶜ (nc (raw U u c))) (raw U u c) inv))
          (=ᶜ-refl (nc (raw U u c)))
    where
    inv : pauli ⟦ nc (invᶜ (nc (raw U u c))) ⟧ᶜ ≈ pauli ⟦ nc (raw U u c) ⟧ᶜ
    inv = chain₃ (pauli ⟦ nc (invᶜ (nc (raw U u c))) ⟧ᶜ)
                 (pauli ⟦ invᶜ (nc (raw U u c)) ⟧ᶜ)
                 (pauli ⟦ nc (raw U u c) ⟧ᶜ †)
                 (pauli ⟦ nc (raw U u c) ⟧ᶜ)
            (≈-sym (nc-≈ (invᶜ (nc (raw U u c)))))
            (≈-sym (†-code (nc (raw U u c))))
            (herm-gen U (pauli ⟦ c ⟧ᶜ) (pauli ⟦ nc (raw U u c) ⟧ᶜ) e
                      (image-≈ U u c))

  nonid-from : (c : Code) → (cx c ≡ false → cz c ≡ false → ⊥) →
               nonid c ≡ true
  nonid-from (code a true  z)     _ = refl
  nonid-from (code a false true)  _ = refl
  nonid-from (code a false false) k = ⊥-elim (k refl refl)

  nonid-image : (U : Op 1) (u : 𝒞 2 U) (c : Code) →
                (cx c1 ≡ cx c → cz c1 ≡ cz c → ⊥) →
                nonid (nc (raw U u c)) ≡ true
  nonid-image U u c k = nonid-from (nc (raw U u c)) (λ ex ez →
    let r = back U (proj₁ u) c1 c c1 (nc (raw U u c))
                 (conj-c1 U (proj₁ u)) (image-≈ U u c) (sym ex) (sym ez)
    in k (proj₁ r) (proj₂ r))

  differ-from : (c d : Code) → (cx c ≡ cx d → cz c ≡ cz d → ⊥) →
                not ((cx c =ᵇ cx d) ∧ (cz c =ᵇ cz d)) ≡ true
  differ-from c d k with cx c =ᵇ cx d in ex | cz c =ᵇ cz d in ez
  ... | true  | true  =
    ⊥-elim (k (=ᵇ-true {cx c} {cx d} ex) (=ᵇ-true {cz c} {cz d} ez))
  ... | true  | false = refl
  ... | false | _     = refl

  ok-image : (U : Op 1) (u : 𝒞 2 U) →
             ok (nc (raw U u cX)) (nc (raw U u cZ)) ≡ true
  ok-image U u =
    ∧-intro (herm (nc (raw U u cX))) _ (herm-image U u cX X-herm)
   (∧-intro (herm (nc (raw U u cZ))) _ (herm-image U u cZ Z-herm)
   (∧-intro (nonid (nc (raw U u cX))) _ (nonid-image U u cX (λ ()))
   (∧-intro (nonid (nc (raw U u cZ)))
            (differ (nc (raw U u cX)) (nc (raw U u cZ)))
            (nonid-image U u cZ (λ _ ()))
     (differ-from (nc (raw U u cX)) (nc (raw U u cZ)) (λ ex ez →
        x≢ (proj₁ (back U (proj₁ u) cX cZ (nc (raw U u cX))
                        (nc (raw U u cZ)) (image-≈ U u cX) (image-≈ U u cZ)
                        ex ez)))))))
    where
    x≢ : cx cX ≡ cx cZ → ⊥
    x≢ ()

  -- U agrees with W on X and Z: then W† U is a scalar.

  assemble : (U W : Op 1) → Unitary U → Unitary W →
             U · pauli ⟦ cX ⟧ᶜ · U † ≈ W · pauli ⟦ cX ⟧ᶜ · W † →
             U · pauli ⟦ cZ ⟧ᶜ · U † ≈ W · pauli ⟦ cZ ⟧ᶜ · W † →
             Σ[ V ∈ Op 1 ] (U ≈ W · V) × Unitary V × Scalar V
  assemble U W uU uW ex ez =
    W † · U ,
    ≈-sym (cancelˡ′ W U uW) ,
    Unitary-· (W †) U (Unitary-† W uW) uU ,
    schur (W † · U) (Unitary-· (W †) U (Unitary-† W uW) uU)
          (fixes U W (pauli ⟦ cX ⟧ᶜ) uW ex)
          (fixes U W (pauli ⟦ cZ ⟧ᶜ) uW ez)

  classify′ : (U : Op 1) → Unitary U → (c₁ c₂ : Code) →
              U · pauli ⟦ cX ⟧ᶜ · U † ≈ pauli ⟦ c₁ ⟧ᶜ →
              U · pauli ⟦ cZ ⟧ᶜ · U † ≈ pauli ⟦ c₂ ⟧ᶜ →
              (i : Fin 24) → keyX i ≡ c₁ → keyZ i ≡ c₂ →
              Σ[ V ∈ Op 1 ] (U ≈ opW (lookup words i) · V) × Unitary V ×
                            Scalar V
  classify′ U uU c₁ c₂ e₁ e₂ i k₁ k₂ =
    assemble U (opW (lookup words i)) uU (opW-unitary (lookup words i))
      (chain₄ (U · pauli ⟦ cX ⟧ᶜ · U †) (pauli ⟦ c₁ ⟧ᶜ)
              (pauli ⟦ nc (actW (lookup words i) cX) ⟧ᶜ)
              (pauli ⟦ actW (lookup words i) cX ⟧ᶜ)
              (opW (lookup words i) · pauli ⟦ cX ⟧ᶜ · opW (lookup words i) †)
         e₁ (code≡ c₁ (nc (actW (lookup words i) cX)) (sym k₁))
         (≈-sym (nc-≈ (actW (lookup words i) cX)))
         (≈-sym (word-act (lookup words i) cX)))
      (chain₄ (U · pauli ⟦ cZ ⟧ᶜ · U †) (pauli ⟦ c₂ ⟧ᶜ)
              (pauli ⟦ nc (actW (lookup words i) cZ) ⟧ᶜ)
              (pauli ⟦ actW (lookup words i) cZ ⟧ᶜ)
              (opW (lookup words i) · pauli ⟦ cZ ⟧ᶜ · opW (lookup words i) †)
         e₂ (code≡ c₂ (nc (actW (lookup words i) cZ)) (sym k₂))
         (≈-sym (nc-≈ (actW (lookup words i) cZ)))
         (≈-sym (word-act (lookup words i) cZ)))

-- Every element of 𝒞 2 on one qubit is one of the 24 words times a
-- unitary scalar.

classify : (U : Op 1) → 𝒞 2 U →
           Σ[ i ∈ Fin 24 ] Σ[ V ∈ Op 1 ]
             (U ≈ opW (lookup words i) · V) × Unitary V × Scalar V
classify U u =
  look (nc (raw U u cX)) (nc (raw U u cZ)) ,
  classify′ U (proj₁ u) (nc (raw U u cX)) (nc (raw U u cZ))
    (image-≈ U u cX) (image-≈ U u cZ)
    (look (nc (raw U u cX)) (nc (raw U u cZ)))
    (proj₁ (table-nc (raw U u cX) (raw U u cZ) (ok-image U u)))
    (proj₂ (table-nc (raw U u cX) (raw U u cZ) (ok-image U u)))


------------------------------------------------------------------------
-- The 24 words are distinct up to phase

-- Operators equal up to a unitary scalar conjugate alike (any n).

same-conj-gen : {n : ℕ} (A B V P : Op n) (a : Amp) → Unitary V →
                ScalarBy V a → A ≈ B · V → A · P · A † ≈ B · P · B †
same-conj-gen A B V P a uV sV e =
  conj-cong e P ⟨≈⟩ conj-· B V P ⟨≈⟩ conj-congᴾ B (scalar-conj V a uV sV P)

distinct : (i j : Fin 24) (V : Op 1) → Unitary V → Scalar V →
           opW (lookup words i) ≈ opW (lookup words j) · V → i ≡ j
distinct i j V uV sV e =
  trans (sym (inverse i)) (trans (cong₂ look kx kz) (inverse j))
  where
  kx : keyX i ≡ keyX j
  kx = nc-inj (actW (lookup words i) cX) (actW (lookup words j) cX)
    (chain₅ (pauli ⟦ nc (actW (lookup words i) cX) ⟧ᶜ)
            (pauli ⟦ actW (lookup words i) cX ⟧ᶜ)
            (opW (lookup words i) · pauli ⟦ cX ⟧ᶜ · opW (lookup words i) †)
            (opW (lookup words j) · pauli ⟦ cX ⟧ᶜ · opW (lookup words j) †)
            (pauli ⟦ actW (lookup words j) cX ⟧ᶜ)
            (pauli ⟦ nc (actW (lookup words j) cX) ⟧ᶜ)
       (≈-sym (nc-≈ (actW (lookup words i) cX)))
       (≈-sym (word-act (lookup words i) cX))
       (same-conj-gen (opW (lookup words i)) (opW (lookup words j)) V
                      (pauli ⟦ cX ⟧ᶜ) (mat V 0₁ 0₁) uV sV e)
       (word-act (lookup words j) cX)
       (nc-≈ (actW (lookup words j) cX)))

  kz : keyZ i ≡ keyZ j
  kz = nc-inj (actW (lookup words i) cZ) (actW (lookup words j) cZ)
    (chain₅ (pauli ⟦ nc (actW (lookup words i) cZ) ⟧ᶜ)
            (pauli ⟦ actW (lookup words i) cZ ⟧ᶜ)
            (opW (lookup words i) · pauli ⟦ cZ ⟧ᶜ · opW (lookup words i) †)
            (opW (lookup words j) · pauli ⟦ cZ ⟧ᶜ · opW (lookup words j) †)
            (pauli ⟦ actW (lookup words j) cZ ⟧ᶜ)
            (pauli ⟦ nc (actW (lookup words j) cZ) ⟧ᶜ)
       (≈-sym (nc-≈ (actW (lookup words i) cZ)))
       (≈-sym (word-act (lookup words i) cZ))
       (same-conj-gen (opW (lookup words i)) (opW (lookup words j)) V
                      (pauli ⟦ cZ ⟧ᶜ) (mat V 0₁ 0₁) uV sV e)
       (word-act (lookup words j) cZ)
       (nc-≈ (actW (lookup words j) cZ)))
