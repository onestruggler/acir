------------------------------------------------------------------------
-- Presentations of groups
--
-- H, CNOT and R_k (k ≤ 2) generate the n-qubit Clifford group modulo
-- unitary scalars
--
-- The paper's gate set is {H, CNOT, R_k} (PathSum.CRK.Circuit, as
-- PathSum.Hierarchy.Circuits's K); its Clifford circuits are those of
-- level at most 2, and PathSum.Hierarchy.Circuits shows that they
-- implement elements of C₂ (crk-𝒞₂).  The converse, for every n
-- (generation-K): every U ∈ C₂ is ⟪ K.⟦ C ⟧ ⟫ · V for a circuit C of
-- level ≤ 2 over {H, CNOT, R_k, R_k†} and a unitary scalar V; with
-- crk-𝒞₂, C₂ is exactly these products (𝒞₂⇔K-generated).  This is the
-- paper's "for k ≤ 3 the above gates suffice to generate C_k" at
-- k = 2, read up to global phases (unitary scalars), for every n;
-- that such a scalar is a root of unity ζ^e is not proved.
--
-- It follows from the {H, S, CZ} version (PathSum.Hierarchy.Generation)
-- by translating the gates (toK): H is H, S is R_2, CZ_(a,b) is
-- H_b CNOT_(a,b) H_b, and CZ_(a,a) = Z_a is R_1.  The translated
-- circuit has level ≤ 2 (toK-level) and conjugates every Pauli as the
-- original does (toK-act; for CZ, actH b ∘ cnot-act a b ∘ actH b is
-- actCZ a b on the data, cz-via-cnot).  So the two operators differ by
-- an operator W fixing every Pauli, a unitary scalar
-- (PathSum.Hierarchy.Generation.Scalar), and U = K V′ with V′ = W V.
-- That the operators are equal, not only up to that scalar, is not
-- needed and not claimed.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Hierarchy.Generation.CRK (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; _∧_; _xor_)
open import Data.Fin.Base using (Fin)
open import Data.Integer.Base using (ℤ; 0ℤ; +_; -_; _+_; _-_; _*_)
open import Data.Integer.Properties using (*-distribˡ-+; *-zeroʳ; +-identityʳ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Nat.Base using (_≤_; _⊔_; z≤n; s≤s)
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Decidable using (Dec; yes; no)

import Data.Fin.Properties as Fin
import Data.Nat.Properties as ℕ

open import PathSum.Assign using ([_]ᶻ; _[_≔_]; ≔-here; ≔-there)
open import PathSum.Compose.Matrix M₀ using (prop-2-7)
open import PathSum.Cyclotomic M₀ using (Amp; _≐_)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.Hierarchy.Levels M₀ using (ρ; ρ-def)
open import PathSum.Maslov.Arith M₀ using (½-xor)

-- The development so far, from one chain of applications (see
-- PathSum.Hierarchy.Generation.Scalar's imports), re-exported for the
-- contract.

open import PathSum.Hierarchy.Generation M₀ public
open import PathSum.RelativePhase M₀ using
  (_≡ᴺ_; ≡ᴺ-refl; ≡ᴺ-≡; ≡ᴺ-sym; ≡ᴺ-trans; ≡ᴺ-+; module ≡ᴺ-Reasoning)

import PathSum.Compose.CRK M₀ as KC

open +-*-Solver using (solve; con; _:+_; _:*_; _:=_)

private
  variable
    n : ℕ

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ∧-false : ∀ a → (a ∧ false) ≡ false
  ∧-false true  = refl
  ∧-false false = refl

  ∧-true : ∀ a → (a ∧ true) ≡ a
  ∧-true true  = refl
  ∧-true false = refl

  ∧-idem : ∀ a → (a ∧ a) ≡ a
  ∧-idem true  = refl
  ∧-idem false = refl


------------------------------------------------------------------------
-- The translation

czK : (a b : Fin n) → Dec (a ≡ b) → K.Circuit n
czK a b (yes _)   = K.R 1 a ∷ []
czK a b (no  a≢b) = K.H b ∷ K.CNOT a b a≢b ∷ K.H b ∷ []

toKg : Cl.Gate n → K.Circuit n
toKg (Cl.H w)    = K.H w ∷ []
toKg (Cl.S w)    = K.R 2 w ∷ []
toKg (Cl.CZ a b) = czK a b (a Fin.≟ b)

toK : Cl.Circuit n → K.Circuit n
toK []      = []
toK (g ∷ C) = toKg g ++ toK C

-- Its level is at most 2.

private
  level-++ : (A B : K.Circuit n) → K.level A ≤ 2 → K.level B ≤ 2 →
             K.level (A ++ B) ≤ 2
  level-++ []                 B a b = b
  level-++ (K.H _ ∷ A)        B a b = level-++ A B a b
  level-++ (K.CNOT _ _ _ ∷ A) B a b = level-++ A B a b
  level-++ (K.R k _ ∷ A)      B a b =
    ℕ.⊔-lub (ℕ.m⊔n≤o⇒m≤o k (K.level A) a)
            (level-++ A B (ℕ.m⊔n≤o⇒n≤o k (K.level A) a) b)
  level-++ (K.R† k _ ∷ A)     B a b =
    ℕ.⊔-lub (ℕ.m⊔n≤o⇒m≤o k (K.level A) a)
            (level-++ A B (ℕ.m⊔n≤o⇒n≤o k (K.level A) a) b)

  czK-level : (a b : Fin n) (d : Dec (a ≡ b)) → K.level (czK a b d) ≤ 2
  czK-level a b (yes _) = s≤s z≤n
  czK-level a b (no  _) = z≤n

  toKg-level : (g : Cl.Gate n) → K.level (toKg g) ≤ 2
  toKg-level (Cl.H w)    = z≤n
  toKg-level (Cl.S w)    = s≤s (s≤s z≤n)
  toKg-level (Cl.CZ a b) = czK-level a b (a Fin.≟ b)

toK-level : (C : Cl.Circuit n) → K.level (toK C) ≤ 2
toK-level []      = z≤n
toK-level (g ∷ C) = level-++ (toKg g) (toK C) (toKg-level g) (toK-level C)


------------------------------------------------------------------------
-- How the translation conjugates the Paulis

-- The path-sum of A followed by B is the product.

crk-++ : (A B : K.Circuit n) → ⟪ K.⟦ A ++ B ⟧ ⟫ ≈ ⟪ K.⟦ B ⟧ ⟫ · ⟪ K.⟦ A ⟧ ⟫
crk-++ A B = ≈-by ⟪ K.⟦ A ++ B ⟧ ⟫ (⟪ K.⟦ B ⟧ ⟫ · ⟪ K.⟦ A ⟧ ⟫)
  (trans (KC.norm-++ A B) (ℕ.+-comm (K.norm A) (K.norm B)))
  (λ x z → KC.amp-⟦++⟧ A B x z ∙ prop-2-7 K.⟦ B ⟧ K.⟦ A ⟧ x z)

private
  conj-I : (P : Op n) → I · P · I † ≈ P
  conj-I P = ·-congʳ (I · P) †-I ⟨≈⟩ ·-identityʳ (I · P) ⟨≈⟩ ·-identityˡ P

  K-nil : (p : PauliData n) →
          ⟪ K.⟦ [] ⟧ ⟫ · pauli p · ⟪ K.⟦ [] ⟧ ⟫ † ≈ pauli p
  K-nil p = conj-cong crk-[] (pauli p) ⟨≈⟩ conj-I (pauli p)

  -- A gate, then a circuit.

  K-cons : (g : K.Gate n) (C : K.Circuit n) (p r s : PauliData n) →
           ⟪ K.⟦ g ∷ [] ⟧ ⟫ · pauli p · ⟪ K.⟦ g ∷ [] ⟧ ⟫ † ≈ pauli r →
           ⟪ K.⟦ C ⟧ ⟫ · pauli r · ⟪ K.⟦ C ⟧ ⟫ † ≈ pauli s →
           ⟪ K.⟦ g ∷ C ⟧ ⟫ · pauli p · ⟪ K.⟦ g ∷ C ⟧ ⟫ † ≈ pauli s
  K-cons g C p r s h₁ h₂ =
    conj-cong (crk-++ (g ∷ []) C) (pauli p)
    ⟨≈⟩ conj-· ⟪ K.⟦ C ⟧ ⟫ ⟪ K.⟦ g ∷ [] ⟧ ⟫ (pauli p)
    ⟨≈⟩ conj-congᴾ ⟪ K.⟦ C ⟧ ⟫ h₁
    ⟨≈⟩ h₂

  -- One gate, through its operator G.

  K-gate : (g : K.Gate n) (G : Op n) → ⟪ K.⟦ g ∷ [] ⟧ ⟫ ≈ G →
           (p r : PauliData n) → G · pauli p · G † ≈ pauli r →
           ⟪ K.⟦ g ∷ [] ⟧ ⟫ · pauli p · ⟪ K.⟦ g ∷ [] ⟧ ⟫ † ≈ pauli r
  K-gate g G e p r h = conj-cong e (pauli p) ⟨≈⟩ h

  -- Equal circuits.  (The facts below about concrete circuits are
  -- stated through these lemmas, for variables, and not as types
  -- written with the concrete circuits: written so, each took Agda
  -- tens of seconds to compare with the lemmas' types.)

  K-via : (C D : K.Circuit n) → C ≡ D → (p r : PauliData n) →
          ⟪ K.⟦ D ⟧ ⟫ · pauli p · ⟪ K.⟦ D ⟧ ⟫ † ≈ pauli r →
          ⟪ K.⟦ C ⟧ ⟫ · pauli p · ⟪ K.⟦ C ⟧ ⟫ † ≈ pauli r
  K-via C .C refl p r h = h

  -- R_1 = Z conjugates as CZ_(a,a): the sign (-1)^(x_a).

  r1-phase : (a : Fin n) (p : PauliData n) (u : Assign n) →
             proj₁ (ΔFn (wireFn (ρ false 1) a) p) u ≡ᴺ
             ¼ * ((+ 2) * [ xs p a ]ᶻ) + ½ * [ dot 0ᵛ u ]ᶻ
  r1-phase a p u = begin
    ρ false 1 * [ u a ]ᶻ - ρ false 1 * [ u a xor xs p a ]ᶻ
      ≡⟨ cong (λ s → s * [ u a ]ᶻ - s * [ u a xor xs p a ]ᶻ) (ρ-def false 1) ⟩
    ½ * [ u a ]ᶻ - ½ * [ u a xor xs p a ]ᶻ
      ≡ᴺ⟨ ≡ᴺ-+ (≡ᴺ-refl {a = ½ * [ u a ]ᶻ}) (neg-½ (u a xor xs p a)) ⟩
    ½ * [ u a ]ᶻ + ½ * [ u a xor xs p a ]ᶻ
      ≡ᴺ⟨ ½-xor (u a) (u a xor xs p a) ⟩
    ½ * [ u a xor (u a xor xs p a) ]ᶻ
      ≡⟨ cong (λ b → ½ * [ b ]ᶻ) (back (u a) (xs p a)) ⟩
    ½ * [ xs p a ]ᶻ
      ≡⟨ sym (trans (cong (λ b → ¼ * ((+ 2) * [ xs p a ]ᶻ) + ½ * [ b ]ᶻ)
                          (dot-0ˡ 0ᵛ u (λ _ → refl)))
                    (trans (cong (λ t → ¼ * ((+ 2) * [ xs p a ]ᶻ) + t)
                                 (*-zeroʳ ½))
                           (trans (+-identityʳ _) (¼·2 [ xs p a ]ᶻ)))) ⟩
    ¼ * ((+ 2) * [ xs p a ]ᶻ) + ½ * [ dot 0ᵛ u ]ᶻ ∎
    where
    open ≡ᴺ-Reasoning
    back : ∀ u x → (u xor (u xor x)) ≡ x
    back true  true  = refl
    back true  false = refl
    back false x     = refl

  R1-conj : (a : Fin n) (p : PauliData n) →
            Rs (ρ false 1) a · pauli p · Rs (ρ false 1) a † ≈
            pauli (actCZ a a p)
  R1-conj a p =
    diag-conj-pauli (wireFn (ρ false 1) a) p ((+ 2) * [ xs p a ]ᶻ) 0ᵛ
                    (r1-phase a p)
    ⟨≈⟩ pauli-≈ (pd ((+ 2) * [ xs p a ]ᶻ) 0ᵛ 0ᵛ ∙ᴾ p) (actCZ a a p)
                ph-eq (λ _ → refl) z-eq
    where
    ph-eq : ¼ * ((+ 2) * [ xs p a ]ᶻ + ph p + (+ 2) * [ dot 0ᵛ (xs p) ]ᶻ) ≡ᴺ
            ¼ * (ph p + (+ 2) * [ xs p a ∧ xs p a ]ᶻ)
    ph-eq = ≡ᴺ-≡ (cong (¼ *_)
      (trans (cong (λ d → (+ 2) * [ xs p a ]ᶻ + ph p + (+ 2) * [ d ]ᶻ)
                   (dot-0ˡ 0ᵛ (xs p) (λ _ → refl)))
        (trans (solve 2 (λ t a → t :+ a :+ con (+ 2) :* con 0ℤ := a :+ t)
                      refl ((+ 2) * [ xs p a ]ᶻ) (ph p))
               (cong (λ b → ph p + (+ 2) * [ b ]ᶻ) (sym (∧-idem (xs p a)))))))
    z-eq : ∀ j → (0ᵛ ⊕ᵛ zs p) j ≡ (czZ a a (xs p) ⊕ᵛ zs p) j
    z-eq j = sym (cong (_xor zs p j) (xor-self (xs p a ∧ eᵛ a j)))

  -- H_b CNOT_(a,b) H_b conjugates as CZ_(a,b), on the data.

  cz-bits : ∀ xa xb zb →
            ((xb ∧ zb) xor ((zb xor xa) ∧ xb)) ≡ (xa ∧ xb)
  cz-bits true  true  true  = refl
  cz-bits true  true  false = refl
  cz-bits true  false true  = refl
  cz-bits true  false false = refl
  cz-bits false true  true  = refl
  cz-bits false true  false = refl
  cz-bits false false true  = refl
  cz-bits false false false = refl

  cz-via-cnot : {a b : Fin n} (a≢b : a ≢ b) (p : PauliData n) →
                actH b (cnot-act a b (actH b p)) ≈ᴾ actCZ a b p
  cz-via-cnot {n} {a} {b} a≢b p = ≈ᴾ-intro ph-eq xx zz
    where
    b≢a : b ≢ a
    b≢a e = a≢b (sym e)
    x = xs p
    z = zs p
    r₁ = actH b p
    r₂ = cnot-act a b r₁

    x₂b : xs r₂ b ≡ z b xor x a
    x₂b = trans (≔-here (xs r₁) b (xs r₁ b xor xs r₁ a))
                (cong₂ _xor_ (≔-here x b (z b)) (≔-there x (z b) a≢b))

    z₂b : zs r₂ b ≡ x b
    z₂b = trans (≔-there (zs r₁) (zs r₁ a xor zs r₁ b) b≢a)
                (≔-here z b (x b))

    A = x b ∧ z b
    B = (z b xor x a) ∧ x b

    ph-eq : ¼ * (ph p + (+ 2) * [ x b ∧ z b ]ᶻ +
                 (+ 2) * [ xs r₂ b ∧ zs r₂ b ]ᶻ) ≡ᴺ
            ¼ * (ph p + (+ 2) * [ x a ∧ x b ]ᶻ)
    ph-eq = begin
      ¼ * (ph p + (+ 2) * [ A ]ᶻ + (+ 2) * [ xs r₂ b ∧ zs r₂ b ]ᶻ)
        ≡⟨ cong (λ c → ¼ * (ph p + (+ 2) * [ A ]ᶻ + (+ 2) * [ c ]ᶻ))
                (cong₂ _∧_ x₂b z₂b) ⟩
      ¼ * (ph p + (+ 2) * [ A ]ᶻ + (+ 2) * [ B ]ᶻ)
        ≡⟨ split ⟩
      ¼ * ph p + (½ * [ A ]ᶻ + ½ * [ B ]ᶻ)
        ≡ᴺ⟨ ≡ᴺ-+ (≡ᴺ-refl {a = ¼ * ph p}) (½-xor A B) ⟩
      ¼ * ph p + ½ * [ A xor B ]ᶻ
        ≡⟨ cong (λ c → ¼ * ph p + ½ * [ c ]ᶻ) (cz-bits (x a) (x b) (z b)) ⟩
      ¼ * ph p + ½ * [ x a ∧ x b ]ᶻ
        ≡⟨ sym (trans (*-distribˡ-+ ¼ (ph p) ((+ 2) * [ x a ∧ x b ]ᶻ))
                      (cong (λ t → ¼ * ph p + t) (¼·2 [ x a ∧ x b ]ᶻ))) ⟩
      ¼ * (ph p + (+ 2) * [ x a ∧ x b ]ᶻ) ∎
      where
      open ≡ᴺ-Reasoning
      split : ¼ * (ph p + (+ 2) * [ A ]ᶻ + (+ 2) * [ B ]ᶻ) ≡
              ¼ * ph p + (½ * [ A ]ᶻ + ½ * [ B ]ᶻ)
      split = trans
        (solve 4 (λ q a s t → q :* (a :+ con (+ 2) :* s :+ con (+ 2) :* t) :=
                              q :* a :+ (q :* (con (+ 2) :* s) :+
                                         q :* (con (+ 2) :* t)))
               refl ¼ (ph p) [ A ]ᶻ [ B ]ᶻ)
        (cong₂ (λ s t → ¼ * ph p + (s + t)) (¼·2 [ A ]ᶻ) (¼·2 [ B ]ᶻ))

    xx-at : ∀ j → Dec (j ≡ b) → xs (actH b r₂) j ≡ x j
    xx-at j (yes refl) = trans (≔-here (xs r₂) b (zs r₂ b)) z₂b
    xx-at j (no  j≢b)  =
      trans (≔-there (xs r₂) (zs r₂ b) j≢b)
        (trans (≔-there (xs r₁) (xs r₁ b xor xs r₁ a) j≢b)
               (≔-there x (z b) j≢b))

    xx : ∀ j → xs (actH b r₂) j ≡ xs (actCZ a b p) j
    xx j = xx-at j (j Fin.≟ b)

    zz-a : ∀ j → j ≢ b → Dec (j ≡ a) →
           zs r₂ j ≡ (czZ a b x ⊕ᵛ z) j
    zz-a j j≢b (yes refl) =
      trans (≔-here (zs r₁) a (zs r₁ a xor zs r₁ b))
        (trans (cong₂ _xor_ (≔-there z (x b) a≢b) (≔-here z b (x b)))
          (sym (trans (cong₂ (λ e₁ e₂ → ((x b ∧ e₁) xor (x a ∧ e₂)) xor z a)
                             (≔-here 0ᵛ a true) (≔-there 0ᵛ true a≢b))
                 (trans (cong₂ (λ s t → (s xor t) xor z a)
                               (∧-true (x b)) (∧-false (x a)))
                        (trans (cong (_xor z a) (xor-false (x b)))
                               (xor-comm (x b) (z a)))))))
    zz-a j j≢b (no  j≢a)  =
      trans (≔-there (zs r₁) (zs r₁ a xor zs r₁ b) j≢a)
        (trans (≔-there z (x b) j≢b)
          (sym (trans (cong₂ (λ e₁ e₂ → ((x b ∧ e₁) xor (x a ∧ e₂)) xor z j)
                             (≔-there 0ᵛ true j≢a) (≔-there 0ᵛ true j≢b))
                      (cong₂ (λ s t → (s xor t) xor z j)
                             (∧-false (x b)) (∧-false (x a))))))

    zz-at : ∀ j → Dec (j ≡ b) → zs (actH b r₂) j ≡ (czZ a b x ⊕ᵛ z) j
    zz-at j (yes refl) =
      trans (≔-here (zs r₂) b (xs r₂ b))
        (trans x₂b
          (sym (trans (cong₂ (λ e₁ e₂ → ((x b ∧ e₁) xor (x a ∧ e₂)) xor z b)
                             (≔-there 0ᵛ true b≢a) (≔-here 0ᵛ b true))
                 (trans (cong₂ (λ s t → (s xor t) xor z b)
                               (∧-false (x b)) (∧-true (x a)))
                        (xor-comm (x a) (z b))))))
    zz-at j (no  j≢b)  =
      trans (≔-there (zs r₂) (xs r₂ b) j≢b) (zz-a j j≢b (j Fin.≟ a))

    zz : ∀ j → zs (actH b r₂) j ≡ zs (actCZ a b p) j
    zz j = zz-at j (j Fin.≟ b)

  czK-act : (a b : Fin n) (d : Dec (a ≡ b)) (p : PauliData n) →
            ⟪ K.⟦ czK a b d ⟧ ⟫ · pauli p · ⟪ K.⟦ czK a b d ⟧ ⟫ † ≈
            pauli (actCZ a b p)
  czK-act a b (yes refl) p =
    K-via (czK a a (yes refl)) (K.R 1 a ∷ []) refl p (actCZ a a p)
      (K-gate (K.R 1 a) (Rs (ρ false 1) a) (crk-gate (K.R 1 a)) p
              (actCZ a a p) (R1-conj a p))
  czK-act a b (no  a≢b)  p =
    K-via (czK a b (no a≢b)) (K.H b ∷ K.CNOT a b a≢b ∷ K.H b ∷ []) refl
          p (actCZ a b p) h
    where
    h₁ = K-gate (K.H b) (hadOp b) (crk-gate (K.H b)) p (actH b p)
                (had-conj b p)
    h₂ = K-gate (K.CNOT a b a≢b) (cnotOp a b) (crk-gate (K.CNOT a b a≢b))
                (actH b p) (cnot-act a b (actH b p))
                (intertwine⇒conj (cnotOp a b) (pauli (actH b p))
                   (pauli (cnot-act a b (actH b p))) (cnot-unitary a b a≢b)
                   (cnot-pauli a b a≢b (actH b p)))
    h₃ = K-gate (K.H b) (hadOp b) (crk-gate (K.H b))
                (cnot-act a b (actH b p)) (actH b (cnot-act a b (actH b p)))
                (had-conj b (cnot-act a b (actH b p)))
    h₄ = K-nil (actH b (cnot-act a b (actH b p)))
           ⟨≈⟩ ≈ᴾ⇒≈ (cz-via-cnot a≢b p)
    h = K-cons (K.H b) (K.CNOT a b a≢b ∷ K.H b ∷ []) p (actH b p)
               (actCZ a b p) h₁
          (K-cons (K.CNOT a b a≢b) (K.H b ∷ []) (actH b p)
                  (cnot-act a b (actH b p)) (actCZ a b p) h₂
            (K-cons (K.H b) [] (cnot-act a b (actH b p))
                    (actH b (cnot-act a b (actH b p))) (actCZ a b p) h₃ h₄))

  toKg-act : (g : Cl.Gate n) (p : PauliData n) →
             ⟪ K.⟦ toKg g ⟧ ⟫ · pauli p · ⟪ K.⟦ toKg g ⟧ ⟫ † ≈ pauli (act g p)
  toKg-act (Cl.H w)    p =
    K-via (toKg (Cl.H w)) (K.H w ∷ []) refl p (act (Cl.H w) p)
      (K-gate (K.H w) (cliffordOp (Cl.H w)) (crk-gate (K.H w)) p
              (act (Cl.H w) p) (gate-conj (Cl.H w) p))
  toKg-act (Cl.S w)    p =
    K-via (toKg (Cl.S w)) (K.R 2 w ∷ []) refl p (act (Cl.S w) p)
      (K-gate (K.R 2 w) (cliffordOp (Cl.S w)) (crk-gate (K.R 2 w)) p
              (act (Cl.S w) p) (gate-conj (Cl.S w) p))
  toKg-act (Cl.CZ a b) p =
    K-via (toKg (Cl.CZ a b)) (czK a b (a Fin.≟ b)) refl p (actCZ a b p)
      (czK-act a b (a Fin.≟ b) p)

-- The translation conjugates every Pauli as the circuit does.

toK-act : (C : Cl.Circuit n) (p : PauliData n) →
          ⟪ K.⟦ toK C ⟧ ⟫ · pauli p · ⟪ K.⟦ toK C ⟧ ⟫ † ≈ pauli (actC C p)
toK-act []      p = K-via (toK []) [] refl p p (K-nil p)
toK-act (g ∷ C) p =
  K-via (toK (g ∷ C)) (toKg g ++ toK C) refl p (actC C (act g p))
    (conj-cong (crk-++ (toKg g) (toK C)) (pauli p)
     ⟨≈⟩ conj-· ⟪ K.⟦ toK C ⟧ ⟫ ⟪ K.⟦ toKg g ⟧ ⟫ (pauli p)
     ⟨≈⟩ conj-congᴾ ⟪ K.⟦ toK C ⟧ ⟫ (toKg-act g p)
     ⟨≈⟩ toK-act C (act g p))


------------------------------------------------------------------------
-- Generation over {H, CNOT, R_k}

-- If K and L conjugate every Pauli alike, U = L V with V a unitary
-- scalar is K V′ with V′ = (K† L) V a unitary scalar: K† L fixes every
-- Pauli.  Stated for any operators and applied once, to the translated
-- circuit and the original.

private
  peel : (U P : Op n) → Unitary U → U † · (U · P · U †) · U ≈ P
  peel U P u =
    ·-congˡ U (·-congʳ (U †) (·-assoc U P (U †)) ⟨≈⟩ cancelˡ U (P · U †) u)
    ⟨≈⟩ cancelʳ′ U P u

  swap : (U K L V : Op n) → Unitary K → Unitary L → Unitary V →
         ScalarBy V (mat V 0ᵛ 0ᵛ) → U ≈ L · V →
         (∀ r → K · pauli r · K † ≈ L · pauli r · L †) →
         Σ[ V′ ∈ Op n ]
           (U ≈ K · V′) × Unitary V′ × ScalarBy V′ (mat V′ 0ᵛ 0ᵛ)
  swap {n} U K L V uK uL uV sV e same =
    (K † · L) · V , eq , uV′ ,
    scalar-fixing ((K † · L) · V) uV′ (λ j → fixes (X^ j))
                  (λ j → fixes (Z^ j))
    where
    uV′ : Unitary ((K † · L) · V)
    uV′ = Unitary-· (K † · L) V (Unitary-· (K †) L (Unitary-† K uK) uL) uV

    eq : U ≈ K · ((K † · L) · V)
    eq = e ⟨≈⟩ ·-congˡ V (≈-sym (cancelˡ′ K L uK))
           ⟨≈⟩ ·-assoc K (K † · L) V

    fixes : (r : PauliData n) →
            (K † · L) · V · pauli r · ((K † · L) · V) † ≈ pauli r
    fixes r =
      conj-· (K † · L) V (pauli r)
      ⟨≈⟩ conj-congᴾ (K † · L) (scalar-conj V (mat V 0ᵛ 0ᵛ) uV sV (pauli r))
      ⟨≈⟩ conj-· (K †) L (pauli r)
      ⟨≈⟩ conj-congᴾ (K †) (≈-sym (same r))
      ⟨≈⟩ ·-congʳ (K † · (K · pauli r · K †)) (†-involutive K)
      ⟨≈⟩ peel K (pauli r) uK

  -- The circuit translated: its operator conjugates every Pauli as the
  -- original's does.

  translate : (U : Op n) →
              Σ[ C ∈ Cl.Circuit n ] Σ[ V ∈ Op n ]
                (U ≈ ⟪ Cl.⟦ C ⟧ ⟫ · V) × Unitary V ×
                ScalarBy V (mat V 0ᵛ 0ᵛ) →
              Σ[ C ∈ K.Circuit n ] (K.level C ≤ 2) × Σ[ V ∈ Op n ]
                (U ≈ ⟪ K.⟦ C ⟧ ⟫ · V) × Unitary V ×
                ScalarBy V (mat V 0ᵛ 0ᵛ)
  translate U (C , V , e , uV , sV) =
    toK C , toK-level C ,
    swap U ⟪ K.⟦ toK C ⟧ ⟫ ⟪ Cl.⟦ C ⟧ ⟫ V
         (𝒞₂-unitary {U = ⟪ K.⟦ toK C ⟧ ⟫}
                     (level-𝒞₂ (toK C) (toK-level C)))
         (circuit-unitary C) uV sV e
         (λ r → toK-act C r ⟨≈⟩ ≈-sym (circuit-act C r))

-- Every element of 𝒞 2 is the operator of a circuit of level ≤ 2 over
-- {H, CNOT, R_k, R_k†} times a unitary scalar.

generation-K : (U : Op n) → 𝒞 2 U →
               Σ[ C ∈ K.Circuit n ] (K.level C ≤ 2) × Σ[ V ∈ Op n ]
                 (U ≈ ⟪ K.⟦ C ⟧ ⟫ · V) × Unitary V ×
                 ScalarBy V (mat V 0ᵛ 0ᵛ)
generation-K U u = translate U (generation U u)

-- Conversely, every such product is in 𝒞 2.

K-generated-𝒞₂ : (C : K.Circuit n) → K.level C ≤ 2 → (V : Op n) (a : Amp) →
                 Unitary V → ScalarBy V a → 𝒞 2 (⟪ K.⟦ C ⟧ ⟫ · V)
K-generated-𝒞₂ C lv V a uV sV =
  𝒞₂-·ʰ {U = ⟪ K.⟦ C ⟧ ⟫} {V = V} (level-𝒞₂ C lv) (scalar-𝒞₂ⁿ V a uV sV)

K-Generated : Op n → Set
K-Generated {n} U = Σ[ C ∈ K.Circuit n ] (K.level C ≤ 2) × Σ[ V ∈ Op n ]
                      (U ≈ ⟪ K.⟦ C ⟧ ⟫ · V) × Unitary V ×
                      ScalarBy V (mat V 0ᵛ 0ᵛ)

𝒞₂⇔K-generated : (U : Op n) → 𝒞 2 U ⇔ K-Generated U
𝒞₂⇔K-generated U = mk⇔ (generation-K U) (λ (C , lv , V , e , uV , sV) →
  𝒞₂-resp {U = ⟪ K.⟦ C ⟧ ⟫ · V} {V = U} (≈-sym e)
         (K-generated-𝒞₂ C lv V (mat V 0ᵛ 0ᵛ) uV sV))
