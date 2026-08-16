------------------------------------------------------------------------
-- Presentations of groups
--
-- Properties of the multilinear polynomials of a path-sum: degrees of
-- monomials, divisibility of finite sums, and divisibility of the
-- lifted linear Boolean forms
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Polynomial.Properties where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_)
open import Data.Bool.Properties using (∧-zeroʳ; ∧-assoc)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Subset using
  (Subset; inside; outside; ⁅_⁆; ⊥; _∪_; _∩_; _∈_; _∉_; _⊆_; ∣_∣)
open import Data.Fin.Subset.Properties using
  (∣⊥∣≡0; ∣⁅x⁆∣≡1; ∪-identityʳ; drop-not-there; drop-∷-⊆; q⊆p∪q;
   x∈⁅x⁆; _⊆?_; _∈?_; ∉⊥; x∈p∪q⁻)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_)
  renaming (-_ to -ℤ_; _^_ to _^ℤ_; _+_ to _+ℤ_; _*_ to _*ℤ_;
            _-_ to _-ℤ_)
open import Data.Integer.Properties using
  (+-identityˡ; +-identityʳ; *-identityˡ; *-identityʳ; *-assoc; *-zeroʳ;
   *-distribˡ-+; *-distribʳ-+; *-cancelˡ-≡; +-assoc; +-inverseˡ;
   neg-distrib-+; pos-*; *-comm; +-comm; *-zeroˡ)
open import Data.Integer.Divisibility.Signed using
  (_∣_; ∣-refl; ∣-trans; ∣ᵤ⇒∣; ∣m∣n⇒∣m+n; ∣n⇒∣m*n; ∣m⇒∣m*n)
open import Data.Nat.Base using
  (ℕ; zero; suc; _+_; _*_; _∸_; _^_; _≤_; z≤n; s≤s)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Vec.Base using (Vec; []; _∷_; here; there; tabulate; insertAt)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Decidable using (Dec; yes; no; ⌊_⌋; _×?_)
open import Relation.Nullary.Negation using (¬_; contradiction)

open import PathSum.Polynomial

import Data.Bool.Properties as Bool
import Data.Integer.Solver as ℤSolver
import Data.Nat.Divisibility as ℕDiv
import Data.Vec.Properties as Vec
import Data.Nat.Properties as ℕ
import Relation.Binary.PropositionalEquality as Eq

open +-*-Solver using (solve; _:+_; _:=_)
open ℤSolver.+-*-Solver using ()
  renaming (solve to solveℤ; con to conℤ; _:+_ to _:+ℤ_; _:*_ to _:*ℤ_;
            _:=_ to _:=ℤ_)

private
  variable
    k n m : ℕ


------------------------------------------------------------------------
-- Sizes of subsets

∣p∣≡0⇒p≡⊥ : (p : Subset k) → ∣ p ∣ ≡ 0 → p ≡ ⊥
∣p∣≡0⇒p≡⊥ []            _  = refl
∣p∣≡0⇒p≡⊥ (outside ∷ p) eq = cong (outside ∷_) (∣p∣≡0⇒p≡⊥ p eq)

∣p∣≡1⇒p≡⁅i⁆ : (p : Subset k) → ∣ p ∣ ≡ 1 → ∃ λ i → p ≡ ⁅ i ⁆
∣p∣≡1⇒p≡⁅i⁆ (inside ∷ p) eq =
  zero , cong (inside ∷_) (∣p∣≡0⇒p≡⊥ p (ℕ.suc-injective eq))
∣p∣≡1⇒p≡⁅i⁆ (outside ∷ p) eq =
  let i , p≡ = ∣p∣≡1⇒p≡⁅i⁆ p eq in suc i , cong (outside ∷_) p≡

∣p∪q∣≤∣p∣+∣q∣ : (p q : Subset k) → ∣ p ∪ q ∣ ≤ ∣ p ∣ + ∣ q ∣
∣p∪q∣≤∣p∣+∣q∣ []            []            = z≤n
∣p∪q∣≤∣p∣+∣q∣ (outside ∷ p) (outside ∷ q) = ∣p∪q∣≤∣p∣+∣q∣ p q
∣p∪q∣≤∣p∣+∣q∣ (inside  ∷ p) (outside ∷ q) = s≤s (∣p∪q∣≤∣p∣+∣q∣ p q)
∣p∪q∣≤∣p∣+∣q∣ (outside ∷ p) (inside  ∷ q) = ℕ.≤-trans
  (s≤s (∣p∪q∣≤∣p∣+∣q∣ p q)) (ℕ.≤-reflexive (sym (ℕ.+-suc ∣ p ∣ ∣ q ∣)))
∣p∪q∣≤∣p∣+∣q∣ (inside  ∷ p) (inside  ∷ q) = s≤s (ℕ.≤-trans
  (∣p∪q∣≤∣p∣+∣q∣ p q)
  (ℕ.≤-trans (ℕ.n≤1+n _) (ℕ.≤-reflexive (sym (ℕ.+-suc ∣ p ∣ ∣ q ∣)))))

∣p∪⁅i⁆∣ : (p : Subset k) (i : Fin k) → i ∉ p → ∣ p ∪ ⁅ i ⁆ ∣ ≡ suc ∣ p ∣
∣p∪⁅i⁆∣ (inside  ∷ p) zero    i∉p = contradiction here i∉p
∣p∪⁅i⁆∣ (outside ∷ p) zero    i∉p = cong suc (cong ∣_∣ (∪-identityʳ p))
∣p∪⁅i⁆∣ (inside  ∷ p) (suc i) i∉p =
  cong suc (∣p∪⁅i⁆∣ p i (drop-not-there i∉p))
∣p∪⁅i⁆∣ (outside ∷ p) (suc i) i∉p = ∣p∪⁅i⁆∣ p i (drop-not-there i∉p)


------------------------------------------------------------------------
-- Degrees of monomials

∥1ᵐ∥≡0 : ∥ 1ᵐ {n} {m} ∥ ≡ 0
∥1ᵐ∥≡0 {n} {m} = cong₂ _+_ (∣⊥∣≡0 n) (∣⊥∣≡0 m)

∥⟪v⟫∥≡1 : (v : Var n m) → ∥ ⟪ v ⟫ ∥ ≡ 1
∥⟪v⟫∥≡1 {n} {m} x[ i ] = cong₂ _+_ (∣⁅x⁆∣≡1 i) (∣⊥∣≡0 m)
∥⟪v⟫∥≡1 {n} {m} y[ j ] = cong₂ _+_ (∣⊥∣≡0 n) (∣⁅x⁆∣≡1 j)

∥γ∥≡0⇒γ≡1ᵐ : (γ : Mon n m) → ∥ γ ∥ ≡ 0 → γ ≡ 1ᵐ
∥γ∥≡0⇒γ≡1ᵐ (α , β) eq = cong₂ _,_
  (∣p∣≡0⇒p≡⊥ α (ℕ.m+n≡0⇒m≡0 ∣ α ∣ eq))
  (∣p∣≡0⇒p≡⊥ β (ℕ.m+n≡0⇒n≡0 ∣ α ∣ eq))

private
  i+j≡1 : ∀ i j → i + j ≡ 1 → (i ≡ 0 × j ≡ 1) ⊎ (i ≡ 1 × j ≡ 0)
  i+j≡1 zero    j eq = inj₁ (refl , eq)
  i+j≡1 (suc i) j eq = inj₂
    ( cong suc (ℕ.m+n≡0⇒m≡0 i (ℕ.suc-injective eq))
    , ℕ.m+n≡0⇒n≡0 i (ℕ.suc-injective eq) )

∥γ∥≡1⇒γ≡⟪v⟫ : (γ : Mon n m) → ∥ γ ∥ ≡ 1 → ∃ λ v → γ ≡ ⟪ v ⟫
∥γ∥≡1⇒γ≡⟪v⟫ (α , β) eq with i+j≡1 ∣ α ∣ ∣ β ∣ eq
... | inj₁ (∣α∣≡0 , ∣β∣≡1) =
  let j , β≡ = ∣p∣≡1⇒p≡⁅i⁆ β ∣β∣≡1
  in y[ j ] , cong₂ _,_ (∣p∣≡0⇒p≡⊥ α ∣α∣≡0) β≡
... | inj₂ (∣α∣≡1 , ∣β∣≡0) =
  let i , α≡ = ∣p∣≡1⇒p≡⁅i⁆ α ∣α∣≡1
  in x[ i ] , cong₂ _,_ α≡ (∣p∣≡0⇒p≡⊥ β ∣β∣≡0)

∥∪ᵐ∥≤ : (γ δ : Mon n m) → ∥ γ ∪ᵐ δ ∥ ≤ ∥ γ ∥ + ∥ δ ∥
∥∪ᵐ∥≤ (α , β) (α′ , β′) = ℕ.≤-trans
  (ℕ.+-mono-≤ (∣p∪q∣≤∣p∣+∣q∣ α α′) (∣p∪q∣≤∣p∣+∣q∣ β β′))
  (ℕ.≤-reflexive (rearrange (∣ α ∣) (∣ β ∣) (∣ α′ ∣) (∣ β′ ∣)))
  where
  rearrange : ∀ a b c d → (a + c) + (b + d) ≡ (a + b) + (c + d)
  rearrange = solve 4
    (λ a b c d → (a :+ c) :+ (b :+ d) := (a :+ b) :+ (c :+ d)) refl

∥∪ᵐ⟪v⟫∥ : (δ : Mon n m) (v : Var n m) → ¬ (v ∈ᵐ δ) →
          ∥ δ ∪ᵐ ⟪ v ⟫ ∥ ≡ suc ∥ δ ∥
∥∪ᵐ⟪v⟫∥ (α , β) x[ i ] v∉δ =
  cong₂ _+_ (∣p∪⁅i⁆∣ α i v∉δ) (cong ∣_∣ (∪-identityʳ β))
∥∪ᵐ⟪v⟫∥ (α , β) y[ j ] v∉δ = trans
  (cong₂ _+_ (cong ∣_∣ (∪-identityʳ α)) (∣p∪⁅i⁆∣ β j v∉δ))
  (ℕ.+-suc ∣ α ∣ ∣ β ∣)


------------------------------------------------------------------------
-- Divisibility

1∣i : ∀ {i} → 1ℤ ∣ i
1∣i = ∣ᵤ⇒∣ (ℕDiv.1∣ _)

i∣0 : ∀ {i} → i ∣ 0ℤ
i∣0 = ∣ᵤ⇒∣ (ℕDiv.divides 0 refl)

2^-mono-∣ : ∀ {a b} → a ≤ b → (+ (2 ^ a)) ∣ (+ (2 ^ b))
2^-mono-∣ {a} {b} a≤b = ∣ᵤ⇒∣ (ℕDiv.divides (2 ^ (b ∸ a)) eq)
  where
  eq : 2 ^ b ≡ 2 ^ (b ∸ a) * 2 ^ a
  eq = trans (cong (2 ^_) (sym (ℕ.m∸n+n≡m a≤b))) (ℕ.^-distribˡ-+-* 2 (b ∸ a) a)


------------------------------------------------------------------------
-- Finite sums

Σsub-∣ : ∀ {c} (f : Subset k → ℤ) → (∀ s → c ∣ f s) → c ∣ Σsub f
Σsub-∣ {k = zero}  f h = h []
Σsub-∣ {k = suc k} f h = ∣m∣n⇒∣m+n
  (Σsub-∣ (λ s → f (inside ∷ s)) (λ s → h (inside ∷ s)))
  (Σsub-∣ (λ s → f (outside ∷ s)) (λ s → h (outside ∷ s)))

Σmon-∣ : ∀ {c} (f : Mon n m → ℤ) → (∀ γ → c ∣ f γ) → c ∣ Σmon f
Σmon-∣ f h = Σsub-∣ _ (λ α → Σsub-∣ _ (λ β → h (α , β)))

Σsub-cong : ∀ {f g : Subset k → ℤ} → (∀ s → f s ≡ g s) → Σsub f ≡ Σsub g
Σsub-cong {k = zero}  f≗g = f≗g []
Σsub-cong {k = suc k} f≗g = cong₂ _+ℤ_
  (Σsub-cong (λ s → f≗g (inside ∷ s)))
  (Σsub-cong (λ s → f≗g (outside ∷ s)))

Σsub-0 : Σsub {k} (λ _ → 0ℤ) ≡ 0ℤ
Σsub-0 {k = zero}  = refl
Σsub-0 {k = suc k} = cong₂ _+ℤ_ (Σsub-0 {k}) (Σsub-0 {k})

Σsub-+ : (f g : Subset k → ℤ) →
         Σsub (λ s → f s +ℤ g s) ≡ Σsub f +ℤ Σsub g
Σsub-+ {k = zero}  f g = refl
Σsub-+ {k = suc k} f g = trans
  (cong₂ _+ℤ_ (Σsub-+ (λ s → f (inside ∷ s)) (λ s → g (inside ∷ s)))
              (Σsub-+ (λ s → f (outside ∷ s)) (λ s → g (outside ∷ s))))
  (shuffle (Σsub (λ s → f (inside ∷ s))) (Σsub (λ s → g (inside ∷ s)))
           (Σsub (λ s → f (outside ∷ s))) (Σsub (λ s → g (outside ∷ s))))
  where
  shuffle : ∀ p q r s → (p +ℤ q) +ℤ (r +ℤ s) ≡ (p +ℤ r) +ℤ (q +ℤ s)
  shuffle = solveℤ 4
    (λ p q r s → (p :+ℤ q) :+ℤ (r :+ℤ s) :=ℤ (p :+ℤ r) :+ℤ (q :+ℤ s)) refl

-- A polynomial all of whose coefficients are divisible by c takes
-- values divisible by c.

eval-∣ : ∀ {c} (P : Poly n m) → (∀ γ → c ∣ P γ) →
         ∀ x y → c ∣ eval P x y
eval-∣ {c = c} P h x y = Σmon-∣ _ each
  where
  each : ∀ γ → c ∣ (if satᵐ γ x y then P γ else 0ℤ)
  each γ with satᵐ γ x y
  ... | true  = h γ
  ... | false = i∣0


------------------------------------------------------------------------
-- Occurrences of variables

v∈δ∪⟪v⟫ : (δ : Mon n m) (v : Var n m) → v ∈ᵐ (δ ∪ᵐ ⟪ v ⟫)
v∈δ∪⟪v⟫ (α , β) x[ i ] = q⊆p∪q α ⁅ i ⁆ (x∈⁅x⁆ i)
v∈δ∪⟪v⟫ (α , β) y[ j ] = q⊆p∪q β ⁅ j ⁆ (x∈⁅x⁆ j)

-- Substituting for a path variable in a polynomial containing no path
-- variable leaves it free of path variables: every coefficient the
-- substitution collects is one of a monomial that does contain a path
-- variable, and so vanishes.

subst-NoVar : (P : Poly n m) (i : Fin m) (c : Bool) (S : Mon n m) →
              (∀ j → NoVar (+ 2) y[ j ] P) →
              ∀ j → NoVar (+ 2) y[ j ] (subst P y[ i ] c S)
subst-NoVar P i c S nov j γ j∈γ = ∣m∣n⇒∣m+n first
  (Σmon-∣ _ (λ δ → Σmon-∣ _ (each δ)))
  where
  first : (+ 2) ∣ (if ⌊ y[ i ] ∈ᵐ? γ ⌋ then 0ℤ else P γ)
  first with y[ i ] ∈ᵐ? γ
  ... | yes _ = i∣0
  ... | no  _ = nov j γ j∈γ

  each : ∀ δ β → (+ 2) ∣ substTerm P y[ i ] c S γ δ β
  each δ β with y[ i ] ∈ᵐ? δ
  ... | yes _ = i∣0
  ... | no  _ with (δ ∪ᵐ β) ≟ᵐ γ
  ...   | no  _ = i∣0
  ...   | yes _ = ∣m⇒∣m*n (liftXor c S β)
                    (nov i (δ ∪ᵐ ⟪ y[ i ] ⟫) (v∈δ∪⟪v⟫ δ y[ i ]))


------------------------------------------------------------------------
-- The alternating sum over a subset

-- Inclusion as a Boolean test, so that it computes on a cons.

infix 5 _⊆ᵇ_

_⊆ᵇ_ : Subset k → Subset k → Bool
[]            ⊆ᵇ []            = true
(inside  ∷ p) ⊆ᵇ (inside  ∷ q) = p ⊆ᵇ q
(inside  ∷ p) ⊆ᵇ (outside ∷ q) = false
(outside ∷ p) ⊆ᵇ (_       ∷ q) = p ⊆ᵇ q

-- _⊆ᵇ_ decides inclusion, so the guard of liftXor can be replaced by
-- it wherever a sum has to be computed.

⊆ᵇ⇒⊆ : (p q : Subset k) → p ⊆ᵇ q ≡ true → p ⊆ q
⊆ᵇ⇒⊆ []            []            _  ()
⊆ᵇ⇒⊆ (inside  ∷ p) (inside  ∷ q) eq here      = here
⊆ᵇ⇒⊆ (inside  ∷ p) (inside  ∷ q) eq (there h) = there (⊆ᵇ⇒⊆ p q eq h)
⊆ᵇ⇒⊆ (outside ∷ p) (t       ∷ q) eq (there h) = there (⊆ᵇ⇒⊆ p q eq h)

⊆⇒⊆ᵇ : (p q : Subset k) → p ⊆ q → p ⊆ᵇ q ≡ true
⊆⇒⊆ᵇ []            []            _   = refl
⊆⇒⊆ᵇ (inside  ∷ p) (inside  ∷ q) sub = ⊆⇒⊆ᵇ p q (drop-∷-⊆ sub)
⊆⇒⊆ᵇ (inside  ∷ p) (outside ∷ q) sub = contradiction (sub here) λ ()
⊆⇒⊆ᵇ (outside ∷ p) (t       ∷ q) sub = ⊆⇒⊆ᵇ p q (drop-∷-⊆ sub)

⌊⊆?⌋ : (p q : Subset k) → ⌊ p ⊆? q ⌋ ≡ p ⊆ᵇ q
⌊⊆?⌋ p q with p ⊆? q | p ⊆ᵇ q in eq
... | yes _   | true  = refl
... | yes sub | false = contradiction (trans (sym (⊆⇒⊆ᵇ p q sub)) eq) λ ()
... | no  ¬s  | true  = contradiction (λ {x} → ⊆ᵇ⇒⊆ p q eq {x}) ¬s
... | no  _   | false = refl

private
  isYes-×? : ∀ {A B : Set} (d₁ : Dec A) (d₂ : Dec B) →
             ⌊ d₁ ×? d₂ ⌋ ≡ ⌊ d₁ ⌋ ∧ ⌊ d₂ ⌋
  isYes-×? (yes _) (yes _) = refl
  isYes-×? (yes _) (no  _) = refl
  isYes-×? (no  _) (yes _) = refl
  isYes-×? (no  _) (no  _) = refl

⌊⊆ᵐ?⌋ : (γ S : Mon n m) →
        ⌊ γ ⊆ᵐ? S ⌋ ≡ (proj₁ γ ⊆ᵇ proj₁ S) ∧ (proj₂ γ ⊆ᵇ proj₂ S)
⌊⊆ᵐ?⌋ (α , β) (α′ , β′) = trans (isYes-×? (α ⊆? α′) (β ⊆? β′))
                                (cong₂ _∧_ (⌊⊆?⌋ α α′) (⌊⊆?⌋ β β′))

-- A monomial is satisfied by an assignment exactly when it is
-- contained in the set of variables the assignment makes true.

sat-⊆ᵇ : (p : Subset k) (f : Fin k → Bool) → sat p f ≡ p ⊆ᵇ tabulate f
sat-⊆ᵇ []            f = refl
sat-⊆ᵇ (outside ∷ p) f = sat-⊆ᵇ p (λ i → f (suc i))
sat-⊆ᵇ (inside  ∷ p) f with f zero
... | true  = sat-⊆ᵇ p (λ i → f (suc i))
... | false = refl

-- Inclusion in an intersection is inclusion in both.

⊆ᵇ-∩ : (p A B : Subset k) → (p ⊆ᵇ A) ∧ (p ⊆ᵇ B) ≡ p ⊆ᵇ (A ∩ B)
⊆ᵇ-∩ []            []            []            = refl
⊆ᵇ-∩ (inside  ∷ p) (inside  ∷ A) (inside  ∷ B) = ⊆ᵇ-∩ p A B
⊆ᵇ-∩ (inside  ∷ p) (inside  ∷ A) (outside ∷ B) = ∧-zeroʳ (p ⊆ᵇ A)
⊆ᵇ-∩ (inside  ∷ p) (outside ∷ A) (t       ∷ B) = refl
⊆ᵇ-∩ (outside ∷ p) (a       ∷ A) (b       ∷ B) = ⊆ᵇ-∩ p A B

Σsub-scale : ∀ {z} (f : Subset k → ℤ) →
             Σsub (λ s → z *ℤ f s) ≡ z *ℤ Σsub f
Σsub-scale {k = zero}      f = refl
Σsub-scale {k = suc k} {z} f = trans
  (cong₂ _+ℤ_ (Σsub-scale {z = z} (λ s → f (inside ∷ s)))
              (Σsub-scale {z = z} (λ s → f (outside ∷ s))))
  (sym (*-distribˡ-+ z (Σsub (λ s → f (inside ∷ s)))
                       (Σsub (λ s → f (outside ∷ s)))))

private
  -- (-2)^(s+1) = (-1 · 2) · (-2)^s
  negpow-suc : ∀ s → negpow (suc s) ≡ ((-ℤ 1ℤ) *ℤ (+ 2)) *ℤ negpow s
  negpow-suc s = trans
    (cong (λ w → ((-ℤ 1ℤ) *ℤ ((-ℤ 1ℤ) ^ℤ s)) *ℤ w) (pos-* 2 (2 ^ s)))
    (assoc4 (-ℤ 1ℤ) ((-ℤ 1ℤ) ^ℤ s) (+ 2) (+ (2 ^ s)))
    where
    assoc4 : ∀ p u q v → (p *ℤ u) *ℤ (q *ℤ v) ≡ (p *ℤ q) *ℤ (u *ℤ v)
    assoc4 = solveℤ 4 (λ p u q v →
      (p :*ℤ u) :*ℤ (q :*ℤ v) :=ℤ (p :*ℤ q) :*ℤ (u :*ℤ v)) refl

-- Splitting off the empty subset, the only one the lifting treats
-- separately.

emptyᵇ : Subset k → Bool
emptyᵇ []            = true
emptyᵇ (inside  ∷ p) = false
emptyᵇ (outside ∷ p) = emptyᵇ p

Σsub-⊥ : (f : Subset k → ℤ) →
         Σsub f ≡ f ⊥ +ℤ Σsub (λ γ → if emptyᵇ γ then 0ℤ else f γ)
Σsub-⊥ {k = zero}  f = sym (+-identityʳ (f []))
Σsub-⊥ {k = suc k} f = trans
  (cong (Σsub (λ s → f (inside ∷ s)) +ℤ_) (Σsub-⊥ (λ s → f (outside ∷ s))))
  (shuffle (Σsub (λ s → f (inside ∷ s))) (f ⊥)
           (Σsub (λ s → if emptyᵇ s then 0ℤ else f (outside ∷ s))))
  where
  shuffle : ∀ p q r → p +ℤ (q +ℤ r) ≡ q +ℤ (p +ℤ r)
  shuffle = solveℤ 3 (λ p q r → p :+ℤ (q :+ℤ r) :=ℤ q :+ℤ (p :+ℤ r)) refl

emptyᵇ-⊥ : emptyᵇ (⊥ {k}) ≡ true
emptyᵇ-⊥ {k = zero}  = refl
emptyᵇ-⊥ {k = suc k} = emptyᵇ-⊥ {k}

emptyᵐ : Mon n m → Bool
emptyᵐ (α , β) = emptyᵇ α ∧ emptyᵇ β

Σmon-⊥ : (f : Mon n m → ℤ) →
         Σmon f ≡ f 1ᵐ +ℤ Σmon (λ γ → if emptyᵐ γ then 0ℤ else f γ)
Σmon-⊥ {n} {m} f = trans
  (trans (Σsub-⊥ (λ α → Σsub (λ β → f (α , β))))
    (trans (cong (_+ℤ Sα) (Σsub-⊥ (λ β → f (⊥ , β))))
           (assoc (f 1ᵐ) Tβ Sα)))
  (cong (f 1ᵐ +ℤ_)
    (sym (trans (Σsub-⊥ (λ α → Σsub (λ β → g (α , β))))
                (cong₂ _+ℤ_ head-eq (Σsub-cong step)))))
  where
  g : Mon n m → ℤ
  g γ = if emptyᵐ γ then 0ℤ else f γ

  Tβ : ℤ
  Tβ = Σsub (λ β → if emptyᵇ β then 0ℤ else f (⊥ , β))

  Sα : ℤ
  Sα = Σsub (λ α → if emptyᵇ α then 0ℤ else Σsub (λ β → f (α , β)))

  assoc : ∀ p q r → (p +ℤ q) +ℤ r ≡ p +ℤ (q +ℤ r)
  assoc = solveℤ 3 (λ p q r → (p :+ℤ q) :+ℤ r :=ℤ p :+ℤ (q :+ℤ r)) refl

  head-eq : Σsub (λ β → g (⊥ , β)) ≡ Tβ
  head-eq = Σsub-cong (λ β →
    cong (λ b → if (b ∧ emptyᵇ β) then 0ℤ else f (⊥ , β)) (emptyᵇ-⊥ {n}))

  step : ∀ α → (if emptyᵇ α then 0ℤ else Σsub (λ β → g (α , β))) ≡
               (if emptyᵇ α then 0ℤ else Σsub (λ β → f (α , β)))
  step α with emptyᵇ α
  ... | true  = refl
  ... | false = refl

-- The empty monomial is the one liftXor treats separately, and it is
-- satisfied by every assignment.

private
  ∧-true : ∀ a b → a ∧ b ≡ true → (a ≡ true) × (b ≡ true)
  ∧-true true true _ = refl , refl

  emptyᵇ⇒≡⊥ : (p : Subset k) → emptyᵇ p ≡ true → p ≡ ⊥
  emptyᵇ⇒≡⊥ []            _  = refl
  emptyᵇ⇒≡⊥ (outside ∷ p) eq = cong (outside ∷_) (emptyᵇ⇒≡⊥ p eq)

  emptyᵐ⇒≡1ᵐ : (γ : Mon n m) → emptyᵐ γ ≡ true → γ ≡ 1ᵐ
  emptyᵐ⇒≡1ᵐ (α , β) eq with ∧-true (emptyᵇ α) (emptyᵇ β) eq
  ... | eα , eβ = cong₂ _,_ (emptyᵇ⇒≡⊥ α eα) (emptyᵇ⇒≡⊥ β eβ)

  ≡1ᵐ⇒emptyᵐ : (γ : Mon n m) → γ ≡ 1ᵐ → emptyᵐ γ ≡ true
  ≡1ᵐ⇒emptyᵐ {n} {m} γ eq = trans (cong emptyᵐ eq)
    (cong₂ _∧_ (emptyᵇ-⊥ {n}) (emptyᵇ-⊥ {m}))

⌊≟ᵐ1ᵐ⌋ : (γ : Mon n m) → ⌊ γ ≟ᵐ 1ᵐ ⌋ ≡ emptyᵐ γ
⌊≟ᵐ1ᵐ⌋ γ with γ ≟ᵐ 1ᵐ | emptyᵐ γ in eq
... | yes γ≡ | true  = refl
... | yes γ≡ | false = contradiction (trans (sym (≡1ᵐ⇒emptyᵐ γ γ≡)) eq) λ ()
... | no  ¬γ≡ | true = contradiction (emptyᵐ⇒≡1ᵐ γ eq) ¬γ≡
... | no  _   | false = refl

sat-⊥ : (f : Fin k → Bool) → sat (⊥ {k}) f ≡ true
sat-⊥ {k = zero}  f = refl
sat-⊥ {k = suc k} f = sat-⊥ (λ i → f (suc i))

satᵐ-1ᵐ : (x : Fin n → Bool) (y : Fin m → Bool) →
          satᵐ (1ᵐ {n} {m}) x y ≡ true
satᵐ-1ᵐ x y = cong₂ _∧_ (sat-⊥ x) (sat-⊥ y)

liftXor-1ᵐ : (c : Bool) (S : Mon n m) →
             liftXor c S 1ᵐ ≡ (if c then 1ℤ else 0ℤ)
liftXor-1ᵐ {n} {m} c S with (1ᵐ {n} {m}) ≟ᵐ 1ᵐ
... | yes _  = refl
... | no  ¬p = contradiction refl ¬p


------------------------------------------------------------------------
-- Inclusion and satisfaction of monomials

infix 5 _⊆ᵐᵇ_

_⊆ᵐᵇ_ : Mon n m → Mon n m → Bool
(α , β) ⊆ᵐᵇ (α′ , β′) = (α ⊆ᵇ α′) ∧ (β ⊆ᵇ β′)

_∩ᵐ_ : Mon n m → Mon n m → Mon n m
(α , β) ∩ᵐ (α′ , β′) = (α ∩ α′) , (β ∩ β′)

satᵐ-⊆ᵐᵇ : (γ : Mon n m) (x : Fin n → Bool) (y : Fin m → Bool) →
           satᵐ γ x y ≡ γ ⊆ᵐᵇ (tabulate x , tabulate y)
satᵐ-⊆ᵐᵇ (α , β) x y = cong₂ _∧_ (sat-⊆ᵇ α x) (sat-⊆ᵇ β y)

private
  ∧-shuffle : ∀ a b c d → (a ∧ b) ∧ (c ∧ d) ≡ (a ∧ c) ∧ (b ∧ d)
  ∧-shuffle true  true  c d = refl
  ∧-shuffle true  false c d = sym (∧-zeroʳ c)
  ∧-shuffle false b     c d = refl

⊆ᵐᵇ-∩ᵐ : (γ A B : Mon n m) →
         (γ ⊆ᵐᵇ A) ∧ (γ ⊆ᵐᵇ B) ≡ γ ⊆ᵐᵇ (A ∩ᵐ B)
⊆ᵐᵇ-∩ᵐ (α , β) (Aα , Aβ) (Bα , Bβ) =
  trans (∧-shuffle (α ⊆ᵇ Aα) (β ⊆ᵇ Aβ) (α ⊆ᵇ Bα) (β ⊆ᵇ Bβ))
        (cong₂ _∧_ (⊆ᵇ-∩ α Aα Bα) (⊆ᵇ-∩ β Aβ Bβ))

Σmon-scale : ∀ {z} (f : Mon n m → ℤ) →
             Σmon (λ γ → z *ℤ f γ) ≡ z *ℤ Σmon f
Σmon-scale {z = z} f =
  trans (Σsub-cong (λ α → Σsub-scale {z = z} (λ β → f (α , β))))
        (Σsub-scale {z = z} (λ α → Σsub (λ β → f (α , β))))

Σmon-cong : ∀ {f g : Mon n m → ℤ} → (∀ γ → f γ ≡ g γ) → Σmon f ≡ Σmon g
Σmon-cong f≗g = Σsub-cong (λ α → Σsub-cong (λ β → f≗g (α , β)))

⊥⊆ᵇ : (q : Subset k) → ⊥ ⊆ᵇ q ≡ true
⊥⊆ᵇ []      = refl
⊥⊆ᵇ (t ∷ q) = ⊥⊆ᵇ q

1ᵐ⊆ᵐᵇ : (A : Mon n m) → 1ᵐ ⊆ᵐᵇ A ≡ true
1ᵐ⊆ᵐᵇ (Aα , Aβ) = cong₂ _∧_ (⊥⊆ᵇ Aα) (⊥⊆ᵇ Aβ)

-- A non-empty monomial has positive degree.

emptyᵇ-false : (p : Subset k) → emptyᵇ p ≡ false → 1 ≤ ∣ p ∣
emptyᵇ-false (inside  ∷ p) _  = s≤s z≤n
emptyᵇ-false (outside ∷ p) eq = emptyᵇ-false p eq

private
  1≤⇒suc∸1 : ∀ x → 1 ≤ x → x ≡ suc (x ∸ 1)
  1≤⇒suc∸1 x le = sym (trans (ℕ.+-comm 1 (x ∸ 1)) (ℕ.m∸n+n≡m le))

emptyᵐ-false : (γ : Mon n m) → emptyᵐ γ ≡ false → ∥ γ ∥ ≡ suc (∥ γ ∥ ∸ 1)
emptyᵐ-false (α , β) eq with emptyᵇ α in eα
... | false = 1≤⇒suc∸1 (∣ α ∣ + ∣ β ∣)
      (ℕ.≤-trans (emptyᵇ-false α eα) (ℕ.m≤m+n ∣ α ∣ ∣ β ∣))
... | true  = 1≤⇒suc∸1 (∣ α ∣ + ∣ β ∣)
      (ℕ.≤-trans (emptyᵇ-false β eq) (ℕ.m≤n+m ∣ β ∣ ∣ α ∣))

-- Arithmetic of the powers.

^-+ : (i : ℤ) (a b : ℕ) → i ^ℤ (a + b) ≡ (i ^ℤ a) *ℤ (i ^ℤ b)
^-+ i zero    b = sym (*-identityˡ (i ^ℤ b))
^-+ i (suc a) b = trans (cong (i *ℤ_) (^-+ i a b))
                        (sym (*-assoc i (i ^ℤ a) (i ^ℤ b)))

negpow-+ : (a b : ℕ) → negpow (a + b) ≡ negpow a *ℤ negpow b
negpow-+ a b = trans
  (cong₂ _*ℤ_ (^-+ (-ℤ 1ℤ) a b)
              (trans (cong +_ (ℕ.^-distribˡ-+-* 2 a b)) (pos-* (2 ^ a) (2 ^ b))))
  (shuffle ((-ℤ 1ℤ) ^ℤ a) ((-ℤ 1ℤ) ^ℤ b) (+ (2 ^ a)) (+ (2 ^ b)))
  where
  shuffle : ∀ p q r s → (p *ℤ q) *ℤ (r *ℤ s) ≡ (p *ℤ r) *ℤ (q *ℤ s)
  shuffle = solveℤ 4
    (λ p q r s → (p :*ℤ q) :*ℤ (r :*ℤ s) :=ℤ (p :*ℤ r) :*ℤ (q :*ℤ s)) refl

neg1-pow : (s : ℕ) → ((-ℤ 1ℤ) ^ℤ s ≡ 1ℤ) ⊎ ((-ℤ 1ℤ) ^ℤ s ≡ -ℤ 1ℤ)
neg1-pow zero    = inj₁ refl
neg1-pow (suc s) with neg1-pow s
... | inj₁ eq = inj₂ (trans (cong ((-ℤ 1ℤ) *ℤ_) eq) (*-identityʳ (-ℤ 1ℤ)))
... | inj₂ eq = inj₁ (cong ((-ℤ 1ℤ) *ℤ_) eq)

-- Guards.

if-∧ : ∀ (p q : Bool) (a : ℤ) →
       (if p then (if q then a else 0ℤ) else 0ℤ) ≡ (if (p ∧ q) then a else 0ℤ)
if-∧ true  q a = refl
if-∧ false q a = refl

if-scale : ∀ (p : Bool) (z a : ℤ) →
           (if p then (z *ℤ a) else 0ℤ) ≡ z *ℤ (if p then a else 0ℤ)
if-scale true  z a = refl
if-scale false z a = sym (*-zeroʳ z)

+-cancelˡ-≡ : ∀ i j k → i +ℤ j ≡ i +ℤ k → j ≡ k
+-cancelˡ-≡ i j k eq =
  trans (sym (undo i j)) (trans (cong ((-ℤ i) +ℤ_) eq) (undo i k))
  where
  undo : ∀ u v → (-ℤ u) +ℤ (u +ℤ v) ≡ v
  undo u v = trans (sym (+-assoc (-ℤ u) u v))
                   (trans (cong (_+ℤ v) (+-inverseˡ u)) (+-identityˡ v))

if-* : ∀ (p q : Bool) (a b : ℤ) →
       (if (p ∧ q) then (a *ℤ b) else 0ℤ) ≡
       (if p then a else 0ℤ) *ℤ (if q then b else 0ℤ)
if-* true  true  a b = refl
if-* true  false a b = sym (*-zeroʳ a)
if-* false q     a b = refl

-- Summing (-2)^|γ| over the subsets γ of A gives (1-2)^|A|.  This is
-- what makes the lifting of a Boolean polynomial Boolean-valued
-- (lemma 2.5): adding one variable to A multiplies the sum by -1.

subset-sum : (A : Subset k) →
             Σsub (λ γ → if (γ ⊆ᵇ A) then negpow (∣ γ ∣) else 0ℤ) ≡
             (-ℤ 1ℤ) ^ℤ (∣ A ∣)
subset-sum []            = *-identityˡ 1ℤ
subset-sum (inside ∷ A)  = trans
  (cong₂ _+ℤ_
    (trans (Σsub-cong (λ γ → step (γ ⊆ᵇ A) (∣ γ ∣)))
      (trans (Σsub-scale {z = (-ℤ 1ℤ) *ℤ (+ 2)}
                (λ γ → if (γ ⊆ᵇ A) then negpow (∣ γ ∣) else 0ℤ))
             (cong (((-ℤ 1ℤ) *ℤ (+ 2)) *ℤ_) (subset-sum A))))
    (subset-sum A))
  (final ((-ℤ 1ℤ) ^ℤ (∣ A ∣)))
  where
  step : ∀ b s → (if b then negpow (suc s) else 0ℤ) ≡
                 ((-ℤ 1ℤ) *ℤ (+ 2)) *ℤ (if b then negpow s else 0ℤ)
  step true  s = negpow-suc s
  step false s = sym (*-zeroʳ ((-ℤ 1ℤ) *ℤ (+ 2)))

  final : ∀ v → (((-ℤ 1ℤ) *ℤ (+ 2)) *ℤ v) +ℤ v ≡ (-ℤ 1ℤ) *ℤ v
  final = solveℤ 1 (λ v →
    ((conℤ (-ℤ 1ℤ) :*ℤ conℤ (+ 2)) :*ℤ v) :+ℤ v :=ℤ conℤ (-ℤ 1ℤ) :*ℤ v) refl
subset-sum {suc k} (outside ∷ A) =
  trans (cong (_+ℤ Σsub (λ γ → if (γ ⊆ᵇ A) then negpow (∣ γ ∣) else 0ℤ))
              (Σsub-0 {k}))
        (trans (+-identityˡ _) (subset-sum A))


------------------------------------------------------------------------
-- Exchanging and collapsing sums

-- Both are needed to evaluate a substitution: its coefficient at γ is
-- a sum over the ways of splitting γ, so the outer sum over γ has to
-- be moved inside and then collapsed against that split.

Σsub-swap : ∀ {l} (f : Subset k → Subset l → ℤ) →
            Σsub (λ s → Σsub (λ t → f s t)) ≡
            Σsub (λ t → Σsub (λ s → f s t))
Σsub-swap {k = zero}  f = refl
Σsub-swap {k = suc k} f = trans
  (cong₂ _+ℤ_ (Σsub-swap (λ s t → f (inside ∷ s) t))
              (Σsub-swap (λ s t → f (outside ∷ s) t)))
  (sym (Σsub-+ (λ t → Σsub (λ s → f (inside ∷ s) t))
               (λ t → Σsub (λ s → f (outside ∷ s) t))))

-- Equality of subsets as a Boolean test, so that it computes on a
-- cons and a delta sum collapses.

infix 5 _≡ᵇ_

_≡ᵇ_ : Subset k → Subset k → Bool
[]            ≡ᵇ []            = true
(inside  ∷ p) ≡ᵇ (inside  ∷ q) = p ≡ᵇ q
(inside  ∷ p) ≡ᵇ (outside ∷ q) = false
(outside ∷ p) ≡ᵇ (inside  ∷ q) = false
(outside ∷ p) ≡ᵇ (outside ∷ q) = p ≡ᵇ q

≡ᵇ⇒≡ : (p q : Subset k) → p ≡ᵇ q ≡ true → p ≡ q
≡ᵇ⇒≡ []            []            _  = refl
≡ᵇ⇒≡ (inside  ∷ p) (inside  ∷ q) eq = cong (inside ∷_) (≡ᵇ⇒≡ p q eq)
≡ᵇ⇒≡ (outside ∷ p) (outside ∷ q) eq = cong (outside ∷_) (≡ᵇ⇒≡ p q eq)

≡⇒≡ᵇ : (p : Subset k) → p ≡ᵇ p ≡ true
≡⇒≡ᵇ []            = refl
≡⇒≡ᵇ (inside  ∷ p) = ≡⇒≡ᵇ p
≡⇒≡ᵇ (outside ∷ p) = ≡⇒≡ᵇ p

⌊≟ˢ⌋ : (p q : Subset k) → ⌊ Vec.≡-dec Bool._≟_ p q ⌋ ≡ p ≡ᵇ q
⌊≟ˢ⌋ p q with Vec.≡-dec Bool._≟_ p q | p ≡ᵇ q in eq
... | yes _   | true  = refl
... | yes p≡q | false = contradiction
      (trans (sym (trans (cong (_≡ᵇ q) p≡q) (≡⇒≡ᵇ q))) eq) λ ()
... | no  ¬p  | true  = contradiction (≡ᵇ⇒≡ p q eq) ¬p
... | no  _   | false = refl

-- A sum whose summand vanishes away from one point is that point's
-- value.

Σsub-delta : (p : Subset k) (h : Subset k → ℤ) →
             Σsub (λ s → if (s ≡ᵇ p) then h s else 0ℤ) ≡ h p
Σsub-delta {k = zero}  []            h = refl
Σsub-delta {k = suc k} (inside ∷ p)  h = trans
  (cong₂ _+ℤ_ (Σsub-delta p (λ s → h (inside ∷ s))) (Σsub-0 {k}))
  (+-identityʳ (h (inside ∷ p)))
Σsub-delta {k = suc k} (outside ∷ p) h = trans
  (cong₂ _+ℤ_ (Σsub-0 {k}) (Σsub-delta p (λ s → h (outside ∷ s))))
  (+-identityˡ (h (outside ∷ p)))


Σmon-swap : (F : Mon n m → Mon n m → ℤ) →
            Σmon (λ γ → Σmon (λ δ → F γ δ)) ≡
            Σmon (λ δ → Σmon (λ γ → F γ δ))
Σmon-swap F =
  trans (Σsub-cong (λ α →
          Σsub-swap (λ β α′ → Σsub (λ β′ → F (α , β) (α′ , β′)))))
  (trans (Σsub-swap (λ α α′ →
          Σsub (λ β → Σsub (λ β′ → F (α , β) (α′ , β′)))))
  (trans (Σsub-cong (λ α′ → Σsub-cong (λ α →
          Σsub-swap (λ β β′ → F (α , β) (α′ , β′)))))
         (Σsub-cong (λ α′ →
          Σsub-swap (λ α β′ → Σsub (λ β → F (α , β) (α′ , β′)))))))

-- Σsub splits on the head of a subset; [HH] substitutes for a
-- variable at an arbitrary index, so the split is needed there too.

Σsub-splitAt : ∀ {k} (i : Fin (suc k)) (f : Subset (suc k) → ℤ) →
               Σsub f ≡
               Σsub (λ s → f (insertAt s i inside) +ℤ f (insertAt s i outside))
Σsub-splitAt zero f =
  sym (Σsub-+ (λ s → f (inside ∷ s)) (λ s → f (outside ∷ s)))
Σsub-splitAt {suc k} (suc i) f =
  cong₂ _+ℤ_ (Σsub-splitAt i (λ s → f (inside ∷ s)))
             (Σsub-splitAt i (λ s → f (outside ∷ s)))

-- Satisfaction distributes over unions of monomials.

private
  ∧-dup : ∀ b p q → b ∧ (p ∧ q) ≡ (b ∧ p) ∧ (b ∧ q)
  ∧-dup true  p q = refl
  ∧-dup false p q = refl

  ∧-mid : ∀ b p q → b ∧ (p ∧ q) ≡ p ∧ (b ∧ q)
  ∧-mid true  p q = refl
  ∧-mid false p q = sym (∧-zeroʳ p)

sat-∪ : (p q : Subset k) (f : Fin k → Bool) →
        sat (p ∪ q) f ≡ sat p f ∧ sat q f
sat-∪ []            []            f = refl
sat-∪ (inside  ∷ p) (inside  ∷ q) f = trans
  (cong (f zero ∧_) (sat-∪ p q (λ i → f (suc i))))
  (∧-dup (f zero) (sat p (λ i → f (suc i))) (sat q (λ i → f (suc i))))
sat-∪ (inside  ∷ p) (outside ∷ q) f = trans
  (cong (f zero ∧_) (sat-∪ p q (λ i → f (suc i))))
  (sym (∧-assoc (f zero) (sat p (λ i → f (suc i)))
                (sat q (λ i → f (suc i)))))
sat-∪ (outside ∷ p) (inside  ∷ q) f = trans
  (cong (f zero ∧_) (sat-∪ p q (λ i → f (suc i))))
  (∧-mid (f zero) (sat p (λ i → f (suc i))) (sat q (λ i → f (suc i))))
sat-∪ (outside ∷ p) (outside ∷ q) f = sat-∪ p q (λ i → f (suc i))

satᵐ-∪ : (γ δ : Mon n m) (x : Fin n → Bool) (y : Fin m → Bool) →
         satᵐ (γ ∪ᵐ δ) x y ≡ satᵐ γ x y ∧ satᵐ δ x y
satᵐ-∪ (α , β) (α′ , β′) x y = trans
  (cong₂ _∧_ (sat-∪ α α′ x) (sat-∪ β β′ y))
  (∧-shuffle (sat α x) (sat α′ x) (sat β y) (sat β′ y))

infix 5 _≡ᵐᵇ_

_≡ᵐᵇ_ : Mon n m → Mon n m → Bool
(α , β) ≡ᵐᵇ (α′ , β′) = (α ≡ᵇ α′) ∧ (β ≡ᵇ β′)

≡ᵐᵇ⇒≡ : (γ δ : Mon n m) → γ ≡ᵐᵇ δ ≡ true → γ ≡ δ
≡ᵐᵇ⇒≡ (α , β) (α′ , β′) eq with ∧-true (α ≡ᵇ α′) (β ≡ᵇ β′) eq
... | e₁ , e₂ = cong₂ _,_ (≡ᵇ⇒≡ α α′ e₁) (≡ᵇ⇒≡ β β′ e₂)

≡⇒≡ᵐᵇ : (γ : Mon n m) → γ ≡ᵐᵇ γ ≡ true
≡⇒≡ᵐᵇ (α , β) = cong₂ _∧_ (≡⇒≡ᵇ α) (≡⇒≡ᵇ β)

⌊≟ᵐ⌋ : (γ δ : Mon n m) → ⌊ γ ≟ᵐ δ ⌋ ≡ γ ≡ᵐᵇ δ
⌊≟ᵐ⌋ γ δ with γ ≟ᵐ δ | γ ≡ᵐᵇ δ in eq
... | yes _   | true  = refl
... | yes γ≡δ | false = contradiction
      (trans (sym (trans (cong (_≡ᵐᵇ δ) γ≡δ) (≡⇒≡ᵐᵇ δ))) eq) λ ()
... | no  ¬p  | true  = contradiction (≡ᵐᵇ⇒≡ γ δ eq) ¬p
... | no  _   | false = refl

if-pull : ∀ (b : Bool) (g : Subset k → ℤ) →
          Σsub (λ s → if b then g s else 0ℤ) ≡ (if b then Σsub g else 0ℤ)
if-pull         true  g = refl
if-pull {k = k} false g = Σsub-0 {k}

Σmon-delta : (γ₀ : Mon n m) (h : Mon n m → ℤ) →
             Σmon (λ γ → if (γ ≡ᵐᵇ γ₀) then h γ else 0ℤ) ≡ h γ₀
Σmon-delta (α₀ , β₀) h =
  trans (Σsub-cong inner) (Σsub-delta α₀ (λ α → h (α , β₀)))
  where
  inner : ∀ α →
    Σsub (λ β → if ((α ≡ᵇ α₀) ∧ (β ≡ᵇ β₀)) then h (α , β) else 0ℤ) ≡
    (if (α ≡ᵇ α₀) then h (α , β₀) else 0ℤ)
  inner α = trans
    (Σsub-cong (λ β → sym (if-∧ (α ≡ᵇ α₀) (β ≡ᵇ β₀) (h (α , β)))))
    (trans (if-pull (α ≡ᵇ α₀)
             (λ β → if (β ≡ᵇ β₀) then h (α , β) else 0ℤ))
           (cong (λ w → if (α ≡ᵇ α₀) then w else 0ℤ)
                 (Σsub-delta β₀ (λ β → h (α , β)))))


------------------------------------------------------------------------
-- Splitting a polynomial at a variable

-- P ∖ᵛ v collects the terms free of v; P /ᵛ v is the quotient by v,
-- so that P is (P ∖ᵛ v) + v · (P /ᵛ v).  Stating substitution this way
-- avoids having to update an assignment at a variable whose position
-- depends on whether it is an input or a path variable.

infixl 6 _∖ᵛ_ _/ᵛ_

_∖ᵛ_ : Poly n m → Var n m → Poly n m
(P ∖ᵛ v) γ = if ⌊ v ∈ᵐ? γ ⌋ then 0ℤ else P γ

_/ᵛ_ : Poly n m → Var n m → Poly n m
(P /ᵛ v) δ = if ⌊ v ∈ᵐ? δ ⌋ then 0ℤ else P (δ ∪ᵐ ⟪ v ⟫)

if-pullᵐ : ∀ (b : Bool) (g : Mon n m → ℤ) →
           Σmon (λ γ → if b then g γ else 0ℤ) ≡ (if b then Σmon g else 0ℤ)
if-pullᵐ         true  g = refl
if-pullᵐ {n} {m} false g = trans
  (Σsub-cong {k = n} {f = λ _ → Σsub {m} (λ _ → 0ℤ)} {g = λ _ → 0ℤ}
             (λ _ → Σsub-0 {m}))
  (Σsub-0 {n})

if-swap : ∀ (p q : Bool) (a : ℤ) →
          (if p then (if q then a else 0ℤ) else 0ℤ) ≡
          (if q then (if p then a else 0ℤ) else 0ℤ)
if-swap true  true  a = refl
if-swap true  false a = refl
if-swap false true  a = refl
if-swap false false a = refl

≡ᵇ-sym : (p q : Subset k) → p ≡ᵇ q ≡ q ≡ᵇ p
≡ᵇ-sym []            []            = refl
≡ᵇ-sym (inside  ∷ p) (inside  ∷ q) = ≡ᵇ-sym p q
≡ᵇ-sym (inside  ∷ p) (outside ∷ q) = refl
≡ᵇ-sym (outside ∷ p) (inside  ∷ q) = refl
≡ᵇ-sym (outside ∷ p) (outside ∷ q) = ≡ᵇ-sym p q

≡ᵐᵇ-sym : (γ δ : Mon n m) → γ ≡ᵐᵇ δ ≡ δ ≡ᵐᵇ γ
≡ᵐᵇ-sym (α , β) (α′ , β′) = cong₂ _∧_ (≡ᵇ-sym α α′) (≡ᵇ-sym β β′)


------------------------------------------------------------------------
-- Evaluation is a homomorphism

Σmon-0 : Σmon {n} {m} (λ _ → 0ℤ) ≡ 0ℤ
Σmon-0 {n} {m} = trans
  (Σsub-cong {k = n} {f = λ _ → Σsub {m} (λ _ → 0ℤ)} {g = λ _ → 0ℤ}
             (λ _ → Σsub-0 {m}))
  (Σsub-0 {n})

Σmon-+ : (f g : Mon n m → ℤ) →
         Σmon (λ γ → f γ +ℤ g γ) ≡ Σmon f +ℤ Σmon g
Σmon-+ {n} {m} f g = trans
  (Σsub-cong (λ α → Σsub-+ (λ β → f (α , β)) (λ β → g (α , β))))
  (Σsub-+ (λ α → Σsub (λ β → f (α , β)))
          (λ α → Σsub (λ β → g (α , β))))

Σsub-neg : (f : Subset k → ℤ) → Σsub (λ s → -ℤ f s) ≡ -ℤ Σsub f
Σsub-neg {k = zero}  f = refl
Σsub-neg {k = suc k} f = trans
  (cong₂ _+ℤ_ (Σsub-neg (λ s → f (inside ∷ s)))
              (Σsub-neg (λ s → f (outside ∷ s))))
  (sym (neg-distrib-+ (Σsub (λ s → f (inside ∷ s)))
                      (Σsub (λ s → f (outside ∷ s)))))

Σmon-neg : (f : Mon n m → ℤ) → Σmon (λ γ → -ℤ f γ) ≡ -ℤ Σmon f
Σmon-neg f = trans (Σsub-cong (λ α → Σsub-neg (λ β → f (α , β))))
                   (Σsub-neg (λ α → Σsub (λ β → f (α , β))))

private
  if-0 : ∀ (b : Bool) → (if b then 0ℤ else 0ℤ) ≡ 0ℤ
  if-0 true  = refl
  if-0 false = refl

eval-+ᴾ : (P Q : Poly n m) (x : Fin n → Bool) (y : Fin m → Bool) →
          eval (P +ᴾ Q) x y ≡ eval P x y +ℤ eval Q x y
eval-+ᴾ P Q x y = trans (Σmon-cong per)
  (Σmon-+ (λ γ → if satᵐ γ x y then P γ else 0ℤ)
          (λ γ → if satᵐ γ x y then Q γ else 0ℤ))
  where
  per : ∀ γ → (if satᵐ γ x y then (P γ +ℤ Q γ) else 0ℤ) ≡
              (if satᵐ γ x y then P γ else 0ℤ) +ℤ
              (if satᵐ γ x y then Q γ else 0ℤ)
  per γ with satᵐ γ x y
  ... | true  = refl
  ... | false = refl

eval-neg : (P : Poly n m) (x : Fin n → Bool) (y : Fin m → Bool) →
           eval (λ γ → -ℤ P γ) x y ≡ -ℤ eval P x y
eval-neg P x y = trans (Σmon-cong per)
  (Σmon-neg (λ γ → if satᵐ γ x y then P γ else 0ℤ))
  where
  per : ∀ γ → (if satᵐ γ x y then (-ℤ P γ) else 0ℤ) ≡
              -ℤ (if satᵐ γ x y then P γ else 0ℤ)
  per γ with satᵐ γ x y
  ... | true  = refl
  ... | false = refl

eval-−ᴾ : (P Q : Poly n m) (x : Fin n → Bool) (y : Fin m → Bool) →
          eval (P -ᴾ Q) x y ≡ eval P x y -ℤ eval Q x y
eval-−ᴾ P Q x y = trans (eval-+ᴾ P (λ γ → -ℤ Q γ) x y)
                        (cong (eval P x y +ℤ_) (eval-neg Q x y))

eval-·ᴾ : (z : ℤ) (P : Poly n m) (x : Fin n → Bool) (y : Fin m → Bool) →
          eval (z ·ᴾ P) x y ≡ z *ℤ eval P x y
eval-·ᴾ z P x y = trans (Σmon-cong (λ γ → if-scale (satᵐ γ x y) z (P γ)))
  (Σmon-scale {z = z} (λ γ → if satᵐ γ x y then P γ else 0ℤ))

eval-κ : (z : ℤ) (x : Fin n → Bool) (y : Fin m → Bool) →
         eval (κ z) x y ≡ z
eval-κ {n} {m} z x y = trans
  (Σmon-⊥ (λ γ → if satᵐ γ x y then κ z γ else 0ℤ))
  (trans (cong₂ _+ℤ_ head tail) (+-identityʳ z))
  where
  head : (if satᵐ (1ᵐ {n} {m}) x y then κ z 1ᵐ else 0ℤ) ≡ z
  head = trans (cong (λ b → if b then κ z (1ᵐ {n} {m}) else 0ℤ)
                     (satᵐ-1ᵐ x y)) at-1ᵐ
    where
    at-1ᵐ : κ z (1ᵐ {n} {m}) ≡ z
    at-1ᵐ with (1ᵐ {n} {m}) ≟ᵐ 1ᵐ
    ... | yes _  = refl
    ... | no  ¬p = contradiction refl ¬p

  tail : Σmon (λ γ → if emptyᵐ γ then 0ℤ
                     else (if satᵐ γ x y then κ z γ else 0ℤ)) ≡ 0ℤ
  tail = trans (Σmon-cong per) (Σmon-0 {n} {m})
    where
    per : ∀ γ → (if emptyᵐ γ then 0ℤ
                 else (if satᵐ γ x y then κ z γ else 0ℤ)) ≡ 0ℤ
    per γ = aux γ (emptyᵐ γ) refl
      where
      aux : ∀ γ b → emptyᵐ γ ≡ b →
            (if b then 0ℤ else (if satᵐ γ x y then κ z γ else 0ℤ)) ≡ 0ℤ
      aux γ true  eq = refl
      aux γ false eq = trans
        (cong (λ w → if satᵐ γ x y then w else 0ℤ)
              (cong (λ b → if b then z else 0ℤ) (trans (⌊≟ᵐ1ᵐ⌋ γ) eq)))
        (if-0 (satᵐ γ x y))

-- Congruent polynomials have congruent values.

eval-≈ : ∀ {d} (P Q : Poly n m) → P ≈[ d ] Q →
         (x : Fin n → Bool) (y : Fin m → Bool) →
         d ∣ (eval P x y -ℤ eval Q x y)
eval-≈ {d = d} P Q P≈Q x y = Eq.subst (d ∣_) (eval-−ᴾ P Q x y)
  (eval-∣ (P -ᴾ Q) P≈Q x y)


Σsub-scaleʳ : ∀ {z} (f : Subset k → ℤ) →
              Σsub (λ s → f s *ℤ z) ≡ Σsub f *ℤ z
Σsub-scaleʳ {k = zero}      f = refl
Σsub-scaleʳ {k = suc k} {z} f = trans
  (cong₂ _+ℤ_ (Σsub-scaleʳ {z = z} (λ s → f (inside ∷ s)))
              (Σsub-scaleʳ {z = z} (λ s → f (outside ∷ s))))
  (sym (*-distribʳ-+ z (Σsub (λ s → f (inside ∷ s)))
                       (Σsub (λ s → f (outside ∷ s)))))


------------------------------------------------------------------------
-- Lemma 2.5: the lifting of a linear Boolean form is Boolean-valued

-- Write A for the variables of S that the assignment makes true.  The
-- lifting evaluates to the constant plus ±(the alternating sum over
-- the non-empty subsets of A), and that sum is 0 or 1 because the sum
-- over *all* subsets of A is ±1.

module _ {n m : ℕ} (c : Bool) (S : Mon n m)
         (x : Fin n → Bool) (y : Fin m → Bool) where

  private
    T : Mon n m
    T = (tabulate x , tabulate y)

    A : Mon n m
    A = T ∩ᵐ S

    G : ℤ
    G = Σmon (λ γ → if emptyᵐ γ then 0ℤ
                    else (if (γ ⊆ᵐᵇ A) then negpow (∥ γ ∥ ∸ 1) else 0ℤ))

    E : ℤ
    E = Σmon (λ γ → if (γ ⊆ᵐᵇ A) then negpow (∥ γ ∥) else 0ℤ)

    C : ℤ
    C = (-ℤ 1ℤ) *ℤ (+ 2)

    -- Splitting off the empty monomial from E leaves -2 times G.

    E-tail : ∀ γ → (if emptyᵐ γ then 0ℤ
                    else (if (γ ⊆ᵐᵇ A) then negpow (∥ γ ∥) else 0ℤ)) ≡
                   C *ℤ (if emptyᵐ γ then 0ℤ
                         else (if (γ ⊆ᵐᵇ A) then negpow (∥ γ ∥ ∸ 1)
                               else 0ℤ))
    E-tail γ = aux γ (emptyᵐ γ) refl
      where
      aux : ∀ γ b → emptyᵐ γ ≡ b →
            (if b then 0ℤ else (if (γ ⊆ᵐᵇ A) then negpow (∥ γ ∥) else 0ℤ)) ≡
            C *ℤ (if b then 0ℤ
                  else (if (γ ⊆ᵐᵇ A) then negpow (∥ γ ∥ ∸ 1) else 0ℤ))
      aux γ true  eq = sym (*-zeroʳ C)
      aux γ false eq = trans
        (cong (λ w → if (γ ⊆ᵐᵇ A) then w else 0ℤ)
          (trans (cong negpow (emptyᵐ-false γ eq)) (negpow-suc (∥ γ ∥ ∸ 1))))
        (if-scale (γ ⊆ᵐᵇ A) C (negpow (∥ γ ∥ ∸ 1)))

    E-split : E ≡ 1ℤ +ℤ (C *ℤ G)
    E-split = trans
      (Σmon-⊥ (λ γ → if (γ ⊆ᵐᵇ A) then negpow (∥ γ ∥) else 0ℤ))
      (cong₂ _+ℤ_ head-val
        (trans (Σmon-cong E-tail)
               (Σmon-scale {z = C}
                 (λ γ → if emptyᵐ γ then 0ℤ
                        else (if (γ ⊆ᵐᵇ A) then negpow (∥ γ ∥ ∸ 1)
                              else 0ℤ)))))
      where
      head-val : (if (1ᵐ ⊆ᵐᵇ A) then negpow (∥ 1ᵐ {n} {m} ∥) else 0ℤ) ≡ 1ℤ
      head-val = trans
        (cong (λ b → if b then negpow (∥ 1ᵐ {n} {m} ∥) else 0ℤ) (1ᵐ⊆ᵐᵇ A))
        (trans (cong negpow (∥1ᵐ∥≡0 {n} {m})) (*-identityˡ 1ℤ))

    -- E factorises, one component per kind of variable.

    E-val : E ≡ ((-ℤ 1ℤ) ^ℤ ∣ proj₁ A ∣) *ℤ ((-ℤ 1ℤ) ^ℤ ∣ proj₂ A ∣)
    E-val = trans (Σsub-cong (λ α → trans (Σsub-cong (split α))
                    (Σsub-scale {z = if (α ⊆ᵇ proj₁ A) then negpow ∣ α ∣
                                     else 0ℤ}
                      (λ β → if (β ⊆ᵇ proj₂ A) then negpow ∣ β ∣ else 0ℤ))))
      (trans (Σsub-scaleʳ
                {z = Σsub (λ β → if (β ⊆ᵇ proj₂ A) then negpow ∣ β ∣
                                 else 0ℤ)}
                (λ α → if (α ⊆ᵇ proj₁ A) then negpow ∣ α ∣ else 0ℤ))
             (cong₂ _*ℤ_ (subset-sum (proj₁ A)) (subset-sum (proj₂ A))))
      where
      split : ∀ α β →
              (if ((α ⊆ᵇ proj₁ A) ∧ (β ⊆ᵇ proj₂ A))
               then negpow (∣ α ∣ + ∣ β ∣) else 0ℤ) ≡
              (if (α ⊆ᵇ proj₁ A) then negpow ∣ α ∣ else 0ℤ) *ℤ
              (if (β ⊆ᵇ proj₂ A) then negpow ∣ β ∣ else 0ℤ)
      split α β = trans
        (cong (λ w → if ((α ⊆ᵇ proj₁ A) ∧ (β ⊆ᵇ proj₂ A)) then w else 0ℤ)
              (negpow-+ ∣ α ∣ ∣ β ∣))
        (if-* (α ⊆ᵇ proj₁ A) (β ⊆ᵇ proj₂ A) (negpow ∣ α ∣) (negpow ∣ β ∣))

    -- The evaluation of the lifting, split the same way.

    eval-tail : ∀ γ →
      (if emptyᵐ γ then 0ℤ
       else (if satᵐ γ x y then liftXor c S γ else 0ℤ)) ≡
      sgn c *ℤ (if emptyᵐ γ then 0ℤ
                else (if (γ ⊆ᵐᵇ A) then negpow (∥ γ ∥ ∸ 1) else 0ℤ))
    eval-tail γ = aux γ (emptyᵐ γ) refl
      where
      aux : ∀ γ b → emptyᵐ γ ≡ b →
        (if b then 0ℤ else (if satᵐ γ x y then liftXor c S γ else 0ℤ)) ≡
        sgn c *ℤ (if b then 0ℤ
                  else (if (γ ⊆ᵐᵇ A) then negpow (∥ γ ∥ ∸ 1) else 0ℤ))
      aux γ true  eq = sym (*-zeroʳ (sgn c))
      aux γ false eq = trans
        (cong (λ w → if satᵐ γ x y then w else 0ℤ)
          (trans
            (cong (λ b → if b then (if c then 1ℤ else 0ℤ)
                         else (if ⌊ γ ⊆ᵐ? S ⌋
                               then sgn c *ℤ negpow (∥ γ ∥ ∸ 1) else 0ℤ))
                  (trans (⌊≟ᵐ1ᵐ⌋ γ) eq))
            (cong (λ b → if b then sgn c *ℤ negpow (∥ γ ∥ ∸ 1) else 0ℤ)
                  (⌊⊆ᵐ?⌋ γ S))))
        (trans
          (cong (λ b → if b then (if (γ ⊆ᵐᵇ S)
                                  then sgn c *ℤ negpow (∥ γ ∥ ∸ 1) else 0ℤ)
                       else 0ℤ)
                (satᵐ-⊆ᵐᵇ γ x y))
          (trans (if-∧ (γ ⊆ᵐᵇ T) (γ ⊆ᵐᵇ S) (sgn c *ℤ negpow (∥ γ ∥ ∸ 1)))
            (trans
              (cong (λ b → if b then sgn c *ℤ negpow (∥ γ ∥ ∸ 1) else 0ℤ)
                    (⊆ᵐᵇ-∩ᵐ γ T S))
              (if-scale (γ ⊆ᵐᵇ A) (sgn c) (negpow (∥ γ ∥ ∸ 1))))))

    eval-split : eval (liftXor c S) x y ≡
                 (if c then 1ℤ else 0ℤ) +ℤ (sgn c *ℤ G)
    eval-split = trans
      (Σmon-⊥ (λ γ → if satᵐ γ x y then liftXor c S γ else 0ℤ))
      (cong₂ _+ℤ_ head-val
        (trans (Σmon-cong eval-tail)
               (Σmon-scale {z = sgn c}
                 (λ γ → if emptyᵐ γ then 0ℤ
                        else (if (γ ⊆ᵐᵇ A) then negpow (∥ γ ∥ ∸ 1)
                              else 0ℤ)))))
      where
      head-val : (if satᵐ (1ᵐ {n} {m}) x y then liftXor c S 1ᵐ else 0ℤ) ≡
                 (if c then 1ℤ else 0ℤ)
      head-val = trans
        (cong (λ b → if b then liftXor c S 1ᵐ else 0ℤ) (satᵐ-1ᵐ x y))
        (liftXor-1ᵐ c S)

    -- E is ±1, so -2·G is 0 or -2, so G is 0 or 1.

    G-0 : E ≡ 1ℤ → G ≡ 0ℤ
    G-0 eq = *-cancelˡ-≡ C G 0ℤ (trans
      (+-cancelˡ-≡ 1ℤ (C *ℤ G) 0ℤ (trans (sym E-split) eq))
      (sym (*-zeroʳ C)))

    G-1 : E ≡ -ℤ 1ℤ → G ≡ 1ℤ
    G-1 eq = *-cancelˡ-≡ C G 1ℤ (trans
      (+-cancelˡ-≡ 1ℤ (C *ℤ G) C (trans (sym E-split) eq))
      (sym (*-identityʳ C)))

    G-value : (G ≡ 0ℤ) ⊎ (G ≡ 1ℤ)
    G-value with neg1-pow ∣ proj₁ A ∣ | neg1-pow ∣ proj₂ A ∣
    ... | inj₁ e₁ | inj₁ e₂ = inj₁ (G-0 (trans E-val (cong₂ _*ℤ_ e₁ e₂)))
    ... | inj₁ e₁ | inj₂ e₂ = inj₂ (G-1 (trans E-val (cong₂ _*ℤ_ e₁ e₂)))
    ... | inj₂ e₁ | inj₁ e₂ = inj₂ (G-1 (trans E-val (cong₂ _*ℤ_ e₁ e₂)))
    ... | inj₂ e₁ | inj₂ e₂ = inj₁ (G-0 (trans E-val (cong₂ _*ℤ_ e₁ e₂)))

    finish : ∀ (b : Bool) (g : ℤ) → (g ≡ 0ℤ) ⊎ (g ≡ 1ℤ) →
             (((if b then 1ℤ else 0ℤ) +ℤ (sgn b *ℤ g)) ≡ 0ℤ) ⊎
             (((if b then 1ℤ else 0ℤ) +ℤ (sgn b *ℤ g)) ≡ 1ℤ)
    finish true  g (inj₁ e) = inj₂ (cong (λ w → 1ℤ +ℤ ((-ℤ 1ℤ) *ℤ w)) e)
    finish true  g (inj₂ e) = inj₁ (cong (λ w → 1ℤ +ℤ ((-ℤ 1ℤ) *ℤ w)) e)
    finish false g (inj₁ e) = inj₁ (cong (λ w → 0ℤ +ℤ (1ℤ *ℤ w)) e)
    finish false g (inj₂ e) = inj₂ (cong (λ w → 0ℤ +ℤ (1ℤ *ℤ w)) e)

  -- Lemma 2.5.

  liftXor-value : (eval (liftXor c S) x y ≡ 0ℤ) ⊎
                  (eval (liftXor c S) x y ≡ 1ℤ)
  liftXor-value with finish c G G-value
  ... | inj₁ e = inj₁ (trans eval-split e)
  ... | inj₂ e = inj₂ (trans eval-split e)


------------------------------------------------------------------------
-- The lifted linear Boolean forms

-- Every coefficient of the lifting of  c ⊕ ⨁_{u ∈ S} u  is divisible
-- by 2^(|γ|-1); the constant coefficient is only claimed to be
-- divisible by 2^0 = 1.

liftXor-∣ : ∀ {n m} (c : Bool) (S γ : Mon n m) →
            (+ (2 ^ (∥ γ ∥ ∸ 1))) ∣ liftXor c S γ
liftXor-∣ {n} {m} c S γ with γ ≟ᵐ 1ᵐ
... | yes γ≡1ᵐ rewrite γ≡1ᵐ = Eq.subst
        (λ z → (+ (2 ^ (z ∸ 1))) ∣ (if c then 1ℤ else 0ℤ))
        (sym (∥1ᵐ∥≡0 {n} {m})) 1∣i
... | no  _    with γ ⊆ᵐ? S
...   | yes _ = ∣n⇒∣m*n (sgn c) (∣n⇒∣m*n ((-ℤ 1ℤ) ^ℤ (∥ γ ∥ ∸ 1)) ∣-refl)
...   | no  _ = i∣0


------------------------------------------------------------------------
-- Evaluating a substitution

-- The coefficient of subst P at γ sums over the ways of splitting γ,
-- so evaluating it moves the sum over γ inside and collapses it: only
-- the splitting δ ∪ β = γ survives.

private
  collapse : ∀ {n m} (P : Poly n m) (v : Var n m) (c : Bool) (S : Mon n m)
             (x : Fin n → Bool) (y : Fin m → Bool) (δ β : Mon n m) →
             Σmon (λ γ → if satᵐ γ x y
                         then substTerm P v c S γ δ β else 0ℤ) ≡
             (if ⌊ v ∈ᵐ? δ ⌋ then 0ℤ
              else (if satᵐ (δ ∪ᵐ β) x y
                    then P (δ ∪ᵐ ⟪ v ⟫) *ℤ liftXor c S β else 0ℤ))
  collapse {n} {m} P v c S x y δ β with v ∈ᵐ? δ
  ... | yes _ = trans (Σmon-cong {g = λ _ → 0ℤ} (λ γ → if-0 (satᵐ γ x y)))
                      (Σmon-0 {n} {m})
  ... | no  _ = trans (Σmon-cong step)
        (Σmon-delta (δ ∪ᵐ β)
          (λ γ → if satᵐ γ x y
                 then P (δ ∪ᵐ ⟪ v ⟫) *ℤ liftXor c S β else 0ℤ))
    where
    X : ℤ
    X = P (δ ∪ᵐ ⟪ v ⟫) *ℤ liftXor c S β

    step : ∀ γ →
      (if satᵐ γ x y
       then (if ⌊ (δ ∪ᵐ β) ≟ᵐ γ ⌋ then X else 0ℤ) else 0ℤ) ≡
      (if (γ ≡ᵐᵇ (δ ∪ᵐ β))
       then (if satᵐ γ x y then X else 0ℤ) else 0ℤ)
    step γ = trans
      (cong (λ b → if satᵐ γ x y then (if b then X else 0ℤ) else 0ℤ)
            (trans (⌊≟ᵐ⌋ (δ ∪ᵐ β) γ) (≡ᵐᵇ-sym (δ ∪ᵐ β) γ)))
      (if-swap (satᵐ γ x y) (γ ≡ᵐᵇ (δ ∪ᵐ β)) X)

-- With the inner sum collapsed, the sum over β factors: the part of P
-- depending on the substituted variable comes out, and what is left is
-- the evaluation of the lifted form.

private
  if-+ : ∀ (p : Bool) (a b : ℤ) →
         (if p then (a +ℤ b) else 0ℤ) ≡
         (if p then a else 0ℤ) +ℤ (if p then b else 0ℤ)
  if-+ true  a b = refl
  if-+ false a b = refl

  factor : ∀ {n m} (P : Poly n m) (v : Var n m) (c : Bool) (S : Mon n m)
           (x : Fin n → Bool) (y : Fin m → Bool) (δ : Mon n m) →
           Σmon (λ β → if ⌊ v ∈ᵐ? δ ⌋ then 0ℤ
                       else (if satᵐ (δ ∪ᵐ β) x y
                             then P (δ ∪ᵐ ⟪ v ⟫) *ℤ liftXor c S β
                             else 0ℤ)) ≡
           eval (liftXor c S) x y *ℤ
           (if satᵐ δ x y then (P /ᵛ v) δ else 0ℤ)
  factor {n} {m} P v c S x y δ with v ∈ᵐ? δ
  ... | yes _ = trans (Σmon-0 {n} {m})
        (sym (trans (cong (eval (liftXor c S) x y *ℤ_) (if-0 (satᵐ δ x y)))
                    (*-zeroʳ (eval (liftXor c S) x y))))
  ... | no  _ = trans inner outer
    where
    L : Mon n m → ℤ
    L = liftXor c S

    Pv : ℤ
    Pv = P (δ ∪ᵐ ⟪ v ⟫)

    inner : Σmon (λ β → if satᵐ (δ ∪ᵐ β) x y then Pv *ℤ L β else 0ℤ) ≡
            (if satᵐ δ x y then (Pv *ℤ eval L x y) else 0ℤ)
    inner = trans
      (Σmon-cong (λ β → trans
        (cong (λ b → if b then Pv *ℤ L β else 0ℤ) (satᵐ-∪ δ β x y))
        (sym (if-∧ (satᵐ δ x y) (satᵐ β x y) (Pv *ℤ L β)))))
      (trans
        (if-pullᵐ (satᵐ δ x y)
                  (λ β → if satᵐ β x y then Pv *ℤ L β else 0ℤ))
        (cong (λ z → if satᵐ δ x y then z else 0ℤ)
          (trans (Σmon-cong (λ β → if-scale (satᵐ β x y) Pv (L β)))
                 (Σmon-scale {z = Pv}
                   (λ β → if satᵐ β x y then L β else 0ℤ)))))

    outer : (if satᵐ δ x y then (Pv *ℤ eval L x y) else 0ℤ) ≡
            eval L x y *ℤ (if satᵐ δ x y then Pv else 0ℤ)
    outer = trans (cong (λ z → if satᵐ δ x y then z else 0ℤ)
                        (*-comm Pv (eval L x y)))
                  (if-scale (satᵐ δ x y) (eval L x y) Pv)

-- Lemma 2.13's companion at the level of values: substituting the form
-- c ⊕ ⨁S for v is, under evaluation, multiplying the quotient by the
-- value of the form.

eval-subst : ∀ {n m} (P : Poly n m) (v : Var n m) (c : Bool) (S : Mon n m)
             (x : Fin n → Bool) (y : Fin m → Bool) →
             eval (subst P v c S) x y ≡
             eval (P ∖ᵛ v) x y +ℤ
             (eval (liftXor c S) x y *ℤ eval (P /ᵛ v) x y)
eval-subst {n} {m} P v c S x y =
  trans step1 (cong (eval (P ∖ᵛ v) x y +ℤ_) step2)
  where
  T : Mon n m → Mon n m → Mon n m → ℤ
  T = substTerm P v c S

  U : Mon n m → Mon n m → Mon n m → ℤ
  U γ δ β = if satᵐ γ x y then T γ δ β else 0ℤ

  step1 : eval (subst P v c S) x y ≡
          eval (P ∖ᵛ v) x y +ℤ
          Σmon (λ γ → if satᵐ γ x y
                      then Σmon (λ δ → Σmon (T γ δ)) else 0ℤ)
  step1 = trans
    (Σmon-cong (λ γ → if-+ (satᵐ γ x y) ((P ∖ᵛ v) γ)
                           (Σmon (λ δ → Σmon (T γ δ)))))
    (Σmon-+ (λ γ → if satᵐ γ x y then (P ∖ᵛ v) γ else 0ℤ)
            (λ γ → if satᵐ γ x y
                   then Σmon (λ δ → Σmon (T γ δ)) else 0ℤ))

  step2 : Σmon (λ γ → if satᵐ γ x y
                      then Σmon (λ δ → Σmon (T γ δ)) else 0ℤ) ≡
          eval (liftXor c S) x y *ℤ eval (P /ᵛ v) x y
  step2 = trans
    -- push the guard through both inner sums
    (Σmon-cong (λ γ → sym (trans
      (Σmon-cong (λ δ → if-pullᵐ (satᵐ γ x y) (T γ δ)))
      (if-pullᵐ (satᵐ γ x y) (λ δ → Σmon (T γ δ))))))
    (trans
      -- move the γ sum innermost
      (trans (Σmon-swap (λ γ δ → Σmon (λ β → U γ δ β)))
             (Σmon-cong (λ δ → Σmon-swap (λ γ β → U γ δ β))))
      (trans
        -- collapse it against the splitting, then factor
        (Σmon-cong (λ δ → Σmon-cong (λ β → collapse P v c S x y δ β)))
        (trans (Σmon-cong (λ δ → factor P v c S x y δ))
               (Σmon-scale {z = eval (liftXor c S) x y}
                 (λ δ → if satᵐ δ x y then (P /ᵛ v) δ else 0ℤ)))))


------------------------------------------------------------------------
-- Splitting a sum at a variable

-- The dual of the substitution lemma: a sum splits at any variable,
-- the subsets omitting it each contributing twice, once with it and
-- once without.  Combined with the substitution lemma this says that
-- evaluating subst P v c S at an assignment is evaluating P at the
-- assignment updated to give v the value of the form.

private
  ⌊∈?⌋-suc : ∀ {k} (i : Fin k) (b : Bool) (s : Subset k) →
             ⌊ suc i ∈? (b ∷ s) ⌋ ≡ ⌊ i ∈? s ⌋
  ⌊∈?⌋-suc i b s with i ∈? s
  ... | yes _ = refl
  ... | no  _ = refl

  if-pullᵉ : ∀ (b : Bool) (g : Subset k → ℤ) →
             Σsub (λ s → if b then 0ℤ else g s) ≡ (if b then 0ℤ else Σsub g)
  if-pullᵉ {k = k} true  g = Σsub-0 {k}
  if-pullᵉ         false g = refl

Σsub-at : ∀ {k} (i : Fin k) (f : Subset k → ℤ) →
          Σsub f ≡
          Σsub (λ s → if ⌊ i ∈? s ⌋ then 0ℤ else (f s +ℤ f (s ∪ ⁅ i ⁆)))
Σsub-at {suc k} zero f = sym (trans
  (cong₂ _+ℤ_ (Σsub-0 {k})
              (trans (Σsub-cong (λ s →
                        cong (λ t → f (outside ∷ s) +ℤ f (inside ∷ t))
                             (∪-identityʳ s)))
                     (Σsub-+ (λ s → f (outside ∷ s))
                             (λ s → f (inside ∷ s)))))
  (trans (+-identityˡ (Σsub (λ s → f (outside ∷ s)) +ℤ
                       Σsub (λ s → f (inside ∷ s))))
         (+-comm (Σsub (λ s → f (outside ∷ s)))
                 (Σsub (λ s → f (inside ∷ s))))))
Σsub-at {suc k} (suc i) f = trans
  (cong₂ _+ℤ_ (Σsub-at i (λ s → f (inside  ∷ s)))
              (Σsub-at i (λ s → f (outside ∷ s))))
  (cong₂ _+ℤ_ (Σsub-cong (λ s → adjust inside  s))
              (Σsub-cong (λ s → adjust outside s)))
  where
  adjust : ∀ (b : Bool) (s : Subset k) →
           (if ⌊ i ∈? s ⌋ then 0ℤ
            else (f (b ∷ s) +ℤ f (b ∷ (s ∪ ⁅ i ⁆)))) ≡
           (if ⌊ suc i ∈? (b ∷ s) ⌋ then 0ℤ
            else (f (b ∷ s) +ℤ f (b ∷ (s ∪ ⁅ i ⁆))))
  adjust b s = cong (λ t → if t then 0ℤ
                           else (f (b ∷ s) +ℤ f (b ∷ (s ∪ ⁅ i ⁆))))
                    (sym (⌊∈?⌋-suc i b s))

Σmon-at : ∀ {n m} (v : Var n m) (g : Mon n m → ℤ) →
          Σmon g ≡
          Σmon (λ δ → if ⌊ v ∈ᵐ? δ ⌋ then 0ℤ
                      else (g δ +ℤ g (δ ∪ᵐ ⟪ v ⟫)))
Σmon-at {n} {m} x[ i ] g = trans
  (Σsub-at i (λ α → Σsub (λ β → g (α , β))))
  (Σsub-cong (λ α → sym (trans
    (Σsub-cong (λ β →
      cong (λ t → if ⌊ i ∈? α ⌋ then 0ℤ
                  else (g (α , β) +ℤ g (α ∪ ⁅ i ⁆ , t)))
           (∪-identityʳ β)))
    (trans (if-pullᵉ ⌊ i ∈? α ⌋
             (λ β → g (α , β) +ℤ g (α ∪ ⁅ i ⁆ , β)))
           (cong (λ z → if ⌊ i ∈? α ⌋ then 0ℤ else z)
                 (Σsub-+ (λ β → g (α , β))
                         (λ β → g (α ∪ ⁅ i ⁆ , β))))))))
Σmon-at {n} {m} y[ j ] g =
  Σsub-cong (λ α → trans
    (Σsub-at j (λ β → g (α , β)))
    (Σsub-cong (λ β →
      cong (λ t → if ⌊ j ∈? β ⌋ then 0ℤ
                  else (g (α , β) +ℤ g (t , β ∪ ⁅ j ⁆)))
           (sym (∪-identityʳ α)))))

-- The value of a variable at an assignment.

valᵛ : Var n m → (Fin n → Bool) → (Fin m → Bool) → Bool
valᵛ x[ i ] x y = x i
valᵛ y[ j ] x y = y j

sat-⁅⁆ : (i : Fin k) (f : Fin k → Bool) → sat ⁅ i ⁆ f ≡ f i
sat-⁅⁆ zero    f = trans (cong (f zero ∧_) (sat-⊥ (λ i → f (suc i))))
                         (Bool.∧-identityʳ (f zero))
sat-⁅⁆ (suc i) f = sat-⁅⁆ i (λ j → f (suc j))

satᵐ-⟪⟫ : (v : Var n m) (x : Fin n → Bool) (y : Fin m → Bool) →
          satᵐ ⟪ v ⟫ x y ≡ valᵛ v x y
satᵐ-⟪⟫ x[ i ] x y = trans (cong₂ _∧_ (sat-⁅⁆ i x) (sat-⊥ y))
                           (Bool.∧-identityʳ (x i))
satᵐ-⟪⟫ y[ j ] x y = cong₂ _∧_ (sat-⊥ x) (sat-⁅⁆ j y)

private
  if-e+ : ∀ (p : Bool) (a b : ℤ) →
          (if p then 0ℤ else (a +ℤ b)) ≡
          (if p then 0ℤ else a) +ℤ (if p then 0ℤ else b)
  if-e+ true  a b = refl
  if-e+ false a b = refl

  if-eswap : ∀ (p q : Bool) (a : ℤ) →
             (if p then 0ℤ else (if q then a else 0ℤ)) ≡
             (if q then (if p then 0ℤ else a) else 0ℤ)
  if-eswap true  true  a = refl
  if-eswap true  false a = refl
  if-eswap false true  a = refl
  if-eswap false false a = refl

  partB : ∀ {n m} (P : Poly n m) (v : Var n m)
          (x : Fin n → Bool) (y : Fin m → Bool) →
          Σmon (λ δ → if ⌊ v ∈ᵐ? δ ⌋ then 0ℤ
                      else (if (satᵐ δ x y ∧ valᵛ v x y)
                            then P (δ ∪ᵐ ⟪ v ⟫) else 0ℤ)) ≡
          (if valᵛ v x y then 1ℤ else 0ℤ) *ℤ eval (P /ᵛ v) x y
  partB {n} {m} P v x y with valᵛ v x y
  ... | true  = trans
        (Σmon-cong (λ δ → trans
          (cong (λ b → if ⌊ v ∈ᵐ? δ ⌋ then 0ℤ
                       else (if b then P (δ ∪ᵐ ⟪ v ⟫) else 0ℤ))
                (Bool.∧-identityʳ (satᵐ δ x y)))
          (if-eswap ⌊ v ∈ᵐ? δ ⌋ (satᵐ δ x y) (P (δ ∪ᵐ ⟪ v ⟫)))))
        (sym (*-identityˡ (eval (P /ᵛ v) x y)))
  ... | false = trans
        (trans
          (Σmon-cong {g = λ _ → 0ℤ} (λ δ → trans
            (cong (λ b → if ⌊ v ∈ᵐ? δ ⌋ then 0ℤ
                         else (if b then P (δ ∪ᵐ ⟪ v ⟫) else 0ℤ))
                  (∧-zeroʳ (satᵐ δ x y)))
            (if-0 ⌊ v ∈ᵐ? δ ⌋)))
          (Σmon-0 {n} {m}))
        (sym (*-zeroˡ (eval (P /ᵛ v) x y)))

-- Evaluation splits at a variable: the terms free of it, plus its
-- value times the value of the quotient.

eval-split : ∀ {n m} (P : Poly n m) (v : Var n m)
             (x : Fin n → Bool) (y : Fin m → Bool) →
             eval P x y ≡
             eval (P ∖ᵛ v) x y +ℤ
             ((if valᵛ v x y then 1ℤ else 0ℤ) *ℤ eval (P /ᵛ v) x y)
eval-split {n} {m} P v x y = trans
  (Σmon-at v (λ γ → if satᵐ γ x y then P γ else 0ℤ))
  (trans (Σmon-cong (λ δ → if-e+ ⌊ v ∈ᵐ? δ ⌋ (g δ) (g (δ ∪ᵐ ⟪ v ⟫))))
  (trans (Σmon-+ (λ δ → if ⌊ v ∈ᵐ? δ ⌋ then 0ℤ else g δ)
                 (λ δ → if ⌊ v ∈ᵐ? δ ⌋ then 0ℤ else g (δ ∪ᵐ ⟪ v ⟫)))
         (cong₂ _+ℤ_ partA partB′)))
  where
  g : Mon n m → ℤ
  g γ = if satᵐ γ x y then P γ else 0ℤ

  partA : Σmon (λ δ → if ⌊ v ∈ᵐ? δ ⌋ then 0ℤ else g δ) ≡ eval (P ∖ᵛ v) x y
  partA = Σmon-cong (λ δ → if-eswap ⌊ v ∈ᵐ? δ ⌋ (satᵐ δ x y) (P δ))

  partB′ : Σmon (λ δ → if ⌊ v ∈ᵐ? δ ⌋ then 0ℤ else g (δ ∪ᵐ ⟪ v ⟫)) ≡
           (if valᵛ v x y then 1ℤ else 0ℤ) *ℤ eval (P /ᵛ v) x y
  partB′ = trans
    (Σmon-cong (λ δ →
      cong (λ b → if ⌊ v ∈ᵐ? δ ⌋ then 0ℤ
                  else (if b then P (δ ∪ᵐ ⟪ v ⟫) else 0ℤ))
           (trans (satᵐ-∪ δ ⟪ v ⟫ x y)
                  (cong (satᵐ δ x y ∧_) (satᵐ-⟪⟫ v x y)))))
    (partB P v x y)

-- Hence the two agree wherever the assignment already gives v the
-- value of the form -- which is exactly where [HH]'s branches survive
-- interference, so no assignment ever has to be updated.

eval-subst-fixed :
  ∀ {n m} (P : Poly n m) (v : Var n m) (c : Bool) (S : Mon n m)
  (x : Fin n → Bool) (y : Fin m → Bool) →
  (if valᵛ v x y then 1ℤ else 0ℤ) ≡ eval (liftXor c S) x y →
  eval (subst P v c S) x y ≡ eval P x y
eval-subst-fixed P v c S x y eq = trans
  (eval-subst P v c S x y)
  (sym (trans (eval-split P v x y)
              (cong (λ z → eval (P ∖ᵛ v) x y +ℤ (z *ℤ eval (P /ᵛ v) x y))
                    eq)))


------------------------------------------------------------------------
-- Evaluation respects pointwise equality of assignments

-- An assignment is a function, so two assignments agreeing everywhere
-- need not be equal.  Splitting a sum over assignments at an index
-- produces exactly such a pair, so evaluation has to be known to
-- respect the pointwise relation.

sat-cong : (p : Subset k) {f g : Fin k → Bool} → (∀ i → f i ≡ g i) →
           sat p f ≡ sat p g
sat-cong []            f≗g = refl
sat-cong (inside  ∷ p) f≗g =
  cong₂ _∧_ (f≗g zero) (sat-cong p (λ i → f≗g (suc i)))
sat-cong (outside ∷ p) f≗g = sat-cong p (λ i → f≗g (suc i))

satᵐ-cong : (γ : Mon n m) {x x′ : Fin n → Bool} {y y′ : Fin m → Bool} →
            (∀ i → x i ≡ x′ i) → (∀ j → y j ≡ y′ j) →
            satᵐ γ x y ≡ satᵐ γ x′ y′
satᵐ-cong (α , β) x≗ y≗ = cong₂ _∧_ (sat-cong α x≗) (sat-cong β y≗)

eval-cong : (P : Poly n m) {x x′ : Fin n → Bool} {y y′ : Fin m → Bool} →
            (∀ i → x i ≡ x′ i) → (∀ j → y j ≡ y′ j) →
            eval P x y ≡ eval P x′ y′
eval-cong P x≗ y≗ = Σmon-cong (λ γ →
  cong (λ b → if b then P γ else 0ℤ) (satᵐ-cong γ x≗ y≗))

-- Satisfaction reads the assignment only at the variables of the
-- monomial, so a polynomial mentioning no monomial containing v has a
-- value insensitive to the assignment at v.

sat-cong-⊆ : (p : Subset k) {f g : Fin k → Bool} →
             (∀ j → j ∈ p → f j ≡ g j) → sat p f ≡ sat p g
sat-cong-⊆ []            h = refl
sat-cong-⊆ (inside  ∷ p) h =
  cong₂ _∧_ (h zero here) (sat-cong-⊆ p (λ j j∈p → h (suc j) (there j∈p)))
sat-cong-⊆ (outside ∷ p) h =
  sat-cong-⊆ p (λ j j∈p → h (suc j) (there j∈p))

eval-off : ∀ {n m} (Q : Poly n m) (i : Fin m) →
           (∀ γ → y[ i ] ∈ᵐ γ → Q γ ≡ 0ℤ) →
           (x : Fin n → Bool) (y y′ : Fin m → Bool) →
           (∀ j → ¬ (j ≡ i) → y j ≡ y′ j) →
           eval Q x y ≡ eval Q x y′
eval-off {n} {m} Q i hyp x y y′ agree =
  trans (kill y) (trans (Σmon-cong step) (sym (kill y′)))
  where
  kill : ∀ w → eval Q x w ≡
         Σmon (λ δ → if ⌊ y[ i ] ∈ᵐ? δ ⌋ then 0ℤ
                     else (if satᵐ δ x w then Q δ else 0ℤ))
  kill w = trans
    (Σmon-at y[ i ] (λ γ → if satᵐ γ x w then Q γ else 0ℤ))
    (Σmon-cong (λ δ →
      cong (λ z → if ⌊ y[ i ] ∈ᵐ? δ ⌋ then 0ℤ else z)
        (trans
          (cong (λ z → (if satᵐ δ x w then Q δ else 0ℤ) +ℤ z)
            (trans
              (cong (λ z → if satᵐ (δ ∪ᵐ ⟪ y[ i ] ⟫) x w then z else 0ℤ)
                    (hyp (δ ∪ᵐ ⟪ y[ i ] ⟫) (v∈δ∪⟪v⟫ δ y[ i ])))
              (if-0 (satᵐ (δ ∪ᵐ ⟪ y[ i ] ⟫) x w))))
          (+-identityʳ (if satᵐ δ x w then Q δ else 0ℤ)))))

  step : ∀ δ →
         (if ⌊ y[ i ] ∈ᵐ? δ ⌋ then 0ℤ
          else (if satᵐ δ x y then Q δ else 0ℤ)) ≡
         (if ⌊ y[ i ] ∈ᵐ? δ ⌋ then 0ℤ
          else (if satᵐ δ x y′ then Q δ else 0ℤ))
  step (α , β) with i ∈? β
  ... | yes _   = refl
  ... | no  i∉β = cong (λ b → if b then Q (α , β) else 0ℤ)
        (cong (sat α x ∧_)
          (sat-cong-⊆ β (λ j j∈β →
            agree j (λ j≡i → i∉β (Eq.subst (_∈ β) j≡i j∈β)))))

-- A substituted polynomial mentions no monomial containing the
-- substituted variable, provided the form does not contain it either:
-- the only surviving splittings put the variable in the part read by
-- the form, whose lifting is supported on subsets of S.

v∉1ᵐ : (v : Var n m) → ¬ (v ∈ᵐ 1ᵐ)
v∉1ᵐ x[ i ] = ∉⊥
v∉1ᵐ y[ j ] = ∉⊥

∈ᵐ-mono : (v : Var n m) {γ δ : Mon n m} → γ ⊆ᵐ δ → v ∈ᵐ γ → v ∈ᵐ δ
∈ᵐ-mono x[ i ] (α⊆ , _) v∈ = α⊆ v∈
∈ᵐ-mono y[ j ] (_ , β⊆) v∈ = β⊆ v∈

∈ᵐ-∪ : (v : Var n m) (δ β : Mon n m) →
       ¬ (v ∈ᵐ δ) → v ∈ᵐ (δ ∪ᵐ β) → v ∈ᵐ β
∈ᵐ-∪ x[ i ] (α , _) (α′ , _) v∉δ v∈ with x∈p∪q⁻ α α′ v∈
... | inj₁ p = contradiction p v∉δ
... | inj₂ q = q
∈ᵐ-∪ y[ j ] (_ , β) (_ , β′) v∉δ v∈ with x∈p∪q⁻ β β′ v∈
... | inj₁ p = contradiction p v∉δ
... | inj₂ q = q

liftXor-0 : (c : Bool) (S γ : Mon n m) (v : Var n m) →
            v ∈ᵐ γ → ¬ (v ∈ᵐ S) → liftXor c S γ ≡ 0ℤ
liftXor-0 c S γ v v∈γ v∉S with γ ≟ᵐ 1ᵐ
... | yes refl = contradiction v∈γ (v∉1ᵐ v)
... | no  _ with γ ⊆ᵐ? S
...   | yes γ⊆S = contradiction (∈ᵐ-mono v γ⊆S v∈γ) v∉S
...   | no  _   = refl

subst-0 : ∀ {n m} (P : Poly n m) (v : Var n m) (c : Bool) (S : Mon n m) →
          ¬ (v ∈ᵐ S) → ∀ γ → v ∈ᵐ γ → subst P v c S γ ≡ 0ℤ
subst-0 {n} {m} P v c S v∉S γ v∈γ = cong₂ _+ℤ_ first
  (trans (Σmon-cong {g = λ _ → 0ℤ} (λ δ →
           trans (Σmon-cong {g = λ _ → 0ℤ} (each δ)) (Σmon-0 {n} {m})))
         (Σmon-0 {n} {m}))
  where
  first : (if ⌊ v ∈ᵐ? γ ⌋ then 0ℤ else P γ) ≡ 0ℤ
  first with v ∈ᵐ? γ
  ... | yes _ = refl
  ... | no ¬p = contradiction v∈γ ¬p

  each : ∀ δ β → substTerm P v c S γ δ β ≡ 0ℤ
  each δ β with v ∈ᵐ? δ
  ... | yes _ = refl
  ... | no v∉δ with (δ ∪ᵐ β) ≟ᵐ γ
  ...   | no  _  = refl
  ...   | yes eq = trans
          (cong (λ z → P (δ ∪ᵐ ⟪ v ⟫) *ℤ z)
            (liftXor-0 c S β v
              (∈ᵐ-∪ v δ β v∉δ (Eq.subst (v ∈ᵐ_) (sym eq) v∈γ)) v∉S))
          (*-zeroʳ (P (δ ∪ᵐ ⟪ v ⟫)))
