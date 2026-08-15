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
open import Data.Bool.Properties using (∧-zeroʳ)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Subset using
  (Subset; inside; outside; ⁅_⁆; ⊥; _∪_; _∩_; _∈_; _∉_; _⊆_; ∣_∣)
open import Data.Fin.Subset.Properties using
  (∣⊥∣≡0; ∣⁅x⁆∣≡1; ∪-identityʳ; drop-not-there; drop-∷-⊆; q⊆p∪q;
   x∈⁅x⁆; _⊆?_)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_)
  renaming (-_ to -ℤ_; _^_ to _^ℤ_; _+_ to _+ℤ_; _*_ to _*ℤ_)
open import Data.Integer.Properties using
  (+-identityˡ; +-identityʳ; *-identityˡ; *-zeroʳ; *-distribˡ-+; pos-*)
open import Data.Integer.Divisibility.Signed using
  (_∣_; ∣-refl; ∣-trans; ∣ᵤ⇒∣; ∣m∣n⇒∣m+n; ∣n⇒∣m*n; ∣m⇒∣m*n)
open import Data.Nat.Base using
  (ℕ; zero; suc; _+_; _*_; _∸_; _^_; _≤_; z≤n; s≤s)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Vec.Base using (Vec; []; _∷_; here; there; tabulate)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Decidable using (Dec; yes; no; ⌊_⌋; _×?_)
open import Relation.Nullary.Negation using (¬_; contradiction)

open import PathSum.Polynomial

import Data.Integer.Solver as ℤSolver
import Data.Nat.Divisibility as ℕDiv
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
