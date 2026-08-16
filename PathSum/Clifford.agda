------------------------------------------------------------------------
-- Presentations of groups
--
-- Clifford completeness (Amy, QPL 2018, section 4.3)
--
-- Over the Clifford group the phase polynomial of a path-sum has
-- order at most 2.  Lemma 4.3 says that such a path-sum, if it has
-- only internal path variables and denotes the identity, always
-- admits a reduction whose phase again has order at most 2;
-- corollary 4.4 iterates this to a decision procedure.  Both are
-- proved below, over the semantic interface of PathSum.Semantics.
--
-- The module is parameterised by M₀, the denominator of the phase
-- being 2^(3 + M₀): three dyadic digits are what an order-2
-- polynomial can use, and any further precision is inert.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; z≤n; s≤s)

import PathSum.Semantics as Sem

module PathSum.Clifford
  (M₀ : ℕ) (sem : Sem.Semantics (suc (suc (suc M₀))))
  where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Subset using
  (Subset; Side; inside; outside; ⁅_⁆; ⊥; _∈_; _⊆_; ∣_∣)
open import Data.Fin.Subset.Properties using
  (Empty-unique; ∉⊥; ⊥⊆; x∈⁅x⁆; x∈⁅y⁆⇒x≡y)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; -_; _*_; _-_)
  renaming (_+_ to _+ℤ_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; _∣?_; ∣-refl; ∣-trans; ∣m∣n⇒∣m+n; ∣m∣n⇒∣m-n; *-monoʳ-∣)
open import Data.Integer.Properties using
  (+-identityˡ; +-identityʳ; *-identityˡ; *-identityʳ; *-zeroʳ;
   neg-involutive; neg-distribʳ-*)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Vec.Base using (Vec; []; _∷_; tabulate; here; there)
open import Data.Vec.Properties using
  (lookup∘tabulate; []=⇒lookup; lookup⇒[]=)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Decidable using (Dec; yes; no; ⌊_⌋)
open import Relation.Nullary.Negation using (¬_; contradiction)

open import PathSum.Base
open import PathSum.Order (suc (suc (suc M₀)))
open import PathSum.Polynomial
open import PathSum.Polynomial.Properties
open import PathSum.Reduction (suc (suc (suc M₀)))
open import PathSum.Semantics (suc (suc (suc M₀))) using (Semantics)

import Data.Bool.Properties as Bool
import Data.Nat.Properties as ℕ
import Data.Vec.Properties as Vec
import Relation.Binary.PropositionalEquality as Eq

open Semantics sem
open +-*-Solver using (solve; con; _:+_; _:-_; _:*_; _:=_)

private
  M : ℕ
  M = suc (suc (suc M₀))

  variable
    n k m : ℕ


------------------------------------------------------------------------
-- Reading off coefficients

private
  κ-1ᵐ : (c : ℤ) → κ {n} {m} c 1ᵐ ≡ c
  κ-1ᵐ {n} {m} c with (1ᵐ {n} {m}) ≟ᵐ 1ᵐ
  ... | yes _ = refl
  ... | no ¬p = contradiction refl ¬p

  κ-≢ : (c : ℤ) {γ : Mon n m} → γ ≢ 1ᵐ → κ c γ ≡ 0ℤ
  κ-≢ c {γ} γ≢ with γ ≟ᵐ 1ᵐ
  ... | yes p = contradiction p γ≢
  ... | no  _ = refl

  liftXor-∈ : (c : Bool) (S : Mon n m) {γ : Mon n m} → γ ≢ 1ᵐ → γ ⊆ᵐ S →
              liftXor c S γ ≡ sgn c * negpow (∥ γ ∥ ∸ 1)
  liftXor-∈ c S {γ} γ≢ γ⊆ with γ ≟ᵐ 1ᵐ
  ... | yes p = contradiction p γ≢
  ... | no  _ with γ ⊆ᵐ? S
  ...   | yes _ = refl
  ...   | no ¬q = contradiction γ⊆ ¬q

  liftXor-∉ : (c : Bool) (S : Mon n m) {γ : Mon n m} → γ ≢ 1ᵐ →
              ¬ (γ ⊆ᵐ S) → liftXor c S γ ≡ 0ℤ
  liftXor-∉ c S {γ} γ≢ γ⊄ with γ ≟ᵐ 1ᵐ
  ... | yes p = contradiction p γ≢
  ... | no  _ with γ ⊆ᵐ? S
  ...   | yes q = contradiction q γ⊄
  ...   | no  _ = refl


------------------------------------------------------------------------
-- Monomials of degree at most two

private
  ⟪v⟫≢1ᵐ : (v : Var n m) → ⟪ v ⟫ ≢ 1ᵐ
  ⟪v⟫≢1ᵐ {n} {m} v ⟪v⟫≡1ᵐ
    with trans (sym (∥⟪v⟫∥≡1 v)) (trans (cong ∥_∥ ⟪v⟫≡1ᵐ) (∥1ᵐ∥≡0 {n} {m}))
  ... | ()

  ⟪v⟫⊆ : (v : Var n m) (S : Mon n m) → v ∈ᵐ S → ⟪ v ⟫ ⊆ᵐ S
  ⟪v⟫⊆ x[ i ] (α , β) i∈α =
    (λ x∈⁅i⁆ → Eq.subst (_∈ α) (sym (x∈⁅y⁆⇒x≡y i x∈⁅i⁆)) i∈α) , ⊥⊆
  ⟪v⟫⊆ y[ j ] (α , β) j∈β =
    ⊥⊆ , (λ x∈⁅j⁆ → Eq.subst (_∈ β) (sym (x∈⁅y⁆⇒x≡y j x∈⁅j⁆)) j∈β)

  ⟪v⟫⊄ : (v : Var n m) (S : Mon n m) → ¬ (v ∈ᵐ S) → ¬ (⟪ v ⟫ ⊆ᵐ S)
  ⟪v⟫⊄ x[ i ] (α , β) v∉S (p , _) = v∉S (p (x∈⁅x⁆ i))
  ⟪v⟫⊄ y[ j ] (α , β) v∉S (_ , q) = v∉S (q (x∈⁅x⁆ j))

  ⊆1ᵐ : {γ : Mon n m} → γ ⊆ᵐ 1ᵐ → γ ≡ 1ᵐ
  ⊆1ᵐ {γ = α , β} (p , q) = cong₂ _,_
    (Empty-unique (λ (_ , x∈α) → ∉⊥ (p x∈α)))
    (Empty-unique (λ (_ , x∈β) → ∉⊥ (q x∈β)))

  liftXor-1ᵐ-0 : (γ : Mon n m) → liftXor false 1ᵐ γ ≡ 0ℤ
  liftXor-1ᵐ-0 γ with γ ≟ᵐ 1ᵐ
  ... | yes _  = refl
  ... | no  γ≢ with γ ⊆ᵐ? 1ᵐ
  ...   | yes γ⊆ = contradiction (⊆1ᵐ γ⊆) γ≢
  ...   | no  _  = refl

data Shape {n m : ℕ} (γ : Mon n m) : Set where
  const  : γ ≡ 1ᵐ → Shape γ
  single : (v : Var n m) → γ ≡ ⟪ v ⟫ → Shape γ
  big    : 2 ≤ ∥ γ ∥ → Shape γ

shape : (γ : Mon n m) → Shape γ
shape γ with ∥ γ ∥ in ∥γ∥≡
... | zero        = const (∥γ∥≡0⇒γ≡1ᵐ γ ∥γ∥≡)
... | suc zero    = single (proj₁ (∥γ∥≡1⇒γ≡⟪v⟫ γ ∥γ∥≡))
                           (proj₂ (∥γ∥≡1⇒γ≡⟪v⟫ γ ∥γ∥≡))
... | suc (suc t) = big (ℕ.≤-trans (s≤s (s≤s z≤n))
                                   (ℕ.≤-reflexive (sym ∥γ∥≡)))


------------------------------------------------------------------------
-- The support of a quotient

-- The set of variables whose coefficient in Q does not vanish.  For a
-- second-order quotient this is the S of the linear form ½(c ⊕ ⨁ S).

private
  sel : Poly n m → Var n m → Side
  sel Q u = if ⌊ pow M ∣? Q ⟪ u ⟫ ⌋ then outside else inside

  sel-inside : (Q : Poly n m) (u : Var n m) →
               ¬ (pow M ∣ Q ⟪ u ⟫) → sel Q u ≡ inside
  sel-inside Q u ¬d with pow M ∣? Q ⟪ u ⟫
  ... | yes d = contradiction d ¬d
  ... | no  _ = refl

  sel-outside : (Q : Poly n m) (u : Var n m) →
                pow M ∣ Q ⟪ u ⟫ → sel Q u ≡ outside
  sel-outside Q u d with pow M ∣? Q ⟪ u ⟫
  ... | yes _ = refl
  ... | no ¬d = contradiction d ¬d

  ∈tabulate⁺ : ∀ {k} (f : Fin k → Side) (i : Fin k) →
               f i ≡ inside → i ∈ tabulate f
  ∈tabulate⁺ f i eq =
    lookup⇒[]= i (tabulate f) (trans (lookup∘tabulate f i) eq)

  ∈tabulate⁻ : ∀ {k} (f : Fin k → Side) (i : Fin k) →
               i ∈ tabulate f → f i ≡ inside
  ∈tabulate⁻ f i i∈ = trans (sym (lookup∘tabulate f i)) ([]=⇒lookup i∈)

supp : Poly n m → Mon n m
supp Q = tabulate (λ i → sel Q x[ i ]) , tabulate (λ j → sel Q y[ j ])

private
  ∈supp⁺ : (Q : Poly n m) (u : Var n m) →
           ¬ (pow M ∣ Q ⟪ u ⟫) → u ∈ᵐ supp Q
  ∈supp⁺ Q x[ i ] ¬d = ∈tabulate⁺ _ i (sel-inside Q x[ i ] ¬d)
  ∈supp⁺ Q y[ j ] ¬d = ∈tabulate⁺ _ j (sel-inside Q y[ j ] ¬d)

  ∈supp⁻ : (Q : Poly n m) (u : Var n m) →
           u ∈ᵐ supp Q → ¬ (pow M ∣ Q ⟪ u ⟫)
  ∈supp⁻ Q x[ i ] u∈ d
    with trans (sym (∈tabulate⁻ _ i u∈)) (sel-outside Q x[ i ] d)
  ... | ()
  ∈supp⁻ Q y[ j ] u∈ d
    with trans (sym (∈tabulate⁻ _ j u∈)) (sel-outside Q y[ j ] d)
  ... | ()

  ∉supp : (Q : Poly n m) (u : Var n m) →
          ¬ (u ∈ᵐ supp Q) → pow M ∣ Q ⟪ u ⟫
  ∉supp Q u u∉ with pow M ∣? Q ⟪ u ⟫
  ... | yes d = d
  ... | no ¬d = contradiction (∈supp⁺ Q u ¬d) u∉


------------------------------------------------------------------------
-- The two leading dyadic digits

private
  ½+½ : ½ +ℤ ½ ≡ pow M
  ½+½ = trans (sym (double ½)) (sym (pow-suc (M ∸ 1)))
    where
    double : ∀ i → i * (+ 2) ≡ i +ℤ i
    double = solve 1 (λ i → i :* con (+ 2) := i :+ i) refl

  shift : ∀ x → (x - ½) +ℤ pow M ≡ x +ℤ ½
  shift x = trans (cong ((x - ½) +ℤ_) (sym ½+½)) (lem x ½)
    where
    lem : ∀ i h → (i - h) +ℤ (h +ℤ h) ≡ i +ℤ h
    lem = solve 2 (λ i h → (i :- h) :+ (h :+ h) := i :+ h) refl

  -- The two half-integers ±½ agree modulo 2^M.

  sgn-shift : (c : Bool) (x : ℤ) →
              pow M ∣ (x - ½) → pow M ∣ (x - (½ * sgn c))
  sgn-shift false x d =
    Eq.subst (λ z → pow M ∣ (x - z)) (sym (*-identityʳ ½)) d
  sgn-shift true  x d = Eq.subst (λ z → pow M ∣ (x - z)) (sym half≡)
    (Eq.subst (pow M ∣_) (sym (x+½ x)) (∣m∣n⇒∣m+n d ∣-refl))
    where
    half≡ : ½ * sgn true ≡ - ½
    half≡ = trans (sym (neg-distribʳ-* ½ 1ℤ)) (cong -_ (*-identityʳ ½))

    x+½ : ∀ i → i - (- ½) ≡ (i - ½) +ℤ pow M
    x+½ i = trans (cong (i +ℤ_) (neg-involutive ½)) (sym (shift i))


------------------------------------------------------------------------
-- The second-order decomposition of a quotient

-- Lemma 4.3 writes the quotient of a second-order phase polynomial by
-- an internal path variable as ¼a + ½bQ₀ with a, b in Z₂ and Q₀ a
-- linear Boolean form.  Given the constant part ¼a as `base`, the
-- ½-part is read off from the coefficients of Q: its set of variables
-- is the support of Q, and its constant is the remaining dyadic digit
-- of the coefficient of 1.

module _ {n m : ℕ} (Q : Poly n m) (base : ℤ)
         (prof⟪⟫ : ∀ v → pow (M ∸ 1) ∣ Q ⟪ v ⟫)
         (prof≥2 : ∀ γ → 2 ≤ ∥ γ ∥ → pow M ∣ Q γ)
         where

  private
    build : (c : Bool) →
            pow M ∣ (Q 1ᵐ - (base +ℤ (½ * (if c then 1ℤ else 0ℤ)))) →
            Q ≈[ pow M ] (κ base +ᴾ (½ ·ᴾ liftXor c (supp Q)))
    build c cst γ with shape γ

    -- The constant coefficient: this is the hypothesis.
    ... | const γ≡1ᵐ = Eq.subst
      (λ z → pow M ∣ (Q z - (κ base z +ℤ (½ * liftXor c (supp Q) z))))
      (sym γ≡1ᵐ) at1ᵐ
      where
      rhs : κ base (1ᵐ {n} {m}) +ℤ (½ * liftXor c (supp Q) (1ᵐ {n} {m})) ≡
            base +ℤ (½ * (if c then 1ℤ else 0ℤ))
      rhs = cong₂ _+ℤ_ (κ-1ᵐ {n} {m} base)
                       (cong (½ *_) (liftXor-1ᵐ {n} {m} c (supp Q)))

      at1ᵐ : pow M ∣ (Q 1ᵐ - (κ base (1ᵐ {n} {m}) +ℤ
                              (½ * liftXor c (supp Q) (1ᵐ {n} {m}))))
      at1ᵐ = Eq.subst (λ z → pow M ∣ (Q 1ᵐ - z)) (sym rhs) cst

    -- A linear coefficient: it is ½ exactly on the support of Q.
    ... | single v γ≡⟪v⟫ = Eq.subst
      (λ z → pow M ∣ (Q z - (κ base z +ℤ (½ * liftXor c (supp Q) z))))
      (sym γ≡⟪v⟫) at⟪v⟫
      where
      at⟪v⟫ : pow M ∣
              (Q ⟪ v ⟫ - (κ base ⟪ v ⟫ +ℤ (½ * liftXor c (supp Q) ⟪ v ⟫)))
      at⟪v⟫ with v ∈ᵐ? supp Q
      ... | yes v∈S = Eq.subst (λ z → pow M ∣ (Q ⟪ v ⟫ - z)) (sym rhs)
        (sgn-shift c (Q ⟪ v ⟫)
          (digit (M ∸ 1) (prof⟪⟫ v) (∈supp⁻ Q v v∈S)))
        where
        coeff : sgn c * negpow (∥ ⟪ v ⟫ ∥ ∸ 1) ≡ sgn c
        coeff = trans (cong (λ z → sgn c * negpow (z ∸ 1)) (∥⟪v⟫∥≡1 v))
          (trans (cong (sgn c *_) (*-identityˡ 1ℤ)) (*-identityʳ (sgn c)))

        rhs : κ base ⟪ v ⟫ +ℤ (½ * liftXor c (supp Q) ⟪ v ⟫) ≡ ½ * sgn c
        rhs = trans (cong₂ _+ℤ_ (κ-≢ base (⟪v⟫≢1ᵐ v))
                (cong (½ *_)
                  (liftXor-∈ c (supp Q) (⟪v⟫≢1ᵐ v) (⟪v⟫⊆ v (supp Q) v∈S))))
              (trans (+-identityˡ _) (cong (½ *_) coeff))
      ... | no v∉S = Eq.subst (λ z → pow M ∣ (Q ⟪ v ⟫ - z)) (sym rhs)
        (Eq.subst (pow M ∣_) (sym (+-identityʳ (Q ⟪ v ⟫))) (∉supp Q v v∉S))
        where
        rhs : κ base ⟪ v ⟫ +ℤ (½ * liftXor c (supp Q) ⟪ v ⟫) ≡ 0ℤ
        rhs = trans (cong₂ _+ℤ_ (κ-≢ base (⟪v⟫≢1ᵐ v))
                (cong (½ *_)
                  (liftXor-∉ c (supp Q) (⟪v⟫≢1ᵐ v) (⟪v⟫⊄ v (supp Q) v∉S))))
              (trans (+-identityˡ _) (*-zeroʳ ½))

    -- A coefficient of degree at least two: both sides vanish.
    ... | big 2≤ = Eq.subst (λ z → pow M ∣ (Q γ - z)) (sym rhs)
      (∣m∣n⇒∣m-n (prof≥2 γ 2≤) liftdiv)
      where
      γ≢1ᵐ : γ ≢ 1ᵐ
      γ≢1ᵐ γ≡1ᵐ with Eq.subst (2 ≤_)
                       (trans (cong ∥_∥ γ≡1ᵐ) (∥1ᵐ∥≡0 {n} {m})) 2≤
      ... | ()

      rhs : κ base γ +ℤ (½ * liftXor c (supp Q) γ) ≡
            ½ * liftXor c (supp Q) γ
      rhs = trans (cong (_+ℤ (½ * liftXor c (supp Q) γ)) (κ-≢ base γ≢1ᵐ))
                  (+-identityˡ _)

      bound : M ≤ (M ∸ 1) + (∥ γ ∥ ∸ 1)
      bound = ℕ.≤-trans (ℕ.≤-reflexive (sym (ℕ.+-comm (M ∸ 1) 1)))
                        (ℕ.+-monoʳ-≤ (M ∸ 1) (ℕ.∸-monoˡ-≤ 1 2≤))

      liftdiv : pow M ∣ (½ * liftXor c (supp Q) γ)
      liftdiv = ∣-trans (pow-∣ bound)
        (Eq.subst (_∣ (½ * liftXor c (supp Q) γ))
          (pow-+ (M ∸ 1) (∥ γ ∥ ∸ 1))
          (*-monoʳ-∣ ½ (liftXor-∣ c (supp Q) γ)))

  decompose : pow (M ∸ 1) ∣ (Q 1ᵐ - base) →
              ∃ λ c → Q ≈[ pow M ] (κ base +ᴾ (½ ·ᴾ liftXor c (supp Q)))
  decompose hbase with pow M ∣? (Q 1ᵐ - base)
  ... | yes h = false , build false
    (Eq.subst (λ z → pow M ∣ (Q 1ᵐ - (base +ℤ z))) (sym (*-zeroʳ ½))
      (Eq.subst (pow M ∣_)
        (cong (λ w → Q 1ᵐ - w) (sym (+-identityʳ base))) h))
  ... | no ¬h = true , build true
    (Eq.subst (λ z → pow M ∣ (Q 1ᵐ - (base +ℤ z))) (sym (*-identityʳ ½))
      (Eq.subst (pow M ∣_) (regroup (Q 1ᵐ) base ½)
        (digit (M ∸ 1) hbase ¬h)))
    where
    regroup : ∀ i b h → (i - b) - h ≡ i - (b +ℤ h)
    regroup = solve 3 (λ i b h → (i :- b) :- h := i :- (b :+ h)) refl


------------------------------------------------------------------------
-- The profile of a second-order quotient

private
  head-ord : {P : Poly n (suc m)} {d : ℕ} → Ord≤ d P →
             ∀ δ → pow (val d (suc ∥ δ ∥)) ∣ head-part P δ
  head-ord {P = P} {d} ordP (α , β) =
    Eq.subst (λ z → pow (val d z) ∣ P (α , inside ∷ β))
             (ℕ.+-suc (∣ α ∣) (∣ β ∣)) (ordP (α , inside ∷ β))

module _ {n m : ℕ} {P : Poly n (suc m)} (ordP : Ord≤ 2 P) where

  prof1ᵐ : pow (M ∸ 2) ∣ head-part P 1ᵐ
  prof1ᵐ = Eq.subst (λ z → pow (val 2 (suc z)) ∣ head-part P 1ᵐ)
                    (∥1ᵐ∥≡0 {n} {m}) (head-ord ordP 1ᵐ)

  prof⟪⟫ : ∀ v → pow (M ∸ 1) ∣ head-part P ⟪ v ⟫
  prof⟪⟫ v = Eq.subst (λ z → pow (val 2 (suc z)) ∣ head-part P ⟪ v ⟫)
                      (∥⟪v⟫∥≡1 v) (head-ord ordP ⟪ v ⟫)

  prof≥2 : ∀ γ → 2 ≤ ∥ γ ∥ → pow M ∣ head-part P γ
  prof≥2 γ 2≤ = Eq.subst (λ z → pow z ∣ head-part P γ)
                         (cong (M ∸_) (ℕ.m≤n⇒m∸n≡0 (s≤s 2≤)))
                         (head-ord ordP γ)


------------------------------------------------------------------------
-- Lemma 4.3: progress and preservation

private
  findPath : ∀ {k} (β : Subset k) → (∃ λ j → j ∈ β) ⊎ (β ≡ ⊥)
  findPath []            = inj₂ refl
  findPath (inside ∷ β)  = inj₁ (zero , here)
  findPath (outside ∷ β) with findPath β
  ... | inj₁ (j , j∈β) = inj₁ (suc j , there j∈β)
  ... | inj₂ β≡⊥       = inj₂ (cong (outside ∷_) β≡⊥)

  _≟ˢ_ : ∀ {k} (p q : Subset k) → Dec (p ≡ q)
  _≟ˢ_ = Vec.≡-dec Bool._≟_

-- Either a rule of figure 2 applies, preserving both the order bound
-- and internality of the path variables, or ξ is not the identity.
--
-- With the normalisation exponent explicit there is a third
-- possibility, which the paper's lemma 4.3 does not discuss: the
-- interference pattern of the phase calls for [ω] or for [Elim], but
-- the normalisation of ξ is smaller than the rule consumes -- one
-- unit for [ω], two for [Elim] -- so no rule applies.  Such a ξ is
-- not the identity either, since summing away a path variable
-- without paying for it leaves entries of magnitude √2 or 2; but
-- that is an argument about magnitudes rather than about rewriting,
-- and it is not formalised here.

data Progress {n k m : ℕ} (ξ : PathSum n k (suc m)) : Set where
  reduces    : ∀ {k′} (ξ′ : PathSum n k′ m) → ξ ⟶ ξ′ → Internal ξ′ →
               Ord≤ 2 (phase ξ′) → Progress ξ
  not-id     : ¬ (ξ ≋ idPS) → Progress ξ
  undersized : k < 2 → Progress ξ

private
  -- Cases 1 and 2 of lemma 4.3: the quotient is ½Q₀.  If Q₀ contains
  -- a path variable, [HH] applies; if Q₀ is zero, [Elim] applies; and
  -- otherwise Q₀ is a non-zero form in the input variables alone, so
  -- lemma 4.2 shows ξ is not the identity.
  -- [Elim] consumes two units of normalisation.
  case-elim : (ξ : PathSum n k (suc m)) → Internal ξ → Ord≤ 2 (phase ξ) →
              head-part (phase ξ) ≈[ pow M ] 0ᴾ → Progress ξ
  case-elim {k = zero}          ξ int ordP eq = undersized (s≤s z≤n)
  case-elim {k = suc zero}      ξ int ordP eq = undersized (s≤s (s≤s z≤n))
  case-elim {k = suc (suc k)}   ξ int ordP eq =
    reduces (elim-reduct ξ) (elim ξ eq (int zero))
            (tail-Internal ξ int) (tail-Ord≤ ordP)

  finish : (ξ : PathSum n k (suc m)) → Internal ξ → Ord≤ 2 (phase ξ) →
           (c : Bool) (S : Mon n m) →
           head-part (phase ξ) ≈[ pow M ] (½ ·ᴾ liftXor c S) →
           Progress ξ
  finish ξ int ordP c S eq with findPath (proj₂ S)
  ... | inj₁ (i , i∈β) = reduces
    (hh-reduct ξ i c S)
    (hh ξ i c S i∈β eq (int zero))
    (λ j w → subst-NoVar (tail-part (out ξ w)) i c (S ∖ᵐ y[ i ])
               (λ j′ → tail-Internal ξ int j′ w) j)
    (subst-Ord≤ (tail-part (phase ξ)) y[ i ] c (S ∖ᵐ y[ i ])
                (tail-Ord≤ ordP))
  finish ξ int ordP true  S eq | inj₂ β≡⊥ =
    not-id (interference ξ true S eq (int zero) β≡⊥ λ ())
  finish ξ int ordP false S eq | inj₂ β≡⊥ with proj₁ S ≟ˢ ⊥
  ... | no ¬α≡⊥ = not-id (interference ξ false S eq (int zero) β≡⊥
                           λ (_ , S≡1ᵐ) → ¬α≡⊥ (cong proj₁ S≡1ᵐ))
  ... | yes α≡⊥ = case-elim ξ int ordP elim-eq
    where
    S≡1ᵐ : S ≡ 1ᵐ
    S≡1ᵐ = cong₂ _,_ α≡⊥ β≡⊥

    elim-eq : head-part (phase ξ) ≈[ pow M ] 0ᴾ
    elim-eq γ = Eq.subst (λ z → pow M ∣ (head-part (phase ξ) γ - z))
      (trans (cong (λ z → ½ * liftXor false z γ) S≡1ᵐ)
        (trans (cong (½ *_) (liftXor-1ᵐ-0 γ)) (*-zeroʳ ½)))
      (eq γ)

  -- Case 3 of lemma 4.3: the quotient is ¼ + ½Q₀ and [ω] applies,
  -- consuming one unit of normalisation.
  caseω : (ξ : PathSum n k (suc m)) → Internal ξ →
          (ordP : Ord≤ 2 (phase ξ)) →
          (∃ λ c → head-part (phase ξ) ≈[ pow M ]
             (κ ¼ +ᴾ (½ ·ᴾ liftXor c (supp (head-part (phase ξ)))))) →
          Progress ξ
  caseω {k = zero}  ξ int ordP _ = undersized (s≤s z≤n)
  caseω {k = suc k} ξ int ordP (c , eq) = reduces
    (ω-reduct ξ c (supp (head-part (phase ξ))))
    (ω ξ c (supp (head-part (phase ξ))) eq (int zero))
    (tail-Internal ξ int)
    (Ord≤-+ (Ord≤-∸ (Ord≤-κ ∣-refl)
      (Ord≤-liftXor 2 c (supp (head-part (phase ξ)))))
      (tail-Ord≤ ordP))

  case0 : (ξ : PathSum n k (suc m)) → Internal ξ → Ord≤ 2 (phase ξ) →
          (∃ λ c → head-part (phase ξ) ≈[ pow M ]
             (κ 0ℤ +ᴾ (½ ·ᴾ liftXor c (supp (head-part (phase ξ)))))) →
          Progress ξ
  case0 ξ int ordP (c , eq) =
    finish ξ int ordP c (supp (head-part (phase ξ)))
      (λ γ → Eq.subst (λ z → pow M ∣ (head-part (phase ξ) γ - z))
               (drop γ) (eq γ))
    where
    drop : ∀ γ → κ 0ℤ γ +ℤ (½ * liftXor c (supp (head-part (phase ξ))) γ) ≡
                 ½ * liftXor c (supp (head-part (phase ξ))) γ
    drop γ with γ ≟ᵐ 1ᵐ
    ... | yes _ = +-identityˡ _
    ... | no  _ = +-identityˡ _

progress : (ξ : PathSum n k (suc m)) → Internal ξ → Ord≤ 2 (phase ξ) →
           Progress ξ
progress ξ int ordP with pow (M ∸ 1) ∣? head-part (phase ξ) 1ᵐ
... | no ¬a = caseω ξ int ordP
  (decompose (head-part (phase ξ)) ¼ (prof⟪⟫ ordP) (prof≥2 ordP)
    (digit (M ∸ 2) (prof1ᵐ ordP) ¬a))
... | yes a = case0 ξ int ordP
  (decompose (head-part (phase ξ)) 0ℤ (prof⟪⟫ ordP) (prof≥2 ordP)
    (Eq.subst (pow (M ∸ 1) ∣_)
      (sym (+-identityʳ (head-part (phase ξ) 1ᵐ))) a))

-- Lemma 4.3 as stated in the paper, together with the side condition
-- on the normalisation that the paper leaves implicit.

lemma-4-3 : (ξ : PathSum n k (suc m)) → Internal ξ → Ord≤ 2 (phase ξ) →
            ξ ≋ idPS →
            (∃ λ k′ → ∃ λ (ξ′ : PathSum n k′ m) →
               (ξ ⟶ ξ′) × Ord≤ 2 (phase ξ′))
            ⊎ (k < 2)
lemma-4-3 ξ int ordP ξ≋id with progress ξ int ordP
... | reduces {k′} ξ′ step _ ord′ = inj₁ (k′ , ξ′ , step , ord′)
... | not-id ¬id                  = contradiction ξ≋id ¬id
... | undersized k<2              = inj₂ k<2


------------------------------------------------------------------------
-- Corollary 4.4: deciding equivalence of Clifford circuits

-- Iterating lemma 4.3 either exhausts the path variables, leaving a
-- path-sum with no path variable left to sum over -- and denoting the
-- same operator as ξ, by proposition 3.1 -- or proves outright that ξ
-- is not the identity.  Two things the paper's corollary states are
-- not formalised: the polynomial time bound, and the reduction of the
-- general case to this one, which is the isometry restriction of
-- section 4.1 followed by Gaussian elimination.

data Reduces {n k m : ℕ} (ξ : PathSum n k m) : Set where
  done  : ∀ {k′} {ξ′ : PathSum n k′ 0} → ξ ⟶* ξ′ → Reduces ξ
  no-id : ¬ (ξ ≋ idPS) → Reduces ξ
  stuck : ∀ {k′ m′} {ξ′ : PathSum n k′ (suc m′)} → ξ ⟶* ξ′ → k′ < 2 →
          Reduces ξ

corollary-4-4 : (ξ : PathSum n k m) → Internal ξ → Ord≤ 2 (phase ξ) →
                Reduces ξ
corollary-4-4 {m = zero}  ξ int ordP = done ε
corollary-4-4 {m = suc m} ξ int ordP with progress ξ int ordP
... | not-id ¬id      = no-id ¬id
... | undersized k<2  = stuck ε k<2
... | reduces ξ′ step int′ ord′ with corollary-4-4 ξ′ int′ ord′
...   | done steps       = done (step ◅ steps)
...   | stuck steps k<2  = stuck (step ◅ steps) k<2
...   | no-id ¬id        =
        no-id λ ξ≋id → ¬id (≋-trans (≋-sym (⟶-sound step)) ξ≋id)
