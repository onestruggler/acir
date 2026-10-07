------------------------------------------------------------------------
-- Presentations of groups
--
-- The Clifford hierarchy (Amy, QPL 2018, preliminaries)
--
-- The paper recalls the Clifford hierarchy: "C₁ is the Pauli group and
-- C_k = {U | U C₁ U† ⊆ C_(k-1)}", the Clifford group being C₂.  Here
-- that is a family of predicates on the operators of
-- PathSum.Hierarchy.Operator, by recursion on k exactly as printed:
--
--    𝒞 1 U        U is a Pauli, U ≈ i^a X^x Z^z for some data;
--    𝒞 (k + 1) U  U is unitary, and U P U† ∈ 𝒞 k for every Pauli P,
--
-- and 𝒞 0 is empty, the hierarchy starting at 1.  "Every Pauli" ranges
-- over the data of PathSum.Hierarchy.Pauli, which name every element
-- of the Pauli group; as 𝒞 k respects ≈ (𝒞-resp), that is the same as
-- ranging over the Pauli operators.  The paper leaves "unitary"
-- implicit in its unitary picture; here it is part of the definition.
-- The operators are those with entries in Z[ζ, 1/√2], ζ = e^(2πi/2^M);
-- the hierarchy within them is the paper's intersected with them (see
-- PathSum.Hierarchy.Operator).
--
-- What is proved here holds for every n and M:
--
--   * 𝒞 k is invariant under ≈, and its members are unitary;
--   * the levels increase, 𝒞 k ⊆ 𝒞 (k + 1) (𝒞-mono), every Pauli and
--     the identity being in every level;
--   * every level is closed under multiplying by a power of i
--     (𝒞-i, so by a sign), from the second on by any global phase ζ^e
--     (𝒞-◃), and under multiplying by a Pauli on the right
--     (𝒞-·pauli);
--   * from the second level on, under multiplying on the right by an
--     element of 𝒞 2 (𝒞-·₂); in particular 𝒞 2 is closed under
--     products (𝒞₂-·) and contains I: the Clifford group;
--   * the generator form: U ∈ 𝒞 2 exactly when U is unitary and
--     conjugates each X_j and each Z_j to a Pauli (𝒞₂⇔gen), and
--     U ∈ 𝒞 3 exactly when U is unitary and conjugates each X_j and
--     each Z_j into 𝒞 2 (𝒞₃⇔gen).  Both rest on every Pauli being a
--     phase times a product of generators (module Decompose), and on
--     𝒞 1 and 𝒞 2 being closed under products; 𝒞 k for k ≥ 3 is not
--     (PathSum.Hierarchy.Circuits), so the generator form is claimed
--     at these two levels only;
--   * for a unitary U, "U P U† is the Pauli Q" and "U P = Q U" are the
--     same (conj⇔intertwine), which is how gates are shown to be in
--     𝒞 2: by computing how they intertwine the generators
--     (𝒞₂-by-intertwining).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Hierarchy (M₀ : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; T; not; if_then_else_; _∧_; _xor_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; toℕ; fromℕ<)
open import Data.Integer.Base using (ℤ; 0ℤ; +_; -_; _+_; _*_)
open import Data.Integer.Properties using
  (+-inverseˡ; *-zeroʳ; +-identityˡ; +-identityʳ)
open import Data.Nat.Base using (zero; _<_; _<ᵇ_; _≡ᵇ_)
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Nullary.Negation using (¬_; contradiction)

import Data.Fin.Properties as Fin
import Data.Nat.Properties as ℕ

open import PathSum.Assign using ([_]ᶻ)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.Hierarchy.Operator M₀
open import PathSum.Hierarchy.Pauli M₀
open import PathSum.RelativePhase M₀ using (_≡ᴺ_; ≡ᴺ-refl; ≡ᴺ-≡)

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- The hierarchy

-- Membership of the Pauli group.

IsPauli : Op n → Set
IsPauli {n} U = Σ[ p ∈ PauliData n ] U ≈ pauli p

-- 𝒞 k, k ≥ 1.

𝒞 : ℕ → Op n → Set
𝒞 zero          U = ⊥
𝒞 (suc zero)    U = IsPauli U
𝒞 (suc (suc k)) U = Unitary U × (∀ p → 𝒞 (suc k) (U · pauli p · U †))


------------------------------------------------------------------------
-- Conjugates

conj-cong : {U V : Op n} → U ≈ V → (P : Op n) → U · P · U † ≈ V · P · V †
conj-cong e P = ·-cong (·-congˡ P e) (†-cong e)

conj-congᴾ : (U : Op n) {P Q : Op n} → P ≈ Q → U · P · U † ≈ U · Q · U †
conj-congᴾ U e = ·-congˡ (U †) (·-congʳ U e)

-- Conjugating by a product conjugates by each factor in turn.

conj-· : (A B P : Op n) → A · B · P · (A · B) † ≈ A · (B · P · B †) · A †
conj-· A B P =
  ·-congʳ (A · B · P) (†-· A B)
  ⟨≈⟩ ·-congˡ (B † · A †) (·-assoc A B P)
  ⟨≈⟩ ·-assoc A (B · P) (B † · A †)
  ⟨≈⟩ ·-congʳ A (≈-sym (·-assoc (B · P) (B †) (A †)))
  ⟨≈⟩ ≈-sym (·-assoc A (B · P · B †) (A †))

-- A phase passes through a conjugation, and cancels when it is the
-- conjugating operator's.

conj-◃ : (e : ℤ) (U P : Op n) → U · (e ◃ P) · U † ≈ e ◃ (U · P · U †)
conj-◃ e U P = ·-congˡ (U †) (◃-·ʳ e U P) ⟨≈⟩ ◃-·ˡ e (U · P) (U †)

◃-conj : (e : ℤ) (U P : Op n) → (e ◃ U) · P · (e ◃ U) † ≈ U · P · U †
◃-conj e U P =
  ·-cong (◃-·ˡ e U P) (◃-† e U)
  ⟨≈⟩ ◃-·ʳ (- e) (e ◃ (U · P)) (U †)
  ⟨≈⟩ ◃-cong (- e) (◃-·ˡ e (U · P) (U †))
  ⟨≈⟩ ◃-◃ (- e) e (U · P · U †)
  ⟨≈⟩ ◃-exp (U · P · U †) (+-inverseˡ e)
  ⟨≈⟩ ◃-0 (U · P · U †)

-- For a unitary, conjugating a product is the product of the
-- conjugates.

conj-split : (U P Q : Op n) → Unitary U →
             U · (P · Q) · U † ≈ (U · P · U †) · (U · Q · U †)
conj-split U P Q u = ≈-sym (
  ·-assoc (U · P) (U †) (U · Q · U †)
  ⟨≈⟩ ·-congʳ (U · P) (≈-sym (·-assoc (U †) (U · Q) (U †)))
  ⟨≈⟩ ·-congʳ (U · P) (·-congˡ (U †) (cancelˡ U Q u))
  ⟨≈⟩ ≈-sym (·-assoc (U · P) Q (U †))
  ⟨≈⟩ ·-congˡ (U †) (·-assoc U P Q))

-- For a unitary U, U P U† = Q exactly when U P = Q U.

conj⇒intertwine : (U P Q : Op n) → Unitary U → U · P · U † ≈ Q → U · P ≈ Q · U
conj⇒intertwine U P Q u e =
  ≈-sym (cancelʳ′ U (U · P) u) ⟨≈⟩ ·-congˡ U e

intertwine⇒conj : (U P Q : Op n) → Unitary U → U · P ≈ Q · U → U · P · U † ≈ Q
intertwine⇒conj U P Q u e = ·-congˡ (U †) e ⟨≈⟩ cancelʳ U Q u

conj⇔intertwine : (U P Q : Op n) → Unitary U → (U · P · U † ≈ Q) ⇔ (U · P ≈ Q · U)
conj⇔intertwine U P Q u =
  mk⇔ (conj⇒intertwine U P Q u) (intertwine⇒conj U P Q u)


------------------------------------------------------------------------
-- Basic properties

𝒞-resp : ∀ k {U V : Op n} → U ≈ V → 𝒞 k U → 𝒞 k V
𝒞-resp zero          e ()
𝒞-resp (suc zero)    e (p , h) = p , ≈-sym e ⟨≈⟩ h
𝒞-resp (suc (suc k)) e (u , h) =
  Unitary-cong e u , λ p → 𝒞-resp (suc k) (conj-cong e (pauli p)) (h p)

𝒞-unitary : ∀ k {U : Op n} → 𝒞 (suc k) U → Unitary U
𝒞-unitary zero    (p , h) = Unitary-cong (≈-sym h) (pauli-unitary p)
𝒞-unitary (suc k) (u , _) = u

-- A sign times a Pauli is a Pauli.

sign-pauli : (b : Bool) (q : PauliData n) →
             (½ * [ b ]ᶻ) ◃ pauli q ≈ pauli (pd (ph q + (+ 2) * [ b ]ᶻ) (xs q) (zs q))
sign-pauli b q =
  ◃-exp (pauli q) (sym (¼·2 [ b ]ᶻ)) ⟨≈⟩ ◃-pauli ((+ 2) * [ b ]ᶻ) q

-- Every Pauli is in every level.

𝒞-pauli : ∀ k (p : PauliData n) → 𝒞 (suc k) (pauli p)
𝒞-pauli zero    p = p , ≈-refl
𝒞-pauli (suc k) p = pauli-unitary p , λ q →
  𝒞-resp (suc k) (≈-sym (pauli-conj p q ⟨≈⟩ sign-pauli (ω p q) q))
         (𝒞-pauli k (pd (ph q + (+ 2) * [ ω p q ]ᶻ) (xs q) (zs q)))

𝒞-I : ∀ k → 𝒞 (suc k) (I {n})
𝒞-I k = 𝒞-resp (suc k) pauli-I (𝒞-pauli k 1ᴾ)

-- The levels increase.

𝒞-mono : ∀ k {U : Op n} → 𝒞 (suc k) U → 𝒞 (suc (suc k)) U
𝒞-mono zero    (p , h) = Unitary-cong (≈-sym h) (pauli-unitary p) , λ q →
  𝒞-resp 1 (≈-sym (conj-cong h (pauli q))) (proj₂ (𝒞-pauli 1 p) q)
𝒞-mono (suc k) (u , h) = u , λ p → 𝒞-mono k (h p)


------------------------------------------------------------------------
-- Phases

-- From the second level on, any global phase.

𝒞-◃ : ∀ k (e : ℤ) {U : Op n} → 𝒞 (suc (suc k)) U → 𝒞 (suc (suc k)) (e ◃ U)
𝒞-◃ k e {U} (u , h) = Unitary-◃ e U u , λ p →
  𝒞-resp (suc k) (≈-sym (◃-conj e U (pauli p))) (h p)

-- At every level, a power of i, so a sign.

𝒞-i : ∀ k (t : ℤ) {U : Op n} → 𝒞 (suc k) U → 𝒞 (suc k) ((¼ * t) ◃ U)
𝒞-i zero    t (p , h) = pd (ph p + t) (xs p) (zs p) ,
                        ◃-cong (¼ * t) h ⟨≈⟩ ◃-pauli t p
𝒞-i (suc k) t {U}     = 𝒞-◃ k (¼ * t) {U}

𝒞-sign : ∀ k (b : Bool) {U : Op n} → 𝒞 (suc k) U → 𝒞 (suc k) ((½ * [ b ]ᶻ) ◃ U)
𝒞-sign k b {U} c =
  𝒞-resp (suc k) (◃-exp U (¼·2 [ b ]ᶻ)) (𝒞-i k ((+ 2) * [ b ]ᶻ) c)


------------------------------------------------------------------------
-- Products

-- A Pauli on the right: conjugating by U Q is conjugating by Q, which
-- gives back the Pauli up to a sign, then by U.

𝒞-·pauli : ∀ k {U : Op n} (q : PauliData n) → 𝒞 (suc k) U →
           𝒞 (suc k) (U · pauli q)
𝒞-·pauli zero    q (p , h) = p ∙ᴾ q , ·-congˡ (pauli q) h ⟨≈⟩ pauli-· p q
𝒞-·pauli (suc k) {U} q (u , h) =
  Unitary-· U (pauli q) u (pauli-unitary q) , λ p →
    𝒞-resp (suc k) (≈-sym (step p)) (𝒞-sign k (ω q p) (h p))
  where
  step : ∀ p → U · pauli q · pauli p · (U · pauli q) † ≈
               (½ * [ ω q p ]ᶻ) ◃ (U · pauli p · U †)
  step p = conj-· U (pauli q) (pauli p)
           ⟨≈⟩ conj-congᴾ U (pauli-conj q p)
           ⟨≈⟩ conj-◃ (½ * [ ω q p ]ᶻ) U (pauli p)

-- An element of 𝒞 2 on the right, from the second level on.

𝒞-·₂ : ∀ k {U V : Op n} → 𝒞 (suc (suc k)) U → 𝒞 2 V →
       𝒞 (suc (suc k)) (U · V)
𝒞-·₂ k {U} {V} (uU , hU) (uV , hV) = Unitary-· U V uU uV , λ p →
  let (p′ , e) = hV p in
  𝒞-resp (suc k) (≈-sym (conj-· U V (pauli p) ⟨≈⟩ conj-congᴾ U e)) (hU p′)

-- The Clifford group is closed under products.

𝒞₂-· : {U V : Op n} → 𝒞 2 U → 𝒞 2 V → 𝒞 2 (U · V)
𝒞₂-· {U = U} {V} = 𝒞-·₂ 0 {U} {V}


------------------------------------------------------------------------
-- Every Pauli is a product of generators

-- A property of Pauli data that respects ≈, holds at the identity, is
-- closed under products and powers of i, and holds at every X_j and
-- every Z_j, holds everywhere: P(a, x, z) = i^a X^x Z^z, and X^x is
-- the product of the X_j with x_j = 1, built up wire by wire.

private
  T→≡ : ∀ {b} → T b → b ≡ true
  T→≡ {true} _ = refl

  ¬T→≡ : ∀ {b} → ¬ T b → b ≡ false
  ¬T→≡ {true}  ¬t = ⊥-elim (¬t _)
  ¬T→≡ {false} _  = refl

  ∧-false : ∀ a → (a ∧ false) ≡ false
  ∧-false true  = refl
  ∧-false false = refl

  ∧-true : ∀ a → (a ∧ true) ≡ a
  ∧-true true  = refl
  ∧-true false = refl

  ∧-xor : ∀ a b c → (a ∧ b) xor (a ∧ c) ≡ (a ∧ (b xor c))
  ∧-xor true  b c = refl
  ∧-xor false b c = refl

  -- a < m + 1 is a < m or a = m, never both.

  <ᵇ-suc : ∀ a m → (a <ᵇ suc m) ≡ ((a <ᵇ m) xor (a ≡ᵇ m))
  <ᵇ-suc zero    zero    = refl
  <ᵇ-suc zero    (suc m) = refl
  <ᵇ-suc (suc a) zero    = refl
  <ᵇ-suc (suc a) (suc m) = <ᵇ-suc a m

module Decompose
  {n : ℕ} (G : PauliData n → Set)
  (G-≈ : ∀ {p q} → pauli p ≈ pauli q → G p → G q)
  (G-1 : G 1ᴾ)
  (G-∙ : ∀ {p q} → G p → G q → G (p ∙ᴾ q))
  (G-i : ∀ (t : ℤ) {p} → G p → G (pd (ph p + t) (xs p) (zs p)))
  (G-X : ∀ j → G (X^ j))
  (G-Z : ∀ j → G (Z^ j))
  where

  -- x on the wires below m.

  cut : ℕ → Assign n → Assign n
  cut m x j = x j ∧ (toℕ j <ᵇ m)

  -- x on wire m.

  bit : ℕ → Assign n → Assign n
  bit m x j = x j ∧ (toℕ j ≡ᵇ m)

  private
    cut-0 : (x : Assign n) → ∀ j → 0ᵛ j ≡ cut 0 x j
    cut-0 x j = sym (∧-false (x j))

    cut-n : (x : Assign n) → ∀ j → cut n x j ≡ x j
    cut-n x j = trans (cong (x j ∧_) (T→≡ (ℕ.<⇒<ᵇ (Fin.toℕ<n j))))
                      (∧-true (x j))

    cut-suc : (m : ℕ) (x : Assign n) →
              ∀ j → (cut m x ⊕ᵛ bit m x) j ≡ cut (suc m) x j
    cut-suc m x j = trans (∧-xor (x j) (toℕ j <ᵇ m) (toℕ j ≡ᵇ m))
                          (cong (x j ∧_) (sym (<ᵇ-suc (toℕ j) m)))

    -- Wire m, when there is one, is the only one numbered m.

    at-m : {m : ℕ} (m<n : m < n) (j : Fin n) →
           (toℕ j ≡ᵇ m) ≡ eᵛ (fromℕ< m<n) j
    at-m {m} m<n j with j Fin.≟ fromℕ< m<n
    ... | yes refl = T→≡ (ℕ.≡⇒≡ᵇ (toℕ (fromℕ< m<n)) m (Fin.toℕ-fromℕ< m<n))
    ... | no  j≢   = ¬T→≡ (λ t → j≢ (Fin.toℕ-injective
            (trans (ℕ.≡ᵇ⇒≡ (toℕ j) m t) (sym (Fin.toℕ-fromℕ< m<n)))))

    past-n : {m : ℕ} → ¬ (m < n) → (j : Fin n) → (toℕ j ≡ᵇ m) ≡ false
    past-n {m} m≮n j = ¬T→≡ (λ t →
      m≮n (subst< (ℕ.≡ᵇ⇒≡ (toℕ j) m t) (Fin.toℕ<n j)))
      where
      subst< : ∀ {a b} → a ≡ b → a < n → b < n
      subst< refl lt = lt

    -- x_j ∧ [j = j₀] is x_(j₀) ∧ [j = j₀].

    pick : (x : Assign n) (j₀ j : Fin n) →
           (x j ∧ eᵛ j₀ j) ≡ (x j₀ ∧ eᵛ j₀ j)
    pick x j₀ j with j Fin.≟ j₀
    ... | yes refl = refl
    ... | no  _    = trans (∧-false (x j)) (sym (∧-false (x j₀)))

  -- A Pauli built from a bit vector, additively.

  module Additive
    (mk : Assign n → PauliData n)
    (mk-≗ : ∀ {x y} → (∀ j → x j ≡ y j) → pauli (mk x) ≈ pauli (mk y))
    (mk-0 : pauli (mk 0ᵛ) ≈ pauli 1ᴾ)
    (mk-∙ : ∀ x y → pauli (mk x ∙ᴾ mk y) ≈ pauli (mk (x ⊕ᵛ y)))
    (mk-e : ∀ j → G (mk (eᵛ j)))
    where

    private
      G-0 : ∀ {x} → (∀ j → 0ᵛ j ≡ x j) → G (mk x)
      G-0 z = G-≈ (≈-sym mk-0 ⟨≈⟩ mk-≗ z) G-1

      G-bit-at : {m : ℕ} (m<n : m < n) (x : Assign n) (b : Bool) →
                 x (fromℕ< m<n) ≡ b → G (mk (bit m x))
      G-bit-at m<n x true  xb = G-≈ (mk-≗ λ j →
        sym (trans (cong (x j ∧_) (at-m m<n j))
              (trans (pick x (fromℕ< m<n) j)
                (cong (_∧ eᵛ (fromℕ< m<n) j) xb))))
        (mk-e (fromℕ< m<n))
      G-bit-at m<n x false xb = G-0 λ j →
        sym (trans (cong (x j ∧_) (at-m m<n j))
              (trans (pick x (fromℕ< m<n) j)
                (cong (_∧ eᵛ (fromℕ< m<n) j) xb)))

      G-bit : (m : ℕ) (x : Assign n) → G (mk (bit m x))
      G-bit m x with m ℕ.<? n
      ... | yes m<n = G-bit-at m<n x (x (fromℕ< m<n)) refl
      ... | no  m≮n = G-0 λ j →
              sym (trans (cong (x j ∧_) (past-n m≮n j)) (∧-false (x j)))

      G-cut : (x : Assign n) (m : ℕ) → G (mk (cut m x))
      G-cut x zero    = G-0 (cut-0 x)
      G-cut x (suc m) = G-≈ (mk-∙ (cut m x) (bit m x) ⟨≈⟩ mk-≗ (cut-suc m x))
                            (G-∙ (G-cut x m) (G-bit m x))

    every : ∀ x → G (mk x)
    every x = G-≈ (mk-≗ (cut-n x)) (G-cut x n)

  -- The X part and the Z part.

  private
    dot-0-0 : ∀ (x : Assign n) → ¼ * (0ℤ + 0ℤ + (+ 2) * [ dot 0ᵛ x ]ᶻ) ≡ᴺ ¼ * 0ℤ
    dot-0-0 x = ≡ᴺ-≡ (cong (λ b → ¼ * (0ℤ + 0ℤ + (+ 2) * [ b ]ᶻ))
                           (dot-0ˡ 0ᵛ x (λ _ → refl)))

    0-dot-0 : ∀ (z : Assign n) → ¼ * (0ℤ + 0ℤ + (+ 2) * [ dot z 0ᵛ ]ᶻ) ≡ᴺ ¼ * 0ℤ
    0-dot-0 z = ≡ᴺ-≡ (cong (λ b → ¼ * (0ℤ + 0ℤ + (+ 2) * [ b ]ᶻ))
                           (dot-0ʳ z 0ᵛ (λ _ → refl)))

  open Additive (λ x → pd 0ℤ x 0ᵛ)
    (λ {x} {y} xy → pauli-≈ (pd 0ℤ x 0ᵛ) (pd 0ℤ y 0ᵛ) ≡ᴺ-refl xy
                            (λ _ → refl))
    ≈-refl
    (λ x y → pauli-≈ (pd 0ℤ x 0ᵛ ∙ᴾ pd 0ℤ y 0ᵛ) (pd 0ℤ (x ⊕ᵛ y) 0ᵛ)
                     (dot-0-0 y) (λ _ → refl) (λ _ → refl))
    G-X
    renaming (every to every-X)

  open Additive (λ z → pd 0ℤ 0ᵛ z)
    (λ {z} {z′} zz → pauli-≈ (pd 0ℤ 0ᵛ z) (pd 0ℤ 0ᵛ z′) ≡ᴺ-refl
                             (λ _ → refl) zz)
    ≈-refl
    (λ z z′ → pauli-≈ (pd 0ℤ 0ᵛ z ∙ᴾ pd 0ℤ 0ᵛ z′) (pd 0ℤ 0ᵛ (z ⊕ᵛ z′))
                      (0-dot-0 z) (λ _ → refl) (λ _ → refl))
    G-Z
    renaming (every to every-Z)

  everywhere : ∀ p → G p
  everywhere p = G-≈
    (pauli-≈ (pd (ph r + ph p) (xs r) (zs r)) p
             (≡ᴺ-≡ (cong (¼ *_) (shape (dot {n} 0ᵛ 0ᵛ)
                                        (dot-0ˡ {n} 0ᵛ 0ᵛ (λ _ → refl)))))
             (λ j → xor-false (xs p j)) (λ _ → refl))
    (G-i (ph p) (G-∙ (every-X (xs p)) (every-Z (zs p))))
    where
    r : PauliData n
    r = pd 0ℤ (xs p) 0ᵛ ∙ᴾ pd 0ℤ 0ᵛ (zs p)
    shape : ∀ b → b ≡ false → 0ℤ + 0ℤ + (+ 2) * [ b ]ᶻ + ph p ≡ ph p
    shape .false refl = +-identityˡ (ph p)


------------------------------------------------------------------------
-- The generator form at the first two levels

-- U ∈ 𝒞 2 iff U is unitary and each U X_j U† and U Z_j U† is a Pauli.

private
  conj-1 : (U : Op n) → Unitary U → U · pauli 1ᴾ · U † ≈ I
  conj-1 U u = conj-congᴾ U pauli-I ⟨≈⟩ ·-congˡ (U †) (·-identityʳ U) ⟨≈⟩ proj₂ u

  -- U i^t P U† = i^t U P U†.

  conj-i : (U : Op n) (t : ℤ) (p : PauliData n) →
           U · pauli (pd (ph p + t) (xs p) (zs p)) · U † ≈
           (¼ * t) ◃ (U · pauli p · U †)
  conj-i U t p = conj-congᴾ U (≈-sym (◃-pauli t p)) ⟨≈⟩ conj-◃ (¼ * t) U (pauli p)

𝒞₂-gen : (U : Op n) → Unitary U →
         (∀ j → IsPauli (U · pauli (X^ j) · U †)) →
         (∀ j → IsPauli (U · pauli (Z^ j) · U †)) → 𝒞 2 U
𝒞₂-gen U u hX hZ = u , Decompose.everywhere G
  (λ e g → 𝒞-resp 1 (conj-congᴾ U e) g)
  (1ᴾ , conj-1 U u ⟨≈⟩ ≈-sym pauli-I)
  (λ {p} {q} gp gq →
     proj₁ gp ∙ᴾ proj₁ gq ,
     conj-congᴾ U (≈-sym (pauli-· p q)) ⟨≈⟩ conj-split U (pauli p) (pauli q) u
     ⟨≈⟩ ·-cong (proj₂ gp) (proj₂ gq) ⟨≈⟩ pauli-· (proj₁ gp) (proj₁ gq))
  (λ t {p} g → 𝒞-resp 1 (≈-sym (conj-i U t p))
                         (𝒞-i 0 t {U · pauli p · U †} g))
  hX hZ
  where
  G : PauliData _ → Set
  G p = IsPauli (U · pauli p · U †)

𝒞₂⇔gen : (U : Op n) →
         𝒞 2 U ⇔ (Unitary U × (∀ j → IsPauli (U · pauli (X^ j) · U †))
                            × (∀ j → IsPauli (U · pauli (Z^ j) · U †)))
𝒞₂⇔gen U = mk⇔ (λ (u , h) → u , (λ j → h (X^ j)) , (λ j → h (Z^ j)))
               (λ (u , hX , hZ) → 𝒞₂-gen U u hX hZ)

-- U ∈ 𝒞 3 iff U is unitary and each U X_j U† and U Z_j U† is in 𝒞 2:
-- the conjugate of a product of generators is the product of their
-- conjugates, and 𝒞 2 is closed under products.

𝒞₃-gen : (U : Op n) → Unitary U →
         (∀ j → 𝒞 2 (U · pauli (X^ j) · U †)) →
         (∀ j → 𝒞 2 (U · pauli (Z^ j) · U †)) → 𝒞 3 U
𝒞₃-gen U u hX hZ = u , Decompose.everywhere G
  (λ e g → 𝒞-resp 2 (conj-congᴾ U e) g)
  (𝒞-resp 2 (≈-sym (conj-1 U u)) (𝒞-I 1))
  (λ {p} {q} gp gq →
     𝒞-resp 2 (≈-sym (conj-congᴾ U (≈-sym (pauli-· p q))
                      ⟨≈⟩ conj-split U (pauli p) (pauli q) u))
           (𝒞₂-· {U = U · pauli p · U †} {V = U · pauli q · U †} gp gq))
  (λ t {p} g → 𝒞-resp 2 (≈-sym (conj-i U t p))
                         (𝒞-i 1 t {U · pauli p · U †} g))
  hX hZ
  where
  G : PauliData _ → Set
  G p = 𝒞 2 (U · pauli p · U †)

𝒞₃⇔gen : (U : Op n) →
         𝒞 3 U ⇔ (Unitary U × (∀ j → 𝒞 2 (U · pauli (X^ j) · U †))
                            × (∀ j → 𝒞 2 (U · pauli (Z^ j) · U †)))
𝒞₃⇔gen U = mk⇔ (λ (u , h) → u , (λ j → h (X^ j)) , (λ j → h (Z^ j)))
               (λ (u , hX , hZ) → 𝒞₃-gen U u hX hZ)

-- The form gates are checked in: U intertwines each generator with
-- some Pauli.

𝒞₂-by-intertwining : (U : Op n) → Unitary U →
  (∀ j → Σ[ q ∈ PauliData n ] U · pauli (X^ j) ≈ pauli q · U) →
  (∀ j → Σ[ q ∈ PauliData n ] U · pauli (Z^ j) ≈ pauli q · U) → 𝒞 2 U
𝒞₂-by-intertwining U u hX hZ = 𝒞₂-gen U u
  (λ j → let (q , e) = hX j in q , intertwine⇒conj U (pauli (X^ j)) (pauli q) u e)
  (λ j → let (q , e) = hZ j in q , intertwine⇒conj U (pauli (Z^ j)) (pauli q) u e)
