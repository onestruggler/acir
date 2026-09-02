{-# OPTIONS --cubical-compatible --safe #-}

------------------------------------------------------------------------
-- Presentations of groups
--
-- The Pauli calculus, shared between the qupit Clifford presentations.
--
-- Paper-V0 and Paper-V1 present the same group over the same alphabet,
-- and differ only in how they spell the multiplier.  Everything below
-- depends on four facts they share — order-S, order-H (read as
-- H ^ 4 ≈ ε), (S • H) ^ 3 ≈ ε and comm-HHSHHS — so it is stated once
-- here, over an abstract relation Γ, and instantiated by each
-- development.  Only three of the four are axioms on both sides:
-- (S • H) ^ 3 ≈ ε is Paper-V0's order-SH but a theorem in Paper-V1
-- (Lemmas.OneWire.lemma-order-SH), which is why it is taken as the
-- hypothesis order-SH' rather than named for an axiom.
--
-- Z, X and R are *defined* here rather than taken as parameters: both
-- developments define them by the same words over Symplectic's gates, so
-- the definitions below are definitionally equal to either one's.
--
-- What is NOT here is X • Z ≈ Z • X.  That is the one fact whose proof
-- differs between the two — Paper-V1 reads the Pauli prefix straight off
-- its order-H, while Paper-V0 has to compare (R • H) ^ 3 with (S • H) ^ 3
-- — so it is a hypothesis of the companion module, not of this one.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; setoid ; module ≡-Reasoning)
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq

open import Data.Product using (_,_ ; proj₁ ; proj₂ ; ∃)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _%_ ; _/_)
open import Data.Nat.DivMod
import Data.Nat as Nat
import Data.Nat.Properties as NP
open import Data.Fin hiding (_+_ ; _-_)
open import Data.Fin.Properties using (toℕ-inject₁ ; toℕ-fromℕ< ; toℕ-injective)

open import Word.Base as WB hiding (wfoldl ; _^'_)
open import Word.Properties
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.GroupLike
open import Notations

open import Data.Nat.Primality
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.ProjectiveClifford.Qupit.Shared.PauliBase
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open Primitive-Root-Modp' g* g-gen

-- The generator layer, taken from Symplectic exactly as both
-- developments take it.
open import Examples.Groups.Symplectic.Simplified.Syntactics
  p-2 p-prime g* g-gen as NSim
open NSim.Symplectic using (Gen ; S ; H ; S⁻¹ ; SympGate)

------------------------------------------------------------------------
-- The derived Pauli words
--
-- Written out here so that the calculus does not have to be parameterised
-- by them; both Paper-V0 and Paper-V1 define them by these same words.

module Words where

  1/2 : ℤ ₚ
  1/2 = ((₂ , λ ()) ⁻¹) .proj₁

  Z : ∀ {n} -> Word (Gen (₁₊ n))
  Z = H • H • S • H • H • S⁻¹

  X : ∀ {n} -> Word (Gen (₁₊ n))
  X = H • S • H • H • S⁻¹ • H

  Z⁻¹ : ∀ {n} -> Word (Gen (₁₊ n))
  Z⁻¹ = Z ^ p-1

  X⁻¹ : ∀ {n} -> Word (Gen (₁₊ n))
  X⁻¹ = X ^ p-1

  Z^ : ℤ ₚ ->  ∀ {n} -> Word (Gen (₁₊ n))
  Z^ k = Z ^ toℕ k

  X^ : ℤ ₚ ->  ∀ {n} -> Word (Gen (₁₊ n))
  X^ k = X ^ toℕ k

  S^' : ℤ ₚ ->  ∀ {n} -> Word (Gen (₁₊ n))
  S^' k = S ^ toℕ k

  R : ∀ {n} -> Word (Gen (₁₊ n))
  R = S • Z^ 1/2

  R^ : ℤ ₚ ->  ∀ {n} -> Word (Gen (₁₊ n))
  R^ k = R ^ toℕ k

open Words public

------------------------------------------------------------------------
-- ℤₚ arithmetic
--
-- None of this mentions the relation, so it is stated once outside the
-- parameterised modules below.  It is the exponent bookkeeping the
-- bridge needs: halves add to one, negation distributes, and (-₁)·k
-- is -k.

open import ForStdlib.Data.Fin.Mod.Prime.Properties p-2 p-prime using (toℕ-+)

-- The modulus of a bare numeral is not inferable on its own, so the one
-- that appears as an operand below is pinned here (1ₚ is ForStdlib's).
2ₚ : ℤ ₚ
2ₚ = ₂

private
  2<p : 2 Nat.< p
  2<p = s≤s (s≤s (s≤s z≤n))

  1+1≡2 : 1ₚ + 1ₚ ≡ 2ₚ
  1+1≡2 = toℕ-injective (Eq.trans (toℕ-+ 1ₚ 1ₚ) (m<n⇒m%n≡m 2<p))

aux-half*2 : 1/2 * 2ₚ ≡ 1ₚ
aux-half*2 = lemma-⁻¹ˡ 2ₚ {{nztoℕ {y = 2ₚ} {neq0 = λ ()}}}

aux-half+half : 1/2 + 1/2 ≡ 1ₚ
aux-half+half =
  Eq.trans (Eq.sym (Eq.cong₂ (λ s t → s + t) (*-identityʳ 1/2) (*-identityʳ 1/2)))
    (Eq.trans (Eq.sym (*-distribˡ-+ 1/2 1ₚ 1ₚ))
      (Eq.trans (Eq.cong (1/2 *_) 1+1≡2) aux-half*2))

aux-half-half : ∀ (x : ℤ ₚ) → 1/2 * x + 1/2 * x ≡ x
aux-half-half x =
  Eq.trans (Eq.sym (*-distribʳ-+ x 1/2 1/2))
    (Eq.trans (Eq.cong (_* x) aux-half+half) (*-identityˡ x))

neg-involutive : ∀ (x : ℤ ₚ) → - (- x) ≡ x
neg-involutive x =
  Eq.trans (Eq.sym (+-identityʳ (- (- x))))
    (Eq.trans (Eq.cong (- (- x) +_) (Eq.sym (+-inverseˡ x)))
      (Eq.trans (Eq.sym (+-assoc (- (- x)) (- x) x))
        (Eq.trans (Eq.cong (_+ x) (+-inverseˡ (- x))) (+-identityˡ x))))

private
  zero-k : ∀ (k : ℤ ₚ) → k + (- ₁) * k ≡ ₀
  zero-k k =
    Eq.trans (Eq.cong (_+ (- ₁) * k) (Eq.sym (*-identityˡ k)))
      (Eq.trans (Eq.sym (*-distribʳ-+ k ₁ (- ₁)))
        (Eq.trans (Eq.cong (_* k) (+-inverseʳ ₁)) (*-zeroˡ k)))

neg-mul : ∀ (k : ℤ ₚ) → (- ₁) * k ≡ - k
neg-mul k =
  Eq.sym (Eq.trans (Eq.sym (+-identityʳ (- k)))
    (Eq.trans (Eq.cong (- k +_) (Eq.sym (zero-k k)))
      (Eq.trans (Eq.sym (+-assoc (- k) k ((- ₁) * k)))
        (Eq.trans (Eq.cong (_+ (- ₁) * k) (+-inverseˡ k))
          (+-identityˡ ((- ₁) * k))))))

neg-+ : ∀ (u v : ℤ ₚ) → - (u + v) ≡ - u + - v
neg-+ u v =
  Eq.trans (Eq.sym (neg-mul (u + v)))
    (Eq.trans (*-distribˡ-+ (- ₁) u v)
      (Eq.cong₂ (λ s t → s + t) (neg-mul u) (neg-mul v)))

neg-* : ∀ (a b : ℤ ₚ) → (- a) * b ≡ - (a * b)
neg-* a b =
  Eq.trans (Eq.cong (_* b) (Eq.sym (neg-mul a)))
    (Eq.trans (*-assoc (- ₁) a b) (neg-mul (a * b)))

-- …and likewise the zero.
0ₚ' : ℤ ₚ
0ₚ' = ₀

neg0 : - 0ₚ' ≡ 0ₚ'
neg0 = Eq.trans (Eq.sym (+-identityʳ (- 0ₚ'))) (+-inverseˡ 0ₚ')

------------------------------------------------------------------------
-- The calculus itself
--
-- Parameterised by the relation and by the four axioms both
-- presentations share.  order-H is taken in the form H ^ 4 ≈ ε, which is
-- what each development derives from its own order-H — that is exactly
-- the point at which the two spellings of the multiplier stop mattering.

module Calculus
  (n : ℕ)
  (Γ : WRel (Gen (₁₊ n)))
  (grouplike : Grouplike Γ)
  (order-S' : let open PB Γ in S ^ p ≈ ε)
  (order-H4 : let open PB Γ in H ^ 4 ≈ ε)
  (order-SH' : let open PB Γ in (S • H) ^ 3 ≈ ε)
  where

  open PB Γ
  open PP Γ
  open SR word-setoid
  open Group-Lemmas Γ grouplike using (•-cancelʳ ; •-cancelˡ)

  S⁻¹S : S⁻¹ • S ≈ ε
  S⁻¹S = begin
    S ^ p-1 • S        ≈⟨ sym (^-+ S p-1 1) ⟩
    S ^ (p-1 Nat.+ 1)  ≡⟨ Eq.cong (S ^_) (NP.+-comm p-1 1) ⟩
    S ^ p              ≈⟨ order-S' ⟩
    ε ∎

  H≈H⁵ : H ≈ H ^ 5
  H≈H⁵ = begin
    H          ≈⟨ sym left-unit ⟩
    ε • H      ≈⟨ cleft sym order-H4 ⟩
    H ^ 4 • H  ≈⟨ sym (^-+ H 4 1) ⟩
    H ^ 5 ∎

  -- (S • H) ^ 3 ≈ ε, cancelled on the right by S • H.
  lemma-SHSH : S • H • S • H ≈ H ^ 3 • S⁻¹
  lemma-SHSH = •-cancelʳ {h = S • H} (begin
    (S • H • S • H) • (S • H)  ≈⟨ by-assoc auto ⟩
    (S • H) ^ 3                ≈⟨ order-SH' ⟩
    ε                          ≈⟨ sym aux ⟩
    (H ^ 3 • S⁻¹) • (S • H) ∎)
    where
    aux : (H ^ 3 • S⁻¹) • (S • H) ≈ ε
    aux = begin
      (H ^ 3 • S⁻¹) • (S • H)  ≈⟨ assoc ⟩
      H ^ 3 • (S⁻¹ • (S • H))  ≈⟨ cright sym assoc ⟩
      H ^ 3 • ((S⁻¹ • S) • H)  ≈⟨ cright cleft S⁻¹S ⟩
      H ^ 3 • (ε • H)          ≈⟨ cright left-unit ⟩
      H ^ 3 • H                ≈⟨ sym (^-+ H 3 1) ⟩
      H ^ 4                    ≈⟨ order-H4 ⟩
      ε ∎

  lemma-HSH : H • S • H ≈ S⁻¹ • H ^ 3 • S⁻¹
  lemma-HSH = •-cancelˡ {g = S} (begin
    S • (H • S • H)            ≈⟨ lemma-SHSH ⟩
    H ^ 3 • S⁻¹                ≈⟨ sym left-unit ⟩
    ε • (H ^ 3 • S⁻¹)          ≈⟨ cleft sym order-S' ⟩
    (S • S⁻¹) • (H ^ 3 • S⁻¹)  ≈⟨ assoc ⟩
    S • (S⁻¹ • H ^ 3 • S⁻¹) ∎)

------------------------------------------------------------------------
-- The bridge between the R- and S-spellings of the multiplier
--
-- Parameterised by the facts both Paper-V1 and Simplified-V1 already
-- have, X • Z ≈ Z • X among them.  Instantiating this at Simplified-V1
-- is what gives Paper-V0 the bridge: Paper-V0.Iso already transports
-- Simplified-V1 theorems into Paper-V0's theory.

module BridgeCalc
  (n : ℕ)
  (Γ : WRel (Gen (₁₊ n)))
  (order-X : let open PB Γ in X ^ p ≈ ε)
  (order-Z : let open PB Γ in Z ^ p ≈ ε)
  (comm-Z-S : let open PB Γ in Z • S ≈ S • Z)
  (comm-X-Z : let open PB Γ in X • Z ≈ Z • X)
  (conj-H-X^k : let open PB Γ in ∀ k → H • X ^ k ≈ Z ^ k • H)
  (conj-X^k-H : let open PB Γ in ∀ k → X ^ k • H ≈ H • Z⁻¹ ^ k)
  (lemma-XS : let open PB Γ in X • S ≈ S • X • Z⁻¹)
  (pow-mod : let open PB Γ in
             ∀ (w : Word (Gen (₁₊ n))) → w ^ p ≈ ε → ∀ m → w ^ m ≈ w ^ (m Nat.% p))
  (induction : let open PB Γ in
               ∀ {a b c} → a • b ≈ c • a → ∀ k → a • b ^ k ≈ c ^ k • a)
  (inductionˡ : let open PB Γ in
                ∀ {a b c} → a • b ≈ b • c → ∀ l → a ^ l • b ≈ b • c ^ l)
  where

  open PB Γ
  open PP Γ
  open SR word-setoid
  open Pattern-Assoc

  comm-X^k-Z^l : ∀ k l -> X ^ k • Z ^ l ≈ Z ^ l • X ^ k
  comm-X^k-Z^l k l = comm⇒pow-comm k l comm-X-Z

  ------------------------------------------------------------------------
  -- Pauli powers at ℤₚ exponents

  X^-+ : ∀ a b -> X^ a • X^ b ≈ X^ (a + b)
  X^-+ a b = begin
    X ^ toℕ a • X ^ toℕ b          ≈⟨ sym (^-+ X (toℕ a) (toℕ b)) ⟩
    X ^ (toℕ a Nat.+ toℕ b)        ≈⟨ pow-mod X order-X (toℕ a Nat.+ toℕ b) ⟩
    X ^ ((toℕ a Nat.+ toℕ b) % p)  ≈⟨ refl' (Eq.cong (X ^_) (Eq.sym (toℕ-+ a b))) ⟩
    X ^ toℕ (a + b) ∎

  Z^-+ : ∀ a b -> Z^ a • Z^ b ≈ Z^ (a + b)
  Z^-+ a b = begin
    Z ^ toℕ a • Z ^ toℕ b          ≈⟨ sym (^-+ Z (toℕ a) (toℕ b)) ⟩
    Z ^ (toℕ a Nat.+ toℕ b)        ≈⟨ pow-mod Z order-Z (toℕ a Nat.+ toℕ b) ⟩
    Z ^ ((toℕ a Nat.+ toℕ b) % p)  ≈⟨ refl' (Eq.cong (Z ^_) (Eq.sym (toℕ-+ a b))) ⟩
    Z ^ toℕ (a + b) ∎

  Z^-* : ∀ a b -> (Z^ a) ^ toℕ b ≈ Z^ (a * b)
  Z^-* a b = begin
    (Z ^ toℕ a) ^ toℕ b            ≈⟨ ^^ Z (toℕ a) (toℕ b) ⟩
    Z ^ (toℕ a Nat.* toℕ b)        ≈⟨ pow-mod Z order-Z _ ⟩
    Z ^ ((toℕ a Nat.* toℕ b) % p)  ≈⟨ refl' (Eq.cong (Z ^_) (lemma-toℕ-% a b)) ⟩
    Z ^ toℕ (a * b) ∎

  Z⁻¹^ : ∀ (k : ℤ ₚ) → Z⁻¹ ^ toℕ k ≈ Z^ (- k)
  Z⁻¹^ k = begin
    (Z ^ p-1) ^ toℕ k            ≈⟨ ^^ Z p-1 (toℕ k) ⟩
    Z ^ (p-1 Nat.* toℕ k)        ≈⟨ pow-mod Z order-Z (p-1 Nat.* toℕ k) ⟩
    Z ^ ((p-1 Nat.* toℕ k) % p)  ≈⟨ refl' (Eq.cong (Z ^_) step) ⟩
    Z ^ toℕ (- k) ∎
    where
    step : (p-1 Nat.* toℕ k) % p ≡ toℕ (- k)
    step = Eq.trans (Eq.cong (λ m → (m Nat.* toℕ k) % p) (Eq.sym lemma-toℕ-1ₚ))
             (Eq.trans (lemma-toℕ-% (- ₁) k) (Eq.cong toℕ (neg-mul k)))

  ------------------------------------------------------------------------
  -- Moving an X-power past an S-power

  conj-X-S : X • S ≈ (S • Z⁻¹) • X
  conj-X-S = begin
    X • S          ≈⟨ lemma-XS ⟩
    S • X • Z⁻¹    ≈⟨ cright (comm-X^k-Z^l 1 p-1) ⟩
    S • Z⁻¹ • X    ≈⟨ sym assoc ⟩
    (S • Z⁻¹) • X ∎

  conj-X-S^l : ∀ l -> X • S ^ l ≈ (S • Z⁻¹) ^ l • X
  conj-X-S^l l = induction conj-X-S l

  X-S^ : ∀ m -> X • S^' m ≈ S^' m • (X • Z^ (- m))
  X-S^ m = begin
    X • S ^ toℕ m
      ≈⟨ conj-X-S^l (toℕ m) ⟩
    (S • Z⁻¹) ^ toℕ m • X
      ≈⟨ cleft (^-• S Z⁻¹ (toℕ m) (comm⇒pow-comm 1 p-1 (sym comm-Z-S))) ⟩
    (S ^ toℕ m • Z⁻¹ ^ toℕ m) • X
      ≈⟨ cleft cright (Z⁻¹^ m) ⟩
    (S^' m • Z^ (- m)) • X
      ≈⟨ assoc ⟩
    S^' m • (Z^ (- m) • X)
      ≈⟨ cright sym (comm-X^k-Z^l 1 (toℕ (- m))) ⟩
    S^' m • (X • Z^ (- m)) ∎

  X^-S^ : ∀ k m -> X^ k • S^' m ≈ S^' m • (X^ k • Z^ (- (k * m)))
  X^-S^ k m = begin
    X ^ toℕ k • S^' m
      ≈⟨ inductionˡ (X-S^ m) (toℕ k) ⟩
    S^' m • (X • Z^ (- m)) ^ toℕ k
      ≈⟨ cright (^-• X (Z^ (- m)) (toℕ k) (comm-X^k-Z^l 1 (toℕ (- m)))) ⟩
    S^' m • (X ^ toℕ k • (Z^ (- m)) ^ toℕ k)
      ≈⟨ cright cright (Z^-* (- m) k) ⟩
    S^' m • (X^ k • Z^ ((- m) * k))
      ≈⟨ cright cright (refl' (Eq.cong (λ z → Z^ z) negswap)) ⟩
    S^' m • (X^ k • Z^ (- (k * m))) ∎
    where
    negswap : (- m) * k ≡ - (k * m)
    negswap = Eq.trans (neg-* m k) (Eq.cong (λ z → - z) (*-comm m k))

  ------------------------------------------------------------------------
  -- A Pauli crossing one block S^m • H

  P-Bm : ∀ m α β -> (X^ α • Z^ β) • (S^' m • H)
                    ≈ (S^' m • H) • (X^ (β + - (α * m)) • Z^ (- α))
  P-Bm m α β = begin
    (X^ α • Z^ β) • (S^' m • H)
      ≈⟨ assoc ⟩
    X^ α • (Z^ β • (S^' m • H))
      ≈⟨ cright sym assoc ⟩
    X^ α • ((Z^ β • S^' m) • H)
      ≈⟨ cright cleft (comm⇒pow-comm (toℕ β) (toℕ m) comm-Z-S) ⟩
    X^ α • ((S^' m • Z^ β) • H)
      ≈⟨ cright assoc ⟩
    X^ α • (S^' m • (Z^ β • H))
      ≈⟨ cright cright sym (conj-H-X^k (toℕ β)) ⟩
    X^ α • (S^' m • (H • X^ β))
      ≈⟨ cright sym assoc ⟩
    X^ α • ((S^' m • H) • X^ β)
      ≈⟨ sym assoc ⟩
    (X^ α • (S^' m • H)) • X^ β
      ≈⟨ cleft sym assoc ⟩
    ((X^ α • S^' m) • H) • X^ β
      ≈⟨ cleft cleft (X^-S^ α m) ⟩
    ((S^' m • (X^ α • Z^ (- (α * m)))) • H) • X^ β
      ≈⟨ cleft assoc ⟩
    (S^' m • ((X^ α • Z^ (- (α * m))) • H)) • X^ β
      ≈⟨ cleft cright assoc ⟩
    (S^' m • (X^ α • (Z^ (- (α * m)) • H))) • X^ β
      ≈⟨ cleft cright cright sym (conj-H-X^k (toℕ (- (α * m)))) ⟩
    (S^' m • (X^ α • (H • X^ (- (α * m))))) • X^ β
      ≈⟨ cleft cright sym assoc ⟩
    (S^' m • ((X^ α • H) • X^ (- (α * m)))) • X^ β
      ≈⟨ cleft cright cleft (conj-X^k-H (toℕ α)) ⟩
    (S^' m • ((H • Z⁻¹ ^ toℕ α) • X^ (- (α * m)))) • X^ β
      ≈⟨ cleft cright cleft cright (Z⁻¹^ α) ⟩
    (S^' m • ((H • Z^ (- α)) • X^ (- (α * m)))) • X^ β
      ≈⟨ cleft cright assoc ⟩
    (S^' m • (H • (Z^ (- α) • X^ (- (α * m))))) • X^ β
      ≈⟨ cleft cright cright sym (comm-X^k-Z^l (toℕ (- (α * m))) (toℕ (- α))) ⟩
    (S^' m • (H • (X^ (- (α * m)) • Z^ (- α)))) • X^ β
      ≈⟨ cleft sym assoc ⟩
    ((S^' m • H) • (X^ (- (α * m)) • Z^ (- α))) • X^ β
      ≈⟨ assoc ⟩
    (S^' m • H) • ((X^ (- (α * m)) • Z^ (- α)) • X^ β)
      ≈⟨ cright assoc ⟩
    (S^' m • H) • (X^ (- (α * m)) • (Z^ (- α) • X^ β))
      ≈⟨ cright cright sym (comm-X^k-Z^l (toℕ β) (toℕ (- α))) ⟩
    (S^' m • H) • (X^ (- (α * m)) • (X^ β • Z^ (- α)))
      ≈⟨ cright sym assoc ⟩
    (S^' m • H) • ((X^ (- (α * m)) • X^ β) • Z^ (- α))
      ≈⟨ cright cleft (X^-+ (- (α * m)) β) ⟩
    (S^' m • H) • (X^ (- (α * m) + β) • Z^ (- α))
      ≈⟨ cright cleft (refl' (Eq.cong (λ z → X^ z) (+-comm (- (α * m)) β))) ⟩
    (S^' m • H) • (X^ (β + - (α * m)) • Z^ (- α)) ∎

  Pu' : ∀ γ δ η -> (X^ γ • Z^ δ) • X^ η ≈ X^ (γ + η) • Z^ δ
  Pu' γ δ η = begin
    (X^ γ • Z^ δ) • X^ η   ≈⟨ assoc ⟩
    X^ γ • (Z^ δ • X^ η)   ≈⟨ cright sym (comm-X^k-Z^l (toℕ η) (toℕ δ)) ⟩
    X^ γ • (X^ η • Z^ δ)   ≈⟨ sym assoc ⟩
    (X^ γ • X^ η) • Z^ δ   ≈⟨ cleft (X^-+ γ η) ⟩
    X^ (γ + η) • Z^ δ ∎

  R-split : ∀ k -> R ^ k ≈ S ^ k • (Z^ 1/2) ^ k
  R-split k = ^-• S (Z^ 1/2) k (comm⇒pow-comm 1 (toℕ 1/2) (sym comm-Z-S))

  R^-H : ∀ c -> R^ c • H ≈ (S^' c • H) • X^ (1/2 * c)
  R^-H c = begin
    R ^ toℕ c • H
      ≈⟨ cleft (R-split (toℕ c)) ⟩
    (S ^ toℕ c • (Z^ 1/2) ^ toℕ c) • H
      ≈⟨ cleft cright (Z^-* 1/2 c) ⟩
    (S^' c • Z^ (1/2 * c)) • H
      ≈⟨ assoc ⟩
    S^' c • (Z^ (1/2 * c) • H)
      ≈⟨ cright sym (conj-H-X^k (toℕ (1/2 * c))) ⟩
    S^' c • (H • X^ (1/2 * c))
      ≈⟨ sym assoc ⟩
    (S^' c • H) • X^ (1/2 * c) ∎

  stepm : ∀ w m α β -> (w • (X^ α • Z^ β)) • ((S^' m • H) • X^ (1/2 * m))
          ≈ (w • (S^' m • H)) • (X^ ((β + - (α * m)) + (1/2 * m)) • Z^ (- α))
  stepm w m α β = begin
    (w • (X^ α • Z^ β)) • ((S^' m • H) • X^ (1/2 * m))
      ≈⟨ assoc ⟩
    w • ((X^ α • Z^ β) • ((S^' m • H) • X^ (1/2 * m)))
      ≈⟨ cright sym assoc ⟩
    w • (((X^ α • Z^ β) • (S^' m • H)) • X^ (1/2 * m))
      ≈⟨ cright cleft (P-Bm m α β) ⟩
    w • (((S^' m • H) • (X^ (β + - (α * m)) • Z^ (- α))) • X^ (1/2 * m))
      ≈⟨ cright assoc ⟩
    w • ((S^' m • H) • ((X^ (β + - (α * m)) • Z^ (- α)) • X^ (1/2 * m)))
      ≈⟨ cright cright (Pu' (β + - (α * m)) (- α) (1/2 * m)) ⟩
    w • ((S^' m • H) • (X^ ((β + - (α * m)) + (1/2 * m)) • Z^ (- α)))
      ≈⟨ sym assoc ⟩
    (w • (S^' m • H)) • (X^ ((β + - (α * m)) + (1/2 * m)) • Z^ (- α)) ∎

  ------------------------------------------------------------------------
  -- A Z-power crossing the whole multiplier
  --
  -- The three blocks of the multiplier's S-word, in the order the XM
  -- spelling has them — S^b, S^a, S^b — carry a Z-power across and leave
  -- it scaled by a.  Each application of P-Bm turns the Z into an X and
  -- back; what makes this a Z-rule rather than a general Pauli one is
  -- that the X-part cancels at the third block, and that is exactly where
  -- a · b ≡ ₁ is used.  With any other pair of exponents an X-power would
  -- survive.
  --
  -- This is the diagonal action of the multiplier on the Pauli group:
  -- conjugating by XM x sends Z to Z^x.  Simplified-V1.SemiM proves the
  -- same thing of its own spelling, and calls the factor β = g⁻¹ there
  -- because it states it for M g rather than for XM g.

  Z-blocks : ∀ a b → a * b ≡ 1ₚ → ∀ k →
             Z^ k • ((S^' b • H) • ((S^' a • H) • (S^' b • H)))
             ≈ ((S^' b • H) • ((S^' a • H) • (S^' b • H))) • Z^ (a * k)
  Z-blocks a b ab≡1 k = begin
    Z^ k • ((S^' b • H) • ((S^' a • H) • (S^' b • H)))
      ≈⟨ cleft (sym left-unit) ⟩
    (X^ ₀ • Z^ k) • ((S^' b • H) • ((S^' a • H) • (S^' b • H)))
      ≈⟨ sym assoc ⟩
    ((X^ ₀ • Z^ k) • (S^' b • H)) • ((S^' a • H) • (S^' b • H))
      ≈⟨ cleft (P-Bm b ₀ k) ⟩
    ((S^' b • H) • (X^ (k + - (₀ * b)) • Z^ (- ₀)))
      • ((S^' a • H) • (S^' b • H))
      ≈⟨ cleft cright (cong (refl' (Eq.cong (λ z → X^ z) e1))
                            (refl' (Eq.cong (λ z → Z^ z) neg0))) ⟩
    ((S^' b • H) • (X^ k • Z^ ₀)) • ((S^' a • H) • (S^' b • H))
      ≈⟨ assoc ⟩
    (S^' b • H) • ((X^ k • Z^ ₀) • ((S^' a • H) • (S^' b • H)))
      ≈⟨ cright sym assoc ⟩
    (S^' b • H) • (((X^ k • Z^ ₀) • (S^' a • H)) • (S^' b • H))
      ≈⟨ cright cleft (P-Bm a k ₀) ⟩
    (S^' b • H)
      • (((S^' a • H) • (X^ (₀ + - (k * a)) • Z^ (- k))) • (S^' b • H))
      ≈⟨ cright cleft cright cleft (refl' (Eq.cong (λ z → X^ z) e2)) ⟩
    (S^' b • H)
      • (((S^' a • H) • (X^ (- (k * a)) • Z^ (- k))) • (S^' b • H))
      ≈⟨ cright assoc ⟩
    (S^' b • H)
      • ((S^' a • H) • ((X^ (- (k * a)) • Z^ (- k)) • (S^' b • H)))
      ≈⟨ cright cright (P-Bm b (- (k * a)) (- k)) ⟩
    (S^' b • H)
      • ((S^' a • H) • ((S^' b • H)
        • (X^ ((- k) + - ((- (k * a)) * b)) • Z^ (- (- (k * a))))))
      ≈⟨ cright cright cright (cong (refl' (Eq.cong (λ z → X^ z) e3))
                                    (refl' (Eq.cong (λ z → Z^ z) e4))) ⟩
    (S^' b • H) • ((S^' a • H) • ((S^' b • H) • (X^ ₀ • Z^ (a * k))))
      ≈⟨ cright cright cright left-unit ⟩
    (S^' b • H) • ((S^' a • H) • ((S^' b • H) • Z^ (a * k)))
      ≈⟨ cright sym assoc ⟩
    (S^' b • H) • (((S^' a • H) • (S^' b • H)) • Z^ (a * k))
      ≈⟨ sym assoc ⟩
    ((S^' b • H) • ((S^' a • H) • (S^' b • H))) • Z^ (a * k) ∎
    where
    -- The first block leaves the exponent alone: it entered with no
    -- X-part, so P-Bm's correction -(₀ · b) is zero.
    e1 : k + - (₀ * b) ≡ k
    e1 = Eq.trans (Eq.cong (λ z → k + - z) (*-zeroˡ b))
           (Eq.trans (Eq.cong (k +_) neg0) (+-identityʳ k))

    e2 : ₀ + - (k * a) ≡ - (k * a)
    e2 = +-identityˡ (- (k * a))

    -- The third block's X-correction is -((-(k·a))·b) = k·a·b = k, which
    -- cancels the -k the second block left.  This is the a · b ≡ ₁ step.
    u≡-k : (- (k * a)) * b ≡ - k
    u≡-k = Eq.trans (neg-* (k * a) b)
             (Eq.cong (λ z → - z)
               (Eq.trans (*-assoc k a b)
                 (Eq.trans (Eq.cong (k *_) ab≡1) (*-identityʳ k))))

    e3 : (- k) + - ((- (k * a)) * b) ≡ ₀
    e3 = Eq.trans (Eq.cong (λ z → (- k) + - z) u≡-k)
           (Eq.trans (Eq.cong ((- k) +_) (neg-involutive k)) (+-inverseˡ k))

    e4 : - (- (k * a)) ≡ a * k
    e4 = Eq.trans (neg-involutive (k * a)) (*-comm k a)

  -- …and the same across the whole multiplier, prefix included.  W is the
  -- word Paper-V1 spells XM x by — SHS' x x⁻¹, blocks b, a, b — and a Z
  -- commutes with the Pauli prefix in front of the blocks outright: with
  -- its Z-part trivially, with its X-part by comm-X-Z.
  module MulZ (x : ℤ* ₚ) where

    private
      a : ℤ ₚ
      a = x .proj₁

      b : ℤ ₚ
      b = (x ⁻¹) .proj₁

      γ : ℤ ₚ
      γ = (b + - ₁) * 1/2

      δ : ℤ ₚ
      δ = (₁ + - a) * 1/2

      ab≡1 : a * b ≡ 1ₚ
      ab≡1 = lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = x .proj₂}}}

      Blocks : Word (Gen (₁₊ n))
      Blocks = S^' b • (H • (S^' a • (H • (S^' b • H))))

      through : ∀ k → Z^ k • Blocks ≈ Blocks • Z^ (a * k)
      through k = begin
        Z^ k • (S^' b • (H • (S^' a • (H • (S^' b • H)))))
          ≈⟨ cright (by-passoc (□ ^ 6) (□ ^ 2 • □ ^ 2 • □ ^ 2) auto) ⟩
        Z^ k • ((S^' b • H) • ((S^' a • H) • (S^' b • H)))
          ≈⟨ Z-blocks a b ab≡1 k ⟩
        ((S^' b • H) • ((S^' a • H) • (S^' b • H))) • Z^ (a * k)
          ≈⟨ cleft sym (by-passoc (□ ^ 6) (□ ^ 2 • □ ^ 2 • □ ^ 2) auto) ⟩
        (S^' b • (H • (S^' a • (H • (S^' b • H))))) • Z^ (a * k) ∎

    W : Word (Gen (₁₊ n))
    W = Z^ γ • (X^ δ • Blocks)

    Z-W : ∀ k → Z^ k • W ≈ W • Z^ (a * k)
    Z-W k = begin
      Z^ k • (Z^ γ • (X^ δ • Blocks))
        ≈⟨ sym assoc ⟩
      (Z^ k • Z^ γ) • (X^ δ • Blocks)
        ≈⟨ cleft (comm⇒pow-comm (toℕ k) (toℕ γ) refl) ⟩
      (Z^ γ • Z^ k) • (X^ δ • Blocks)
        ≈⟨ assoc ⟩
      Z^ γ • (Z^ k • (X^ δ • Blocks))
        ≈⟨ cright sym assoc ⟩
      Z^ γ • ((Z^ k • X^ δ) • Blocks)
        ≈⟨ cright cleft sym (comm-X^k-Z^l (toℕ δ) (toℕ k)) ⟩
      Z^ γ • ((X^ δ • Z^ k) • Blocks)
        ≈⟨ cright assoc ⟩
      Z^ γ • (X^ δ • (Z^ k • Blocks))
        ≈⟨ cright cright (through k) ⟩
      Z^ γ • (X^ δ • (Blocks • Z^ (a * k)))
        ≈⟨ cright sym assoc ⟩
      Z^ γ • ((X^ δ • Blocks) • Z^ (a * k))
        ≈⟨ sym assoc ⟩
      (Z^ γ • (X^ δ • Blocks)) • Z^ (a * k) ∎

  ------------------------------------------------------------------------
  -- The two spellings of semi-MR
  --
  -- Paper-V0 states the rule over R:
  --
  --     XM x • R^(a·a)  ≈  R • XM x,
  --
  -- and Paper-V1 over S, with the Pauli that the change of spelling
  -- leaves behind written out on the left:
  --
  --     XM x • (S^(a·a) • Z^((a·a - a)·½))  ≈  S • XM x.
  --
  -- They are the same rule.  R^(a·a) splits into S^(a·a) • Z^(½·a²), and
  -- the Z^½ that the R on the right contributes crosses the multiplier by
  -- MulZ, picking up the factor a.  Both sides then carry a trailing
  -- Z^(½·a), and cancelling it is the entire difference between the two
  -- statements — which is why the S-form's exponent is ½a² - ½a rather
  -- than the ½a² that R-splitting alone would give.

  module SemiMR (x : ℤ* ₚ) where

    private
      a : ℤ ₚ
      a = x .proj₁

      W : Word (Gen (₁₊ n))
      W = MulZ.W x

      e : ℤ ₚ
      e = (a * a + - a) * 1/2

      R^-split : R^ (a * a) ≈ S^' (a * a) • Z^ (1/2 * (a * a))
      R^-split = trans (R-split (toℕ (a * a))) (cright (Z^-* 1/2 (a * a)))

      -- ½a² is the axiom's exponent plus the ½a the R on the right leaves.
      split-e : e + 1/2 * a ≡ 1/2 * (a * a)
      split-e =
        Eq.trans (Eq.cong (_+ (1/2 * a)) distr)
          (Eq.trans (+-assoc (1/2 * (a * a)) (- (1/2 * a)) (1/2 * a))
            (Eq.trans (Eq.cong ((1/2 * (a * a)) +_) (+-inverseˡ (1/2 * a)))
              (+-identityʳ (1/2 * (a * a)))))
        where
        distr : e ≡ 1/2 * (a * a) + - (1/2 * a)
        distr = Eq.trans (*-distribʳ-+ 1/2 (a * a) (- a))
                  (Eq.cong₂ (λ s t → s + t) (*-comm (a * a) 1/2)
                    (Eq.trans (neg-* a 1/2)
                      (Eq.cong (λ z → - z) (*-comm a 1/2))))

      -- Both sides of the R-form, with the trailing Z^(½a) exposed.
      L : W • R^ (a * a) ≈ (W • (S^' (a * a) • Z^ e)) • Z^ (1/2 * a)
      L = begin
        W • R^ (a * a)
          ≈⟨ cright R^-split ⟩
        W • (S^' (a * a) • Z^ (1/2 * (a * a)))
          ≈⟨ cright cright (refl' (Eq.cong (λ z → Z^ z) (Eq.sym split-e))) ⟩
        W • (S^' (a * a) • Z^ (e + 1/2 * a))
          ≈⟨ cright cright sym (Z^-+ e (1/2 * a)) ⟩
        W • (S^' (a * a) • (Z^ e • Z^ (1/2 * a)))
          ≈⟨ cright sym assoc ⟩
        W • ((S^' (a * a) • Z^ e) • Z^ (1/2 * a))
          ≈⟨ sym assoc ⟩
        (W • (S^' (a * a) • Z^ e)) • Z^ (1/2 * a) ∎

      Rt : R • W ≈ (S • W) • Z^ (1/2 * a)
      Rt = begin
        (S • Z^ 1/2) • W
          ≈⟨ assoc ⟩
        S • (Z^ 1/2 • W)
          ≈⟨ cright (MulZ.Z-W x 1/2) ⟩
        S • (W • Z^ (a * 1/2))
          ≈⟨ cright cright (refl' (Eq.cong (λ z → Z^ z) (*-comm a 1/2))) ⟩
        S • (W • Z^ (1/2 * a))
          ≈⟨ sym assoc ⟩
        (S • W) • Z^ (1/2 * a) ∎

      -- Right cancellation of a Z-power, by hand: BridgeCalc takes no
      -- grouplike witness, and Z^u • Z^(-u) is ε by Z^-+ alone.
      cancel : ∀ {u v} → u • Z^ (1/2 * a) ≈ v • Z^ (1/2 * a) → u ≈ v
      cancel {u} {v} eq = begin
        u
          ≈⟨ sym right-unit ⟩
        u • ε
          ≈⟨ cright sym zz ⟩
        u • (Z^ (1/2 * a) • Z^ (- (1/2 * a)))
          ≈⟨ sym assoc ⟩
        (u • Z^ (1/2 * a)) • Z^ (- (1/2 * a))
          ≈⟨ cleft eq ⟩
        (v • Z^ (1/2 * a)) • Z^ (- (1/2 * a))
          ≈⟨ assoc ⟩
        v • (Z^ (1/2 * a) • Z^ (- (1/2 * a)))
          ≈⟨ cright zz ⟩
        v • ε
          ≈⟨ right-unit ⟩
        v ∎
        where
        zz : Z^ (1/2 * a) • Z^ (- (1/2 * a)) ≈ ε
        zz = trans (Z^-+ (1/2 * a) (- (1/2 * a)))
               (refl' (Eq.cong (λ z → Z^ z) (+-inverseʳ (1/2 * a))))

    -- Paper-V1's spelling gives Paper-V0's …
    S⇒R : W • (S^' (a * a) • Z^ e) ≈ S • W → W • R^ (a * a) ≈ R • W
    S⇒R h = trans L (trans (cleft h) (sym Rt))

    -- … and back.
    R⇒S : W • R^ (a * a) ≈ R • W → W • (S^' (a * a) • Z^ e) ≈ S • W
    R⇒S h = cancel (trans (sym L) (trans h Rt))

  ------------------------------------------------------------------------
  -- The bridge
  --
  -- The R-word RHR x x⁻¹ and the S-word SHS' x⁻¹ x are the same word.
  -- Three blocks, collapsed by stepm, then the Pauli carried back across
  -- them by P-Bm; the arithmetic is x · x⁻¹ ≡ ₁ throughout.

  module Bridge (x : ℤ* ₚ) where

    private
      a : ℤ ₚ
      a = x .proj₁

      b : ℤ ₚ
      b = (x ⁻¹) .proj₁

      γ : ℤ ₚ
      γ = (a + - ₁) * 1/2

      δ : ℤ ₚ
      δ = (₁ + - b) * 1/2

      ab≡1 : a * b ≡ ₁
      ab≡1 = lemma-⁻¹ʳ a {{nztoℕ {y = a} {neq0 = x .proj₂}}}

      half-ab : (1/2 * a) * b ≡ 1/2
      half-ab = Eq.trans (*-assoc 1/2 a b)
                  (Eq.trans (Eq.cong (1/2 *_) ab≡1) (*-identityʳ 1/2))

      distr : ∀ c → (c + - ₁) * 1/2 ≡ (1/2 * c) + - 1/2
      distr c = Eq.trans (*-distribʳ-+ 1/2 c (- ₁))
                  (Eq.cong₂ (λ s t → s + t) (*-comm c 1/2) (neg-mul 1/2))

      distr' : (₁ + - b) * 1/2 ≡ 1/2 + - (1/2 * b)
      distr' = Eq.trans (*-distribʳ-+ 1/2 ₁ (- b))
                 (Eq.cong₂ (λ s t → s + t) (*-identityˡ 1/2)
                   (Eq.trans (Eq.cong (_* 1/2) (Eq.sym (neg-mul b)))
                     (Eq.trans (*-assoc (- ₁) b 1/2)
                       (Eq.trans (neg-mul (b * 1/2))
                         (Eq.cong (λ z → - z) (*-comm b 1/2))))))

      halfba : (1/2 * b) * a ≡ 1/2
      halfba = Eq.trans (*-assoc 1/2 b a)
                 (Eq.trans (Eq.cong (1/2 *_) (Eq.trans (*-comm b a) ab≡1))
                   (*-identityʳ 1/2))

      B1 : (₀ + - ((1/2 * a) * b)) + (1/2 * b) ≡ (b + - ₁) * 1/2
      B1 = Eq.trans (Eq.cong (_+ (1/2 * b))
                       (+-identityˡ (- ((1/2 * a) * b))))
             (Eq.trans (Eq.cong (λ z → - z + (1/2 * b)) half-ab)
               (Eq.trans (+-comm (- 1/2) (1/2 * b)) (Eq.sym (distr b))))

      B3 : - ((b + - ₁) * 1/2) ≡ (₁ + - b) * 1/2
      B3 = Eq.trans (Eq.cong (λ z → - z) (distr b))
             (Eq.trans (neg-+ (1/2 * b) (- 1/2))
               (Eq.trans (Eq.cong (λ z → - (1/2 * b) + z) (neg-involutive 1/2))
                 (Eq.trans (+-comm (- (1/2 * b)) 1/2) (Eq.sym distr'))))

      B2 : ((- (1/2 * a)) + - (((b + - ₁) * 1/2) * a)) + (1/2 * a)
           ≡ (a + - ₁) * 1/2
      B2 = Eq.trans (Eq.cong (λ z → ((- (1/2 * a)) + - z) + (1/2 * a)) inner)
             (Eq.trans (Eq.cong (λ z → ((- (1/2 * a)) + z) + (1/2 * a)) negd)
               (Eq.trans collapse (Eq.sym (distr a))))
        where
        inner : ((b + - ₁) * 1/2) * a ≡ 1/2 + - (1/2 * a)
        inner = Eq.trans (Eq.cong (_* a) (distr b))
                  (Eq.trans (*-distribʳ-+ a (1/2 * b) (- 1/2))
                    (Eq.cong₂ (λ s t → s + t) halfba (neg-* 1/2 a)))
        negd : - (1/2 + - (1/2 * a)) ≡ - 1/2 + (1/2 * a)
        negd = Eq.trans (neg-+ 1/2 (- (1/2 * a)))
                 (Eq.cong (λ z → - 1/2 + z) (neg-involutive (1/2 * a)))
        collapse : ((- (1/2 * a)) + (- 1/2 + (1/2 * a))) + (1/2 * a)
                   ≡ (1/2 * a) + - 1/2
        collapse = Eq.trans (Eq.cong (_+ (1/2 * a)) inner2)
                     (+-comm (- 1/2) (1/2 * a))
          where
          inner2 : (- (1/2 * a)) + (- 1/2 + (1/2 * a)) ≡ - 1/2
          inner2 = Eq.trans (Eq.cong ((- (1/2 * a)) +_) (+-comm (- 1/2) (1/2 * a)))
                     (Eq.trans (Eq.sym (+-assoc (- (1/2 * a)) (1/2 * a) (- 1/2)))
                       (Eq.trans (Eq.cong (_+ (- 1/2)) (+-inverseˡ (1/2 * a)))
                         (+-identityˡ (- 1/2))))

      δa≡γ : δ * a ≡ γ
      δa≡γ = Eq.trans (Eq.cong (_* a) distr')
               (Eq.trans (*-distribʳ-+ a 1/2 (- (1/2 * b)))
                 (Eq.trans (Eq.cong ((1/2 * a) +_)
                              (Eq.trans (neg-* (1/2 * b) a)
                                (Eq.cong (λ z → - z) halfba)))
                   (Eq.sym (distr a))))

      C1 : γ + - (δ * a) ≡ ₀
      C1 = Eq.trans (Eq.cong (λ z → γ + - z) δa≡γ) (+-inverseʳ γ)

      C2 : (- δ) + - (₀ * b) ≡ - δ
      C2 = Eq.trans (Eq.cong (λ z → (- δ) + - z) (*-zeroˡ b))
             (Eq.trans (Eq.cong ((- δ) +_) neg0) (+-identityʳ (- δ)))

      C3 : ₀ + - ((- δ) * a) ≡ γ
      C3 = Eq.trans (+-identityˡ _)
             (Eq.trans (Eq.cong (λ z → - z) (neg-* δ a))
               (Eq.trans (neg-involutive (δ * a)) δa≡γ))

      K : Word (Gen (₁₊ n))
      K = ((S^' a • H) • (S^' b • H)) • (S^' a • H)

      lhs : R^ a • (H • (R^ b • (H • (R^ a • H)))) ≈ K • (X^ γ • Z^ δ)
      lhs = begin
        R^ a • (H • (R^ b • (H • (R^ a • H))))
          ≈⟨ by-passoc (□ ^ 6) (□ ^ 2 • □ ^ 2 • □ ^ 2) auto ⟩
        (R^ a • H) • ((R^ b • H) • (R^ a • H))
          ≈⟨ sym assoc ⟩
        ((R^ a • H) • (R^ b • H)) • (R^ a • H)
          ≈⟨ cong (cong (R^-H a) (R^-H b)) (R^-H a) ⟩
        (((S^' a • H) • X^ (1/2 * a)) • ((S^' b • H) • X^ (1/2 * b)))
          • ((S^' a • H) • X^ (1/2 * a))
          ≈⟨ cleft cleft cright (sym right-unit) ⟩
        (((S^' a • H) • (X^ (1/2 * a) • Z^ ₀)) • ((S^' b • H) • X^ (1/2 * b)))
          • ((S^' a • H) • X^ (1/2 * a))
          ≈⟨ cleft (stepm (S^' a • H) b (1/2 * a) ₀) ⟩
        (((S^' a • H) • (S^' b • H))
          • (X^ ((₀ + - ((1/2 * a) * b)) + (1/2 * b)) • Z^ (- (1/2 * a))))
          • ((S^' a • H) • X^ (1/2 * a))
          ≈⟨ cleft cright cleft (refl' (Eq.cong (λ z → X^ z) B1)) ⟩
        (((S^' a • H) • (S^' b • H))
          • (X^ ((b + - ₁) * 1/2) • Z^ (- (1/2 * a))))
          • ((S^' a • H) • X^ (1/2 * a))
          ≈⟨ stepm ((S^' a • H) • (S^' b • H)) a ((b + - ₁) * 1/2) (- (1/2 * a)) ⟩
        K • (X^ (((- (1/2 * a)) + - (((b + - ₁) * 1/2) * a)) + (1/2 * a))
             • Z^ (- ((b + - ₁) * 1/2)))
          ≈⟨ cright (cong (refl' (Eq.cong (λ z → X^ z) B2))
                          (refl' (Eq.cong (λ z → Z^ z) B3))) ⟩
        K • (X^ γ • Z^ δ) ∎

      K-conj : (X^ δ • Z^ γ) • K ≈ K • (X^ γ • Z^ δ)
      K-conj = begin
        (X^ δ • Z^ γ) • (((S^' a • H) • (S^' b • H)) • (S^' a • H))
          ≈⟨ sym assoc ⟩
        ((X^ δ • Z^ γ) • ((S^' a • H) • (S^' b • H))) • (S^' a • H)
          ≈⟨ cleft sym assoc ⟩
        (((X^ δ • Z^ γ) • (S^' a • H)) • (S^' b • H)) • (S^' a • H)
          ≈⟨ cleft cleft (P-Bm a δ γ) ⟩
        (((S^' a • H) • (X^ (γ + - (δ * a)) • Z^ (- δ))) • (S^' b • H))
          • (S^' a • H)
          ≈⟨ cleft cleft cright cleft (refl' (Eq.cong (λ z → X^ z) C1)) ⟩
        (((S^' a • H) • (X^ ₀ • Z^ (- δ))) • (S^' b • H)) • (S^' a • H)
          ≈⟨ cleft assoc ⟩
        ((S^' a • H) • ((X^ ₀ • Z^ (- δ)) • (S^' b • H))) • (S^' a • H)
          ≈⟨ cleft cright (P-Bm b ₀ (- δ)) ⟩
        ((S^' a • H) • ((S^' b • H) • (X^ ((- δ) + - (₀ * b)) • Z^ (- ₀))))
          • (S^' a • H)
          ≈⟨ cleft cright cright (cong (refl' (Eq.cong (λ z → X^ z) C2))
                                       (refl' (Eq.cong (λ z → Z^ z) neg0))) ⟩
        ((S^' a • H) • ((S^' b • H) • (X^ (- δ) • Z^ ₀))) • (S^' a • H)
          ≈⟨ cleft sym assoc ⟩
        (((S^' a • H) • (S^' b • H)) • (X^ (- δ) • Z^ ₀)) • (S^' a • H)
          ≈⟨ assoc ⟩
        ((S^' a • H) • (S^' b • H)) • ((X^ (- δ) • Z^ ₀) • (S^' a • H))
          ≈⟨ cright (P-Bm a (- δ) ₀) ⟩
        ((S^' a • H) • (S^' b • H))
          • ((S^' a • H) • (X^ (₀ + - ((- δ) * a)) • Z^ (- (- δ))))
          ≈⟨ cright cright (cong (refl' (Eq.cong (λ z → X^ z) C3))
                                 (refl' (Eq.cong (λ z → Z^ z) (neg-involutive δ)))) ⟩
        ((S^' a • H) • (S^' b • H)) • ((S^' a • H) • (X^ γ • Z^ δ))
          ≈⟨ sym assoc ⟩
        K • (X^ γ • Z^ δ) ∎

      rhs : Z^ γ • (X^ δ • (S^' a • (H • (S^' b • (H • (S^' a • H))))))
            ≈ K • (X^ γ • Z^ δ)
      rhs = begin
        Z^ γ • (X^ δ • (S^' a • (H • (S^' b • (H • (S^' a • H))))))
          ≈⟨ by-passoc (□ ^ 8) (□ ^ 2 • (□ ^ 2 • □ ^ 2) • □ ^ 2) auto ⟩
        (Z^ γ • X^ δ) • K
          ≈⟨ cleft sym (comm-X^k-Z^l (toℕ δ) (toℕ γ)) ⟩
        (X^ δ • Z^ γ) • K
          ≈⟨ K-conj ⟩
        K • (X^ γ • Z^ δ) ∎

    -- The R-word for the multiplier is the S-word with its Pauli prefix.
    bridge : R^ a • (H • (R^ b • (H • (R^ a • H))))
             ≈ Z^ γ • (X^ δ • (S^' a • (H • (S^' b • (H • (S^' a • H))))))
    bridge = trans lhs (sym rhs)
