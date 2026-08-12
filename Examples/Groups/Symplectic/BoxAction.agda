------------------------------------------------------------------------
-- Presentations of groups
--
-- Single-qupit box actions for the plain gate set.
--
-- The Pauli action `act w = ap ⟦ w ⟧` of the basic single-qupit boxes
-- (S-powers, H, the H·S rotation, the multiplier M).  These are the
-- ground layer of the constructive normal-form theorem `Theorem-LM`.
--
-- Because the plain S is a single (unparameterised) gate, `S^ κ` is the
-- ℕ-power `S ^ toℕ κ`, so its action must be computed by induction over
-- toℕ κ together with the mod-p successor law `sc (suc m) = sc m + ₁`.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; 2+ ; zero ; suc)
open import Data.Nat.Primality using (Prime)

module Examples.Groups.Symplectic.BoxAction (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

import Data.Nat as Nat
open import Data.Nat.DivMod using (m%n<n ; _%_ ; %-distribˡ-+ ; m<n⇒m%n≡m)
open import Data.Fin using (Fin ; toℕ ; fromℕ<)
open import Data.Fin.Properties using (toℕ<n ; toℕ-fromℕ< ; fromℕ<-toℕ ; fromℕ<-cong)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (≡×≡⇒≡)
open import Data.Vec using (_∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; module ≡-Reasoning)

open import Notations
open import Word.Base using ([_]ʷ ; ε ; _•_ ; _^_)

open import ForStdlib.Data.Fin.Mod
open PrimeModulus p-2 p-prime
open import Algebra.Properties.Ring (+-*-ring p-2)

open import Examples.Groups.ProjectivePauli.Semantics p-2 p-prime using (Pauli ; Pauli1 ; pZ ; pX ; pI)

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic using (Circuit ; Gen ; S ; H ; S^ ; M ; CZ ; CZ^ ; Ex ; _↑)


open import Examples.Groups.Symplectic.Semantics p-2 p-prime as Sem
open Sem.Symplectic using (ap)
open Sem.Interpretation using (⟦_⟧)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The Pauli action of a circuit (act (w • v) = act w ∘ act v on the nose)

act : ∀ {n} → Circuit n → Pauli n → Pauli n
act w = ap ⟦ w ⟧

------------------------------------------------------------------------
-- ℕ → ℤ/p, the canonical mod-p representative, and its two laws

sc : ℕ → ℤ ₚ
sc m = fromℕ< (m%n<n m p)

-- sc is a section of toℕ on Fin p.
sc-toℕ : ∀ (κ : ℤ ₚ) → sc (toℕ κ) ≡ κ
sc-toℕ κ = begin
  fromℕ< (m%n<n (toℕ κ) p)
    ≡⟨ fromℕ<-cong (toℕ κ % p) (toℕ κ) (m<n⇒m%n≡m (toℕ<n κ)) (m%n<n (toℕ κ) p) (toℕ<n κ) ⟩
  fromℕ< (toℕ<n κ)
    ≡⟨ fromℕ<-toℕ κ (toℕ<n κ) ⟩
  κ ∎
  where open ≡-Reasoning

oneₚ : ℤ ₚ
oneₚ = ₁

-- toℕ ₁ = 1  (p ≥ 2).
toℕ-₁ : toℕ oneₚ ≡ 1
toℕ-₁ = Eq.refl

1<p : 1 Nat.< p
1<p = Nat.s≤s (Nat.s≤s Nat.z≤n)

-- Mod-p successor: sc (suc m) = ₁ + sc m.
sc-suc : ∀ m → sc (suc m) ≡ oneₚ + sc m
sc-suc m =
  fromℕ<-cong (suc m % p) ((toℕ oneₚ Nat.+ toℕ (sc m)) % p)
    proof (m%n<n (suc m) p) (m%n<n (toℕ oneₚ Nat.+ toℕ (sc m)) p)
  where
  open ≡-Reasoning
  proof : suc m % p ≡ (toℕ oneₚ Nat.+ toℕ (sc m)) % p
  proof = begin
    suc m % p                                    ≡⟨ %-distribˡ-+ 1 m p ⟩
    (1 % p Nat.+ m % p) % p                      ≡⟨ Eq.cong (λ z → (z Nat.+ m % p) % p) (m<n⇒m%n≡m 1<p) ⟩
    (1 Nat.+ m % p) % p                          ≡⟨ Eq.cong (λ z → (toℕ oneₚ Nat.+ z) % p) (Eq.sym (toℕ-fromℕ< (m%n<n m p))) ⟩
    (toℕ oneₚ Nat.+ toℕ (sc m)) % p ∎

------------------------------------------------------------------------
-- The S-power action:  S ^ m sends (a , b) to (a , b + a·⟨m⟩)

act-S^ℕ : ∀ (m : ℕ) (a b : ℤ ₚ) (t : Pauli n) →
  act (S ^ m) ((a , b) ∷ t) ≡ (a , b + a * sc m) ∷ t
act-S^ℕ zero a b t = Eq.cong (λ z → (a , z) ∷ t)
  (Eq.trans (Eq.sym (+-identityʳ b)) (Eq.cong (b +_) (Eq.sym (*-zeroʳ a))))
act-S^ℕ 1 a b t = Eq.cong (λ z → (a , z) ∷ t)
  (Eq.cong (b +_) (Eq.sym (*-identityʳ a)))
act-S^ℕ (2+ m) a b t = begin
  act (S • S ^ ₁₊ m) ((a , b) ∷ t)
    ≡⟨ Eq.refl ⟩
  act S (act (S ^ ₁₊ m) ((a , b) ∷ t))
    ≡⟨ Eq.cong (act S) (act-S^ℕ (₁₊ m) a b t) ⟩
  act S ((a , b + a * sc (₁₊ m)) ∷ t)
    ≡⟨ Eq.refl ⟩
  (a , (b + a * sc (₁₊ m)) + a) ∷ t
    ≡⟨ Eq.cong (λ z → (a , z) ∷ t) step ⟩
  (a , b + a * sc (2+ m)) ∷ t ∎
  where
  open ≡-Reasoning
  step : (b + a * sc (₁₊ m)) + a ≡ b + a * sc (2+ m)
  step = begin
    (b + a * sc (₁₊ m)) + a          ≡⟨ +-assoc b (a * sc (₁₊ m)) a ⟩
    b + (a * sc (₁₊ m) + a)          ≡⟨ Eq.cong (b +_) (+-comm (a * sc (₁₊ m)) a) ⟩
    b + (a + a * sc (₁₊ m))          ≡⟨ Eq.cong (λ z → b + (z + a * sc (₁₊ m))) (Eq.sym (*-identityʳ a)) ⟩
    b + (a * ₁ + a * sc (₁₊ m))      ≡⟨ Eq.cong (b +_) (Eq.sym (*-distribˡ-+ a ₁ (sc (₁₊ m)))) ⟩
    b + a * (₁ + sc (₁₊ m))          ≡⟨ Eq.cong (λ z → b + a * z) (Eq.sym (sc-suc (₁₊ m))) ⟩
    b + a * sc (2+ m) ∎

-- The field-scalar form:  act (S^ κ) (a , b) = (a , b + a·κ).
act-S^ : ∀ (κ : ℤ ₚ) (a b : ℤ ₚ) (t : Pauli n) →
  act (S^ κ) ((a , b) ∷ t) ≡ (a , b + a * κ) ∷ t
act-S^ κ a b t = Eq.trans (act-S^ℕ (toℕ κ) a b t)
  (Eq.cong (λ z → (a , b + a * z) ∷ t) (sc-toℕ κ))

------------------------------------------------------------------------
-- The H and H·S rotations

act-H : ∀ (a b : ℤ ₚ) (t : Pauli n) → act H ((a , b) ∷ t) ≡ (- b , a) ∷ t
act-H a b t = Eq.refl

act-HS^ : ∀ (κ a b : ℤ ₚ) (t : Pauli n) →
  act (H • S^ κ) ((a , b) ∷ t) ≡ (- (b + a * κ) , a) ∷ t
act-HS^ κ a b t = Eq.cong (act H) (act-S^ κ a b t)

------------------------------------------------------------------------
-- The multiplier M x acts as the symplectic scaling diag(x⁻¹ , x).
-- The pure-algebra tail is ported from the (commented) NF1-Sym.lemma-M;
-- the S-power peels use act-S^ (the plain S^ κ does not reduce on its own).

-- The A-box column is built from XM, whereas act-M below is stated for
-- ZM.  XM x is ZM (x ⁻¹), so one congruence carries the action across;
-- callers chain this in front of act-M.
act-XM : ∀ (x : ℤ* ₚ) (ps : Pauli (₁₊ n)) →
  act (Symplectic.XM x) ps ≡ act (M (x ⁻¹)) ps
act-XM x ps = Eq.cong (λ w → act w ps) (Symplectic.XM≡ZM⁻¹ x)

act-M : ∀ (x' : ℤ* ₚ) (a b : ℤ ₚ) (t : Pauli n) →
  act (M x') ((a , b) ∷ t) ≡ (a * ((x' ⁻¹) .proj₁) , b * (x' .proj₁)) ∷ t
act-M x' a b t = begin
  act (M x') ((a , b) ∷ t)
    ≡⟨ Eq.refl ⟩
  act (S^ x • H • S^ x⁻¹ • H • S^ x) ((- b , a) ∷ t)
    ≡⟨ Eq.cong (act (S^ x • H • S^ x⁻¹ • H)) (act-S^ x (- b) a t) ⟩
  act (S^ x • H • S^ x⁻¹ • H) ((- b , a + (- b) * x) ∷ t)
    ≡⟨ Eq.refl ⟩
  act (S^ x • H • S^ x⁻¹) ((- (a + (- b) * x) , - b) ∷ t)
    ≡⟨ Eq.cong (act (S^ x • H)) (act-S^ x⁻¹ (- (a + (- b) * x)) (- b) t) ⟩
  act (S^ x • H) ((- (a + (- b) * x) , - b + (- (a + (- b) * x)) * x⁻¹) ∷ t)
    ≡⟨ Eq.refl ⟩
  act (S^ x) ((- (- b + (- (a + (- b) * x)) * x⁻¹) , - (a + (- b) * x)) ∷ t)
    ≡⟨ act-S^ x (- (- b + (- (a + (- b) * x)) * x⁻¹)) (- (a + (- b) * x)) t ⟩
  (- (- b + - (a + - b * x) * x⁻¹) , - (a + - b * x) + - (- b + - (a + - b * x) * x⁻¹) * x) ∷ t
    ≡⟨ Eq.cong (_∷ t) (Eq.sym (≡×≡⇒≡ (-‿+-comm (- b) (- (a + - b * x) * x⁻¹) , Eq.cong₂ _+_ (-‿+-comm a (- b * x)) (Eq.cong (_* x) (-‿+-comm (- b) (- (a + - b * x) * x⁻¹)))))) ⟩
  (- - b + - ((- (a + - b * x)) * x⁻¹) , - a + - (- b * x) + (- - b + - (- (a + - b * x) * x⁻¹)) * x) ∷ t
    ≡⟨ Eq.cong (_∷ t) (≡×≡⇒≡ (Eq.cong₂ _+_ (-‿involutive b) (-‿distribˡ-* ((- (a + - b * x))) x⁻¹) , Eq.cong₂ _+_ (Eq.cong (- a +_) (-‿distribˡ-* (- b) x)) (Eq.cong₂ (λ xx yy → (xx + yy) * x) (-‿involutive b) (-‿distribˡ-* (- (a + - b * x)) x⁻¹)))) ⟩
  (b + - (- (a + - b * x)) * x⁻¹ , - a + - - b * x + (b + - - (a + - b * x) * x⁻¹) * x) ∷ t
    ≡⟨ Eq.cong (_∷ t) (≡×≡⇒≡ (Eq.cong (λ xx → b + xx * x⁻¹) (-‿involutive (a + - b * x)) , Eq.cong₂ _+_ (Eq.cong (λ xx → - a + xx * x) (-‿involutive b)) (Eq.cong (λ xx → (b + xx * x⁻¹) * x) (-‿involutive (a + - b * x))))) ⟩
  (b + (a + - b * x) * x⁻¹ , - a + b * x + (b + (a + - b * x) * x⁻¹) * x) ∷ t
    ≡⟨ Eq.cong (_∷ t) (≡×≡⇒≡ (Eq.cong (b +_) (*-distribʳ-+ x⁻¹ a (- b * x)) , Eq.cong (λ xx → - a + b * x + xx) (*-distribʳ-+ x b ((a + - b * x) * x⁻¹)))) ⟩
  (b + (a * x⁻¹ + - b * x * x⁻¹) , - a + b * x + (b * x + (a + - b * x) * x⁻¹ * x)) ∷ t
    ≡⟨ Eq.cong (_∷ t) (≡×≡⇒≡ (Eq.cong (λ xx → b + (a * x⁻¹ + xx)) (*-assoc (- b) x x⁻¹) , Eq.cong (λ xx → - a + b * x + (b * x + xx)) (*-assoc ((a + - b * x)) x⁻¹ x))) ⟩
  (b + (a * x⁻¹ + - b * (x * x⁻¹)) , - a + b * x + (b * x + (a + - b * x) * (x⁻¹ * x))) ∷ t
    ≡⟨ Eq.cong (_∷ t) (≡×≡⇒≡ (Eq.cong (λ xx → b + (a * x⁻¹ + - b * xx)) (lemma-⁻¹ʳ x {{nztoℕ {y = x} {neq0 = x' .proj₂}}}) , Eq.cong (λ xx → - a + b * x + (b * x + (a + - b * x) * xx)) (lemma-⁻¹ˡ x {{nztoℕ {y = x} {neq0 = x' .proj₂}}}))) ⟩
  (b + (a * x⁻¹ + - b * ₁) , - a + b * x + (b * x + (a + - b * x) * ₁)) ∷ t
    ≡⟨ Eq.cong (_∷ t) (≡×≡⇒≡ (Eq.cong (λ xx → b + (a * x⁻¹ + xx)) (*-identityʳ (- b)) , Eq.cong (λ xx → - a + b * x + (b * x + xx)) (*-identityʳ (a + - b * x)))) ⟩
  (b + (a * x⁻¹ + - b) , - a + b * x + (b * x + (a + - b * x))) ∷ t
    ≡⟨ Eq.cong (_∷ t) (≡×≡⇒≡ (Eq.cong (b +_) (+-comm (a * x⁻¹) (- b)) , Eq.cong (λ xx → - a + b * x + xx) (+-comm (b * x) ((a + - b * x))))) ⟩
  (b + (- b + a * x⁻¹) , - a + b * x + ((a + - b * x) + b * x)) ∷ t
    ≡⟨ Eq.cong (_∷ t) (Eq.sym (≡×≡⇒≡ (+-assoc b (- b) (a * x⁻¹) , +-assoc (- a + b * x) ((a + - b * x)) (b * x)))) ⟩
  (b + - b + a * x⁻¹ , - a + b * x + (a + - b * x) + b * x) ∷ t
    ≡⟨ Eq.cong (_∷ t) (≡×≡⇒≡ (Eq.cong (_+ a * x⁻¹) (+-inverseʳ b) , Eq.cong (_+ b * x) (+-assoc (- a) (b * x) ((a + - b * x))))) ⟩
  (₀ + a * x⁻¹ , - a + (b * x + (a + - b * x)) + b * x) ∷ t
    ≡⟨ Eq.cong (_∷ t) (≡×≡⇒≡ (+-identityˡ (a * x⁻¹) , Eq.cong (λ xx → - a + (b * x + xx) + b * x) (+-comm a (- b * x)))) ⟩
  (a * x⁻¹ , - a + (b * x + (- b * x + a)) + b * x) ∷ t
    ≡⟨ Eq.cong (λ xx → (a * x⁻¹ , - a + xx + b * x) ∷ t) (Eq.sym (+-assoc (b * x) (- b * x) a)) ⟩
  (a * x⁻¹ , - a + (b * x + - b * x + a) + b * x) ∷ t
    ≡⟨ Eq.cong (λ xx → (a * x⁻¹ , - a + (b * x + xx + a) + b * x) ∷ t) (Eq.sym (-‿distribˡ-* b x)) ⟩
  (a * x⁻¹ , - a + (b * x + - (b * x) + a) + b * x) ∷ t
    ≡⟨ Eq.cong (λ xx → (a * x⁻¹ , - a + (xx + a) + b * x) ∷ t) (+-inverseʳ (b * x)) ⟩
  (a * x⁻¹ , - a + (₀ + a) + b * x) ∷ t
    ≡⟨ Eq.cong (λ xx → (a * x⁻¹ , - a + xx + b * x) ∷ t) (+-identityˡ a) ⟩
  (a * x⁻¹ , - a + a + b * x) ∷ t
    ≡⟨ Eq.cong (λ xx → (a * x⁻¹ , xx + b * x) ∷ t) (+-inverseˡ a) ⟩
  (a * x⁻¹ , ₀ + b * x) ∷ t
    ≡⟨ Eq.cong (λ xx → (a * x⁻¹ , xx) ∷ t) (+-identityˡ (b * x)) ⟩
  (a * x⁻¹ , b * x) ∷ t ∎
  where
  open ≡-Reasoning
  x = x' .proj₁
  x⁻¹ = (x' ⁻¹) .proj₁

------------------------------------------------------------------------
-- The CZ-power action (two qupits):
--   CZ^ κ sends (a,b)(a',b') to (a, b+a'·κ)(a', b'+a·κ).

act-CZ^ℕ : ∀ (m : ℕ) (a b a' b' : ℤ ₚ) (t : Pauli n) →
  act (CZ ^ m) ((a , b) ∷ (a' , b') ∷ t)
    ≡ (a , b + a' * sc m) ∷ (a' , b' + a * sc m) ∷ t
act-CZ^ℕ zero a b a' b' t =
  Eq.cong₂ (λ z w → (a , z) ∷ (a' , w) ∷ t)
    (Eq.trans (Eq.sym (+-identityʳ b)) (Eq.cong (b +_) (Eq.sym (*-zeroʳ a'))))
    (Eq.trans (Eq.sym (+-identityʳ b')) (Eq.cong (b' +_) (Eq.sym (*-zeroʳ a))))
act-CZ^ℕ 1 a b a' b' t =
  Eq.cong₂ (λ z w → (a , z) ∷ (a' , w) ∷ t)
    (Eq.cong (b +_) (Eq.sym (*-identityʳ a')))
    (Eq.cong (b' +_) (Eq.sym (*-identityʳ a)))
act-CZ^ℕ (2+ m) a b a' b' t = begin
  act (CZ • CZ ^ ₁₊ m) ((a , b) ∷ (a' , b') ∷ t)
    ≡⟨ Eq.refl ⟩
  act CZ (act (CZ ^ ₁₊ m) ((a , b) ∷ (a' , b') ∷ t))
    ≡⟨ Eq.cong (act CZ) (act-CZ^ℕ (₁₊ m) a b a' b' t) ⟩
  act CZ ((a , b + a' * sc (₁₊ m)) ∷ (a' , b' + a * sc (₁₊ m)) ∷ t)
    ≡⟨ Eq.refl ⟩
  (a , (b + a' * sc (₁₊ m)) + a') ∷ (a' , (b' + a * sc (₁₊ m)) + a) ∷ t
    ≡⟨ Eq.cong₂ (λ z w → (a , z) ∷ (a' , w) ∷ t) (sc-step a' b) (sc-step a b') ⟩
  (a , b + a' * sc (2+ m)) ∷ (a' , b' + a * sc (2+ m)) ∷ t ∎
  where
  open ≡-Reasoning
  sc-step : ∀ y z → (z + y * sc (₁₊ m)) + y ≡ z + y * sc (2+ m)
  sc-step y z = begin
    (z + y * sc (₁₊ m)) + y          ≡⟨ +-assoc z (y * sc (₁₊ m)) y ⟩
    z + (y * sc (₁₊ m) + y)          ≡⟨ Eq.cong (z +_) (+-comm (y * sc (₁₊ m)) y) ⟩
    z + (y + y * sc (₁₊ m))          ≡⟨ Eq.cong (λ w → z + (w + y * sc (₁₊ m))) (Eq.sym (*-identityʳ y)) ⟩
    z + (y * ₁ + y * sc (₁₊ m))      ≡⟨ Eq.cong (z +_) (Eq.sym (*-distribˡ-+ y ₁ (sc (₁₊ m)))) ⟩
    z + y * (₁ + sc (₁₊ m))          ≡⟨ Eq.cong (λ w → z + y * w) (Eq.sym (sc-suc (₁₊ m))) ⟩
    z + y * sc (2+ m) ∎

act-CZ^ : ∀ (κ a b a' b' : ℤ ₚ) (t : Pauli n) →
  act (CZ^ κ) ((a , b) ∷ (a' , b') ∷ t)
    ≡ (a , b + a' * κ) ∷ (a' , b' + a * κ) ∷ t
act-CZ^ κ a b a' b' t = Eq.trans (act-CZ^ℕ (toℕ κ) a b a' b' t)
  (Eq.cong₂ (λ z w → (a , b + a' * z) ∷ (a' , b' + a * w) ∷ t) (sc-toℕ κ) (sc-toℕ κ))

------------------------------------------------------------------------
-- Ex swaps the two qupits:  Ex (a,b)(c,d) = (c,d)(a,b).

private
  -- -(-y + -(x + -y)) = x
  aux-swap1 : ∀ x y → - (- y + - (x + - y)) ≡ x
  aux-swap1 x y = begin
    - (- y + - (x + - y))
      ≡⟨ Eq.cong (λ z → - (- y + z)) (Eq.trans (Eq.sym (-‿+-comm x (- y))) (Eq.cong (- x +_) (-‿involutive y))) ⟩
    - (- y + (- x + y))
      ≡⟨ Eq.cong (λ z → - (- y + z)) (+-comm (- x) y) ⟩
    - (- y + (y + - x))
      ≡⟨ Eq.cong -_ (Eq.sym (+-assoc (- y) y (- x))) ⟩
    - (- y + y + - x)
      ≡⟨ Eq.cong (λ z → - (z + - x)) (+-inverseˡ y) ⟩
    - (₀ + - x)
      ≡⟨ Eq.cong -_ (+-identityˡ (- x)) ⟩
    - (- x)
      ≡⟨ -‿involutive x ⟩
    x ∎
    where open ≡-Reasoning

  -- -(x + -y) + x = y
  aux-final : ∀ x y → - (x + - y) + x ≡ y
  aux-final x y = begin
    - (x + - y) + x
      ≡⟨ Eq.cong (_+ x) (Eq.trans (Eq.sym (-‿+-comm x (- y))) (Eq.cong (- x +_) (-‿involutive y))) ⟩
    (- x + y) + x
      ≡⟨ Eq.cong (_+ x) (+-comm (- x) y) ⟩
    (y + - x) + x
      ≡⟨ +-assoc y (- x) x ⟩
    y + (- x + x)
      ≡⟨ Eq.cong (y +_) (+-inverseˡ x) ⟩
    y + ₀
      ≡⟨ +-identityʳ y ⟩
    y ∎
    where open ≡-Reasoning

act-Ex : ∀ (a b c d : ℤ ₚ) (t : Pauli n) →
  act Ex ((a , b) ∷ (c , d) ∷ t) ≡ (c , d) ∷ (a , b) ∷ t
act-Ex a b c d t = begin
  act Ex ((a , b) ∷ (c , d) ∷ t)
    ≡⟨ Eq.refl ⟩
  (- (- b + - (c + - b)) , - (a + - d) + - (- d + - (a + - d))) ∷
    (- (- d + - (a + - d)) , - (c + - b) + - (- b + - (c + - b))) ∷ t
    ≡⟨ Eq.cong₂ (λ P Q → P ∷ Q ∷ t)
         (≡×≡⇒≡ (aux-swap1 c b , Eq.trans (Eq.cong (- (a + - d) +_) (aux-swap1 a d)) (aux-final a d)))
         (≡×≡⇒≡ (aux-swap1 a d , Eq.trans (Eq.cong (- (c + - b) +_) (aux-swap1 c b)) (aux-final c b))) ⟩
  (c , d) ∷ (a , b) ∷ t ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- Lifting a circuit up one wire fixes the top qupit and acts on the tail.

lemma-act-↑ : ∀ {n} (w : Circuit n) p ps → act (w ↑) (p ∷ ps) ≡ p ∷ act w ps
lemma-act-↑ [ g ]ʷ  p ps = Eq.refl
lemma-act-↑ ε       p ps = Eq.refl
lemma-act-↑ (w • v) p ps =
  Eq.trans (Eq.cong (act (w ↑)) (lemma-act-↑ v p ps)) (lemma-act-↑ w p (act v ps))
