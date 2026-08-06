------------------------------------------------------------------------
-- Presentations of groups
--
-- The Pauli rules present (ℤ/pℤ × ℤ/pℤ)ⁿ.
--
-- XZ.agda gives the n-wire Pauli presentation: generators X and Z on
-- each wire, each of order p, all commuting.  Its semantic target is
-- the additive group of Pauli n = (ℤ/pℤ × ℤ/pℤ)ⁿ, a Pauli word being
-- read as the vector of its X- and Z-exponents.
--
-- The normal form is X^a Z^b on each wire, read straight off that
-- vector; normalising a word is just collecting exponents, which the
-- commutation lemmas of XZ.agda already support.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; suc ; 2+)
open import Data.Nat.Primality using (Prime)

open import Notations

module Examples.Groups.Symplectic.XZPresentation
  (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Algebra.Bundles using (Group)
open import Data.Fin using (toℕ)
open import Data.Fin.Properties using (toℕ-injective ; toℕ-fromℕ< ; toℕ<n)
import Data.Nat as Nat
open import Data.Nat.DivMod
  using (_%_ ; _/_ ; m%n<n ; n%n≡0 ; %-distribˡ-+ ; m%n%n≡m%n ; m<n⇒m%n≡m
        ; m≡m%n+[m/n]*n)
import Data.Nat.Properties as NP
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Vec using ([] ; _∷_)
open import Level using (0ℓ)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
import Relation.Binary.Reasoning.Setoid as SR

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)
import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Definitions
  using (_IsPresentationOf_ ; _IsSubPresentationOf_ ; isPresentationOf)
import Normalization.NormalForm.Setoid as SNF
import Normalization.StarPresentation

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Examples.Groups.Pauli.Semantics p-2 p-prime
  using ( Pauli ; Pauli1 ; pI ; pIₙ ; pX ; pZ ; pX₀ ; pZ₀
        ; _+₁_ ; _+ₚ_ ; +ₚ-group
        ; +₁-identityˡ ; +₁-identityʳ
        ; +ₚ-assoc ; +ₚ-comm ; +ₚ-identityˡ ; +ₚ-identityʳ )
open import Examples.Groups.Symplectic.XZ p-2 p-prime

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- ℤ/pℤ as the image of ℕ
--
-- mult k is the k-fold sum of ₁; it is the residue of k, so it is the
-- identity on representatives of ℤ/pℤ and vanishes at p.

mult : ℕ → ℤ ₚ
mult ₀      = ₀
mult (₁₊ k) = ₁ + mult k

toℕ-+ : ∀ (a b : ℤ ₚ) → toℕ (a + b) ≡ (toℕ a Nat.+ toℕ b) % p
toℕ-+ a b = toℕ-fromℕ< (m%n<n (toℕ a Nat.+ toℕ b) p)

private
  0%p≡0 : 0 % p ≡ 0
  0%p≡0 = Eq.refl

  mult-% : ∀ k → toℕ (mult k) ≡ k % p
  mult-% ₀      = Eq.sym 0%p≡0
  mult-% (₁₊ k) = begin
    toℕ (₁ + mult k)               ≡⟨ toℕ-+ ₁ (mult k) ⟩
    (1 Nat.+ toℕ (mult k)) % p     ≡⟨ Eq.cong (λ z → (1 Nat.+ z) % p) (mult-% k) ⟩
    (1 Nat.+ k % p) % p            ≡⟨ %-distribˡ-+ 1 (k % p) p ⟩
    (1 % p Nat.+ (k % p) % p) % p  ≡⟨ Eq.cong (λ z → (1 % p Nat.+ z) % p) (m%n%n≡m%n k p) ⟩
    (1 % p Nat.+ k % p) % p        ≡⟨ Eq.sym (%-distribˡ-+ 1 k p) ⟩
    (1 Nat.+ k) % p                ∎
    where open Eq.≡-Reasoning

-- mult undoes toℕ, and kills p.
mult-toℕ : ∀ (a : ℤ ₚ) → mult (toℕ a) ≡ a
mult-toℕ a = toℕ-injective (Eq.trans (mult-% (toℕ a)) (m<n⇒m%n≡m (toℕ<n a)))

mult-p : mult p ≡ ₀
mult-p = toℕ-injective (Eq.trans (mult-% p) (n%n≡0 p))

------------------------------------------------------------------------
-- The semantics
--
-- A generator is the corresponding one-hot Pauli; a word is the sum of
-- its letters.  (This is the extension of ⟦_⟧₀ along the Pauli group,
-- written out so that it can be reasoned about at every width.)

⟦_⟧₀ : Gen n → Pauli n
⟦ X-gen ⟧₀ = pX₀
⟦ Z-gen ⟧₀ = pZ₀
⟦ g ↥ ⟧₀   = pI ∷ ⟦ g ⟧₀

sem : Word (Gen n) → Pauli n
sem [ x ]ʷ  = ⟦ x ⟧₀
sem ε       = pIₙ
sem (w • v) = sem w +ₚ sem v

-- Shifting a word up a wire prefixes the identity.
sem-↑ : ∀ (w : Word (Gen n)) → sem (w ↑) ≡ pI ∷ sem w
sem-↑ [ x ]ʷ  = Eq.refl
sem-↑ ε       = Eq.refl
sem-↑ (w • v) = begin
  sem (w ↑) +ₚ sem (v ↑)      ≡⟨ Eq.cong₂ _+ₚ_ (sem-↑ w) (sem-↑ v) ⟩
  (pI ∷ sem w) +ₚ (pI ∷ sem v) ≡⟨ Eq.cong (_∷ (sem w +ₚ sem v)) (+₁-identityˡ pI) ⟩
  pI ∷ (sem w +ₚ sem v)        ∎
  where open Eq.≡-Reasoning

-- Powers of the two generators on the bottom wire.
sem-X^ : ∀ {n} k → sem (X {n} ^ k) ≡ (mult k , ₀) ∷ pIₙ
sem-X^ ₀      = Eq.refl
sem-X^ ₁      = Eq.cong (λ z → (z , ₀) ∷ pIₙ) (Eq.sym (+-identityʳ ₁))
sem-X^ (₂₊ k) = begin
  pX₀ +ₚ sem (X ^ ₁₊ k)
    ≡⟨ Eq.cong (pX₀ +ₚ_) (sem-X^ (₁₊ k)) ⟩
  ((₁ , ₀) +₁ (mult (₁₊ k) , ₀)) ∷ (pIₙ +ₚ pIₙ)
    ≡⟨ Eq.cong₂ _∷_ (Eq.cong ((₁ + mult (₁₊ k)) ,_) (+-identityˡ ₀))
                    (+ₚ-identityˡ pIₙ) ⟩
  (mult (₂₊ k) , ₀) ∷ pIₙ ∎
  where open Eq.≡-Reasoning

sem-Z^ : ∀ {n} k → sem (Z {n} ^ k) ≡ (₀ , mult k) ∷ pIₙ
sem-Z^ ₀      = Eq.refl
sem-Z^ ₁      = Eq.cong (λ z → (₀ , z) ∷ pIₙ) (Eq.sym (+-identityʳ ₁))
sem-Z^ (₂₊ k) = begin
  pZ₀ +ₚ sem (Z ^ ₁₊ k)
    ≡⟨ Eq.cong (pZ₀ +ₚ_) (sem-Z^ (₁₊ k)) ⟩
  ((₀ , ₁) +₁ (₀ , mult (₁₊ k))) ∷ (pIₙ +ₚ pIₙ)
    ≡⟨ Eq.cong₂ _∷_ (Eq.cong (_, (₁ + mult (₁₊ k))) (+-identityˡ ₀))
                    (+ₚ-identityˡ pIₙ) ⟩
  (₀ , mult (₂₊ k)) ∷ pIₙ ∎
  where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- Soundness

sound-ax : ∀ {n} {w v : Word (Gen n)} → n QRel, w === v → sem w ≡ sem v
sound-ax {₁₊ n} order-X =
  Eq.trans (sem-X^ p) (Eq.cong (λ z → (z , ₀) ∷ pIₙ) mult-p)
sound-ax {₁₊ n} order-Z =
  Eq.trans (sem-Z^ p) (Eq.cong (λ z → (₀ , z) ∷ pIₙ) mult-p)
sound-ax {₁₊ n} comm-Z-X          = +ₚ-comm pZ₀ pX₀
sound-ax {₂₊ n} (comm-X {g = g})  = +ₚ-comm (pI ∷ ⟦ g ⟧₀) pX₀
sound-ax {₂₊ n} (comm-Z {g = g})  = +ₚ-comm (pI ∷ ⟦ g ⟧₀) pZ₀
sound-ax {₁₊ n} (cong↑ {w = w} {v} ax) =
  Eq.trans (sem-↑ w) (Eq.trans (Eq.cong (pI ∷_) (sound-ax ax)) (Eq.sym (sem-↑ v)))

------------------------------------------------------------------------
-- The normal form
--
-- X^a Z^b on each wire, read off the exponent vector.

inv-nf : Pauli n → Word (Gen n)
inv-nf {₀}    []             = ε
inv-nf {₁₊ n} ((a , b) ∷ ps) = X ^ toℕ a • Z ^ toℕ b • (inv-nf ps) ↑

-- The section law: reading a vector back out of its normal form gives
-- the vector.
sem-inv : ∀ (P : Pauli n) → sem (inv-nf P) ≡ P
sem-inv {₀}    []             = Eq.refl
sem-inv {₁₊ n} ((a , b) ∷ ps) = begin
  sem (X ^ toℕ a) +ₚ (sem (Z ^ toℕ b) +ₚ sem ((inv-nf ps) ↑))
    ≡⟨ Eq.cong₂ _+ₚ_ (sem-X^ (toℕ a))
        (Eq.cong₂ _+ₚ_ (sem-Z^ (toℕ b))
          (Eq.trans (sem-↑ (inv-nf ps)) (Eq.cong (pI ∷_) (sem-inv ps)))) ⟩
  ((mult (toℕ a) , ₀) ∷ pIₙ) +ₚ (((₀ , mult (toℕ b)) ∷ pIₙ) +ₚ (pI ∷ ps))
    ≡⟨ Eq.cong₂ _∷_ head-eq tail-eq ⟩
  (a , b) ∷ ps ∎
  where
  open Eq.≡-Reasoning
  head-eq : (mult (toℕ a) , ₀) +₁ ((₀ , mult (toℕ b)) +₁ pI) ≡ (a , b)
  head-eq = begin
    (mult (toℕ a) , ₀) +₁ ((₀ , mult (toℕ b)) +₁ pI)
      ≡⟨ Eq.cong ((mult (toℕ a) , ₀) +₁_) (+₁-identityʳ (₀ , mult (toℕ b))) ⟩
    (mult (toℕ a) , ₀) +₁ (₀ , mult (toℕ b))
      ≡⟨ Eq.cong₂ _,_ (+-identityʳ (mult (toℕ a))) (+-identityˡ (mult (toℕ b))) ⟩
    (mult (toℕ a) , mult (toℕ b))
      ≡⟨ Eq.cong₂ _,_ (mult-toℕ a) (mult-toℕ b) ⟩
    (a , b) ∎
  tail-eq : pIₙ +ₚ (pIₙ +ₚ ps) ≡ ps
  tail-eq = Eq.trans (+ₚ-identityˡ (pIₙ +ₚ ps)) (+ₚ-identityˡ ps)

------------------------------------------------------------------------
-- The Pauli presentation is commutative
--
-- Every pair of generators commutes — X with Z by comm-Z-X, either with
-- anything on a higher wire by comm-X / comm-Z, and two higher-wire
-- generators by cong↑ — so every pair of words does.

gen-comm : ∀ {n} (x y : Gen n) →
           let open PB (n QRel,_===_) in [ x ]ʷ • [ y ]ʷ ≈ [ y ]ʷ • [ x ]ʷ
gen-comm {₁₊ n} X-gen  X-gen  = PB.refl
gen-comm {₁₊ n} X-gen  Z-gen  = PB.sym (PB.axiom comm-Z-X)
gen-comm {₁₊ n} Z-gen  X-gen  = PB.axiom comm-Z-X
gen-comm {₁₊ n} Z-gen  Z-gen  = PB.refl
gen-comm {₂₊ n} X-gen  (y ↥)  = PB.sym (PB.axiom comm-X)
gen-comm {₂₊ n} (x ↥)  X-gen  = PB.axiom comm-X
gen-comm {₂₊ n} Z-gen  (y ↥)  = PB.sym (PB.axiom comm-Z)
gen-comm {₂₊ n} (x ↥)  Z-gen  = PB.axiom comm-Z
gen-comm {₂₊ n} (x ↥)  (y ↥)  =
  lemma-cong↑ ([ x ]ʷ • [ y ]ʷ) ([ y ]ʷ • [ x ]ʷ) (gen-comm x y)

word-comm : ∀ {n} (u v : Word (Gen n)) →
            let open PB (n QRel,_===_) in u • v ≈ v • u
word-comm {n} [ x ]ʷ [ y ]ʷ = gen-comm x y
word-comm {n} [ x ]ʷ ε      = PB.trans PB.right-unit (PB.sym PB.left-unit)
word-comm {n} [ x ]ʷ (v • w) = begin
  [ x ]ʷ • (v • w)  ≈⟨ sym assoc ⟩
  ([ x ]ʷ • v) • w  ≈⟨ cleft (word-comm [ x ]ʷ v) ⟩
  (v • [ x ]ʷ) • w  ≈⟨ assoc ⟩
  v • ([ x ]ʷ • w)  ≈⟨ cright (word-comm [ x ]ʷ w) ⟩
  v • (w • [ x ]ʷ)  ≈⟨ sym assoc ⟩
  (v • w) • [ x ]ʷ  ∎
  where
  open PB (n QRel,_===_)
  open PP (n QRel,_===_)
  open SR word-setoid
word-comm {n} ε v = PB.trans PB.left-unit (PB.sym PB.right-unit)
word-comm {n} (u • u') v = begin
  (u • u') • v  ≈⟨ assoc ⟩
  u • (u' • v)  ≈⟨ cright (word-comm u' v) ⟩
  u • (v • u')  ≈⟨ sym assoc ⟩
  (u • v) • u'  ≈⟨ cleft (word-comm u v) ⟩
  (v • u) • u'  ≈⟨ assoc ⟩
  v • (u • u')  ∎
  where
  open PB (n QRel,_===_)
  open PP (n QRel,_===_)
  open SR word-setoid

-- The interchange law of a commutative monoid.
interchange : ∀ {n} (u v u' v' : Word (Gen n)) →
              let open PB (n QRel,_===_) in
              (u • v) • (u' • v') ≈ (u • u') • (v • v')
interchange {n} u v u' v' = begin
  (u • v) • (u' • v')  ≈⟨ assoc ⟩
  u • (v • (u' • v'))  ≈⟨ cright (sym assoc) ⟩
  u • ((v • u') • v')  ≈⟨ cright (cleft (word-comm v u')) ⟩
  u • ((u' • v) • v')  ≈⟨ cright assoc ⟩
  u • (u' • (v • v'))  ≈⟨ sym assoc ⟩
  (u • u') • (v • v')  ∎
  where
  open PB (n QRel,_===_)
  open PP (n QRel,_===_)
  open SR word-setoid

------------------------------------------------------------------------
-- Exponents may be taken modulo p

private
  module _ {n : ℕ} where
    open PB ((₁₊ n) QRel,_===_)
    open PP ((₁₊ n) QRel,_===_)
    open SR word-setoid

    -- The generic argument: a generator of order p has powers depending
    -- only on the exponent mod p.
    pow-mod : ∀ (w : Word (Gen (₁₊ n))) → w ^ p ≈ ε → ∀ k → w ^ k ≈ w ^ (k % p)
    pow-mod w ord k = begin
      w ^ k                             ≡⟨ Eq.cong (w ^_) (m≡m%n+[m/n]*n k p) ⟩
      w ^ (k % p Nat.+ k / p Nat.* p)   ≈⟨ ^-+ w (k % p) (k / p Nat.* p) ⟩
      w ^ (k % p) • w ^ (k / p Nat.* p) ≈⟨ cright (refl' (Eq.cong (w ^_) (NP.*-comm (k / p) p))) ⟩
      w ^ (k % p) • w ^ (p Nat.* (k / p)) ≈⟨ cright (sym (^^ w p (k / p))) ⟩
      w ^ (k % p) • (w ^ p) ^ (k / p)   ≈⟨ cright (^-cong (w ^ p) ε (k / p) ord) ⟩
      w ^ (k % p) • ε ^ (k / p)         ≈⟨ cright (ε^k=ε (k / p)) ⟩
      w ^ (k % p) • ε                   ≈⟨ right-unit ⟩
      w ^ (k % p)                       ∎

    -- Adding exponents on the bottom wire.
    pow-add : ∀ (w : Word (Gen (₁₊ n))) → w ^ p ≈ ε → ∀ (a c : ℤ ₚ) →
              w ^ toℕ a • w ^ toℕ c ≈ w ^ toℕ (a + c)
    pow-add w ord a c = begin
      w ^ toℕ a • w ^ toℕ c         ≈⟨ sym (^-+ w (toℕ a) (toℕ c)) ⟩
      w ^ (toℕ a Nat.+ toℕ c)       ≈⟨ pow-mod w ord (toℕ a Nat.+ toℕ c) ⟩
      w ^ ((toℕ a Nat.+ toℕ c) % p) ≡⟨ Eq.cong (w ^_) (Eq.sym (toℕ-+ a c)) ⟩
      w ^ toℕ (a + c)               ∎

    X-add : ∀ (a c : ℤ ₚ) → X {n} ^ toℕ a • X ^ toℕ c ≈ X ^ toℕ (a + c)
    X-add = pow-add X (axiom order-X)

    Z-add : ∀ (a c : ℤ ₚ) → Z {n} ^ toℕ a • Z ^ toℕ c ≈ Z ^ toℕ (a + c)
    Z-add = pow-add Z (axiom order-Z)

------------------------------------------------------------------------
-- The retraction
--
-- inv-nf turns sums into products, so normalising a word returns it.

inv-hom : ∀ {n} (P Q : Pauli n) →
          let open PB (n QRel,_===_) in
          inv-nf (P +ₚ Q) ≈ inv-nf P • inv-nf Q
inv-hom {₀}    []             []             = PB.sym PB.left-unit
inv-hom {₁₊ n} ((a , b) ∷ ps) ((c , d) ∷ qs) = begin
  X ^ toℕ (a + c) • (Z ^ toℕ (b + d) • (inv-nf (ps +ₚ qs)) ↑)
    ≈⟨ cong (sym (X-add a c))
            (cong (sym (Z-add b d))
                  (lemma-cong↑ _ _ (inv-hom ps qs))) ⟩
  (X ^ toℕ a • X ^ toℕ c)
    • ((Z ^ toℕ b • Z ^ toℕ d) • ((inv-nf ps) ↑ • (inv-nf qs) ↑))
    ≈⟨ cright (sym (interchange (Z ^ toℕ b) ((inv-nf ps) ↑)
                                (Z ^ toℕ d) ((inv-nf qs) ↑))) ⟩
  (X ^ toℕ a • X ^ toℕ c)
    • ((Z ^ toℕ b • (inv-nf ps) ↑) • (Z ^ toℕ d • (inv-nf qs) ↑))
    ≈⟨ sym (interchange (X ^ toℕ a) (Z ^ toℕ b • (inv-nf ps) ↑)
                        (X ^ toℕ c) (Z ^ toℕ d • (inv-nf qs) ↑)) ⟩
  (X ^ toℕ a • (Z ^ toℕ b • (inv-nf ps) ↑))
    • (X ^ toℕ c • (Z ^ toℕ d • (inv-nf qs) ↑)) ∎
  where
  open PB ((₁₊ n) QRel,_===_)
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid

inv-ε : ∀ {n} → let open PB (n QRel,_===_) in inv-nf (pIₙ {n}) ≈ ε
inv-ε {₀}    = PB.refl
inv-ε {₁₊ n} = begin
  ε • (ε • (inv-nf pIₙ) ↑)  ≈⟨ left-unit ⟩
  ε • (inv-nf pIₙ) ↑        ≈⟨ left-unit ⟩
  (inv-nf pIₙ) ↑            ≈⟨ lemma-cong↑ _ _ (inv-ε {n}) ⟩
  ε ↑                       ≈⟨ refl ⟩
  ε                         ∎
  where
  open PB ((₁₊ n) QRel,_===_)
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid

inv-gen : ∀ {n} (x : Gen n) →
          let open PB (n QRel,_===_) in inv-nf ⟦ x ⟧₀ ≈ [ x ]ʷ
inv-gen {₁₊ n} X-gen = begin
  X ^ 1 • (ε • (inv-nf pIₙ) ↑)  ≈⟨ cright left-unit ⟩
  X • (inv-nf pIₙ) ↑            ≈⟨ cright (lemma-cong↑ _ _ (inv-ε {n})) ⟩
  X • ε                         ≈⟨ right-unit ⟩
  X                             ∎
  where
  open PB ((₁₊ n) QRel,_===_)
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
inv-gen {₁₊ n} Z-gen = begin
  ε • (Z ^ 1 • (inv-nf pIₙ) ↑)  ≈⟨ left-unit ⟩
  Z • (inv-nf pIₙ) ↑            ≈⟨ cright (lemma-cong↑ _ _ (inv-ε {n})) ⟩
  Z • ε                         ≈⟨ right-unit ⟩
  Z                             ∎
  where
  open PB ((₁₊ n) QRel,_===_)
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid
inv-gen {₁₊ n} (g ↥) = begin
  ε • (ε • (inv-nf ⟦ g ⟧₀) ↑)  ≈⟨ left-unit ⟩
  ε • (inv-nf ⟦ g ⟧₀) ↑        ≈⟨ left-unit ⟩
  (inv-nf ⟦ g ⟧₀) ↑            ≈⟨ lemma-cong↑ _ _ (inv-gen g) ⟩
  [ g ]ʷ ↑                     ≈⟨ refl ⟩
  [ g ↥ ]ʷ                     ∎
  where
  open PB ((₁₊ n) QRel,_===_)
  open PP ((₁₊ n) QRel,_===_)
  open SR word-setoid

retract : ∀ {n} (w : Word (Gen n)) →
          let open PB (n QRel,_===_) in inv-nf (sem w) ≈ w
retract {n} [ x ]ʷ = inv-gen x
retract {n} ε      = inv-ε
retract {n} (u • v) = begin
  inv-nf (sem u +ₚ sem v)     ≈⟨ inv-hom (sem u) (sem v) ⟩
  inv-nf (sem u) • inv-nf (sem v) ≈⟨ cong (retract u) (retract v) ⟩
  u • v                       ∎
  where
  open PB (n QRel,_===_)
  open PP (n QRel,_===_)
  open SR word-setoid

------------------------------------------------------------------------
-- The presentation

module Build (n : ℕ) where

  private
    Γ = n QRel,_===_
    module SP = Normalization.StarPresentation Γ (Eq.setoid (Pauli n))
    module GS = SP.GroupSem (+ₚ-group n) ⟦_⟧₀
    module NF = SNF Γ (Eq.setoid (Pauli n))

    -- The extension of ⟦_⟧₀ along the Pauli group is `sem`.
    sem-agrees : ∀ (w : Word (Gen n)) → GS.⟦ w ⟧ ≡ sem w
    sem-agrees [ x ]ʷ  = Eq.refl
    sem-agrees ε       = Eq.refl
    sem-agrees (u • v) = Eq.cong₂ _+ₚ_ (sem-agrees u) (sem-agrees v)

    nfp : NF.NormalForm
    nfp = record
      { rightInverse = record
          { to        = sem
          ; from      = inv-nf
          ; to-cong   = sound
          ; from-cong = λ { Eq.refl → PB.refl }
          ; inverseʳ  = λ { {w} Eq.refl → retract w }
          }
      }
      where
      sound : ∀ {w v} → PB._≈_ Γ w v → sem w ≡ sem v
      sound PB.refl            = Eq.refl
      sound (PB.sym eq)        = Eq.sym (sound eq)
      sound (PB.trans eq eq')  = Eq.trans (sound eq) (sound eq')
      sound (PB.cong eq eq')   = Eq.cong₂ _+ₚ_ (sound eq) (sound eq')
      sound (PB.assoc {w} {v} {u}) = +ₚ-assoc (sem w) (sem v) (sem u)
      sound (PB.left-unit {v})     = +ₚ-identityˡ (sem v)
      sound (PB.right-unit {v})    = +ₚ-identityʳ (sem v)
      sound (PB.axiom ax)      = sound-ax ax

    unfp : NF.UniqueNormalForm (Group.setoid (+ₚ-group n)) GS.⟦_⟧ nfp
    unfp = record
      { unique = λ { {P} {Q} eq →
          Eq.trans (Eq.sym (sem-inv P))
            (Eq.trans (Eq.trans (Eq.sym (sem-agrees (inv-nf P)))
                        (Eq.trans eq (sem-agrees (inv-nf Q))))
              (sem-inv Q)) }
      }

    sound-⟦⟧ : ∀ {w v} → Γ w v → GS.⟦ w ⟧ ≡ GS.⟦ v ⟧
    sound-⟦⟧ {w} {v} ax =
      Eq.trans (sem-agrees w) (Eq.trans (sound-ax ax) (Eq.sym (sem-agrees v)))

    module GSP = GS.GetSubPresentation
                   sound-⟦⟧ XZ-GroupLike.grouplike nfp unfp

    -- The congruence of the extension (GroupSem re-exports only the
    -- subpresentation, so take it from Extend directly).
    open import Normalization.StarInterp Γ using (module Extend)
    module E  = Extend (Group.monoid (+ₚ-group n)) ⟦_⟧₀
    module EC = E.Cong sound-⟦⟧

  subpres : Γ IsSubPresentationOf (+ₚ-group n)
  subpres = GSP.groupSubPres

  -- ⟦_⟧ is onto: every Pauli is the reading of its own normal form.
  surj : ∀ (P : Pauli n) → GS.⟦ inv-nf P ⟧ ≡ P
  surj P = Eq.trans (sem-agrees (inv-nf P)) (sem-inv P)

  presentation : Γ IsPresentationOf (+ₚ-group n)
  presentation =
    isPresentationOf subpres
      (λ P → inv-nf P , λ eq → Eq.trans (EC.fʷ-cong eq) (surj P))

------------------------------------------------------------------------
-- The Pauli rules present (ℤ/pℤ × ℤ/pℤ)ⁿ

presentation : ∀ {n} → (n QRel,_===_) IsPresentationOf (+ₚ-group n)
presentation {n} = Build.presentation n
