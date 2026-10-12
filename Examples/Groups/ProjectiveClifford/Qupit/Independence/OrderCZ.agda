------------------------------------------------------------------------
-- Presentations of groups
--
-- order-CZ is independent of the other Paper-V1 rules, when the
-- primitive root is odd
--
-- The witness counts CZ letters mod 2.  At width 2 that separates
-- order-CZ, whose two sides differ by p letters — odd, since p is an
-- odd prime — from every other rule, whose two sides differ by an
-- even number:
--
--   one-wire rules                  0  (no CZ at all)
--   order-Ex                        6
--   comm-CZ-S↑, semi-Ex-S↑/H↑       0
--   semi-M↑CZ                   g − 1  (toℕ g, against 1)
--   blake-c12                   p − 1  (p, against 1)
--
-- so it needs toℕ g odd, and that is the theorem's hypothesis.  For
-- even g the survey found order-CZ redundant at p = 3 and 5.
--
-- The parity cannot be kept beyond width 2: semi-CX↑-CZ↓ has two CZs
-- on one side and nine on the other.  So the model reads parities at
-- widths ≤ 2 and is the trivial monoid from width 3 up, where every
-- three-wire rule starts.  That suffices for an instance at width 2:
-- a derivation there only involves instances of width ≤ 2.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; suc)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_,_ ; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Notations
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.ProjectiveClifford.Qupit.Independence.OrderCZ
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open import Algebra.Bundles using (Monoid)
import Algebra.Construct.Terminal as Terminal
open import Algebra.Morphism.Structures using (module MonoidMorphisms)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Nat.Base using (parity ; z≤n ; s≤s)
open import Data.Nat.Divisibility using (_∣_ ; divides)
open import Data.Nat.Primality using (composite ; module Prime)
open import Data.Parity.Base as ℙ using (Parity ; 0ℙ ; 1ℙ)
import Data.Parity.Properties as ℙₚ
open import Data.Product using (_×_ ; proj₁)
open import Data.Unit using (⊤ ; tt)
open import Function using (case_of_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality
  using (refl ; sym ; trans ; cong ; cong₂ ; module ≡-Reasoning)
open import Relation.Nullary.Negation using (¬_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)

import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Syntactics
  p-3 p-prime g* g-gen as Pap
open Pap using (Gen ; gate₀ ; gate₁ ; gate₂ ; _↥ ; _↑ ; S ; CZ ; CX)
open Pap.Clifford-Relations
  using (module Base ; srel ; Z ; X ; SHS' ; XM ; XMg)
open Base using (_SRel,_===_)
open import Examples.Groups.ProjectiveClifford.Qupit.Independence.Selection
  p-3 p-prime g* g-gen
  using (order-CZ ; Without ; _IndependentOf_ ; module Soundness)

open Primitive-Root-Modp' g* g-gen using (g′ ; g^_)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- p is odd
--
-- p = 3 + p-3 is prime, so it is not 2, and an even number other than 2
-- is not prime.

private
  even⇒2∣ : ∀ m → parity m ≡ 0ℙ → 2 ∣ m
  even⇒2∣ 0             _ = divides 0 refl
  even⇒2∣ 1             ()
  even⇒2∣ (suc (suc m)) e =
    divides (suc (_∣_.quotient d)) (cong (λ x → suc (suc x)) (_∣_.equality d))
    where d = even⇒2∣ m e

odd-p : parity ₚ ≡ 1ℙ
odd-p with parity ₚ in e
... | 1ℙ = refl
... | 0ℙ = ⊥-elim (Prime.notComposite p-prime
                     (composite (s≤s (s≤s (s≤s z≤n))) (even⇒2∣ ₚ e)))

-- and so p - 1 is even.
even-p-1 : parity p-1 ≡ 0ℙ
even-p-1 = trans (sym (ℙₚ.suc-homo-⁻¹ p-3)) (cong ℙ._⁻¹ odd-p)

------------------------------------------------------------------------
-- Counting CZs, mod 2

cz : Gen n → Parity
cz (gate₀ ())
cz (gate₁ _) = 0ℙ
cz (gate₂ _) = 1ℙ
cz (g ↥)     = cz g

count : Word (Gen n) → Parity
count [ g ]ʷ  = cz g
count ε       = 0ℙ
count (w • v) = count w ℙ.+ count v

-- A power of a word with an odd count has the parity of its exponent.
count-^ : (w : Word (Gen n)) → count w ≡ 1ℙ → ∀ k → count (w ^ k) ≡ parity k
count-^ w e 0             = refl
count-^ w e 1             = e
count-^ w e (suc (suc k)) =
  trans (cong₂ ℙ._+_ e (count-^ w e (suc k))) (ℙₚ.suc-homo-⁻¹ k)

------------------------------------------------------------------------
-- Words without a CZ
--
-- Every one-wire word of Paper-V1 is a product of powers of H and S,
-- whose exponents are spelled through toℕ and the inverses of units,
-- so its count does not compute.  It is 0 all the same, since no
-- letter is a CZ; Free says so letter by letter, and is closed under
-- powers and shifts.

Free : Word (Gen n) → Set
Free [ gate₀ _ ]ʷ = ⊤
Free [ gate₁ _ ]ʷ = ⊤
Free [ gate₂ _ ]ʷ = ⊥
Free [ g ↥ ]ʷ     = Free [ g ]ʷ
Free ε            = ⊤
Free (w • v)      = Free w × Free v

free-count : (w : Word (Gen n)) → Free w → count w ≡ 0ℙ
free-count [ gate₀ () ]ʷ _
free-count [ gate₁ _ ]ʷ  _        = refl
free-count [ gate₂ _ ]ʷ  ()
free-count [ g ↥ ]ʷ      f        = free-count [ g ]ʷ f
free-count ε             _        = refl
free-count (w • v)       (f , f') = cong₂ ℙ._+_ (free-count w f) (free-count v f')

free-^ : (w : Word (Gen n)) → Free w → ∀ k → Free (w ^ k)
free-^ w f 0             = tt
free-^ w f 1             = f
free-^ w f (suc (suc k)) = f , free-^ w f (suc k)

free-↑ : (w : Word (Gen n)) → Free w → Free (w ↑)
free-↑ [ g ]ʷ   f        = f
free-↑ ε        _        = tt
free-↑ (w • v)  (f , f') = free-↑ w f , free-↑ v f'

free-S^ : ∀ k → Free (S {n} ^ k)
free-S^ = free-^ S tt

free-Z : Free (Z {n})
free-Z = tt , tt , tt , tt , tt , free-S^ p-1

free-X : Free (X {n})
free-X = tt , tt , tt , tt , free-S^ p-1 , tt

free-SHS' : ∀ a b → Free (SHS' {n} a b)
free-SHS' a b =
  free-^ Z free-Z (toℕ ((b + - ₁) * Pap.1/2)) ,
  free-^ X free-X (toℕ ((₁ + - a) * Pap.1/2)) ,
  free-S^ (toℕ b) , tt , free-S^ (toℕ a) , tt , free-S^ (toℕ b) , tt

free-XM : ∀ x → Free (XM {n} x)
free-XM x = free-SHS' (x .proj₁) ((x ⁻¹) .proj₁)

-- Two CZ-free words have the same count.
one-wire : {w v : Word (Gen n)} → Free w → Free v → count w ≡ count v
one-wire {w = w} {v} f f' = trans (free-count w f) (sym (free-count v f'))

------------------------------------------------------------------------
-- The model: parities up to width 2, nothing from width 3

mon : ℕ → Monoid 0ℓ 0ℓ
mon 0      = ℙₚ.+-0-monoid
mon 1      = ℙₚ.+-0-monoid
mon 2      = ℙₚ.+-0-monoid
mon (₃₊ _) = Terminal.monoid

private
  module Mon {n} = Monoid (mon n)

  -- The carrier, equality and product at width n, with the width
  -- explicit: mon is not injective, so it cannot be inferred.
  C : ℕ → Set
  C n = Monoid.Carrier (mon n)

  infix 4 _⊢_≈_
  _⊢_≈_ : ∀ n → C n → C n → Set
  n ⊢ x ≈ y = Monoid._≈_ (mon n) x y

  _⊢_∙_ : ∀ n → C n → C n → C n
  n ⊢ x ∙ y = Monoid._∙_ (mon n) x y

-- A parity read at width n.
emb : ∀ n → Parity → C n
emb 0      x = x
emb 1      x = x
emb 2      x = x
emb (₃₊ _) _ = _

emb-0 : ∀ n → n ⊢ emb n 0ℙ ≈ Monoid.ε (mon n)
emb-0 0      = refl
emb-0 1      = refl
emb-0 2      = refl
emb-0 (₃₊ _) = _

emb-+ : ∀ n x y → n ⊢ emb n (x ℙ.+ y) ≈ (n ⊢ emb n x ∙ emb n y)
emb-+ 0      _ _ = refl
emb-+ 1      _ _ = refl
emb-+ 2      _ _ = refl
emb-+ (₃₊ _) _ _ = _

-- Every width's monoid is commutative, so every comm rule holds.
comm : ∀ n (x y : C n) → n ⊢ (n ⊢ x ∙ y) ≈ (n ⊢ y ∙ x)
comm 0      = ℙₚ.+-comm
comm 1      = ℙₚ.+-comm
comm 2      = ℙₚ.+-comm
comm (₃₊ _) _ _ = _

⟦_⟧₀ : Gen n → C n
⟦_⟧₀ {n} g = emb n (cz g)

-- The shift is the identity up to width 2 and forgets from there.
σ : C n → C (suc n)
σ {0}           x = x
σ {1}           x = x
σ {suc (suc _)} _ = _

σ-hom : MonoidMorphisms.IsMonoidHomomorphism
          (Monoid.rawMonoid (mon n)) (Monoid.rawMonoid (mon (suc n))) (σ {n})
σ-hom {0} = record
  { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = λ e → e }
      ; homo = λ _ _ → refl }
  ; ε-homo = refl }
σ-hom {1} = record
  { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = λ e → e }
      ; homo = λ _ _ → refl }
  ; ε-homo = refl }
σ-hom {suc (suc _)} = record
  { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = λ _ → _ }
      ; homo = λ _ _ → _ }
  ; ε-homo = _ }

⟦↥⟧ : (g : Gen n) → suc n ⊢ ⟦ g ↥ ⟧₀ ≈ σ {n} ⟦ g ⟧₀
⟦↥⟧ {0}           _ = refl
⟦↥⟧ {1}           _ = refl
⟦↥⟧ {suc (suc _)} _ = _

------------------------------------------------------------------------
-- Soundness of the model for every rule but order-CZ
--
-- A word is read as the parity of its count; so an instance holds as
-- soon as its two sides have equal counts, which is what is checked
-- below for each one- and two-wire rule.  The three-wire rules live
-- at widths ≥ 3, where there is nothing to check.  The one rule that
-- needs g odd is semi-M↑CZ.

module Model (g-odd : parity (toℕ g) ≡ 1ℙ) where

  open Soundness order-CZ mon ⟦_⟧₀

  ⟦⟧-count : (w : Word (Gen n)) → n ⊢ ⟦ w ⟧ ≈ emb n (count w)
  ⟦⟧-count {n} [ g ]ʷ  = Mon.refl {n}
  ⟦⟧-count {n} ε       = Mon.sym {n} (emb-0 n)
  ⟦⟧-count {n} (w • v) =
    Mon.trans {n} (Mon.∙-cong {n} (⟦⟧-count w) (⟦⟧-count v))
                  (Mon.sym {n} (emb-+ n (count w) (count v)))

  -- An instance holds once its two sides have equal counts.  The
  -- instance itself is passed only to fix the width and the words.
  by-count : {w v : Word (Gen n)} → n SRel, w === v →
             count w ≡ count v → n ⊢ ⟦ w ⟧ ≈ ⟦ v ⟧
  by-count {n} {w} {v} _ e =
    Mon.trans {n} (⟦⟧-count w)
      (Mon.trans {n} (Mon.reflexive {n} (cong (emb n) e))
                     (Mon.sym {n} (⟦⟧-count v)))

  -- In particular, once neither side has a CZ.
  by-free : {w v : Word (Gen n)} → n SRel, w === v →
            Free w → Free v → n ⊢ ⟦ w ⟧ ≈ ⟦ v ⟧
  by-free {w = w} {v} s f f' = by-count s (one-wire {w = w} {v} f f')

  -- semi-M↑CZ: g CZs against one, which is where g must be odd.
  count-semi-M↑CZ :
    count (XMg {n} ↑ • CZ ^ toℕ g) ≡ count (CZ • XMg ↑)
  count-semi-M↑CZ {n} = begin
    count (XMg ↑) ℙ.+ count (CZ ^ toℕ g)
      ≡⟨ cong₂ ℙ._+_ M↑≡0 (count-^ CZ refl (toℕ g)) ⟩
    parity (toℕ g)
      ≡⟨ g-odd ⟩
    1ℙ
      ≡⟨ sym (cong (1ℙ ℙ.+_) M↑≡0) ⟩
    1ℙ ℙ.+ count (XMg ↑) ∎
    where
    open ≡-Reasoning
    M↑≡0 : count (XMg {n} ↑) ≡ 0ℙ
    M↑≡0 = free-count (XMg {n} ↑) (free-↑ XMg (free-XM g′))

  -- blake-c12: p CZs against one, and p is odd.
  count-blake-c12 :
    count ((S {n} ^ p-1) ↑ • S ^ p-1 • CX ^ p-1 • S • CX) ≡ count (CZ {n})
  count-blake-c12 {n} =
    cong₂ ℙ._+_
      (free-count ((S {n} ^ p-1) ↑) (free-↑ (S ^ p-1) (free-S^ p-1)))
      (cong₂ ℙ._+_ (free-count (S {suc n} ^ p-1) (free-S^ p-1))
        (cong (ℙ._+ 1ℙ) (trans (count-^ (CX {n}) refl p-1) even-p-1)))

  sound-srel : {w v : Word (Gen n)} (s : n SRel, w === v) →
               Without order-CZ (srel s) → n ⊢ ⟦ w ⟧ ≈ ⟦ v ⟧
  sound-srel s@Base.order-S      _  =
    by-free s (free-S^ ₚ) tt
  sound-srel s@Base.order-H      _  =
    by-free s (tt , tt) (free-XM -'₁)
  sound-srel s@(Base.M-power k)  _  =
    by-free s (free-^ XMg (free-XM g′) (toℕ k)) (free-XM (g^ k))
  sound-srel s@Base.semi-MR      _  =
    by-free s
      (free-XM g′ , free-S^ (toℕ (g * g)) ,
       free-^ Z free-Z (toℕ ((g * g + - g) * Pap.1/2)))
      (tt , free-XM g′)
  sound-srel s@Base.comm-HHSHHS  _  = by-count s refl
  sound-srel Base.order-CZ       ¬u = ⊥-elim (¬u refl)
  sound-srel s@Base.order-Ex     _  = by-count s refl
  sound-srel s@Base.comm-CZ-S↑   _  = by-count s refl
  sound-srel s@Base.semi-M↑CZ    _  = by-count s count-semi-M↑CZ
  sound-srel s@Base.semi-Ex-S↑   _  = by-count s refl
  sound-srel s@Base.semi-Ex-H↑   _  = by-count s refl
  sound-srel s@Base.blake-c12    _  = by-count s count-blake-c12
  sound-srel Base.yang-baxter    _  = _
  sound-srel Base.cz-slide       _  = _
  sound-srel Base.semi-CX↑-CZ↓   _  = _

  open Shift (λ {n} → σ {n}) (λ {n} → σ-hom {n}) (λ {n} → ⟦↥⟧ {n})
  open Rules sound-srel sound-cong↑
    (λ {n} h g _ → comm (suc n) ⟦ g ↥ ⟧₀ ⟦ gate₁ {n = n} h ⟧₀)
    (λ {n} h g _ → comm (suc (suc n)) ⟦ g ↥ ↥ ⟧₀ ⟦ gate₂ {n = n} h ⟧₀)
    (λ ())
    public

  -- At width 2, CZ ^ p has p CZs and ε none.
  separates : ¬ (2 ⊢ ⟦ CZ {0} ^ ₚ ⟧ ≈ ⟦ ε {Gen 2} ⟧)
  separates e =
    case trans (sym (trans (count-^ (CZ {0}) refl ₚ) odd-p))
               (trans (sym (⟦⟧-count (CZ {0} ^ ₚ))) e) of λ ()

------------------------------------------------------------------------
-- The theorem
--
-- For every odd prime p and every primitive root g with toℕ g odd,
-- order-CZ at width 2 is not derivable from the other fourteen rules
-- and the structural rules.

order-CZ-independent : parity (toℕ g) ≡ 1ℙ →
                       srel (Base.order-CZ {0}) IndependentOf order-CZ
order-CZ-independent g-odd =
  Model.independent g-odd (srel Base.order-CZ) (Model.separates g-odd)
