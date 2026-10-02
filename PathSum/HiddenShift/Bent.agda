------------------------------------------------------------------------
-- Presentations of groups
--
-- Bent functions and their duals, through the Walsh transform
--
-- Section 5.2 of Amy's QPL 2018 paper runs the hidden shift algorithm
-- of Rötteler [28] on "the shifted and dual bent functions f′, f̃".  A
-- Boolean function f on n = 2m bits is bent, with dual f̃, when its
-- Walsh transform is 2^m times the sign of f̃ everywhere:
--
--    Σ_x (-1)^{f(x) + a·x} = 2^m (-1)^{f̃(a)}   for every a  (Bent m f f̃).
--
-- The definition is the usual one (Rothaus; the transform of a bent
-- function is ±2^(n/2), its signs defining the dual), stated with the
-- dual given; n is even by construction, Fin (m + m).  Functions are
-- the exponents of the paper's ±1-valued f, Booleans with
-- sgn true = -1 (PathSum.Polynomial.sgn).
--
-- What the algorithm uses of f is one consequence (walsh-shift): the
-- transform of the shifted function f(· ⊕ s) is the transform of f
-- times the character of s, Σ_u (-1)^{f(u ⊕ s) + u·a} =
-- 2^m (-1)^{f̃(a) + s·a}, the sum being invariant under translation.
-- PathSum.HiddenShift.Walsh proved it for the Maiorana-McFarland
-- functions only (walsh-mm-shift); here it is derived from bentness
-- alone.  The Maiorana-McFarland functions g(x) + x·y are bent with
-- dual g(y) + x·y (mm-bent, from Walsh's walsh-mm), so they are an
-- instance.
--
-- RespectsB f (PathSum.HiddenShift.Walsh) says that f reads its
-- argument only through its values: pointwise equal assignments get
-- the same value.  Assignments are functions Fin n → Bool, equal here
-- only pointwise, and without function extensionality nothing forces
-- an arbitrary f to respect that; the sums Σᶻ, built bit by bit, need
-- it to be translated (Σᶻ-shift) or collapsed (Σᶻ-δ), so the theorems
-- that do so assume it.  It is automatic for the functions that matter
-- -- the reading boolᴾ P of a polynomial respects it (HiddenShift's
-- boolᴾ-resp), and so does any function written in terms of the bits
-- of its argument.  PathSum.HiddenShift.AnyBent asks it of the bent
-- function and its dual when they are arbitrary functions
-- (hidden-shift-any), and not at all when they are polynomials'
-- readings (hidden-shift-bent).
--
-- Also here: bentness reads its functions through their values
-- (Bent-cong), and the dual of a bent function is bent, with dual f
-- (dual-bent: by the orthogonality of characters, the transform of f̃
-- is 2^(-m) times the double transform of f, which is 2^n times f).
-- Sums are PathSum.AssignSum's Σᶻ; the exchange of two of them is
-- Σᶻ-swap.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.HiddenShift.Bent where

open import Data.Bool.Base using (Bool; true; false; _xor_; if_then_else_)
open import Data.Bool.Properties using (xor-assoc)
open import Data.Fin.Base using (Fin)
open import Data.Integer.Base using (ℤ; 0ℤ; +_; _+_; _*_)
open import Data.Integer.Properties using
  (*-comm; *-assoc; *-zeroʳ; *-cancelˡ-≡; pos-*)
open import Data.Nat.Base using (ℕ; zero; suc)
  renaming (_+_ to _ℕ+_; _^_ to _ℕ^_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)

import Data.Nat.Properties as ℕ

open import PathSum.Assign using (same)
open import PathSum.AssignSum using
  (Σᶻ; Σᶻ-zero; Σᶻ-suc; Σᶻ-cong; Σᶻ-+; Σᶻ-*; RespectsZ; _∷ᵃ_)
open import PathSum.HiddenShift.Walsh using
  (_⊕ᵃ_; RespectsB; dot; dot-cong; dot-comm; dot-⊕ˡ; sgn-xor;
   Σᶻ-shift; Σᶻ-δ; character-shift; mm; dual; walsh-mm)
open import PathSum.Polynomial using (sgn)

private
  variable
    k l m : ℕ


------------------------------------------------------------------------
-- The Walsh transform, and bentness

-- Σ_x (-1)^{f(x) + a·x}.

walsh : ((Fin k → Bool) → Bool) → (Fin k → Bool) → ℤ
walsh f a = Σᶻ (λ x → sgn (f x xor dot a x))

-- f on 2m bits is bent with dual f̃.

Bent : ∀ m → ((Fin (m ℕ+ m) → Bool) → Bool) →
       ((Fin (m ℕ+ m) → Bool) → Bool) → Set
Bent m f f̃ = ∀ a → walsh f a ≡ + (2 ℕ^ m) * sgn (f̃ a)

-- Only the values of f and f̃ matter.

Bent-cong : {f f′ f̃ f̃′ : (Fin (m ℕ+ m) → Bool) → Bool} →
            (∀ x → f x ≡ f′ x) → (∀ a → f̃ a ≡ f̃′ a) →
            Bent m f f̃ → Bent m f′ f̃′
Bent-cong {m} hf hf̃ b a = trans
  (Σᶻ-cong (λ x → cong (λ t → sgn (t xor dot a x)) (sym (hf x))))
  (trans (b a) (cong (λ t → + (2 ℕ^ m) * sgn t) (hf̃ a)))

-- The Maiorana-McFarland functions are bent.

mm-bent : (g : (Fin m → Bool) → Bool) → RespectsB g → Bent m (mm g) (dual g)
mm-bent g g-resp a = trans
  (Σᶻ-cong (λ x → cong (λ t → sgn (mm g x xor t)) (dot-comm a x)))
  (walsh-mm g g-resp a)


------------------------------------------------------------------------
-- The transform of the shifted function

private
  cancel : (s v : Fin k → Bool) → ∀ i → ((v ⊕ᵃ s) ⊕ᵃ s) i ≡ v i
  cancel s v i = trans (xor-assoc (v i) (s i) (s i)) (again (v i) (s i))
    where
    again : ∀ a b → a xor (b xor b) ≡ a
    again false false = refl
    again false true  = refl
    again true  false = refl
    again true  true  = refl

walsh-shift : (f f̃ : (Fin (m ℕ+ m) → Bool) → Bool) → RespectsB f →
              Bent m f f̃ → (s a : Fin (m ℕ+ m) → Bool) →
              Σᶻ (λ u → sgn (f (u ⊕ᵃ s) xor dot u a)) ≡
              + (2 ℕ^ m) * sgn (f̃ a xor dot s a)
walsh-shift {m} f f̃ f-resp bent s a = begin
  Σᶻ F
    ≡⟨ sym (Σᶻ-shift s F F-resp) ⟩
  Σᶻ (λ v → F (v ⊕ᵃ s))
    ≡⟨ Σᶻ-cong point ⟩
  Σᶻ (λ v → sgn (dot s a) * sgn (f v xor dot a v))
    ≡⟨ Σᶻ-* (sgn (dot s a)) (λ v → sgn (f v xor dot a v)) ⟩
  sgn (dot s a) * walsh f a
    ≡⟨ cong (sgn (dot s a) *_) (bent a) ⟩
  sgn (dot s a) * (P * sgn (f̃ a))
    ≡⟨ regroup (sgn (dot s a)) P (sgn (f̃ a)) ⟩
  P * (sgn (f̃ a) * sgn (dot s a))
    ≡⟨ cong (P *_) (sym (sgn-xor (f̃ a) (dot s a))) ⟩
  P * sgn (f̃ a xor dot s a)
    ∎
  where
  open ≡-Reasoning

  P : ℤ
  P = + (2 ℕ^ m)

  F : (Fin (m ℕ+ m) → Bool) → ℤ
  F u = sgn (f (u ⊕ᵃ s) xor dot u a)

  F-resp : RespectsZ F
  F-resp u v h = cong sgn (cong₂ _xor_
    (f-resp (u ⊕ᵃ s) (v ⊕ᵃ s) (λ i → cong (_xor s i) (h i)))
    (dot-cong h (λ _ → refl)))

  point : ∀ v → F (v ⊕ᵃ s) ≡ sgn (dot s a) * sgn (f v xor dot a v)
  point v = trans
    (cong sgn (trans
      (cong₂ _xor_ (f-resp ((v ⊕ᵃ s) ⊕ᵃ s) v (cancel s v))
                   (dot-⊕ˡ v s a))
      (trans (sym (xor-assoc (f v) (dot v a) (dot s a)))
             (cong (λ t → (f v xor t) xor dot s a) (dot-comm v a)))))
    (trans (sgn-xor (f v xor dot a v) (dot s a))
           (*-comm (sgn (f v xor dot a v)) (sgn (dot s a))))

  regroup : ∀ a b d → a * (b * d) ≡ b * (d * a)
  regroup a b d = trans (sym (*-assoc a b d))
    (trans (cong (_* d) (*-comm a b))
      (trans (*-assoc b a d) (cong (b *_) (*-comm a d))))


------------------------------------------------------------------------
-- Exchanging two sums

Σᶻ-swap : (F : (Fin k → Bool) → (Fin l → Bool) → ℤ) →
          Σᶻ (λ a → Σᶻ (λ b → F a b)) ≡ Σᶻ (λ b → Σᶻ (λ a → F a b))
Σᶻ-swap {zero}  F = trans (Σᶻ-zero (λ a → Σᶻ (λ b → F a b)))
  (sym (Σᶻ-cong (λ b → Σᶻ-zero (λ a → F a b))))
Σᶻ-swap {suc k} F = begin
  Σᶻ (λ a → Σᶻ (λ b → F a b))
    ≡⟨ Σᶻ-suc (λ a → Σᶻ (λ b → F a b)) ⟩
  Σᶻ (λ g → Σᶻ (λ b → F (false ∷ᵃ g) b)) +
  Σᶻ (λ g → Σᶻ (λ b → F (true ∷ᵃ g) b))
    ≡⟨ cong₂ _+_ (Σᶻ-swap (λ g b → F (false ∷ᵃ g) b))
                 (Σᶻ-swap (λ g b → F (true ∷ᵃ g) b)) ⟩
  Σᶻ (λ b → Σᶻ (λ g → F (false ∷ᵃ g) b)) +
  Σᶻ (λ b → Σᶻ (λ g → F (true ∷ᵃ g) b))
    ≡⟨ sym (Σᶻ-+ (λ b → Σᶻ (λ g → F (false ∷ᵃ g) b))
                 (λ b → Σᶻ (λ g → F (true ∷ᵃ g) b))) ⟩
  Σᶻ (λ b → Σᶻ (λ g → F (false ∷ᵃ g) b) + Σᶻ (λ g → F (true ∷ᵃ g) b))
    ≡⟨ Σᶻ-cong (λ b → sym (Σᶻ-suc (λ a → F a b))) ⟩
  Σᶻ (λ b → Σᶻ (λ a → F a b))
    ∎
  where open ≡-Reasoning


------------------------------------------------------------------------
-- The dual of a bent function is bent

-- 2^m times the transform of f̃ at x is the double transform of f,
-- which the orthogonality of characters collapses to 2^n (-1)^{f(x)}.

dual-bent : (f f̃ : (Fin (m ℕ+ m) → Bool) → Bool) → RespectsB f →
            Bent m f f̃ → Bent m f̃ f
dual-bent {m} f f̃ f-resp bent x =
  *-cancelˡ-≡ P (walsh f̃ x) (P * sgn (f x)) {{ℕ.m^n≢0 2 m}} (begin
  P * walsh f̃ x
    ≡⟨ sym (Σᶻ-* P (λ a → sgn (f̃ a xor dot x a))) ⟩
  Σᶻ (λ a → P * sgn (f̃ a xor dot x a))
    ≡⟨ Σᶻ-cong step ⟩
  Σᶻ (λ a → Σᶻ (λ y → sgn (f y) * sgn (dot a y xor dot x a)))
    ≡⟨ Σᶻ-swap (λ a y → sgn (f y) * sgn (dot a y xor dot x a)) ⟩
  Σᶻ (λ y → Σᶻ (λ a → sgn (f y) * sgn (dot a y xor dot x a)))
    ≡⟨ Σᶻ-cong (λ y → trans
         (Σᶻ-* (sgn (f y)) (λ a → sgn (dot a y xor dot x a)))
         (trans (cong (sgn (f y) *_) (character-shift x y))
                (guard (same x y) (sgn (f y))))) ⟩
  Σᶻ (λ y → if same x y then Q * sgn (f y) else 0ℤ)
    ≡⟨ Σᶻ-δ x (λ y → Q * sgn (f y)) resp ⟩
  Q * sgn (f x)
    ≡⟨ cong (_* sgn (f x))
            (trans (cong +_ (ℕ.^-distribˡ-+-* 2 m m))
                   (pos-* (2 ℕ^ m) (2 ℕ^ m))) ⟩
  (P * P) * sgn (f x)
    ≡⟨ *-assoc P P (sgn (f x)) ⟩
  P * (P * sgn (f x))
    ∎)
  where
  open ≡-Reasoning

  P Q : ℤ
  P = + (2 ℕ^ m)
  Q = + (2 ℕ^ (m ℕ+ m))

  -- One term: 2^m (-1)^{f̃(a)} is the transform of f at a.

  step : ∀ a → P * sgn (f̃ a xor dot x a) ≡
               Σᶻ (λ y → sgn (f y) * sgn (dot a y xor dot x a))
  step a = begin
    P * sgn (f̃ a xor dot x a)
      ≡⟨ cong (P *_) (sgn-xor (f̃ a) (dot x a)) ⟩
    P * (sgn (f̃ a) * sgn (dot x a))
      ≡⟨ sym (*-assoc P (sgn (f̃ a)) (sgn (dot x a))) ⟩
    (P * sgn (f̃ a)) * sgn (dot x a)
      ≡⟨ cong (_* sgn (dot x a)) (sym (bent a)) ⟩
    walsh f a * sgn (dot x a)
      ≡⟨ *-comm (walsh f a) (sgn (dot x a)) ⟩
    sgn (dot x a) * walsh f a
      ≡⟨ sym (Σᶻ-* (sgn (dot x a)) (λ y → sgn (f y xor dot a y))) ⟩
    Σᶻ (λ y → sgn (dot x a) * sgn (f y xor dot a y))
      ≡⟨ Σᶻ-cong (λ y → term y) ⟩
    Σᶻ (λ y → sgn (f y) * sgn (dot a y xor dot x a))
      ∎
    where
    term : ∀ y → sgn (dot x a) * sgn (f y xor dot a y) ≡
                 sgn (f y) * sgn (dot a y xor dot x a)
    term y = trans (*-comm (sgn (dot x a)) (sgn (f y xor dot a y)))
      (trans (sym (sgn-xor (f y xor dot a y) (dot x a)))
        (trans (cong sgn (xor-assoc (f y) (dot a y) (dot x a)))
               (sgn-xor (f y) (dot a y xor dot x a))))

  guard : ∀ t (σ : ℤ) → σ * (if t then Q else 0ℤ) ≡ (if t then Q * σ else 0ℤ)
  guard true  σ = *-comm σ Q
  guard false σ = *-zeroʳ σ

  resp : RespectsZ (λ y → Q * sgn (f y))
  resp u v h = cong (λ t → Q * sgn t) (f-resp u v h)
