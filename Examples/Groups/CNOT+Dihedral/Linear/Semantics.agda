------------------------------------------------------------------------
-- Presentations of groups
--
-- The linear coset tower: what the representatives compute
--
-- r ℓ writes the parity ℓ·x on wire 0 (r-head), and the column part
-- s₁ u of a normal form keeps wire 0 (s₁-head), sends 0 to 0 and the
-- vector u to e₀ (s₁-zero, s₁-vec).  The data are read back from these
-- values: a nonzero row is determined by its parities (dot-injective),
-- a vector by itself (vec₁-injective).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.CNOT+Dihedral.Linear.Semantics where

open import Data.Bool using (Bool ; true ; false ; _xor_)
open import Data.Bool.Properties using (xor-identityʳ)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec using (Vec ; [] ; _∷_ ; head ; tail ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊ ; ₂₊)

open import Examples.Groups.CNOT+Dihedral.Semantics
open import Examples.Groups.CNOT+Dihedral.Syntactics
open import Examples.Groups.CNOT+Dihedral.Evaluation
open import Examples.Groups.CNOT+Dihedral.Linear.Local using (CX01)
open import Examples.Groups.CNOT+Dihedral.Linear.Base

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Parities and vectors

dot : NZ n → Bits n → Bool
dot e₀     (a ∷ x) = a
dot (cx ℓ) (a ∷ x) = dot ℓ x xor a
dot (sw ℓ) (a ∷ x) = dot ℓ x

zeros : Bits n
zeros {n} = replicate n false

e-vec : Bits (₁₊ n)
e-vec = true ∷ zeros

vec₁ : SOne n → Bits n
vec₁ one₀    = e-vec
vec₁ (one u) = true ∷ vec u

dot-zeros : (ℓ : NZ n) → dot ℓ zeros ≡ false
dot-zeros e₀     = Eq.refl
dot-zeros (cx ℓ) = Eq.cong (_xor false) (dot-zeros ℓ)
dot-zeros (sw ℓ) = dot-zeros ℓ

-- A vector on which the parity is odd.
witness : (ℓ : NZ n) → Σ (Bits n) (λ x → dot ℓ x ≡ true)
witness e₀     = e-vec , Eq.refl
witness (cx ℓ) = e-vec , Eq.cong (_xor true) (dot-zeros ℓ)
witness (sw ℓ) = false ∷ proj₁ (witness ℓ) , proj₂ (witness ℓ)

private
  t≢f : true ≢ false
  t≢f ()

  absurd : ∀ {A : Set} → true ≡ false → A
  absurd ()

dot-injective : (ℓ ℓ' : NZ n) → (∀ x → dot ℓ x ≡ dot ℓ' x) → ℓ ≡ ℓ'
dot-injective e₀ e₀ e = Eq.refl
dot-injective e₀ (cx ℓ') e =
  absurd (Eq.trans (Eq.sym (proj₂ (witness ℓ')))
           (Eq.trans (Eq.sym (xor-identityʳ _)) (Eq.sym (e (false ∷ proj₁ (witness ℓ'))))))
dot-injective e₀ (sw ℓ') e =
  absurd (Eq.trans (e (true ∷ zeros)) (dot-zeros ℓ'))
dot-injective (cx ℓ) e₀ e =
  absurd (Eq.trans (Eq.sym (proj₂ (witness ℓ)))
           (Eq.trans (Eq.sym (xor-identityʳ _)) (e (false ∷ proj₁ (witness ℓ)))))
dot-injective (sw ℓ) e₀ e =
  absurd (Eq.trans (Eq.sym (e (true ∷ zeros))) (dot-zeros ℓ))
dot-injective (cx ℓ) (cx ℓ') e =
  Eq.cong cx (dot-injective ℓ ℓ' λ x →
    Eq.trans (Eq.sym (xor-identityʳ _)) (Eq.trans (e (false ∷ x)) (xor-identityʳ _)))
dot-injective (sw ℓ) (sw ℓ') e = Eq.cong sw (dot-injective ℓ ℓ' λ x → e (false ∷ x))
dot-injective (cx ℓ) (sw ℓ') e = absurd (flip-absurd (dot ℓ zeros) lo hi)
  where
  lo : dot ℓ zeros ≡ dot ℓ' zeros
  lo = Eq.trans (Eq.sym (xor-identityʳ _)) (e (false ∷ zeros))
  hi : (dot ℓ zeros xor true) ≡ dot ℓ' zeros
  hi = e (true ∷ zeros)
  flip-absurd : ∀ b → b ≡ dot ℓ' zeros → (b xor true) ≡ dot ℓ' zeros → true ≡ false
  flip-absurd false p q = Eq.trans q (Eq.sym p)
  flip-absurd true  p q = Eq.sym (Eq.trans q (Eq.sym p))
dot-injective (sw ℓ) (cx ℓ') e =
  Eq.sym (dot-injective (cx ℓ') (sw ℓ) (λ x → Eq.sym (e x)))

vec-nonzero : (u : NZ n) → vec u ≢ zeros
vec-nonzero e₀     ()
vec-nonzero (cx u) ()
vec-nonzero (sw u) e = vec-nonzero u (Eq.cong tail e)

vec-injective : (u u' : NZ n) → vec u ≡ vec u' → u ≡ u'
vec-injective e₀     e₀      e = Eq.refl
vec-injective e₀     (cx u') e = ⊥-elim (vec-nonzero u' (Eq.sym (Eq.cong tail e)))
  where open import Data.Empty using (⊥-elim)
vec-injective e₀     (sw u') ()
vec-injective (cx u) e₀      e = ⊥-elim (vec-nonzero u (Eq.cong tail e))
  where open import Data.Empty using (⊥-elim)
vec-injective (cx u) (cx u') e = Eq.cong cx (vec-injective u u' (Eq.cong tail e))
vec-injective (cx u) (sw u') ()
vec-injective (sw u) e₀      ()
vec-injective (sw u) (cx u') ()
vec-injective (sw u) (sw u') e = Eq.cong sw (vec-injective u u' (Eq.cong tail e))

vec₁-injective : (u u' : SOne n) → vec₁ u ≡ vec₁ u' → u ≡ u'
vec₁-injective one₀    one₀     e = Eq.refl
vec₁-injective one₀    (one u') e =
  ⊥-elim (vec-nonzero u' (Eq.sym (Eq.cong tail e)))
  where open import Data.Empty using (⊥-elim)
vec₁-injective (one u) one₀     e =
  ⊥-elim (vec-nonzero u (Eq.cong tail e))
  where open import Data.Empty using (⊥-elim)
vec₁-injective (one u) (one u') e = Eq.cong one (vec-injective u u' (Eq.cong tail e))

------------------------------------------------------------------------
-- The gadgets on two wires

private
  hd-CNOT : (a : Bool) (v : Bits (₁₊ n)) → head (fn CNOT (a ∷ v)) ≡ head v xor a
  hd-CNOT a (c ∷ y) = Eq.cong head (fn-CNOT a c y)

  hd-SWAP : (a : Bool) (v : Bits (₁₊ n)) → head (fn SWAP (a ∷ v)) ≡ head v
  hd-SWAP a (c ∷ y) = Eq.cong head (fn-SWAP a c y)

fn-CX01 : (a b : Bool) (y : Bits n) → fn CX01 (a ∷ b ∷ y) ≡ a ∷ (b xor a) ∷ y
fn-CX01 a b y =
  Eq.trans (fn-• SWAP (CNOT • SWAP) (a ∷ b ∷ y))
  (Eq.trans (Eq.cong (fn SWAP) (fn-• CNOT SWAP (a ∷ b ∷ y)))
  (Eq.trans (Eq.cong (λ v → fn SWAP (fn CNOT v)) (fn-SWAP a b y))
  (Eq.trans (Eq.cong (fn SWAP) (fn-CNOT b a y))
  (Eq.trans (fn-SWAP (a xor b) a y)
            (Eq.cong (λ c → a ∷ c ∷ y) (xor-comm a b))))))
  where open import Data.Bool.Properties using (xor-comm)

private
  hd-CX01 : (a : Bool) (v : Bits (₁₊ n)) → head (fn CX01 (a ∷ v)) ≡ a
  hd-CX01 a (c ∷ y) = Eq.cong head (fn-CX01 a c y)

  hd-↑ : (w : Circuit n) (v : Bits (₁₊ n)) → head (fn (w ↑) v) ≡ head v
  hd-↑ w (a ∷ y) = Eq.cong head (fn-↑ w a y)

-- Products, one factor at a time.
private
  fn-•↑ : (g : Circuit (₁₊ n)) (w : Circuit n) (a : Bool) (x : Bits n) →
          fn (g • w ↑) (a ∷ x) ≡ fn g (a ∷ fn w x)
  fn-•↑ g w a x = Eq.trans (fn-• g (w ↑) (a ∷ x)) (Eq.cong (fn g) (fn-↑ w a x))

------------------------------------------------------------------------
-- What the representatives compute

r-head : (ℓ : NZ (₁₊ n)) (x : Bits (₁₊ n)) → head (fn (r ℓ) x) ≡ dot ℓ x
r-head e₀ (a ∷ x) = Eq.cong head (fn-ε (a ∷ x))
r-head (cx ℓ) (a ∷ x) =
  Eq.trans (Eq.cong head (fn-•↑ CNOT (r ℓ) a x))
  (Eq.trans (hd-CNOT a (fn (r ℓ) x)) (Eq.cong (_xor a) (r-head ℓ x)))
r-head (sw ℓ) (a ∷ x) =
  Eq.trans (Eq.cong head (fn-•↑ SWAP (r ℓ) a x))
  (Eq.trans (hd-SWAP a (fn (r ℓ) x)) (r-head ℓ x))

s₁-head : (u : SOne (₁₊ n)) (x : Bits (₁₊ n)) → head (fn (s₁ u) x) ≡ head x
s₁-head one₀ x = Eq.cong head (fn-ε x)
s₁-head (one u) (a ∷ x) =
  Eq.trans (Eq.cong head (fn-•↑ CX01 (s u) a x)) (hd-CX01 a (fn (s u) x))

s-zero : (u : NZ n) → fn (s u) zeros ≡ zeros
s-zero e₀ = fn-ε zeros
s-zero (cx u) =
  Eq.trans (fn-•↑ CX01 (s u) false zeros)
  (Eq.trans (Eq.cong (λ v → fn CX01 (false ∷ v)) (s-zero u))
            (fn-CX01 false false zeros))
s-zero (sw u) =
  Eq.trans (fn-•↑ SWAP (s u) false zeros)
  (Eq.trans (Eq.cong (λ v → fn SWAP (false ∷ v)) (s-zero u))
            (fn-SWAP false false zeros))

s-vec : (u : NZ (₁₊ n)) → fn (s u) (vec u) ≡ e-vec
s-vec e₀ = fn-ε e-vec
s-vec (cx u) =
  Eq.trans (fn-•↑ CX01 (s u) true (vec u))
  (Eq.trans (Eq.cong (λ v → fn CX01 (true ∷ v)) (s-vec u))
            (fn-CX01 true true zeros))
s-vec (sw u) =
  Eq.trans (fn-•↑ SWAP (s u) false (vec u))
  (Eq.trans (Eq.cong (λ v → fn SWAP (false ∷ v)) (s-vec u))
            (fn-SWAP false true zeros))

s₁-zero : (u : SOne n) → fn (s₁ u) zeros ≡ zeros
s₁-zero one₀    = fn-ε zeros
s₁-zero (one u) =
  Eq.trans (fn-•↑ CX01 (s u) false zeros)
  (Eq.trans (Eq.cong (λ v → fn CX01 (false ∷ v)) (s-zero u))
            (fn-CX01 false false zeros))

s₁-vec : (u : SOne (₁₊ n)) → fn (s₁ u) (vec₁ u) ≡ e-vec
s₁-vec one₀    = fn-ε e-vec
s₁-vec (one u) =
  Eq.trans (fn-•↑ CX01 (s u) true (vec u))
  (Eq.trans (Eq.cong (λ v → fn CX01 (true ∷ v)) (s-vec u))
            (fn-CX01 true true zeros))

-- The upper part keeps wire 0.
↑-head : (w : Circuit n) (v : Bits (₁₊ n)) → head (fn (w ↑) v) ≡ head v
↑-head = hd-↑
