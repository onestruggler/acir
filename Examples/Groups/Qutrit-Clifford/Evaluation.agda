------------------------------------------------------------------------
-- Presentations of groups
--
-- Evaluating circuits column by column
--
-- Semantics reads a circuit as the product of its gates' matrices, and
-- a product of two dense 27 × 27 tries costs some twenty thousand
-- multiplications in ℤ[ζ]: about thirty seconds, too slow for the
-- three-qutrit rules, whose SWAPs are nine gates each.  Here a gate
-- acts on a column vector locally — an H on one wire combines three
-- entries, S, CZ and −ω change one — and every entry of a gate is a
-- power of ζ, so the multiplications are rotations of the four
-- coefficients: ζ ⟨a , b , c , e⟩ = ⟨−e , a , b + e , c⟩, as ζ⁴ =
-- ζ² − 1.  ev w has the matrix of w column by column, and ev w ≈ ⟦ w ⟧
-- (ev-≈); eqF compares two values exactly, with each power of √3
-- computed once, and by-fast checks a rule on its own wires by them.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Qutrit-Clifford.Evaluation where

open import Algebra.Bundles using (CommutativeRing)
open import Data.Bool.Base using (Bool ; T ; true ; false ; _∧_ ; if_then_else_)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Integer.Base as ℤ using (+_ ; -[1+_])
import Data.List.Base as List
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
import Data.Nat.Properties as ℕP
open import Data.Unit using (tt)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)

open import Word.Base using ([_]ʷ ; ε ; _•_)

import Examples.Independence.Semantics.Quartic as Quartic
open import Examples.Groups.Qutrit-Clifford.Syntactics
open import Examples.Groups.Qutrit-Clifford.Semantics

open +-*-Solver using (solve ; _:=_ ; _:+_ ; _:*_ ; :-_ ; con)
open Quartic (+ 1) (-[1+ 0 ]) using (_*ₗ_ ; *≡*ₗ ; ⟨≡⟩ ; Q⁴ ; module Mul)
open CommutativeRing R using (*-assoc ; *-identityˡ)

private
  variable
    k n : ℕ

  open Eq.≡-Reasoning

------------------------------------------------------------------------
-- Multiplication by powers of ζ

-- Only ζ³ (the factor of H), ζ⁴ = ω, ζ⁸ = ω² and ζ¹⁰ = −ω occur, and
-- each is a linear map of the four coefficients, since ζ⁴ = ζ² − 1
-- and ζ⁶ = −1.  The entries they are applied to are evaluated already
-- (strict, below), so they are not forced here.
r3 : Q → Q
r3 ⟨ a , b , c , e ⟩ =
  ⟨ ℤ.- (b ℤ.+ e) , ℤ.- c , b , a ℤ.+ c ⟩

r4 : Q → Q
r4 ⟨ a , b , c , e ⟩ =
  ⟨ ℤ.- (a ℤ.+ c) , ℤ.- (b ℤ.+ e) , a , b ⟩

r8 : Q → Q
r8 ⟨ a , b , c , e ⟩ =
  ⟨ c , e , ℤ.- (a ℤ.+ c) , ℤ.- (b ℤ.+ e) ⟩

r10 : Q → Q
r10 ⟨ a , b , c , e ⟩ =
  ⟨ a ℤ.+ c , b ℤ.+ e , ℤ.- a , ℤ.- b ⟩

private
  module MP {m : ℕ} = Mul (_:+_ {m}) _:*_

  π₀ π₁ π₂ π₃ : {B : Set} → Q⁴ B → B
  π₀ (a , _ , _ , _) = a
  π₁ (_ , a , _ , _) = a
  π₂ (_ , _ , a , _) = a
  π₃ (_ , _ , _ , a) = a

r3-ok : (v : Q) → x ^q 3 * v ≡ r3 v
r3-ok ⟨ a , b , c , e ⟩ = Eq.trans (*≡*ₗ (x ^q 3) ⟨ a , b , c , e ⟩) (⟨≡⟩
  (solve 4 (λ a b c e → π₀ (MP.mul (con (+ 1)) (con -[1+ 0 ]) (con (+ 0) , con (+ 0) , con (+ 0) , con (+ 1)) (a , b , c , e))
     := :- (b :+ e)) refl a b c e)
  (solve 4 (λ a b c e → π₁ (MP.mul (con (+ 1)) (con -[1+ 0 ]) (con (+ 0) , con (+ 0) , con (+ 0) , con (+ 1)) (a , b , c , e))
     := :- c) refl a b c e)
  (solve 4 (λ a b c e → π₂ (MP.mul (con (+ 1)) (con -[1+ 0 ]) (con (+ 0) , con (+ 0) , con (+ 0) , con (+ 1)) (a , b , c , e))
     := b) refl a b c e)
  (solve 4 (λ a b c e → π₃ (MP.mul (con (+ 1)) (con -[1+ 0 ]) (con (+ 0) , con (+ 0) , con (+ 0) , con (+ 1)) (a , b , c , e))
     := a :+ c) refl a b c e))

r4-ok : (v : Q) → x ^q 4 * v ≡ r4 v
r4-ok ⟨ a , b , c , e ⟩ = Eq.trans (*≡*ₗ (x ^q 4) ⟨ a , b , c , e ⟩) (⟨≡⟩
  (solve 4 (λ a b c e → π₀ (MP.mul (con (+ 1)) (con -[1+ 0 ]) (con -[1+ 0 ] , con (+ 0) , con (+ 1) , con (+ 0)) (a , b , c , e))
     := :- (a :+ c)) refl a b c e)
  (solve 4 (λ a b c e → π₁ (MP.mul (con (+ 1)) (con -[1+ 0 ]) (con -[1+ 0 ] , con (+ 0) , con (+ 1) , con (+ 0)) (a , b , c , e))
     := :- (b :+ e)) refl a b c e)
  (solve 4 (λ a b c e → π₂ (MP.mul (con (+ 1)) (con -[1+ 0 ]) (con -[1+ 0 ] , con (+ 0) , con (+ 1) , con (+ 0)) (a , b , c , e))
     := a) refl a b c e)
  (solve 4 (λ a b c e → π₃ (MP.mul (con (+ 1)) (con -[1+ 0 ]) (con -[1+ 0 ] , con (+ 0) , con (+ 1) , con (+ 0)) (a , b , c , e))
     := b) refl a b c e))

r8-ok : (v : Q) → x ^q 8 * v ≡ r8 v
r8-ok ⟨ a , b , c , e ⟩ = Eq.trans (*≡*ₗ (x ^q 8) ⟨ a , b , c , e ⟩) (⟨≡⟩
  (solve 4 (λ a b c e → π₀ (MP.mul (con (+ 1)) (con -[1+ 0 ]) (con (+ 0) , con (+ 0) , con -[1+ 0 ] , con (+ 0)) (a , b , c , e))
     := c) refl a b c e)
  (solve 4 (λ a b c e → π₁ (MP.mul (con (+ 1)) (con -[1+ 0 ]) (con (+ 0) , con (+ 0) , con -[1+ 0 ] , con (+ 0)) (a , b , c , e))
     := e) refl a b c e)
  (solve 4 (λ a b c e → π₂ (MP.mul (con (+ 1)) (con -[1+ 0 ]) (con (+ 0) , con (+ 0) , con -[1+ 0 ] , con (+ 0)) (a , b , c , e))
     := :- (a :+ c)) refl a b c e)
  (solve 4 (λ a b c e → π₃ (MP.mul (con (+ 1)) (con -[1+ 0 ]) (con (+ 0) , con (+ 0) , con -[1+ 0 ] , con (+ 0)) (a , b , c , e))
     := :- (b :+ e)) refl a b c e))

r10-ok : (v : Q) → x ^q 10 * v ≡ r10 v
r10-ok ⟨ a , b , c , e ⟩ = Eq.trans (*≡*ₗ (x ^q 10) ⟨ a , b , c , e ⟩) (⟨≡⟩
  (solve 4 (λ a b c e → π₀ (MP.mul (con (+ 1)) (con -[1+ 0 ]) (con (+ 1) , con (+ 0) , con -[1+ 0 ] , con (+ 0)) (a , b , c , e))
     := a :+ c) refl a b c e)
  (solve 4 (λ a b c e → π₁ (MP.mul (con (+ 1)) (con -[1+ 0 ]) (con (+ 1) , con (+ 0) , con -[1+ 0 ] , con (+ 0)) (a , b , c , e))
     := b :+ e) refl a b c e)
  (solve 4 (λ a b c e → π₂ (MP.mul (con (+ 1)) (con -[1+ 0 ]) (con (+ 1) , con (+ 0) , con -[1+ 0 ] , con (+ 0)) (a , b , c , e))
     := :- a) refl a b c e)
  (solve 4 (λ a b c e → π₃ (MP.mul (con (+ 1)) (con -[1+ 0 ]) (con (+ 1) , con (+ 0) , con -[1+ 0 ] , con (+ 0)) (a , b , c , e))
     := :- b) refl a b c e))

-- Multiplication by ω^j and by S's phase on |b⟩.
rotω : Fin 3 → Q → Q
rotω zero             a = a
rotω (suc zero)       a = r4 a
rotω (suc (suc zero)) a = r8 a

rotω-ok : (j : Fin 3) (a : Q) → ω^ j * a ≡ rotω j a
rotω-ok zero             a = *-identityˡ a
rotω-ok (suc zero)       a = r4-ok a
rotω-ok (suc (suc zero)) a = r8-ok a

rotS : Fin 3 → Q → Q
rotS zero             a = r4 a
rotS (suc zero)       a = r4 a
rotS (suc (suc zero)) a = a

rotS-ok : (b : Fin 3) (a : Q) → sph b * a ≡ rotS b a
rotS-ok zero             a = r4-ok a
rotS-ok (suc zero)       a = r4-ok a
rotS-ok (suc (suc zero)) a = *-identityˡ a

------------------------------------------------------------------------
-- Operators applied to vectors

app : Op n → (Digits n → Q) → Digits n → Q
app M f xs = Σv (λ z → M xs z * f z)

app-cong : {M N : Op n} → M ≐ N → (f : Digits n → Q) (xs : Digits n) →
           app M f xs ≡ app N f xs
app-cong e f xs = Σ-cong (λ z → Eq.cong (_* f z) (e xs z))

app-congᶠ : (M : Op n) {f g : Digits n → Q} → (∀ z → f z ≡ g z) → (xs : Digits n) →
            app M f xs ≡ app M g xs
app-congᶠ M e xs = Σ-cong (λ z → Eq.cong (M xs z *_) (e z))

app-id : (f : Digits n → Q) (xs : Digits n) → app (ix (idM {n})) f xs ≡ f xs
app-id f xs = Eq.trans (app-cong ix-id f xs) (Σ-δˡ xs f)

app-⊙ : (M N : Op n) (f : Digits n → Q) (xs : Digits n) →
        app M (app N f) xs ≡ app (M ⊙ N) f xs
app-⊙ M N f xs = begin
  Σv (λ z → M xs z * Σv (λ t → N z t * f t))
    ≡⟨ Σ-cong (λ z → Eq.sym (Σ-scaleˡ (M xs z) (λ t → N z t * f t))) ⟩
  Σv (λ z → Σv (λ t → M xs z * (N z t * f t)))
    ≡⟨ Σ-swap (λ z t → M xs z * (N z t * f t)) ⟩
  Σv (λ t → Σv (λ z → M xs z * (N z t * f t)))
    ≡⟨ Σ-cong (λ t → Σ-cong (λ z → Eq.sym (*-assoc (M xs z) (N z t) (f t)))) ⟩
  Σv (λ t → Σv (λ z → (M xs z * N z t) * f t))
    ≡⟨ Σ-cong (λ t → Σ-scaleʳ (f t) (λ z → M xs z * N z t)) ⟩
  Σv (λ t → (M ⊙ N) xs t * f t) ∎

-- A scalar, a gate on the bottom one or two wires, and an operator one
-- wire up, applied to a vector.
app-scal : (c : Q) (f : Digits n → Q) (xs : Digits n) →
           app (ix (scalM {n} c)) f xs ≡ c * f xs
app-scal c f xs = begin
  Σv (λ z → ix (scalM c) xs z * f z)
    ≡⟨ app-cong (ix-scalM c) f xs ⟩
  Σv (λ z → (c * δv xs z) * f z)
    ≡⟨ Σ-cong (λ z → *-assoc c (δv xs z) (f z)) ⟩
  Σv (λ z → c * (δv xs z * f z))
    ≡⟨ Σ-scaleˡ c (λ z → δv xs z * f z) ⟩
  c * Σv (λ z → δv xs z * f z)
    ≡⟨ Eq.cong (c *_) (Σ-δˡ xs f) ⟩
  c * f xs ∎

app-emb₁ : (G : Mat 1) (f : Digits (suc n) → Q) (a : Fin 3) (xs : Digits n) →
           app (ix (tenM G (idM {n}))) f (a ∷ xs) ≡
           Σ₁ (λ b → ix G (a ∷ []) (b ∷ []) * f (b ∷ xs))
app-emb₁ G f a xs = Σ₁-cong λ b → let g = ix G (a ∷ []) (b ∷ []) in begin
  Σv (λ zs → ix (tenM G idM) (a ∷ xs) (b ∷ zs) * f (b ∷ zs))
    ≡⟨ Σ-cong (λ zs → Eq.cong (_* f (b ∷ zs))
         (Eq.trans (ix-tenM G idM (a ∷ xs) (b ∷ zs))
                   (Eq.cong (ix G (a ∷ []) (b ∷ []) *_) (ix-id xs zs)))) ⟩
  Σv (λ zs → (g * δv xs zs) * f (b ∷ zs))
    ≡⟨ Σ-cong (λ zs → *-assoc g (δv xs zs) (f (b ∷ zs))) ⟩
  Σv (λ zs → g * (δv xs zs * f (b ∷ zs)))
    ≡⟨ Σ-scaleˡ g (λ zs → δv xs zs * f (b ∷ zs)) ⟩
  g * Σv (λ zs → δv xs zs * f (b ∷ zs))
    ≡⟨ Eq.cong (g *_) (Σ-δˡ xs (λ zs → f (b ∷ zs))) ⟩
  g * f (b ∷ xs) ∎

app-emb₂ : (G : Mat 2) (f : Digits (suc (suc n)) → Q) (a a' : Fin 3) (xs : Digits n) →
           app (ix (tenM G (idM {n}))) f (a ∷ a' ∷ xs) ≡
           Σ₁ (λ b → Σ₁ (λ b' → ix G (a ∷ a' ∷ []) (b ∷ b' ∷ []) * f (b ∷ b' ∷ xs)))
app-emb₂ G f a a' xs = Σ₁-cong λ b → Σ₁-cong λ b' →
  let g = ix G (a ∷ a' ∷ []) (b ∷ b' ∷ []) in begin
  Σv (λ zs → ix (tenM G idM) (a ∷ a' ∷ xs) (b ∷ b' ∷ zs) * f (b ∷ b' ∷ zs))
    ≡⟨ Σ-cong (λ zs → Eq.cong (_* f (b ∷ b' ∷ zs))
         (Eq.trans (ix-tenM G idM (a ∷ a' ∷ xs) (b ∷ b' ∷ zs))
                   (Eq.cong (g *_) (ix-id xs zs)))) ⟩
  Σv (λ zs → (g * δv xs zs) * f (b ∷ b' ∷ zs))
    ≡⟨ Σ-cong (λ zs → *-assoc g (δv xs zs) (f (b ∷ b' ∷ zs))) ⟩
  Σv (λ zs → g * (δv xs zs * f (b ∷ b' ∷ zs)))
    ≡⟨ Σ-scaleˡ g (λ zs → δv xs zs * f (b ∷ b' ∷ zs)) ⟩
  g * Σv (λ zs → δv xs zs * f (b ∷ b' ∷ zs))
    ≡⟨ Eq.cong (g *_) (Σ-δˡ xs (λ zs → f (b ∷ b' ∷ zs))) ⟩
  g * f (b ∷ b' ∷ xs) ∎

app-up : (G : Mat n) (f : Digits (suc n) → Q) (a : Fin 3) (xs : Digits n) →
         app (ix (tenM (idM {1}) G)) f (a ∷ xs) ≡ app (ix G) (λ zs → f (a ∷ zs)) xs
app-up G f a xs = begin
  Σ₁ (λ b → Σv (λ zs → ix (tenM idM G) (a ∷ xs) (b ∷ zs) * f (b ∷ zs)))
    ≡⟨ Σ₁-cong (λ b → Σ-cong (λ zs → Eq.trans (Eq.cong (_* f (b ∷ zs))
         (Eq.trans (ix-tenM idM G (a ∷ xs) (b ∷ zs))
                   (Eq.cong (_* ix G xs zs) (ix-id {1} (a ∷ []) (b ∷ [])))))
         (regroup (δ₁ a b) (ix G xs zs) (f (b ∷ zs))))) ⟩
  Σ₁ (λ b → Σv (λ zs → δ₁ a b * (ix G xs zs * f (b ∷ zs))))
    ≡⟨ Σ₁-cong (λ b → Σ-scaleˡ (δ₁ a b) (λ zs → ix G xs zs * f (b ∷ zs))) ⟩
  Σ₁ (λ b → δ₁ a b * Σv (λ zs → ix G xs zs * f (b ∷ zs)))
    ≡⟨ Σ₁-δˡ a (λ b → Σv (λ zs → ix G xs zs * f (b ∷ zs))) ⟩
  Σv (λ zs → ix G xs zs * f (a ∷ zs)) ∎
  where
  open CommutativeRing R using (*-identityʳ)
  regroup : (d g c : Q) → ((d * 1#) * g) * c ≡ d * (g * c)
  regroup d g c = Eq.trans (Eq.cong (λ u → (u * g) * c) (*-identityʳ d)) (*-assoc d g c)

------------------------------------------------------------------------
-- The generators, locally

-- The entry at xs of a generator's image of a vector f, read off at
-- most three entries of f.
loc : Gen n → (Digits n → Q) → Digits n → Q
loc (gate₀ ν-gate)  f xs             = r10 (f xs)
loc (gate₁ H-gate)  f (a ∷ xs)       = r3 (Σ₁ (λ b → rotω (a ⊠ b) (f (b ∷ xs))))
loc (gate₁ S-gate)  f (a ∷ xs)       = rotS a (f (a ∷ xs))
loc (gate₂ CZ-gate) f (a ∷ a' ∷ xs)  = rotω (a ⊠ a') (f (a ∷ a' ∷ xs))
loc (g ↥)           f (a ∷ xs)       = loc g (λ zs → f (a ∷ zs)) xs

loc-ok : (g : Gen n) (f : Digits n → Q) (xs : Digits n) →
         loc g f xs ≡ app (ix (proj₂ ⟦ g ⟧₀)) f xs
loc-ok (gate₀ ν-gate) f xs =
  Eq.sym (Eq.trans (app-scal (x ^q 10) f xs) (r10-ok (f xs)))
loc-ok (gate₁ H-gate) f (a ∷ xs) = Eq.sym (begin
  app (ix (tenM (proj₂ Hᵍ) idM)) f (a ∷ xs)
    ≡⟨ app-emb₁ (proj₂ Hᵍ) f a xs ⟩
  Σ₁ (λ b → ix (proj₂ Hᵍ) (a ∷ []) (b ∷ []) * f (b ∷ xs))
    ≡⟨ Σ₁-cong (λ b → Eq.trans
         (Eq.cong (_* f (b ∷ xs)) (ix-matOf Hₒ (a ∷ []) (b ∷ [])))
         (*-assoc (x ^q 3) (ω^ (a ⊠ b)) (f (b ∷ xs)))) ⟩
  Σ₁ (λ b → x ^q 3 * (ω^ (a ⊠ b) * f (b ∷ xs)))
    ≡⟨ Σ₁-scaleˡ (x ^q 3) (λ b → ω^ (a ⊠ b) * f (b ∷ xs)) ⟩
  x ^q 3 * Σ₁ (λ b → ω^ (a ⊠ b) * f (b ∷ xs))
    ≡⟨ Eq.cong (x ^q 3 *_) (Σ₁-cong (λ b → rotω-ok (a ⊠ b) (f (b ∷ xs)))) ⟩
  x ^q 3 * Σ₁ (λ b → rotω (a ⊠ b) (f (b ∷ xs)))
    ≡⟨ r3-ok (Σ₁ (λ b → rotω (a ⊠ b) (f (b ∷ xs)))) ⟩
  loc (gate₁ H-gate) f (a ∷ xs) ∎)
loc-ok (gate₁ S-gate) f (a ∷ xs) = Eq.sym (begin
  app (ix (tenM (proj₂ Sᵍ) idM)) f (a ∷ xs)
    ≡⟨ app-emb₁ (proj₂ Sᵍ) f a xs ⟩
  Σ₁ (λ b → ix (proj₂ Sᵍ) (a ∷ []) (b ∷ []) * f (b ∷ xs))
    ≡⟨ Σ₁-cong (λ b → Eq.trans
         (Eq.cong (_* f (b ∷ xs)) (ix-matOf Sₒ (a ∷ []) (b ∷ [])))
         (*-assoc (δ₁ a b) (sph b) (f (b ∷ xs)))) ⟩
  Σ₁ (λ b → δ₁ a b * (sph b * f (b ∷ xs)))
    ≡⟨ Σ₁-δˡ a (λ b → sph b * f (b ∷ xs)) ⟩
  sph a * f (a ∷ xs)
    ≡⟨ rotS-ok a (f (a ∷ xs)) ⟩
  loc (gate₁ S-gate) f (a ∷ xs) ∎)
loc-ok (gate₂ CZ-gate) f (a ∷ a' ∷ xs) = Eq.sym (begin
  app (ix (tenM (proj₂ CZᵍ) idM)) f (a ∷ a' ∷ xs)
    ≡⟨ app-emb₂ (proj₂ CZᵍ) f a a' xs ⟩
  Σ₁ (λ b → Σ₁ (λ b' → ix (proj₂ CZᵍ) (a ∷ a' ∷ []) (b ∷ b' ∷ []) * f (b ∷ b' ∷ xs)))
    ≡⟨ Σ₁-cong (λ b → Σ₁-cong (λ b' → Eq.trans
         (Eq.cong (_* f (b ∷ b' ∷ xs)) (ix-matOf CZₒ (a ∷ a' ∷ []) (b ∷ b' ∷ [])))
         (regroup (δ₁ a b) (δ₁ a' b') (ω^ (b ⊠ b')) (f (b ∷ b' ∷ xs))))) ⟩
  Σ₁ (λ b → Σ₁ (λ b' → δ₁ a b * (δ₁ a' b' * (ω^ (b ⊠ b') * f (b ∷ b' ∷ xs)))))
    ≡⟨ Σ₁-cong (λ b → Σ₁-scaleˡ (δ₁ a b) (λ b' → δ₁ a' b' * (ω^ (b ⊠ b') * f (b ∷ b' ∷ xs)))) ⟩
  Σ₁ (λ b → δ₁ a b * Σ₁ (λ b' → δ₁ a' b' * (ω^ (b ⊠ b') * f (b ∷ b' ∷ xs))))
    ≡⟨ Σ₁-δˡ a (λ b → Σ₁ (λ b' → δ₁ a' b' * (ω^ (b ⊠ b') * f (b ∷ b' ∷ xs)))) ⟩
  Σ₁ (λ b' → δ₁ a' b' * (ω^ (a ⊠ b') * f (a ∷ b' ∷ xs)))
    ≡⟨ Σ₁-δˡ a' (λ b' → ω^ (a ⊠ b') * f (a ∷ b' ∷ xs)) ⟩
  ω^ (a ⊠ a') * f (a ∷ a' ∷ xs)
    ≡⟨ rotω-ok (a ⊠ a') (f (a ∷ a' ∷ xs)) ⟩
  loc (gate₂ CZ-gate) f (a ∷ a' ∷ xs) ∎)
  where
  regroup : (d d' w c : Q) → (d * (d' * w)) * c ≡ d * (d' * (w * c))
  regroup d d' w c = Eq.trans (*-assoc d (d' * w) c) (Eq.cong (d *_) (*-assoc d' w c))
loc-ok (g ↥) f (a ∷ xs) =
  Eq.trans (loc-ok g (λ zs → f (a ∷ zs)) xs) (Eq.sym (app-up (proj₂ ⟦ g ⟧₀) f a xs))

------------------------------------------------------------------------
-- Forcing

-- A natural number evaluated, and handed on as the literal it is: the
-- as-pattern binds the value matched.  Quartic.forceℕ hands on suc m
-- instead, which the builtin arithmetic does not take for a literal,
-- so that later sums and products of it are computed in unary — with
-- the entries of a three-qutrit word in the millions, gigabytes.
forceN : {B : Set} → ℕ → (ℕ → B) → B
forceN n@zero    k = k n
forceN n@(suc _) k = k n

forceN-id : {B : Set} (n : ℕ) (k : ℕ → B) → forceN n k ≡ k n
forceN-id zero    k = refl
forceN-id (suc n) k = refl

forceZ : {B : Set} → ℤ.ℤ → (ℤ.ℤ → B) → B
forceZ (+ n)      k = forceN n (λ m → k (+ m))
forceZ -[1+ n ]   k = forceN n (λ m → k -[1+ m ])

forceZ-id : {B : Set} (i : ℤ.ℤ) (k : ℤ.ℤ → B) → forceZ i k ≡ k i
forceZ-id (+ n)    k = forceN-id n (λ m → k (+ m))
forceZ-id -[1+ n ] k = forceN-id n (λ m → k -[1+ m ])

-- The four coefficients evaluated before the element is passed on.
forceQ : {B : Set} → Q → (Q → B) → B
forceQ ⟨ a , b , c , e ⟩ k =
  forceZ a λ a → forceZ b λ b → forceZ c λ c → forceZ e λ e → k ⟨ a , b , c , e ⟩

forceQ-id : {B : Set} (a : Q) (k : Q → B) → forceQ a k ≡ k a
forceQ-id ⟨ a , b , c , e ⟩ k =
  Eq.trans (forceZ-id a _) (Eq.trans (forceZ-id b _)
  (Eq.trans (forceZ-id c _) (forceZ-id e _)))

-- The product, its factors forced so.
mulF : Q → Q → Q
mulF a b = forceQ a λ a → forceQ b λ b → a *ₗ b

mulF-ok : (a b : Q) → mulF a b ≡ a * b
mulF-ok a b = Eq.trans (forceQ-id a (λ a → forceQ b λ b → a *ₗ b))
                (Eq.trans (forceQ-id b (λ b → a *ₗ b)) (Eq.sym (*≡*ₗ a b)))

------------------------------------------------------------------------
-- Tries of rows

-- A trie of 3ᵏ rows, each a trie of 3ᶜ entries.
Rows : ℕ → ℕ → Set
Rows k c = Tab k (Tab c Q)

rix : {c : ℕ} → Rows k c → Digits k → Digits c → Q
rix R xs ys = get (get R xs) ys

mapT : (k : ℕ) {A B : Set} → (A → B) → Tab k A → Tab k B
mapT zero    f a                   = f a
mapT (suc k) f (a₀ ∷ a₁ ∷ a₂ ∷ []) = mapT k f a₀ ∷ mapT k f a₁ ∷ mapT k f a₂ ∷ []

zip3T : (k : ℕ) {A B C D : Set} → (A → B → C → D) → Tab k A → Tab k B → Tab k C → Tab k D
zip3T zero    f a b c = f a b c
zip3T (suc k) f (a₀ ∷ a₁ ∷ a₂ ∷ []) (b₀ ∷ b₁ ∷ b₂ ∷ []) (c₀ ∷ c₁ ∷ c₂ ∷ []) =
  zip3T k f a₀ b₀ c₀ ∷ zip3T k f a₁ b₁ c₁ ∷ zip3T k f a₂ b₂ c₂ ∷ []

get-map : (k : ℕ) {A B : Set} (f : A → B) (t : Tab k A) (xs : Digits k) →
          get (mapT k f t) xs ≡ f (get t xs)
get-map zero    f t                   []                   = refl
get-map (suc k) f (a₀ ∷ a₁ ∷ a₂ ∷ []) (zero ∷ xs)          = get-map k f a₀ xs
get-map (suc k) f (a₀ ∷ a₁ ∷ a₂ ∷ []) (suc zero ∷ xs)      = get-map k f a₁ xs
get-map (suc k) f (a₀ ∷ a₁ ∷ a₂ ∷ []) (suc (suc zero) ∷ xs) = get-map k f a₂ xs

get-zip3 : (k : ℕ) {A B C D : Set} (f : A → B → C → D) (s : Tab k A) (t : Tab k B)
           (u : Tab k C) (xs : Digits k) →
           get (zip3T k f s t u) xs ≡ f (get s xs) (get t xs) (get u xs)
get-zip3 zero    f s t u [] = refl
get-zip3 (suc k) f (a₀ ∷ a₁ ∷ a₂ ∷ []) (b₀ ∷ b₁ ∷ b₂ ∷ []) (c₀ ∷ c₁ ∷ c₂ ∷ []) (zero ∷ xs) =
  get-zip3 k f a₀ b₀ c₀ xs
get-zip3 (suc k) f (a₀ ∷ a₁ ∷ a₂ ∷ []) (b₀ ∷ b₁ ∷ b₂ ∷ []) (c₀ ∷ c₁ ∷ c₂ ∷ []) (suc zero ∷ xs) =
  get-zip3 k f a₁ b₁ c₁ xs
get-zip3 (suc k) f (a₀ ∷ a₁ ∷ a₂ ∷ []) (b₀ ∷ b₁ ∷ b₂ ∷ []) (c₀ ∷ c₁ ∷ c₂ ∷ [])
         (suc (suc zero) ∷ xs) =
  get-zip3 k f a₂ b₂ c₂ xs

------------------------------------------------------------------------
-- The generators as row operations, every entry forced

-- An element with its coefficients evaluated.
strict : Q → Q
strict a = forceQ a (λ b → b)

strict-id : (a : Q) → strict a ≡ a
strict-id a = forceQ-id a (λ b → b)

-- A map of every entry of a trie of rows.
mapR : (k c : ℕ) → (Q → Q) → Rows k c → Rows k c
mapR k c f = mapT k (mapT c (λ a → strict (f a)))

rix-mapR : (k c : ℕ) (f : Q → Q) (R : Rows k c) (xs : Digits k) (ys : Digits c) →
           rix (mapR k c f R) xs ys ≡ f (rix R xs ys)
rix-mapR k c f R xs ys =
  Eq.trans (Eq.cong (λ t → get t ys) (get-map k (mapT c (λ a → strict (f a))) R xs))
    (Eq.trans (get-map c (λ a → strict (f a)) (get R xs) ys) (strict-id (f (rix R xs ys))))

-- The row a of H's image: r3 (Σ_b ω^{ab} row_b), as loc has it.
hrow : Fin 3 → Q → Q → Q → Q
hrow a p q r =
  r3 (rotω (a ⊠ zero) p + (rotω (a ⊠ suc zero) q + (rotω (a ⊠ suc (suc zero)) r + 0#)))

hR : (k c : ℕ) → Fin 3 → Rows k c → Rows k c → Rows k c → Rows k c
hR k c a = zip3T k (zip3T c (λ p q r → strict (hrow a p q r)))

rix-hR : (k c : ℕ) (a : Fin 3) (R₀ R₁ R₂ : Rows k c) (xs : Digits k) (ys : Digits c) →
         rix (hR k c a R₀ R₁ R₂) xs ys ≡ hrow a (rix R₀ xs ys) (rix R₁ xs ys) (rix R₂ xs ys)
rix-hR k c a R₀ R₁ R₂ xs ys =
  Eq.trans (Eq.cong (λ t → get t ys)
             (get-zip3 k (zip3T c (λ p q r → strict (hrow a p q r))) R₀ R₁ R₂ xs))
    (Eq.trans (get-zip3 c (λ p q r → strict (hrow a p q r)) (get R₀ xs) (get R₁ xs) (get R₂ xs) ys)
              (strict-id _))

applyR : (c : ℕ) → Gen k → Rows k c → Rows k c
applyR {k} c (gate₀ ν-gate) R = mapR k c (r10) R
applyR {suc k} c (gate₁ H-gate) (R₀ ∷ R₁ ∷ R₂ ∷ []) =
  hR k c zero R₀ R₁ R₂ ∷ hR k c (suc zero) R₀ R₁ R₂ ∷ hR k c (suc (suc zero)) R₀ R₁ R₂ ∷ []
applyR {suc k} c (gate₁ S-gate) (R₀ ∷ R₁ ∷ R₂ ∷ []) =
  mapR k c (r4) R₀ ∷ mapR k c (r4) R₁ ∷ R₂ ∷ []
applyR {suc (suc k)} c (gate₂ CZ-gate)
       ((R₀₀ ∷ R₀₁ ∷ R₀₂ ∷ []) ∷ (R₁₀ ∷ R₁₁ ∷ R₁₂ ∷ []) ∷ (R₂₀ ∷ R₂₁ ∷ R₂₂ ∷ []) ∷ []) =
    (R₀₀ ∷ R₀₁ ∷ R₀₂ ∷ [])
  ∷ (R₁₀ ∷ mapR k c (r4) R₁₁ ∷ mapR k c (r8) R₁₂ ∷ [])
  ∷ (R₂₀ ∷ mapR k c (r8) R₂₁ ∷ mapR k c (r4) R₂₂ ∷ [])
  ∷ []
applyR {suc k} c (g ↥) (R₀ ∷ R₁ ∷ R₂ ∷ []) =
  applyR c g R₀ ∷ applyR c g R₁ ∷ applyR c g R₂ ∷ []

-- A generator's row operation computes loc on every column.
applyR-ok : (c : ℕ) (g : Gen k) (R : Rows k c) (xs : Digits k) (ys : Digits c) →
            rix (applyR c g R) xs ys ≡ loc g (λ zs → rix R zs ys) xs
applyR-ok {k} c (gate₀ ν-gate) R xs ys = rix-mapR k c (r10) R xs ys
applyR-ok {suc k} c (gate₁ H-gate) (R₀ ∷ R₁ ∷ R₂ ∷ []) (zero ∷ xs) ys =
  rix-hR k c zero R₀ R₁ R₂ xs ys
applyR-ok {suc k} c (gate₁ H-gate) (R₀ ∷ R₁ ∷ R₂ ∷ []) (suc zero ∷ xs) ys =
  rix-hR k c (suc zero) R₀ R₁ R₂ xs ys
applyR-ok {suc k} c (gate₁ H-gate) (R₀ ∷ R₁ ∷ R₂ ∷ []) (suc (suc zero) ∷ xs) ys =
  rix-hR k c (suc (suc zero)) R₀ R₁ R₂ xs ys
applyR-ok {suc k} c (gate₁ S-gate) (R₀ ∷ R₁ ∷ R₂ ∷ []) (zero ∷ xs) ys =
  rix-mapR k c (r4) R₀ xs ys
applyR-ok {suc k} c (gate₁ S-gate) (R₀ ∷ R₁ ∷ R₂ ∷ []) (suc zero ∷ xs) ys =
  rix-mapR k c (r4) R₁ xs ys
applyR-ok {suc k} c (gate₁ S-gate) (R₀ ∷ R₁ ∷ R₂ ∷ []) (suc (suc zero) ∷ xs) ys = refl
applyR-ok {suc (suc k)} c (gate₂ CZ-gate)
  ((R₀₀ ∷ R₀₁ ∷ R₀₂ ∷ []) ∷ (R₁₀ ∷ R₁₁ ∷ R₁₂ ∷ []) ∷ (R₂₀ ∷ R₂₁ ∷ R₂₂ ∷ []) ∷ [])
  (zero ∷ zero ∷ xs) ys =
  refl
applyR-ok {suc (suc k)} c (gate₂ CZ-gate)
  ((R₀₀ ∷ R₀₁ ∷ R₀₂ ∷ []) ∷ (R₁₀ ∷ R₁₁ ∷ R₁₂ ∷ []) ∷ (R₂₀ ∷ R₂₁ ∷ R₂₂ ∷ []) ∷ [])
  (zero ∷ suc zero ∷ xs) ys =
  refl
applyR-ok {suc (suc k)} c (gate₂ CZ-gate)
  ((R₀₀ ∷ R₀₁ ∷ R₀₂ ∷ []) ∷ (R₁₀ ∷ R₁₁ ∷ R₁₂ ∷ []) ∷ (R₂₀ ∷ R₂₁ ∷ R₂₂ ∷ []) ∷ [])
  (zero ∷ suc (suc zero) ∷ xs) ys =
  refl
applyR-ok {suc (suc k)} c (gate₂ CZ-gate)
  ((R₀₀ ∷ R₀₁ ∷ R₀₂ ∷ []) ∷ (R₁₀ ∷ R₁₁ ∷ R₁₂ ∷ []) ∷ (R₂₀ ∷ R₂₁ ∷ R₂₂ ∷ []) ∷ [])
  (suc zero ∷ zero ∷ xs) ys =
  refl
applyR-ok {suc (suc k)} c (gate₂ CZ-gate)
  ((R₀₀ ∷ R₀₁ ∷ R₀₂ ∷ []) ∷ (R₁₀ ∷ R₁₁ ∷ R₁₂ ∷ []) ∷ (R₂₀ ∷ R₂₁ ∷ R₂₂ ∷ []) ∷ [])
  (suc zero ∷ suc zero ∷ xs) ys =
  rix-mapR k c (r4) R₁₁ xs ys
applyR-ok {suc (suc k)} c (gate₂ CZ-gate)
  ((R₀₀ ∷ R₀₁ ∷ R₀₂ ∷ []) ∷ (R₁₀ ∷ R₁₁ ∷ R₁₂ ∷ []) ∷ (R₂₀ ∷ R₂₁ ∷ R₂₂ ∷ []) ∷ [])
  (suc zero ∷ suc (suc zero) ∷ xs) ys =
  rix-mapR k c (r8) R₁₂ xs ys
applyR-ok {suc (suc k)} c (gate₂ CZ-gate)
  ((R₀₀ ∷ R₀₁ ∷ R₀₂ ∷ []) ∷ (R₁₀ ∷ R₁₁ ∷ R₁₂ ∷ []) ∷ (R₂₀ ∷ R₂₁ ∷ R₂₂ ∷ []) ∷ [])
  (suc (suc zero) ∷ zero ∷ xs) ys =
  refl
applyR-ok {suc (suc k)} c (gate₂ CZ-gate)
  ((R₀₀ ∷ R₀₁ ∷ R₀₂ ∷ []) ∷ (R₁₀ ∷ R₁₁ ∷ R₁₂ ∷ []) ∷ (R₂₀ ∷ R₂₁ ∷ R₂₂ ∷ []) ∷ [])
  (suc (suc zero) ∷ suc zero ∷ xs) ys =
  rix-mapR k c (r8) R₂₁ xs ys
applyR-ok {suc (suc k)} c (gate₂ CZ-gate)
  ((R₀₀ ∷ R₀₁ ∷ R₀₂ ∷ []) ∷ (R₁₀ ∷ R₁₁ ∷ R₁₂ ∷ []) ∷ (R₂₀ ∷ R₂₁ ∷ R₂₂ ∷ []) ∷ [])
  (suc (suc zero) ∷ suc (suc zero) ∷ xs) ys =
  rix-mapR k c (r4) R₂₂ xs ys
applyR-ok {suc k} c (g ↥) (R₀ ∷ R₁ ∷ R₂ ∷ []) (zero ∷ xs) ys = applyR-ok c g R₀ xs ys
applyR-ok {suc k} c (g ↥) (R₀ ∷ R₁ ∷ R₂ ∷ []) (suc zero ∷ xs) ys = applyR-ok c g R₁ xs ys
applyR-ok {suc k} c (g ↥) (R₀ ∷ R₁ ∷ R₂ ∷ []) (suc (suc zero) ∷ xs) ys = applyR-ok c g R₂ xs ys

-- A word, from the right: run c w R is ⟦ w ⟧ R.
run : (c : ℕ) → Circuit k → Rows k c → Rows k c
run c [ g ]ʷ  R = applyR c g R
run c ε       R = R
run c (w • u) R = run c w (run c u R)

run-ok : (c : ℕ) (w : Circuit k) (R : Rows k c) (xs : Digits k) (ys : Digits c) →
         rix (run c w R) xs ys ≡ app (ix (proj₂ ⟦ w ⟧)) (λ zs → rix R zs ys) xs
run-ok c [ g ]ʷ R xs ys =
  Eq.trans (applyR-ok c g R xs ys) (loc-ok g (λ zs → rix R zs ys) xs)
run-ok c ε R xs ys = Eq.sym (app-id (λ zs → rix R zs ys) xs)
run-ok c (w • u) R xs ys = begin
  rix (run c w (run c u R)) xs ys
    ≡⟨ run-ok c w (run c u R) xs ys ⟩
  app (ix Mw) (λ zs → rix (run c u R) zs ys) xs
    ≡⟨ app-congᶠ (ix Mw) (λ zs → run-ok c u R zs ys) xs ⟩
  app (ix Mw) (app (ix Mu) (λ zs → rix R zs ys)) xs
    ≡⟨ app-⊙ (ix Mw) (ix Mu) (λ zs → rix R zs ys) xs ⟩
  app (ix Mw ⊙ ix Mu) (λ zs → rix R zs ys) xs
    ≡⟨ app-cong (≐-sym (ix-mul Mw Mu)) (λ zs → rix R zs ys) xs ⟩
  app (ix (mulM Mw Mu)) (λ zs → rix R zs ys) xs ∎
  where
  Mw = proj₂ ⟦ w ⟧
  Mu = proj₂ ⟦ u ⟧

-- The reading: the row operations of w applied to the identity.
⟦_⟧R : Circuit k → Mat k
⟦_⟧R {k} w = mat (run k w (entries (idM {k})))

⟦⟧R-ok : (w : Circuit k) → ix ⟦ w ⟧R ≐ ix (proj₂ ⟦ w ⟧)
⟦⟧R-ok {k} w xs ys = begin
  rix (run k w (entries (idM {k}))) xs ys
    ≡⟨ run-ok k w (entries (idM {k})) xs ys ⟩
  app (ix M) (λ zs → ix (idM {k}) zs ys) xs
    ≡⟨ app-congᶠ (ix M) (λ zs → ix-id {k} zs ys) xs ⟩
  Σv (λ z → ix M xs z * δv z ys)
    ≡⟨ Σ-δʳ ys (ix M xs) ⟩
  ix M xs ys ∎
  where M = proj₂ ⟦ w ⟧

ev : Circuit k → Sc k
ev w = proj₁ ⟦ w ⟧ , ⟦ w ⟧R

ev-≈ : (w : Circuit k) → ev w ≈ ⟦ w ⟧
ev-≈ w = ≐→≈ {s = ev w} {⟦ w ⟧} refl (⟦⟧R-ok w)

------------------------------------------------------------------------
-- Two H on one wire at once

-- Two H on one wire are −3 times the permutation |j⟩ ↦ |−j⟩ (at the
-- scale of two H): the row a of their image is −3 times the row −a.
-- Half the H in the words that the box relations evaluate come in such
-- pairs, and H is the costliest letter, so runL takes two at a time.
m3 : Q → Q
m3 ⟨ a , b , c , e ⟩ =
  ⟨ -[1+ 2 ] ℤ.* a , -[1+ 2 ] ℤ.* b , -[1+ 2 ] ℤ.* c , -[1+ 2 ] ℤ.* e ⟩

-- The row −a of p q r.
sel : Fin 3 → Q → Q → Q → Q
sel zero             p q r = p
sel (suc zero)       p q r = r
sel (suc (suc zero)) p q r = q

private
  -- hrow over any operations, so that the solver can read its
  -- coefficients: at the polynomials, ⟦_⟧ of it is what hrow computes
  -- on ⟨ … ⟩.
  module Lin {A : Set} (_⊕_ : A → A → A) (⊖_ : A → A) (o : A) where

    r3ᴬ r4ᴬ r8ᴬ : Q⁴ A → Q⁴ A
    r3ᴬ (a , b , c , e) = ⊖ (b ⊕ e) , ⊖ c , b , a ⊕ c
    r4ᴬ (a , b , c , e) = ⊖ (a ⊕ c) , ⊖ (b ⊕ e) , a , b
    r8ᴬ (a , b , c , e) = c , e , ⊖ (a ⊕ c) , ⊖ (b ⊕ e)

    rotᴬ : Fin 3 → Q⁴ A → Q⁴ A
    rotᴬ zero             v = v
    rotᴬ (suc zero)       v = r4ᴬ v
    rotᴬ (suc (suc zero)) v = r8ᴬ v

    addᴬ : Q⁴ A → Q⁴ A → Q⁴ A
    addᴬ (a₀ , a₁ , a₂ , a₃) (b₀ , b₁ , b₂ , b₃) = a₀ ⊕ b₀ , a₁ ⊕ b₁ , a₂ ⊕ b₂ , a₃ ⊕ b₃

    hrowᴬ : Fin 3 → Q⁴ A → Q⁴ A → Q⁴ A → Q⁴ A
    hrowᴬ a p q r = r3ᴬ (addᴬ (rotᴬ (a ⊠ zero) p) (addᴬ (rotᴬ (a ⊠ suc zero) q)
                      (addᴬ (rotᴬ (a ⊠ suc (suc zero)) r) (o , o , o , o))))

    hhᴬ : Fin 3 → Q⁴ A → Q⁴ A → Q⁴ A → Q⁴ A
    hhᴬ a p q r = hrowᴬ a (hrowᴬ zero p q r) (hrowᴬ (suc zero) p q r) (hrowᴬ (suc (suc zero)) p q r)

  module LP {m : ℕ} = Lin (_:+_ {m}) :-_ (con (+ 0))

hh-ok : (a : Fin 3) (p q r : Q) →
        hrow a (hrow zero p q r) (hrow (suc zero) p q r) (hrow (suc (suc zero)) p q r) ≡
        m3 (sel a p q r)
hh-ok zero ⟨ p₀ , p₁ , p₂ , p₃ ⟩ ⟨ q₀ , q₁ , q₂ , q₃ ⟩ ⟨ r₀ , r₁ , r₂ , r₃ ⟩ = ⟨≡⟩
    (solve 12 (λ p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ r₀ r₁ r₂ r₃ →
       π₀ (LP.hhᴬ zero (p₀ , p₁ , p₂ , p₃) (q₀ , q₁ , q₂ , q₃) (r₀ , r₁ , r₂ , r₃))
         := con -[1+ 2 ] :* p₀) refl p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ r₀ r₁ r₂ r₃)
    (solve 12 (λ p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ r₀ r₁ r₂ r₃ →
       π₁ (LP.hhᴬ zero (p₀ , p₁ , p₂ , p₃) (q₀ , q₁ , q₂ , q₃) (r₀ , r₁ , r₂ , r₃))
         := con -[1+ 2 ] :* p₁) refl p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ r₀ r₁ r₂ r₃)
    (solve 12 (λ p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ r₀ r₁ r₂ r₃ →
       π₂ (LP.hhᴬ zero (p₀ , p₁ , p₂ , p₃) (q₀ , q₁ , q₂ , q₃) (r₀ , r₁ , r₂ , r₃))
         := con -[1+ 2 ] :* p₂) refl p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ r₀ r₁ r₂ r₃)
    (solve 12 (λ p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ r₀ r₁ r₂ r₃ →
       π₃ (LP.hhᴬ zero (p₀ , p₁ , p₂ , p₃) (q₀ , q₁ , q₂ , q₃) (r₀ , r₁ , r₂ , r₃))
         := con -[1+ 2 ] :* p₃) refl p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ r₀ r₁ r₂ r₃)
hh-ok (suc zero) ⟨ p₀ , p₁ , p₂ , p₃ ⟩ ⟨ q₀ , q₁ , q₂ , q₃ ⟩ ⟨ r₀ , r₁ , r₂ , r₃ ⟩ = ⟨≡⟩
    (solve 12 (λ p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ r₀ r₁ r₂ r₃ →
       π₀ (LP.hhᴬ (suc zero) (p₀ , p₁ , p₂ , p₃) (q₀ , q₁ , q₂ , q₃) (r₀ , r₁ , r₂ , r₃))
         := con -[1+ 2 ] :* r₀) refl p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ r₀ r₁ r₂ r₃)
    (solve 12 (λ p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ r₀ r₁ r₂ r₃ →
       π₁ (LP.hhᴬ (suc zero) (p₀ , p₁ , p₂ , p₃) (q₀ , q₁ , q₂ , q₃) (r₀ , r₁ , r₂ , r₃))
         := con -[1+ 2 ] :* r₁) refl p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ r₀ r₁ r₂ r₃)
    (solve 12 (λ p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ r₀ r₁ r₂ r₃ →
       π₂ (LP.hhᴬ (suc zero) (p₀ , p₁ , p₂ , p₃) (q₀ , q₁ , q₂ , q₃) (r₀ , r₁ , r₂ , r₃))
         := con -[1+ 2 ] :* r₂) refl p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ r₀ r₁ r₂ r₃)
    (solve 12 (λ p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ r₀ r₁ r₂ r₃ →
       π₃ (LP.hhᴬ (suc zero) (p₀ , p₁ , p₂ , p₃) (q₀ , q₁ , q₂ , q₃) (r₀ , r₁ , r₂ , r₃))
         := con -[1+ 2 ] :* r₃) refl p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ r₀ r₁ r₂ r₃)
hh-ok (suc (suc zero)) ⟨ p₀ , p₁ , p₂ , p₃ ⟩ ⟨ q₀ , q₁ , q₂ , q₃ ⟩ ⟨ r₀ , r₁ , r₂ , r₃ ⟩ = ⟨≡⟩
    (solve 12 (λ p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ r₀ r₁ r₂ r₃ →
       π₀ (LP.hhᴬ (suc (suc zero)) (p₀ , p₁ , p₂ , p₃) (q₀ , q₁ , q₂ , q₃) (r₀ , r₁ , r₂ , r₃))
         := con -[1+ 2 ] :* q₀) refl p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ r₀ r₁ r₂ r₃)
    (solve 12 (λ p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ r₀ r₁ r₂ r₃ →
       π₁ (LP.hhᴬ (suc (suc zero)) (p₀ , p₁ , p₂ , p₃) (q₀ , q₁ , q₂ , q₃) (r₀ , r₁ , r₂ , r₃))
         := con -[1+ 2 ] :* q₁) refl p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ r₀ r₁ r₂ r₃)
    (solve 12 (λ p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ r₀ r₁ r₂ r₃ →
       π₂ (LP.hhᴬ (suc (suc zero)) (p₀ , p₁ , p₂ , p₃) (q₀ , q₁ , q₂ , q₃) (r₀ , r₁ , r₂ , r₃))
         := con -[1+ 2 ] :* q₂) refl p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ r₀ r₁ r₂ r₃)
    (solve 12 (λ p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ r₀ r₁ r₂ r₃ →
       π₃ (LP.hhᴬ (suc (suc zero)) (p₀ , p₁ , p₂ , p₃) (q₀ , q₁ , q₂ , q₃) (r₀ , r₁ , r₂ , r₃))
         := con -[1+ 2 ] :* q₃) refl p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ r₀ r₁ r₂ r₃)

private
  -- The entry of the row a of H's image of H's image of R₀ R₁ R₂.
  hh-at : (k c : ℕ) (a : Fin 3) (R₀ R₁ R₂ : Rows k c) (xs : Digits k) (ys : Digits c) →
          m3 (sel a (rix R₀ xs ys) (rix R₁ xs ys) (rix R₂ xs ys)) ≡
          rix (hR k c a (hR k c zero R₀ R₁ R₂) (hR k c (suc zero) R₀ R₁ R₂)
                        (hR k c (suc (suc zero)) R₀ R₁ R₂)) xs ys
  hh-at k c a R₀ R₁ R₂ xs ys = Eq.sym (Eq.trans (rix-hR k c a S₀ S₁ S₂ xs ys)
    (Eq.trans (Eq.cong₂ (λ u v → hrow a u v (rix S₂ xs ys)) (rix-hR k c zero R₀ R₁ R₂ xs ys)
                 (rix-hR k c (suc zero) R₀ R₁ R₂ xs ys))
       (Eq.trans (Eq.cong (hrow a (hrow zero p q r) (hrow (suc zero) p q r))
                    (rix-hR k c (suc (suc zero)) R₀ R₁ R₂ xs ys))
          (hh-ok a p q r))))
    where
    S₀ = hR k c zero R₀ R₁ R₂
    S₁ = hR k c (suc zero) R₀ R₁ R₂
    S₂ = hR k c (suc (suc zero)) R₀ R₁ R₂
    p = rix R₀ xs ys
    q = rix R₁ xs ys
    r = rix R₂ xs ys

-- Two applications of a generator; for H, the rows exchanged and scaled.
applyR2 : (c : ℕ) → Gen k → Rows k c → Rows k c
applyR2 {suc k} c (gate₁ H-gate) (R₀ ∷ R₁ ∷ R₂ ∷ []) =
  mapR k c m3 R₀ ∷ mapR k c m3 R₂ ∷ mapR k c m3 R₁ ∷ []
applyR2 {suc k} c (g ↥) (R₀ ∷ R₁ ∷ R₂ ∷ []) =
  applyR2 c g R₀ ∷ applyR2 c g R₁ ∷ applyR2 c g R₂ ∷ []
applyR2 c g R = applyR c g (applyR c g R)

applyR2-ok : (c : ℕ) (g : Gen k) (R : Rows k c) (xs : Digits k) (ys : Digits c) →
             rix (applyR2 c g R) xs ys ≡ rix (applyR c g (applyR c g R)) xs ys
applyR2-ok {suc k} c (gate₁ H-gate) (R₀ ∷ R₁ ∷ R₂ ∷ []) (zero ∷ xs) ys =
  Eq.trans (rix-mapR k c m3 R₀ xs ys) (hh-at k c zero R₀ R₁ R₂ xs ys)
applyR2-ok {suc k} c (gate₁ H-gate) (R₀ ∷ R₁ ∷ R₂ ∷ []) (suc zero ∷ xs) ys =
  Eq.trans (rix-mapR k c m3 R₂ xs ys) (hh-at k c (suc zero) R₀ R₁ R₂ xs ys)
applyR2-ok {suc k} c (gate₁ H-gate) (R₀ ∷ R₁ ∷ R₂ ∷ []) (suc (suc zero) ∷ xs) ys =
  Eq.trans (rix-mapR k c m3 R₁ xs ys) (hh-at k c (suc (suc zero)) R₀ R₁ R₂ xs ys)
applyR2-ok {suc k} c (g ↥) (R₀ ∷ R₁ ∷ R₂ ∷ []) (zero ∷ xs) ys = applyR2-ok c g R₀ xs ys
applyR2-ok {suc k} c (g ↥) (R₀ ∷ R₁ ∷ R₂ ∷ []) (suc zero ∷ xs) ys = applyR2-ok c g R₁ xs ys
applyR2-ok {suc k} c (g ↥) (R₀ ∷ R₁ ∷ R₂ ∷ []) (suc (suc zero) ∷ xs) ys = applyR2-ok c g R₂ xs ys
applyR2-ok {zero} c (gate₀ ν-gate) R xs ys = refl
applyR2-ok {suc k} c (gate₀ ν-gate) R xs ys = refl
applyR2-ok {suc k} c (gate₁ S-gate) R xs ys = refl
applyR2-ok {suc (suc k)} c (gate₂ CZ-gate) R xs ys = refl

-- A generator's row operation respects the entries it is applied to.
applyR-cong : (c : ℕ) (g : Gen k) {A B : Rows k c} (ys : Digits c) →
              (∀ zs → rix A zs ys ≡ rix B zs ys) →
              (xs : Digits k) → rix (applyR c g A) xs ys ≡ rix (applyR c g B) xs ys
applyR-cong c g {A} {B} ys e xs =
  Eq.trans (applyR-ok c g A xs ys) (Eq.trans (loc-ok g (λ zs → rix A zs ys) xs)
    (Eq.trans (app-congᶠ (ix (proj₂ ⟦ g ⟧₀)) e xs)
      (Eq.sym (Eq.trans (applyR-ok c g B xs ys) (loc-ok g (λ zs → rix B zs ys) xs)))))

-- A list of letters as a word, in operator order (the head acts last):
-- Presentation.Tactics.Words.Associative.word-of-list, which this
-- module, being --cubical-compatible, cannot import.
wordL : List.List (Gen k) → Circuit k
wordL List.[]       = ε
wordL (g List.∷ gs) = [ g ]ʷ • wordL gs

-- The same H twice.
pairH : Gen k → Gen k → Bool
pairH (gate₁ H-gate) (gate₁ H-gate) = true
pairH (g ↥)          (g' ↥)         = pairH g g'
pairH _              _              = false

pairH-≡ : (g g' : Gen k) → pairH g g' ≡ true → g' ≡ g
pairH-≡ (gate₁ H-gate) (gate₁ H-gate) _ = refl
pairH-≡ (g ↥)          (g' ↥)         e = Eq.cong _↥ (pairH-≡ g g' e)
pairH-≡ (gate₀ ν-gate)  g'            ()
pairH-≡ (gate₁ S-gate)  g'            ()
pairH-≡ (gate₂ CZ-gate) g'            ()
pairH-≡ (gate₁ H-gate) (gate₀ ν-gate)  ()
pairH-≡ (gate₁ H-gate) (gate₁ S-gate)  ()
pairH-≡ (gate₁ H-gate) (gate₂ CZ-gate) ()
pairH-≡ (gate₁ H-gate) (g' ↥)          ()
pairH-≡ (g ↥)          (gate₀ ν-gate)  ()
pairH-≡ (g ↥)          (gate₁ H-gate)  ()
pairH-≡ (g ↥)          (gate₁ S-gate)  ()
pairH-≡ (g ↥)          (gate₂ CZ-gate) ()

-- A list of letters, in operator order, the same H twice in one step.
runL : (c : ℕ) → List.List (Gen k) → Rows k c → Rows k c
runL c List.[]                         R = R
runL c (g List.∷ List.[])              R = applyR c g R
runL c (g List.∷ gs@(g' List.∷ hs))    R =
  if pairH g g' then applyR2 c g (runL c hs R) else applyR c g (runL c gs R)

-- A step of runL, the soundness of the rest given.
runL-step : (c : ℕ) (g g' : Gen k) (hs : List.List (Gen k)) (R : Rows k c) (xs : Digits k) (ys : Digits c) →
            (∀ zs → rix (runL c hs R) zs ys ≡ rix (run c (wordL hs) R) zs ys) →
            (∀ zs → rix (runL c (g' List.∷ hs) R) zs ys ≡ rix (run c (wordL (g' List.∷ hs)) R) zs ys) →
            rix (runL c (g List.∷ g' List.∷ hs) R) xs ys ≡ rix (run c (wordL (g List.∷ g' List.∷ hs)) R) xs ys
runL-step c g g' hs R xs ys ih₂ ih₁ with pairH g g' in e
... | true  = Eq.trans (applyR2-ok c g (runL c hs R) xs ys)
               (applyR-cong c g ys (λ zs → Eq.trans (applyR-cong c g ys ih₂ zs)
                                          (Eq.cong (λ h → rix (applyR c h (run c (wordL hs) R)) zs ys)
                                                   (Eq.sym (pairH-≡ g g' e))))
                 xs)
... | false = applyR-cong c g ys ih₁ xs

runL-ok : (c : ℕ) (gs : List.List (Gen k)) (R : Rows k c) (xs : Digits k) (ys : Digits c) →
          rix (runL c gs R) xs ys ≡ rix (run c (wordL gs) R) xs ys
runL-ok c List.[]                      R xs ys = refl
runL-ok c (g List.∷ List.[])           R xs ys = refl
runL-ok c (g List.∷ gs@(g' List.∷ hs)) R xs ys =
  runL-step c g g' hs R xs ys (λ zs → runL-ok c hs R zs ys) (λ zs → runL-ok c gs R zs ys)

⟦_⟧L : List.List (Gen k) → Mat k
⟦_⟧L {k} gs = mat (runL k gs (entries (idM {k})))

⟦⟧L-ok : (gs : List.List (Gen k)) → ix ⟦ gs ⟧L ≐ ix (proj₂ ⟦ wordL gs ⟧)
⟦⟧L-ok {k} gs xs ys = Eq.trans (runL-ok k gs (entries (idM {k})) xs ys) (⟦⟧R-ok (wordL gs) xs ys)

-- The value of a list of letters, by runL.
evL : List.List (Gen k) → Sc k
evL gs = proj₁ ⟦ wordL gs ⟧ , ⟦ gs ⟧L

evL-≈ : (gs : List.List (Gen k)) → evL gs ≈ ⟦ wordL gs ⟧
evL-≈ gs = ≐→≈ {s = evL gs} {⟦ wordL gs ⟧} refl (⟦⟧L-ok gs)

------------------------------------------------------------------------
-- Exact comparison

-- Equality of elements as a Boolean on the builtin equality of natural
-- numbers.  Quartic._≟_ would do, but its with-clauses match on yes refl,
-- which evaluates the proof of each equation — a recursion as deep as the
-- integers, which reach millions here.
eqℤ : ℤ.ℤ → ℤ.ℤ → Bool
eqℤ (+ m)    (+ n)    = m ℕ.≡ᵇ n
eqℤ -[1+ m ] -[1+ n ] = m ℕ.≡ᵇ n
eqℤ _        _        = false

eqℤ-sound : (i j : ℤ.ℤ) → T (eqℤ i j) → i ≡ j
eqℤ-sound (+ m)    (+ n)    t = Eq.cong +_ (ℕP.≡ᵇ⇒≡ m n t)
eqℤ-sound -[1+ m ] -[1+ n ] t = Eq.cong -[1+_] (ℕP.≡ᵇ⇒≡ m n t)

eqQ : Q → Q → Bool
eqQ ⟨ a₀ , a₁ , a₂ , a₃ ⟩ ⟨ b₀ , b₁ , b₂ , b₃ ⟩ =
  eqℤ a₀ b₀ ∧ eqℤ a₁ b₁ ∧ eqℤ a₂ b₂ ∧ eqℤ a₃ b₃

private
  ∧-l : ∀ {x y} → T (x ∧ y) → T x
  ∧-l {true} _ = tt

  ∧-r : ∀ {x y} → T (x ∧ y) → T y
  ∧-r {true} t = t

eqQ-sound : (a b : Q) → T (eqQ a b) → a ≡ b
eqQ-sound ⟨ a₀ , a₁ , a₂ , a₃ ⟩ ⟨ b₀ , b₁ , b₂ , b₃ ⟩ t =
  ⟨≡⟩ (eqℤ-sound a₀ b₀ (∧-l t)) (eqℤ-sound a₁ b₁ (∧-l (∧-r {eqℤ a₀ b₀} t)))
      (eqℤ-sound a₂ b₂ (∧-l (∧-r {eqℤ a₁ b₁} (∧-r {eqℤ a₀ b₀} t))))
      (eqℤ-sound a₃ b₃ (∧-r {eqℤ a₂ b₂} (∧-r {eqℤ a₁ b₁} (∧-r {eqℤ a₀ b₀} t))))

-- r^{h'} M = r^h M' entry by entry, the two powers of √3 computed once.
cmp : Q → Q → Mat n → Mat n → Bool
cmp {n} a b M M' = allD n λ i → allD n λ j → eqQ (mulF a (ix M i j)) (mulF b (ix M' i j))

-- The powers of √3, each multiplication forced.
pow3 : ℕ → Q
pow3 zero    = 1q
pow3 (suc h) = mulF √3 (pow3 h)

pow3-ok : (h : ℕ) → pow3 h ≡ √3 ^q h
pow3-ok zero    = refl
pow3-ok (suc h) = Eq.trans (mulF-ok √3 (pow3 h)) (Eq.cong (√3 *_) (pow3-ok h))

eqF : Sc n → Sc n → Bool
eqF (h , M) (h' , M') = forceQ (pow3 h') λ a → forceQ (pow3 h) λ b → cmp a b M M'

eqF-sound : (s s' : Sc n) → T (eqF s s') → s ≈ s'
eqF-sound {n} (h , M) (h' , M') t = phased 0 refl λ i j →
  Eq.trans (Eq.trans (Eq.cong (_* ix M i j) (Eq.sym (pow3-ok h'))) (Eq.sym (mulF-ok a (ix M i j))))
  (Eq.trans (eqQ-sound (mulF a (ix M i j)) (mulF b (ix M' i j))
               (allD-sound n (λ j → eqQ (mulF a (ix M i j)) (mulF b (ix M' i j)))
                 (allD-sound n (λ i → allD n λ j → eqQ (mulF a (ix M i j)) (mulF b (ix M' i j)))
                             t′ i) j))
  (Eq.trans (mulF-ok b (ix M' i j))
            (Eq.cong (_* ix M' i j) (Eq.trans (pow3-ok h) (Eq.sym (*-identityˡ (√3 ^q h)))))))
  where
  a = pow3 h'
  b = pow3 h
  t′ : T (cmp a b M M')
  t′ = Eq.subst T (Eq.trans (forceQ-id a (λ a → forceQ b λ b → cmp a b M M'))
                            (forceQ-id b (λ b → cmp a b M M'))) t

private
  ≈-trans' : {s₁ s₂ s₃ : Sc n} → s₁ ≈ s₂ → s₂ ≈ s₃ → s₁ ≈ s₃
  ≈-trans' {s₁ = s₁} {s₂} {s₃} = ≈-trans {s₁ = s₁} {s₂} {s₃}

  ≈-sym' : {s s' : Sc n} → s ≈ s' → s' ≈ s
  ≈-sym' {s = s} {s'} = ≈-sym {s = s} {s'}

-- An equation on its own wires, checked by evaluation.  State the check
-- for named words (Soundness.Checks): the type of the evidence is then
-- the very type expected here, where an implicit width elaborated as
-- 0 in one and as zero in the other makes the conversion checker
-- evaluate both Booleans again, slowly.
checked : (l r : Circuit k) → T (eqF (ev l) (ev r)) → ⟦ l ⟧ ≈ ⟦ r ⟧
checked l r t =
  ≈-trans' {s₁ = ⟦ l ⟧} {ev l} {⟦ r ⟧} (≈-sym' {s = ev l} {⟦ l ⟧} (ev-≈ l))
    (≈-trans' {s₁ = ev l} {ev r} {⟦ r ⟧} (eqF-sound (ev l) (ev r) t) (ev-≈ r))

-- The same for lists of letters, by evL.
checkedL : (l r : List.List (Gen k)) → T (eqF (evL l) (evL r)) →
           ⟦ wordL l ⟧ ≈ ⟦ wordL r ⟧
checkedL l r t =
  ≈-trans' {s₁ = ⟦ wordL l ⟧} {evL l} {⟦ wordL r ⟧}
    (≈-sym' {s = evL l} {⟦ wordL l ⟧} (evL-≈ l))
    (≈-trans' {s₁ = evL l} {evL r} {⟦ wordL r ⟧} (eqF-sound (evL l) (evL r) t) (evL-≈ r))

-- An equation on k wires, checked by evaluation, holds on the bottom k
-- wires of every wider circuit.
by-fast : (l r : Circuit k) {n : ℕ} {w v : Circuit (k +ℕ n)} →
          l ↓ᵏ n ≡ w → r ↓ᵏ n ≡ v → T (eqF (ev l) (ev r)) → ⟦ w ⟧ ≈ ⟦ v ⟧
by-fast l r el er t = lift l r el er (checked l r t)
