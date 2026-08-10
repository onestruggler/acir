------------------------------------------------------------------------
-- Presentations of groups
--
-- The Clifford group as automorphisms of P4 (p = 2), stage 2b: cact1 g is
-- a group homomorphism of P4.
--
-- cact1 g (s , P) = (s + δ g P , actg g P) is a homomorphism of P4 because
--   * actg g is additive on the Pauli part (Interpretation.actg-+), and
--   * δ g is a quadratic refinement of the symplectic form: its
--     polarisation matches the change of the commutation cocycle γ under
--     actg g (δ-coc).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.ProjectiveClifford.Qubit.CliffordAut where

open import Data.Nat using (ℕ)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import ForStdlib.Data.Fin.Mod

open import ForStdlib.Data.Fin.Mod.Prime.Two using (p-2 ; p-prime)

open PrimeModulus p-2 p-prime

open import Examples.Groups.ProjectivePauli.Semantics p-2 p-prime
  using (Pauli ; Pauli1 ; _+ₚ_ ; _+₁_ ; pIₙ)
import Examples.Groups.Symplectic.Semantics p-2 p-prime as SympSem
open SympSem.Interpretation using (actg ; actg-+)
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
  using (module Symplectic)
open Symplectic
  using (Gen ; gate₁ ; gate₂ ; H-gate ; S-gate ; CZ-gate ; _↥)


open import Examples.Groups.Pauli.Qubit.SignedPauli
  using (Φ ; P4Carrier ; β ; γ ; ι ; ι-+ ; _·_ ; +-swap-middle)
open import Examples.Groups.ProjectiveClifford.Qubit.CliffordAction using (δ ; incl ; cact1 ; cact)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- ℤ/4 helper identities (both moduli concrete, so mostly by computation)

-- ι has order ≤ 2 in ℤ/4.
ι-2 : (x : ℤ ₚ) → ι x + ι x ≡ ₀
ι-2 ₀ = auto
ι-2 ₁ = auto

-- incl is additive up to the ×2 image of the product.
incl-+ : (a c : ℤ ₚ) → incl a + incl c ≡ incl (a + c) + ι (a * c)
incl-+ ₀ ₀ = auto
incl-+ ₀ ₁ = auto
incl-+ ₁ ₀ = auto
incl-+ ₁ ₁ = auto

-- -x = x at p = 2.
neg-id : (x : ℤ ₚ) → - x ≡ x
neg-id ₀ = auto
neg-id ₁ = auto

-- γ on a cons cell splits off the head commutation b·c and the tail.
γ-cons : ∀ {m} (a b c d : ℤ ₚ) (t t' : Pauli m) →
         γ ((a , b) ∷ t) ((c , d) ∷ t') ≡ ι (b * c) + γ t t'
γ-cons a b c d t t' = ι-+ (b * c) (β t t')

-- Two generic ℤ/4 rearrangements, factoring a common tail term.
app-U : (A U D Y Z : Φ) → A + D ≡ Y + Z → (A + U) + D ≡ Y + (Z + U)
app-U A U D Y Z hyp = begin
  (A + U) + D   ≡⟨ +-assoc A U D ⟩
  A + (U + D)   ≡⟨ Eq.cong (A +_) (+-comm U D) ⟩
  A + (D + U)   ≡⟨ Eq.sym (+-assoc A D U) ⟩
  (A + D) + U   ≡⟨ Eq.cong (_+ U) hyp ⟩
  (Y + Z) + U   ≡⟨ +-assoc Y Z U ⟩
  Y + (Z + U)   ∎
  where open Eq.≡-Reasoning

pre-C : (C A D Y Z : Φ) → A + D ≡ Y + Z → (C + A) + D ≡ Y + (C + Z)
pre-C C A D Y Z hyp = begin
  (C + A) + D   ≡⟨ +-assoc C A D ⟩
  C + (A + D)   ≡⟨ Eq.cong (C +_) hyp ⟩
  C + (Y + Z)   ≡⟨ Eq.sym (+-assoc C Y Z) ⟩
  (C + Y) + Z   ≡⟨ Eq.cong (_+ Z) (+-comm C Y) ⟩
  (Y + C) + Z   ≡⟨ +-assoc Y C Z ⟩
  Y + (C + Z)   ∎
  where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- The head cocycle identity for the S gate (finite, by computation).

HEAD-S : (a b c : ℤ ₚ) →
  ι (b * c) + incl (a + c) ≡ (incl a + incl c) + ι ((b + a) * c)
HEAD-S ₀ ₀ ₀ = auto
HEAD-S ₀ ₀ ₁ = auto
HEAD-S ₀ ₁ ₀ = auto
HEAD-S ₀ ₁ ₁ = auto
HEAD-S ₁ ₀ ₀ = auto
HEAD-S ₁ ₀ ₁ = auto
HEAD-S ₁ ₁ ₀ = auto
HEAD-S ₁ ₁ ₁ = auto

-- The S-gate clause of δ-coc, stated with the definitional reductions of
-- δ and actg already applied.
δ-coc-S : ∀ {m} (a b c d : ℤ ₚ) (ps qs : Pauli m) →
  γ ((a , b) ∷ ps) ((c , d) ∷ qs) + incl (a + c) ≡
  (incl a + incl c) + γ ((a , b + a) ∷ ps) ((c , d + c) ∷ qs)
δ-coc-S a b c d ps qs = begin
  γ ((a , b) ∷ ps) ((c , d) ∷ qs) + incl (a + c)
    ≡⟨ Eq.cong (_+ incl (a + c)) (γ-cons a b c d ps qs) ⟩
  (ι (b * c) + γ ps qs) + incl (a + c)
    ≡⟨ app-U (ι (b * c)) (γ ps qs) (incl (a + c))
             (incl a + incl c) (ι ((b + a) * c)) (HEAD-S a b c) ⟩
  (incl a + incl c) + (ι ((b + a) * c) + γ ps qs)
    ≡⟨ Eq.cong ((incl a + incl c) +_)
               (Eq.sym (γ-cons a (b + a) c (d + c) ps qs)) ⟩
  (incl a + incl c) + γ ((a , b + a) ∷ ps) ((c , d + c) ∷ qs)  ∎
  where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- The remaining head identities and the full phase cocycle δ-coc

HEAD-H : (a b c d : ℤ ₚ) →
  ι (b * c) + ι ((a + c) * (b + d)) ≡
  (ι (a * b) + ι (c * d)) + ι (a * (- d))
HEAD-H ₀ ₀ ₀ ₀ = auto
HEAD-H ₀ ₀ ₀ ₁ = auto
HEAD-H ₀ ₀ ₁ ₀ = auto
HEAD-H ₀ ₀ ₁ ₁ = auto
HEAD-H ₀ ₁ ₀ ₀ = auto
HEAD-H ₀ ₁ ₀ ₁ = auto
HEAD-H ₀ ₁ ₁ ₀ = auto
HEAD-H ₀ ₁ ₁ ₁ = auto
HEAD-H ₁ ₀ ₀ ₀ = auto
HEAD-H ₁ ₀ ₀ ₁ = auto
HEAD-H ₁ ₀ ₁ ₀ = auto
HEAD-H ₁ ₀ ₁ ₁ = auto
HEAD-H ₁ ₁ ₀ ₀ = auto
HEAD-H ₁ ₁ ₀ ₁ = auto
HEAD-H ₁ ₁ ₁ ₀ = auto
HEAD-H ₁ ₁ ₁ ₁ = auto

-- γ on two cons cells.
γ-cons2 : ∀ {m} (a b a' b' c d c' d' : ℤ ₚ) (t t' : Pauli m) →
  γ ((a , b) ∷ (a' , b') ∷ t) ((c , d) ∷ (c' , d') ∷ t') ≡
  (ι (b * c) + ι (b' * c')) + γ t t'
γ-cons2 a b a' b' c d c' d' t t' = begin
  γ ((a , b) ∷ (a' , b') ∷ t) ((c , d) ∷ (c' , d') ∷ t')
    ≡⟨ γ-cons a b c d ((a' , b') ∷ t) ((c' , d') ∷ t') ⟩
  ι (b * c) + γ ((a' , b') ∷ t) ((c' , d') ∷ t')
    ≡⟨ Eq.cong (ι (b * c) +_) (γ-cons a' b' c' d' t t') ⟩
  ι (b * c) + (ι (b' * c') + γ t t')
    ≡⟨ Eq.sym (+-assoc (ι (b * c)) (ι (b' * c')) (γ t t')) ⟩
  (ι (b * c) + ι (b' * c')) + γ t t'  ∎
  where open Eq.≡-Reasoning

-- The two-qubit head identity for CZ (finite, by computation).
HEAD-CZ : (a b a' b' c c' : ℤ ₚ) →
  (ι (b * c) + ι (b' * c')) + ι ((a + c) * (a' + c')) ≡
  (ι (a * a') + ι (c * c')) +
  (ι ((b + a') * c) + ι ((b' + a) * c'))
HEAD-CZ ₀ ₀ ₀ ₀ ₀ ₀ = auto
HEAD-CZ ₀ ₀ ₀ ₀ ₀ ₁ = auto
HEAD-CZ ₀ ₀ ₀ ₀ ₁ ₀ = auto
HEAD-CZ ₀ ₀ ₀ ₀ ₁ ₁ = auto
HEAD-CZ ₀ ₀ ₀ ₁ ₀ ₀ = auto
HEAD-CZ ₀ ₀ ₀ ₁ ₀ ₁ = auto
HEAD-CZ ₀ ₀ ₀ ₁ ₁ ₀ = auto
HEAD-CZ ₀ ₀ ₀ ₁ ₁ ₁ = auto
HEAD-CZ ₀ ₀ ₁ ₀ ₀ ₀ = auto
HEAD-CZ ₀ ₀ ₁ ₀ ₀ ₁ = auto
HEAD-CZ ₀ ₀ ₁ ₀ ₁ ₀ = auto
HEAD-CZ ₀ ₀ ₁ ₀ ₁ ₁ = auto
HEAD-CZ ₀ ₀ ₁ ₁ ₀ ₀ = auto
HEAD-CZ ₀ ₀ ₁ ₁ ₀ ₁ = auto
HEAD-CZ ₀ ₀ ₁ ₁ ₁ ₀ = auto
HEAD-CZ ₀ ₀ ₁ ₁ ₁ ₁ = auto
HEAD-CZ ₀ ₁ ₀ ₀ ₀ ₀ = auto
HEAD-CZ ₀ ₁ ₀ ₀ ₀ ₁ = auto
HEAD-CZ ₀ ₁ ₀ ₀ ₁ ₀ = auto
HEAD-CZ ₀ ₁ ₀ ₀ ₁ ₁ = auto
HEAD-CZ ₀ ₁ ₀ ₁ ₀ ₀ = auto
HEAD-CZ ₀ ₁ ₀ ₁ ₀ ₁ = auto
HEAD-CZ ₀ ₁ ₀ ₁ ₁ ₀ = auto
HEAD-CZ ₀ ₁ ₀ ₁ ₁ ₁ = auto
HEAD-CZ ₀ ₁ ₁ ₀ ₀ ₀ = auto
HEAD-CZ ₀ ₁ ₁ ₀ ₀ ₁ = auto
HEAD-CZ ₀ ₁ ₁ ₀ ₁ ₀ = auto
HEAD-CZ ₀ ₁ ₁ ₀ ₁ ₁ = auto
HEAD-CZ ₀ ₁ ₁ ₁ ₀ ₀ = auto
HEAD-CZ ₀ ₁ ₁ ₁ ₀ ₁ = auto
HEAD-CZ ₀ ₁ ₁ ₁ ₁ ₀ = auto
HEAD-CZ ₀ ₁ ₁ ₁ ₁ ₁ = auto
HEAD-CZ ₁ ₀ ₀ ₀ ₀ ₀ = auto
HEAD-CZ ₁ ₀ ₀ ₀ ₀ ₁ = auto
HEAD-CZ ₁ ₀ ₀ ₀ ₁ ₀ = auto
HEAD-CZ ₁ ₀ ₀ ₀ ₁ ₁ = auto
HEAD-CZ ₁ ₀ ₀ ₁ ₀ ₀ = auto
HEAD-CZ ₁ ₀ ₀ ₁ ₀ ₁ = auto
HEAD-CZ ₁ ₀ ₀ ₁ ₁ ₀ = auto
HEAD-CZ ₁ ₀ ₀ ₁ ₁ ₁ = auto
HEAD-CZ ₁ ₀ ₁ ₀ ₀ ₀ = auto
HEAD-CZ ₁ ₀ ₁ ₀ ₀ ₁ = auto
HEAD-CZ ₁ ₀ ₁ ₀ ₁ ₀ = auto
HEAD-CZ ₁ ₀ ₁ ₀ ₁ ₁ = auto
HEAD-CZ ₁ ₀ ₁ ₁ ₀ ₀ = auto
HEAD-CZ ₁ ₀ ₁ ₁ ₀ ₁ = auto
HEAD-CZ ₁ ₀ ₁ ₁ ₁ ₀ = auto
HEAD-CZ ₁ ₀ ₁ ₁ ₁ ₁ = auto
HEAD-CZ ₁ ₁ ₀ ₀ ₀ ₀ = auto
HEAD-CZ ₁ ₁ ₀ ₀ ₀ ₁ = auto
HEAD-CZ ₁ ₁ ₀ ₀ ₁ ₀ = auto
HEAD-CZ ₁ ₁ ₀ ₀ ₁ ₁ = auto
HEAD-CZ ₁ ₁ ₀ ₁ ₀ ₀ = auto
HEAD-CZ ₁ ₁ ₀ ₁ ₀ ₁ = auto
HEAD-CZ ₁ ₁ ₀ ₁ ₁ ₀ = auto
HEAD-CZ ₁ ₁ ₀ ₁ ₁ ₁ = auto
HEAD-CZ ₁ ₁ ₁ ₀ ₀ ₀ = auto
HEAD-CZ ₁ ₁ ₁ ₀ ₀ ₁ = auto
HEAD-CZ ₁ ₁ ₁ ₀ ₁ ₀ = auto
HEAD-CZ ₁ ₁ ₁ ₀ ₁ ₁ = auto
HEAD-CZ ₁ ₁ ₁ ₁ ₀ ₀ = auto
HEAD-CZ ₁ ₁ ₁ ₁ ₀ ₁ = auto
HEAD-CZ ₁ ₁ ₁ ₁ ₁ ₀ = auto
HEAD-CZ ₁ ₁ ₁ ₁ ₁ ₁ = auto

sign-lemma : (s s' Dp Dp' A D W : Φ) → A + D ≡ (Dp + Dp') + W →
             (s + s' + A) + D ≡ ((s + Dp) + (s' + Dp')) + W
sign-lemma s s' Dp Dp' A D W hyp = begin
  (s + s' + A) + D       ≡⟨ +-assoc (s + s') A D ⟩
  (s + s') + (A + D)      ≡⟨ Eq.cong ((s + s') +_) hyp ⟩
  (s + s') + ((Dp + Dp') + W)  ≡⟨ Eq.sym (+-assoc (s + s') (Dp + Dp') W) ⟩
  ((s + s') + (Dp + Dp')) + W  ≡⟨ Eq.cong (_+ W) (+-swap-middle s s' Dp Dp') ⟩
  ((s + Dp) + (s' + Dp')) + W  ∎
  where open Eq.≡-Reasoning

------------------------------------------------------------------------
-- The phase cocycle and the homomorphism property of cact1

δ-coc : (g : Gen n) (P P' : Pauli n) →
  γ P P' + δ g (P +ₚ P') ≡ (δ g P + δ g P') + γ (actg g P) (actg g P')
δ-coc (gate₁ S-gate) ((a , b) ∷ ps) ((c , d) ∷ qs) = δ-coc-S a b c d ps qs
δ-coc (gate₁ H-gate) ((a , b) ∷ ps) ((c , d) ∷ qs) = begin
  γ ((a , b) ∷ ps) ((c , d) ∷ qs) + ι ((a + c) * (b + d))
    ≡⟨ Eq.cong (_+ ι ((a + c) * (b + d))) (γ-cons a b c d ps qs) ⟩
  (ι (b * c) + γ ps qs) + ι ((a + c) * (b + d))
    ≡⟨ app-U (ι (b * c)) (γ ps qs) (ι ((a + c) * (b + d)))
             (ι (a * b) + ι (c * d)) (ι (a * (- d))) (HEAD-H a b c d) ⟩
  (ι (a * b) + ι (c * d)) + (ι (a * (- d)) + γ ps qs)
    ≡⟨ Eq.cong ((ι (a * b) + ι (c * d)) +_)
               (Eq.sym (γ-cons (- b) a (- d) c ps qs)) ⟩
  (ι (a * b) + ι (c * d)) + γ ((- b , a) ∷ ps) ((- d , c) ∷ qs)  ∎
  where open Eq.≡-Reasoning
δ-coc (gate₂ CZ-gate) ((a , b) ∷ (a' , b') ∷ ps) ((c , d) ∷ (c' , d') ∷ qs) = begin
  γ ((a , b) ∷ (a' , b') ∷ ps) ((c , d) ∷ (c' , d') ∷ qs) + ι ((a + c) * (a' + c'))
    ≡⟨ Eq.cong (_+ ι ((a + c) * (a' + c'))) (γ-cons2 a b a' b' c d c' d' ps qs) ⟩
  ((ι (b * c) + ι (b' * c')) + γ ps qs) + ι ((a + c) * (a' + c'))
    ≡⟨ app-U (ι (b * c) + ι (b' * c')) (γ ps qs) (ι ((a + c) * (a' + c')))
             (ι (a * a') + ι (c * c'))
             (ι ((b + a') * c) + ι ((b' + a) * c')) (HEAD-CZ a b a' b' c c') ⟩
  (ι (a * a') + ι (c * c')) +
    ((ι ((b + a') * c) + ι ((b' + a) * c')) + γ ps qs)
    ≡⟨ Eq.cong ((ι (a * a') + ι (c * c')) +_)
               (Eq.sym (γ-cons2 a (b + a') a' (b' + a) c (d + c') c' (d' + c) ps qs)) ⟩
  (ι (a * a') + ι (c * c')) +
    γ ((a , b + a') ∷ (a' , b' + a) ∷ ps) ((c , d + c') ∷ (c' , d' + c) ∷ qs)  ∎
  where open Eq.≡-Reasoning
δ-coc (g ↥) ((a , b) ∷ ps) ((c , d) ∷ qs) = begin
  γ ((a , b) ∷ ps) ((c , d) ∷ qs) + δ g (ps +ₚ qs)
    ≡⟨ Eq.cong (_+ δ g (ps +ₚ qs)) (γ-cons a b c d ps qs) ⟩
  (ι (b * c) + γ ps qs) + δ g (ps +ₚ qs)
    ≡⟨ pre-C (ι (b * c)) (γ ps qs) (δ g (ps +ₚ qs)) (δ g ps + δ g qs)
             (γ (actg g ps) (actg g qs)) (δ-coc g ps qs) ⟩
  (δ g ps + δ g qs) + (ι (b * c) + γ (actg g ps) (actg g qs))
    ≡⟨ Eq.cong ((δ g ps + δ g qs) +_) (Eq.sym (γ-cons a b c d (actg g ps) (actg g qs))) ⟩
  (δ g ps + δ g qs) + γ ((a , b) ∷ actg g ps) ((c , d) ∷ actg g qs)  ∎
  where open Eq.≡-Reasoning

-- cact1 g is a homomorphism of P4: the Pauli part is actg-+, the phase part
-- is δ-coc packaged by sign-lemma.
cact1-homo : (g : Gen n) (x y : P4Carrier n) →
             cact1 g (x · y) ≡ cact1 g x · cact1 g y
cact1-homo g (s , P) (s' , P') =
  Eq.cong₂ _,_
    (sign-lemma s s' (δ g P) (δ g P') (γ P P') (δ g (P +ₚ P'))
                (γ (actg g P) (actg g P')) (δ-coc g P P'))
    (actg-+ g P P')

------------------------------------------------------------------------
-- cact of a whole Clifford word is a homomorphism of P4

cact-homo : (w : Word (Gen n)) (x y : P4Carrier n) →
            cact w (x · y) ≡ cact w x · cact w y
cact-homo [ g ]ʷ  x y = cact1-homo g x y
cact-homo ε       x y = Eq.refl
cact-homo (w • v) x y =
  Eq.trans (Eq.cong (cact w) (cact-homo v x y))
           (cact-homo w (cact v x) (cact v y))

------------------------------------------------------------------------
-- Each generator has P4-order dividing 4 (S⁴ = H⁴ = CZ⁴ = 1 on P4)

-- Reassociate a left-nested 4-fold phase sum and cancel it.
collapse4 : (s c0 c1 c2 c3 : Φ) → ((c0 + c1) + c2) + c3 ≡ ₀ →
            (((s + c0) + c1) + c2) + c3 ≡ s
collapse4 s c0 c1 c2 c3 hyp = begin
  (((s + c0) + c1) + c2) + c3
    ≡⟨ Eq.cong (λ □ → (□ + c2) + c3) (+-assoc s c0 c1) ⟩
  ((s + (c0 + c1)) + c2) + c3
    ≡⟨ Eq.cong (_+ c3) (+-assoc s (c0 + c1) c2) ⟩
  (s + ((c0 + c1) + c2)) + c3
    ≡⟨ +-assoc s ((c0 + c1) + c2) c3 ⟩
  s + (((c0 + c1) + c2) + c3)
    ≡⟨ Eq.cong (s +_) hyp ⟩
  s + ₀
    ≡⟨ +-identityʳ s ⟩
  s ∎
  where open Eq.≡-Reasoning

g4-id : (g : Gen n) (x : P4Carrier n) →
        cact1 g (cact1 g (cact1 g (cact1 g x))) ≡ x
g4-id (gate₁ H-gate) (s , (₀ , ₀) ∷ ps) = Eq.cong₂ _,_ (collapse4 s _ _ _ _ Eq.refl) Eq.refl
g4-id (gate₁ H-gate) (s , (₀ , ₁) ∷ ps) = Eq.cong₂ _,_ (collapse4 s _ _ _ _ Eq.refl) Eq.refl
g4-id (gate₁ H-gate) (s , (₁ , ₀) ∷ ps) = Eq.cong₂ _,_ (collapse4 s _ _ _ _ Eq.refl) Eq.refl
g4-id (gate₁ H-gate) (s , (₁ , ₁) ∷ ps) = Eq.cong₂ _,_ (collapse4 s _ _ _ _ Eq.refl) Eq.refl
g4-id (gate₁ S-gate) (s , (₀ , ₀) ∷ ps) = Eq.cong₂ _,_ (collapse4 s _ _ _ _ Eq.refl) Eq.refl
g4-id (gate₁ S-gate) (s , (₀ , ₁) ∷ ps) = Eq.cong₂ _,_ (collapse4 s _ _ _ _ Eq.refl) Eq.refl
g4-id (gate₁ S-gate) (s , (₁ , ₀) ∷ ps) = Eq.cong₂ _,_ (collapse4 s _ _ _ _ Eq.refl) Eq.refl
g4-id (gate₁ S-gate) (s , (₁ , ₁) ∷ ps) = Eq.cong₂ _,_ (collapse4 s _ _ _ _ Eq.refl) Eq.refl
g4-id (gate₂ CZ-gate) (s , (₀ , ₀) ∷ (₀ , ₀) ∷ ps) = Eq.cong₂ _,_ (collapse4 s _ _ _ _ Eq.refl) Eq.refl
g4-id (gate₂ CZ-gate) (s , (₀ , ₀) ∷ (₀ , ₁) ∷ ps) = Eq.cong₂ _,_ (collapse4 s _ _ _ _ Eq.refl) Eq.refl
g4-id (gate₂ CZ-gate) (s , (₀ , ₀) ∷ (₁ , ₀) ∷ ps) = Eq.cong₂ _,_ (collapse4 s _ _ _ _ Eq.refl) Eq.refl
g4-id (gate₂ CZ-gate) (s , (₀ , ₀) ∷ (₁ , ₁) ∷ ps) = Eq.cong₂ _,_ (collapse4 s _ _ _ _ Eq.refl) Eq.refl
g4-id (gate₂ CZ-gate) (s , (₀ , ₁) ∷ (₀ , ₀) ∷ ps) = Eq.cong₂ _,_ (collapse4 s _ _ _ _ Eq.refl) Eq.refl
g4-id (gate₂ CZ-gate) (s , (₀ , ₁) ∷ (₀ , ₁) ∷ ps) = Eq.cong₂ _,_ (collapse4 s _ _ _ _ Eq.refl) Eq.refl
g4-id (gate₂ CZ-gate) (s , (₀ , ₁) ∷ (₁ , ₀) ∷ ps) = Eq.cong₂ _,_ (collapse4 s _ _ _ _ Eq.refl) Eq.refl
g4-id (gate₂ CZ-gate) (s , (₀ , ₁) ∷ (₁ , ₁) ∷ ps) = Eq.cong₂ _,_ (collapse4 s _ _ _ _ Eq.refl) Eq.refl
g4-id (gate₂ CZ-gate) (s , (₁ , ₀) ∷ (₀ , ₀) ∷ ps) = Eq.cong₂ _,_ (collapse4 s _ _ _ _ Eq.refl) Eq.refl
g4-id (gate₂ CZ-gate) (s , (₁ , ₀) ∷ (₀ , ₁) ∷ ps) = Eq.cong₂ _,_ (collapse4 s _ _ _ _ Eq.refl) Eq.refl
g4-id (gate₂ CZ-gate) (s , (₁ , ₀) ∷ (₁ , ₀) ∷ ps) = Eq.cong₂ _,_ (collapse4 s _ _ _ _ Eq.refl) Eq.refl
g4-id (gate₂ CZ-gate) (s , (₁ , ₀) ∷ (₁ , ₁) ∷ ps) = Eq.cong₂ _,_ (collapse4 s _ _ _ _ Eq.refl) Eq.refl
g4-id (gate₂ CZ-gate) (s , (₁ , ₁) ∷ (₀ , ₀) ∷ ps) = Eq.cong₂ _,_ (collapse4 s _ _ _ _ Eq.refl) Eq.refl
g4-id (gate₂ CZ-gate) (s , (₁ , ₁) ∷ (₀ , ₁) ∷ ps) = Eq.cong₂ _,_ (collapse4 s _ _ _ _ Eq.refl) Eq.refl
g4-id (gate₂ CZ-gate) (s , (₁ , ₁) ∷ (₁ , ₀) ∷ ps) = Eq.cong₂ _,_ (collapse4 s _ _ _ _ Eq.refl) Eq.refl
g4-id (gate₂ CZ-gate) (s , (₁ , ₁) ∷ (₁ , ₁) ∷ ps) = Eq.cong₂ _,_ (collapse4 s _ _ _ _ Eq.refl) Eq.refl
g4-id (g ↥) (s , p ∷ ps) =
  Eq.cong₂ _,_ (Eq.cong proj₁ (g4-id g (s , ps)))
               (Eq.cong (p ∷_) (Eq.cong proj₂ (g4-id g (s , ps))))
