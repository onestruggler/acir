------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 4.2, generalised and corrected (Amy, QPL 2018)
--
-- Lemma 4.2 of "Towards Large-scale Functional Verification of
-- Universal Quantum Circuits" refutes identity by interference: where
-- the phase is ½y₀Q + R with y₀ internal, the two branches of y₀
-- cancel at every path where Q is odd, so an input at which Q is odd
-- at every path has a vanishing diagonal entry, and the identity's
-- diagonal entries are 1.  That is interference-at, which needs
-- nothing of Q.  An input of that kind exists as soon as Q mentions no
-- path variable modulo 2 (then its parity does not depend on the
-- paths: parity-free) and is not ≡ 0 modulo 2 (then some input makes
-- it odd, by a search over the inputs and Möbius inversion:
-- even-or-odd-input); that is interferenceᴳ.  The paper's §4.2 prose
-- asks for a non-zero Boolean-valued Q in input variables only, which
-- is then 1 at some input (one-somewhere, the fact the paper cites to
-- its reference [26]), and that is enough: interference-bool.  Where
-- Q is even modulo 2 instead, the head of the phase is ≡ 0 modulo 1,
-- which is [Elim]'s premise; so for Q free of path variables modulo 2
-- one of the two always happens (elim-or-not-id).
--
-- The lemma as the paper states it is false.  It asks only that Q be
-- "a non-zero integer-valued polynomial not containing any path
-- variables", and Q = 2x₁ is one: ½y₀·2x₁ = y₀x₁ is an integer, so
-- the phase does not see y₀ at all and the two branches double
-- instead of cancelling.  Two counterexamples are checked, both with
-- Q = 2x₁, y₀ internal and Q free of path variables exactly:
--
-- * lemma-4-2-as-stated-fails: |x⟩ ↦ ½ Σ_{y₀} e^{2πi·½y₀·2x₁} |x⟩,
--   the identity.  Its normalisation is 1/√2², not the paper's
--   1/√2^(m+1) = 1/√2 (with which it would be √2 times the
--   identity); here, as in PathSum.Denotation, the normalisation is
--   free.
-- * lemma-4-2-as-stated-fails-tied has the paper's normalisation, one
--   factor 1/√2 per path variable, at m = 2:
--   |x⟩ ↦ 1/√2³ Σ_{y₀y₁y₂} e^{2πi(½y₀·2x₁ + ⅛ - ¼y₁ - ⅛y₂ + ¾y₁y₂)}
--   |x₁ ⊕ y₂⟩, again the identity: the two branches of y₀ agree, and
--   those of y₁ cancel where y₂ = 1 (the y₁ coefficient is then ½)
--   and add up to √2 where y₂ = 0 (it is then -¼).
--
-- So the formal hypothesis is Q odd (not merely non-zero) somewhere;
-- and, as in [HH], y₀ internal, which the paper leaves implicit.
-- Where lemma 4.3 uses the lemma, Q is a linear Boolean-valued form in
-- the inputs, a case of interference-bool; PathSum.Denotation proves
-- that case on its own (interference-lemma), and it is not derived
-- again here.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; zero; suc)

module PathSum.Interference (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_)
open import Data.Fin.Base using (zero)
open import Data.Fin.Subset using (inside; outside; _∈_)
open import Data.Fin.Subset.Properties using (∉⊥)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; -_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; _∣?_; divides; ∣-refl; ∣m∣n⇒∣m+n; ∣m∣n⇒∣m-n; ∣m⇒∣-m; ∣⇒∣ᵤ;
   0∣⇒≡0)
open import Data.Integer.Properties using
  (+-identityˡ; +-identityʳ; +-inverseʳ; *-zeroʳ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Divisibility using (∣1⇒≡1)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Vec.Base using (_∷_; here)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Nullary.Negation using (¬_; contradiction)

open import PathSum.Base using
  (PathSum; ⟨_,_⟩; phase; out; idPS; y₀; head-part; tail-part)
open import PathSum.Cyclotomic M₀ using
  (Amp; _≐_; 0ᴬ; zpow; zpow-cong; zpow-0≢0ᴬ; √2·-map; √2·-0ᴬ; Σᴮ;
   Σᴮ-cong; Σᴮ-0; extend; scale; scale-map; scale-injective)
  renaming (N to Nᶻ)
open import PathSum.Decide M₀ using (search)
open import PathSum.Denotation M₀ using
  (Assign; hits; amp; _≋_; ≋-trans; amp-idPS; elim-sound; eval-true;
   eval-false)
open import PathSum.Identity M₀ using (id-if)
open import PathSum.Mobius using (values⇒coefficientsᵐ)
open import PathSum.Pairs M₀ using (module Pair; half-odd; hits-eval)
open import PathSum.Polynomial using
  (Poly; Var; x[_]; y[_]; ⟪_⟫; _≟ᵐ_; 0ᴾ; _-ᴾ_; _·ᴾ_; κ; μ;
   _≈[_]_; NoVar; satᵐ; sat; eval)
open import PathSum.Polynomial.Boolean using
  (IsBit; BoolValued; ≈-from-values)
open import PathSum.Polynomial.Product using (eval-0ᴾ; ≈-refl; ≈-trans)
open import PathSum.Polynomial.Properties using
  (Σmon-cong; eval-∣; eval-−ᴾ; eval-·ᴾ; eval-κ; eval-≈; eval-cong;
   eval-ext; emptyᵇ; emptyᵇ⇒≡⊥; emptyᵇ-witness; sat-cong-⊆; i∣0)
open import PathSum.Polynomial.Substitution using
  (Absent; Absent-·ᴾ; Absent-μ)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Order M using (pow; pow-suc)
open import PathSum.Reduction M using (⅛; ¼; ½; elim-reduct)
open import PathSum.Reduction.General M using (½·-≈)

open +-*-Solver using (solve; con; _:+_; _:-_; :-_; _:*_; _:=_)

private
  variable
    n k m : ℕ


------------------------------------------------------------------------
-- A vanishing diagonal entry

-- The identity's diagonal entries are ζ^0, so a path-sum with a
-- diagonal amplitude that vanishes is not the identity, whatever its
-- normalisation.

private
  scale-0ᴬ : ∀ j → scale j 0ᴬ ≐ 0ᴬ
  scale-0ᴬ zero    _ = refl
  scale-0ᴬ (suc j) w = trans (√2·-map (scale-0ᴬ j) w) (√2·-0ᴬ w)

vanishing⇒¬id : (ξ : PathSum n k m) (x : Assign n) → amp ξ x x ≐ 0ᴬ →
                ¬ (ξ ≋ idPS)
vanishing⇒¬id {k = k} ξ x amp0 ξ≋id =
  zpow-0≢0ᴬ (λ w → trans (sym (amp-idPS x w)) (idzero w))
  where
  idzero : amp idPS x x ≐ 0ᴬ
  idzero = scale-injective k (amp idPS x x) 0ᴬ
    (λ w → trans (sym (ξ≋id x x w)) (trans (amp0 w) (sym (scale-0ᴬ k w))))


------------------------------------------------------------------------
-- The semantic core

-- Where the head of the phase is ½Q and Q is odd at x at every path,
-- every pair of branches of y₀ cancels at x, so the diagonal entry at
-- x vanishes.  Nothing is asked of Q beyond that one input.

interference-at : (ξ : PathSum n k (suc m)) (Q : Poly n m) →
                  head-part (phase ξ) ≈[ pow M ] (½ ·ᴾ Q) →
                  (∀ w → NoVar (+ 2) y₀ (out ξ w)) →
                  (x : Assign n) →
                  (∀ (y : Assign m) → ¬ ((+ 2) ∣ eval Q x y)) →
                  ¬ (ξ ≋ idPS)
interference-at {m = m} ξ Q eqP eqf x odd = vanishing⇒¬id ξ x amp0
  where
  open Pair ξ eqf using (F; hd; amp-pairs; F-cancel)

  half : ∀ y → pow M ∣ (hd x y - ½)
  half y = half-odd {h = hd x y} {s = eval Q x y}
    (subst (λ u → pow M ∣ (hd x y - u)) (eval-·ᴾ ½ Q x y)
           (eval-≈ {d = pow M} (head-part (phase ξ)) (½ ·ᴾ Q) eqP x y))
    (odd y)

  amp0 : amp ξ x x ≐ 0ᴬ
  amp0 w = trans (amp-pairs x x w)
    (trans (Σᴮ-cong (λ y → F-cancel x x y (half y)) w) (Σᴮ-0 {m} w))


------------------------------------------------------------------------
-- Quotients free of path variables modulo 2

-- Splitting Q into its monomials without path variables and the rest,
-- the rest has even coefficients and the first part does not read the
-- paths at all; so the parity of Q at x is the same at every path.

private
  if-0 : ∀ (b : Bool) → (if b then 0ℤ else 0ℤ) ≡ 0ℤ
  if-0 true  = refl
  if-0 false = refl

  -- The monomials of Q without path variables.
  inputs : Poly n m → Poly n m
  inputs Q (α , β) = if emptyᵇ β then Q (α , β) else 0ℤ

  rest-even : (Q : Poly n m) → (∀ j → NoVar (+ 2) y[ j ] Q) →
              ∀ γ → (+ 2) ∣ (Q -ᴾ inputs Q) γ
  rest-even Q noy (α , β) = go (emptyᵇ β) refl
    where
    go : ∀ b → emptyᵇ β ≡ b →
         (+ 2) ∣ (Q (α , β) - (if b then Q (α , β) else 0ℤ))
    go true  _  = subst ((+ 2) ∣_) (sym (+-inverseʳ (Q (α , β)))) i∣0
    go false eq = subst ((+ 2) ∣_) (sym (+-identityʳ (Q (α , β))))
      (noy (proj₁ wit) (α , β) (proj₂ wit))
      where
      wit = emptyᵇ-witness β eq

  inputs-const : (Q : Poly n m) (x : Assign n) (y y′ : Assign m) →
                 eval (inputs Q) x y ≡ eval (inputs Q) x y′
  inputs-const Q x y y′ = Σmon-cong per
    where
    per : ∀ γ → (if satᵐ γ x y then inputs Q γ else 0ℤ) ≡
                (if satᵐ γ x y′ then inputs Q γ else 0ℤ)
    per (α , β) = go (emptyᵇ β) refl
      where
      zero-at : ∀ v → emptyᵇ β ≡ false →
                (if satᵐ (α , β) x v then inputs Q (α , β) else 0ℤ) ≡ 0ℤ
      zero-at v eq = trans
        (cong (λ b → if satᵐ (α , β) x v then (if b then Q (α , β) else 0ℤ)
                     else 0ℤ) eq)
        (if-0 (satᵐ (α , β) x v))

      go : ∀ b → emptyᵇ β ≡ b →
           (if satᵐ (α , β) x y then inputs Q (α , β) else 0ℤ) ≡
           (if satᵐ (α , β) x y′ then inputs Q (α , β) else 0ℤ)
      go true  eq = cong (λ s → if sat α x ∧ s then inputs Q (α , β) else 0ℤ)
        (sat-cong-⊆ β {y} {y′} (λ j j∈β →
          contradiction (subst (j ∈_) (emptyᵇ⇒≡⊥ β eq) j∈β) ∉⊥))
      go false eq = trans (zero-at y eq) (sym (zero-at y′ eq))

  reshape : ∀ a b c → a - b ≡ (a - c) - (b - c)
  reshape = solve 3 (λ a b c → a :- b := (a :- c) :- (b :- c)) refl

parity-free : (Q : Poly n m) → (∀ j → NoVar (+ 2) y[ j ] Q) →
              ∀ (x : Assign n) (y y′ : Assign m) →
              (+ 2) ∣ (eval Q x y - eval Q x y′)
parity-free Q noy x y y′ =
  subst ((+ 2) ∣_) (sym (reshape (eval Q x y) (eval Q x y′) (eval I x y)))
        (∣m∣n⇒∣m-n (off y) off′)
  where
  I = inputs Q

  -- At every path, Q and its input part have the same parity ...
  off : ∀ v → (+ 2) ∣ (eval Q x v - eval I x v)
  off v = subst ((+ 2) ∣_) (eval-−ᴾ Q I x v)
                (eval-∣ (Q -ᴾ I) (rest-even Q noy) x v)

  -- ... and the input part takes the same value at every path.
  off′ : (+ 2) ∣ (eval Q x y′ - eval I x y)
  off′ = subst (λ u → (+ 2) ∣ (eval Q x y′ - u))
               (sym (inputs-const Q x y y′)) (off y′)


-- So a quotient free of path variables modulo 2 is either ≡ 0 modulo
-- 2, or odd at some input at every path.  The search is over the
-- inputs at the all-false path, which by parity-free stands for every
-- path, and Möbius inversion turns "even at every point" into "even
-- coefficient by coefficient".

private
  fill : ∀ a b → (a - b) + b ≡ a
  fill = solve 2 (λ a b → (a :- b) :+ b := a) refl

  module Search {n m : ℕ} (Q : Poly n m)
                (noy : ∀ j → NoVar (+ 2) y[ j ] Q) where

    y⁰ : Assign m
    y⁰ _ = false

    Even : Assign n → Set
    Even x = (+ 2) ∣ eval Q x y⁰

    resp : ∀ {x x′} → (∀ i → x i ≡ x′ i) → Even x → Even x′
    resp {x} {x′} x≗x′ =
      subst ((+ 2) ∣_) (eval-cong Q {x} {x′} {y⁰} {y⁰} x≗x′ (λ _ → refl))

    -- Even at the all-false path, so even at every path.
    everywhere : ∀ x → Even x → ∀ y → (+ 2) ∣ eval Q x y
    everywhere x e y = subst ((+ 2) ∣_) (fill (eval Q x y) (eval Q x y⁰))
      (∣m∣n⇒∣m+n (parity-free Q noy x y y⁰) e)

    even : (∀ x → Even x) → Q ≈[ + 2 ] 0ᴾ
    even all = ≈-from-values {c = + 2} Q 0ᴾ (λ x y →
      subst ((+ 2) ∣_)
        (sym (trans (cong (λ u → eval Q x y - u) (eval-0ᴾ x y))
                    (+-identityʳ (eval Q x y))))
        (everywhere x (all x) y))

    odd : ∀ x → ¬ Even x → ∀ y → ¬ ((+ 2) ∣ eval Q x y)
    odd x ¬e y e = ¬e (subst ((+ 2) ∣_) (fill (eval Q x y⁰) (eval Q x y))
      (∣m∣n⇒∣m+n (parity-free Q noy x y⁰ y) e))

    decide : Q ≈[ + 2 ] 0ᴾ ⊎
             ∃ (λ x → ∀ y → ¬ ((+ 2) ∣ eval Q x y))
    decide with search Even (λ x → (+ 2) ∣? eval Q x y⁰) resp
    ... | inj₁ all      = inj₁ (even all)
    ... | inj₂ (x , ¬e) = inj₂ (x , odd x ¬e)

even-or-odd-input : (Q : Poly n m) → (∀ j → NoVar (+ 2) y[ j ] Q) →
                    Q ≈[ + 2 ] 0ᴾ ⊎
                    ∃ (λ (x : Assign n) →
                         ∀ (y : Assign m) → ¬ ((+ 2) ∣ eval Q x y))
even-or-odd-input = Search.decide

-- The claim of §4.2 that the paper cites to [26]: a non-zero
-- Boolean-valued polynomial in the input variables only is 1 at some
-- input.  Boolean values that are all even are all 0, and a polynomial
-- that vanishes at every point has no non-zero coefficient.

private
  2∤1 : ¬ ((+ 2) ∣ 1ℤ)
  2∤1 h with ∣1⇒≡1 (∣⇒∣ᵤ h)
  ... | ()

  even-bit : ∀ {z} → IsBit z → (+ 2) ∣ z → 0ℤ ∣ z
  even-bit (inj₁ refl) _ = i∣0
  even-bit (inj₂ refl) h = contradiction h 2∤1

  odd-bit : ∀ {z} → IsBit z → ¬ ((+ 2) ∣ z) → z ≡ 1ℤ
  odd-bit (inj₁ refl) h = contradiction i∣0 h
  odd-bit (inj₂ refl) _ = refl

one-somewhere : (Q : Poly n m) → BoolValued Q →
                (∀ j → NoVar (+ 2) y[ j ] Q) → ¬ (∀ γ → Q γ ≡ 0ℤ) →
                ∃ λ (x : Assign n) → ∀ (y : Assign m) → eval Q x y ≡ 1ℤ
one-somewhere Q bQ noy nonzero = pick (even-or-odd-input Q noy)
  where
  pick : Q ≈[ + 2 ] 0ᴾ ⊎ ∃ (λ x → ∀ y → ¬ ((+ 2) ∣ eval Q x y)) →
         ∃ λ x → ∀ y → eval Q x y ≡ 1ℤ
  pick (inj₁ Q≈0) = contradiction (λ γ → 0∣⇒≡0
    (values⇒coefficientsᵐ 0ℤ Q (λ x y → even-bit (bQ x y) (even x y)) γ))
    nonzero
    where
    even : ∀ x y → (+ 2) ∣ eval Q x y
    even x y = subst ((+ 2) ∣_)
      (trans (cong (λ u → eval Q x y - u) (eval-0ᴾ x y))
             (+-identityʳ (eval Q x y)))
      (eval-≈ {d = + 2} Q 0ᴾ Q≈0 x y)
  pick (inj₂ (x , odd)) = x , λ y → odd-bit (bQ x y) (odd y)


------------------------------------------------------------------------
-- Lemma 4.2, corrected

-- Q free of path variables modulo 2 and not ≡ 0 modulo 2.

interferenceᴳ : (ξ : PathSum n k (suc m)) (Q : Poly n m) →
                head-part (phase ξ) ≈[ pow M ] (½ ·ᴾ Q) →
                (∀ w → NoVar (+ 2) y₀ (out ξ w)) →
                (∀ j → NoVar (+ 2) y[ j ] Q) →
                ¬ (Q ≈[ + 2 ] 0ᴾ) →
                ¬ (ξ ≋ idPS)
interferenceᴳ ξ Q eqP eqf noy nonzero = settle (even-or-odd-input Q noy)
  where
  settle : Q ≈[ + 2 ] 0ᴾ ⊎ ∃ (λ x → ∀ y → ¬ ((+ 2) ∣ eval Q x y)) →
           ¬ (ξ ≋ idPS)
  settle (inj₁ even)      = contradiction even nonzero
  settle (inj₂ (x , odd)) = interference-at ξ Q eqP eqf x odd

-- The paper's §4.2 wording: a non-zero Boolean-valued quotient in the
-- input variables only.

interference-bool : (ξ : PathSum n k (suc m)) (Q : Poly n m) →
                    head-part (phase ξ) ≈[ pow M ] (½ ·ᴾ Q) →
                    (∀ w → NoVar (+ 2) y₀ (out ξ w)) →
                    BoolValued Q → (∀ j → NoVar (+ 2) y[ j ] Q) →
                    ¬ (∀ γ → Q γ ≡ 0ℤ) →
                    ¬ (ξ ≋ idPS)
interference-bool ξ Q eqP eqf bQ noy nonzero =
  interference-at ξ Q eqP eqf (proj₁ found) (λ y e →
    2∤1 (subst ((+ 2) ∣_) (proj₂ found y) e))
  where
  found = one-somewhere Q bQ noy nonzero

-- The alternative: an even quotient makes the head of the phase ≡ 0
-- modulo 1, which is [Elim]'s premise.

elim-or-not-id : (ξ : PathSum n k (suc m)) (Q : Poly n m) →
                 head-part (phase ξ) ≈[ pow M ] (½ ·ᴾ Q) →
                 (∀ w → NoVar (+ 2) y₀ (out ξ w)) →
                 (∀ j → NoVar (+ 2) y[ j ] Q) →
                 head-part (phase ξ) ≈[ pow M ] 0ᴾ ⊎ ¬ (ξ ≋ idPS)
elim-or-not-id ξ Q eqP eqf noy = settle (even-or-odd-input Q noy)
  where
  half-zero : (½ ·ᴾ 0ᴾ) ≈[ pow M ] 0ᴾ
  half-zero γ = subst (pow M ∣_) (sym (+-identityʳ (½ * 0ℤ)))
                      (subst (pow M ∣_) (sym (*-zeroʳ ½)) i∣0)

  settle : Q ≈[ + 2 ] 0ᴾ ⊎ ∃ (λ x → ∀ y → ¬ ((+ 2) ∣ eval Q x y)) →
           head-part (phase ξ) ≈[ pow M ] 0ᴾ ⊎ ¬ (ξ ≋ idPS)
  settle (inj₁ even) = inj₁
    (≈-trans {c = pow M} {P = head-part (phase ξ)} {Q = ½ ·ᴾ Q} {R = 0ᴾ} eqP
      (≈-trans {c = pow M} {P = ½ ·ᴾ Q} {Q = ½ ·ᴾ 0ᴾ} {R = 0ᴾ}
        (½·-≈ {P = Q} {Q = 0ᴾ} even) half-zero))
  settle (inj₂ (x , odd)) = inj₂ (interference-at ξ Q eqP eqf x odd)


------------------------------------------------------------------------
-- Building the counterexamples

-- h ⊲ t is y₀·h + t: h is the coefficient of the first path variable
-- and t the rest, so that head-part and tail-part take it apart again,
-- definitionally.

infixr 5 _⊲_

_⊲_ : Poly n m → Poly n m → Poly n (suc m)
(h ⊲ t) (α , inside  ∷ β) = h (α , β)
(h ⊲ t) (α , outside ∷ β) = t (α , β)

-- The quotient 2x₁: non-zero, integer-valued, free of path variables.

Q-2x₁ : Poly 1 m
Q-2x₁ = (+ 2) ·ᴾ μ x[ zero ]

private
  μ-at : (v : Var n m) → μ v ⟪ v ⟫ ≡ 1ℤ
  μ-at v with ⟪ v ⟫ ≟ᵐ ⟪ v ⟫
  ... | yes _ = refl
  ... | no ¬p = contradiction refl ¬p

  2≢0 : ¬ ((+ 2) * 1ℤ ≡ 0ℤ)
  2≢0 ()

Q-2x₁-nonzero : ¬ (∀ γ → Q-2x₁ {m} γ ≡ 0ℤ)
Q-2x₁-nonzero h = 2≢0
  (trans (sym (cong (λ u → (+ 2) * u) (μ-at x[ zero ]))) (h ⟪ x[ zero ] ⟫))

Q-2x₁-no-paths : ∀ j → Absent y[ j ] (Q-2x₁ {m})
Q-2x₁-no-paths j =
  Absent-·ᴾ (+ 2) {v = y[ j ]} {A = μ x[ zero ]} (Absent-μ x[ zero ] y[ j ] ∉⊥)

private
  ½·2 : ½ * (+ 2) ≡ pow M
  ½·2 = sym (pow-suc (suc (suc M₀)))

  -- ½ · 2u is a whole number.
  whole : ∀ u → pow M ∣ ((½ * ((+ 2) * u)) - 0ℤ)
  whole u = divides u (trans (shape ½ u) (cong (λ v → u * v) ½·2))
    where
    shape : ∀ h u → (h * ((+ 2) * u)) - 0ℤ ≡ u * (h * (+ 2))
    shape = solve 2 (λ h u →
      (h :* (con (+ 2) :* u)) :- con 0ℤ := u :* (h :* con (+ 2))) refl

  -- So y₀ is invisible in a phase ½y₀·2x₁ + R.
  head-whole : (R : Poly 1 m) →
               head-part ((½ ·ᴾ Q-2x₁) ⊲ R) ≈[ pow M ] 0ᴾ
  head-whole R (α , β) = whole (μ x[ zero ] (α , β))


------------------------------------------------------------------------
-- The paper's lemma 4.2 is false: at a free normalisation

-- |x⟩ ↦ ½ Σ_{y₀} e^{2πi·½y₀·2x₁} |x⟩.  [Elim] removes y₀, and what is
-- left is the identity's polynomials.

ξ-2x₁ : PathSum 1 2 1
ξ-2x₁ = ⟨ (½ ·ᴾ Q-2x₁) ⊲ 0ᴾ , (λ w → 0ᴾ ⊲ μ x[ w ]) ⟩

private
  internal-2x₁ : ∀ w → NoVar (+ 2) y₀ (out ξ-2x₁ w)
  internal-2x₁ w (α , _ ∷ β) here = i∣0

ξ-2x₁≋id : ξ-2x₁ ≋ idPS
ξ-2x₁≋id = ≋-trans {ξ = ξ-2x₁} {ζ = elim-reduct ξ-2x₁} {χ = idPS}
  (elim-sound ξ-2x₁ (head-whole 0ᴾ) internal-2x₁)
  (id-if (elim-reduct ξ-2x₁) (λ w → ≈-refl {c = + 2} {P = μ x[ w ]})
         (≈-refl {c = pow M} {P = 0ᴾ}))

lemma-4-2-as-stated-fails :
  ∃ λ (ξ : PathSum 1 2 1) → ∃ λ (Q : Poly 1 0) →
    (head-part (phase ξ) ≈[ pow M ] (½ ·ᴾ Q)) ×
    (∀ w → NoVar (+ 2) y₀ (out ξ w)) ×
    ¬ (∀ γ → Q γ ≡ 0ℤ) ×
    (ξ ≋ idPS)
lemma-4-2-as-stated-fails =
  ξ-2x₁ , Q-2x₁ , ≈-refl {c = pow M} {P = ½ ·ᴾ Q-2x₁} , internal-2x₁ ,
  Q-2x₁-nonzero , ξ-2x₁≋id


------------------------------------------------------------------------
-- The paper's lemma 4.2 is false: at its own normalisation

-- "Tied": the normalisation is one factor 1/√2 per path variable, as
-- in definition 2.1 and in the lemma's statement, 1/√2^(m+1) -- here
-- with m = 2, so three path variables and 1/√2³.  The phase is
-- ½y₀·2x₁ + R with R = ⅛ - ¼y₁ - ⅛y₂ + ¾y₁y₂, and the output x₁ ⊕ y₂.
-- [Elim] removes y₀; then the branches of y₁ cancel where y₂ = 1 and
-- make √2 where y₂ = 0, which is the one path returning the input, so
-- the amplitude is √2 times the identity's against a normalisation of
-- 1/√2.  (No rule of figure 2 finishes the job, y₂ not being internal:
-- the amplitude is computed.)

private
  ¾ : ℤ
  ¾ = ¼ + ½

R-tied : Poly 1 2
R-tied = (κ ¾ ⊲ κ (- ¼)) ⊲ (κ (- ⅛) ⊲ κ ⅛)

ξ-tied : PathSum 1 3 3
ξ-tied = ⟨ (½ ·ᴾ Q-2x₁) ⊲ R-tied
         , (λ w → 0ᴾ ⊲ (0ᴾ ⊲ (κ 1ℤ ⊲ μ x[ w ]))) ⟩

private
  internal-tied : ∀ w → NoVar (+ 2) y₀ (out ξ-tied w)
  internal-tied w (α , _ ∷ β) here = i∣0

  ζ : PathSum 1 1 2
  ζ = elim-reduct ξ-tied

  internal-ζ : ∀ w → NoVar (+ 2) y₀ (out ζ w)
  internal-ζ w (α , _ ∷ β) here = i∣0

  module Z = Pair ζ internal-ζ

  y∅ : Assign 0
  y∅ ()

  -- The dyadic constants.

  double : ∀ u → u + u ≡ u * (+ 2)
  double = solve 1 (λ u → u :+ u := u :* con (+ 2)) refl

  ⅛+⅛ : ⅛ + ⅛ ≡ ¼
  ⅛+⅛ = trans (double ⅛) (sym (pow-suc M₀))

  ¼+¼ : ¼ + ¼ ≡ ½
  ¼+¼ = trans (double ¼) (sym (pow-suc (suc M₀)))

  ½+½ : ½ + ½ ≡ pow M
  ½+½ = trans (double ½) ½·2

  -- The coefficient of y₁, where y₂ is 1 and where it is 0, and the
  -- constant term where y₂ is 0.

  hd-true : ∀ x g → Z.hd x (extend true g) ≡ ¾ + (- ¼)
  hd-true x g = trans (eval-true (head-part (phase ζ)) x g)
    (cong₂ _+_
      (trans (eval-ext (head-part (head-part (phase ζ))) (κ ¾)
                       (λ _ → refl) x g) (eval-κ ¾ x g))
      (trans (eval-ext (tail-part (head-part (phase ζ))) (κ (- ¼))
                       (λ _ → refl) x g) (eval-κ (- ¼) x g)))

  hd-false : ∀ x g → Z.hd x (extend false g) ≡ - ¼
  hd-false x g = trans (eval-false (head-part (phase ζ)) x g)
    (trans (eval-ext (tail-part (head-part (phase ζ))) (κ (- ¼))
                     (λ _ → refl) x g) (eval-κ (- ¼) x g))

  tv-false : ∀ x g → Z.tv x (extend false g) ≡ ⅛
  tv-false x g = trans (eval-false (tail-part (phase ζ)) x g)
    (trans (eval-ext (tail-part (tail-part (phase ζ))) (κ ⅛)
                     (λ _ → refl) x g) (eval-κ ⅛ x g))

  -- Where y₂ = 1 the coefficient of y₁ is ¾ - ¼ = ½: the branches
  -- cancel.

  cancel-at : ∀ x g → pow M ∣ (Z.hd x (extend true g) - ½)
  cancel-at x g = subst (pow M ∣_)
    (sym (trans (cong (λ u → u - ½) (hd-true x g)) (vanish ¼ ½))) i∣0
    where
    vanish : ∀ a b → ((a + b) + (- a)) - b ≡ 0ℤ
    vanish = solve 2 (λ a b → ((a :+ b) :+ (:- a)) :- b := con 0ℤ) refl

  -- Where y₂ = 0 it is -¼ ≡ ¼ + ½: [ω]'s interference.

  ω-at : ∀ x g → pow M ∣ (Z.hd x (extend false g) - (¼ + ½))
  ω-at x g = subst (pow M ∣_)
    (sym (trans (cong (λ u → u - (¼ + ½)) (hd-false x g)) (negate ¼ ½)))
    (∣m⇒∣-m one)
    where
    negate : ∀ a b → (- a) - (a + b) ≡ - ((a + a) + b)
    negate = solve 2 (λ a b → (:- a) :- (a :+ b) := :- ((a :+ a) :+ b)) refl

    one : pow M ∣ ((¼ + ¼) + ½)
    one = subst (pow M ∣_) (sym (trans (cong (λ u → u + ½) ¼+¼) ½+½)) ∣-refl

  -- There the pair makes √2 ζ^((⅛ - ¼) + ⅛) = √2 ζ^0 at the output x₁,
  -- which is √2 times the identity's entry.

  exp-at : ∀ x g →
           (+ Nᶻ) ∣ (((⅛ - ¼) + Z.tv x (extend false g)) -
                     eval (phase idPS) x y∅)
  exp-at x g = subst ((+ Nᶻ) ∣_)
    (sym (trans (cong₂ (λ u v → ((⅛ - ¼) + u) - v) (tv-false x g)
                       (eval-0ᴾ x y∅))
                (trans (cong (λ u → ((⅛ - u) + ⅛) - 0ℤ) (sym ⅛+⅛))
                       (collapse ⅛))))
    i∣0
    where
    collapse : ∀ a → ((a - (a + a)) + a) - 0ℤ ≡ 0ℤ
    collapse = solve 1 (λ a → ((a :- (a :+ a)) :+ a) :- con 0ℤ := con 0ℤ)
                       refl

  -- The rest of ξ's outputs, without y₁: they hit what the identity
  -- hits where y₂ = 0.

  ζ₁ : PathSum 1 0 1
  ζ₁ = ⟨ tail-part (phase ζ) , (λ w → tail-part (out ζ w)) ⟩

  hits-at : ∀ x z g → Z.hitsT x (extend false g) z ≡ hits idPS x y∅ z
  hits-at x z g = hits-eval ζ₁ idPS x (extend false g) y∅ z (λ w →
    trans (eval-false (tail-part (out ζ w)) x g)
      (trans (eval-ext (tail-part (tail-part (out ζ w))) (μ x[ w ])
                       (λ _ → refl) x g)
             (eval-cong (μ x[ w ]) {x} {x} {g} {y∅} (λ _ → refl) (λ ()))))

  if-cong : ∀ {p q : Bool} {a b : Amp} → p ≡ q → a ≐ b →
            (if p then a else 0ᴬ) ≐ (if q then b else 0ᴬ)
  if-cong {p = true}  refl a≐b = a≐b
  if-cong {p = false} refl _   = λ _ → refl

  target : ∀ x z g →
           (if Z.hitsT x (extend false g) z
            then zpow ((⅛ - ¼) + Z.tv x (extend false g)) else 0ᴬ)
           ≐ scale 0 (amp idPS x z)
  target x z g = if-cong (hits-at x z g)
    (zpow-cong {(⅛ - ¼) + Z.tv x (extend false g)} {eval (phase idPS) x y∅}
               (exp-at x g))

  branch-true : ∀ x z g → Z.F x z (extend true g) ≐ 0ᴬ
  branch-true x z g = Z.F-cancel x z (extend true g) (cancel-at x g)

  branch-false : ∀ x z g → Z.F x z (extend false g) ≐ scale 1 (amp idPS x z)
  branch-false x z g i = trans (Z.F-ω₁ x z (extend false g) (ω-at x g) i)
    (√2·-map {a = if Z.hitsT x (extend false g) z
                  then zpow ((⅛ - ¼) + Z.tv x (extend false g)) else 0ᴬ}
             {b = scale 0 (amp idPS x z)} (target x z g) i)

  -- A sum over one path variable whose true branch vanishes.  (The
  -- scale-map 0 wrappers keep the amplitude of the reduct from being
  -- unfolded when the types are compared.)

  Σᴮ₁ : ∀ (f : Assign 1 → Amp) (a : Amp) →
        (∀ g → f (extend true g) ≐ 0ᴬ) → (∀ g → f (extend false g) ≐ a) →
        Σᴮ f ≐ a
  Σᴮ₁ f a t e i = trans (cong₂ _+_ (t _ i) (e _ i)) (+-identityˡ (a i))

  ζ≋id : ζ ≋ idPS
  ζ≋id x z i = trans (scale-map 0 (Z.amp-pairs x z) i)
    (scale-map 0 {a = Σᴮ (Z.F x z)} {b = scale 1 (amp idPS x z)}
      (Σᴮ₁ (Z.F x z) (scale 1 (amp idPS x z))
           (branch-true x z) (branch-false x z)) i)

ξ-tied≋id : ξ-tied ≋ idPS
ξ-tied≋id = ≋-trans {ξ = ξ-tied} {ζ = ζ} {χ = idPS}
  (elim-sound ξ-tied (head-whole R-tied) internal-tied) ζ≋id

lemma-4-2-as-stated-fails-tied :
  ∃ λ (ξ : PathSum 1 3 3) → ∃ λ (Q : Poly 1 2) →
    (head-part (phase ξ) ≈[ pow M ] (½ ·ᴾ Q)) ×
    (∀ j → Absent y[ j ] Q) ×
    (∀ w → NoVar (+ 2) y₀ (out ξ w)) ×
    ¬ (∀ γ → Q γ ≡ 0ℤ) ×
    (ξ ≋ idPS)
lemma-4-2-as-stated-fails-tied =
  ξ-tied , Q-2x₁ , ≈-refl {c = pow M} {P = ½ ·ᴾ Q-2x₁} , Q-2x₁-no-paths ,
  internal-tied , Q-2x₁-nonzero , ξ-tied≋id
