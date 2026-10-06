------------------------------------------------------------------------
-- Presentations of groups
--
-- Tied path-sums: definition 2.1's normalisation (Amy, QPL 2018)
--
-- Definition 2.1 ties the normalisation of a path-sum to its path
-- variables: 1/√2^m, with m of them.  PathSum.Base keeps the exponent
-- k apart from m, because the rules of figure 2 do not preserve the
-- tie, so a PathSum n k m with k ≠ m is a path-sum in the paper's sense
-- only through its operator.  Several counterexamples of this
-- development have k ≠ m: PathSum.Compose.Counterexample's P₀ and P₊,
-- PathSum.PartialIsometry.Strict's ½·id and PathSum.Interference's
-- lemma-4-2-as-stated-fails.  This module gives two moves that change
-- k - m by one without changing the operator, and shows that they
-- always reach the tie.
--
--   * pad ξ adds a path variable that occurs nowhere (k + 2, m + 1).
--     Every path is counted twice, and the extra normalisation 1/2
--     undoes that.  It is [Elim] read backwards (pad-≋, from
--     PathSum.Denotation's elim-sound).
--   * gadget ξ adds two path variables y₀ y₁, occurring in no output,
--     with the phase ⅛y₀ - ⅛y₁ + ½y₀y₁ (k + 1, m + 2).  Its four values
--     0, ⅛, -⅛ and ½ give 1 + ζ^⅛ + ζ^-⅛ - 1 = √2, and the extra
--     normalisation 1/√2 undoes that (amp-gadget, gadget-≋, from
--     PathSum.Pairs's Quad).  These are the four values of
--     PathSum.Interference's R-tied, without its constant term.
--
-- pad raises k - m by one and gadget lowers it by one, so every
-- path-sum is equivalent to a tied one (tie; cast only rewrites the
-- indices).  Keeping k apart from m is therefore a matter of
-- presentation: PathSum n k m has exactly the operators of the paper's
-- path-sums with variable inputs, at the fixed precision M (constant
-- inputs are PathSum.Signature's).  The properties of the operator used
-- here transfer along ≋:
--
--   * WellFormed: PathSum.Compose.WellFormed's WellFormed-≋.
--   * Definition 2.4: PathSum.PartialIsometry's Isometric-≋ and
--     PartialIsometric-≋.
--   * Lemma 4.1's restriction condition: Restriction-id-≋, here.
--   * Being the identity: ≋-trans.
--
-- So each counterexample with k ≠ m has a tied twin with the same
-- properties.  The twins are in PathSum.Compose.Counterexample.Tied,
-- PathSum.PartialIsometry.Strict.Tied and
-- PathSum.Isometry.Counterexample; lemma 4.2's is PathSum.Interference's
-- lemma-4-2-as-stated-fails-tied.  The moves change the polynomials,
-- so a counterexample to a syntactic statement (lemma 4.2 reads the
-- phase) needs its own tied witness.
--
-- move carries a fact about gadget ξ (or pad ξ) to a name defined as
-- it, along an equation that Agda checks on the path-sums: for a
-- closed path-sum, asking Agda to see the definition inside an
-- amplitude makes it unfold the amplitude.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; zero; suc)

module PathSum.Tied (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Fin.Base using (zero; suc)
open import Data.Fin.Subset using (inside; outside)
open import Data.Integer.Base using (ℤ; 0ℤ; +_; -_; _+_)
open import Data.Integer.Properties using (+-inverseˡ; +-identityˡ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (_∸_; _≤_)
  renaming (_+_ to _ℕ+_)
open import Data.Nat.Properties using (+-suc; ≤-total; m∸n+n≡m)
open import Data.Product.Base using (∃; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Vec.Base using (_∷_; here; there)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

open import PathSum.AmpLinear M₀ using (scale-comm)
open import PathSum.Base using (PathSum; ⟨_,_⟩; phase; out; y₀)
open import PathSum.Compose.Sum M₀ using (if-cong; zpow-≡)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _+ᴬ_; _≐_; zpow; zpow-anti; √2·; √2·-zpow; √2·-map;
   √2·-0ᴬ; √2·-Σᴮ; Σᴮ-cong; scale; scale-map; scale-√2;
   scale-injective)
open import PathSum.Denotation M₀ using
  (Assign; hits; amp; _≋_; ≋-refl; ≋-trans; elim-sound)
open import PathSum.Interference M₀ using (_⊲_)
open import PathSum.Isometry M₀ using (Restriction-id)
open import PathSum.Pairs M₀ using (module Quad; hits-eval)
open import PathSum.Polynomial using (y[_]; 0ᴾ; κ; NoVar; eval)
open import PathSum.Polynomial.Properties using (eval-ext; eval-κ; i∣0)
open import PathSum.Polynomial.Substitution using (q₀₀; q₀₁; q₁₀; q₁₁)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Reduction M using (⅛; ½; elim-reduct)

open +-*-Solver using (solve; _:+_; :-_; _:=_)

private
  variable
    n k m k′ m′ : ℕ

  -- Chains of equalities of amplitudes.

  infixr 5 _∙_

  _∙_ : {a b c : Amp} → a ≐ b → b ≐ c → a ≐ c
  (p ∙ q) i = trans (p i) (q i)

  ≐-sym : {a b : Amp} → a ≐ b → b ≐ a
  ≐-sym p i = sym (p i)


------------------------------------------------------------------------
-- Padding: a path variable that occurs nowhere

-- |x⟩ ↦ 1/√2^(k+2) Σ_{y₀ y} e^{2πiP(x,y)} |f(x,y)⟩: each path of ξ
-- twice.

pad : PathSum n k m → PathSum n (suc (suc k)) (suc m)
pad ξ = ⟨ 0ᴾ ⊲ phase ξ , (λ w → 0ᴾ ⊲ out ξ w) ⟩

private
  pad-internal : (ξ : PathSum n k m) → ∀ w → NoVar (+ 2) y₀ (out (pad ξ) w)
  pad-internal ξ w (α , _ ∷ β) here = i∣0

-- [Elim] removes y₀ again, and what is left is ξ itself.

pad-≋ : (ξ : PathSum n k m) → pad ξ ≋ ξ
pad-≋ ξ = ≋-trans {ξ = pad ξ} {ζ = elim-reduct (pad ξ)} {χ = ξ}
  (elim-sound (pad ξ) (λ _ → i∣0) (pad-internal ξ))
  (≋-refl {ξ = ξ})


------------------------------------------------------------------------
-- The √2 gadget

-- |x⟩ ↦ 1/√2^(k+1) Σ_{y₀ y₁ y} e^{2πi(⅛y₀ - ⅛y₁ + ½y₀y₁ + P(x,y))}
-- |f(x,y)⟩.  In the notation of PathSum.Interference, h ⊲ t is
-- y₀·h + t.

gadget : PathSum n k m → PathSum n (suc k) (suc (suc m))
gadget ξ = ⟨ (κ ½ ⊲ κ ⅛) ⊲ (κ (- ⅛) ⊲ phase ξ)
           , (λ w → 0ᴾ ⊲ (0ᴾ ⊲ out ξ w)) ⟩

private
  gadget-y₀ : (ξ : PathSum n k m) →
              ∀ w → NoVar (+ 2) y₀ (out (gadget ξ) w)
  gadget-y₀ ξ w (α , _ ∷ β) here = i∣0

  gadget-y₁ : (ξ : PathSum n k m) →
              ∀ w → NoVar (+ 2) y[ suc zero ] (out (gadget ξ) w)
  gadget-y₁ ξ w (α , inside  ∷ _ ∷ β) (there here) = i∣0
  gadget-y₁ ξ w (α , outside ∷ _ ∷ β) (there here) = i∣0

  √2·-if : ∀ (p : Bool) (a : Amp) →
           (if p then √2· a else 0ᴬ) ≐ √2· (if p then a else 0ᴬ)
  √2·-if true  a _ = refl
  √2·-if false a j = sym (√2·-0ᴬ j)

  regroup : ∀ a b c d → (a + b) + (c + d) ≡ (a + d) + (b + c)
  regroup = solve 4 (λ a b c d →
    (a :+ b) :+ (c :+ d) := (a :+ d) :+ (b :+ c)) refl

  drop : ∀ h e u → (h + e) + ((- e) + u) ≡ u + h
  drop = solve 3 (λ h e u → (h :+ e) :+ ((:- e) :+ u) := u :+ h) refl

-- The four branches of y₀ y₁ over each path y of ξ: the quarters of
-- the phase are ½, ⅛, -⅛ and ξ's phase, so the branches are ζ^(½+t),
-- ζ^(⅛+t), ζ^(-⅛+t) and ζ^t.  The first and the last cancel, and the
-- middle two make √2 ζ^t.

module _ {n k m : ℕ} (ξ : PathSum n k m) where

  private
    open Quad (gadget ξ) (gadget-y₀ ξ) (gadget-y₁ ξ)

    t : Assign n → Assign m → ℤ
    t x y = eval (phase ξ) x y

    e₁₁≡ : ∀ x y → e₁₁ x y ≡ ½
    e₁₁≡ x y = trans (eval-ext (q₁₁ (phase (gadget ξ))) (κ ½)
                               (λ _ → refl) x y)
                     (eval-κ ½ x y)

    e₁₀≡ : ∀ x y → e₁₀ x y ≡ ⅛
    e₁₀≡ x y = trans (eval-ext (q₁₀ (phase (gadget ξ))) (κ ⅛)
                               (λ _ → refl) x y)
                     (eval-κ ⅛ x y)

    e₀₁≡ : ∀ x y → e₀₁ x y ≡ - ⅛
    e₀₁≡ x y = trans (eval-ext (q₀₁ (phase (gadget ξ))) (κ (- ⅛))
                               (λ _ → refl) x y)
                     (eval-κ (- ⅛) x y)

    e₀₀≡ : ∀ x y → e₀₀ x y ≡ t x y
    e₀₀≡ x y = eval-ext (q₀₀ (phase (gadget ξ))) (phase ξ) (λ _ → refl) x y

    hits≡ : ∀ x y z → hitsQ x y z ≡ hits ξ x y z
    hits≡ x y z = hits-eval ξ₀₀ ξ x y y z (λ w →
      eval-ext (q₀₀ (out (gadget ξ) w)) (out ξ w) (λ _ → refl) x y)

    module _ (x : Assign n) (y : Assign m) where

      u : ℤ
      u = e₀₀ x y

      A B C D : Amp
      A = zpow ((e₁₁ x y + e₁₀ x y) + (e₀₁ x y + u))
      B = zpow (e₁₀ x y + u)
      C = zpow (e₀₁ x y + u)
      D = zpow u

      exp-A : (e₁₁ x y + e₁₀ x y) + (e₀₁ x y + u) ≡ u + ½
      exp-A = trans
        (cong₂ (λ p q → (p + q) + (e₀₁ x y + u)) (e₁₁≡ x y) (e₁₀≡ x y))
        (trans (cong (λ r → (½ + ⅛) + (r + u)) (e₀₁≡ x y)) (drop ½ ⅛ u))

      -- ζ^(½+t) = -ζ^t.

      AD : (A +ᴬ D) ≐ 0ᴬ
      AD j = trans (cong (_+ D j) ((zpow-≡ exp-A ∙ zpow-anti u) j))
                   (+-inverseˡ (D j))

      -- ζ^(⅛+t) + ζ^(-⅛+t) = √2 ζ^t.

      BC₀ : (B +ᴬ C) ≐ (zpow (⅛ + u) +ᴬ zpow ((- ⅛) + u))
      BC₀ j = cong₂ _+_ (zpow-≡ (cong (_+ u) (e₁₀≡ x y)) j)
                        (zpow-≡ (cong (_+ u) (e₀₁≡ x y)) j)

      BC : (B +ᴬ C) ≐ √2· (zpow (t x y))
      BC = BC₀ ∙ ≐-sym (√2·-zpow u) ∙ √2·-map (zpow-≡ (e₀₀≡ x y))

      four : ((A +ᴬ B) +ᴬ (C +ᴬ D)) ≐ √2· (zpow (t x y))
      four j = trans (regroup (A j) (B j) (C j) (D j))
        (trans (cong₂ _+_ (AD j) (BC j))
               (+-identityˡ (√2· (zpow (t x y)) j)))

  -- So the gadget multiplies every amplitude by √2 ...

  amp-gadget : ∀ x z → amp (gadget ξ) x z ≐ √2· (amp ξ x z)
  amp-gadget x z =
    amp-quads x z
    ∙ Σᴮ-cong (λ y → Fq-form x z y
                     ∙ if-cong (hits≡ x y z) (four x y)
                     ∙ √2·-if (hits ξ x y z) (zpow (t x y)))
    ∙ ≐-sym (√2·-Σᴮ (λ y → if hits ξ x y z then zpow (t x y) else 0ᴬ))

  -- ... which the extra normalisation 1/√2 undoes.

  gadget-≋ : gadget ξ ≋ ξ
  gadget-≋ x z = scale-map k (amp-gadget x z) ∙ scale-√2 k (amp ξ x z)


------------------------------------------------------------------------
-- Every path-sum has a tied twin

-- Rewriting the indices along equations.

cast : k ≡ k′ → m ≡ m′ → PathSum n k m → PathSum n k′ m′
cast refl refl ξ = ξ

cast-≋ : (p : k ≡ k′) (q : m ≡ m′) (ξ : PathSum n k m) → cast p q ξ ≋ ξ
cast-≋ refl refl ξ = ≋-refl {ξ = ξ}

-- A path-sum with definition 2.1's normalisation equivalent to ξ.

Twin : PathSum n k m → Set
Twin {n = n} ξ = ∃ λ j → ∃ λ (ξ′ : PathSum n j j) → ξ′ ≋ ξ

private
  twin-via : (ζ : PathSum n k′ m′) (ξ : PathSum n k m) → ζ ≋ ξ →
             Twin ζ → Twin ξ
  twin-via ζ ξ e (j , ξ′ , e′) =
    j , ξ′ , ≋-trans {ξ = ξ′} {ζ = ζ} {χ = ξ} e′ e

  -- k exceeds m by d: d gadgets.

  tie-down : ∀ d (ξ : PathSum n (d ℕ+ m) m) → Twin ξ
  tie-down {m = m} zero    ξ = m , ξ , ≋-refl {ξ = ξ}
  tie-down {m = m} (suc d) ξ =
    twin-via ζ ξ (≋-trans {ξ = ζ} {ζ = gadget ξ} {χ = ξ}
                          (cast-≋ p refl (gadget ξ)) (gadget-≋ ξ))
             (tie-down d ζ)
    where
    p : suc (suc (d ℕ+ m)) ≡ d ℕ+ suc (suc m)
    p = sym (trans (+-suc d (suc m)) (cong suc (+-suc d m)))

    ζ = cast p refl (gadget ξ)

  -- m exceeds k by d: d paddings.

  tie-up : ∀ d (ξ : PathSum n k (d ℕ+ k)) → Twin ξ
  tie-up {k = k} zero    ξ = k , ξ , ≋-refl {ξ = ξ}
  tie-up {k = k} (suc d) ξ =
    twin-via ζ ξ (≋-trans {ξ = ζ} {ζ = pad ξ} {χ = ξ}
                          (cast-≋ refl q (pad ξ)) (pad-≋ ξ))
             (tie-up d ζ)
    where
    q : suc (suc (d ℕ+ k)) ≡ d ℕ+ suc (suc k)
    q = sym (trans (+-suc d (suc k)) (cong suc (+-suc d k)))

    ζ = cast refl q (pad ξ)

tie : (ξ : PathSum n k m) → Twin ξ
tie {k = k} {m = m} ξ = by (≤-total k m)
  where
  by : k ≤ m ⊎ m ≤ k → Twin ξ
  by (inj₁ k≤m) = twin-via ζ ξ (cast-≋ refl e ξ) (tie-up (m ∸ k) ζ)
    where
    e : m ≡ (m ∸ k) ℕ+ k
    e = sym (m∸n+n≡m k≤m)

    ζ = cast refl e ξ
  by (inj₂ m≤k) = twin-via ζ ξ (cast-≋ e refl ξ) (tie-down (k ∸ m) ζ)
    where
    e : k ≡ (k ∸ m) ℕ+ m
    e = sym (m∸n+n≡m m≤k)

    ζ = cast e refl ξ


------------------------------------------------------------------------
-- Moving facts to a name

-- What is proved of gadget ξ or pad ξ holds of a name defined as it.
-- For a closed path-sum, though, asking Agda to see that inside an
-- amplitude makes it unfold the amplitude (minutes, gigabytes).  move
-- takes the equation instead, checked on the path-sums, and its two
-- ends are explicit, so no type is compared before they are known.

move : (P : PathSum n k m → Set) (ξ ζ : PathSum n k m) → ξ ≡ ζ →
       P ξ → P ζ
move P ξ ζ refl p = p


------------------------------------------------------------------------
-- Lemma 4.1's restriction condition is a property of the operator

-- ξ ≋ ζ says √2^k′ amp ξ = √2^k amp ζ; on the diagonal, √2^k ζ⁰ for ξ
-- becomes √2^k′ ζ⁰ for ζ.

Restriction-id-≋ : (ξ : PathSum n k m) (ζ : PathSum n k′ m′) → ξ ≋ ζ →
                   Restriction-id ξ → Restriction-id ζ
Restriction-id-≋ {k = k} {k′ = k′} ξ ζ e rid x =
  scale-injective k (amp ζ x x) (scale k′ (zpow 0ℤ))
    (≐-sym (e x x) ∙ scale-map k′ (rid x) ∙ scale-comm k′ k (zpow 0ℤ))
