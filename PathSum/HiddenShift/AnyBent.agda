------------------------------------------------------------------------
-- Presentations of groups
--
-- The quantum hidden shift algorithm for any bent function (Amy, QPL
-- 2018, section 5.2)
--
-- Section 5.2: "given oracles O_f′ : |x⟩ ↦ f(x + s)|x⟩ and
-- O_f̃ : |x⟩ ↦ f̃(x)|x⟩ for the shifted and dual bent functions f′, f̃
-- ..., the circuit H^{⊗n} O_f̃ H^{⊗n} O_f′ H^{⊗n} is known [28] to
-- implement the mapping |0⟩ ↦ |s⟩".  PathSum.HiddenShift proves this
-- for the Maiorana-McFarland functions, the ones the paper's
-- benchmarks use; this module proves it for every bent function, from
-- the definition of bentness alone (PathSum.HiddenShift.Bent).
--
-- The statement.  E and Ẽ are any integer polynomials in the 2m inputs,
-- read as Boolean functions modulo 2 (boolᴾ) -- the exponents of the
-- oracles' signs -- such that boolᴾ E is bent with dual boolᴾ Ẽ.  The
-- circuit is HiddenShift's composite (definition 2.6) of the same
-- layers, HSᵇ E Ẽ s = Hᴾ ∘ Oᴾ Ẽ ∘ Hᴾ ∘ Oᴾ (shiftᴾ s E) ∘ Hᴾ: the oracle of
-- the shifted function f′ = f(· ⊕ s) acts first, the oracle of the
-- dual second, as in the paper (operators compose right to left).  Its
-- column at the input 0 is √2^K |s⟩, K = 3n its normalisation, so the
-- normalised amplitude from |0⟩ to |z⟩ is 1 at z = s and 0 elsewhere
-- (hidden-shift-bent); equivalently it agrees with the specification
-- |x⟩ ↦ |s⟩ on that column (hidden-shift-bent-spec), and the circuit on
-- |0⟩ (PathSum.HiddenShift.Simulation's at0, every input replaced by
-- 0) is equivalent to the specification in the sense of definition 2.3
-- (hidden-shift-bent-≋), as HiddenShift.Simulation states it for the
-- Maiorana-McFarland case.
--
-- The proof is HiddenShift's, layer by layer by proposition 2.7, the
-- column staying an integer multiple of ζ^0:
--
--    1  ↦  (-1)^{f(u ⊕ s)}  ↦  2^m (-1)^{f̃(v) + s·v}  ↦  2^m (-1)^{s·v}
--       ↦  2^m 2^n [z = s],
--
-- with the one fact about f, the transform of the shifted function
-- (Bent.walsh-shift), derived from bentness instead of computed for
-- g(x) + x·y.  The order of the oracles is the paper's: the dual's
-- oracle cancels the sign the transform of f′ leaves.  (In the other
-- order the signs (-1)^{f(v) + f(v ⊕ s)} would remain, which need not
-- be a character; that observation is not formalised.)
--
-- Every bent function.  The theorem is about oracles given by
-- polynomials, as path-sums need, but that is no restriction: every
-- Boolean function f is the reading modulo 2 of a polynomial,
-- polyᴮ f (PathSum.Polynomial.Interpolate, by interpolation at the head
-- variable; bool-polyᴮ).  So for every bent pair f, f̃ the circuit with
-- the oracles of polyᴮ f, shifted, and polyᴮ f̃ maps |0⟩ to |s⟩
-- (hidden-shift-any, hidden-shift-any-≋).  The one hypothesis besides
-- bentness is that f and f̃ read their argument only through its values
-- (RespectsB; see PathSum.HiddenShift.Bent), which every function
-- written in terms of the bits of its argument satisfies.
--
-- The Maiorana-McFarland case is an instance (mm-bentᴾ, from
-- Bent.mm-bent): HSᵇ (mmᴾ g) (dualᴾ g) s is HiddenShift's HS g s by
-- definition, and hidden-shift-mm is HiddenShift's hidden-shift
-- recovered from the general theorem.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.AnyBent (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; _xor_; if_then_else_)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; _*_)
open import Data.Integer.Properties using
  (*-identityʳ; *-zeroʳ; *-zeroˡ; *-comm; pos-*)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (zero; suc)
  renaming (_+_ to _ℕ+_; _^_ to _ℕ^_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)

import Data.Nat.Properties as ℕ
import Data.Nat.Solver as ℕSolver

open import PathSum.Assign using (same)
open import PathSum.AssignSum using (Σᶻ; Σᶻ-cong; Σᶻ-*; RespectsZ)
open import PathSum.Base using (PathSum)
open import PathSum.Compose using (_∘ᴾ_)
open import PathSum.Compose.Properties M₀ using
  (applyᴾ-cong; prop-2-7ᶜ)
open import PathSum.Compose.Sum M₀ using (scale-exp)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _≐_; zpow; scale; scale-map)
open import PathSum.Denotation M₀ using (Assign; amp; _≋_)
open import PathSum.HiddenShift M₀ using
  (Hᴾ; Oᴾ; specᴾ; boolᴾ; boolᴾ-resp; mmᴾ; dualᴾ; shiftᴾ; bool-mmᴾ;
   bool-dualᴾ; bool-shiftᴾ; amp-Hᴾ; applyᴾ-Hᴾ; applyᴾ-Oᴾ; amp-specᴾ;
   hs-norm; HS; scale-twice; scale-0ᴬ; none)
open import PathSum.HiddenShift.Bent using
  (Bent; Bent-cong; walsh-shift; mm-bent)
open import PathSum.HiddenShift.Sign M₀ using (⌈_⌉)
open import PathSum.HiddenShift.Simulation M₀ using (at0; amp-at0)
open import PathSum.HiddenShift.Walsh using
  (0ᵃ; _⊕ᵃ_; RespectsB; dot; dot-cong; dot-0ˡ; sgn-xor; sgn-absorb;
   character-shift; mm; dual)
open import PathSum.Polynomial using (Poly; sgn)
open import PathSum.Polynomial.Interpolate using (polyᴮ; odd-polyᴮ)

open +-*-Solver using (solve; _:*_; _:=_)

private
  variable
    n m : ℕ


------------------------------------------------------------------------
-- The circuit, for any pair of oracles

-- H^{⊗n} O_Ẽ H^{⊗n} O_{E(· ⊕ s)} H^{⊗n}, read right to left: the
-- shifted oracle first, the dual's second.

HSᵇ : Poly (m ℕ+ m) 0 → Poly (m ℕ+ m) 0 → Assign (m ℕ+ m) →
      PathSum (m ℕ+ m) (hs-norm (m ℕ+ m)) (hs-norm (m ℕ+ m))
HSᵇ {m} E Ẽ s = Hᴾ ∘ᴾ Oᴾ Ẽ ∘ᴾ Hᴾ ∘ᴾ Oᴾ (shiftᴾ s E) ∘ᴾ Hᴾ


------------------------------------------------------------------------
-- The column at 0

module _ {m : ℕ} (E Ẽ : Poly (m ℕ+ m) 0) (s : Assign (m ℕ+ m))
         (bent : Bent m (boolᴾ E) (boolᴾ Ẽ)) where

  private
    f f̃ : Assign (m ℕ+ m) → Bool
    f = boolᴾ E
    f̃ = boolᴾ Ẽ

    P : ℤ
    P = + (2 ℕ^ m)

    swap : ∀ a p t → a * (p * t) ≡ p * (a * t)
    swap = solve 3 (λ a p t → a :* (p :* t) := p :* (a :* t)) refl

    -- The column after each layer.

    c₁ c₂ c₃ c₄ c₅ : Assign (m ℕ+ m) → ℤ
    c₁ _ = 1ℤ
    c₂ u = sgn (f (u ⊕ᵃ s))
    c₃ v = P * sgn (f̃ v xor dot s v)
    c₄ v = P * sgn (dot s v)
    c₅ z = P * (if same s z then + (2 ℕ^ (m ℕ+ m)) else 0ℤ)

    c₂-resp : RespectsZ c₂
    c₂-resp a b h = cong sgn (boolᴾ-resp E (a ⊕ᵃ s) (b ⊕ᵃ s)
                                         (λ i → cong (_xor s i) (h i)))

    c₃-resp : RespectsZ c₃
    c₃-resp a b h = cong (λ t → P * sgn t) (cong₂ _xor_
      (boolᴾ-resp Ẽ a b h)
      (dot-cong {u = s} {u′ = s} {v = a} {v′ = b} (λ _ → refl) h))

    c₄-resp : RespectsZ c₄
    c₄-resp a b h = cong (λ t → P * sgn t)
      (dot-cong {u = s} {u′ = s} {v = a} {v′ = b} (λ _ → refl) h)

    -- The first layer spreads |0⟩ uniformly.

    st₁ : ∀ u → amp (Hᴾ {m ℕ+ m}) 0ᵃ u ≐ ⌈ c₁ ⌉ u
    st₁ u i = trans (amp-Hᴾ 0ᵃ u i)
                    (cong (λ b → sgn b * zpow 0ℤ i) (dot-0ˡ u))

    -- The oracle of f′ = f(· ⊕ s) signs the uniform column.

    st₂ : ∀ u → amp (Oᴾ (shiftᴾ s E) ∘ᴾ Hᴾ) 0ᵃ u ≐ ⌈ c₂ ⌉ u
    st₂ u i = trans (prop-2-7ᶜ (Oᴾ (shiftᴾ s E)) Hᴾ 0ᵃ u i)
      (trans (applyᴾ-cong (Oᴾ (shiftᴾ s E)) {amp Hᴾ 0ᵃ} {⌈ c₁ ⌉} st₁ u i)
        (trans (applyᴾ-Oᴾ (shiftᴾ s E) c₁ (λ _ _ _ → refl) u i)
               (cong (λ t → t * zpow 0ℤ i) sign)))
      where
      sign : sgn (boolᴾ (shiftᴾ s E) u) * 1ℤ ≡ c₂ u
      sign = trans (*-identityʳ _) (cong sgn (bool-shiftᴾ s E u))

    -- The Walsh transform of f′: 2^m f̃ times the character of s, by
    -- bentness.

    st₃ : ∀ v → amp (Hᴾ ∘ᴾ Oᴾ (shiftᴾ s E) ∘ᴾ Hᴾ) 0ᵃ v ≐ ⌈ c₃ ⌉ v
    st₃ v i = trans (prop-2-7ᶜ Hᴾ (Oᴾ (shiftᴾ s E) ∘ᴾ Hᴾ) 0ᵃ v i)
      (trans (applyᴾ-cong Hᴾ {amp (Oᴾ (shiftᴾ s E) ∘ᴾ Hᴾ) 0ᵃ} {⌈ c₂ ⌉}
                          st₂ v i)
        (trans (applyᴾ-Hᴾ c₂ c₂-resp v i)
               (cong (λ t → t * zpow 0ℤ i) walsh)))
      where
      walsh : Σᶻ (λ u → sgn (dot u v) * c₂ u) ≡ c₃ v
      walsh = trans
        (Σᶻ-cong (λ u → trans (*-comm (sgn (dot u v)) (c₂ u))
                              (sym (sgn-xor (f (u ⊕ᵃ s)) (dot u v)))))
        (walsh-shift {m} f f̃ (boolᴾ-resp E) bent s v)

    -- The oracle of the dual cancels f̃, leaving the character of s.

    st₄ : ∀ v → amp (Oᴾ Ẽ ∘ᴾ Hᴾ ∘ᴾ Oᴾ (shiftᴾ s E) ∘ᴾ Hᴾ) 0ᵃ v ≐ ⌈ c₄ ⌉ v
    st₄ v i = trans
      (prop-2-7ᶜ (Oᴾ Ẽ) (Hᴾ ∘ᴾ Oᴾ (shiftᴾ s E) ∘ᴾ Hᴾ) 0ᵃ v i)
      (trans (applyᴾ-cong (Oᴾ Ẽ) {amp (Hᴾ ∘ᴾ Oᴾ (shiftᴾ s E) ∘ᴾ Hᴾ) 0ᵃ}
                          {⌈ c₃ ⌉} st₃ v i)
        (trans (applyᴾ-Oᴾ Ẽ c₃ c₃-resp v i)
               (cong (λ t → t * zpow 0ℤ i) sign)))
      where
      sign : sgn (f̃ v) * c₃ v ≡ c₄ v
      sign = trans (swap (sgn (f̃ v)) P (sgn (f̃ v xor dot s v)))
                   (cong (P *_) (sgn-absorb (f̃ v) (dot s v)))

    -- The last layer interferes the character of s into |s⟩.

    st₅ : ∀ z → amp (HSᵇ {m} E Ẽ s) 0ᵃ z ≐ ⌈ c₅ ⌉ z
    st₅ z i = trans
      (prop-2-7ᶜ Hᴾ (Oᴾ Ẽ ∘ᴾ Hᴾ ∘ᴾ Oᴾ (shiftᴾ s E) ∘ᴾ Hᴾ) 0ᵃ z i)
      (trans (applyᴾ-cong Hᴾ
               {amp (Oᴾ Ẽ ∘ᴾ Hᴾ ∘ᴾ Oᴾ (shiftᴾ s E) ∘ᴾ Hᴾ) 0ᵃ}
               {⌈ c₄ ⌉} st₄ z i)
        (trans (applyᴾ-Hᴾ c₄ c₄-resp z i)
               (cong (λ t → t * zpow 0ℤ i) orth)))
      where
      orth : Σᶻ (λ v → sgn (dot v z) * c₄ v) ≡ c₅ z
      orth = trans
        (Σᶻ-cong (λ v → trans (swap (sgn (dot v z)) P (sgn (dot s v)))
          (cong (P *_) (sym (sgn-xor (dot v z) (dot s v))))))
        (trans (Σᶻ-* P (λ v → sgn (dot v z xor dot s v)))
               (cong (P *_) (character-shift s z)))

    -- 2^m 2^n is √2^(3n).

    norm≡ : hs-norm (m ℕ+ m) ≡ (m ℕ+ (m ℕ+ m)) ℕ+ (m ℕ+ (m ℕ+ m))
    norm≡ = ℕSolver.+-*-Solver.solve 1 (λ a →
      ((((a ℕSolver.+-*-Solver.:+ a) ℕSolver.+-*-Solver.:+
         ℕSolver.+-*-Solver.con 0) ℕSolver.+-*-Solver.:+
        (a ℕSolver.+-*-Solver.:+ a)) ℕSolver.+-*-Solver.:+
        ℕSolver.+-*-Solver.con 0) ℕSolver.+-*-Solver.:+
        (a ℕSolver.+-*-Solver.:+ a)
      ℕSolver.+-*-Solver.:=
      (a ℕSolver.+-*-Solver.:+ (a ℕSolver.+-*-Solver.:+ a))
        ℕSolver.+-*-Solver.:+
      (a ℕSolver.+-*-Solver.:+ (a ℕSolver.+-*-Solver.:+ a))) refl m

    final : ∀ b l → (P * (if b then + (2 ℕ^ (m ℕ+ m)) else 0ℤ)) * zpow 0ℤ l ≡
                    (if b then scale (hs-norm (m ℕ+ m)) (zpow 0ℤ) else 0ᴬ) l
    final true  l = sym (trans (scale-exp (zpow 0ℤ) norm≡ l)
      (trans (scale-twice (m ℕ+ (m ℕ+ m)) (zpow 0ℤ) l)
             (cong (_* zpow 0ℤ l)
                   (trans (cong +_ (ℕ.^-distribˡ-+-* 2 m (m ℕ+ m)))
                          (pos-* (2 ℕ^ m) (2 ℕ^ (m ℕ+ m)))))))
    final false l =
      trans (cong (_* zpow 0ℤ l) (*-zeroʳ P)) (*-zeroˡ (zpow 0ℤ l))

  -- The hidden shift algorithm for any bent function: from |0⟩ the
  -- circuit reaches |s⟩, with amplitude √2^K before the normalisation
  -- 1/√2^K, and nothing else.

  hidden-shift-bent : (z : Assign (m ℕ+ m)) →
                      amp (HSᵇ {m} E Ẽ s) 0ᵃ z ≐
                      (if same s z then scale (hs-norm (m ℕ+ m)) (zpow 0ℤ)
                       else 0ᴬ)
  hidden-shift-bent z i = trans (st₅ z i) (final (same s z) i)

  -- The same against the specification |x⟩ ↦ |s⟩ ...

  hidden-shift-bent-spec : (x z : Assign (m ℕ+ m)) →
                           amp (HSᵇ {m} E Ẽ s) 0ᵃ z ≐
                           scale (hs-norm (m ℕ+ m)) (amp (specᴾ s) x z)
  hidden-shift-bent-spec x z i = trans (hidden-shift-bent z i)
    (sym (trans (scale-map (hs-norm (m ℕ+ m)) (amp-specᴾ s x z) i)
                (pick (same s z) i)))
    where
    pick : ∀ b → scale (hs-norm (m ℕ+ m)) (if b then zpow 0ℤ else 0ᴬ) ≐
                 (if b then scale (hs-norm (m ℕ+ m)) (zpow 0ℤ) else 0ᴬ)
    pick true  l = refl
    pick false l = scale-0ᴬ (hs-norm (m ℕ+ m)) l

  -- ... and the circuit on |0⟩ is the specification, in the sense of
  -- definition 2.3.

  hidden-shift-bent-≋ : at0 (HSᵇ {m} E Ẽ s) ≋ specᴾ s
  hidden-shift-bent-≋ x z i =
    trans (amp-at0 (HSᵇ {m} E Ẽ s) x z i) (hidden-shift-bent-spec x z i)


------------------------------------------------------------------------
-- The Maiorana-McFarland functions, an instance

-- g(x) + x·y is bent with dual g(y) + x·y, read off the polynomials.

mm-bentᴾ : (g : Poly m 0) → Bent m (boolᴾ (mmᴾ g)) (boolᴾ (dualᴾ g))
mm-bentᴾ {m} g =
  Bent-cong {m = m} (λ u → sym (bool-mmᴾ g u)) (λ u → sym (bool-dualᴾ g u))
            (mm-bent (boolᴾ g) (boolᴾ-resp g))

-- The circuit is PathSum.HiddenShift's, by definition, and so is its
-- theorem.

HSᵇ-mm : (g : Poly m 0) (s : Assign (m ℕ+ m)) →
         HSᵇ {m} (mmᴾ g) (dualᴾ g) s ≡ HS g s
HSᵇ-mm {m} g s = refl

hidden-shift-mm : (g : Poly m 0) (s z : Assign (m ℕ+ m)) →
                  amp (HS g s) 0ᵃ z ≐
                  (if same s z then scale (hs-norm (m ℕ+ m)) (zpow 0ℤ) else 0ᴬ)
hidden-shift-mm {m} g s =
  hidden-shift-bent {m} (mmᴾ g) (dualᴾ g) s (mm-bentᴾ g)

------------------------------------------------------------------------
-- Every bent pair of Boolean functions

-- The oracles' exponents may be any polynomials reading as f and f̃:
-- every Boolean function is one's reading.

bool-polyᴮ : (f : Assign n → Bool) → RespectsB f →
             ∀ x → boolᴾ (polyᴮ f) x ≡ f x
bool-polyᴮ f resp x = odd-polyᴮ f resp x none

-- So the hidden shift algorithm works for every bent function f with
-- dual f̃: with the oracles of polyᴮ f (shifted) and polyᴮ f̃, |0⟩ ↦ |s⟩.

module _ {m : ℕ} (f f̃ : Assign (m ℕ+ m) → Bool)
         (f-resp : RespectsB f) (f̃-resp : RespectsB f̃)
         (bent : Bent m f f̃) (s : Assign (m ℕ+ m)) where

  private
    bentᴾ : Bent m (boolᴾ (polyᴮ f)) (boolᴾ (polyᴮ f̃))
    bentᴾ = Bent-cong {m = m} (λ x → sym (bool-polyᴮ f f-resp x))
                              (λ a → sym (bool-polyᴮ f̃ f̃-resp a)) bent

  hidden-shift-any : (z : Assign (m ℕ+ m)) →
                     amp (HSᵇ {m} (polyᴮ f) (polyᴮ f̃) s) 0ᵃ z ≐
                     (if same s z then scale (hs-norm (m ℕ+ m)) (zpow 0ℤ)
                      else 0ᴬ)
  hidden-shift-any = hidden-shift-bent {m} (polyᴮ f) (polyᴮ f̃) s bentᴾ

  hidden-shift-any-≋ : at0 (HSᵇ {m} (polyᴮ f) (polyᴮ f̃) s) ≋ specᴾ s
  hidden-shift-any-≋ =
    hidden-shift-bent-≋ {m} (polyᴮ f) (polyᴮ f̃) s bentᴾ
