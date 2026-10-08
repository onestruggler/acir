------------------------------------------------------------------------
-- Presentations of groups
--
-- What equivalence with |x⟩ ↦ |s⟩ says about a path-sum of order one
--
-- Every path-sum reachable from the hidden shift circuit on |0⟩ is
-- equivalent (definition 2.3) to the specification |x⟩ ↦ |s⟩
-- (PathSum.HiddenShift.Stuck.reachable-≋).  For a path-sum with phase
-- ½F modulo 1 and outputs G modulo 2 (PathSum.HiddenShift.Positive.
-- Values' VTracks), its amplitude from x to z is the signed count of
-- the paths y with G(y) = z, Σ (-1)^F(y), times ζ^0 (amp-cnt), and the
-- equivalence says that this count vanishes off s and is not 0 at s,
-- where it is moreover not even unless the path-sum carries at least
-- two units of normalisation (module Spec).  Pairing the paths that
-- differ in one variable no output reads gives the three facts the
-- progress argument of PathSum.HiddenShift.Positive needs:
--
-- * if F flips with that variable, the pairs cancel and every count is
--   0 -- impossible (flip⇒⊥);
-- * if F does not depend on it, every count is even, so the
--   normalisation is at least 2 and [Elim] applies (flat⇒2≤k);
-- * if the outputs determine the path, every output reached by one
--   path has count ±1, so at most one path exists -- with a path
--   variable left there would be two (endgame).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.Positive.Amplitude (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; not; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; _+_; _*_)
open import Data.Integer.Properties using
  (*-identityʳ; *-zeroˡ; *-assoc; +-identityʳ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (zero; suc; _≤_; s≤s; z≤n)
open import Data.Vec.Base using (_∷_; lookup; tabulate)
open import Data.Vec.Properties using
  (tabulate∘lookup; lookup∘tabulate; tabulate-cong)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Assign using
  ([_]ᶻ; _[_≔_]; same; same-refl; same-true; same-false)
open import PathSum.AssignSum using
  (Σᶻ; Σᶻ-cong; Σᶻ-0; Σᶻ-*; Σᶻ-point; Σᶻ-at; RespectsZ)
open import PathSum.Base using (PathSum; phase; out)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _·ᴬ_; _≐_; Σᴮ-cong; zpow; zpow-cong; scale; scale-map;
   √2·-map; √2·-0ᴬ; √2·-injective; zpow-0≢0ᴬ; 2·≢scale-zpow0; 0ᶠ;
   zpow0-at-0)
open import PathSum.Denotation M₀ using
  (Assign; amp; hits; _≋_; hits-intro; hits-elim; hits-≗³)
open import PathSum.HiddenShift M₀ using (specᴾ; amp-specᴾ)
open import PathSum.HiddenShift.Positive.Boolean
open import PathSum.HiddenShift.Positive.Values M₀ using
  (VTracks; tracks; tab-≔)
open import PathSum.HiddenShift.Sign M₀ using (1ᴬ; zpow-½-bit; Σᴮ-ᶻ)
open import PathSum.HiddenShift.Track M₀ using (phase-at; out-at)
open import PathSum.Polynomial using (sgn; eval)

open +-*-Solver using (solve; con; _:+_; _:*_; _:=_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Reduction M using (½)

private
  variable
    N k m : ℕ


------------------------------------------------------------------------
-- Amplitudes are signed counts

-- The signed count of the paths from x to z.

cnt : PathSum N k m → (Pt m → Bool) → Assign N → Assign N → Assign m → ℤ
cnt ξ F x z y = if hits ξ x y z then sgn (F (tabulate y)) else 0ℤ

cnt-resp : (ξ : PathSum N k m) (F : Pt m → Bool) (x z : Assign N) →
           RespectsZ (cnt ξ F x z)
cnt-resp ξ F x z g h g≗h = cong₂ (λ b p → if b then sgn (F p) else 0ℤ)
  (hits-≗³ ξ (λ _ → refl) g≗h (λ _ → refl)) (tabulate-cong g≗h)

amp-cnt : {ξ : PathSum N k m} {F : Pt m → Bool}
          {G : Fin N → Pt m → Bool} → VTracks ξ F G →
          ∀ x z → amp ξ x z ≐ (Σᶻ (cnt ξ F x z) ·ᴬ 1ᴬ)
amp-cnt {ξ = ξ} {F} tr x z i = trans
  (Σᴮ-cong {f = λ y → if hits ξ x y z then zpow (eval (phase ξ) x y) else 0ᴬ}
           {g = λ y → cnt ξ F x z y ·ᴬ 1ᴬ}
           (λ y → term y (hits ξ x y z)) i)
  (Σᴮ-ᶻ (cnt ξ F x z) (cnt-resp ξ F x z) 1ᴬ i)
  where
  term : ∀ y b → (if b then zpow (eval (phase ξ) x y) else 0ᴬ) ≐
                 ((if b then sgn (F (tabulate y)) else 0ℤ) ·ᴬ 1ᴬ)
  term y true  i = trans
    (zpow-cong {eval (phase ξ) x y} {½ * [ F (tabulate y) ]ᶻ}
               (phase-at (tracks tr) x y) i)
    (zpow-½-bit (F (tabulate y)) i)
  term y false i = sym (*-zeroˡ (1ᴬ i))

-- A path reaches z exactly when G takes the value z on it.

module Paths {ξ : PathSum N k m} {F : Pt m → Bool}
             {G : Fin N → Pt m → Bool} (tr : VTracks ξ F G) where

  hits-val : ∀ x y z → hits ξ x y z ≡ true → ∀ w → G w (tabulate y) ≡ z w
  hits-val x y z h w =
    trans (sym (out-at (tracks tr) w x y)) (hits-elim ξ x y z h w)

  hits-from : ∀ x y z → (∀ w → G w (tabulate y) ≡ z w) → hits ξ x y z ≡ true
  hits-from x y z h =
    hits-intro ξ x y z (λ w → trans (out-at (tracks tr) w x y) (h w))

  hits-same : ∀ x y y′ z → (∀ w → G w (tabulate y) ≡ G w (tabulate y′)) →
              hits ξ x y z ≡ hits ξ x y′ z
  hits-same x y y′ z h = go (hits ξ x y z) (hits ξ x y′ z) refl refl
    where
    go : ∀ b b′ → hits ξ x y z ≡ b → hits ξ x y′ z ≡ b′ → b ≡ b′
    go true  true  _ _ = refl
    go false false _ _ = refl
    go true  false e e′ = ⊥-elim (t≢f (trans (sym (hits-from x y′ z
      (λ w → trans (sym (h w)) (hits-val x y z e w)))) e′))
      where
      t≢f : true ≢ false
      t≢f ()
    go false true  e e′ = ⊥-elim (t≢f (trans (sym (hits-from x y z
      (λ w → trans (h w) (hits-val x y′ z e′ w)))) e))
      where
      t≢f : true ≢ false
      t≢f ()

open Paths public


------------------------------------------------------------------------
-- Equivalence with the specification

private
  scale-0ᴬ : ∀ j → scale j 0ᴬ ≐ 0ᴬ
  scale-0ᴬ zero    i = refl
  scale-0ᴬ (suc j) i = trans (√2·-map (scale-0ᴬ j) i) (√2·-0ᴬ i)

  scale-zpow0≢0 : ∀ j → ¬ (scale j (zpow 0ℤ) ≐ 0ᴬ)
  scale-zpow0≢0 zero    eq = zpow-0≢0ᴬ eq
  scale-zpow0≢0 (suc j) eq = scale-zpow0≢0 j
    (√2·-injective (scale j (zpow 0ℤ)) 0ᴬ
      (λ i → trans (eq i) (sym (√2·-0ᴬ i))))

  at-least-2 : ∀ j (a : Amp) → ((+ 2) ·ᴬ a) ≐ scale j (zpow 0ℤ) → 2 ≤ j
  at-least-2 zero          a h = ⊥-elim (2·≢scale-zpow0 a 0 (s≤s z≤n) h)
  at-least-2 (suc zero)    a h =
    ⊥-elim (2·≢scale-zpow0 a 1 (s≤s (s≤s z≤n)) h)
  at-least-2 (suc (suc j)) a h = s≤s (s≤s z≤n)

  sgn≢0 : ∀ b → sgn b ≢ 0ℤ
  sgn≢0 false ()
  sgn≢0 true  ()

  dbl : ∀ a → a + a ≡ (+ 2) * a
  dbl = solve 1 (λ a → a :+ a := con (+ 2) :* a) refl

  if-0 : ∀ b {a : ℤ} → a ≡ 0ℤ → (if b then 0ℤ else a) ≡ 0ℤ
  if-0 true  _ = refl
  if-0 false e = e

  pair-flip : ∀ h a →
              (if h then sgn a else 0ℤ) + (if h then sgn (not a) else 0ℤ) ≡ 0ℤ
  pair-flip true  false = refl
  pair-flip true  true  = refl
  pair-flip false a     = refl

  pair-even : ∀ b (u v : ℤ) → v ≡ u →
              (if b then 0ℤ else (u + v)) ≡ (+ 2) * (if b then 0ℤ else u)
  pair-even true  u v e = refl
  pair-even false u v e = trans (cong (λ t → u + t) e) (dbl u)

module Spec {ξ : PathSum N k m} {F : Pt m → Bool}
            {G : Fin N → Pt m → Bool} (tr : VTracks ξ F G)
            (s : Assign N) (eqv : ξ ≋ specᴾ s) where

  -- The column at any input, read through the count.

  col : ∀ x z → (Σᶻ (cnt ξ F x z) ·ᴬ 1ᴬ) ≐ scale k (if same s z then 1ᴬ else 0ᴬ)
  col x z i = trans (sym (amp-cnt tr x z i))
                    (trans (eqv x z i) (scale-map k (amp-specᴾ s x z) i))

  col-s : ∀ x → (Σᶻ (cnt ξ F x s) ·ᴬ 1ᴬ) ≐ scale k 1ᴬ
  col-s x = subst
    (λ b → (Σᶻ (cnt ξ F x s) ·ᴬ 1ᴬ) ≐ scale k (if b then 1ᴬ else 0ᴬ))
                  (same-refl s) (col x s)

  -- Not 0 at s, 0 elsewhere, and even at s only with two units of
  -- normalisation.

  nonzero : ∀ x → Σᶻ (cnt ξ F x s) ≢ 0ℤ
  nonzero x e = scale-zpow0≢0 k (λ i → trans (sym (col-s x i))
    (trans (cong (_* 1ᴬ i) e) (*-zeroˡ (1ᴬ i))))

  zero-off : ∀ x z → same s z ≡ false → Σᶻ (cnt ξ F x z) ≡ 0ℤ
  zero-off x z e = trans (sym (*-identityʳ (Σᶻ (cnt ξ F x z))))
    (trans (cong (Σᶻ (cnt ξ F x z) *_) (sym zpow0-at-0))
      (trans (subst (λ b → (Σᶻ (cnt ξ F x z) ·ᴬ 1ᴬ) ≐
                           scale k (if b then 1ᴬ else 0ᴬ)) e (col x z) 0ᶠ)
             (scale-0ᴬ k 0ᶠ)))

  even⇒2≤k : ∀ x b → Σᶻ (cnt ξ F x s) ≡ (+ 2) * b → 2 ≤ k
  even⇒2≤k x b e = at-least-2 k (b ·ᴬ 1ᴬ) (λ i →
    trans (sym (*-assoc (+ 2) b (1ᴬ i)))
      (trans (cong (_* 1ᴬ i) (sym e)) (col-s x i)))

  ----------------------------------------------------------------------
  -- Pairing the paths across a variable no output reads

  private
    x₀ : Assign N
    x₀ _ = false

    -- The two paths of a pair reach the same outputs.
    pair-hits : (j : Fin m) → (∀ w → Indep (G w) j) → ∀ x y z →
                hits ξ x (y [ j ≔ true ]) z ≡ hits ξ x (y [ j ≔ false ]) z
    pair-hits j ind x y z = hits-same tr x (y [ j ≔ true ]) (y [ j ≔ false ]) z
      (λ w → trans (cong (G w) (tab-≔ y j true))
        (trans (ind w (tabulate y)) (cong (G w) (sym (tab-≔ y j false)))))

  -- If F flips with the variable, every count vanishes: impossible.

  flip⇒⊥ : (j : Fin m) → (∀ w → Indep (G w) j) →
           (∀ p → F (set p j true) ≡ not (F (set p j false))) → ⊥
  flip⇒⊥ j ind flp = nonzero x₀ (trans
    (Σᶻ-at j (cnt ξ F x₀ s) (cnt-resp ξ F x₀ s))
    (trans (Σᶻ-cong (λ y → if-0 (y j) (term y))) Σᶻ-0))
    where
    term : ∀ y → cnt ξ F x₀ s (y [ j ≔ false ]) +
                 cnt ξ F x₀ s (y [ j ≔ true ]) ≡ 0ℤ
    term y = trans
      (cong₂ (λ h a → (if hits ξ x₀ (y [ j ≔ false ]) s
                       then sgn (F (tabulate (y [ j ≔ false ]))) else 0ℤ) +
                      (if h then sgn a else 0ℤ))
             (pair-hits j ind x₀ y s)
             (trans (cong F (tab-≔ y j true))
               (trans (flp (tabulate y))
                 (cong (λ p → not (F p)) (sym (tab-≔ y j false))))))
      (pair-flip (hits ξ x₀ (y [ j ≔ false ]) s)
                 (F (tabulate (y [ j ≔ false ]))))

  -- If F does not depend on it, the count at s is even: [Elim] has the
  -- normalisation it consumes.

  flat⇒2≤k : (j : Fin m) → (∀ w → Indep (G w) j) → Indep F j → 2 ≤ k
  flat⇒2≤k j ind flt = even⇒2≤k x₀
    (Σᶻ (λ y → if y j then 0ℤ else cnt ξ F x₀ s (y [ j ≔ false ])))
    (trans (Σᶻ-at j (cnt ξ F x₀ s) (cnt-resp ξ F x₀ s))
      (trans (Σᶻ-cong (λ y → pair-even (y j) _ _ (term y)))
             (Σᶻ-* (+ 2) (λ y → if y j then 0ℤ
                                else cnt ξ F x₀ s (y [ j ≔ false ])))))
    where
    term : ∀ y → cnt ξ F x₀ s (y [ j ≔ true ]) ≡ cnt ξ F x₀ s (y [ j ≔ false ])
    term y = cong₂ (λ h a → if h then sgn a else 0ℤ)
      (pair-hits j ind x₀ y s)
      (trans (cong F (tab-≔ y j true))
        (trans (flt (tabulate y)) (cong F (sym (tab-≔ y j false)))))

  -- If the outputs determine the path, there is only one.

  endgame : (∀ p p′ → (∀ w → G w p ≡ G w p′) → p ≡ p′) →
            (p₀ p₁ : Pt m) → p₀ ≢ p₁ → ⊥
  endgame inj p₀ p₁ p₀≢p₁ =
    p₀≢p₁ (inj p₀ p₁ (λ w → trans (sym (on p₀ w)) (on p₁ w)))
    where
    -- The count at the output of a path is that path's sign.
    point : ∀ p → Σᶻ (cnt ξ F x₀ (λ w → G w p)) ≡ sgn (F p)
    point p = trans (Σᶻ-point f (cnt-resp ξ F x₀ z) (lookup p))
      (trans (cong₂ _+_ here (trans (Σᶻ-cong rest) Σᶻ-0))
             (+-identityʳ (sgn (F p))))
      where
      z : Assign N
      z w = G w p

      f : Assign _ → ℤ
      f = cnt ξ F x₀ z

      here : f (lookup p) ≡ sgn (F p)
      here = trans (cong (λ b → if b then sgn (F (tabulate (lookup p))) else 0ℤ)
                         (hits-from tr x₀ (lookup p) z
                            (λ w → cong (G w) (tabulate∘lookup p))))
                   (cong (λ t → sgn (F t)) (tabulate∘lookup p))

      rest : ∀ y → (if same (lookup p) y then 0ℤ else f y) ≡ 0ℤ
      rest y = go (same (lookup p) y) refl
        where
        off : ∀ h → hits ξ x₀ y z ≡ h → same (lookup p) y ≡ false → f y ≡ 0ℤ
        off false e _  = cong (λ b → if b then sgn (F (tabulate y)) else 0ℤ) e
        off true  e ne = ⊥-elim (same-false (lookup p) y ne (λ j →
          trans (cong (λ t → lookup t j)
                      (sym (inj (tabulate y) p (hits-val tr x₀ y z e))))
                (lookup∘tabulate y j)))

        go : ∀ b → same (lookup p) y ≡ b → (if b then 0ℤ else f y) ≡ 0ℤ
        go true  _ = refl
        go false e = off (hits ξ x₀ y z) refl e

    -- So every path's output is s.
    on : ∀ p w → s w ≡ G w p
    on p = go (same s (λ w → G w p)) refl
      where
      go : ∀ b → same s (λ w → G w p) ≡ b → ∀ w → s w ≡ G w p
      go true  e = same-true s (λ w → G w p) e
      go false e = ⊥-elim (sgn≢0 (F p) (trans (sym (point p))
                                              (zero-off x₀ (λ w → G w p) e)))
