------------------------------------------------------------------------
-- Presentations of groups
--
-- Renumbering path variables preserves the denotation, and
-- proposition 3.1 for the rules at any path variable
--
-- Definition 2.1 sums over every assignment y ∈ Z₂^m to the path
-- variables, and such a sum does not depend on how the variables are
-- numbered.  That is the one semantic fact the general rules of
-- PathSum.Anywhere need: front j ξ ≋ ξ (front-≋).  Every general step
-- is a head step on some front j ξ, whose soundness is
-- PathSum.Denotation.⟶-sound unchanged, so proposition 3.1 for the
-- general calculus follows by transitivity (⟶ᵍ-sound, ⟶ᵍ*-sound).
-- The same argument works for any sound relation (Anywhere-sound),
-- and unions of sound relations are sound (∪ᴿ-sound), which is what
-- rules added later need.  No well-formedness is needed: renumbering
-- is sound for every path-sum.
--
-- The sum over assignments to m + 1 variables splits, by definition,
-- at the first one.  Σᴮ-insert splits it at the j-th instead, as a
-- sum of the two sums with y_j fixed to true and to false; this is
-- the amplitude analogue of Polynomial.Properties.Σsub-splitAt.  The
-- rest is bookkeeping: renumbering commutes with evaluation
-- (Reorder.eval-front), so it does not change which paths hit an
-- output (hits-front) nor the phase they carry, and the amplitude of
-- front j ξ is the amplitude of ξ summed in another order
-- (amp-front).  Denotation's helpers for outputs are private, so the
-- statement about hits goes through its public outBit and
-- hits-intro/hits-elim; PathSum.Denotation itself is not changed.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.Anywhere.Sound (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; not; if_then_else_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Integer.Base using (+_; _+_)
open import Data.Integer.Divisibility.Signed using (_∣?_)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (zero; suc)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Nullary.Negation using (contradiction)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Base
open import PathSum.Cyclotomic M₀ using
  (Amp; _≐_; _+ᴬ_; 0ᴬ; Σᴮ; Σᴮ-cong; extend; Respects; zpow; scale-map)
open import PathSum.Denotation M₀ using
  (Assign; hits; amp; outBit; _≋_; ≋-refl; ≋-sym; ≋-trans; ⟶-sound;
   hits-intro; hits-elim; hits-≗³)
open import PathSum.Polynomial using (eval)
open import PathSum.Polynomial.Properties using (eval-cong)
open import PathSum.Reorder
open import PathSum.Anywhere M

open +-*-Solver using (solve; _:+_; _:=_)

private
  variable
    n k m k′ m′ k″ m″ : ℕ


------------------------------------------------------------------------
-- Sums over assignments, split at any variable

private
  extend-cong : ∀ {k} (b : Bool) (g h : Fin k → Bool) →
                (∀ j → g j ≡ h j) → ∀ j → extend b g j ≡ extend b h j
  extend-cong b g h g≗h zero    = refl
  extend-cong b g h g≗h (suc j) = g≗h j

  shuffle : ∀ p q r s → (p + q) + (r + s) ≡ (p + r) + (q + s)
  shuffle = solve 4 (λ p q r s →
    (p :+ q) :+ (r :+ s) := (p :+ r) :+ (q :+ s)) refl

-- At position 0 this is the definition of Σᴮ.  At suc j the sum is
-- split at the head and each half at j; the four quarter-sums, with
-- the head and y_(suc j) fixed, are then regrouped by the value of
-- y_(suc j).  The summand is only known to respect pointwise equality
-- of assignments, since the assignments the two sides build are
-- pointwise, not definitionally, equal.

Σᴮ-insert : (j : Fin (suc m)) (f : (Fin (suc m) → Bool) → Amp) →
            Respects f →
            Σᴮ f ≐ (Σᴮ (λ g → f (insertᵃ j true g)) +ᴬ
                    Σᴮ (λ g → f (insertᵃ j false g)))
Σᴮ-insert {m = m} zero f resp i = cong₂ _+_
  (Σᴮ-cong (λ g → resp (extend true g) (insertᵃ zero true g) (pt true g)) i)
  (Σᴮ-cong (λ g → resp (extend false g) (insertᵃ zero false g) (pt false g)) i)
  where
  pt : ∀ b (g : Fin m → Bool) l → extend b g l ≡ insertᵃ zero b g l
  pt b g zero    = refl
  pt b g (suc l) = refl
Σᴮ-insert {zero}  (suc ()) f resp i
Σᴮ-insert {suc m} (suc j) f resp i = trans
  (cong₂ _+_ (Σᴮ-insert j (λ g → f (extend true g)) (respExt true) i)
             (Σᴮ-insert j (λ g → f (extend false g)) (respExt false) i))
  (trans (shuffle (A true true i) (A true false i)
                  (A false true i) (A false false i))
         (cong₂ _+_ (cong₂ _+_ (A≐B true true i) (A≐B false true i))
                    (cong₂ _+_ (A≐B true false i) (A≐B false false i))))
  where
  respExt : ∀ a → Respects (λ g → f (extend a g))
  respExt a g h g≗h =
    resp (extend a g) (extend a h) (extend-cong a g h g≗h)

  -- The quarter-sum with the head fixed to a and y_(suc j) to b, as
  -- the left-hand side and as the right-hand side build it.
  A B : Bool → Bool → Amp
  A a b = Σᴮ (λ g → f (extend a (insertᵃ j b g)))
  B a b = Σᴮ (λ g → f (insertᵃ (suc j) b (extend a g)))

  pt : ∀ a b g l →
       extend a (insertᵃ j b g) l ≡ insertᵃ (suc j) b (extend a g) l
  pt a b g zero    = refl
  pt a b g (suc l) = refl

  A≐B : ∀ a b → A a b ≐ B a b
  A≐B a b = Σᴮ-cong (λ g →
    resp (extend a (insertᵃ j b g)) (insertᵃ (suc j) b (extend a g))
         (pt a b g))

-- The sum over the renumbered assignments is the same sum.

Σᴮ-front : (j : Fin (suc m)) (f : (Fin (suc m) → Bool) → Amp) →
           Respects f → Σᴮ f ≐ Σᴮ (λ y′ → f (unfront j y′))
Σᴮ-front = Σᴮ-insert


------------------------------------------------------------------------
-- Renumbering does not change which paths hit an output

-- Two path-sums whose outputs read the same bits at two paths send
-- those paths to the same outputs.  Denotation's reading of an output
-- is private; its public outBit, hits-intro and hits-elim suffice.

hits-outBit : (ξ : PathSum n k m) (ζ : PathSum n k′ m′) (x : Assign n)
              (y : Assign m) (y′ : Assign m′) (z : Assign n) →
              (∀ w → outBit ξ x y w ≡ outBit ζ x y′ w) →
              hits ξ x y z ≡ hits ζ x y′ z
hits-outBit ξ ζ x y y′ z same = go (hits ξ x y z) refl (hits ζ x y′ z) refl
  where
  go : ∀ a → hits ξ x y z ≡ a → ∀ b → hits ζ x y′ z ≡ b → a ≡ b
  go true  _  true  _  = refl
  go false _  false _  = refl
  go true  ea false eb = contradiction
    (trans (sym (hits-intro ζ x y′ z (λ w →
       trans (sym (same w)) (hits-elim ξ x y z ea w)))) eb)
    λ ()
  go false ea true  eb = contradiction
    (trans (sym (hits-intro ξ x y z (λ w →
       trans (same w) (hits-elim ζ x y′ z eb w)))) ea)
    λ ()

-- An output reads its bit off its value, and renumbering commutes
-- with evaluation.  (outBit ξ x y w unfolds to that reading, private
-- helpers still reducing outside their module.)

outBit-front : (j : Fin (suc m)) (ξ : PathSum n k (suc m)) (x : Assign n)
               (y′ : Assign (suc m)) (w : Fin n) →
               outBit (front j ξ) x y′ w ≡ outBit ξ x (unfront j y′) w
outBit-front j ξ x y′ w =
  cong (λ v → not ⌊ (+ 2) ∣? v ⌋) (eval-front j (out ξ w) x y′)

hits-front : (j : Fin (suc m)) (ξ : PathSum n k (suc m)) (x : Assign n)
             (y′ : Assign (suc m)) (z : Assign n) →
             hits (front j ξ) x y′ z ≡ hits ξ x (unfront j y′) z
hits-front j ξ x y′ z =
  hits-outBit (front j ξ) ξ x y′ (unfront j y′) z (outBit-front j ξ x y′)


------------------------------------------------------------------------
-- Renumbering preserves the denotation

private
  if-cong : ∀ {p q : Bool} {a b : Amp} → p ≡ q → a ≐ b →
            (if p then a else 0ᴬ) ≐ (if q then b else 0ᴬ)
  if-cong {p = true}  refl a≐b = a≐b
  if-cong {p = false} refl a≐b = λ _ → refl

-- Each entry of front j ξ is the corresponding entry of ξ, summed
-- over the renumbered paths.  The summand of ξ is named, and the
-- phases are related by an equation between exponents only.

amp-front : (j : Fin (suc m)) (ξ : PathSum n k (suc m)) (x z : Assign n) →
            amp (front j ξ) x z ≐ amp ξ x z
amp-front {m = m} {n = n} j ξ x z i =
  trans (Σᴮ-cong per i) (sym (Σᴮ-front j Bξ resp i))
  where
  Bξ : Assign (suc m) → Amp
  Bξ y = if hits ξ x y z then zpow (eval (phase ξ) x y) else 0ᴬ

  per : ∀ y′ →
        (if hits (front j ξ) x y′ z
         then zpow (eval (frontᴾ j (phase ξ)) x y′) else 0ᴬ) ≐
        Bξ (unfront j y′)
  per y′ = if-cong (hits-front j ξ x y′ z)
    (λ i′ → cong (λ e → zpow e i′) (eval-front j (phase ξ) x y′))

  resp : Respects Bξ
  resp g h g≗h = if-cong
    (hits-≗³ ξ {x} {x} {g} {h} {z} {z} (λ _ → refl) g≗h (λ _ → refl))
    (λ i′ → cong (λ e → zpow e i′)
                 (eval-cong (phase ξ) {x} {x} {g} {h} (λ _ → refl) g≗h))

front-≋ : (j : Fin (suc m)) (ξ : PathSum n k (suc m)) → front j ξ ≋ ξ
front-≋ {k = k} j ξ x z = scale-map k (amp-front j ξ x z)

≋-front : (j : Fin (suc m)) (ξ : PathSum n k (suc m)) → ξ ≋ front j ξ
≋-front j ξ = ≋-sym {ξ = front j ξ} {ζ = ξ} (front-≋ j ξ)


------------------------------------------------------------------------
-- Proposition 3.1 for the rules at any path variable

-- A step at y_j is a sound step on front j ξ, which is equivalent to
-- ξ.  The path-sums are written out: _≋_ matches on both
-- normalisations, so none of them is recoverable by unification.

Anywhere-sound :
  {R : PSRel} →
  (∀ {n k m k′ m′} {ξ : PathSum n k m} {ζ : PathSum n k′ m′} →
   R ξ ζ → ξ ≋ ζ) →
  ∀ {n k m k′ m′} {ξ : PathSum n k m} {ζ : PathSum n k′ m′} →
  Anywhere R ξ ζ → ξ ≋ ζ
Anywhere-sound snd {ξ = ξ} {ζ} (plain r) = snd {ξ = ξ} {ζ = ζ} r
Anywhere-sound snd {ξ = ξ} {ζ} (at j r)  =
  ≋-trans {ξ = ξ} {ζ = front j ξ} {χ = ζ}
    (≋-front j ξ) (snd {ξ = front j ξ} {ζ = ζ} r)

-- A union of sound relations is sound.

∪ᴿ-sound :
  {R R′ : PSRel} →
  (∀ {n k m k′ m′} {ξ : PathSum n k m} {ζ : PathSum n k′ m′} →
   R ξ ζ → ξ ≋ ζ) →
  (∀ {n k m k′ m′} {ξ : PathSum n k m} {ζ : PathSum n k′ m′} →
   R′ ξ ζ → ξ ≋ ζ) →
  ∀ {n k m k′ m′} {ξ : PathSum n k m} {ζ : PathSum n k′ m′} →
  (R ∪ᴿ R′) ξ ζ → ξ ≋ ζ
∪ᴿ-sound snd snd′ {ξ = ξ} {ζ} (inl r) = snd  {ξ = ξ} {ζ = ζ} r
∪ᴿ-sound snd snd′ {ξ = ξ} {ζ} (inr r) = snd′ {ξ = ξ} {ζ = ζ} r

-- The rules of PathSum.Reduction at any path variable.

⟶ᵍ-sound : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶ᵍ ζ → ξ ≋ ζ
⟶ᵍ-sound {ξ = a} {ζ = b} =
  Anywhere-sound (λ {_} {_} {_} {_} {_} {ξ} {ζ} → ⟶-sound {ξ = ξ} {ζ = ζ})
    {ξ = a} {ζ = b}

⟶ᵍ*-sound : {ξ : PathSum n k m} {ζ : PathSum n k′ m′} → ξ ⟶ᵍ* ζ → ξ ≋ ζ
⟶ᵍ*-sound {ξ = a} εᵍ = ≋-refl {ξ = a}
⟶ᵍ*-sound {ξ = a} {ζ = d} (_◅ᵍ_ {ζ = b} step steps) =
  ≋-trans {ξ = a} {ζ = b} {χ = d} (⟶ᵍ-sound step) (⟶ᵍ*-sound steps)
