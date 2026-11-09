------------------------------------------------------------------------
-- Presentations of groups
--
-- The circuits that keep a wire, and their faithfulness
--
-- A placed letter keeps wire m when its target is another wire, and
-- a word of letters that each keep wire m acts on the 16 states as a
-- permutation that preserves that wire's bit.  Faithful m says that the
-- theory decides those words: two of them with the same function are
-- equal.  The subgroup that keeps wire 3 is the paper's K, and
-- faithfulness of K gives faithfulness for every wire (faithful), by
-- the relabelling τ m that exchanges wires m and 3, as Placed.narrow
-- does for the three-wire circuits; that τ m takes a letter keeping
-- wire m to one keeping wire 3 is decided for all letters
-- (keeps-τ-check).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.XCXCCX-4bit.Faithful where

open import Data.Bool.Base using (Bool ; true ; false ; T ; not ; _∧_ ; _∨_)
open import Data.Unit.Base using (tt)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; map)
import Data.Nat.Properties as ℕP
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (_•_)
import Presentation.Base as PB

open import Notations using (₀ ; ₁ ; ₂ ; ₃)

open import Examples.Groups.XCXCCX-4bit.Syntactics
open import Examples.Groups.XCXCCX-4bit.Semantics using (⟦_⟧ ; _≐_ ; ≐-refl ; ≐-sym ; ≐-trans ; ⨾-cong ; sound)
open import Examples.Groups.XCXCCX-4bit.Placed

open PB (4 VRel,_===_) using (_≈_ ; refl ; sym ; trans ; cong)
open Cx.Complete cox using (Pc-inv′)
open Relabel using (net)

private
  ∧ˡ : ∀ {a b} → a ∧ b ≡ true → a ≡ true
  ∧ˡ {true} _ = Eq.refl

  ∧ʳ : ∀ {a b} → a ∧ b ≡ true → b ≡ true
  ∧ʳ {true} h = h

------------------------------------------------------------------------
-- Targets

target : PG → Wire
target (Xᵖ t)       = t
target (CXᵖ c t)    = t
target (CCXᵖ a b t) = t

-- The letter does not change wire m.
keeps : Wire → PG → Bool
keeps m g = not (m == target g)

every-++ : (p : PG → Bool) (xs ys : List PG) → every p xs ≡ true → every p ys ≡ true →
           every p (xs ++ ys) ≡ true
every-++ p []       ys _  h = h
every-++ p (x ∷ xs) ys hx hy =
  Eq.cong₂ _∧_ (∧ˡ hx) (every-++ p xs ys (∧ʳ {p x} hx) hy)

-- A word whose letters target a or b keeps every other wire.
targets : Wire → Wire → PG → Bool
targets a b g = (target g == a) ∨ (target g == b)

private
  T→≡ : ∀ {c} → T c → c ≡ true
  T→≡ {true} _ = Eq.refl

  ≡→T : ∀ {c} → c ≡ true → T c
  ≡→T Eq.refl = tt

  keep-by : (m a b x : Wire) → (x == a) ∨ (x == b) ≡ true → T (not (m == a)) → T (not (m == b)) →
            not (m == x) ≡ true
  keep-by m a b x h ha hb with x == a in ea
  ... | true  = Eq.subst (λ z → not (m == z) ≡ true) (Eq.sym (==-sound x a (≡→T ea))) (T→≡ ha)
  ... | false = Eq.subst (λ z → not (m == z) ≡ true) (Eq.sym (==-sound x b (≡→T h))) (T→≡ hb)

keeps-from : (m a b : Wire) (xs : List PG) → every (targets a b) xs ≡ true →
             T (not (m == a)) → T (not (m == b)) → every (keeps m) xs ≡ true
keeps-from m a b []       _ _  _  = Eq.refl
keeps-from m a b (x ∷ xs) h ha hb =
  Eq.cong₂ _∧_ (keep-by m a b (target x) (∧ˡ h) ha hb) (keeps-from m a b xs (∧ʳ {targets a b x} h) ha hb)

------------------------------------------------------------------------
-- Relabelling: τ m takes a letter that keeps wire m to one that keeps
-- wire 3 (decided once for all letters and wires)

private
  imp : Bool → Bool → Bool
  imp a b = not a ∨ b

  imp-sound : ∀ {a b} → imp a b ≡ true → a ≡ true → b ≡ true
  imp-sound h Eq.refl = h

  keeps-τ-check : (m : Wire) → forallPG (λ g → imp (keeps m g) (keeps ₃ (relabel (τ m) g))) ≡ true
  keeps-τ-check ₀ = Eq.refl
  keeps-τ-check ₁ = Eq.refl
  keeps-τ-check ₂ = Eq.refl
  keeps-τ-check ₃ = Eq.refl

  keeps-τ : (m : Wire) (g : PG) → keeps m g ≡ true → keeps ₃ (relabel (τ m) g) ≡ true
  keeps-τ m g = imp-sound (forallPG-sound (λ g → imp (keeps m g) (keeps ₃ (relabel (τ m) g))) (keeps-τ-check m) g)

every-keeps-τ : (m : Wire) (u : List PG) → every (keeps m) u ≡ true →
                every (keeps ₃) (map (relabel (τ m)) u) ≡ true
every-keeps-τ m []      _ = Eq.refl
every-keeps-τ m (g ∷ u) h =
  Eq.cong₂ _∧_ (keeps-τ m g (∧ˡ h)) (every-keeps-τ m u (∧ʳ {keeps m g} h))

------------------------------------------------------------------------
-- Faithfulness

-- The theory decides the words that keep wire m.
Faithful : Wire → Set
Faithful m = (u v : List PG) → every (keeps m) u ≡ true → every (keeps m) v ≡ true →
             ⟦ u ⟧ᵖ* ≐ ⟦ v ⟧ᵖ* → 4 ⊢ ι* u ≈ ι* v

-- Faithfulness for wire 3 is faithfulness for every wire.
faithful : Faithful ₃ → (m : Wire) → Faithful m
faithful f₃ m u v hu hv e = unconj (Pc-inv′ 0 ℕP.≤-refl (net R)) step
  where
  R = τ m
  u′ = map (relabel R) u
  v′ = map (relabel R) v
  hu′ : every (keeps ₃) u′ ≡ true
  hu′ = every-keeps-τ m u hu
  hv′ : every (keeps ₃) v′ ≡ true
  hv′ = every-keeps-τ m v hv
  eu : 4 ⊢ ι* u′ ≈ S R • ι* u • S⁻ R
  eu = relabel-ι* R u
  ev : 4 ⊢ ι* v′ ≈ S R • ι* v • S⁻ R
  ev = relabel-ι* R v
  e′ : ⟦ ι* u ⟧ ≐ ⟦ ι* v ⟧
  e′ = ≐-trans (ι*-sem u) (≐-trans e (≐-sym (ι*-sem v)))
  mid : ⟦ S R • ι* u • S⁻ R ⟧ ≐ ⟦ S R • ι* v • S⁻ R ⟧
  mid = ⨾-cong {f = ⟦ S R ⟧} {f′ = ⟦ S R ⟧} ≐-refl (⨾-cong {g = ⟦ S⁻ R ⟧} {g′ = ⟦ S⁻ R ⟧} e′ ≐-refl)
  sem′ : ⟦ u′ ⟧ᵖ* ≐ ⟦ v′ ⟧ᵖ*
  sem′ = ≐-trans (≐-sym (ι*-sem u′)) (≐-trans (sound eu) (≐-trans mid (≐-trans (≐-sym (sound ev)) (ι*-sem v′))))
  step : 4 ⊢ S R • ι* u • S⁻ R ≈ S R • ι* v • S⁻ R
  step = trans (sym eu) (trans (f₃ u′ v′ hu′ hv′ sem′) ev)
