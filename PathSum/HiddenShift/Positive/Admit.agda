------------------------------------------------------------------------
-- Presentations of groups
--
-- Proving that a given [HH] is output-safe and Clifford-safe
--
-- Tools for showing that a chain someone else built lies in
-- PathSum.HiddenShift.Positive.Class's class (used by
-- PathSum.HiddenShift.Positive.Exists for PathSum.HiddenShift.Exists'
-- three passes).
--
-- * hh-elimᴷ: PathSum.HiddenShift.Track's hh-elim -- [HH] at y_j with
--   y_i ← Q, then [Elim] of y_i -- as a chain of the class, given that
--   the [HH] is output-safe and Clifford-safe (the [Elim] always is).
-- * module Safe: sufficient conditions.  An [HH] whose quotient
--   mentions no variable is output-safe (os-none), as is one that
--   substitutes an internal variable (os-target); it is Clifford-safe
--   when its quotient's value is affine and every internal Clifford
--   variable the quotient mentions forces the substituted variable to
--   be internal and Clifford too (cs-from) -- Boolean's Cl-hh.
-- * Cl-unfr⁻¹: a variable Clifford after renumbering was Clifford
--   before.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.Positive.Admit (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; _xor_)
open import Data.Bool.Properties using (xor-same)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ)
open import Data.Nat.Base using (zero; suc)
open import Data.Product.Base using (_×_; _,_)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using (_∷_; lookup; removeAt; insertAt)
open import Data.Vec.Properties using (insertAt-removeAt)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)

open import PathSum.Assign using ([_]ᶻ; _[_≔_])
open import PathSum.Base using (PathSum; phase; out; head-part; tail-part)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.HiddenShift.Positive.Boolean
open import PathSum.HiddenShift.Positive.Class M₀ using
  (Int; Clifᶜ; OutSafe; CliffSafe; Admᶠ; _⟶ᴷ*_; εᴷ; _◅ᴷ_)
open import PathSum.HiddenShift.Positive.Invariant M₀ using
  (module HHᴵ; Clif⇒Cl; Cl⇒Clif)
open import PathSum.HiddenShift.Positive.Values M₀ using (VTracks)
open import PathSum.HiddenShift.Track M₀ using
  (Tracks; hh-premise; out-premise; hh-tracks; elim-tracks; absent-/ʸ)
open import PathSum.Polynomial using
  (Poly; y[_]; eval; μ; _+ᴾ_; _·ᴾ_; _≈[_]_)
open import PathSum.Polynomial.Boolean using (IsBit; BoolValued; IsBit-if)
open import PathSum.Polynomial.Substitution using
  (Absent; Absent⇒NoVar; substᴾ-absent)
open import PathSum.Reorder using (insertᵃ; front; frontᴾ)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Anywhere M using (plain; at)
open import PathSum.Full M using (_⟶ᶠ_; elimAtᶠ)
open import PathSum.Order M using (pow)
open import PathSum.Reduction M using (½; elim-reduct)
open import PathSum.Reduction.General M using (hhᴳ; hhᴳ-reduct)

private
  variable
    N n k m k′ m′ k″ m″ : ℕ


------------------------------------------------------------------------
-- Chains of the class, appended

infixr 5 _◅◅ᴷ_

_◅◅ᴷ_ : {ξ : PathSum N k m} {ζ : PathSum N k′ m′} {χ : PathSum N k″ m″} →
        ξ ⟶ᴷ* ζ → ζ ⟶ᴷ* χ → ξ ⟶ᴷ* χ
εᴷ        ◅◅ᴷ ss′ = ss′
(s ◅ᴷ ss) ◅◅ᴷ ss′ = s ◅ᴷ (ss ◅◅ᴷ ss′)


------------------------------------------------------------------------
-- [HH] and [Elim] of the substituted variable, admissibly

hh-elimᴷ : (ξ : PathSum N (suc (suc k)) (suc (suc m)))
           {F : Assign (suc (suc m)) → Bool}
           {G : Fin N → Assign (suc (suc m)) → Bool} → Tracks ξ F G →
           (j : Fin (suc (suc m))) (i : Fin (suc m)) (Q : Poly N (suc m))
           (q : Assign (suc m) → Bool) →
           (hq : ∀ x y → eval Q x y ≡ [ q y ]ᶻ) → (absQ : Absent y[ i ] Q) →
           (dF : ∀ y → F (insertᵃ j true y) xor F (insertᵃ j false y) ≡
                       y i xor q y) →
           (∀ w y → G w (insertᵃ j true y) ≡ G w (insertᵃ j false y)) →
           OutSafe (front j ξ) i Q → CliffSafe (front j ξ) i Q →
           (ξ ⟶ᴷ* elim-reduct (front i (hhᴳ-reduct (front j ξ) i Q))) ×
           Tracks (elim-reduct (front i (hhᴳ-reduct (front j ξ) i Q)))
             (λ y → F (insertᵃ j false (insertᵃ i false y
                                          [ i ≔ q (insertᵃ i false y) ])))
             (λ w y → G w (insertᵃ j false (insertᵃ i false y
                                              [ i ≔ q (insertᵃ i false y) ])))
hh-elimᴷ ξ tr j i Q q hq absQ dF dG os cs =
  ((step₁ , (os , cs)) ◅ᴷ (step₂ , tt) ◅ᴷ εᴷ) ,
  elim-tracks ζ (hh-tracks ξ tr j i Q q hq) i
  where

  ζ : PathSum _ _ _
  ζ = hhᴳ-reduct (front j ξ) i Q

  bQ : BoolValued Q
  bQ x y = subst IsBit (sym (hq x y)) (IsBit-if (q y))

  step₁ : ξ ⟶ᶠ ζ
  step₁ = at j (plain (hhᴳ (front j ξ) i Q bQ absQ
                           (hh-premise ξ tr j i Q q hq dF)
                           (out-premise ξ tr j dG)))

  step₂ : ζ ⟶ᶠ elim-reduct (front i ζ)
  step₂ = elimAtᶠ ζ i
    (absent-/ʸ (phase ζ) i
      (substᴾ-absent (tail-part (frontᴾ j (phase ξ))) y[ i ] Q absQ))
    (λ w → Absent⇒NoVar {v = y[ i ]}
      (substᴾ-absent (tail-part (frontᴾ j (out ξ w))) y[ i ] Q absQ))


------------------------------------------------------------------------
-- Sufficient conditions

module Safe {χ : PathSum N k (suc (suc m))} {F : Pt (suc (suc m)) → Bool}
            {G : Fin N → Pt (suc (suc m)) → Bool} (tr : VTracks χ F G)
            (i : Fin (suc m)) (Q : Poly N (suc m)) (bQ : BoolValued Q)
            (absQ : Absent y[ i ] Q)
            (eqP : head-part (phase χ) ≈[ pow M ] (½ ·ᴾ (μ y[ i ] +ᴾ Q))) where

  open HHᴵ tr i Q bQ absQ eqP using (q; q-val; q-indep; F″; reduct)

  private
    t≢f : true ≢ false
    t≢f ()

    bit-inj : ∀ {a b} → [ a ]ᶻ ≡ [ b ]ᶻ → a ≡ b
    bit-inj {false} {false} _ = refl
    bit-inj {true}  {true}  _ = refl
    bit-inj {false} {true}  ()
    bit-inj {true}  {false} ()

  -- The substituted value is the value of Q.

  q-agree : (q′ : Pt (suc m) → Bool) →
            (∀ x p → eval Q x (lookup p) ≡ [ q′ p ]ᶻ) → ∀ p → q p ≡ q′ p
  q-agree q′ h p = bit-inj (trans (sym (q-val x₀ p)) (h x₀ p))
    where
    x₀ : Fin _ → Bool
    x₀ _ = false

  -- Output safety.

  os-none : (∀ v → Absent y[ v ] Q) → OutSafe χ i Q
  os-none all v _ ¬abs = ⊥-elim (¬abs (all v))

  os-target : Int χ (suc i) → OutSafe χ i Q
  os-target int _ _ _ = int

  -- Clifford safety.

  cs-from : Aff q →
            (∀ v → ¬ Absent y[ v ] Q → Int χ (suc v) →
                   Clifᶜ (phase χ) (suc v) → Clifᶜ (phase χ) (suc i)) →
            CliffSafe χ i Q
  cs-from aq forced v int cl = Cl⇒Clif reduct v (by (v ≟ i))
    where
    -- q reads v only if Q mentions it.
    κ-present : κˢ v q ≡ true → ¬ Absent y[ v ] Q
    κ-present κ abs = t≢f (trans (sym κ)
      (trans (cong (_xor q 0ᵖ) (indep-set {f = q} {v} (q-indep v abs) 0ᵖ true))
             (xor-same (q 0ᵖ))))

    by : Dec (v ≡ i) → Cl F″ v
    by (yes v≡i) = subst (Cl F″) (sym v≡i)
      (Cl-hh-self {f = F} {q} i (q-indep i absQ))
    by (no v≢i)  = Cl-hh {f = F} {q} aq i v v≢i (Clif⇒Cl tr (suc v) cl)
      (λ κ → Clif⇒Cl tr (suc i) (forced v (κ-present κ) int cl))


------------------------------------------------------------------------
-- Renumbering back

-- The first coordinate moved back to position j.

frt : Fin (suc n) → Pt (suc n) → Pt (suc n)
frt j p = lookup p j ∷ removeAt p j

unfr-frt : (j : Fin (suc n)) (p : Pt (suc n)) → unfr j (frt j p) ≡ p
unfr-frt j p = insertAt-removeAt p j

AffMap-frt : (j : Fin (suc n)) → AffMap (frt j)
AffMap-frt j = AffMap-linear
  (λ x y → cong₂ _∷_ (lookup-⊕ x y j) (removeAt-⊕ x y j))
  (cong₂ _∷_ (lookup-0ᵖ j) (removeAt-0ᵖ j))

Cl-unfr⁻¹ : {f : Pt (suc n) → Bool} (j v : Fin (suc n)) →
            Cl (λ p → f (unfr j p)) v → Cl f (πᶠ j v)
Cl-unfr⁻¹ {f = f} j v c = Aff-cong eq (Aff-∘ c (AffMap-frt j))
  where
  at′ : ∀ p b → f (unfr j (set (frt j p) v b)) ≡ f (set p (πᶠ j v) b)
  at′ p b = cong f (trans (unfr-set j (frt j p) v b)
                         (cong (λ t → set t (πᶠ j v) b) (unfr-frt j p)))

  eq : ∀ p → ∂ˢ (λ p → f (unfr j p)) v (frt j p) ≡ ∂ˢ f (πᶠ j v) p
  eq p = cong₂ _xor_ (at′ p true) (at′ p false)
