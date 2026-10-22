------------------------------------------------------------------------
-- Presentations of groups
--
-- A window: a sub-circuit whose gates avoid one wire, as a placed
-- circuit of one width less
--
-- Lemma 5.1 (Place) speaks of `place i u = cyc⁻¹ i • u ↑ • cyc i`; a
-- derivation meets instead a run of gates none of which touches wire
-- i, each spelled at the full width.  `ins i` is that spelling of a
-- gate of the smaller width — the wires from i up moved up one — and
-- `place-ins` says a circuit whose gates avoid i (`avoidsʷ`, decided
-- gate by gate) is its placement.  So `win`: two such runs with the
-- same semantics are equal, given completeness one width down — one
-- semantic step on a window.  The proofs use the swap rules and are in
-- `Laws sf` (SwapFacts); `win` takes those with completeness, `Base`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Windows where

open import Data.Bool using (Bool ; true ; false ; _∧_ ; T)
open import Data.Unit using (tt)
open import Data.Nat using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
open import Data.Product using (_×_ ; _,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; wmap)

open import Notations using (₁₊ ; ₂₊)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Semantics using (_~_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)
open import Examples.Groups.Clifford+CS.MultiControlled using (_↧ ; top)
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.SwapFacts using (SwapFacts)
open import Examples.Groups.Clifford+CS.TopWeakening using (low-comm)
open import Examples.Groups.Clifford+CS.SemanticSteps using (Complete ; Same ; same-sem)
open import Examples.Groups.Clifford+CS.Place renaming (module Laws to PlaceLaws)

private
  variable
    k r : ℕ

------------------------------------------------------------------------
-- A gate of the smaller width, spelled with wire i inserted

-- The wires from i up move up one.
ins : (i : ℕ) → Gen k → Gen (₁₊ k)
ins zero    g         = g ↥
ins (suc i) (gate₀ h) = gate₀ h
ins (suc i) (gate₁ h) = gate₁ h
ins (suc i) (gate₂ h) = gate₂ h
ins (suc i) (g ↥)     = ins i g ↥

insʷ : (i : ℕ) → Circuit k → Circuit (₁₊ k)
insʷ i = wmap (ins i)

-- Whether a gate lies entirely below or entirely above wire i (so that
-- `ins i` is its placement); at i = 0 every gate does.
avoids : (i : ℕ) → Gen k → Bool
avoids zero          _         = true
avoids (suc i)       (gate₀ h) = true
avoids (suc i)       (gate₁ h) = true
avoids (suc zero)    (gate₂ h) = false
avoids (suc (suc i)) (gate₂ h) = true
avoids (suc i)       (g ↥)     = avoids i g

avoidsʷ : (i : ℕ) → Circuit k → Bool
avoidsʷ i [ g ]ʷ  = avoids i g
avoidsʷ i ε       = true
avoidsʷ i (u • v) = avoidsʷ i u ∧ avoidsʷ i v

private
  ∧-T : ∀ {x y : Bool} → T (x ∧ y) → T x × T y
  ∧-T {true} {true} _ = tt , tt

------------------------------------------------------------------------
-- Given the swap rules

module Laws (sf : SwapFacts) where

  open SwapFacts sf
  open PlaceLaws sf

  ------------------------------------------------------------------------
  -- Such a gate is placed by `ins`

  -- The step of the induction on the gate's position: one wire up.
  private
    place-gen-↥ : ∀ i r (g : Gen (i +ℕ r)) → (₁₊ (i +ℕ r)) ⊢ place {r} i [ g ]ʷ ≈ [ ins i g ]ʷ →
                  (₂₊ (i +ℕ r)) ⊢ place {r} (suc i) [ g ↥ ]ʷ ≈ [ ins i g ↥ ]ʷ
    place-gen-↥ i r g ih = begin
      (cyc⁻¹ i ↑ • Swap) • ([ g ]ʷ ↑ ↑ • (Swap • cyc i ↑))
        ≈⟨ by-passoc ((□ • □) • (□ • (□ • □))) (□ • (□ • □) • (□ • □)) Eq.refl ⟩
      cyc⁻¹ i ↑ • (Swap • [ g ]ʷ ↑ ↑) • (Swap • cyc i ↑)
        ≈⟨ back _ (front _ (low-comm Swap [ g ]ʷ)) ⟩
      cyc⁻¹ i ↑ • ([ g ]ʷ ↑ ↑ • Swap) • (Swap • cyc i ↑)
        ≈⟨ by-passoc (□ • (□ • □) • (□ • □)) (□ • □ • (□ • □) • □) Eq.refl ⟩
      cyc⁻¹ i ↑ • [ g ]ʷ ↑ ↑ • (Swap • Swap) • cyc i ↑
        ≈⟨ back _ (back _ (trans (front _ Swap²) left-unit)) ⟩
      cyc⁻¹ i ↑ • [ g ]ʷ ↑ ↑ • cyc i ↑
        ≈⟨ lemma-cong↑ (place i [ g ]ʷ) [ ins i g ]ʷ ih ⟩
      [ ins i g ]ʷ ↑ ∎
      where open Tools ((₂₊ (i +ℕ r)) VRel,_===_)

  -- A gate avoiding wire i is placed by `ins i`.  The clauses refine i
  -- and r so that every constructor's index is decidable.
  place-gen : ∀ i r (g : Gen (i +ℕ r)) → T (avoids i g) →
              (₁₊ (i +ℕ r)) ⊢ place {r} i [ g ]ʷ ≈ [ ins i g ]ʷ
  place-gen zero r g _ = trans left-unit right-unit
    where open Tools ((₁₊ r) VRel,_===_)
  place-gen (suc zero) zero (gate₀ h) _ = place-low 1 [ gate₀ h ]ʷ
  place-gen (suc zero) zero (gate₁ h) _ = place-low 1 [ gate₁ h ]ʷ
  place-gen (suc zero) zero (g ↥) a = place-gen-↥ zero zero g (place-gen zero zero g a)
  place-gen (suc zero) (suc r) (gate₀ h) _ = place-low 1 [ gate₀ h ]ʷ
  place-gen (suc zero) (suc r) (gate₁ h) _ = place-low 1 [ gate₁ h ]ʷ
  place-gen (suc zero) (suc r) (gate₂ h) ()
  place-gen (suc zero) (suc r) (g ↥) a = place-gen-↥ zero (suc r) g (place-gen zero (suc r) g a)
  place-gen (suc (suc i)) r (gate₀ h) _ = place-low (suc (suc i)) [ gate₀ h ]ʷ
  place-gen (suc (suc i)) r (gate₁ h) _ = place-low (suc (suc i)) [ gate₁ h ]ʷ
  place-gen (suc (suc i)) r (gate₂ h) _ = place-low (suc (suc i)) [ gate₂ h ]ʷ
  place-gen (suc (suc i)) r (g ↥) a = place-gen-↥ (suc i) r g (place-gen (suc i) r g a)

  -- A circuit whose gates avoid wire i is placed by `insʷ`.
  place-ins : ∀ i r (u : Circuit (i +ℕ r)) → T (avoidsʷ i u) →
              (₁₊ (i +ℕ r)) ⊢ place {r} i u ≈ insʷ i u
  place-ins i r [ g ]ʷ a = place-gen i r g a
  place-ins i r ε _ = trans (back _ left-unit) (cyc⁻¹-cyc i)
    where open Tools ((₁₊ (i +ℕ r)) VRel,_===_)
  place-ins i r (u • v) a with ∧-T a
  ... | (au , av) = trans (place-• i u v) (cong (place-ins i r u au) (place-ins i r v av))
    where open Tools ((₁₊ (i +ℕ r)) VRel,_===_)

  ------------------------------------------------------------------------
  -- A semantic step on a window

  -- Two runs of gates avoiding wire i, with the same semantics, are
  -- equal, given completeness at the smaller width.
  window : ∀ i r → (∀ {u v : Circuit (i +ℕ r)} → ⟦ u ⟧ ~ ⟦ v ⟧ → (i +ℕ r) ⊢ u ≈ v) →
        (u v : Circuit (i +ℕ r)) → T (avoidsʷ i u) → T (avoidsʷ i v) → Same u v →
        (₁₊ (i +ℕ r)) ⊢ insʷ i u ≈ insʷ i v
  window i r complete u v au av e =
    trans (sym (place-ins i r u au))
      (trans (lemma-5-1 i complete (same-sem u v e)) (place-ins i r v av))
    where open Tools ((₁₊ (i +ℕ r)) VRel,_===_)

------------------------------------------------------------------------
-- What a window step takes

-- The swap rules and completeness at the width of the window: the
-- window libraries take it as an argument, so that they need not wait
-- for the proofs (Swaps.facts, Completeness).
record Base (k : ℕ) : Set where
  field
    facts    : SwapFacts
    complete : Complete k

win : ∀ i r → Base (i +ℕ r) →
      (u v : Circuit (i +ℕ r)) → T (avoidsʷ i u) → T (avoidsʷ i v) → Same u v →
      (₁₊ (i +ℕ r)) ⊢ insʷ i u ≈ insʷ i v
win i r b = Laws.window (Base.facts b) i r (Base.complete b)
