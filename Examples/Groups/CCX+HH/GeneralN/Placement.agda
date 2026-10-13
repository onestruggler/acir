------------------------------------------------------------------------
-- Presentations of groups
--
-- Compile arbitrary distinct placements of X, CX, and CCX to adjacent
-- classical gates at the same width.  Routing is derived from the
-- symmetric-group synthesis, not from an added ancilla or a gate-set
-- extension.  Classical.physical expands its SWAPs into HH circuits.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)

module Examples.Groups.CCX+HH.GeneralN.Placement (extra : ℕ) where

open import Data.Bool.Base using (Bool ; true ; _∧_ ; _xor_)
open import Data.Bool.Properties using (∧-identityʳ)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.Fin.Permutation as P
  using (Permutation′ ; _⟨$⟩ʳ_ ; _⟨$⟩ˡ_ ; flip ; inverseˡ ; inverseʳ)
open import Data.Nat.Base using (suc ; zero)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; _≢_ ; refl ; sym ; trans ; cong ; cong₂ ; subst)
open import Relation.Nullary.Decidable using (Dec ; yes ; no)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)
import Examples.Groups.CCX+HH.GeneralN.Classical as C
import Examples.Groups.CCX+HH.GeneralN.ControlledX as Controlled
import Examples.Groups.CCX+HH.GeneralN.BorrowedBit as Borrowed
import Examples.Groups.CCX+HH.GeneralN.WirePermutations as W
import Examples.Groups.CCX+HH.Syntactics as HH

width : ℕ
width = suc (suc (suc extra))

module N = Controlled (Fin width) _≟_
module B = Borrowed (Fin width) _≟_
open C using (State ; _≈s_)

pull : Permutation′ width → State width → State width
pull p s i = s (p ⟨$⟩ʳ i)

private
  pull-cancel : ∀ p s → pull (flip p) (pull p s) ≈s s
  pull-cancel p s i = cong s (inverseʳ p)

  pull-toggle : ∀ p t b s →
    pull (flip p) (B.toggle t b s) ≈s B.toggle (p ⟨$⟩ʳ t) b (pull (flip p) s)
  pull-toggle p t b s i = select (i ≟ (p ⟨$⟩ʳ t))
    where
    Goal : Fin width → Set
    Goal j = pull (flip p) (B.toggle t b s) j ≡
      B.toggle (p ⟨$⟩ʳ t) b (pull (flip p) s) j

    at-target : Goal (p ⟨$⟩ʳ t)
    at-target = trans
      (trans (cong (B.toggle t b s) (inverseˡ p)) (B.toggle-at t b s))
      (sym (trans (B.toggle-at (p ⟨$⟩ʳ t) b (pull (flip p) s))
        (cong (λ j → s j xor b) (inverseˡ p))))

    select : Dec (i ≡ p ⟨$⟩ʳ t) → Goal i
    select (yes eq) = subst Goal (sym eq) at-target
    select (no different) = trans
      (B.toggle-other (λ eq → different
        (trans (sym (inverseʳ p)) (cong (p ⟨$⟩ʳ_) eq))) b s)
      (sym (B.toggle-other different b (pull (flip p) s)))

  conjugate-toggle : ∀ p t b s →
    pull (flip p) (B.toggle t b (pull p s)) ≈s B.toggle (p ⟨$⟩ʳ t) b s
  conjugate-toggle p t b s i = trans (pull-toggle p t b (pull p s) i)
    (B.toggle-cong (p ⟨$⟩ʳ t) b (pull-cancel p s) i)

conjugated : Permutation′ width → C.Gen width → C.Circuit width
conjugated p g = W.route (flip p) • [ g ]ʷ • W.route p

private
  conjugated-correct : ∀ p g t (test : State width → Bool) →
    (∀ s → C.act₀ g s ≈s B.toggle t (test s) s) →
    ∀ s → C.act (conjugated p g) s ≈s B.toggle (p ⟨$⟩ʳ t) (test (pull p s)) s
  conjugated-correct p g t test base s i = trans
    (W.route-correct (flip p) (C.act₀ g (C.act (W.route p) s)) i)
    (trans (C.act₀-cong g (W.route-correct p s) (p ⟨$⟩ˡ i))
      (trans (base (pull p s) (p ⟨$⟩ˡ i))
        (conjugate-toggle p t (test (pull p s)) s i)))

  x-base : ∀ s → C.x s ≈s B.toggle zero true s
  x-base s zero = refl
  x-base s (suc i) = refl

  cx-base : ∀ s → C.cx s ≈s B.toggle zero (s (suc zero)) s
  cx-base s zero = refl
  cx-base s (suc i) = refl

  ccx-base : ∀ s → C.ccx s ≈s B.toggle zero (s (suc zero) ∧ s (suc (suc zero))) s
  ccx-base s zero = refl
  ccx-base s (suc i) = refl

place₀ : N.Gate → C.Circuit width
place₀ (N.X t) = conjugated (W.one t) (C.gate₁ C.X-gate)
place₀ (N.CX c t) = conjugated (W.two t c) (C.gate₂ C.CX-gate)
place₀ (N.CCX a b t) = conjugated (W.three t a b) (C.gate₃ C.CCX-gate)

Proper : N.Gate → Set
Proper (N.X t) = ⊤
Proper (N.CX c t) = t ≢ c
Proper (N.CCX a b t) = t ≢ a × t ≢ b × a ≢ b

place₀-correct : ∀ g → Proper g → ∀ s → C.act (place₀ g) s ≈s N.act₀ g s
place₀-correct (N.X t) valid s i = trans
  (conjugated-correct (W.one t) (C.gate₁ C.X-gate) zero (λ _ → true) x-base s i)
  (cong (λ j → B.toggle j true s i) (W.one-zero t))
place₀-correct (N.CX c t) valid s i = trans
  (conjugated-correct (W.two t c) (C.gate₂ C.CX-gate) zero (λ v → v (suc zero)) cx-base s i)
  (trans (cong₂ (λ j b → B.toggle j b s i) (W.two-zero t c valid)
    (cong s (W.two-one t c)))
    (cong (λ b → B.toggle t b s i) (sym (∧-identityʳ (s c)))))
place₀-correct (N.CCX a b t) (ta , tb , ab) s i = trans
  (conjugated-correct (W.three t a b) (C.gate₃ C.CCX-gate) zero
    (λ v → v (suc zero) ∧ v (suc (suc zero))) ccx-base s i)
  (trans (cong₂ (λ j z → B.toggle j z s i) (W.three-zero t a b ta tb)
    (cong₂ _∧_ (cong s (W.three-one t a b ab)) (cong s (W.three-two t a b))))
    (cong (λ z → B.toggle t z s i) (cong (s a ∧_) (sym (∧-identityʳ (s b))))))

place : Word N.Gate → C.Circuit width
place = place₀ ʷ

AllProper : Word N.Gate → Set
AllProper [ g ]ʷ = Proper g
AllProper ε = ⊤
AllProper (u • v) = AllProper u × AllProper v

place-correct : ∀ w → AllProper w → ∀ s → C.act (place w) s ≈s N.act w s
place-correct [ g ]ʷ valid = place₀-correct g valid
place-correct ε valid s i = refl
place-correct (u • v) (pu , pv) s i = trans
  (C.act-cong (place u) (place-correct v pv s) i)
  (place-correct u pu (N.act v s) i)

physical : Word N.Gate → HH.Circuit width
physical w = C.physical (place w)

private
  next-valid : ∀ {k a b t r} {cs : Vec (Fin width) k} →
    N.Valid (a ∷ b ∷ cs) t r → N.Valid (r ∷ cs) t a
  next-valid v = record
    { target≢spare = proj₁ (N.Valid.target-fresh v)
    ; target-fresh = N.Valid.target≢spare v , proj₂ (proj₂ (N.Valid.target-fresh v))
    ; spare-fresh = (λ eq → proj₁ (N.Valid.spare-fresh v) (sym eq)) ,
        proj₂ (proj₁ (N.Valid.distinct v))
    ; distinct = proj₂ (proj₂ (N.Valid.spare-fresh v)) , proj₂ (proj₂ (N.Valid.distinct v))
    }

  proper-step : ∀ {a d} → Proper a → AllProper d →
    AllProper ([ a ]ʷ • d • [ a ]ʷ • d)
  proper-step pa pd = pa , pd , pa , pd

compile-proper : ∀ k (cs : Vec (Fin width) k) t r → N.Valid cs t r →
  AllProper (N.compile k cs t r)
compile-proper zero [] t r valid = tt
compile-proper (suc zero) (a ∷ []) t r valid = proj₁ (N.Valid.target-fresh valid)
compile-proper (suc (suc zero)) (a ∷ b ∷ []) t r valid =
  proj₁ (N.Valid.target-fresh valid) , proj₁ (proj₂ (N.Valid.target-fresh valid)) ,
  proj₁ (proj₁ (N.Valid.distinct valid))
compile-proper (suc (suc (suc k))) (a ∷ b ∷ cs) t r valid =
  proper-step {a = N.CCX a b r} {d = N.compile (suc (suc k)) (r ∷ cs) t a}
    (proj₁ (N.Valid.spare-fresh valid) , proj₁ (proj₂ (N.Valid.spare-fresh valid)) ,
      proj₁ (proj₁ (N.Valid.distinct valid)))
    (compile-proper (suc (suc k)) (r ∷ cs) t a (next-valid valid))

controlled : ∀ k → Vec (Fin width) k → Fin width → Fin width → C.Circuit width
controlled k cs t r = place (N.compile k cs t r)

controlled-correct : ∀ k (cs : Vec (Fin width) k) t r → N.Valid cs t r →
  ∀ s → C.act (controlled k cs t r) s ≈s N.controlled cs t s
controlled-correct k cs t r valid s i = trans
  (place-correct (N.compile k cs t r) (compile-proper k cs t r valid) s i)
  (N.compile-correct k cs t r valid s i)

physical-controlled : ∀ k → Vec (Fin width) k → Fin width → Fin width → HH.Circuit width
physical-controlled k cs t r = C.physical (controlled k cs t r)
