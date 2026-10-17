------------------------------------------------------------------------
-- Presentations of groups
--
-- Transport at every width: an equation on n wires, put under the
-- control, is an equation on n + 1
--
-- The joint paper's transport lemma (stability-notes.md, Theorem S): if
-- n ⊢ u ≈ v then n + 1 ⊢ λ¹(u) ≈ λ¹(v), for the theory with the control
-- schema (Stable.Rules) and every n ≥ 4.  λ¹ is letterwise, so it is
-- enough to carry every axiom instance (`transport` from `AxOk`).  By
-- the width:
--
-- * On four wires every instance is carried by completeness on five,
--   both sides having the same semantics (λ¹-~ of soundness).
-- * From five on, by the instance:
--   - a rule of Syntactics leaves its top wire idle (Stable.Untop), so
--     it is `top` of the same rule a width down, and λ¹ of that is the
--     stretched image a width down (Stable.Coherence, from the two
--     borrowed-wire switches on six wires);
--   - AX, the controlled four-wire rules and the schema are carried to
--     the schema one control up: λ¹ of λ¹ᵏ (suc k) w is λ¹ᵏ (suc (suc k))
--     w by definition;
--   - cong↑ is cong↑ of the instance a width down, λ¹ commuting with
--     the shift, and ω↑=ω holds on the nose;
--   - a commutation comm₁, comm₂ of a gate on the bottom wires with a
--     gate g above it that leaves the top wire idle is `top` of the
--     commutation a width down, as for the rules; the ones where g
--     reaches the top wire (`IsHigh`) are left as hypotheses.
--
-- So transport at every width rests on completeness on five wires, the
-- two six-wire switches, and those commutations (`Hyp`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Stable.Transport where

open import Data.Nat using (ℕ ; zero ; suc)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₀ ; ₃ ; ₂₊ ; ₃₊ ; ₄₊)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Semantics using (_~_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.MultiControlled using (top ; _↧)
open import Examples.Groups.Clifford+CS.Place using (place)
open import Examples.Groups.Clifford+CS.Five.Rules using (old ; ax ; λ-lf ; λ-hyb-sq ; λ-hyb-yb ; λ-ck-tct)
open import Examples.Groups.Clifford+CS.Lambda
open import Examples.Groups.Clifford+CS.Lambda.Semantics using (λ¹-~)
open import Examples.Groups.Clifford+CS.Stable.Rules
open import Examples.Groups.Clifford+CS.Stable.Soundness using (axiom-soundᵧ)
open import Examples.Groups.Clifford+CS.Stable.Weakening using (stretch-congᵧ)
open import Examples.Groups.Clifford+CS.Stable.Coherence using (Switch₆ ; λ¹-top)
open import Examples.Groups.Clifford+CS.Stable.Untop using (Untop ; mk ; untop)
open import Examples.Groups.Clifford+CS.Stable.Insert using (place-congᵧ ; place-•ᵧ ; place₁-↑ ; λ¹₁-place)

private
  variable
    k m : ℕ

------------------------------------------------------------------------
-- From the axiom instances to derivations

AxOk : ℕ → Set
AxOk m = ∀ {w v} → (₄₊ m) YVRel, w === v → (suc (₄₊ m)) ⊢ᵧ λ¹ʷ w ≈ λ¹ʷ v

transport : AxOk m → ∀ {u v} → (₄₊ m) ⊢ᵧ u ≈ v → (suc (₄₊ m)) ⊢ᵧ λ¹ʷ u ≈ λ¹ʷ v
transport ok PB.refl          = PB.refl
transport ok (PB.sym e)       = PB.sym (transport ok e)
transport ok (PB.trans e f)   = PB.trans (transport ok e) (transport ok f)
transport ok (PB.cong e f)    = PB.cong (transport ok e) (transport ok f)
transport ok PB.assoc         = PB.assoc
transport ok PB.left-unit     = PB.left-unit
transport ok PB.right-unit    = PB.right-unit
transport ok (PB.axiom a)     = ok a

------------------------------------------------------------------------
-- A gate that leaves the top wire idle, or not

data View : Gen (suc k) → Set where
  low  : (g : Gen k) → View (g ↧)
  high : (g : Gen (suc k)) → View g

private
  up : {g : Gen (suc k)} → View g → View (g ↥)
  up (low g)  = low (g ↥)
  up (high g) = high (g ↥)

view : (g : Gen (suc k)) → View g
view         (gate₀ h) = low (gate₀ h)
view {zero}  (gate₁ h) = high (gate₁ h)
view {suc k} (gate₁ h) = low (gate₁ h)
view {suc zero}    (gate₂ h) = high (gate₂ h)
view {suc (suc k)} (gate₂ h) = low (gate₂ h)
view {zero}  (g ↥) = high (g ↥)
view {suc k} (g ↥) = up (view g)

IsHigh : Gen (suc k) → Set
IsHigh g = view g ≡ high g

------------------------------------------------------------------------
-- The hypotheses

record Hyp : Set where
  field
    complete₅ : ∀ {u v : Circuit 5} → ⟦ u ⟧ ~ ⟦ v ⟧ → 5 ⊢ᵧ u ≈ v
    switch    : Switch₆
    -- The CS on the top two wires of five against S or K on wire 0.
    comm₁-base : (h : Gate 1) →
                 (₂₊ (₄₊ zero)) ⊢ᵧ λ¹ {suc zero} (gate₂ CS-gate ↥ ↥ ↥) • λ¹ {suc zero} (gate₁ h)
                                 ≈ λ¹ {suc zero} (gate₁ h) • λ¹ {suc zero} (gate₂ CS-gate ↥ ↥ ↥)
    comm₂-high : ∀ m (h : Gate 2) (g : Gen (₂₊ (suc m))) → IsHigh g →
                 (₂₊ (₄₊ m)) ⊢ᵧ λ¹ (g ↥ ↥) • λ¹ (gate₂ h) ≈ λ¹ (gate₂ h) • λ¹ (g ↥ ↥)

------------------------------------------------------------------------
-- Transport

-- λ¹ commutes with the shift.
λ¹ʷ-↑ : (w : Circuit (₄₊ m)) → λ¹ʷ (w ↑) ≡ λ¹ʷ w ↑
λ¹ʷ-↑ [ g ]ʷ  = Eq.refl
λ¹ʷ-↑ ε       = Eq.refl
λ¹ʷ-↑ (u • v) = Eq.cong₂ _•_ (λ¹ʷ-↑ u) (λ¹ʷ-↑ v)

module _ (H : Hyp) where
  open Hyp H

  private
    -- A five-wire rule under one control is the schema at k = 0.  Generic
    -- in the words, and applied with the width of the goal: an implicit
    -- width that differs from the goal's only in its spelling (1 against
    -- suc 0) made Agda compare λ¹ʷ of the thousand-gate words by
    -- unfolding them.
    wide-ok : ∀ {n} {w v : Circuit (₄₊ n)} → Wide (₄₊ n) w v → (suc (₄₊ n)) ⊢ᵧ λ¹ʷ w ≈ λ¹ʷ v
    wide-ok p = PB.axiom (srelᵧ (ctl 0 p))

    -- An instance a width down with an idle top wire.
    via-top : ∀ m → AxOk m → ∀ {w v} → (₄₊ m) YVRel, w === v →
              (₂₊ (₄₊ m)) ⊢ᵧ λ¹ʷ (top w) ≈ λ¹ʷ (top v)
    via-top m ok {w} {v} a =
      PB.trans (λ¹-top switch m w)
        (PB.trans (stretch-congᵧ (ok a)) (PB.sym (λ¹-top switch m v)))

    rule : ∀ m → AxOk m → ∀ {w v} → (suc (₄₊ m)) SRel, w === v →
           (₂₊ (₄₊ m)) ⊢ᵧ λ¹ʷ w ≈ λ¹ʷ v
    rule m ok r with untop r
    ... | mk r′ Eq.refl Eq.refl = via-top m ok (srelᵧ (five (old r′)))

    -- Both letters one width down with wire 1 inserted.
    via-place : ∀ {r} {A B : Circuit (suc r)} {A′ B′ : Circuit (₂₊ r)} →
                (₂₊ r) ⊢ᵧ A′ ≈ place 1 A → (₂₊ r) ⊢ᵧ B′ ≈ place 1 B →
                (suc r) ⊢ᵧ A • B ≈ B • A → (₂₊ r) ⊢ᵧ A′ • B′ ≈ B′ • A′
    via-place {r} {A} {B} {A′} {B′} a b e = begin
      A′ • B′                 ≈⟨ cong a b ⟩
      place 1 A • place 1 B   ≈⟨ sym (place-•ᵧ 1 A B) ⟩
      place 1 (A • B)         ≈⟨ place-congᵧ 1 e ⟩
      place 1 (B • A)         ≈⟨ place-•ᵧ 1 B A ⟩
      place 1 B • place 1 A   ≈⟨ sym (cong b a) ⟩
      B′ • A′ ∎
      where open Tools ((₂₊ r) YVRel,_===_)

    -- A letter on wire 0 against one reaching the top wire: wire 1 is idle.
    high₁′ : ∀ m → AxOk (suc m) → (h : Gate 1) (g : Gen (₃₊ (suc (suc m)))) → IsHigh g →
             (₂₊ (₄₊ (suc m))) ⊢ᵧ λ¹ (g ↥) • λ¹ (gate₁ h) ≈ λ¹ (gate₁ h) • λ¹ (g ↥)
    high₁′ m ok h (g ↥) _ =
      via-place (PB.sym (embed (place₁-↑ (λ¹ {m} g)))) (λ¹₁-place (suc m) h) (ok (comm₁ᵧ h g))
    high₁′ m ok h (gate₀ x) ()
    high₁′ m ok h (gate₁ x) ()
    high₁′ m ok h (gate₂ x) ()

    -- The same on five wires, where λ¹ of a letter one wire up is not the
    -- image one wire up but the four-wire domain's own.
    high₁ : AxOk 0 → (h : Gate 1) (g : Gen 4) → IsHigh g →
            (₂₊ (₄₊ zero)) ⊢ᵧ λ¹ {suc zero} (g ↥) • λ¹ (gate₁ h) ≈ λ¹ (gate₁ h) • λ¹ {suc zero} (g ↥)
    high₁ ok h (gate₂ CS-gate ↥ ↥) _ = comm₁-base h
    high₁ ok h (gate₁ S-gate ↥ ↥ ↥) _ =
      via-place (PB.sym (embed (place₁-↑ (CSᵗ ₀ ↑ ↑)))) (λ¹₁-place 0 h) (ok (comm₁ᵧ h (gate₁ S-gate ↥ ↥)))
    high₁ ok h (gate₁ K-gate ↥ ↥ ↥) _ =
      via-place (PB.sym (embed (place₁-↑ (CKᵗ ₀ ↑ ↑)))) (λ¹₁-place 0 h) (ok (comm₁ᵧ h (gate₁ K-gate ↥ ↥)))
    high₁ ok h (gate₀ I-gate ↥ ↥ ↥ ↥) _ =
      via-place (PB.sym (embed (place₁-↑ (Sᵗ ₃)))) (λ¹₁-place 0 h) (ok (comm₁ᵧ h (gate₀ I-gate ↥ ↥ ↥)))
    high₁ ok h (gate₀ x) ()
    high₁ ok h (gate₁ x) ()
    high₁ ok h (gate₂ x) ()
    high₁ ok h (gate₀ x ↥) ()
    high₁ ok h (gate₁ x ↥) ()
    high₁ ok h (gate₂ x ↥) ()
    high₁ ok h (gate₀ x ↥ ↥) ()
    high₁ ok h (gate₁ x ↥ ↥) ()
    high₁ ok h (gate₀ x ↥ ↥ ↥) ()

    comm₁-case : ∀ m → AxOk m → (h : Gate 1) (g : Gen (₃₊ (suc m))) (c : View g) → view g ≡ c →
                 (₂₊ (₄₊ m)) ⊢ᵧ λ¹ (g ↥) • λ¹ (gate₁ h) ≈ λ¹ (gate₁ h) • λ¹ (g ↥)
    comm₁-case m       ok h .(g ↧) (low g) _  = via-top m ok (comm₁ᵧ h g)
    comm₁-case zero    ok h g      (high .g) e = high₁ ok h g e
    comm₁-case (suc m) ok h g      (high .g) e = high₁′ m ok h g e

    comm₂-case : ∀ m → AxOk m → (h : Gate 2) (g : Gen (₂₊ (suc m))) (c : View g) → view g ≡ c →
                 (₂₊ (₄₊ m)) ⊢ᵧ λ¹ (g ↥ ↥) • λ¹ (gate₂ h) ≈ λ¹ (gate₂ h) • λ¹ (g ↥ ↥)
    comm₂-case m ok h .(g ↧) (low g) _  = via-top m ok (comm₂ᵧ h g)
    comm₂-case m ok h g      (high .g) e = comm₂-high m h g e

  ok : ∀ m → AxOk m
  -- Four wires: completeness on five.
  ok zero {w} {v} a = complete₅ {λ¹ʷ w} {λ¹ʷ v} (λ¹-~ {0} {w} {v} (axiom-soundᵧ a))
  -- Five wires and more.
  ok (suc m) (srelᵧ (five (old r)))  = rule m (ok m) r
  ok (suc m) (srelᵧ (five ax))       = wide-ok {suc m} w-ax
  ok (suc m) (srelᵧ (five λ-lf))     = wide-ok {suc m} w-lf
  ok (suc m) (srelᵧ (five λ-hyb-sq)) = wide-ok {suc m} w-hyb-sq
  ok (suc m) (srelᵧ (five λ-hyb-yb)) = wide-ok {suc m} w-hyb-yb
  ok (suc m) (srelᵧ (five λ-ck-tct)) = wide-ok {suc m} w-ck-tct
  ok (suc m) (srelᵧ (ctl k p))       = PB.axiom (srelᵧ (ctl (suc k) p))
  ok (suc m) (cong↑ᵧ {w = w} {v} a)  =
    Eq.subst₂ (λ x y → _ ⊢ᵧ x ≈ y) (Eq.sym (λ¹ʷ-↑ w)) (Eq.sym (λ¹ʷ-↑ v))
      (lemma-cong↑ᵧ (λ¹ʷ w) (λ¹ʷ v) (ok m a))
  ok (suc m) (comm₁ᵧ h g)            = comm₁-case m (ok m) h g (view g) Eq.refl
  ok (suc m) (comm₂ᵧ h g)            = comm₂-case m (ok m) h g (view g) Eq.refl
  ok (suc m) (ω↑=ωᵧ I-gate)          = PB.refl

  -- Transport at every width.
  transportᵧ : ∀ m {u v} → (₄₊ m) ⊢ᵧ u ≈ v → (suc (₄₊ m)) ⊢ᵧ λ¹ʷ u ≈ λ¹ʷ v
  transportᵧ m = transport (ok m)
