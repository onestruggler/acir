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
--     commutation a width down, as for the rules;
--   - one where g reaches the top wire (`IsHigh`, of three shapes) has an
--     idle wire in the middle: for S or K on wire 0 it is wire 1, and
--     the commutation is the one a width down with wire 1 inserted
--     (Stable.Insert); for the CS on the wires 0 1, whose image borrows
--     the wires 2 3, it is wire 4 (Stable.Insert4), once g's image is
--     clear of the wires 0 … 3.
--
-- So transport into at most N wires rests on completeness on five wires
-- and the closed equations on six to N of nine wires (`Hyp N`): the two
-- borrowed-wire switches on six wires (Switch₆), and the commutations
-- where the images of the two letters cover every wire, so that no wire
-- can be inserted — the CS on the top two wires of a five-wire domain
-- against S or K on wire 0 (`comm₁-base`) and S or K on its top wire
-- against the CS on the wires 0 1 (`comm₂-base₁`), and the CS on the top
-- two wires of a domain of five to eight wires against the CS on the
-- wires 0 1 (`comm₂-base₂`), the image of the one borrowing the two
-- wires below it and that of the other the wires 2 3.  Each is an
-- equation of controlled gates with the same semantics, to be derived
-- from equations one width down by switching borrowed wires, as the
-- joint paper's b6.py does on six wires.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Stable.Transport where

open import Data.Nat using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
import Data.Nat as ℕ
import Data.Nat.Properties as NP
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₀ ; ₃ ; ₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

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
open import Examples.Groups.Clifford+CS.Stable.Insert4
  using (place₄-↑ ; Σᵗ-place ; topS ; top1 ; top2 ; λ¹-topS ; λ¹-top1 ; λ¹-top2 ; Zᵗ ; W)

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

-- A gate reaching the top wire is the scalar shifted all the way up, S
-- or K on the top wire, or the CS on the top two wires.
data Shape : Gen (suc k) → Set where
  sS : Shape (topS k)
  s1 : (h : Gate 1) → Shape (top1 k h)
  s2 : (h : Gate 2) → Shape {suc k} (top2 k h)

private
  up-inv : {g : Gen (suc k)} (c : View g) → up c ≡ high (g ↥) → c ≡ high g
  up-inv (low g)  ()
  up-inv (high g) _ = Eq.refl

  up-shape : {g : Gen (suc k)} → Shape g → Shape (g ↥)
  up-shape sS     = sS
  up-shape (s1 h) = s1 h
  up-shape (s2 h) = s2 h

high-shape : (g : Gen (suc k)) → IsHigh g → Shape g
high-shape {zero}        (gate₀ x) ()
high-shape {zero}        (gate₁ h) _ = s1 h
high-shape {zero}        (gate₀ I-gate ↥) _ = sS
high-shape {suc k}       (gate₀ x) ()
high-shape {suc k}       (gate₁ h) ()
high-shape {suc zero}    (gate₂ h) _ = s2 h
high-shape {suc (suc k)} (gate₂ h) ()
high-shape {suc k}       (g ↥) e = up-shape (high-shape g (up-inv (view g) e))

------------------------------------------------------------------------
-- The hypotheses

-- What transport into at most N wires needs.
record Hyp (N : ℕ) : Set where
  field
    complete₅ : ∀ {u v : Circuit 5} → ⟦ u ⟧ ~ ⟦ v ⟧ → 5 ⊢ᵧ u ≈ v
    switch    : Switch₆
    -- The CS on the top two wires of five against S or K on wire 0.
    comm₁-base : (h : Gate 1) →
                 (₂₊ (₄₊ zero)) ⊢ᵧ λ¹ {suc zero} (gate₂ CS-gate ↥ ↥ ↥) • λ¹ {suc zero} (gate₁ h)
                                 ≈ λ¹ {suc zero} (gate₁ h) • λ¹ {suc zero} (gate₂ CS-gate ↥ ↥ ↥)
    -- S or K on the top wire of five, and the CS on the top two wires of
    -- five to eight, against the CS on the wires 0 1.
    comm₂-base₁ : (h : Gate 1) →
                  (₂₊ (₄₊ zero)) ⊢ᵧ λ¹ {suc zero} (top1 4 h) • λ¹ {suc zero} (gate₂ CS-gate)
                                  ≈ λ¹ {suc zero} (gate₂ CS-gate) • λ¹ {suc zero} (top1 4 h)
    comm₂-base₂ : ∀ m → m ℕ.≤ 3 → ₂₊ (₄₊ m) ℕ.≤ N →
                  (₂₊ (₄₊ m)) ⊢ᵧ λ¹ {suc m} (top2 (₃₊ m) CS-gate) • λ¹ {suc m} (gate₂ CS-gate)
                               ≈ λ¹ {suc m} (gate₂ CS-gate) • λ¹ {suc m} (top2 (₃₊ m) CS-gate)

------------------------------------------------------------------------
-- Transport

-- λ¹ commutes with the shift.
λ¹ʷ-↑ : (w : Circuit (₄₊ m)) → λ¹ʷ (w ↑) ≡ λ¹ʷ w ↑
λ¹ʷ-↑ [ g ]ʷ  = Eq.refl
λ¹ʷ-↑ ε       = Eq.refl
λ¹ʷ-↑ (u • v) = Eq.cong₂ _•_ (λ¹ʷ-↑ u) (λ¹ʷ-↑ v)

module _ {N : ℕ} (H : Hyp N) where
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

    -- Both letters one width down with wire i inserted.
    via-place : ∀ i {r} {A B : Circuit (i +ℕ r)} {A′ B′ : Circuit (suc (i +ℕ r))} →
                (suc (i +ℕ r)) ⊢ᵧ A′ ≈ place i A → (suc (i +ℕ r)) ⊢ᵧ B′ ≈ place i B →
                (i +ℕ r) ⊢ᵧ A • B ≈ B • A → (suc (i +ℕ r)) ⊢ᵧ A′ • B′ ≈ B′ • A′
    via-place i {r} {A} {B} {A′} {B′} a b e = begin
      A′ • B′                 ≈⟨ cong a b ⟩
      place i A • place i B   ≈⟨ sym (place-•ᵧ i A B) ⟩
      place i (A • B)         ≈⟨ place-congᵧ i e ⟩
      place i (B • A)         ≈⟨ place-•ᵧ i B A ⟩
      place i B • place i A   ≈⟨ sym (cong b a) ⟩
      B′ • A′ ∎
      where open Tools ((suc (i +ℕ r)) YVRel,_===_)

    -- A letter on wire 0 against one reaching the top wire: wire 1 is idle.
    high₁′ : ∀ m → AxOk (suc m) → (h : Gate 1) (g : Gen (₃₊ (suc (suc m)))) → IsHigh g →
             (₂₊ (₄₊ (suc m))) ⊢ᵧ λ¹ (g ↥) • λ¹ (gate₁ h) ≈ λ¹ (gate₁ h) • λ¹ (g ↥)
    high₁′ m ok h (g ↥) _ =
      via-place 1 (PB.sym (embed (place₁-↑ (λ¹ {m} g)))) (λ¹₁-place (suc m) h) (ok (comm₁ᵧ h g))
    high₁′ m ok h (gate₀ x) ()
    high₁′ m ok h (gate₁ x) ()
    high₁′ m ok h (gate₂ x) ()

    -- The same on five wires, where λ¹ of a letter one wire up is not the
    -- image one wire up but the four-wire domain's own.
    high₁ : AxOk 0 → (h : Gate 1) (g : Gen 4) → IsHigh g →
            (₂₊ (₄₊ zero)) ⊢ᵧ λ¹ {suc zero} (g ↥) • λ¹ (gate₁ h) ≈ λ¹ (gate₁ h) • λ¹ {suc zero} (g ↥)
    high₁ ok h (gate₂ CS-gate ↥ ↥) _ = comm₁-base h
    high₁ ok h (gate₁ S-gate ↥ ↥ ↥) _ =
      via-place 1 (PB.sym (embed (place₁-↑ (CSᵗ ₀ ↑ ↑)))) (λ¹₁-place 0 h) (ok (comm₁ᵧ h (gate₁ S-gate ↥ ↥)))
    high₁ ok h (gate₁ K-gate ↥ ↥ ↥) _ =
      via-place 1 (PB.sym (embed (place₁-↑ (CKᵗ ₀ ↑ ↑)))) (λ¹₁-place 0 h) (ok (comm₁ᵧ h (gate₁ K-gate ↥ ↥)))
    high₁ ok h (gate₀ I-gate ↥ ↥ ↥ ↥) _ =
      via-place 1 (PB.sym (embed (place₁-↑ (Sᵗ ₃)))) (λ¹₁-place 0 h) (ok (comm₁ᵧ h (gate₀ I-gate ↥ ↥ ↥)))
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

    -- The CS on the wires 0 1 against a gate reaching the top wire: wire 4
    -- is idle, from six wires on for the scalar and S or K, from ten on
    -- for the CS on the top two wires.
    high₂ : ∀ m → ₂₊ (₄₊ m) ℕ.≤ N → AxOk m → (h : Gate 2) (g : Gen (₂₊ (suc m))) → Shape g →
            (₂₊ (₄₊ m)) ⊢ᵧ λ¹ (g ↥ ↥) • λ¹ (gate₂ h) ≈ λ¹ (gate₂ h) • λ¹ (g ↥ ↥)
    high₂ m q ok CS-gate _ sS =
      via-place 4
        (Eq.subst₂ (λ x y → _ ⊢ᵧ x ≈ place 4 y) (Eq.sym (λ¹-topS (suc m))) (Eq.sym (λ¹-topS m))
          (PB.sym (embed (place₄-↑ (Sᵗ m)))))
        (embed (Σᵗ-place m)) (ok (comm₂ᵧ CS-gate (topS (₁₊ m))))
    high₂ zero    q ok CS-gate _ (s1 h) = comm₂-base₁ h
    high₂ (suc m) q ok CS-gate _ (s1 h) =
      via-place 4
        (Eq.subst₂ (λ x y → _ ⊢ᵧ x ≈ place 4 y) (Eq.sym (λ¹-top1 (₂₊ m) h)) (Eq.sym (λ¹-top1 (suc m) h))
          (PB.sym (embed (place₄-↑ (Zᵗ m h)))))
        (embed (Σᵗ-place (suc m))) (ok (comm₂ᵧ CS-gate (top1 (₂₊ m) h)))
    high₂ zero                      q ok CS-gate _ (s2 CS-gate) = comm₂-base₂ zero ℕ.z≤n q
    high₂ (suc zero)                q ok CS-gate _ (s2 CS-gate) = comm₂-base₂ (suc zero) (ℕ.s≤s ℕ.z≤n) q
    high₂ (suc (suc zero))          q ok CS-gate _ (s2 CS-gate) =
      comm₂-base₂ (suc (suc zero)) (ℕ.s≤s (ℕ.s≤s ℕ.z≤n)) q
    high₂ (suc (suc (suc zero)))    q ok CS-gate _ (s2 CS-gate) =
      comm₂-base₂ (suc (suc (suc zero))) (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ℕ.z≤n))) q
    high₂ (suc (suc (suc (suc m)))) q ok CS-gate _ (s2 CS-gate) =
      via-place 4
        (Eq.subst₂ (λ x y → _ ⊢ᵧ x ≈ place 4 y) (Eq.sym (λ¹-top2 (suc (₄₊ m)))) (Eq.sym (λ¹-top2 (₄₊ m)))
          (PB.sym (embed (place₄-↑ (W m)))))
        (embed (Σᵗ-place (₄₊ m))) (ok (comm₂ᵧ CS-gate (top2 (₄₊ m) CS-gate)))

    comm₂-case : ∀ m → ₂₊ (₄₊ m) ℕ.≤ N → AxOk m → (h : Gate 2) (g : Gen (₂₊ (suc m))) (c : View g) → view g ≡ c →
                 (₂₊ (₄₊ m)) ⊢ᵧ λ¹ (g ↥ ↥) • λ¹ (gate₂ h) ≈ λ¹ (gate₂ h) • λ¹ (g ↥ ↥)
    comm₂-case m q ok h .(g ↧) (low g)   _ = via-top m ok (comm₂ᵧ h g)
    comm₂-case m q ok h g      (high .g) e = high₂ m q ok h g (high-shape g e)

  -- Transport into at most N wires.
  ok : ∀ m → suc (₄₊ m) ℕ.≤ N → AxOk m
  -- Four wires: completeness on five.
  ok zero _ {w} {v} a = complete₅ {λ¹ʷ w} {λ¹ʷ v} (λ¹-~ {0} {w} {v} (axiom-soundᵧ a))
  -- Five wires and more.
  ok (suc m) b (srelᵧ (five (old r)))  = rule m (ok m (NP.<⇒≤ b)) r
  ok (suc m) b (srelᵧ (five ax))       = wide-ok {suc m} w-ax
  ok (suc m) b (srelᵧ (five λ-lf))     = wide-ok {suc m} w-lf
  ok (suc m) b (srelᵧ (five λ-hyb-sq)) = wide-ok {suc m} w-hyb-sq
  ok (suc m) b (srelᵧ (five λ-hyb-yb)) = wide-ok {suc m} w-hyb-yb
  ok (suc m) b (srelᵧ (five λ-ck-tct)) = wide-ok {suc m} w-ck-tct
  ok (suc m) b (srelᵧ (ctl k p))       = PB.axiom (srelᵧ (ctl (suc k) p))
  ok (suc m) b (cong↑ᵧ {w = w} {v} a)  =
    Eq.subst₂ (λ x y → _ ⊢ᵧ x ≈ y) (Eq.sym (λ¹ʷ-↑ w)) (Eq.sym (λ¹ʷ-↑ v))
      (lemma-cong↑ᵧ (λ¹ʷ w) (λ¹ʷ v) (ok m (NP.<⇒≤ b) a))
  ok (suc m) b (comm₁ᵧ h g)            = comm₁-case m (ok m (NP.<⇒≤ b)) h g (view g) Eq.refl
  ok (suc m) b (comm₂ᵧ h g)            = comm₂-case m b (ok m (NP.<⇒≤ b)) h g (view g) Eq.refl
  ok (suc m) b (ω↑=ωᵧ I-gate)          = PB.refl

  -- Transport at every width.
  transportᵧ : ∀ m → suc (₄₊ m) ℕ.≤ N → ∀ {u v} → (₄₊ m) ⊢ᵧ u ≈ v → (suc (₄₊ m)) ⊢ᵧ λ¹ʷ u ≈ λ¹ʷ v
  transportᵧ m b = transport (ok m b)
