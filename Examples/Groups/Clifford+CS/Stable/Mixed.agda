------------------------------------------------------------------------
-- Presentations of groups
--
-- (F4) at every width: a white and a black controlled generator commute
--
-- Stable.Calc gives (F4), λ⁰ g • λ¹ h ≈ λ¹ h • λ⁰ g, for the pairs of
-- generators both lifted or both at the bottom of the domain.  The
-- pairs of a lifted generator g ↥ and a bottom one b go as the
-- transport's commutations do (Stable.Transport), with g ↥ white:
--
-- * if g ↥ leaves the top domain wire idle (`View.low`), the statement
--   is the one a width down stretched — λ¹ (g ↧) ≈ stretch (λ¹ g) is
--   Stable.Coherence (from the two six-wire switches), and λ⁰ (g ↧) ≈
--   stretch (λ⁰ g) with X on the control carried by stretch-X;
-- * if g ↥ reaches the top domain wire, there is an idle wire in the
--   middle — wire 1 for b on wire 0 (Stable.Insert), wire 4 for the CS
--   on the wires 0 1 once g ↥'s image is clear of the wires 0 … 3
--   (Stable.Insert4) — and the statement is the one a width down with
--   that wire inserted;
-- * the scalar b is the one a width down lifted;
--
-- and the pairs with b white follow by conjugating with X on the
-- control (`sym-col`).  What is left are the white versions of the
-- transport's base facts (`MixBase`): on six wires the CS on the top two
-- wires of a five-wire domain against S or K on wire 0, and S or K on
-- its top wire against the CS on the wires 0 1; on six to nine wires the
-- CS on the top two wires against the CS on the wires 0 1.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Stable.Mixed where

open import Data.Nat using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
import Data.Nat as ℕ
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_)

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.MultiControlled using (_↧)
open import Examples.Groups.Clifford+CS.Completeness using (complete₁)
open import Examples.Groups.Clifford+CS.SemanticSteps using (module Below)
open import Examples.Groups.Clifford+CS.Place using (place)
open import Examples.Groups.Clifford+CS.Lambda
open import Examples.Groups.Clifford+CS.Stable.Rules
open import Examples.Groups.Clifford+CS.Stable.Weakening using (stretch-congᵧ ; stretch-•ᵧ)
open import Examples.Groups.Clifford+CS.Stable.Coherence using (λ¹-top-gen)
open import Examples.Groups.Clifford+CS.Stable.Insert using (place-congᵧ ; place-•ᵧ ; place₁-↑ ; λ¹₁-place)
open import Examples.Groups.Clifford+CS.Stable.Insert4
  using (place₄-↑ ; Σᵗ-place ; topS ; top1 ; top2 ; λ¹-topS ; Zᵗ ; λ¹-top1 ; W ; λ¹-top2)
open import Examples.Groups.Clifford+CS.Stable.Transport using (View ; low ; high ; view ; IsHigh ; Shape ; sS ; s1 ; s2 ; high-shape)
open import Examples.Groups.Clifford+CS.Stable.HypFrom using (Completeᵧ ; Six)
open import Examples.Groups.Clifford+CS.Stable.Calc using (F4ᵗ ; F4-sem ; B ; bI ; bS ; bK ; bC ; gB ; f4-bot ; stretch-X)
open import Examples.Groups.Clifford+CS.Stable.Six.All using (six)

private
  variable
    n k : ℕ

  module S₁ = Below 1 complete₁

------------------------------------------------------------------------
-- The base facts

record MixBase : Set where
  field
    b₁ : (h : Gate 1) →
         (₂₊ (₄₊ zero)) ⊢ᵧ λ⁰ {suc zero} (gate₂ CS-gate ↥ ↥ ↥) • λ¹ {suc zero} (gate₁ h)
                         ≈ λ¹ {suc zero} (gate₁ h) • λ⁰ {suc zero} (gate₂ CS-gate ↥ ↥ ↥)
    b₂ : (h : Gate 1) →
         (₂₊ (₄₊ zero)) ⊢ᵧ λ⁰ {suc zero} (top1 4 h) • λ¹ {suc zero} (gate₂ CS-gate)
                         ≈ λ¹ {suc zero} (gate₂ CS-gate) • λ⁰ {suc zero} (top1 4 h)
    b₃ : ∀ m → m ℕ.≤ 3 →
         (₂₊ (₄₊ m)) ⊢ᵧ λ⁰ {suc m} (top2 (₃₊ m) CS-gate) • λ¹ {suc m} (gate₂ CS-gate)
                      ≈ λ¹ {suc m} (gate₂ CS-gate) • λ⁰ {suc m} (top2 (₃₊ m) CS-gate)

------------------------------------------------------------------------
-- X on the control

Xᵗ² : ∀ k → (₁₊ k) ⊢ Xᵗ k • Xᵗ k ≈ ε
Xᵗ² zero    = S₁.by-sem₀ (X • X) ε Eq.refl
Xᵗ² (suc k) = lemma-cong↑ (Xᵗ k • Xᵗ k) ε (Xᵗ² k)

-- The two colours exchanged: conjugate by X on the control.
sym-col : ∀ n (a c : Gen (₄₊ n)) →
          (suc (₄₊ n)) ⊢ᵧ λ⁰ a • λ¹ c ≈ λ¹ c • λ⁰ a →
          (suc (₄₊ n)) ⊢ᵧ λ⁰ c • λ¹ a ≈ λ¹ a • λ⁰ c
sym-col n a c e = sym (begin
  λ¹ a • (x • λ¹ c • x)                    ≈⟨ sym left-unit ⟩
  ε • λ¹ a • (x • λ¹ c • x)                ≈⟨ front _ (sym xx) ⟩
  (x • x) • λ¹ a • (x • λ¹ c • x)          ≈⟨ by-passoc ((□ • □) • □ • (□ • □ • □)) (□ • ((□ • □ • □) • □) • □) Eq.refl ⟩
  x • ((x • λ¹ a • x) • λ¹ c) • x          ≈⟨ back x (front x e) ⟩
  x • (λ¹ c • (x • λ¹ a • x)) • x          ≈⟨ by-passoc (□ • (□ • (□ • □ • □)) • □) ((□ • □ • □) • □ • (□ • □)) Eq.refl ⟩
  (x • λ¹ c • x) • λ¹ a • (x • x)          ≈⟨ back _ (back _ xx) ⟩
  (x • λ¹ c • x) • λ¹ a • ε                ≈⟨ back _ right-unit ⟩
  (x • λ¹ c • x) • λ¹ a ∎)
  where
  x = Xᵗ (₄₊ n)
  xx : (suc (₄₊ n)) ⊢ᵧ x • x ≈ ε
  xx = embed (Xᵗ² (₄₊ n))
  open Tools ((suc (₄₊ n)) YVRel,_===_)

------------------------------------------------------------------------
-- The reductions

module Reduce (c₅ : Completeᵧ 5) where

  private
    sw = Six.switch (six c₅)

  -- λ⁰ of a letter with an idle top domain wire.
  λ⁰-top : ∀ m (g : Gen (₄₊ m)) → (₂₊ (₄₊ m)) ⊢ᵧ λ⁰ {suc m} (g ↧) ≈ stretch (λ⁰ {m} g)
  λ⁰-top m g = begin
    x′ • λ¹ (g ↧) • x′                         ≈⟨ cong (sym sx) (cong (λ¹-top-gen sw m g) (sym sx)) ⟩
    stretch x • stretch (λ¹ g) • stretch x     ≈⟨ back _ (sym (stretch-•ᵧ (λ¹ g) x)) ⟩
    stretch x • stretch (λ¹ g • x)             ≈⟨ sym (stretch-•ᵧ x (λ¹ g • x)) ⟩
    stretch (x • λ¹ g • x) ∎
    where
    x = Xᵗ (₄₊ m)
    x′ = Xᵗ (suc (₄₊ m))
    sx : (₂₊ (₄₊ m)) ⊢ᵧ stretch x ≈ x′
    sx = embed (stretch-X (₃₊ m))
    open Tools ((₂₊ (₄₊ m)) YVRel,_===_)

  -- A pair with an idle top domain wire: the pair a width down, stretched.
  via-top : ∀ m (a c : Gen (₄₊ m)) → (suc (₄₊ m)) ⊢ᵧ λ⁰ a • λ¹ c ≈ λ¹ c • λ⁰ a →
            (₂₊ (₄₊ m)) ⊢ᵧ λ⁰ {suc m} (a ↧) • λ¹ (c ↧) ≈ λ¹ (c ↧) • λ⁰ {suc m} (a ↧)
  via-top m a c e = begin
    λ⁰ (a ↧) • λ¹ (c ↧)                    ≈⟨ cong (λ⁰-top m a) (λ¹-top-gen sw m c) ⟩
    stretch (λ⁰ a) • stretch (λ¹ c)        ≈⟨ sym (stretch-•ᵧ (λ⁰ a) (λ¹ c)) ⟩
    stretch (λ⁰ a • λ¹ c)                  ≈⟨ stretch-congᵧ e ⟩
    stretch (λ¹ c • λ⁰ a)                  ≈⟨ stretch-•ᵧ (λ¹ c) (λ⁰ a) ⟩
    stretch (λ¹ c) • stretch (λ⁰ a)        ≈⟨ sym (cong (λ¹-top-gen sw m c) (λ⁰-top m a)) ⟩
    λ¹ (c ↧) • λ⁰ (a ↧) ∎
    where open Tools ((₂₊ (₄₊ m)) YVRel,_===_)

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

  module _ (base : MixBase) where
    open MixBase base

    private
      -- A letter on wire 0 against a white letter reaching the top
      -- domain wire: wire 1 is idle.
      high₁′ : ∀ m → F4ᵗ (suc m) → (h : Gate 1) (g : Gen (₃₊ (suc (suc m)))) → IsHigh g →
               (₂₊ (₄₊ (suc m))) ⊢ᵧ λ⁰ (g ↥) • λ¹ (gate₁ h) ≈ λ¹ (gate₁ h) • λ⁰ (g ↥)
      high₁′ m F h (g ↥) _ =
        via-place 1 (PB.sym (embed (place₁-↑ (λ⁰ {m} g)))) (λ¹₁-place (suc m) h) (F (g ↥) (gate₁ h))
      high₁′ m F h (gate₀ x) ()
      high₁′ m F h (gate₁ x) ()
      high₁′ m F h (gate₂ x) ()

      -- The same on six wires.
      high₁ : F4ᵗ 0 → (h : Gate 1) (g : Gen 4) → IsHigh g →
              (₂₊ (₄₊ zero)) ⊢ᵧ λ⁰ {suc zero} (g ↥) • λ¹ (gate₁ h) ≈ λ¹ (gate₁ h) • λ⁰ {suc zero} (g ↥)
      high₁ F h (gate₂ CS-gate ↥ ↥) _ = b₁ h
      high₁ F h (gate₁ S-gate ↥ ↥ ↥) _ =
        via-place 1 (PB.sym (embed (place₁-↑ (Xᵗ ₃ • CSᵗ ₀ ↑ ↑ • Xᵗ ₃)))) (λ¹₁-place 0 h)
          (F (gate₁ S-gate ↥ ↥ ↥) (gate₁ h))
      high₁ F h (gate₁ K-gate ↥ ↥ ↥) _ =
        via-place 1 (PB.sym (embed (place₁-↑ (Xᵗ ₃ • CKᵗ ₀ ↑ ↑ • Xᵗ ₃)))) (λ¹₁-place 0 h)
          (F (gate₁ K-gate ↥ ↥ ↥) (gate₁ h))
      high₁ F h (gate₀ I-gate ↥ ↥ ↥ ↥) _ =
        via-place 1 (PB.sym (embed (place₁-↑ (Xᵗ ₃ • Sᵗ ₃ • Xᵗ ₃)))) (λ¹₁-place 0 h)
          (F (gate₀ I-gate ↥ ↥ ↥ ↥) (gate₁ h))
      high₁ F h (gate₀ x) ()
      high₁ F h (gate₁ x) ()
      high₁ F h (gate₂ x) ()
      high₁ F h (gate₀ x ↥) ()
      high₁ F h (gate₁ x ↥) ()
      high₁ F h (gate₂ x ↥) ()
      high₁ F h (gate₀ x ↥ ↥) ()
      high₁ F h (gate₁ x ↥ ↥) ()
      high₁ F h (gate₀ x ↥ ↥ ↥) ()

      one₁ : ∀ m → F4ᵗ m → (h : Gate 1) (g : Gen (₃₊ (suc m))) (c : View g) → view g ≡ c →
             (₂₊ (₄₊ m)) ⊢ᵧ λ⁰ (g ↥) • λ¹ (gate₁ h) ≈ λ¹ (gate₁ h) • λ⁰ (g ↥)
      one₁ m       F h .(g ↧) (low g)   _ = via-top m (g ↥) (gate₁ h) (F (g ↥) (gate₁ h))
      one₁ zero    F h g      (high .g) e = high₁ F h g e
      one₁ (suc m) F h g      (high .g) e = high₁′ m F h g e

      -- The CS on the wires 0 1 against a white letter reaching the top
      -- domain wire: wire 4 is idle, from six wires on for the scalar,
      -- seven for S or K, ten for the CS.
      high₂ : ∀ m → F4ᵗ m → (g : Gen (₄₊ m)) → Shape g →
              (₂₊ (₄₊ m)) ⊢ᵧ λ⁰ (g ↥) • λ¹ (gate₂ CS-gate) ≈ λ¹ (gate₂ CS-gate) • λ⁰ (g ↥)
      high₂ m F _ sS =
        via-place 4
          (Eq.subst₂ (λ x y → _ ⊢ᵧ x ≈ place 4 y)
             (Eq.sym (Eq.cong (λ x → Xᵗ (suc (₄₊ m)) • x • Xᵗ (suc (₄₊ m))) (λ¹-topS (suc m))))
             (Eq.sym (Eq.cong (λ x → Xᵗ (₄₊ m) • x • Xᵗ (₄₊ m)) (λ¹-topS m)))
             (PB.sym (embed (place₄-↑ (Xᵗ m • Sᵗ m • Xᵗ m)))))
          (embed (Σᵗ-place m)) (F (topS (₃₊ m)) (gate₂ CS-gate))
      high₂ zero    F _ (s1 h) = b₂ h
      high₂ (suc m) F _ (s1 h) =
        via-place 4
          (Eq.subst₂ (λ x y → _ ⊢ᵧ x ≈ place 4 y)
             (Eq.sym (Eq.cong (λ x → Xᵗ (₂₊ (₄₊ m)) • x • Xᵗ (₂₊ (₄₊ m))) (λ¹-top1 (₂₊ m) h)))
             (Eq.sym (Eq.cong (λ x → Xᵗ (suc (₄₊ m)) • x • Xᵗ (suc (₄₊ m))) (λ¹-top1 (suc m) h)))
             (PB.sym (embed (place₄-↑ (Xᵗ (₁₊ m) • Zᵗ m h • Xᵗ (₁₊ m))))))
          (embed (Σᵗ-place (suc m))) (F (top1 (₄₊ m) h) (gate₂ CS-gate))
      high₂ zero                      F _ (s2 CS-gate) = b₃ zero ℕ.z≤n
      high₂ (suc zero)                F _ (s2 CS-gate) = b₃ (suc zero) (ℕ.s≤s ℕ.z≤n)
      high₂ (suc (suc zero))          F _ (s2 CS-gate) = b₃ (suc (suc zero)) (ℕ.s≤s (ℕ.s≤s ℕ.z≤n))
      high₂ (suc (suc (suc zero)))    F _ (s2 CS-gate) =
        b₃ (suc (suc (suc zero))) (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s ℕ.z≤n)))
      high₂ (suc (suc (suc (suc m)))) F _ (s2 CS-gate) =
        via-place 4
          (Eq.subst₂ (λ x y → _ ⊢ᵧ x ≈ place 4 y)
             (Eq.sym (Eq.cong (λ x → Xᵗ (suc (₄₊ (₄₊ m))) • x • Xᵗ (suc (₄₊ (₄₊ m)))) (λ¹-top2 (suc (₄₊ m)))))
             (Eq.sym (Eq.cong (λ x → Xᵗ (₄₊ (₄₊ m)) • x • Xᵗ (₄₊ (₄₊ m))) (λ¹-top2 (₄₊ m))))
             (PB.sym (embed (place₄-↑ (Xᵗ (₄₊ m) • W m • Xᵗ (₄₊ m))))))
          (embed (Σᵗ-place (₄₊ m))) (F (top2 (₂₊ (₄₊ m)) CS-gate) (gate₂ CS-gate))

      two : ∀ m → F4ᵗ m → (g : Gen (₃₊ (suc m))) (c : View g) → view g ≡ c →
            (₂₊ (₄₊ m)) ⊢ᵧ λ⁰ (g ↥) • λ¹ (gate₂ CS-gate) ≈ λ¹ (gate₂ CS-gate) • λ⁰ (g ↥)
      two m F .(g ↧) (low g)   _ = via-top m (g ↥) (gate₂ CS-gate) (F (g ↥) (gate₂ CS-gate))
      two m F g      (high .g) e = high₂ m F g (high-shape g e)

    -- A white lifted generator against a black bottom one.
    mixˡ : ∀ m → F4ᵗ m → (g : Gen (₄₊ m)) (b : B) →
           (₂₊ (₄₊ m)) ⊢ᵧ λ⁰ {suc m} (g ↥) • λ¹ (gB b) ≈ λ¹ (gB b) • λ⁰ {suc m} (g ↥)
    mixˡ m F g bI = lemma-cong↑ᵧ (λ⁰ g • λ¹ (gate₀ I-gate)) (λ¹ (gate₀ I-gate) • λ⁰ g) (F g (gate₀ I-gate))
    mixˡ m F g bS = one₁ m F S-gate g (view g) Eq.refl
    mixˡ m F g bK = one₁ m F K-gate g (view g) Eq.refl
    mixˡ m F g bC = two m F g (view g) Eq.refl

    -- (F4) at every width.
    f4 : ∀ m → F4ᵗ m
    f4 zero    g h = c₅ (F4-sem g h)
    f4 (suc m) (gate₀ I-gate)  (gate₀ I-gate)  = f4-bot m bI bI (f4 m (gB bI) (gB bI))
    f4 (suc m) (gate₀ I-gate)  (gate₁ S-gate)  = f4-bot m bI bS (f4 m (gB bI) (gB bS))
    f4 (suc m) (gate₀ I-gate)  (gate₁ K-gate)  = f4-bot m bI bK (f4 m (gB bI) (gB bK))
    f4 (suc m) (gate₀ I-gate)  (gate₂ CS-gate) = f4-bot m bI bC (f4 m (gB bI) (gB bC))
    f4 (suc m) (gate₁ S-gate)  (gate₀ I-gate)  = f4-bot m bS bI (f4 m (gB bS) (gB bI))
    f4 (suc m) (gate₁ S-gate)  (gate₁ S-gate)  = f4-bot m bS bS (f4 m (gB bS) (gB bS))
    f4 (suc m) (gate₁ S-gate)  (gate₁ K-gate)  = f4-bot m bS bK (f4 m (gB bS) (gB bK))
    f4 (suc m) (gate₁ S-gate)  (gate₂ CS-gate) = f4-bot m bS bC (f4 m (gB bS) (gB bC))
    f4 (suc m) (gate₁ K-gate)  (gate₀ I-gate)  = f4-bot m bK bI (f4 m (gB bK) (gB bI))
    f4 (suc m) (gate₁ K-gate)  (gate₁ S-gate)  = f4-bot m bK bS (f4 m (gB bK) (gB bS))
    f4 (suc m) (gate₁ K-gate)  (gate₁ K-gate)  = f4-bot m bK bK (f4 m (gB bK) (gB bK))
    f4 (suc m) (gate₁ K-gate)  (gate₂ CS-gate) = f4-bot m bK bC (f4 m (gB bK) (gB bC))
    f4 (suc m) (gate₂ CS-gate) (gate₀ I-gate)  = f4-bot m bC bI (f4 m (gB bC) (gB bI))
    f4 (suc m) (gate₂ CS-gate) (gate₁ S-gate)  = f4-bot m bC bS (f4 m (gB bC) (gB bS))
    f4 (suc m) (gate₂ CS-gate) (gate₁ K-gate)  = f4-bot m bC bK (f4 m (gB bC) (gB bK))
    f4 (suc m) (gate₂ CS-gate) (gate₂ CS-gate) = f4-bot m bC bC (f4 m (gB bC) (gB bC))
    f4 (suc m) (g ↥) (h ↥) = lemma-cong↑ᵧ (λ⁰ g • λ¹ h) (λ¹ h • λ⁰ g) (f4 m g h)
    f4 (suc m) (g ↥) (gate₀ I-gate)  = mixˡ m (f4 m) g bI
    f4 (suc m) (g ↥) (gate₁ S-gate)  = mixˡ m (f4 m) g bS
    f4 (suc m) (g ↥) (gate₁ K-gate)  = mixˡ m (f4 m) g bK
    f4 (suc m) (g ↥) (gate₂ CS-gate) = mixˡ m (f4 m) g bC
    f4 (suc m) (gate₀ I-gate)  (h ↥) = sym-col (suc m) (h ↥) (gB bI) (mixˡ m (f4 m) h bI)
    f4 (suc m) (gate₁ S-gate)  (h ↥) = sym-col (suc m) (h ↥) (gB bS) (mixˡ m (f4 m) h bS)
    f4 (suc m) (gate₁ K-gate)  (h ↥) = sym-col (suc m) (h ↥) (gB bK) (mixˡ m (f4 m) h bK)
    f4 (suc m) (gate₂ CS-gate) (h ↥) = sym-col (suc m) (h ↥) (gB bC) (mixˡ m (f4 m) h bC)
