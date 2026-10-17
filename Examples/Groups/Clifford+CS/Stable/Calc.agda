------------------------------------------------------------------------
-- Presentations of groups
--
-- The λ-calculus at every width: (F5) and (F4) for generators
--
-- The affine decoding of Five rests on two facts about the controlled
-- functor (Five.Calc): (F5) a domain gate is its white and its black
-- controlled halves, g = λ⁰ g • λ¹ g, and (F4) a white and a black
-- controlled gate commute, λ⁰ g • λ¹ h = λ¹ h • λ⁰ g.  Both hold
-- semantically at every width — the blocks of ctrl⁰ and ctrl (`split`,
-- `swap`) — so on five wires they are completeness there.  From six on
-- they go by induction on the width: a generator one wire up is the
-- generator one width down lifted, so the statement is lifted
-- (λ⁰ (g ↥) = λ⁰ g ↑, λ¹ (g ↥) = λ¹ g ↑); a generator at the bottom of
-- the domain is the one a width down with an idle wire stretched in
-- below the control (λ¹ of S, K, CS by definition, of the scalar by
-- `stretch-S`, and X on the control by `stretch-X`), so the statement is
-- stretched.  That gives (F5) at every width (`f5`), and (F4) for every
-- pair of generators both lifted or both at the bottom; the pairs of a
-- lifted and a bottom generator are the record `Mixed`, what is left
-- (`f4`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Stable.Calc where

open import Data.Nat using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
import Relation.Binary.Reasoning.Setoid as SetoidR
open import Algebra.Bundles using (Monoid)
open import Word.Base using ([_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_)
open import Examples.Groups.Clifford+CS.Semantics.Control
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.MultiControlled using (top ; _↧)
open import Examples.Groups.Clifford+CS.Completeness using (complete₂)
open import Examples.Groups.Clifford+CS.SemanticSteps using (module Below)
open import Examples.Groups.Clifford+CS.Lambda
open import Examples.Groups.Clifford+CS.Lambda.Semantics using (⟦•⟧ ; topS ; ⟦top⟧ ; λ¹-sem ; λ⁰-sem)
open import Examples.Groups.Clifford+CS.Lambda.Split using (top-↑ ; Sw²)
open import Examples.Groups.Clifford+CS.Stable.Rules
open import Examples.Groups.Clifford+CS.Stable.Weakening using (stretch-congᵧ ; stretch-•ᵧ)
open import Examples.Groups.Clifford+CS.Stable.Coherence using (stretch-S)
open import Examples.Groups.Clifford+CS.Stable.HypFrom using (Completeᵧ)

private
  variable
    n k : ℕ

  module R (n : ℕ) = SetoidR (Monoid.setoid (Scaled-monoid n))

  module S₂ = Below 2 complete₂

------------------------------------------------------------------------
-- The blocks of ctrl⁰ and ctrl

private
  -- Two blocks of the same scale.
  blk-~ : {l l′ : ℕ} {P P′ M M′ : Op n} → (l , P) ~ (l′ , P′) → (l , M) ~ (l′ , M′) →
          (l , blk P M) ~ (l′ , blk P′ M′)
  blk-~ {l = l} {l′} {P} {P′} {M} {M′} e f x y =
    Eq.trans (Eq.sym (blk-scale (γ^ l′) P M x y))
      (Eq.trans (blk-cong e f x y) (blk-scale (γ^ l) P′ M′ x y))

  -- The scalar block of ctrl is the unit.
  unit~ : (b : ℕ) → (b , scal {n} (γ^ b)) ~ ε∙
  unit~ b x y = *-identityˡ (γ^ b * δb x y)

  -- s times the unit block, on either side.
  ∙u : (s : Scaled n) (b : ℕ) → (s ∙ (b , scal (γ^ b))) ~ s
  ∙u s b = ~-trans {s = s ∙ (b , scal (γ^ b))} {t = s ∙ ε∙} {u = s}
             (∙-cong {s = s} {s} {b , scal (γ^ b)} {ε∙} (~-refl s) (unit~ b)) (∙-identityʳ s)

  u∙ : (s : Scaled n) (b : ℕ) → ((b , scal (γ^ b)) ∙ s) ~ s
  u∙ s b = ~-trans {s = (b , scal (γ^ b)) ∙ s} {t = ε∙ ∙ s} {u = s}
             (∙-cong {s = b , scal (γ^ b)} {ε∙} {s} {s} (unit~ b) (~-refl s)) (∙-identityˡ s)

-- A gate with an idle control wire is its white and black halves.
split : (s : Scaled n) → (ctrl⁰ s ∙ ctrl s) ~ topS s
split (l , M) =
  ~-trans {s = ctrl⁰ (l , M) ∙ ctrl (l , M)}
          {t = (l +ℕ l , blk (M ⊙ scal (γ^ l)) (scal (γ^ l) ⊙ M))}
          {u = topS (l , M)}
    (~-reflexive {l = l +ℕ l} {l +ℕ l}
                 {M = blk M (scal (γ^ l)) ⊙ blk (scal (γ^ l)) M}
                 {blk (M ⊙ scal (γ^ l)) (scal (γ^ l) ⊙ M)} Eq.refl
                 (blk-⊙ M (scal (γ^ l)) (scal (γ^ l)) M))
    (blk-~ {l = l +ℕ l} {l} {M ⊙ scal (γ^ l)} {M} {scal (γ^ l) ⊙ M} {M}
       (∙u (l , M) l) (u∙ (l , M) l))

-- A white and a black controlled gate commute.
swap : (s t : Scaled n) → (ctrl⁰ s ∙ ctrl t) ~ (ctrl t ∙ ctrl⁰ s)
swap (a , A) (b , B) =
  ~-trans {s = ctrl⁰ (a , A) ∙ ctrl (b , B)}
          {t = (a +ℕ b , blk (A ⊙ scal (γ^ b)) (scal (γ^ a) ⊙ B))}
          {u = ctrl (b , B) ∙ ctrl⁰ (a , A)}
    (~-reflexive {l = a +ℕ b} {a +ℕ b}
                 {M = blk A (scal (γ^ a)) ⊙ blk (scal (γ^ b)) B}
                 {blk (A ⊙ scal (γ^ b)) (scal (γ^ a) ⊙ B)} Eq.refl
                 (blk-⊙ A (scal (γ^ a)) (scal (γ^ b)) B))
  (~-trans {s = (a +ℕ b , blk (A ⊙ scal (γ^ b)) (scal (γ^ a) ⊙ B))}
           {t = (b +ℕ a , blk (scal (γ^ b) ⊙ A) (B ⊙ scal (γ^ a)))}
           {u = ctrl (b , B) ∙ ctrl⁰ (a , A)}
    (blk-~ {l = a +ℕ b} {b +ℕ a} {A ⊙ scal (γ^ b)} {scal (γ^ b) ⊙ A} {scal (γ^ a) ⊙ B} {B ⊙ scal (γ^ a)}
       (~-trans {s = (a , A) ∙ (b , scal (γ^ b))} {t = (a , A)} {u = (b , scal (γ^ b)) ∙ (a , A)}
          (∙u (a , A) b) (~-sym {s = (b , scal (γ^ b)) ∙ (a , A)} {t = (a , A)} (u∙ (a , A) b)))
       (~-trans {s = (a , scal (γ^ a)) ∙ (b , B)} {t = (b , B)} {u = (b , B) ∙ (a , scal (γ^ a))}
          (u∙ (b , B) a) (~-sym {s = (b , B) ∙ (a , scal (γ^ a))} {t = (b , B)} (∙u (b , B) a))))
    (~-reflexive {l = b +ℕ a} {b +ℕ a}
                 {M = blk (scal (γ^ b) ⊙ A) (B ⊙ scal (γ^ a))}
                 {blk (scal (γ^ b)) B ⊙ blk A (scal (γ^ a))} Eq.refl
                 (≐-sym (blk-⊙ (scal (γ^ b)) B A (scal (γ^ a))))))

------------------------------------------------------------------------
-- The two facts, semantically, at every width

F5-sem : (g : Gen (₄₊ n)) → ⟦ [ g ↧ ]ʷ ⟧ ~ ⟦ λ⁰ g • λ¹ g ⟧
F5-sem {n} g = begin
  ⟦ top [ g ]ʷ ⟧                      ≈⟨ ⟦top⟧ [ g ]ʷ ⟩
  topS ⟦ [ g ]ʷ ⟧                     ≈⟨ ~-sym {s = ctrl⁰ ⟦ [ g ]ʷ ⟧ ∙ ctrl ⟦ [ g ]ʷ ⟧} {t = topS ⟦ [ g ]ʷ ⟧}
                                           (split ⟦ [ g ]ʷ ⟧) ⟩
  ctrl⁰ ⟦ [ g ]ʷ ⟧ ∙ ctrl ⟦ [ g ]ʷ ⟧   ≈⟨ ∙-cong {s = ctrl⁰ ⟦ [ g ]ʷ ⟧} {⟦ λ⁰ g ⟧} {ctrl ⟦ [ g ]ʷ ⟧} {⟦ λ¹ g ⟧}
                                           (~-sym {s = ⟦ λ⁰ g ⟧} {t = ctrl⁰ ⟦ [ g ]ʷ ⟧} (λ⁰-sem [ g ]ʷ))
                                           (~-sym {s = ⟦ λ¹ g ⟧} {t = ctrl ⟦ [ g ]ʷ ⟧} (λ¹-sem [ g ]ʷ)) ⟩
  ⟦ λ⁰ g ⟧ ∙ ⟦ λ¹ g ⟧                 ≈⟨ ~-sym {s = ⟦ λ⁰ g • λ¹ g ⟧} {t = ⟦ λ⁰ g ⟧ ∙ ⟦ λ¹ g ⟧} (⟦•⟧ (λ⁰ g) (λ¹ g)) ⟩
  ⟦ λ⁰ g • λ¹ g ⟧                     ∎
  where open R (suc (₄₊ n))

F4-sem : (g h : Gen (₄₊ n)) → ⟦ λ⁰ g • λ¹ h ⟧ ~ ⟦ λ¹ h • λ⁰ g ⟧
F4-sem {n} g h = begin
  ⟦ λ⁰ g • λ¹ h ⟧                     ≈⟨ ⟦•⟧ (λ⁰ g) (λ¹ h) ⟩
  ⟦ λ⁰ g ⟧ ∙ ⟦ λ¹ h ⟧                 ≈⟨ ∙-cong {s = ⟦ λ⁰ g ⟧} {ctrl⁰ ⟦ [ g ]ʷ ⟧} {⟦ λ¹ h ⟧} {ctrl ⟦ [ h ]ʷ ⟧}
                                           (λ⁰-sem [ g ]ʷ) (λ¹-sem [ h ]ʷ) ⟩
  ctrl⁰ ⟦ [ g ]ʷ ⟧ ∙ ctrl ⟦ [ h ]ʷ ⟧   ≈⟨ swap ⟦ [ g ]ʷ ⟧ ⟦ [ h ]ʷ ⟧ ⟩
  ctrl ⟦ [ h ]ʷ ⟧ ∙ ctrl⁰ ⟦ [ g ]ʷ ⟧   ≈⟨ ∙-cong {s = ctrl ⟦ [ h ]ʷ ⟧} {⟦ λ¹ h ⟧} {ctrl⁰ ⟦ [ g ]ʷ ⟧} {⟦ λ⁰ g ⟧}
                                           (~-sym {s = ⟦ λ¹ h ⟧} {t = ctrl ⟦ [ h ]ʷ ⟧} (λ¹-sem [ h ]ʷ))
                                           (~-sym {s = ⟦ λ⁰ g ⟧} {t = ctrl⁰ ⟦ [ g ]ʷ ⟧} (λ⁰-sem [ g ]ʷ)) ⟩
  ⟦ λ¹ h ⟧ ∙ ⟦ λ⁰ g ⟧                 ≈⟨ ~-sym {s = ⟦ λ¹ h • λ⁰ g ⟧} {t = ⟦ λ¹ h ⟧ ∙ ⟦ λ⁰ g ⟧} (⟦•⟧ (λ¹ h) (λ⁰ g)) ⟩
  ⟦ λ¹ h • λ⁰ g ⟧                     ∎
  where open R (suc (₄₊ n))

------------------------------------------------------------------------
-- The statements

F5ᵗ F4ᵗ : ℕ → Set
F5ᵗ n = ∀ (g : Gen (₄₊ n)) → (suc (₄₊ n)) ⊢ᵧ [ g ↧ ]ʷ ≈ λ⁰ g • λ¹ g
F4ᵗ n = ∀ (g h : Gen (₄₊ n)) → (suc (₄₊ n)) ⊢ᵧ λ⁰ g • λ¹ h ≈ λ¹ h • λ⁰ g

------------------------------------------------------------------------
-- The generators at the bottom of the domain, stretched

-- The four generators on the wires 0, 1.
data B : Set where
  bI bS bK bC : B

gB : B → Gen (₄₊ n)
gB bI = gate₀ I-gate
gB bS = gate₁ S-gate
gB bK = gate₁ K-gate
gB bC = gate₂ CS-gate

-- X on the top wire, carried to the new top wire.
stretch-X : ∀ k → (₃₊ k) ⊢ stretch (Xᵗ (₁₊ k)) ≈ Xᵗ (₂₊ k)
stretch-X zero    = lemma-cong↑ (Swap • X • Swap) (X ↑) (S₂.by-sem₀ (Swap • X • Swap) (X ↑) Eq.refl)
stretch-X (suc k) =
  Eq.subst (λ x → (₄₊ k) ⊢ Swᵗ (₂₊ k) • x • Swᵗ (₂₊ k) ≈ Xᵗ (₃₊ k))
           (Eq.sym (top-↑ (Xᵗ (₁₊ k))))
           (lemma-cong↑ (stretch (Xᵗ (₁₊ k))) (Xᵗ (₂₊ k)) (stretch-X k))

private
  -- λ¹ of a bottom generator, stretched.
  stretch-λ¹ : ∀ n (b : B) → (₂₊ (₄₊ n)) ⊢ᵧ stretch (λ¹ {n} (gB b)) ≈ λ¹ {suc n} (gB b)
  stretch-λ¹ n bI = embed (stretch-S (₃₊ n))
  stretch-λ¹ n bS = PB.refl
  stretch-λ¹ n bK = PB.refl
  stretch-λ¹ n bC = PB.refl

  stretch-λ⁰ : ∀ n (b : B) → (₂₊ (₄₊ n)) ⊢ᵧ stretch (λ⁰ {n} (gB b)) ≈ λ⁰ {suc n} (gB b)
  stretch-λ⁰ n b = begin
    stretch (Xt • λ¹ (gB b) • Xt)                 ≈⟨ stretch-•ᵧ Xt (λ¹ (gB b) • Xt) ⟩
    stretch Xt • stretch (λ¹ (gB b) • Xt)         ≈⟨ cong (embed (stretch-X (₃₊ n)))
                                                        (trans (stretch-•ᵧ (λ¹ (gB b)) Xt)
                                                          (cong (stretch-λ¹ n b) (embed (stretch-X (₃₊ n))))) ⟩
    λ⁰ {suc n} (gB b)                              ∎
    where
    Xt = Xᵗ (₄₊ n)
    open Tools ((₂₊ (₄₊ n)) YVRel,_===_)

  -- The swap of the top two wires passes a bottom generator.
  pass : (w g : Circuit k) → k ⊢ w • g ≈ g • w → k ⊢ w • w ≈ ε → k ⊢ w • g • w ≈ g
  pass {k} w g c ww = begin
    w • g • w      ≈⟨ sym assoc ⟩
    (w • g) • w    ≈⟨ front _ c ⟩
    (g • w) • w    ≈⟨ assoc ⟩
    g • w • w      ≈⟨ back _ ww ⟩
    g • ε          ≈⟨ right-unit ⟩
    g              ∎
    where open Tools (k VRel,_===_)

  sw-pass : ∀ n (b : B) → (₂₊ (₄₊ n)) ⊢ Swᵗ (₄₊ n) • [ gB {n} b ↧ ↧ ]ʷ • Swᵗ (₄₊ n) ≈ [ gB {suc n} b ↧ ]ʷ
  sw-pass n bI = pass (Swᵗ (₄₊ n)) _ (comm-gate₀-w I-gate (Swᵗ (₄₊ n))) (Sw² (₄₊ n))
  sw-pass n bS = pass (Swᵗ (₄₊ n)) _ (comm-gate₁-w↑ S-gate (Swᵗ (₃₊ n))) (Sw² (₄₊ n))
  sw-pass n bK = pass (Swᵗ (₄₊ n)) _ (comm-gate₁-w↑ K-gate (Swᵗ (₃₊ n))) (Sw² (₄₊ n))
  sw-pass n bC = pass (Swᵗ (₄₊ n)) _ (comm-gate₂-w↑↑ CS-gate (Swᵗ (₂₊ n))) (Sw² (₄₊ n))

------------------------------------------------------------------------
-- (F5) at every width

f5-bot : ∀ n (b : B) → (suc (₄₊ n)) ⊢ᵧ [ gB {n} b ↧ ]ʷ ≈ λ⁰ (gB b) • λ¹ (gB b) →
         (₂₊ (₄₊ n)) ⊢ᵧ [ gB {suc n} b ↧ ]ʷ ≈ λ⁰ (gB b) • λ¹ (gB b)
f5-bot n b e = begin
  [ gB {suc n} b ↧ ]ʷ                           ≈⟨ sym (embed (sw-pass n b)) ⟩
  stretch [ gB {n} b ↧ ]ʷ                       ≈⟨ stretch-congᵧ e ⟩
  stretch (λ⁰ (gB b) • λ¹ (gB b))               ≈⟨ stretch-•ᵧ (λ⁰ (gB b)) (λ¹ (gB b)) ⟩
  stretch (λ⁰ (gB b)) • stretch (λ¹ (gB b))     ≈⟨ cong (stretch-λ⁰ n b) (stretch-λ¹ n b) ⟩
  λ⁰ (gB b) • λ¹ (gB b)                         ∎
  where open Tools ((₂₊ (₄₊ n)) YVRel,_===_)

f5 : Completeᵧ 5 → ∀ n → F5ᵗ n
f5 c₅ zero    g                  = c₅ (F5-sem g)
f5 c₅ (suc n) (gate₀ I-gate)     = f5-bot n bI (f5 c₅ n (gate₀ I-gate))
f5 c₅ (suc n) (gate₁ S-gate)     = f5-bot n bS (f5 c₅ n (gate₁ S-gate))
f5 c₅ (suc n) (gate₁ K-gate)     = f5-bot n bK (f5 c₅ n (gate₁ K-gate))
f5 c₅ (suc n) (gate₂ CS-gate)    = f5-bot n bC (f5 c₅ n (gate₂ CS-gate))
f5 c₅ (suc n) (g ↥)              = lemma-cong↑ᵧ [ g ↧ ]ʷ (λ⁰ g • λ¹ g) (f5 c₅ n g)

------------------------------------------------------------------------
-- (F4) at every width, given the mixed pairs

-- A lifted generator against a bottom one, in both colours.
record Mixed (n : ℕ) : Set where
  field
    mixˡ : ∀ (g : Gen (₄₊ n)) (b : B) →
           (₂₊ (₄₊ n)) ⊢ᵧ λ⁰ {suc n} (g ↥) • λ¹ (gB b) ≈ λ¹ (gB b) • λ⁰ {suc n} (g ↥)
    mixʳ : ∀ (b : B) (h : Gen (₄₊ n)) →
           (₂₊ (₄₊ n)) ⊢ᵧ λ⁰ {suc n} (gB b) • λ¹ (h ↥) ≈ λ¹ (h ↥) • λ⁰ {suc n} (gB b)

f4-bot : ∀ n (b c : B) → (suc (₄₊ n)) ⊢ᵧ λ⁰ (gB {n} b) • λ¹ (gB c) ≈ λ¹ (gB c) • λ⁰ (gB b) →
         (₂₊ (₄₊ n)) ⊢ᵧ λ⁰ (gB {suc n} b) • λ¹ (gB c) ≈ λ¹ (gB c) • λ⁰ (gB {suc n} b)
f4-bot n b c e = begin
  λ⁰ (gB b) • λ¹ (gB c)                         ≈⟨ sym (cong (stretch-λ⁰ n b) (stretch-λ¹ n c)) ⟩
  stretch (λ⁰ (gB b)) • stretch (λ¹ (gB c))     ≈⟨ sym (stretch-•ᵧ (λ⁰ (gB b)) (λ¹ (gB c))) ⟩
  stretch (λ⁰ (gB b) • λ¹ (gB c))               ≈⟨ stretch-congᵧ e ⟩
  stretch (λ¹ (gB c) • λ⁰ (gB b))               ≈⟨ stretch-•ᵧ (λ¹ (gB c)) (λ⁰ (gB b)) ⟩
  stretch (λ¹ (gB c)) • stretch (λ⁰ (gB b))     ≈⟨ cong (stretch-λ¹ n c) (stretch-λ⁰ n b) ⟩
  λ¹ (gB c) • λ⁰ (gB b)                         ∎
  where open Tools ((₂₊ (₄₊ n)) YVRel,_===_)

module F4 (c₅ : Completeᵧ 5) (mix : ∀ n → Mixed n) where

  f4 : ∀ n → F4ᵗ n
  f4 zero    g h = c₅ (F4-sem g h)
  f4 (suc n) (gate₀ I-gate)  (gate₀ I-gate)  = f4-bot n bI bI (f4 n (gB bI) (gB bI))
  f4 (suc n) (gate₀ I-gate)  (gate₁ S-gate)  = f4-bot n bI bS (f4 n (gB bI) (gB bS))
  f4 (suc n) (gate₀ I-gate)  (gate₁ K-gate)  = f4-bot n bI bK (f4 n (gB bI) (gB bK))
  f4 (suc n) (gate₀ I-gate)  (gate₂ CS-gate) = f4-bot n bI bC (f4 n (gB bI) (gB bC))
  f4 (suc n) (gate₁ S-gate)  (gate₀ I-gate)  = f4-bot n bS bI (f4 n (gB bS) (gB bI))
  f4 (suc n) (gate₁ S-gate)  (gate₁ S-gate)  = f4-bot n bS bS (f4 n (gB bS) (gB bS))
  f4 (suc n) (gate₁ S-gate)  (gate₁ K-gate)  = f4-bot n bS bK (f4 n (gB bS) (gB bK))
  f4 (suc n) (gate₁ S-gate)  (gate₂ CS-gate) = f4-bot n bS bC (f4 n (gB bS) (gB bC))
  f4 (suc n) (gate₁ K-gate)  (gate₀ I-gate)  = f4-bot n bK bI (f4 n (gB bK) (gB bI))
  f4 (suc n) (gate₁ K-gate)  (gate₁ S-gate)  = f4-bot n bK bS (f4 n (gB bK) (gB bS))
  f4 (suc n) (gate₁ K-gate)  (gate₁ K-gate)  = f4-bot n bK bK (f4 n (gB bK) (gB bK))
  f4 (suc n) (gate₁ K-gate)  (gate₂ CS-gate) = f4-bot n bK bC (f4 n (gB bK) (gB bC))
  f4 (suc n) (gate₂ CS-gate) (gate₀ I-gate)  = f4-bot n bC bI (f4 n (gB bC) (gB bI))
  f4 (suc n) (gate₂ CS-gate) (gate₁ S-gate)  = f4-bot n bC bS (f4 n (gB bC) (gB bS))
  f4 (suc n) (gate₂ CS-gate) (gate₁ K-gate)  = f4-bot n bC bK (f4 n (gB bC) (gB bK))
  f4 (suc n) (gate₂ CS-gate) (gate₂ CS-gate) = f4-bot n bC bC (f4 n (gB bC) (gB bC))
  f4 (suc n) (g ↥) (h ↥) = lemma-cong↑ᵧ (λ⁰ g • λ¹ h) (λ¹ h • λ⁰ g) (f4 n g h)
  f4 (suc n) (g ↥) (gate₀ I-gate)  = Mixed.mixˡ (mix n) g bI
  f4 (suc n) (g ↥) (gate₁ S-gate)  = Mixed.mixˡ (mix n) g bS
  f4 (suc n) (g ↥) (gate₁ K-gate)  = Mixed.mixˡ (mix n) g bK
  f4 (suc n) (g ↥) (gate₂ CS-gate) = Mixed.mixˡ (mix n) g bC
  f4 (suc n) (gate₀ I-gate)  (h ↥) = Mixed.mixʳ (mix n) bI h
  f4 (suc n) (gate₁ S-gate)  (h ↥) = Mixed.mixʳ (mix n) bS h
  f4 (suc n) (gate₁ K-gate)  (h ↥) = Mixed.mixʳ (mix n) bK h
  f4 (suc n) (gate₂ CS-gate) (h ↥) = Mixed.mixʳ (mix n) bC h
