------------------------------------------------------------------------
-- Presentations of groups
--
-- (F5) and (F4) semantically, at every width
--
-- A domain gate is its white and black controlled halves, and a white
-- and a black controlled gate commute: the blocks of ctrl⁰ and ctrl
-- (`split`, `swap`), read through Lambda.Semantics (`F5-sem`, `F4-sem`).
-- Kept apart from Stable.Calc so that the base facts on seven to nine
-- wires (Stable.Base8, Base9) can use them without the transport.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Stable.CalcSem where

open import Data.Nat using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
import Relation.Binary.Reasoning.Setoid as SetoidR
open import Algebra.Bundles using (Monoid)
open import Word.Base using ([_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_)
open import Examples.Groups.Clifford+CS.Semantics.Control
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)
open import Examples.Groups.Clifford+CS.MultiControlled using (top ; _↧)
open import Examples.Groups.Clifford+CS.Lambda using (λ¹ ; λ⁰)
open import Examples.Groups.Clifford+CS.Lambda.Semantics using (⟦•⟧ ; topS ; ⟦top⟧ ; λ¹-sem ; λ⁰-sem)

private
  variable
    n : ℕ

  module R (n : ℕ) = SetoidR (Monoid.setoid (Scaled-monoid n))

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

