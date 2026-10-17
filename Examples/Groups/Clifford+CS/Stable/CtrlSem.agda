------------------------------------------------------------------------
-- Presentations of groups
--
-- Controlled operators conjugated below the control, and controlled
-- lines
--
-- Evaluating a doubly controlled S costs gigabytes on five wires and is
-- out of reach on six (Stable.Windows6).  But its semantics is known —
-- a λ¹-image denotes the controlled operator of its domain word
-- (Lambda.Semantics.λ¹-sem) — and what a window does to it is to
-- conjugate it by circuits below the control: top N • w • top N′ with
-- N • N′ = ε denotes ctrl ⟦ N • d • N′ ⟧ when w denotes ctrl ⟦ d ⟧
-- (`conj-ctrl`, from `core′`: the two blocks of topS ⟦N⟧ conjugate the
-- two blocks of ctrl ⟦d⟧, the scalar block back to the unit).  A product
-- of such gates denotes the controlled product (`ctrl-•`), so two lines
-- of them are compared by evaluating their domain words, one wire
-- narrower and without the S-boxes.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Stable.CtrlSem where

open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊)

open import Examples.Groups.Clifford+CS.Semantics hiding (_^_)
open import Examples.Groups.Clifford+CS.Semantics.Control
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Interpretation using (⟦_⟧)
open import Examples.Groups.Clifford+CS.MultiControlled using (top)
open import Examples.Groups.Clifford+CS.Lambda.Semantics using (⟦ε⟧ ; ⟦•⟧ ; topS ; ⟦top⟧)

private
  variable
    n : ℕ

  -- Two blocks of the same scale.
  blk-~ : {l l′ : ℕ} {P P′ M M′ : Op n} → (l , P) ~ (l′ , P′) → (l , M) ~ (l′ , M′) →
          (l , blk P M) ~ (l′ , blk P′ M′)
  blk-~ {l = l} {l′} {P} {P′} {M} {M′} e f x y =
    Eq.trans (Eq.sym (blk-scale (γ^ l′) P M x y))
      (Eq.trans (blk-cong e f x y) (blk-scale (γ^ l) P′ M′ x y))

  -- The scalar block of ctrl is the unit.
  unit~ : (b : ℕ) → (b , scal {n} (γ^ b)) ~ ε∙
  unit~ b x y = *-identityˡ (γ^ b * δb x y)

------------------------------------------------------------------------
-- Conjugating a controlled operator below the control

core′ : (s t s′ : Scaled n) → (s ∙ s′) ~ ε∙ →
        (topS s ∙ (ctrl t ∙ topS s′)) ~ ctrl (s ∙ (t ∙ s′))
core′ (a , A) (b , B) (a′ , A′) h =
  ~-trans {s = topS s ∙ (ctrl (b , B) ∙ topS s′)}
          {t = (L , blk (A ⊙ (scal (γ^ b) ⊙ A′)) (A ⊙ (B ⊙ A′)))}
          {u = ctrl (L , A ⊙ (B ⊙ A′))}
    (~-reflexive {l = L} {L}
                 {M = blk A A ⊙ (blk (scal (γ^ b)) B ⊙ blk A′ A′)}
                 {blk (A ⊙ (scal (γ^ b) ⊙ A′)) (A ⊙ (B ⊙ A′))} Eq.refl
       (≐-trans (⊙-cong (≐-refl (blk A A)) (blk-⊙ (scal (γ^ b)) B A′ A′))
                (blk-⊙ A A (scal (γ^ b) ⊙ A′) (B ⊙ A′))))
    (blk-~ {l = L} {L} {A ⊙ (scal (γ^ b) ⊙ A′)} {scal (γ^ L)} {A ⊙ (B ⊙ A′)} {A ⊙ (B ⊙ A′)}
       comp₁ (~-refl (L , A ⊙ (B ⊙ A′))))
  where
  s = (a , A)
  s′ = (a′ , A′)
  L = a +ℕ (b +ℕ a′)
  u = (b , scal (γ^ b))
  comp₁ : (L , A ⊙ (scal (γ^ b) ⊙ A′)) ~ (L , scal (γ^ L))
  comp₁ =
    ~-trans {s = s ∙ (u ∙ s′)} {t = s ∙ (ε∙ ∙ s′)} {u = L , scal (γ^ L)}
      (∙-cong {s = s} {s} {u ∙ s′} {ε∙ ∙ s′} (~-refl s) (∙-cong {s = u} {ε∙} {s′} {s′} (unit~ b) (~-refl s′)))
      (~-trans {s = s ∙ (ε∙ ∙ s′)} {t = s ∙ s′} {u = L , scal (γ^ L)}
        (∙-cong {s = s} {s} {ε∙ ∙ s′} {s′} (~-refl s) (∙-identityˡ s′))
        (~-trans {s = s ∙ s′} {t = ε∙} {u = L , scal (γ^ L)} h
          (~-sym {s = L , scal (γ^ L)} {t = ε∙} (unit~ L))))

-- On circuits: w denotes ctrl ⟦ d ⟧, and N • N′ is the identity.
conj-ctrl : (N N′ d : Circuit n) (w : Circuit (₁₊ n)) →
            ⟦ N • N′ ⟧ ~ ⟦ ε {X = Gen n} ⟧ → ⟦ w ⟧ ~ ctrl ⟦ d ⟧ →
            ⟦ top N • (w • top N′) ⟧ ~ ctrl ⟦ N • (d • N′) ⟧
conj-ctrl N N′ d w hN hw =
  ~-trans {s = ⟦ top N • (w • top N′) ⟧} {t = ⟦ top N ⟧ ∙ ⟦ w • top N′ ⟧} {u = ctrl ⟦ N • (d • N′) ⟧}
    (⟦•⟧ (top N) (w • top N′))
  (~-trans {s = ⟦ top N ⟧ ∙ ⟦ w • top N′ ⟧} {t = topS sN ∙ (ctrl sd ∙ topS sN′)} {u = ctrl ⟦ N • (d • N′) ⟧}
    (∙-cong {s = ⟦ top N ⟧} {topS sN} {⟦ w • top N′ ⟧} {ctrl sd ∙ topS sN′}
      (⟦top⟧ N)
      (~-trans {s = ⟦ w • top N′ ⟧} {t = ⟦ w ⟧ ∙ ⟦ top N′ ⟧} {u = ctrl sd ∙ topS sN′}
        (⟦•⟧ w (top N′))
        (∙-cong {s = ⟦ w ⟧} {ctrl sd} {⟦ top N′ ⟧} {topS sN′} hw (⟦top⟧ N′))))
  (~-trans {s = topS sN ∙ (ctrl sd ∙ topS sN′)} {t = ctrl (sN ∙ (sd ∙ sN′))} {u = ctrl ⟦ N • (d • N′) ⟧}
    (core′ sN sd sN′ h)
    (ctrl-~ {s = sN ∙ (sd ∙ sN′)} {⟦ N • (d • N′) ⟧}
      (~-sym {s = ⟦ N • (d • N′) ⟧} {t = sN ∙ (sd ∙ sN′)}
        (~-trans {s = ⟦ N • (d • N′) ⟧} {t = sN ∙ ⟦ d • N′ ⟧} {u = sN ∙ (sd ∙ sN′)}
          (⟦•⟧ N (d • N′))
          (∙-cong {s = sN} {sN} {⟦ d • N′ ⟧} {sd ∙ sN′} (~-refl sN) (⟦•⟧ d N′)))))))
  where
  sN = ⟦ N ⟧
  sN′ = ⟦ N′ ⟧
  sd = ⟦ d ⟧
  h : (sN ∙ sN′) ~ ε∙
  h = ~-trans {s = sN ∙ sN′} {t = ⟦ N • N′ ⟧} {u = ε∙}
        (~-sym {s = ⟦ N • N′ ⟧} {t = sN ∙ sN′} (⟦•⟧ N N′))
        (~-trans {s = ⟦ N • N′ ⟧} {t = ⟦ ε ⟧} {u = ε∙} hN ⟦ε⟧)

------------------------------------------------------------------------
-- Products

ctrl-• : (u v : Circuit n) → (ctrl ⟦ u ⟧ ∙ ctrl ⟦ v ⟧) ~ ctrl ⟦ u • v ⟧
ctrl-• u v =
  ~-trans {s = ctrl ⟦ u ⟧ ∙ ctrl ⟦ v ⟧} {t = ctrl (⟦ u ⟧ ∙ ⟦ v ⟧)} {u = ctrl ⟦ u • v ⟧}
    (~-sym {s = ctrl (⟦ u ⟧ ∙ ⟦ v ⟧)} {t = ctrl ⟦ u ⟧ ∙ ctrl ⟦ v ⟧} (ctrl-∙ ⟦ u ⟧ ⟦ v ⟧))
    (ctrl-~ {s = ⟦ u ⟧ ∙ ⟦ v ⟧} {⟦ u • v ⟧} (~-sym {s = ⟦ u • v ⟧} {t = ⟦ u ⟧ ∙ ⟦ v ⟧} (⟦•⟧ u v)))

ctrl-ε′ : ⟦ ε {X = Gen (₁₊ n)} ⟧ ~ ctrl ⟦ ε {X = Gen n} ⟧
ctrl-ε′ =
  ~-trans {s = ⟦ ε ⟧} {t = ε∙} {u = ctrl ⟦ ε ⟧} ⟦ε⟧
    (~-trans {s = ε∙} {t = ctrl ε∙} {u = ctrl ⟦ ε ⟧} (~-sym {s = ctrl ε∙} {t = ε∙} ctrl-ε)
      (ctrl-~ {s = ε∙} {⟦ ε ⟧} (~-sym {s = ⟦ ε ⟧} {t = ε∙} ⟦ε⟧)))
