------------------------------------------------------------------------
-- Presentations of groups
--
-- The spare wire of ctrl₁, given completeness on at most eight wires,
-- in the calculus with the schema.
--
-- ctrl₁ C is C on the wires 2 … controlled by wire 0, with wire 1 a
-- spare that HH and CCX borrow; ctrl C one wire up, brought down by the
-- swap of wires 0 1, is the same with the spare on wire 2.  The two are
-- equal (`spare`, and `spare-w` for circuits).  For a gate at the bottom
-- that is a closed equation, which completeness proves
-- (SpareSem.spare-sem).  Higher up it says that CTRL₁ x ↑, the gadget
-- with an idle wire 0 below it, does not change when the wires 0 and 2
-- are exchanged (`swap02`): CtrlMove.move carries that up, its cycle
-- lying above wire 2.  The exchange is the conjugation by σ, σ ↑, σ, so
-- the algebra is that of conjugations by involutions.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Examples.Groups.CCX+HH.NaturalP.Syntactics as P
import Examples.Groups.CCX+HH.NaturalP.Schema as S
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (interpret)

module Examples.Groups.CCX+HH.NaturalP.Spare
  (complete≤ : ∀ {k} → k ≤ 8 → ∀ {u v : P.Circuit k} → interpret u ≡ interpret v →
     k S.⊢ u ≈ v)
  where

open import Data.Bool.Base using (T)
open import Data.Nat.Base using (zero ; suc ; _+_ ; _≤ᵇ_ ; s≤s)
open import Data.Nat.Properties using (≤ᵇ⇒≤ ; ≤-refl)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using (refl)
open import Word.Base using ([_]ʷ ; ε ; _•_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)
import Presentation.Base as PB

open import Examples.Groups.CCX+HH.NaturalP.Schema
open import Examples.Groups.CCX+HH.NaturalP.Ctrl using (CTRL ; CTRL₁ ; ctrl)
open import Examples.Groups.CCX+HH.NaturalP.CtrlPad using (ctrl₁ ; ctrl-pad ; ctrl₁-pad)
open import Examples.Groups.CCX+HH.NaturalP.CtrlMove using (Z ; Z⁻ ; move)
open import Examples.Groups.CCX+HH.NaturalP.SpareSem using (spare-sem)
import Examples.Groups.CCX+HH.NaturalP.Pad as Pad
import Examples.Groups.Symmetric-Prop.Placement as Placement

private
  variable
    n m : ℕ

  le : ∀ a → T (a ≤ᵇ 8) → a ≤ 8
  le a p = ≤ᵇ⇒≤ a 8 p

  no-scalar : ∀ {n} (h h′ : Gate 0) →
    n ⊢ [ gate₀ h′ ]ʷ • [ gate₀ h ]ʷ ≈ [ gate₀ h ]ʷ • [ gate₀ h′ ]ʷ
  no-scalar ()

  module PL = Placement Gate SW-gate _NPΣ,_===_

------------------------------------------------------------------------
-- Tools

private
  σσ : (₂₊ n) ⊢ σ • σ ≈ ε
  σσ = PB.axiom (srel (σrel σ-inv))

  σ↑σ↑ : (₃₊ n) ⊢ σ ↑ • σ ↑ ≈ ε
  σ↑σ↑ = lemma-cong↑ (σ • σ) ε σσ

  -- Conjugation by an involution.
  cj : Circuit n → Circuit n → Circuit n
  cj X Y = X • (Y • X)

  cj-cong : ∀ {X Y Y′ : Circuit n} → n ⊢ Y ≈ Y′ → n ⊢ cj X Y ≈ cj X Y′
  cj-cong e = PB.cong PB.refl (PB.cong e PB.refl)

  cj-cj : ∀ {X Y : Circuit n} → n ⊢ X • X ≈ ε → n ⊢ cj X (cj X Y) ≈ Y
  cj-cj XX =
    PB.trans (PB.cong PB.refl PB.assoc)
    (PB.trans (PB.sym PB.assoc)
    (PB.trans (PB.cong XX PB.refl)
    (PB.trans PB.left-unit
    (PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl XX) PB.right-unit)))))

  cj-• : ∀ {X U V : Circuit n} → n ⊢ X • X ≈ ε → n ⊢ cj X (U • V) ≈ cj X U • cj X V
  cj-• XX = PB.sym
    (PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl PB.assoc)
    (PB.trans (PB.cong PB.refl (PB.cong PB.refl (PB.sym PB.assoc)))
    (PB.trans (PB.cong PB.refl (PB.cong PB.refl (PB.cong XX PB.refl)))
    (PB.trans (PB.cong PB.refl (PB.cong PB.refl PB.left-unit))
      (PB.cong PB.refl (PB.sym PB.assoc)))))))

  -- A word passing Y and Y⁻ moves inside their conjugate.
  slide : ∀ {X Y C Y⁻ : Circuit n} → n ⊢ X • Y ≈ Y • X → n ⊢ X • Y⁻ ≈ Y⁻ • X →
    n ⊢ X • ((Y • (C • Y⁻)) • X) ≈ Y • ((X • (C • X)) • Y⁻)
  slide XY XY⁻ =
    PB.trans (PB.cong PB.refl PB.assoc)
    (PB.trans (PB.sym PB.assoc)
    (PB.trans (PB.cong XY PB.refl)
    (PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl (PB.cong PB.refl PB.assoc))
    (PB.trans (PB.cong PB.refl (PB.cong PB.refl (PB.cong PB.refl (PB.sym XY⁻))))
    (PB.trans (PB.cong PB.refl (PB.cong PB.refl (PB.sym PB.assoc)))
      (PB.cong PB.refl (PB.sym PB.assoc))))))))

  -- The swaps of wires 0 1 2 conjugating a word, as two conjugations.
  L-form : (Y : Circuit (₃₊ n)) →
    (₃₊ n) ⊢ (σ ↑ • σ) • (Y • (σ • σ ↑)) ≈ cj (σ ↑) (cj σ Y)
  L-form Y =
    PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl (PB.cong PB.refl (PB.sym PB.assoc)))
      (PB.cong PB.refl (PB.sym PB.assoc)))

  ↑ᵏ3 : (Y : Circuit n) → Y ↑ᵏ 3 ≡ Y ↑ ↑ ↑
  ↑ᵏ3 Y = Eq.trans (PL.↑ᵏ-suc Y 2) (Eq.cong _↑ (PL.↑ᵏ-suc Y 1))

  apart₃ : (B₀ : Circuit 3) (Y : Circuit n) →
    (₃₊ n) ⊢ Y ↑ ↑ ↑ • (B₀ ↓ᵏ n) ≈ (B₀ ↓ᵏ n) • Y ↑ ↑ ↑
  apart₃ B₀ Y = Eq.subst (λ x → _ ⊢ x • (B₀ ↓ᵏ _) ≈ (B₀ ↓ᵏ _) • x) (↑ᵏ3 Y)
    (PB.sym (PL.apart no-scalar B₀ Y))

  -- σ and σ ↑ on three wires.
  S₃ U₃ : Circuit 3
  S₃ = [ gate₂ {1} SW-gate ]ʷ
  U₃ = [ gate₂ {0} SW-gate ↥ ]ʷ

  ⇓↑ : (w : Circuit n) → (w ↑) ⇓ ≡ (w ⇓) ↑
  ⇓↑ [ g ]ʷ  = refl
  ⇓↑ ε       = refl
  ⇓↑ (u • v) = Eq.cong₂ _•_ (⇓↑ u) (⇓↑ v)

  CTRL₁-⇓ : (g : Gen n) → CTRL₁ (g ↧) ≡ CTRL₁ g ⇓
  CTRL₁-⇓ (gate₀ ())
  CTRL₁-⇓ (gate₁ X-gate)   = refl
  CTRL₁-⇓ (gate₂ CX-gate)  = refl
  CTRL₁-⇓ (gate₂ HH-gate)  = refl
  CTRL₁-⇓ (gate₂ SW-gate)  = refl
  CTRL₁-⇓ (gate₃ CCX-gate) = refl
  CTRL₁-⇓ (g ↥) = Eq.cong (λ x → (σ ↑ • σ) • x • (σ • σ ↑))
    (Eq.trans (Eq.cong _↑ (CTRL₁-⇓ g)) (Eq.sym (⇓↑ (CTRL₁ g))))

  pos : Gen n → ℕ
  pos (g ↥) = suc (pos g)
  pos _     = 0

  pos-↧ : (g : Gen n) → pos (g ↧) ≡ pos g
  pos-↧ (gate₀ h) = refl
  pos-↧ (gate₁ h) = refl
  pos-↧ (gate₂ h) = refl
  pos-↧ (gate₃ h) = refl
  pos-↧ (g ↥)     = Eq.cong suc (pos-↧ g)

  -- A closed core, widened.
  coreSp : ∀ c (A : Circuit (₄₊ c)) → T (suc (suc (₄₊ c)) ≤ᵇ 8) → ∀ j →
    (suc (suc (₄₊ c)) + j) ⊢ σ • (ctrl (A ↓ᵏ j) ↑ • σ) ≈ ctrl₁ (A ↓ᵏ j)
  coreSp c A le8 j =
    Eq.subst₂ (λ a b → _ ⊢ a ≈ b)
      (Eq.cong (λ x → σ • (x • σ))
         (Eq.trans (Pad.↑↓ (ctrl A) j) (Eq.cong _↑ (Eq.sym (ctrl-pad A j)))))
      (Eq.sym (ctrl₁-pad A j))
      (widen j (complete≤ (le (suc (suc (₄₊ c))) le8)
                 {u = P.σ • (ctrl A P.↑ • P.σ)} {v = ctrl₁ A} (spare-sem A)))

------------------------------------------------------------------------
-- The spare exchanged with an idle wire

-- From the closed equation one wire up.
private
  swap02-base : ∀ {Y : Circuit (₃₊ n)} →
    (₃₊ n) ⊢ σ • (Y • σ) ≈ (σ ↑ • σ) • (Y • (σ • σ ↑)) →
    (₃₊ n) ⊢ cj σ (cj (σ ↑) (cj σ Y)) ≈ Y
  swap02-base {Y = Y} E =
    PB.trans (cj-cong (PB.sym (PB.trans E (L-form Y)))) (cj-cj σσ)

swap02-aux : ∀ f (x : Gen (₃₊ m)) → pos x ≤ f →
  (₂₊ (₄₊ m)) ⊢ cj σ (cj (σ ↑) (cj σ (CTRL₁ x ↑))) ≈ CTRL₁ x ↑
swap02-aux f (gate₀ ()) _
swap02-aux f (gate₁ {₂₊ j} h) _ = swap02-base (coreSp 0 [ gate₁ {2} h ↥ ]ʷ tt j)
swap02-aux f (gate₂ {₁₊ j} h) _ = swap02-base (coreSp 0 [ gate₂ {1} h ↥ ]ʷ tt j)
swap02-aux f (gate₃ {j} h) _    = swap02-base (coreSp 0 [ gate₃ {0} h ↥ ]ʷ tt j)
swap02-aux zero (y ↥) ()
swap02-aux (suc f) (y ↥) (s≤s p) =
  PB.trans (cj-cong (cj-cong (cj-cong mv)))
  (PB.trans (cj-cong (cj-cong (slide SZ SZ⁻)))
  (PB.trans (cj-cong (slide UZ UZ⁻))
  (PB.trans (slide SZ SZ⁻)
  (PB.trans (PB.cong PB.refl (PB.cong IH PB.refl))
    (PB.sym mv)))))
  where
  mv = lemma-cong↑ (CTRL₁ (y ↥)) _ (emb (move y))
  SZ  = PB.sym (apart₃ S₃ (Z y))
  SZ⁻ = PB.sym (apart₃ S₃ (Z⁻ y))
  UZ  = PB.sym (apart₃ U₃ (Z y))
  UZ⁻ = PB.sym (apart₃ U₃ (Z⁻ y))
  IH = Eq.subst (λ c → _ ⊢ cj σ (cj (σ ↑) (cj σ c)) ≈ c)
         (Eq.cong _↑ (CTRL₁-⇓ y))
         (swap02-aux f (y ↧) (Eq.subst (_≤ f) (Eq.sym (pos-↧ y)) p))

swap02 : (x : Gen (₃₊ m)) → (₂₊ (₄₊ m)) ⊢ cj σ (cj (σ ↑) (cj σ (CTRL₁ x ↑))) ≈ CTRL₁ x ↑
swap02 x = swap02-aux (pos x) x ≤-refl

------------------------------------------------------------------------
-- The spare

-- ctrl one wire up, brought down by the swap, is ctrl₁.
spare : (g : Gen (₄₊ m)) → (₂₊ (₄₊ m)) ⊢ σ • (CTRL g ↑ • σ) ≈ CTRL₁ g
spare (gate₀ ())
spare (gate₁ X-gate)  = PB.refl
spare (gate₂ CX-gate) = PB.refl
spare (gate₂ SW-gate) = PB.refl
spare (gate₂ {₂₊ j} HH-gate)  = coreSp 0 [ gate₂ {2} HH-gate ]ʷ tt j
spare (gate₃ {₁₊ j} CCX-gate) = coreSp 0 [ gate₃ {1} CCX-gate ]ʷ tt j
spare (x ↥) =
  PB.trans (PB.sym (PB.trans (PB.sym (cj-cj σσ)) (cj-cong (swap02 x))))
    (PB.sym (L-form (CTRL₁ x ↑)))

spare-w : (w : Circuit (₄₊ m)) → (₂₊ (₄₊ m)) ⊢ σ • (ctrl w ↑ • σ) ≈ ctrl₁ w
spare-w [ g ]ʷ  = spare g
spare-w ε       = PB.trans (PB.cong PB.refl PB.left-unit) σσ
spare-w (u • v) =
  PB.trans (cj-• σσ) (PB.cong (spare-w u) (spare-w v))
