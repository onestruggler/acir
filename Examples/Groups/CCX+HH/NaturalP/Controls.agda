------------------------------------------------------------------------
-- Presentations of groups
--
-- Two controls commute, given completeness on at most eight wires, in
-- the calculus with the schema.
--
-- ctrl (ctrl w) is w under the controls of wires 0 and 1, and the swap
-- of those wires does not change it (`dsym`).  An uncontrolled circuit
-- one wire up conjugating a controlled one is the controlled conjugate
-- (`conj-ctrl`: split it into its two controlled versions, the negative
-- one passing ctrl x and cancelling).  For a gate at the bottom or one
-- wire up the claim is a closed equation (DoubleSem.ctrl₂-sym-sem);
-- higher up, FullMove writes the gadget as a conjugate by the cycle K of
-- the wires above the spare, ctrl of that conjugate is ctrl of the
-- inner gadget conjugated by K one wire up, which passes the swap of
-- wires 0 1, and what is left is the claim one width down.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Examples.Groups.CCX+HH.NaturalP.Syntactics as P
import Examples.Groups.CCX+HH.NaturalP.Schema as S
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (interpret)

module Examples.Groups.CCX+HH.NaturalP.Controls
  (complete≤ : ∀ {k} → k ≤ 8 → ∀ {u v : P.Circuit k} → interpret u ≡ interpret v →
     k S.⊢ u ≈ v)
  where

open import Data.Bool.Base using (T)
open import Data.Nat.Base using (zero ; suc ; _+_ ; _≤ᵇ_)
open import Data.Nat.Properties using (≤ᵇ⇒≤)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using (refl)
open import Word.Base using ([_]ʷ ; ε ; _•_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)
import Presentation.Base as PB

open import Examples.Groups.CCX+HH.NaturalP.Schema
open import Examples.Groups.CCX+HH.NaturalP.Ctrl using (CTRL ; CTRL₁ ; ctrl ; ctrl⁻)
open import Examples.Groups.CCX+HH.NaturalP.CtrlPad using (ctrl-pad)
open import Examples.Groups.CCX+HH.NaturalP.FullMove using (cy ; cy⁻ ; K ; K⁻ ; KK⁻ ; fullmove)
open import Examples.Groups.CCX+HH.NaturalP.DoubleSem using (ctrl₂-sym-sem)
open import Examples.Groups.CCX+HH.NaturalP.CtrlLemma complete≤ using (ctrl-cong)
open import Examples.Groups.CCX+HH.NaturalP.CtrlColour complete≤
  using (opposite ; split-w ; ctrl⁻-•)
import Examples.Groups.CCX+HH.NaturalP.WordAlg as WA
import Examples.Groups.Symmetric-Prop.Placement as Placement
import Examples.Groups.Symmetric-Prop.Cycle as Cycle

private
  variable
    n m : ℕ

  le : ∀ a → T (a ≤ᵇ 8) → a ≤ 8
  le a p = ≤ᵇ⇒≤ a 8 p

  no-scalar : ∀ {n} (h h′ : Gate 0) →
    n ⊢ [ gate₀ h′ ]ʷ • [ gate₀ h ]ʷ ≈ [ gate₀ h ]ʷ • [ gate₀ h′ ]ʷ
  no-scalar ()

  module PL = Placement Gate SW-gate _NPΣ,_===_
  module CY = Cycle Gate SW-gate _NPΣ,_===_
  module W {n} = WA (_VRel,_===_ n)

------------------------------------------------------------------------
-- Tools

private
  σσ : (₂₊ n) ⊢ σ • σ ≈ ε
  σσ = PB.axiom (srel (σrel σ-inv))

  XX : (₁₊ n) ⊢ X • X ≈ ε
  XX = emb (PB.axiom (P.srel (P.srel P.X²)))

  top-cong : ∀ {u v : Circuit n} → n ⊢ u ≈ v → (₁₊ n) ⊢ u ⇓ ≈ v ⇓
  top-cong {u = u} {v} e =
    PB.trans (CY.top-is-bottom no-scalar u)
    (PB.trans (PB.cong PB.refl (PB.cong (lemma-cong↑ u v e) PB.refl))
      (PB.sym (CY.top-is-bottom no-scalar v)))

  ↑ᵏ3 : (Y : Circuit n) → Y ↑ᵏ 3 ≡ Y ↑ ↑ ↑
  ↑ᵏ3 Y = Eq.trans (PL.↑ᵏ-suc Y 2) (Eq.cong _↑ (PL.↑ᵏ-suc Y 1))

  apart₃ : (B₀ : Circuit 3) (Y : Circuit n) →
    (₃₊ n) ⊢ Y ↑ ↑ ↑ • (B₀ ↓ᵏ n) ≈ (B₀ ↓ᵏ n) • Y ↑ ↑ ↑
  apart₃ B₀ Y = Eq.subst (λ x → _ ⊢ x • (B₀ ↓ᵏ _) ≈ (B₀ ↓ᵏ _) • x) (↑ᵏ3 Y)
    (PB.sym (PL.apart no-scalar B₀ Y))

  S₃ : Circuit 3
  S₃ = [ gate₂ {1} SW-gate ]ʷ

  -- ctrl commutes with an idle wire on top.
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

  CTRL-⇓ : (g : Gen (₄₊ n)) → CTRL (g ↧) ≡ CTRL g ⇓
  CTRL-⇓ (gate₀ ())
  CTRL-⇓ (gate₁ X-gate)   = refl
  CTRL-⇓ (gate₂ CX-gate)  = refl
  CTRL-⇓ (gate₂ HH-gate)  = refl
  CTRL-⇓ (gate₂ SW-gate)  = refl
  CTRL-⇓ (gate₃ CCX-gate) = refl
  CTRL-⇓ (g ↥)            = CTRL₁-⇓ g

  ctrl-⇓ : (w : Circuit (₄₊ n)) → ctrl (w ⇓) ≡ ctrl w ⇓
  ctrl-⇓ [ g ]ʷ  = CTRL-⇓ g
  ctrl-⇓ ε       = refl
  ctrl-⇓ (u • v) = Eq.cong₂ _•_ (ctrl-⇓ u) (ctrl-⇓ v)

  ctrl⁻-cong : ∀ {u v : Circuit (₄₊ m)} → (₄₊ m) ⊢ u ≈ v → suc (₄₊ m) ⊢ ctrl⁻ u ≈ ctrl⁻ v
  ctrl⁻-cong e = PB.cong PB.refl (PB.cong (ctrl-cong e) PB.refl)

------------------------------------------------------------------------
-- An uncontrolled conjugation passes inside the control

conj-ctrl : (u x u⁻ : Circuit (₄₊ m)) → (₄₊ m) ⊢ u • u⁻ ≈ ε →
  suc (₄₊ m) ⊢ u ↑ • (ctrl x • u⁻ ↑) ≈ ctrl u • (ctrl x • ctrl u⁻)
conj-ctrl u x u⁻ uu⁻ =
  PB.trans (PB.cong (split-w u)
             (PB.cong PB.refl (PB.trans (split-w u⁻) (opposite u⁻ u⁻))))
    (W.cancel-mid (opposite x u)
      (PB.trans (PB.sym (ctrl⁻-• u u⁻))
        (PB.trans (ctrl⁻-cong uu⁻) (W.cj-ε XX))))

------------------------------------------------------------------------
-- Closed cores

private
  coreD : ∀ c (A : Circuit (₄₊ c)) → T (suc (suc (₄₊ c)) ≤ᵇ 8) → ∀ j →
    (suc (suc (₄₊ c)) + j) ⊢ σ • (ctrl (ctrl (A ↓ᵏ j)) • σ) ≈ ctrl (ctrl (A ↓ᵏ j))
  coreD c A le8 j =
    Eq.subst₂ (λ a b → _ ⊢ a ≈ b)
      (Eq.cong (λ x → σ • (x • σ)) e) e
      (widen j (complete≤ (le (suc (suc (₄₊ c))) le8)
                 {u = P.σ • (ctrl (ctrl A) • P.σ)} {v = ctrl (ctrl A)}
                 (ctrl₂-sym-sem A)))
    where
    e : ctrl (ctrl A) ↓ᵏ j ≡ ctrl (ctrl (A ↓ᵏ j))
    e = Eq.trans (Eq.sym (ctrl-pad (ctrl A) j)) (Eq.cong ctrl (Eq.sym (ctrl-pad A j)))

  directD : (A : Circuit (₄₊ zero)) →
    (₂₊ (₄₊ zero)) ⊢ σ • (ctrl (ctrl A) • σ) ≈ ctrl (ctrl A)
  directD A = complete≤ (le (suc (suc (₄₊ zero))) tt)
    {u = P.σ • (ctrl (ctrl A) • P.σ)} {v = ctrl (ctrl A)} (ctrl₂-sym-sem A)

------------------------------------------------------------------------
-- Two controls commute

dsym-g : (g : Gen (₄₊ m)) → (₂₊ (₄₊ m)) ⊢ σ • (ctrl (CTRL g) • σ) ≈ ctrl (CTRL g)
dsym-g (gate₀ ())
dsym-g (gate₁ {₃₊ j} h)   = coreD 0 [ gate₁ {3} h ]ʷ tt j
dsym-g (gate₂ {₂₊ j} h)   = coreD 0 [ gate₂ {2} h ]ʷ tt j
dsym-g (gate₃ {₁₊ j} h)   = coreD 0 [ gate₃ {1} h ]ʷ tt j
dsym-g (gate₀ () ↥)
dsym-g (gate₁ {₂₊ j} h ↥) = coreD 0 [ gate₁ {2} h ↥ ]ʷ tt j
dsym-g (gate₂ {₁₊ j} h ↥) = coreD 0 [ gate₂ {1} h ↥ ]ʷ tt j
dsym-g (gate₃ {j} h ↥)    = coreD 0 [ gate₃ {0} h ↥ ]ʷ tt j
dsym-g {zero} (h ↥ ↥) = directD [ h ↥ ↥ ]ʷ
dsym-g {suc m} (h ↥ ↥) =
  PB.trans (W.cj-cong E)
  (PB.trans (W.slide SK SK⁻)
  (PB.trans (PB.cong PB.refl (PB.cong IH PB.refl))
    (PB.sym E)))
  where
  A = CTRL₁ h ⇓
  -- ctrl of the gadget, as ctrl of the inner gadget conjugated by K ↑.
  E : _ ⊢ ctrl (CTRL₁ (h ↥)) ≈ K (₃₊ m) ↑ • (ctrl A • K⁻ (₃₊ m) ↑)
  E = PB.trans (ctrl-cong (emb (fullmove h)))
        (PB.sym (conj-ctrl (K (₃₊ m)) A (K⁻ (₃₊ m)) (emb (KK⁻ (₃₊ m)))))
  SK  = PB.sym (apart₃ S₃ (cy (₃₊ m)))
  SK⁻ = PB.sym (apart₃ S₃ (cy⁻ (₃₊ m)))
  IH : _ ⊢ σ • (ctrl A • σ) ≈ ctrl A
  IH = Eq.subst (λ c → _ ⊢ σ • (c • σ) ≈ c) (Eq.sym (ctrl-⇓ (CTRL₁ h)))
         (top-cong (dsym-g {m} (h ↥)))

-- For circuits.
dsym : (w : Circuit (₄₊ m)) → (₂₊ (₄₊ m)) ⊢ σ • (ctrl (ctrl w) • σ) ≈ ctrl (ctrl w)
dsym [ g ]ʷ  = dsym-g g
dsym ε       = W.cj-ε σσ
dsym (u • v) = PB.trans (W.cj-• σσ) (PB.cong (dsym u) (dsym v))
