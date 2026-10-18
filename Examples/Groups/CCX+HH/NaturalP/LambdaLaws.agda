------------------------------------------------------------------------
-- Presentations of groups
--
-- Circuits under several controls, given completeness on at most eight
-- wires, in the calculus with the schema.
--
-- Λ s respects derivations and products (`Λ-cong`, `Λ-•`).  Two
-- patterns with opposite colours at some position commute (`Λ-opp`:
-- CtrlColour.opposite at that position, the positions before it passing
-- through ctrlᵖ).  A black and a white control at one position merge
-- into an idle wire (`Λ-merge`: CtrlColour.split-w).  The swap of two
-- adjacent positions exchanges them in the pattern (`Λ-swap`): at the
-- top, two controls are Controls.dsym, a control and an idle wire the
-- spare lemma (Spare.spare-w), and the other colours follow from those
-- by X on the controls; further down, the swap passes into each control
-- (Controls.conj-ctrl).  The mixed colours use four facts on two wires,
-- proved here by completeness and evaluating 4 × 4 matrices.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Examples.Groups.CCX+HH.NaturalP.Syntactics as P
import Examples.Groups.CCX+HH.NaturalP.Schema as S
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (interpret)

module Examples.Groups.CCX+HH.NaturalP.LambdaLaws
  (complete≤ : ∀ {k} → k ≤ 8 → ∀ {u v : P.Circuit k} → interpret u ≡ interpret v →
     k S.⊢ u ≈ v)
  where

open import Data.Bool.Base using (Bool ; true ; false ; T)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (zero ; suc ; _+_ ; _≤ᵇ_)
open import Data.Nat.Properties using (≤ᵇ⇒≤)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; _++_)
open import Relation.Binary.PropositionalEquality as Eq using (refl)
open import Word.Base using ([_]ʷ ; ε ; _•_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)
import Presentation.Base as PB

open import Examples.Groups.CCX+HH.NaturalP.Schema
open import Examples.Groups.CCX+HH.NaturalP.Ctrl using (CTRL ; ctrl ; ctrl⁻ ; XC)
open import Examples.Groups.CCX+HH.NaturalP.CtrlPad using (ctrl₁ ; ctrl-↑)
open import Examples.Groups.CCX+HH.NaturalP.Lambda
open import Examples.Groups.CCX+HH.NaturalP.CtrlLemma complete≤ using (ctrl-cong)
open import Examples.Groups.CCX+HH.NaturalP.CtrlColour complete≤
  using (opposite ; split-w ; ctrl⁻-•)
open import Examples.Groups.CCX+HH.NaturalP.Spare complete≤ using (spare-w)
open import Examples.Groups.CCX+HH.NaturalP.Controls complete≤ using (dsym ; conj-ctrl)
import Examples.Groups.CCX+HH.NaturalP.WordAlg as WA
open import Examples.Groups.CCX+HH.Decide using (by-eq)
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (_+ᴰ_ ; _*ᴰ_ ; -ᴰ_)

private
  variable
    m i j k c : ℕ

  module W {n} = WA (_VRel,_===_ n)

  le : ∀ a → T (a ≤ᵇ 8) → a ≤ 8
  le a p = ≤ᵇ⇒≤ a 8 p

------------------------------------------------------------------------
-- Facts on two wires

private
  opaque
    unfolding _+ᴰ_ _*ᴰ_ -ᴰ_

    F3′₀ : 2 ⊢ XC • X ↑ ≈ X • (XC • X)
    F3′₀ = complete≤ (le 2 tt) {u = XC • X ↑} {v = X • (XC • X)} (by-eq tt)

    ZZ₀ : 2 ⊢ (X • (XC • X)) • (X • (XC • X)) ≈ ε
    ZZ₀ = complete≤ (le 2 tt) {u = (X • (XC • X)) • (X • (XC • X))} {v = ε} (by-eq tt)

    F3₀ : 2 ⊢ X ↑ • XC ≈ X • (XC • X)
    F3₀ = complete≤ (le 2 tt) {u = X ↑ • XC} {v = X • (XC • X)} (by-eq tt)

    FX₀ : 2 ⊢ σ • (X • σ) ≈ X ↑
    FX₀ = complete≤ (le 2 tt) {u = σ • (X • σ)} {v = X ↑} (by-eq tt)

    FX′₀ : 2 ⊢ σ • (X ↑ • σ) ≈ X
    FX′₀ = complete≤ (le 2 tt) {u = σ • (X ↑ • σ)} {v = X} (by-eq tt)

    XCXC₀ : 2 ⊢ XC • XC ≈ ε
    XCXC₀ = complete≤ (le 2 tt) {u = XC • XC} {v = ε} (by-eq tt)

  F3 : ∀ j → (₂₊ j) ⊢ X ↑ • XC ≈ X • (XC • X)
  F3 j = widen j F3₀

  FX : ∀ j → (₂₊ j) ⊢ σ • (X • σ) ≈ X ↑
  FX j = widen j FX₀

  FX′ : ∀ j → (₂₊ j) ⊢ σ • (X ↑ • σ) ≈ X
  FX′ j = widen j FX′₀

  XCXC : ∀ j → (₂₊ j) ⊢ XC • XC ≈ ε
  XCXC j = widen j XCXC₀

  XX : (₁₊ m) ⊢ X • X ≈ ε
  XX = emb (PB.axiom (P.srel (P.srel P.X²)))

  X↑X↑ : (₂₊ m) ⊢ X ↑ • X ↑ ≈ ε
  X↑X↑ = lemma-cong↑ (X • X) ε XX

  σσ : (₂₊ m) ⊢ σ • σ ≈ ε
  σσ = PB.axiom (srel (σrel σ-inv))

  -- X on wire 0 and on wire 1 commute.
  X-X↑ : (₂₊ m) ⊢ X • X ↑ ≈ X ↑ • X
  X-X↑ = PB.sym (PB.axiom (comm₁ X-gate (gate₁ X-gate)))

------------------------------------------------------------------------
-- One position

ctrlᵖ-cong : ∀ p {u v : Circuit (₄₊ m)} → (₄₊ m) ⊢ u ≈ v →
  suc (₄₊ m) ⊢ ctrlᵖ p u ≈ ctrlᵖ p v
ctrlᵖ-cong (just true)  e = ctrl-cong e
ctrlᵖ-cong (just false) e = PB.cong PB.refl (PB.cong (ctrl-cong e) PB.refl)
ctrlᵖ-cong nothing {u} {v} e = lemma-cong↑ u v e

ctrlᵖ-• : ∀ p (u v : Circuit (₄₊ m)) → suc (₄₊ m) ⊢ ctrlᵖ p (u • v) ≈ ctrlᵖ p u • ctrlᵖ p v
ctrlᵖ-• (just true)  u v = PB.refl
ctrlᵖ-• (just false) u v = ctrl⁻-• u v
ctrlᵖ-• nothing      u v = PB.refl

ctrlᵖ-ε : ∀ p → suc (₄₊ m) ⊢ ctrlᵖ {₄₊ m} p ε ≈ ε
ctrlᵖ-ε (just true)  = PB.refl
ctrlᵖ-ε (just false) = W.cj-ε XX
ctrlᵖ-ε nothing      = PB.refl

private
  F3′ : ∀ j → (₂₊ j) ⊢ XC • X ↑ ≈ X • (XC • X)
  F3′ j = widen j F3′₀

  ZZ : ∀ j → (₂₊ j) ⊢ (X • (XC • X)) • (X • (XC • X)) ≈ ε
  ZZ j = widen j ZZ₀

------------------------------------------------------------------------
-- Patterns

Λ-cong : ∀ (s : Vec Pos k) {u v : Circuit (₄₊ c)} → (₄₊ c) ⊢ u ≈ v →
  (₄₊ (k + c)) ⊢ Λ s u ≈ Λ s v
Λ-cong []      e = e
Λ-cong (p ∷ s) e = ctrlᵖ-cong p (Λ-cong s e)

Λ-• : ∀ (s : Vec Pos k) (u v : Circuit (₄₊ c)) →
  (₄₊ (k + c)) ⊢ Λ s (u • v) ≈ Λ s u • Λ s v
Λ-• []      u v = PB.refl
Λ-• (p ∷ s) u v = PB.trans (ctrlᵖ-cong p (Λ-• s u v)) (ctrlᵖ-• p (Λ s u) (Λ s v))

Λ-ε : ∀ (s : Vec Pos k) → (₄₊ (k + c)) ⊢ Λ {c = c} s ε ≈ ε
Λ-ε []      = PB.refl
Λ-ε (p ∷ s) = PB.trans (ctrlᵖ-cong p (Λ-ε s)) (ctrlᵖ-ε p)

-- Two patterns with opposite colours at some position.
data Differ : Vec Pos k → Vec Pos k → Set where
  here  : ∀ {s s′ : Vec Pos k} → Differ (just true ∷ s) (just false ∷ s′)
  here′ : ∀ {s s′ : Vec Pos k} → Differ (just false ∷ s) (just true ∷ s′)
  there : ∀ {p} {s s′ : Vec Pos k} → Differ s s′ → Differ (p ∷ s) (p ∷ s′)

Λ-opp : ∀ {s s′ : Vec Pos k} → Differ s s′ → (u v : Circuit (₄₊ c)) →
  (₄₊ (k + c)) ⊢ Λ s u • Λ s′ v ≈ Λ s′ v • Λ s u
Λ-opp (here {s = s} {s′}) u v = opposite (Λ s u) (Λ s′ v)
Λ-opp (here′ {s = s} {s′}) u v = PB.sym (opposite (Λ s′ v) (Λ s u))
Λ-opp (there {p = p} {s} {s′} d) u v =
  PB.trans (PB.sym (ctrlᵖ-• p (Λ s u) (Λ s′ v)))
  (PB.trans (ctrlᵖ-cong p (Λ-opp d u v))
    (ctrlᵖ-• p (Λ s′ v) (Λ s u)))

-- A black and a white control at one position merge into an idle wire.
Λ-merge : ∀ (s₁ : Vec Pos i) (s : Vec Pos k) (u : Circuit (₄₊ c)) →
  (₄₊ ((i + suc k) + c)) ⊢
    Λ (s₁ ++ just true ∷ s) u • Λ (s₁ ++ just false ∷ s) u ≈ Λ (s₁ ++ nothing ∷ s) u
Λ-merge []       s u = PB.sym (split-w (Λ s u))
Λ-merge (p ∷ s₁) s u =
  PB.trans (PB.sym (ctrlᵖ-• p (Λ (s₁ ++ just true ∷ s) u) (Λ (s₁ ++ just false ∷ s) u)))
    (ctrlᵖ-cong p (Λ-merge s₁ s u))

------------------------------------------------------------------------
-- Two controls of any colours

private
  -- Conjugation by y and by x commute when x and y do.
  cj-comm : ∀ {n} {x y w : Circuit n} → n ⊢ x • y ≈ y • x →
    n ⊢ W.cj y (W.cj x w) ≈ W.cj x (W.cj y w)
  cj-comm {x = x} {y} {w} xy =
    PB.trans (PB.cong PB.refl PB.assoc)
    (PB.trans (PB.sym PB.assoc)
    (PB.trans (PB.cong (PB.sym xy) (PB.trans PB.assoc (PB.cong PB.refl xy)))
    (PB.trans PB.assoc
      (PB.cong PB.refl (PB.trans (PB.cong PB.refl (PB.sym PB.assoc)) (PB.sym PB.assoc))))))

  -- Conjugating a conjugate.
  cj-dist : ∀ {n} {s z w : Circuit n} → n ⊢ s • s ≈ ε →
    n ⊢ W.cj s (W.cj z w) ≈ W.cj (W.cj s z) (W.cj s w)
  cj-dist ss = PB.trans (W.cj-• ss) (PB.cong PB.refl (W.cj-• ss))

  -- a (q a) = b (q b), when a = b z = z b, z commutes with q and z z = ε.
  trade : ∀ {n} {a b z q : Circuit n} →
    n ⊢ a ≈ b • z → n ⊢ a ≈ z • b → n ⊢ q • z ≈ z • q → n ⊢ z • z ≈ ε →
    n ⊢ a • (q • a) ≈ b • (q • b)
  trade e1 e2 qz zz =
    PB.trans (PB.cong e1 (PB.cong PB.refl e2))
    (PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl (PB.sym PB.assoc))
    (PB.trans (PB.cong PB.refl (PB.cong (PB.sym qz) PB.refl))
    (PB.trans (PB.cong PB.refl PB.assoc)
    (PB.trans (PB.cong PB.refl (PB.cong PB.refl (PB.sym PB.assoc)))
    (PB.trans (PB.cong PB.refl (PB.cong PB.refl (PB.cong zz PB.refl)))
      (PB.cong PB.refl (PB.cong PB.refl PB.left-unit))))))))

  -- ctrl of a white control: X one wire up around the two controls.
  TF : (Y : Circuit (₄₊ m)) →
    (₂₊ (₄₊ m)) ⊢ ctrl (ctrl⁻ Y) ≈ X ↑ • (ctrl (ctrl Y) • X ↑)
  TF {m} Y = trade e1 e2 (opposite (ctrl Y) X) (ZZ (₄₊ m))
    where
    e1 : _ ⊢ XC ≈ X ↑ • (X • (XC • X))
    e1 = PB.trans (PB.sym (PB.trans (PB.sym PB.assoc)
                    (PB.trans (PB.cong X↑X↑ PB.refl) PB.left-unit)))
           (PB.cong PB.refl (F3 (₄₊ m)))
    e2 : _ ⊢ XC ≈ (X • (XC • X)) • X ↑
    e2 = PB.trans (PB.sym (PB.trans PB.assoc
                    (PB.trans (PB.cong PB.refl X↑X↑) PB.right-unit)))
           (PB.cong (F3′ (₄₊ m)) PB.refl)

  sw-tf : (Y : Circuit (₄₊ m)) →
    (₂₊ (₄₊ m)) ⊢ σ • (ctrl (ctrl⁻ Y) • σ) ≈ ctrl⁻ (ctrl Y)
  sw-tf {m} Y =
    PB.trans (W.cj-cong (TF Y))
    (PB.trans (cj-dist σσ)
      (PB.cong (FX′ (₄₊ m)) (PB.cong (dsym Y) (FX′ (₄₊ m)))))

  sw-ft : (Y : Circuit (₄₊ m)) →
    (₂₊ (₄₊ m)) ⊢ σ • (ctrl⁻ (ctrl Y) • σ) ≈ ctrl (ctrl⁻ Y)
  sw-ft Y = PB.trans (W.cj-cong (PB.sym (sw-tf Y))) (W.cj-cj σσ)

  sw-ff : (Y : Circuit (₄₊ m)) →
    (₂₊ (₄₊ m)) ⊢ σ • (ctrl⁻ (ctrl⁻ Y) • σ) ≈ ctrl⁻ (ctrl⁻ Y)
  sw-ff {m} Y =
    PB.trans (W.cj-cong (W.cj-cong (TF Y)))
    (PB.trans (cj-dist σσ)
    (PB.trans (PB.cong (FX (₄₊ m)) (PB.cong (cj-dist σσ) (FX (₄₊ m))))
    (PB.trans (W.cj-cong (PB.cong (FX′ (₄₊ m)) (PB.cong (dsym Y) (FX′ (₄₊ m)))))
    (PB.trans (cj-comm X-X↑)
      (PB.sym (W.cj-cong (TF Y)))))))

  sw-nn : (Y : Circuit (₄₊ m)) → (₂₊ (₄₊ m)) ⊢ σ • ((Y ↑ ↑) • σ) ≈ Y ↑ ↑
  sw-nn Y =
    PB.trans (PB.cong PB.refl (comm-gate₂-w↑↑ SW-gate Y))
    (PB.trans (PB.sym PB.assoc) (PB.trans (PB.cong σσ PB.refl) PB.left-unit))

  sw-nt : (Y : Circuit (₄₊ m)) → (₂₊ (₄₊ m)) ⊢ σ • ((ctrl Y) ↑ • σ) ≈ ctrl (Y ↑)
  sw-nt Y = Eq.subst (λ x → _ ⊢ σ • ((ctrl Y) ↑ • σ) ≈ x) (Eq.sym (ctrl-↑ Y)) (spare-w Y)

  sw-tn : (Y : Circuit (₄₊ m)) → (₂₊ (₄₊ m)) ⊢ σ • (ctrl (Y ↑) • σ) ≈ (ctrl Y) ↑
  sw-tn Y = PB.trans (W.cj-cong (PB.sym (sw-nt Y))) (W.cj-cj σσ)

  sw-nf : (Y : Circuit (₄₊ m)) → (₂₊ (₄₊ m)) ⊢ σ • ((ctrl⁻ Y) ↑ • σ) ≈ ctrl⁻ (Y ↑)
  sw-nf {m} Y =
    PB.trans (cj-dist σσ) (PB.cong (FX′ (₄₊ m)) (PB.cong (sw-nt Y) (FX′ (₄₊ m))))

  sw-fn : (Y : Circuit (₄₊ m)) → (₂₊ (₄₊ m)) ⊢ σ • (ctrl⁻ (Y ↑) • σ) ≈ (ctrl⁻ Y) ↑
  sw-fn Y = PB.trans (W.cj-cong (PB.sym (sw-nf Y))) (W.cj-cj σσ)

-- The swap of the two top positions.
Λ-swap-top : ∀ a b (Y : Circuit (₄₊ m)) →
  (₂₊ (₄₊ m)) ⊢ σ • (ctrlᵖ a (ctrlᵖ b Y) • σ) ≈ ctrlᵖ b (ctrlᵖ a Y)
Λ-swap-top (just true)  (just true)  Y = dsym Y
Λ-swap-top (just true)  (just false) Y = sw-tf Y
Λ-swap-top (just false) (just true)  Y = sw-ft Y
Λ-swap-top (just false) (just false) Y = sw-ff Y
Λ-swap-top nothing      (just true)  Y = sw-nt Y
Λ-swap-top nothing      (just false) Y = sw-nf Y
Λ-swap-top (just true)  nothing      Y = sw-tn Y
Λ-swap-top (just false) nothing      Y = sw-fn Y
Λ-swap-top nothing      nothing      Y = sw-nn Y

------------------------------------------------------------------------
-- The swap of any two adjacent positions

σat-invol : ∀ (s₁ : Vec Pos i) j c → (₄₊ ((i + ₂₊ j) + c)) ⊢ σat s₁ j c • σat s₁ j c ≈ ε
σat-invol []       j c = σσ
σat-invol (p ∷ s₁) j c = lemma-cong↑ (σat s₁ j c • σat s₁ j c) ε (σat-invol s₁ j c)

Λ-swap : ∀ (s₁ : Vec Pos i) a b (s : Vec Pos j) (u : Circuit (₄₊ c)) →
  (₄₊ ((i + ₂₊ j) + c)) ⊢
    σat s₁ j c • (Λ (s₁ ++ a ∷ b ∷ s) u • σat s₁ j c) ≈ Λ (s₁ ++ b ∷ a ∷ s) u
Λ-swap []       a b s u = Λ-swap-top a b (Λ s u)
Λ-swap {j = j} {c = c} (just true ∷ s₁) a b s u =
  PB.trans (conj-ctrl (σat s₁ j c) (Λ (s₁ ++ a ∷ b ∷ s) u) (σat s₁ j c) (σat-invol s₁ j c))
    (ctrl-cong (Λ-swap s₁ a b s u))
Λ-swap {j = j} {c = c} (just false ∷ s₁) a b s u =
  PB.trans (PB.sym (W.slide XT XT))
    (PB.cong PB.refl (PB.cong
      (PB.trans (conj-ctrl Sw (Λ (s₁ ++ a ∷ b ∷ s) u) Sw (σat-invol s₁ j c))
        (ctrl-cong (Λ-swap s₁ a b s u))) PB.refl))
  where
  Sw = σat s₁ j c
  XT = PB.sym (comm-gate₁-w↑ X-gate Sw)
Λ-swap {j = j} {c = c} (nothing ∷ s₁) a b s u =
  lemma-cong↑ (σat s₁ j c • (Λ (s₁ ++ a ∷ b ∷ s) u • σat s₁ j c)) _ (Λ-swap s₁ a b s u)
