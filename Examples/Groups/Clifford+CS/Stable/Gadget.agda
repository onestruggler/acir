------------------------------------------------------------------------
-- Presentations of groups
--
-- The decoding's gadget one wire wider: independence of the affine
-- circuit
--
-- The affine decoding (Affine.Decoding) conjugates a gadget G by affine
-- circuits, and needs G to commute with every CX whose control is off
-- wire 0 (`Indep`).  From five wires on the gadget is λ⁰ of the one a
-- width down (scratchpad/five-qubit-plan.md), and this module carries
-- independence across that step, given the one case it cannot reach:
-- the CX onto the new top wire (`TopTarget`, the paper's (F6) at five
-- wires).  A CX with both wires in the domain is the old one with an
-- idle wire on top (Affine.Widen.ιL-top), which passes λ⁰ G because the
-- old one passes G (Stable.CalcW.pass⁰).  A CX from the top wire onto a
-- domain wire v is λ¹ of X on v: it is CX₁₀ placed by a network that
-- first brings v to wire 0 in the domain and then wire 0 and the top to
-- the bottom two wires, so it is that domain network around CX from the
-- top onto wire 0, and that is λ¹ X by completeness on two wires
-- (`top-cx₀`, through Lambda.Placed); conjugating λ¹ X by a domain
-- circuit is λ¹ of the conjugate (CalcW.conj¹), and every λ¹-image
-- passes λ⁰ G (CalcW.pass¹).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; suc)
open import Notations using (₄₊)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Examples.Groups.Clifford+CS.Lambda using (λ¹ʷ)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_⊢ᵧ_≈_)
open import Examples.Groups.Clifford+CS.Stable.Calc using (F4ᵗ ; F5ᵗ)

module Examples.Groups.Clifford+CS.Stable.Gadget
  (m : ℕ) (c4 : Complete 4) (f4 : F4ᵗ m) (f5 : F5ᵗ m)
  (tr : ∀ {u v : Circuit (₄₊ m)} → (₄₊ m) ⊢ᵧ u ≈ v → (suc (₄₊ m)) ⊢ᵧ λ¹ʷ u ≈ λ¹ʷ v)
  where

open import Data.Fin using (Fin ; toℕ ; inject₁ ; fromℕ) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Nat using (zero ; _<_ ; s≤s)
open import Data.Product using (proj₁ ; proj₂)
import Data.Empty.Irrelevant as Irr
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₃₊)

import Presentation.Base as PB
import Examples.Groups.Symmetric.Syntactics as S

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.Completeness using (complete₂)
open import Examples.Groups.Clifford+CS.SemanticSteps using (module Below)
open import Examples.Groups.Clifford+CS.MultiControlled using (top ; CK₁₀)
open import Examples.Groups.Clifford+CS.PermCalc using (net ; perm ; revS ; perm-inv ; net-inv)
open import Examples.Groups.Clifford+CS.LocalPlace using (pl ; pl-cong ; pl-• ; pl-pl ; place-eq)
open import Examples.Groups.Clifford+CS.Networks using (bring₁ ; bring₂ ; perm-↑s)
open import Examples.Groups.Clifford+CS.NetTop using (topS ; _↧S ; perm-top ; net-top ; revS-top)
open import Examples.Groups.Clifford+CS.Lambda using (λ⁰ʷ ; Sᵗ ; CSᵗ ; CKᵗ)
open import Examples.Groups.Clifford+CS.Lambda.Placed using (Sᵗ-placed ; CSᵗ-placed ; CKᵗ-placed)
open import Examples.Groups.Clifford+CS.Stable.Rules

import Examples.Groups.Clifford+CS.Affine.Theory (₃₊ m) as A₀
import Examples.Groups.Clifford+CS.Affine.Theory (₄₊ m) as A₁
import Examples.Groups.Clifford+CS.Affine.Circuits m c4 as C₀
import Examples.Groups.Clifford+CS.Affine.Circuits (suc m) c4 as C₁
import Examples.Groups.Clifford+CS.Affine.Widen m c4 as Wd
import Examples.Groups.Clifford+CS.Stable.CalcW m f4 f5 tr as CW

private
  W D : ℕ
  W = suc (₄₊ m)
  D = ₄₊ m

  tp : Fin W
  tp = fromℕ (₄₊ m)

  module TW = Tools (W VRel,_===_)
  module S₂ = Below 2 complete₂

open Tools (W YVRel,_===_)

------------------------------------------------------------------------
-- The statements

-- G commutes with every CX whose control is off wire 0.
Indep₀ : Circuit D → Set
Indep₀ G = ∀ (u : Fin (₃₊ m)) (v : A₀.Wire) .(p : sF u ≢ v) →
           D ⊢ᵧ C₀.⟪ A₀.tL (sF u) v p ⟫ • G ≈ G • C₀.⟪ A₀.tL (sF u) v p ⟫

Indep₁ : Circuit W → Set
Indep₁ G = ∀ (u : Fin (₄₊ m)) (v : A₁.Wire) .(p : sF u ≢ v) →
           W ⊢ᵧ C₁.⟪ A₁.tL (sF u) v p ⟫ • G ≈ G • C₁.⟪ A₁.tL (sF u) v p ⟫

-- λ⁰ G commutes with every CX from a domain wire off wire 0 onto the top.
TopTarget : Circuit D → Set
TopTarget G = ∀ (u : Fin (₃₊ m)) .(p : sF (inject₁ u) ≢ tp) →
              W ⊢ᵧ C₁.⟪ A₁.tL (sF (inject₁ u)) tp p ⟫ • λ⁰ʷ G ≈ λ⁰ʷ G • C₁.⟪ A₁.tL (sF (inject₁ u)) tp p ⟫

------------------------------------------------------------------------
-- Wires of the wider circuit: the top, or one of the old ones

private
  data TopView : ∀ {n} → Fin (suc n) → Set where
    is-top : ∀ {n} → TopView (fromℕ n)
    is-low : ∀ {n} (y : Fin n) → TopView (inject₁ y)

  topView : ∀ {n} (x : Fin (suc n)) → TopView x
  topView {zero}  0F     = is-top
  topView {suc n} 0F     = is-low 0F
  topView {suc n} (sF x) = sv (topView x)
    where
    sv : ∀ {x : Fin (suc n)} → TopView x → TopView (sF x)
    sv is-top     = is-top
    sv (is-low y) = is-low (sF y)

  -- The widened network leaves the top wire where it is.
  perm-top-top : ∀ {n} (u : Word (S.Gen n)) → perm (topS u) ⟨$⟩ʳ fromℕ n ≡ fromℕ n
  perm-top-top [ g ]ʷ  = gen g
    where
    gen : ∀ {n} (g : S.Gen n) → perm [ g ↧S ]ʷ ⟨$⟩ʳ fromℕ n ≡ fromℕ n
    gen (S.gate₀ ())
    gen (S.gate₁ ())
    gen (S.gate₂ S.σ-gate) = Eq.refl
    gen {suc n} (g S.↥) = Eq.trans (perm-↑s [ g ↧S ]ʷ (fromℕ n)) (Eq.cong sF (gen g))
  perm-top-top ε       = Eq.refl
  perm-top-top (u • v) = Eq.trans (Eq.cong (perm (topS v) ⟨$⟩ʳ_) (perm-top-top u)) (perm-top-top v)

  back-to : ∀ {n} (σ : Word (S.Gen n)) {a i} → perm σ ⟨$⟩ʳ a ≡ i → perm (revS σ) ⟨$⟩ʳ i ≡ a
  back-to σ {a} e = Eq.subst (λ x → perm (revS σ) ⟨$⟩ʳ x ≡ a) e (perm-inv σ a)

  ≡→≈ : ∀ {a b : Circuit W} → a ≡ b → W ⊢ a ≈ b
  ≡→≈ Eq.refl = TW.refl

------------------------------------------------------------------------
-- CX from the top wire onto wire 0 is λ¹ X

private
  -- A network bringing wire 0 and the top to the bottom two wires.
  B₂ = bring₂ 0F tp (λ ())
  ν  = proj₁ B₂
  ν0 : perm ν ⟨$⟩ʳ 0F ≡ 0F
  ν0 = proj₁ (proj₂ B₂)
  νt : perm ν ⟨$⟩ʳ tp ≡ sF 0F
  νt = proj₂ (proj₂ B₂)

  s0 : Word (S.Gen W)
  s0 = S.σ

  -- S on wire 1 of two, spelled as a placement.
  S₁ : Circuit 2
  S₁ = net (S.σ {0}) • S • net (revS (S.σ {0}))

  Sᵗ-ν : W ⊢ Sᵗ (₄₊ m) ≈ pl ν (S₁ ↓ᵏ (₃₊ m))
  Sᵗ-ν = TW.trans (Sᵗ-placed (₄₊ m) (ν • s0) (Eq.cong (perm s0 ⟨$⟩ʳ_) νt))
                  (TW.sym (pl-pl ν s0 (S {0} ↓ᵏ (₄₊ m))))

  CSᵗ-ν : W ⊢ CSᵗ (₃₊ m) ≈ pl ν (CS {0} ↓ᵏ (₃₊ m))
  CSᵗ-ν = CSᵗ-placed (₃₊ m) ν ν0 νt

  CKᵗ-ν : W ⊢ CKᵗ (₃₊ m) ≈ pl ν (CK₁₀ {0} ↓ᵏ (₃₊ m))
  CKᵗ-ν = CKᵗ-placed (₃₊ m) ν ν0 νt

top-cx₀ : W ⊢ᵧ pl ν (CX₁₀ {0} ↓ᵏ (₃₊ m)) ≈ λ¹ʷ (X {₃₊ m})
top-cx₀ = sym (begin
  CKᵗ k • CSᵗ k • CSᵗ k • CKᵗ k • Sᵗ (₄₊ m)
    ≈⟨ embed (TW.cong CKᵗ-ν (TW.cong CSᵗ-ν (TW.cong CSᵗ-ν (TW.cong CKᵗ-ν Sᵗ-ν)))) ⟩
  pl ν (CK₁₀ {0} ↓ᵏ k) • pl ν (CS {0} ↓ᵏ k) • pl ν (CS {0} ↓ᵏ k) • pl ν (CK₁₀ {0} ↓ᵏ k) • pl ν (S₁ ↓ᵏ k)
    ≈⟨ embed (TW.sym (TW.trans (pl-• ν _ _) (TW.cong TW.refl (TW.trans (pl-• ν _ _) (TW.cong TW.refl
         (TW.trans (pl-• ν _ _) (TW.cong TW.refl (pl-• ν _ _)))))))) ⟩
  pl ν ((CK₁₀ • CS • CS • CK₁₀ • S₁) ↓ᵏ k)
    ≈⟨ embed (pl-cong ν (S₂.by-sem (CK₁₀ • CS • CS • CK₁₀ • S₁) CX₁₀ Eq.refl)) ⟩
  pl ν (CX₁₀ {0} ↓ᵏ k) ∎)
  where
  k : ℕ
  k = ₃₊ m

------------------------------------------------------------------------
-- CX from the top wire onto any domain wire is λ¹ of a domain circuit

module _ (v : Fin D) where
  private
    B₁ = bring₁ v
    σ  = proj₁ B₁
    a a′ : Circuit D
    a  = net σ
    a′ = net (revS σ)

    τ : Word (S.Gen W)
    τ = topS σ • ν

  top-cx : .(p : tp ≢ inject₁ v) → W ⊢ᵧ C₁.⟪ A₁.tL tp (inject₁ v) p ⟫ ≈ λ¹ʷ (a • X • a′)
  top-cx p = begin
    C₁.⟪ A₁.tL tp (inject₁ v) p ⟫
      ≈⟨ embed (place-eq {k = 2} CX₁₀ b τ agree) ⟩
    pl τ (CX₁₀ {0} ↓ᵏ (₃₊ m))
      ≈⟨ embed (TW.sym (pl-pl (topS σ) ν (CX₁₀ {0} ↓ᵏ (₃₊ m)))) ⟩
    pl (topS σ) (pl ν (CX₁₀ {0} ↓ᵏ (₃₊ m)))
      ≈⟨ embed (≡→≈ (Eq.cong₂ (λ x y → x • pl ν (CX₁₀ {0} ↓ᵏ (₃₊ m)) • y) (net-top σ)
                                (Eq.trans (Eq.cong net (revS-top σ)) (net-top (revS σ))))) ⟩
    top a • pl ν (CX₁₀ {0} ↓ᵏ (₃₊ m)) • top a′
      ≈⟨ back (top a) (front (top a′) top-cx₀) ⟩
    top a • λ¹ʷ X • top a′
      ≈⟨ CW.conj¹ a a′ X (embed (net-inv σ)) ⟩
    λ¹ʷ (a • X • a′) ∎
    where
    B = bring₂ (inject₁ v) tp (C₁.ne p)
    b = proj₁ B
    agree : ∀ (j : Fin W) → toℕ j < 2 → perm τ ⟨$⟩ʳ (perm (revS b) ⟨$⟩ʳ j) ≡ j
    agree 0F _ =
      Eq.trans (Eq.cong (perm τ ⟨$⟩ʳ_) (back-to b (proj₁ (proj₂ B))))
        (Eq.trans (Eq.cong (perm ν ⟨$⟩ʳ_) (Eq.trans (perm-top σ v) (Eq.cong inject₁ (proj₂ B₁)))) ν0)
    agree (sF 0F) _ =
      Eq.trans (Eq.cong (perm τ ⟨$⟩ʳ_) (back-to b (proj₂ (proj₂ B))))
        (Eq.trans (Eq.cong (perm ν ⟨$⟩ʳ_) (perm-top-top σ)) νt)
    agree (sF (sF j)) (s≤s (s≤s ()))

------------------------------------------------------------------------
-- The step

private
  go : ∀ (G : Circuit D) → Indep₀ G → TopTarget G →
       ∀ {u : Fin (₄₊ m)} {v : A₁.Wire} → TopView u → TopView v → .(p : sF u ≢ v) →
       W ⊢ᵧ C₁.⟪ A₁.tL (sF u) v p ⟫ • λ⁰ʷ G ≈ λ⁰ʷ G • C₁.⟪ A₁.tL (sF u) v p ⟫
  go G ind tt (is-low u) (is-low v) p = begin
    C₁.⟪ Wd.ιL l ⟫ • λ⁰ʷ G      ≈⟨ front _ (embed (Wd.ιL-top l)) ⟩
    top C₀.⟪ l ⟫ • λ⁰ʷ G         ≈⟨ CW.pass⁰ C₀.⟪ l ⟫ G (ind u v p′) ⟩
    λ⁰ʷ G • top C₀.⟪ l ⟫         ≈⟨ back _ (embed (TW.sym (Wd.ιL-top l))) ⟩
    λ⁰ʷ G • C₁.⟪ Wd.ιL l ⟫ ∎
    where
    p′ : sF u ≢ v
    p′ e = Irr.⊥-elim (p (Eq.cong inject₁ e))
    l = A₀.tL (sF u) v p′
  go G ind tt (is-low u) is-top p = tt u p
  go G ind tt is-top (is-low v) p = begin
    C₁.⟪ A₁.tL tp (inject₁ v) p ⟫ • λ⁰ʷ G      ≈⟨ front _ (top-cx v p) ⟩
    λ¹ʷ h • λ⁰ʷ G                                ≈⟨ CW.pass¹ h G ⟩
    λ⁰ʷ G • λ¹ʷ h                                ≈⟨ back _ (sym (top-cx v p)) ⟩
    λ⁰ʷ G • C₁.⟪ A₁.tL tp (inject₁ v) p ⟫ ∎
    where
    h = net (proj₁ (bring₁ v)) • X • net (revS (proj₁ (bring₁ v)))
  go G ind tt is-top is-top p = Irr.⊥-elim (p Eq.refl)

-- Independence one wire up.
step : ∀ (G : Circuit D) → Indep₀ G → TopTarget G → Indep₁ (λ⁰ʷ G)
step G ind tt u v p = go G ind tt (topView u) (topView v) p
