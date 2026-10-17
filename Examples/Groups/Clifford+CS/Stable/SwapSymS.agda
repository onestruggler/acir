------------------------------------------------------------------------
-- Presentations of groups
--
-- The doubly controlled S does not see the order of its controls
--
-- λ¹ λ¹ S on 6 + m wires — S on wire 0 under the two top wires — is
-- the canonical S-box Σ(0; t, 1 | 2, 3) placed (`λλ-pl`): λ¹ S is the
-- CS of wire 0 and the old top, a CS on the wires 0 1 placed
-- (Lambda.Placed.CSᵗ-placed), λ¹ of a placed circuit is the widened
-- placement of λ¹ of it (CalcW.conj¹), and λ¹ of the CS on the wires 0
-- 1 is Σᵗ, the S-box placed (Σᵗ-placed).  In that placement the old
-- top is the S-box's wire 1 and the new top its control, so the
-- exchange of the two top wires exchanges them, which the S-box does
-- not see (Stable.SboxSym.sbW, from completeness on five wires).  So
-- `ss-S¹`: SwapSym for λ¹ λ¹ S — with Stable.GadgetSym.ss-gad¹, SwapSym
-- for every gadget.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; suc)
open import Notations using (₄₊)
open import Examples.Groups.Clifford+CS.Syntactics using (Circuit)
open import Examples.Groups.Clifford+CS.Lambda using (λ¹ʷ)
open import Examples.Groups.Clifford+CS.Stable.Rules using (_⊢ᵧ_≈_)
open import Examples.Groups.Clifford+CS.Stable.Calc using (F4ᵗ ; F5ᵗ)
open import Examples.Groups.Clifford+CS.Stable.HypFrom using (Completeᵧ)

module Examples.Groups.Clifford+CS.Stable.SwapSymS
  (m : ℕ) (f4₁ : F4ᵗ (suc m)) (f5₁ : F5ᵗ (suc m))
  (tr₁ : ∀ {u v : Circuit (₄₊ (suc m))} → (₄₊ (suc m)) ⊢ᵧ u ≈ v → (suc (₄₊ (suc m))) ⊢ᵧ λ¹ʷ u ≈ λ¹ʷ v)
  (c₅ : Completeᵧ 5)
  where

open import Data.Fin using (Fin ; toℕ ; inject₁ ; fromℕ) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (zero ; _<_ ; s≤s)
open import Data.Product using (proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₃₊)

import Presentation.Base as PB
import Examples.Groups.Symmetric.Syntactics as S

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.MultiControlled using (top)
open import Examples.Groups.Clifford+CS.PermCalc using (net ; perm ; revS ; perm-inv ; net-inv)
open import Examples.Groups.Clifford+CS.LocalPlace using (pl ; pl-cong ; pl-pl ; place-eq)
open import Examples.Groups.Clifford+CS.Networks using (bring₂ ; bring₅ ; perm-↑s)
open import Examples.Groups.Clifford+CS.NetTop using (topS ; _↧S ; perm-top ; net-top ; revS-top)
open import Examples.Groups.Clifford+CS.Lambda using (Swᵗ ; CSᵗ ; Σᵗ)
open import Examples.Groups.Clifford+CS.Lambda.Placed
  using (CSᵗ-placed ; Σᵗ-placed ; swT ; net-swT ; revS-swT ; perm-swT-top ; perm-swT-low)
open import Examples.Groups.Clifford+CS.Five.Letters using (b-Sb2-0-41-3)
open import Examples.Groups.Clifford+CS.Stable.Rules
open import Examples.Groups.Clifford+CS.Stable.SboxSym using (ρ ; sbW)
import Examples.Groups.Clifford+CS.Stable.CalcW as CalcW

private
  D₁ W′ : ℕ
  D₁ = suc (₄₊ m)
  W′ = suc (suc (₄₊ m))

  module CW₁ = CalcW (suc m) f4₁ f5₁ tr₁
  module TW = Tools (W′ VRel,_===_)

  ≡→≈ : ∀ {a b : Circuit W′} → a ≡ b → W′ ⊢ a ≈ b
  ≡→≈ Eq.refl = TW.refl

open Tools (W′ YVRel,_===_)

------------------------------------------------------------------------
-- Wires and networks

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

  perm-swT-top′ : ∀ k → perm (swT k) ⟨$⟩ʳ inject₁ (fromℕ k) ≡ fromℕ (₁₊ k)
  perm-swT-top′ zero    = Eq.refl
  perm-swT-top′ (suc k) = Eq.trans (perm-↑s (swT k) (inject₁ (fromℕ k))) (Eq.cong sF (perm-swT-top′ k))

  revS-revS : ∀ {n} (u : Word (S.Gen n)) → revS (revS u) ≡ u
  revS-revS [ g ]ʷ  = Eq.refl
  revS-revS ε       = Eq.refl
  revS-revS (u • v) = Eq.cong₂ _•_ (revS-revS u) (revS-revS v)

  back-to : ∀ {n} (σ : Word (S.Gen n)) {a i} → perm σ ⟨$⟩ʳ a ≡ i → perm (revS σ) ⟨$⟩ʳ i ≡ a
  back-to σ {a} e = Eq.subst (λ x → perm (revS σ) ⟨$⟩ʳ x ≡ a) e (perm-inv σ a)

  inv-r : ∀ {n} (σ : Word (S.Gen n)) x → perm σ ⟨$⟩ʳ (perm (revS σ) ⟨$⟩ʳ x) ≡ x
  inv-r σ x = Eq.subst (λ τ → perm τ ⟨$⟩ʳ (perm (revS σ) ⟨$⟩ʳ x) ≡ x) (revS-revS σ) (perm-inv (revS σ) x)

  -- The old top, the new top.
  tp : Fin D₁
  tp = fromℕ (₄₊ m)

  tq t6 : Fin W′
  tq = inject₁ tp
  t6 = fromℕ (suc (₄₊ m))

  -- The exchange of the top two wires fixes every other wire.
  sw-fix : ∀ x → x ≢ tq → x ≢ t6 → perm (swT (₄₊ m)) ⟨$⟩ʳ x ≡ x
  sw-fix x n₁ n₂ = go (topView x) n₁ n₂
    where
    go2 : ∀ {y : Fin D₁} → TopView y → inject₁ y ≢ tq → perm (swT (₄₊ m)) ⟨$⟩ʳ inject₁ y ≡ inject₁ y
    go2 is-top     n = ⊥-elim (n Eq.refl)
    go2 (is-low z) n = perm-swT-low (₄₊ m) z
    go : ∀ {x : Fin W′} → TopView x → x ≢ tq → x ≢ t6 → perm (swT (₄₊ m)) ⟨$⟩ʳ x ≡ x
    go is-top     n₁ n₂ = ⊥-elim (n₂ Eq.refl)
    go (is-low y) n₁ n₂ = go2 (topView y) n₁

  -- ν brings wire 0 and the old top to the bottom two wires, μ the
  -- wires 0 … 3 and the new top to the canonical five.
  B₂ = bring₂ 0F tp (λ ())
  ν  = proj₁ B₂

  B₅ = bring₅ 0F (sF 0F) (sF (sF 0F)) (sF (sF (sF 0F))) t6
         (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ())
  μ  = proj₁ B₅
  μ0 = proj₁ (proj₂ B₅)
  μ1 = proj₁ (proj₂ (proj₂ B₅))
  μ2 = proj₁ (proj₂ (proj₂ (proj₂ B₅)))
  μ3 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ B₅))))
  μ4 = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ B₅))))

  τ : Word (S.Gen W′)
  τ = topS ν • μ

  τ0 : perm τ ⟨$⟩ʳ 0F ≡ 0F
  τ0 = Eq.trans (Eq.cong (perm μ ⟨$⟩ʳ_) (Eq.trans (perm-top ν 0F) (Eq.cong inject₁ (proj₁ (proj₂ B₂))))) μ0

  τ1 : perm τ ⟨$⟩ʳ tq ≡ sF 0F
  τ1 = Eq.trans (Eq.cong (perm μ ⟨$⟩ʳ_) (Eq.trans (perm-top ν tp) (Eq.cong inject₁ (proj₂ (proj₂ B₂))))) μ1

  τ4 : perm τ ⟨$⟩ʳ t6 ≡ sF (sF (sF (sF 0F)))
  τ4 = Eq.trans (Eq.cong (perm μ ⟨$⟩ʳ_) (perm-top-top ν)) μ4

  Bx : Circuit W′
  Bx = b-Sb2-0-41-3 ↓ᵏ (suc m)

  Sw : Circuit W′
  Sw = Swᵗ (₄₊ m)

  sw-pl : ∀ (b : Word (S.Gen W′)) (g : Circuit W′) → W′ ⊢ Sw • pl b g • Sw ≈ pl (swT (₄₊ m) • b) g
  sw-pl b g =
    TW.trans (≡→≈ (Eq.sym (Eq.cong₂ (λ x y → x • pl b g • y) (net-swT (₄₊ m))
                                    (Eq.trans (Eq.cong net (revS-swT (₄₊ m))) (net-swT (₄₊ m))))))
             (pl-pl (swT (₄₊ m)) b g)

------------------------------------------------------------------------
-- λ¹ λ¹ S is the S-box placed

λλ-pl : W′ ⊢ᵧ λ¹ʷ (λ¹ʷ (S {₃₊ m})) ≈ pl τ Bx
λλ-pl = begin
  λ¹ʷ (CSᵗ (₃₊ m))
    ≈⟨ tr₁ (embed (CSᵗ-placed (₃₊ m) ν (proj₁ (proj₂ B₂)) (proj₂ (proj₂ B₂)))) ⟩
  λ¹ʷ (pl ν (CS {0} ↓ᵏ (₃₊ m)))
    ≈⟨ sym (CW₁.conj¹ (net ν) (net (revS ν)) (CS {0} ↓ᵏ (₃₊ m)) (embed (net-inv ν))) ⟩
  top (net ν) • Σᵗ (suc m) • top (net (revS ν))
    ≈⟨ embed (≡→≈ (Eq.sym (Eq.cong₂ (λ x y → x • Σᵗ (suc m) • y) (net-top ν)
                              (Eq.trans (Eq.cong net (revS-top ν)) (net-top (revS ν)))))) ⟩
  pl (topS ν) (Σᵗ (suc m))
    ≈⟨ embed (pl-cong (topS ν) (Σᵗ-placed (suc m) μ μ0 μ1 μ2 μ3 μ4)) ⟩
  pl (topS ν) (pl μ Bx)
    ≈⟨ embed (pl-pl (topS ν) μ Bx) ⟩
  pl τ Bx ∎

------------------------------------------------------------------------
-- The exchange of the controls

private
  -- The S-box's wires 2 and 3 are neither top wire, and ρ fixes them.
  agree-mid : ∀ (j : Fin W′) → j ≢ sF 0F → j ≢ sF (sF (sF (sF 0F))) → perm ρ ⟨$⟩ʳ j ≡ j →
        perm ((swT (₄₊ m) • τ) • ρ) ⟨$⟩ʳ (perm (revS τ) ⟨$⟩ʳ j) ≡ j
  agree-mid j n1 n4 ρj =
    Eq.trans (Eq.cong (λ x → perm ρ ⟨$⟩ʳ (perm τ ⟨$⟩ʳ x)) (sw-fix a a≢q a≢6))
      (Eq.trans (Eq.cong (perm ρ ⟨$⟩ʳ_) (inv-r τ j)) ρj)
    where
    a = perm (revS τ) ⟨$⟩ʳ j
    a≢q : a ≢ tq
    a≢q e = n1 (Eq.trans (Eq.sym (inv-r τ j)) (Eq.trans (Eq.cong (perm τ ⟨$⟩ʳ_) e) τ1))
    a≢6 : a ≢ t6
    a≢6 e = n4 (Eq.trans (Eq.sym (inv-r τ j)) (Eq.trans (Eq.cong (perm τ ⟨$⟩ʳ_) e) τ4))

  agree : ∀ (j : Fin W′) → toℕ j < 5 →
          perm ((swT (₄₊ m) • τ) • ρ) ⟨$⟩ʳ (perm (revS τ) ⟨$⟩ʳ j) ≡ j
  agree 0F _ =
    Eq.trans (Eq.cong (λ x → perm ρ ⟨$⟩ʳ (perm τ ⟨$⟩ʳ (perm (swT (₄₊ m)) ⟨$⟩ʳ x))) (back-to τ τ0))
      (Eq.trans (Eq.cong (λ x → perm ρ ⟨$⟩ʳ (perm τ ⟨$⟩ʳ x)) (perm-swT-low (₄₊ m) 0F))
                (Eq.cong (perm ρ ⟨$⟩ʳ_) τ0))
  agree (sF 0F) _ =
    Eq.trans (Eq.cong (λ x → perm ρ ⟨$⟩ʳ (perm τ ⟨$⟩ʳ (perm (swT (₄₊ m)) ⟨$⟩ʳ x))) (back-to τ τ1))
      (Eq.trans (Eq.cong (λ x → perm ρ ⟨$⟩ʳ (perm τ ⟨$⟩ʳ x)) (perm-swT-top′ (₄₊ m)))
                (Eq.cong (perm ρ ⟨$⟩ʳ_) τ4))
  agree (sF (sF (sF (sF 0F)))) _ =
    Eq.trans (Eq.cong (λ x → perm ρ ⟨$⟩ʳ (perm τ ⟨$⟩ʳ (perm (swT (₄₊ m)) ⟨$⟩ʳ x))) (back-to τ τ4))
      (Eq.trans (Eq.cong (λ x → perm ρ ⟨$⟩ʳ (perm τ ⟨$⟩ʳ x)) (perm-swT-top (₄₊ m)))
                (Eq.cong (perm ρ ⟨$⟩ʳ_) τ1))
  agree (sF (sF 0F)) _ = agree-mid (sF (sF 0F)) (λ ()) (λ ()) Eq.refl
  agree (sF (sF (sF 0F))) _ = agree-mid (sF (sF (sF 0F))) (λ ()) (λ ()) Eq.refl
  agree (sF (sF (sF (sF (sF j))))) (s≤s (s≤s (s≤s (s≤s (s≤s ())))))

-- SwapSym for the doubly controlled S.
ss-S¹ : W′ ⊢ᵧ Sw • λ¹ʷ (λ¹ʷ (S {₃₊ m})) • Sw ≈ λ¹ʷ (λ¹ʷ S)
ss-S¹ = begin
  Sw • λ¹ʷ (λ¹ʷ S) • Sw                ≈⟨ back _ (front _ λλ-pl) ⟩
  Sw • pl τ Bx • Sw                    ≈⟨ embed (sw-pl τ Bx) ⟩
  pl (swT (₄₊ m) • τ) Bx               ≈⟨ cong refl (cong (sbW c₅ (suc m)) refl) ⟩
  pl (swT (₄₊ m) • τ) (pl ρ Bx)        ≈⟨ embed (pl-pl (swT (₄₊ m) • τ) ρ Bx) ⟩
  pl ((swT (₄₊ m) • τ) • ρ) Bx         ≈⟨ embed (TW.sym (place-eq {k = 5} b-Sb2-0-41-3 τ ((swT (₄₊ m) • τ) • ρ) agree)) ⟩
  pl τ Bx                              ≈⟨ sym λλ-pl ⟩
  λ¹ʷ (λ¹ʷ S)                          ∎
