------------------------------------------------------------------------
-- Presentations of groups
--
-- The letters of the controlled functor as placed canonical letters
--
-- Every letter of λ¹ on 5 + n wires is one of six canonical letters —
-- S on one wire, CS or CK on two, or one of the three S-boxes of
-- Five.Letters on five — placed by any network that sends the letter's
-- wires to the canonical ones (`placed`): the functor builds its letters
-- by `stretch` (an idle wire inserted below the top: a placement by the
-- exchange of the top two wires, `stretch-pl`) and `_↑` (a placement by
-- the cycle of TopWeakening, `up-pl`), and a placement depends only on
-- where the network sends the significant wires (LocalPlace.place-eq).
-- This is what reduces an equation between letters at any width to one
-- between canonical letters on a few wires.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Lambda.Placed where

open import Data.Fin using (Fin ; toℕ ; inject₁ ; fromℕ) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _<_ ; s≤s ; z≤n)
open import Data.Product using (proj₁ ; proj₂)
open import Data.Fin.Properties using () renaming (suc-injective to Fin-suc-inj)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

import Presentation.Base as PB
import Examples.Groups.Symmetric.Syntactics as S

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.MultiControlled using (top ; CK₁₀)
open import Examples.Groups.Clifford+CS.TopWeakening using (σ ; σ⁻¹ ; σσ⁻¹ ; nat ; top-cong)
open import Examples.Groups.Clifford+CS.PermCalc using (net ; net-↑ ; perm ; revS ; revS-↑ ; perm-inv)
open import Examples.Groups.Clifford+CS.LocalPlace using (pl ; pl-pl ; place-eq)
open import Examples.Groups.Clifford+CS.Networks using (perm-↑0 ; perm-↑s ; bring₁ ; bring₂ ; bring₅)
open import Examples.Groups.Clifford+CS.NetTop using (topS ; perm-top ; pl-top)
open import Examples.Groups.Clifford+CS.Lambda using (Swᵗ ; stretch ; Sᵗ ; CSᵗ ; CKᵗ ; Σᵗ ; λ¹)
open import Examples.Groups.Clifford+CS.Five.Letters using (b-Sb2-0-41-3 ; b-Sb0-1-42-3 ; b-Sb0-2-43-1)

private
  variable
    n k : ℕ

------------------------------------------------------------------------
-- The cycle: w ↑ is top w placed

cycS : (n : ℕ) → Word (S.Gen (₁₊ n))
cycS zero    = ε
cycS (suc n) = S.σ • cycS n S.↑

net-cyc : ∀ n → net (cycS n) ≡ σ n
net-cyc zero    = Eq.refl
net-cyc (suc n) = Eq.cong (Swap •_) (Eq.trans (net-↑ (cycS n)) (Eq.cong _↑ (net-cyc n)))

net-cyc⁻ : ∀ n → net (revS (cycS n)) ≡ σ⁻¹ n
net-cyc⁻ zero    = Eq.refl
net-cyc⁻ (suc n) =
  Eq.cong (_• Swap) (Eq.trans (Eq.cong net (revS-↑ (cycS n)))
                              (Eq.trans (net-↑ (revS (cycS n))) (Eq.cong _↑ (net-cyc⁻ n))))

up-pl : ∀ (w : Circuit n) → (₁₊ n) ⊢ w ↑ ≈ pl (cycS n) (top w)
up-pl {n} w = begin
  w ↑                           ≈⟨ sym right-unit ⟩
  w ↑ • ε                       ≈⟨ back _ (sym (σσ⁻¹ n)) ⟩
  w ↑ • (σ n • σ⁻¹ n)           ≈⟨ sym assoc ⟩
  (w ↑ • σ n) • σ⁻¹ n           ≈⟨ front _ (nat w) ⟩
  (σ n • top w) • σ⁻¹ n         ≈⟨ assoc ⟩
  σ n • top w • σ⁻¹ n           ≈⟨ ≡→≈ (Eq.sym (Eq.cong₂ (λ a b → a • top w • b) (net-cyc n) (net-cyc⁻ n))) ⟩
  pl (cycS n) (top w) ∎
  where
  open Tools ((₁₊ n) VRel,_===_)
  ≡→≈ : ∀ {a b : Circuit (₁₊ n)} → a ≡ b → a ≈ b
  ≡→≈ Eq.refl = refl

perm-cyc : ∀ n (j : Fin n) → perm (cycS n) ⟨$⟩ʳ sF j ≡ inject₁ j
perm-cyc (suc n) 0F     = perm-↑0 (cycS n)
perm-cyc (suc n) (sF j) = Eq.trans (perm-↑s (cycS n) (sF j)) (Eq.cong sF (perm-cyc n j))

------------------------------------------------------------------------
-- The exchange of the top two wires: stretch c is top c placed

swT : (k : ℕ) → Word (S.Gen (₂₊ k))
swT zero    = S.σ
swT (suc k) = swT k S.↑

net-swT : ∀ k → net (swT k) ≡ Swᵗ k
net-swT zero    = Eq.refl
net-swT (suc k) = Eq.trans (net-↑ (swT k)) (Eq.cong _↑ (net-swT k))

revS-swT : ∀ k → revS (swT k) ≡ swT k
revS-swT zero    = Eq.refl
revS-swT (suc k) = Eq.trans (revS-↑ (swT k)) (Eq.cong S._↑ (revS-swT k))

stretch-pl : ∀ (c : Circuit (₂₊ k)) → stretch c ≡ pl (swT (suc k)) (top c)
stretch-pl {k} c =
  Eq.sym (Eq.cong₂ (λ a b → a • top c • b) (net-swT (suc k))
                   (Eq.trans (Eq.cong net (revS-swT (suc k))) (net-swT (suc k))))

perm-swT-top : ∀ k → perm (swT k) ⟨$⟩ʳ fromℕ (₁₊ k) ≡ inject₁ (fromℕ k)
perm-swT-top zero    = Eq.refl
perm-swT-top (suc k) = Eq.trans (perm-↑s (swT k) (fromℕ (₁₊ k))) (Eq.cong sF (perm-swT-top k))

perm-swT-low : ∀ k (w : Fin k) → perm (swT k) ⟨$⟩ʳ inject₁ (inject₁ w) ≡ inject₁ (inject₁ w)
perm-swT-low (suc k) 0F     = perm-↑0 (swT k)
perm-swT-low (suc k) (sF w) = Eq.trans (perm-↑s (swT k) (inject₁ (inject₁ w))) (Eq.cong sF (perm-swT-low k w))

------------------------------------------------------------------------
-- A placement survives ↑ and stretch

module _ {m : ℕ} where
  private
    module T₁ = Tools ((₁₊ m) VRel,_===_)

  up-step : ∀ (g X : Circuit m) (τ′ : Word (S.Gen m)) → m ⊢ g ≈ pl τ′ X →
            (₁₊ m) ⊢ g ↑ ≈ pl (cycS m • topS τ′) (top X)
  up-step g X τ′ e = T₁.begin
    g ↑                              T₁.≈⟨ up-pl g ⟩
    pl (cycS m) (top g)              T₁.≈⟨ T₁.cong T₁.refl (T₁.cong (top-cong e) T₁.refl) ⟩
    pl (cycS m) (top (pl τ′ X))      T₁.≈⟨ ≡→≈ (Eq.cong (pl (cycS m)) (pl-top τ′ X)) ⟩
    pl (cycS m) (pl (topS τ′) (top X)) T₁.≈⟨ pl-pl (cycS m) (topS τ′) (top X) ⟩
    pl (cycS m • topS τ′) (top X) T₁.∎
    where
    ≡→≈ : ∀ {a b : Circuit (₁₊ m)} → a ≡ b → (₁₊ m) ⊢ a ≈ b
    ≡→≈ Eq.refl = T₁.refl

  perm-up : ∀ (τ′ : Word (S.Gen m)) (w : Fin m) → perm (cycS m • topS τ′) ⟨$⟩ʳ sF w ≡ inject₁ (perm τ′ ⟨$⟩ʳ w)
  perm-up τ′ w = Eq.trans (Eq.cong (perm (topS τ′) ⟨$⟩ʳ_) (perm-cyc m w)) (perm-top τ′ w)

stretch-step : ∀ (g X : Circuit (₂₊ k)) (τ′ : Word (S.Gen (₂₊ k))) → (₂₊ k) ⊢ g ≈ pl τ′ X →
               (₃₊ k) ⊢ stretch g ≈ pl (swT (suc k) • topS τ′) (top X)
stretch-step {k} g X τ′ e = T₃.begin
  stretch g                                T₃.≈⟨ ≡→≈ (stretch-pl g) ⟩
  pl (swT (suc k)) (top g)                 T₃.≈⟨ T₃.cong T₃.refl (T₃.cong (top-cong e) T₃.refl) ⟩
  pl (swT (suc k)) (top (pl τ′ X))         T₃.≈⟨ ≡→≈ (Eq.cong (pl (swT (suc k))) (pl-top τ′ X)) ⟩
  pl (swT (suc k)) (pl (topS τ′) (top X))  T₃.≈⟨ pl-pl (swT (suc k)) (topS τ′) (top X) ⟩
  pl (swT (suc k) • topS τ′) (top X) T₃.∎
  where
  module T₃ = Tools ((₃₊ k) VRel,_===_)
  ≡→≈ : ∀ {a b : Circuit (₃₊ k)} → a ≡ b → (₃₊ k) ⊢ a ≈ b
  ≡→≈ Eq.refl = T₃.refl

perm-stretch-top : ∀ k (τ′ : Word (S.Gen (₂₊ k))) →
                   perm (swT (suc k) • topS τ′) ⟨$⟩ʳ fromℕ (₂₊ k) ≡ inject₁ (perm τ′ ⟨$⟩ʳ fromℕ (₁₊ k))
perm-stretch-top k τ′ = Eq.trans (Eq.cong (perm (topS τ′) ⟨$⟩ʳ_) (perm-swT-top (suc k))) (perm-top τ′ (fromℕ (₁₊ k)))

perm-stretch-low : ∀ k (τ′ : Word (S.Gen (₂₊ k))) (w : Fin (₁₊ k)) →
                   perm (swT (suc k) • topS τ′) ⟨$⟩ʳ inject₁ (inject₁ w) ≡ inject₁ (perm τ′ ⟨$⟩ʳ inject₁ w)
perm-stretch-low k τ′ w = Eq.trans (Eq.cong (perm (topS τ′) ⟨$⟩ʳ_) (perm-swT-low (suc k) w)) (perm-top τ′ (inject₁ w))

------------------------------------------------------------------------
-- The canonical letters

data C2 : Set where
  cCS cCK : C2

can2 : C2 → Circuit 2
can2 cCS = CS
can2 cCK = CK₁₀

data C5 : Set where
  cΣ0 cΣ1 cΣ2 : C5

-- Σ(0; t, 1 | 2, 3), Σ(1; t, 2 | 0, 3), Σ(2; t, 3 | 0, 1), t = 4.
can5 : C5 → Circuit 5
can5 cΣ0 = b-Sb2-0-41-3
can5 cΣ1 = b-Sb0-1-42-3
can5 cΣ2 = b-Sb0-2-43-1

private
  top-S : ∀ r → top (S {0} ↓ᵏ r) ≡ S {0} ↓ᵏ suc r
  top-S r = Eq.refl

  top-can2 : ∀ κ r → top (can2 κ ↓ᵏ r) ≡ can2 κ ↓ᵏ suc r
  top-can2 cCS r = Eq.refl
  top-can2 cCK r = Eq.refl

  top-can5 : ∀ κ r → top (can5 κ ↓ᵏ r) ≡ can5 κ ↓ᵏ suc r
  top-can5 cΣ0 r = Eq.refl
  top-can5 cΣ1 r = Eq.refl
  top-can5 cΣ2 r = Eq.refl

  back-to : ∀ {w} (ν : Word (S.Gen w)) {a i} → perm ν ⟨$⟩ʳ a ≡ i → perm (revS ν) ⟨$⟩ʳ i ≡ a
  back-to ν {a} e = Eq.subst (λ x → perm (revS ν) ⟨$⟩ʳ x ≡ a) e (perm-inv ν a)

  ≡→≈ : ∀ {w} {a b : Circuit w} → a ≡ b → w ⊢ a ≈ b
  ≡→≈ Eq.refl = PB.refl

  pl-ε : ∀ {w} (g : Circuit w) → w ⊢ pl ε g ≈ g
  pl-ε g = PB.trans PB.left-unit PB.right-unit


------------------------------------------------------------------------
-- Placement predicates: the letter is the canonical one placed by any
-- network sending its wires to the canonical positions

HS : ∀ r → Fin (₁₊ r) → Circuit (₁₊ r) → Set
HS r t L = ∀ (τ : Word (S.Gen (₁₊ r))) → perm τ ⟨$⟩ʳ t ≡ 0F → (₁₊ r) ⊢ L ≈ pl τ (S {0} ↓ᵏ r)

H2 : ∀ r → C2 → (a t : Fin (₂₊ r)) → Circuit (₂₊ r) → Set
H2 r κ a t L = ∀ (τ : Word (S.Gen (₂₊ r))) → perm τ ⟨$⟩ʳ a ≡ 0F → perm τ ⟨$⟩ʳ t ≡ sF 0F →
               (₂₊ r) ⊢ L ≈ pl τ (can2 κ ↓ᵏ r)

H5 : ∀ r → C5 → (w0 w1 w2 w3 w4 : Fin (5 + r)) → Circuit (5 + r) → Set
H5 r κ w0 w1 w2 w3 w4 L =
  ∀ (τ : Word (S.Gen (5 + r))) → perm τ ⟨$⟩ʳ w0 ≡ 0F → perm τ ⟨$⟩ʳ w1 ≡ sF 0F → perm τ ⟨$⟩ʳ w2 ≡ sF (sF 0F) →
  perm τ ⟨$⟩ʳ w3 ≡ sF (sF (sF 0F)) → perm τ ⟨$⟩ʳ w4 ≡ sF (sF (sF (sF 0F))) → (5 + r) ⊢ L ≈ pl τ (can5 κ ↓ᵏ r)

------------------------------------------------------------------------
-- From one network to any other with the same images

private
  agree1 : ∀ {r} (ν τ : Word (S.Gen (₁₊ r))) {a} → perm ν ⟨$⟩ʳ a ≡ 0F → perm τ ⟨$⟩ʳ a ≡ 0F →
           ∀ (j : Fin (₁₊ r)) → toℕ j < 1 → perm τ ⟨$⟩ʳ (perm (revS ν) ⟨$⟩ʳ j) ≡ j
  agree1 ν τ eν eτ 0F     _        = Eq.trans (Eq.cong (perm τ ⟨$⟩ʳ_) (back-to ν eν)) eτ
  agree1 ν τ eν eτ (sF j) (s≤s ())

  agree2 : ∀ {r} (ν τ : Word (S.Gen (₂₊ r))) {a b} →
           perm ν ⟨$⟩ʳ a ≡ 0F → perm ν ⟨$⟩ʳ b ≡ sF 0F → perm τ ⟨$⟩ʳ a ≡ 0F → perm τ ⟨$⟩ʳ b ≡ sF 0F →
           ∀ (j : Fin (₂₊ r)) → toℕ j < 2 → perm τ ⟨$⟩ʳ (perm (revS ν) ⟨$⟩ʳ j) ≡ j
  agree2 ν τ νa νb τa τb 0F          _ = Eq.trans (Eq.cong (perm τ ⟨$⟩ʳ_) (back-to ν νa)) τa
  agree2 ν τ νa νb τa τb (sF 0F)     _ = Eq.trans (Eq.cong (perm τ ⟨$⟩ʳ_) (back-to ν νb)) τb
  agree2 ν τ νa νb τa τb (sF (sF j)) (s≤s (s≤s ()))

  agree5 : ∀ {r} (ν τ : Word (S.Gen (5 + r))) {a b c d f} →
           perm ν ⟨$⟩ʳ a ≡ 0F → perm ν ⟨$⟩ʳ b ≡ sF 0F → perm ν ⟨$⟩ʳ c ≡ sF (sF 0F) →
           perm ν ⟨$⟩ʳ d ≡ sF (sF (sF 0F)) → perm ν ⟨$⟩ʳ f ≡ sF (sF (sF (sF 0F))) →
           perm τ ⟨$⟩ʳ a ≡ 0F → perm τ ⟨$⟩ʳ b ≡ sF 0F → perm τ ⟨$⟩ʳ c ≡ sF (sF 0F) →
           perm τ ⟨$⟩ʳ d ≡ sF (sF (sF 0F)) → perm τ ⟨$⟩ʳ f ≡ sF (sF (sF (sF 0F))) →
           ∀ (j : Fin (5 + r)) → toℕ j < 5 → perm τ ⟨$⟩ʳ (perm (revS ν) ⟨$⟩ʳ j) ≡ j
  agree5 ν τ νa νb νc νd νf τa τb τc τd τf 0F _ = Eq.trans (Eq.cong (perm τ ⟨$⟩ʳ_) (back-to ν νa)) τa
  agree5 ν τ νa νb νc νd νf τa τb τc τd τf (sF 0F) _ = Eq.trans (Eq.cong (perm τ ⟨$⟩ʳ_) (back-to ν νb)) τb
  agree5 ν τ νa νb νc νd νf τa τb τc τd τf (sF (sF 0F)) _ = Eq.trans (Eq.cong (perm τ ⟨$⟩ʳ_) (back-to ν νc)) τc
  agree5 ν τ νa νb νc νd νf τa τb τc τd τf (sF (sF (sF 0F))) _ = Eq.trans (Eq.cong (perm τ ⟨$⟩ʳ_) (back-to ν νd)) τd
  agree5 ν τ νa νb νc νd νf τa τb τc τd τf (sF (sF (sF (sF 0F)))) _ = Eq.trans (Eq.cong (perm τ ⟨$⟩ʳ_) (back-to ν νf)) τf
  agree5 ν τ νa νb νc νd νf τa τb τc τd τf (sF (sF (sF (sF (sF j))))) (s≤s (s≤s (s≤s (s≤s (s≤s ())))))

------------------------------------------------------------------------
-- The predicates under ↑

HS-up : ∀ r (t : Fin (₁₊ r)) (L : Circuit (₁₊ r)) → HS r t L → HS (suc r) (sF t) (L ↑)
HS-up r t L h τ τt =
  PB.trans (up-step L (S {0} ↓ᵏ r) τ′ (h τ′ (proj₂ B)))
           (place-eq {k = 1} S ν τ (agree1 ν τ νt τt))
  where
  B  = bring₁ t
  τ′ = proj₁ B
  ν  = cycS (₁₊ r) • topS τ′
  νt : perm ν ⟨$⟩ʳ sF t ≡ 0F
  νt = Eq.trans (perm-up τ′ t) (Eq.cong inject₁ (proj₂ B))

H2-up : ∀ r κ (a t : Fin (₂₊ r)) → t ≢ a → (L : Circuit (₂₊ r)) → H2 r κ a t L → H2 (suc r) κ (sF a) (sF t) (L ↑)
H2-up r κ a t ta L h τ τa τt =
  PB.trans (up-step L (can2 κ ↓ᵏ r) τ′ (h τ′ (proj₁ (proj₂ B)) (proj₂ (proj₂ B))))
    (PB.trans (≡→≈ (Eq.cong (pl ν) (top-can2 κ r)))
              (place-eq {k = 2} (can2 κ) ν τ (agree2 ν τ νa νt τa τt)))
  where
  B  = bring₂ a t ta
  τ′ = proj₁ B
  ν  = cycS (₂₊ r) • topS τ′
  νa : perm ν ⟨$⟩ʳ sF a ≡ 0F
  νa = Eq.trans (perm-up τ′ a) (Eq.cong inject₁ (proj₁ (proj₂ B)))
  νt : perm ν ⟨$⟩ʳ sF t ≡ sF 0F
  νt = Eq.trans (perm-up τ′ t) (Eq.cong inject₁ (proj₂ (proj₂ B)))

H5-up : ∀ r κ (a b c d f : Fin (5 + r)) →
        b ≢ a → c ≢ a → c ≢ b → d ≢ a → d ≢ b → d ≢ c → f ≢ a → f ≢ b → f ≢ c → f ≢ d →
        (L : Circuit (5 + r)) → H5 r κ a b c d f L → H5 (suc r) κ (sF a) (sF b) (sF c) (sF d) (sF f) (L ↑)
H5-up r κ a b c d f ba ca cb da db dc fa fb fc fd L h τ τa τb τc τd τf =
  PB.trans (up-step L (can5 κ ↓ᵏ r) τ′ (h τ′ ea eb ec ed ef))
    (PB.trans (≡→≈ (Eq.cong (pl ν) (top-can5 κ r)))
              (place-eq {k = 5} (can5 κ) ν τ (agree5 ν τ νa νb νc νd νf τa τb τc τd τf)))
  where
  B  = bring₅ a b c d f ba ca cb da db dc fa fb fc fd
  τ′ = proj₁ B
  ea = proj₁ (proj₂ B)
  eb = proj₁ (proj₂ (proj₂ B))
  ec = proj₁ (proj₂ (proj₂ (proj₂ B)))
  ed = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ B))))
  ef = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ B))))
  ν  = cycS (5 + r) • topS τ′
  νa = Eq.trans (perm-up τ′ a) (Eq.cong inject₁ ea)
  νb = Eq.trans (perm-up τ′ b) (Eq.cong inject₁ eb)
  νc = Eq.trans (perm-up τ′ c) (Eq.cong inject₁ ec)
  νd = Eq.trans (perm-up τ′ d) (Eq.cong inject₁ ed)
  νf = Eq.trans (perm-up τ′ f) (Eq.cong inject₁ ef)

------------------------------------------------------------------------
-- The predicates under stretch

H2-stretch : ∀ r κ (L : Circuit (₂₊ r)) → H2 r κ 0F (fromℕ (₁₊ r)) L → H2 (suc r) κ 0F (fromℕ (₂₊ r)) (stretch L)
H2-stretch r κ L h τ τa τt =
  PB.trans (stretch-step L (can2 κ ↓ᵏ r) τ′ (h τ′ (proj₁ (proj₂ B)) (proj₂ (proj₂ B))))
    (PB.trans (≡→≈ (Eq.cong (pl ν) (top-can2 κ r)))
              (place-eq {k = 2} (can2 κ) ν τ (agree2 ν τ νa νt τa τt)))
  where
  B  = bring₂ 0F (fromℕ (₁₊ r)) (λ ())
  τ′ = proj₁ B
  ν  = swT (suc r) • topS τ′
  νa : perm ν ⟨$⟩ʳ 0F ≡ 0F
  νa = Eq.trans (perm-stretch-low r τ′ 0F) (Eq.cong inject₁ (proj₁ (proj₂ B)))
  νt : perm ν ⟨$⟩ʳ fromℕ (₂₊ r) ≡ sF 0F
  νt = Eq.trans (perm-stretch-top r τ′) (Eq.cong inject₁ (proj₂ (proj₂ B)))

-- The S-box from the wires 0, 1 borrowing 2, 3, the control on top.
H5-stretch : ∀ r (L : Circuit (5 + r)) →
             H5 r cΣ0 0F (sF 0F) (sF (sF 0F)) (sF (sF (sF 0F))) (fromℕ (₄₊ r)) L →
             H5 (suc r) cΣ0 0F (sF 0F) (sF (sF 0F)) (sF (sF (sF 0F))) (fromℕ (suc (₄₊ r))) (stretch L)
H5-stretch r L h τ τa τb τc τd τf =
  PB.trans (stretch-step L (can5 cΣ0 ↓ᵏ r) τ′ (h τ′ ea eb ec ed ef))
    (PB.trans (≡→≈ (Eq.cong (pl ν) (top-can5 cΣ0 r)))
              (place-eq {k = 5} (can5 cΣ0) ν τ (agree5 ν τ νa νb νc νd νf τa τb τc τd τf)))
  where
  B  = bring₅ 0F (sF 0F) (sF (sF 0F)) (sF (sF (sF 0F))) (fromℕ (₄₊ r))
              (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ())
  τ′ = proj₁ B
  ea = proj₁ (proj₂ B)
  eb = proj₁ (proj₂ (proj₂ B))
  ec = proj₁ (proj₂ (proj₂ (proj₂ B)))
  ed = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ B))))
  ef = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ B))))
  ν  = swT (₄₊ r) • topS τ′
  νa = Eq.trans (perm-stretch-low (₃₊ r) τ′ 0F) (Eq.cong inject₁ ea)
  νb = Eq.trans (perm-stretch-low (₃₊ r) τ′ (sF 0F)) (Eq.cong inject₁ eb)
  νc = Eq.trans (perm-stretch-low (₃₊ r) τ′ (sF (sF 0F))) (Eq.cong inject₁ ec)
  νd = Eq.trans (perm-stretch-low (₃₊ r) τ′ (sF (sF (sF 0F)))) (Eq.cong inject₁ ed)
  νf = Eq.trans (perm-stretch-top (₃₊ r) τ′) (Eq.cong inject₁ ef)

------------------------------------------------------------------------
-- The base letters

private
  HS-base : HS 0 0F S
  HS-base τ τt = PB.trans (PB.sym (pl-ε S)) (place-eq {k = 1} S ε τ (agree1 ε τ Eq.refl τt))

  ↓0₂ : ∀ κ → can2 κ ↓ᵏ 0 ≡ can2 κ
  ↓0₂ cCS = Eq.refl
  ↓0₂ cCK = Eq.refl

  ↓0₅ : ∀ κ → can5 κ ↓ᵏ 0 ≡ can5 κ
  ↓0₅ cΣ0 = Eq.refl
  ↓0₅ cΣ1 = Eq.refl
  ↓0₅ cΣ2 = Eq.refl

  H2-base : ∀ κ → H2 0 κ 0F (sF 0F) (can2 κ)
  H2-base κ τ τa τt =
    PB.trans (PB.sym (pl-ε (can2 κ)))
      (PB.trans (≡→≈ (Eq.cong (pl ε) (Eq.sym (↓0₂ κ))))
                (place-eq {k = 2} (can2 κ) ε τ (agree2 ε τ Eq.refl Eq.refl τa τt)))

H5-base : ∀ κ → H5 0 κ 0F (sF 0F) (sF (sF 0F)) (sF (sF (sF 0F))) (sF (sF (sF (sF 0F)))) (can5 κ)
H5-base κ τ τa τb τc τd τf =
    PB.trans (PB.sym (pl-ε (can5 κ)))
      (PB.trans (≡→≈ (Eq.cong (pl ε) (Eq.sym (↓0₅ κ))))
                (place-eq {k = 5} (can5 κ) ε τ (agree5 ε τ Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl τa τb τc τd τf)))

-- S on the top wire.
Sᵗ-placed : ∀ k → HS k (fromℕ k) (Sᵗ k)
Sᵗ-placed zero    = HS-base
Sᵗ-placed (suc k) = HS-up k (fromℕ k) (Sᵗ k) (Sᵗ-placed k)

-- CS and CK between wire 0 and the top.
CSᵗ-placed : ∀ k → H2 k cCS 0F (fromℕ (₁₊ k)) (CSᵗ k)
CSᵗ-placed zero    = H2-base cCS
CSᵗ-placed (suc k) = H2-stretch k cCS (CSᵗ k) (CSᵗ-placed k)

CKᵗ-placed : ∀ k → H2 k cCK 0F (fromℕ (₁₊ k)) (CKᵗ k)
CKᵗ-placed zero    = H2-base cCK
CKᵗ-placed (suc k) = H2-stretch k cCK (CKᵗ k) (CKᵗ-placed k)

-- The S-box of the wires 0, 1.
Σᵗ-placed : ∀ k → H5 k cΣ0 0F (sF 0F) (sF (sF 0F)) (sF (sF (sF 0F))) (fromℕ (₄₊ k)) (Σᵗ k)
Σᵗ-placed zero    = H5-base cΣ0
Σᵗ-placed (suc k) = H5-stretch k (Σᵗ k) (Σᵗ-placed k)

------------------------------------------------------------------------
-- Every letter of λ¹

-- Five distinct wires.
record D5 {w : ℕ} (a b c d f : Fin w) : Set where
  field
    ba : b ≢ a
    ca : c ≢ a
    cb : c ≢ b
    da : d ≢ a
    db : d ≢ b
    dc : d ≢ c
    fa : f ≢ a
    fb : f ≢ b
    fc : f ≢ c
    fd : f ≢ d

private
  sF≢ : ∀ {w} {a b : Fin w} → a ≢ b → _≢_ {A = Fin (suc w)} (sF a) (sF b)
  sF≢ ne e = ne (Fin-suc-inj e)

  D5-sF : ∀ {w} {a b c d f : Fin w} → D5 a b c d f → D5 (sF a) (sF b) (sF c) (sF d) (sF f)
  D5-sF D = record
    { ba = sF≢ (D5.ba D) ; ca = sF≢ (D5.ca D) ; cb = sF≢ (D5.cb D) ; da = sF≢ (D5.da D)
    ; db = sF≢ (D5.db D) ; dc = sF≢ (D5.dc D) ; fa = sF≢ (D5.fa D) ; fb = sF≢ (D5.fb D)
    ; fc = sF≢ (D5.fc D) ; fd = sF≢ (D5.fd D) }

  -- The canonical positions, the top fourth.
  D5-low : ∀ {r} (t : Fin (5 + r)) → t ≢ 0F → t ≢ sF 0F → t ≢ sF (sF 0F) → t ≢ sF (sF (sF 0F)) →
           D5 {5 + r} 0F (sF 0F) (sF (sF 0F)) (sF (sF (sF 0F))) t
  D5-low t t0 t1 t2 t3 = record
    { ba = λ () ; ca = λ () ; cb = λ () ; da = λ () ; db = λ () ; dc = λ ()
    ; fa = t0 ; fb = t1 ; fc = t2 ; fd = t3 }

-- Where a letter's wires go: the control is always the top wire.
data Placement (n : ℕ) (L : Circuit (suc (₄₊ n))) : Set where
  onS : HS (₄₊ n) (fromℕ (₄₊ n)) L → Placement n L
  on2 : ∀ κ (a : Fin (suc (₄₊ n))) → fromℕ (₄₊ n) ≢ a → H2 (₃₊ n) κ a (fromℕ (₄₊ n)) L → Placement n L
  on5 : ∀ κ (a b c d : Fin (suc (₄₊ n))) → D5 a b c d (fromℕ (₄₊ n)) →
        H5 n κ a b c d (fromℕ (₄₊ n)) L → Placement n L

up-placement : ∀ {n} {L : Circuit (suc (₄₊ n))} → Placement n L → Placement (suc n) (L ↑)
up-placement {n} {L} (onS h) = onS (HS-up (₄₊ n) (fromℕ (₄₊ n)) L h)
up-placement {n} {L} (on2 κ a ta h) = on2 κ (sF a) (sF≢ ta) (H2-up (₃₊ n) κ a (fromℕ (₄₊ n)) ta L h)
up-placement {n} {L} (on5 κ a b c d D h) =
  on5 κ (sF a) (sF b) (sF c) (sF d) (D5-sF D)
      (H5-up n κ a b c d (fromℕ (₄₊ n)) (D5.ba D) (D5.ca D) (D5.cb D) (D5.da D) (D5.db D)
             (D5.dc D) (D5.fa D) (D5.fb D) (D5.fc D) (D5.fd D) L h)

private
  top≢ : ∀ {r} → D5 {5 + r} 0F (sF 0F) (sF (sF 0F)) (sF (sF (sF 0F))) (fromℕ (₄₊ r))
  top≢ = D5-low _ (λ ()) (λ ()) (λ ()) (λ ())

  -- CS or CK between wire 0 and the top of a w-wire circuit, lifted to
  -- the wires 4 − w and 4 of five.
  two₃ : ∀ κ {L : Circuit 2} → H2 0 κ 0F (sF 0F) L → Placement 0 (L ↑ ↑ ↑)
  two₃ κ {L} h =
    on2 κ (sF (sF (sF 0F))) (λ ())
      (H2-up 2 κ (sF (sF 0F)) (sF (sF (sF 0F))) (λ ()) (L ↑ ↑)
        (H2-up 1 κ (sF 0F) (sF (sF 0F)) (λ ()) (L ↑)
          (H2-up 0 κ 0F (sF 0F) (λ ()) L h)))

  two₂ : ∀ κ {L : Circuit 3} → H2 1 κ 0F (sF (sF 0F)) L → Placement 0 (L ↑ ↑)
  two₂ κ {L} h =
    on2 κ (sF (sF 0F)) (λ ())
      (H2-up 2 κ (sF 0F) (sF (sF (sF 0F))) (λ ()) (L ↑)
        (H2-up 1 κ 0F (sF (sF 0F)) (λ ()) L h))

  two₁ : ∀ κ {L : Circuit 4} → H2 2 κ 0F (sF (sF (sF 0F))) L → Placement 0 (L ↑)
  two₁ κ {L} h = on2 κ (sF 0F) (λ ()) (H2-up 2 κ 0F (sF (sF (sF 0F))) (λ ()) L h)

  ident : ∀ κ → Placement 0 (can5 κ)
  ident κ = on5 κ 0F (sF 0F) (sF (sF 0F)) (sF (sF (sF 0F))) top≢ (H5-base κ)

  -- The letters of a four-wire domain above wire 0 (Lambda's λ₁, λ₂, λ₃).
  pl₁ : (g : Gen 1) → Placement 0 (λ¹ {0} (g ↥ ↥ ↥))
  pl₁ I-gen     = onS (Sᵗ-placed 4)
  pl₁ S-gen     = two₃ cCS (CSᵗ-placed 0)
  pl₁ K-gen     = two₃ cCK (CKᵗ-placed 0)
  pl₁ (I-gen ↥) = onS (Sᵗ-placed 4)

  pl₂ : (g : Gen 2) → Placement 0 (λ¹ {0} (g ↥ ↥))
  pl₂ I-gen  = onS (Sᵗ-placed 4)
  pl₂ S-gen  = two₂ cCS (CSᵗ-placed 1)
  pl₂ K-gen  = two₂ cCK (CKᵗ-placed 1)
  pl₂ CS-gen = ident cΣ2
  pl₂ (g ↥)  = pl₁ g

  pl₃ : (g : Gen 3) → Placement 0 (λ¹ {0} (g ↥))
  pl₃ I-gen  = onS (Sᵗ-placed 4)
  pl₃ S-gen  = two₁ cCS (CSᵗ-placed 2)
  pl₃ K-gen  = two₁ cCK (CKᵗ-placed 2)
  pl₃ CS-gen = ident cΣ1
  pl₃ (g ↥)  = pl₂ g

-- Every letter.
placement : ∀ {n} (g : Gen (₄₊ n)) → Placement n (λ¹ g)
placement {n}     I-gen  = onS (Sᵗ-placed (₄₊ n))
placement {n}     S-gen  = on2 cCS 0F (λ ()) (CSᵗ-placed (₃₊ n))
placement {n}     K-gen  = on2 cCK 0F (λ ()) (CKᵗ-placed (₃₊ n))
placement {n}     CS-gen = on5 cΣ0 0F (sF 0F) (sF (sF 0F)) (sF (sF (sF 0F))) top≢ (Σᵗ-placed n)
placement {suc n} (g ↥)  = up-placement (placement g)
placement {zero}  (g ↥)  = pl₃ g
