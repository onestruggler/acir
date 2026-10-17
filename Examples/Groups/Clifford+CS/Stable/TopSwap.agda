------------------------------------------------------------------------
-- Presentations of groups
--
-- The swap of the top two wires as an affine circuit
--
-- On 5 + m wires the exchange of the top two wires, Lambda's Swᵗ, is
-- the affine word SW tq tp = T tq tp • T tp tq • T tq tp of
-- Affine.Theory, read by Affine.Circuits (`sw-aff`, and `sw-aff′` for
-- its reverse, the same word bracketed the other way): Swᵗ k is the
-- swap placed by any network that brings the wires k, k + 1 to the
-- bottom (`Swᵗ-placed`, as Stable.XPlace does for X), and on two wires
-- the swap is the three CX of Affine.Circuits' frame (`T-frame`), by one
-- two-wire evaluation.  Its bit map exchanges the top two bits
-- (`amap-sw`).  So Hyper.D-eqv moves the gadgets of a decoded word
-- across the swap of the top two wires — what K on the top wire needs.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)

module Examples.Groups.Clifford+CS.Stable.TopSwap (m : ℕ) (c4 : Complete 4) where

open import Data.Bool using (Bool ; true ; false ; not ; _xor_ ; if_then_else_)
open import Data.Fin using (Fin ; toℕ ; fromℕ ; inject₁) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Properties using (fromℕ≢inject₁)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Nat using (zero ; suc ; s≤s)
open import Data.Product using (proj₁ ; proj₂)
open import Data.Vec using (Vec ; [] ; _∷_ ; _∷ʳ_ ; lookup)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₂₊ ; ₃₊ ; ₄₊)

import Presentation.Base as PB
import Examples.Groups.Symmetric.Syntactics as S

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Tools using (module Tools)
open import Examples.Groups.Clifford+CS.Completeness using (complete₂)
open import Examples.Groups.Clifford+CS.SemanticSteps using (module Below)
open import Examples.Groups.Clifford+CS.PermCalc using (perm ; revS ; perm-inv)
open import Examples.Groups.Clifford+CS.LocalPlace using (pl ; place-eq ; pl-cong ; pl-•)
open import Examples.Groups.Clifford+CS.Networks using (bring₂)
open import Examples.Groups.Clifford+CS.Lambda using (Swᵗ)
open import Examples.Groups.Clifford+CS.Lambda.Placed using (cycS ; up-step ; perm-up)
open import Examples.Groups.Clifford+CS.NetTop using (topS)
import Examples.Groups.Clifford+CS.Affine.Theory as Theory
import Examples.Groups.Clifford+CS.Affine.Alpha as Alpha
import Examples.Groups.Clifford+CS.Affine.Equivariance as Equivariance
import Examples.Groups.Clifford+CS.Affine.Circuits as Circuits

private
  module S₂ = Below 2 complete₂

  back-to : ∀ {w} (ν : Word (S.Gen w)) {a i} → perm ν ⟨$⟩ʳ a ≡ i → perm (revS ν) ⟨$⟩ʳ i ≡ a
  back-to ν {a} e = Eq.subst (λ x → perm (revS ν) ⟨$⟩ʳ x ≡ a) e (perm-inv ν a)

  agree2 : ∀ {r} (ν τ : Word (S.Gen (₂₊ r))) {a b} →
           perm ν ⟨$⟩ʳ a ≡ 0F → perm ν ⟨$⟩ʳ b ≡ sF 0F → perm τ ⟨$⟩ʳ a ≡ 0F → perm τ ⟨$⟩ʳ b ≡ sF 0F →
           ∀ (j : Fin (₂₊ r)) → toℕ j Data.Nat.< 2 → perm τ ⟨$⟩ʳ (perm (revS ν) ⟨$⟩ʳ j) ≡ j
  agree2 ν τ νa νb τa τb 0F          _ = Eq.trans (Eq.cong (perm τ ⟨$⟩ʳ_) (back-to ν νa)) τa
  agree2 ν τ νa νb τa τb (sF 0F)     _ = Eq.trans (Eq.cong (perm τ ⟨$⟩ʳ_) (back-to ν νb)) τb
  agree2 ν τ νa νb τa τb (sF (sF j)) (s≤s (s≤s ()))

  pl-ε : ∀ {w} (g : Circuit w) → w ⊢ pl ε g ≈ g
  pl-ε g = PB.trans PB.left-unit PB.right-unit

------------------------------------------------------------------------
-- The swap of two wires placed by a network

-- L is the swap of the wires a, b placed by any network sending a, b to
-- 0, 1.
HS : ∀ r → Fin (₂₊ r) → Fin (₂₊ r) → Circuit (₂₊ r) → Set
HS r a b L = ∀ (τ : Word (S.Gen (₂₊ r))) → perm τ ⟨$⟩ʳ a ≡ 0F → perm τ ⟨$⟩ʳ b ≡ sF 0F →
             (₂₊ r) ⊢ L ≈ pl τ (Swap {0} ↓ᵏ r)

HS-base : HS 0 0F (sF 0F) Swap
HS-base τ τa τb = PB.trans (PB.sym (pl-ε Swap)) (place-eq {k = 2} Swap ε τ (agree2 ε τ Eq.refl Eq.refl τa τb))

HS-up : ∀ r (a b : Fin (₂₊ r)) (L : Circuit (₂₊ r)) → HS r a b L → HS (suc r) (sF a) (sF b) (L ↑)
HS-up r a b L h τ τa τb =
  PB.trans (up-step L (Swap {0} ↓ᵏ r) τ′ (h τ′ (proj₁ (proj₂ B)) (proj₂ (proj₂ B))))
           (place-eq {k = 2} Swap ν τ (agree2 ν τ νa νb τa τb))
  where
  ba : b ≢ a
  ba e with Eq.trans (Eq.sym τa) (Eq.trans (Eq.cong (λ x → perm τ ⟨$⟩ʳ sF x) (Eq.sym e)) τb)
  ... | ()
  B  = bring₂ a b ba
  τ′ = proj₁ B
  ν  = cycS (₂₊ r) • topS τ′
  νa : perm ν ⟨$⟩ʳ sF a ≡ 0F
  νa = Eq.trans (perm-up τ′ a) (Eq.cong inject₁ (proj₁ (proj₂ B)))
  νb : perm ν ⟨$⟩ʳ sF b ≡ sF 0F
  νb = Eq.trans (perm-up τ′ b) (Eq.cong inject₁ (proj₂ (proj₂ B)))

-- The swap of the top two wires.
Swᵗ-placed : ∀ k → HS k (inject₁ (fromℕ k)) (fromℕ (suc k)) (Swᵗ k)
Swᵗ-placed zero    = HS-base
Swᵗ-placed (suc k) = HS-up k (inject₁ (fromℕ k)) (fromℕ (suc k)) (Swᵗ k) (Swᵗ-placed k)

------------------------------------------------------------------------
-- As an affine word, on 5 + m wires

private
  module A₁  = Theory (₄₊ m)
  module Al₁ = Alpha (₄₊ m)
  module E₁  = Equivariance (₄₊ m)
  module C₁  = Circuits (suc m) c4
  open Tools ((suc (₄₊ m)) VRel,_===_)

  k₃ : ℕ
  k₃ = ₃₊ m

-- The top wire and the one below it.
tp tq : A₁.Wire
tp = fromℕ (₄₊ m)
tq = inject₁ (fromℕ (₃₊ m))

tq≢tp : tq ≢ tp
tq≢tp e = fromℕ≢inject₁ (Eq.sym e)

-- The swap of the two top wires as an affine word.
τsw : Word A₁.Lt
τsw = A₁.SW tq tp tq≢tp

private
  B = bring₂ tq tp (λ e → tq≢tp (Eq.sym e))
  σ = proj₁ B

  σq : perm σ ⟨$⟩ʳ tq ≡ 0F
  σq = proj₁ (proj₂ B)

  σp : perm σ ⟨$⟩ʳ tp ≡ sF 0F
  σp = proj₂ (proj₂ B)

  -- The CX from tq onto tp, and from tp onto tq, in the frame σ.
  tqp : C₁.⟪ A₁.tL tq tp tq≢tp ⟫ ≈ pl σ (C₁.cx C₁.s0)
  tqp = C₁.T-frame tq≢tp σ C₁.s0 (Eq.cong (perm C₁.s0 ⟨$⟩ʳ_) σp) (Eq.cong (perm C₁.s0 ⟨$⟩ʳ_) σq)

  tpq : C₁.⟪ A₁.tL tp tq (λ e → tq≢tp (Eq.sym e)) ⟫ ≈ pl σ (C₁.cx ε)
  tpq = C₁.T-frame (λ e → tq≢tp (Eq.sym e)) σ ε σq σp

sw-aff : (suc (₄₊ m)) ⊢ Swᵗ k₃ ≈ C₁.⟪ τsw ⟫ʷ
sw-aff = begin
  Swᵗ k₃                                          ≈⟨ Swᵗ-placed k₃ σ σq σp ⟩
  pl σ (Swap {0} ↓ᵏ k₃)                           ≈⟨ pl-cong σ (S₂.by-sem Swap (C₁.cx C₁.s0 • C₁.cx ε • C₁.cx C₁.s0) Eq.refl) ⟩
  pl σ (C₁.cx C₁.s0 • C₁.cx ε • C₁.cx C₁.s0)       ≈⟨ pl-• σ (C₁.cx C₁.s0) (C₁.cx ε • C₁.cx C₁.s0) ⟩
  pl σ (C₁.cx C₁.s0) • pl σ (C₁.cx ε • C₁.cx C₁.s0) ≈⟨ cong refl (pl-• σ (C₁.cx ε) (C₁.cx C₁.s0)) ⟩
  pl σ (C₁.cx C₁.s0) • pl σ (C₁.cx ε) • pl σ (C₁.cx C₁.s0) ≈⟨ sym (cong tqp (cong tpq tqp)) ⟩
  C₁.⟪ τsw ⟫ʷ ∎

sw-aff′ : (suc (₄₊ m)) ⊢ Swᵗ k₃ ≈ C₁.⟪ A₁.rev τsw ⟫ʷ
sw-aff′ = trans sw-aff (sym assoc)

------------------------------------------------------------------------
-- Its bit map

private
  lk-top : ∀ {k} (v : Vec Bool k) (b : Bool) → lookup (v ∷ʳ b) (fromℕ k) ≡ b
  lk-top []      b = Eq.refl
  lk-top (x ∷ v) b = lk-top v b

  lk-inj : ∀ {k} (v : Vec Bool k) (b : Bool) (i : Fin k) → lookup (v ∷ʳ b) (inject₁ i) ≡ lookup v i
  lk-inj (x ∷ v) b 0F     = Eq.refl
  lk-inj (x ∷ v) b (sF i) = lk-inj v b i

  tg-top : ∀ {k} (v : Vec Bool k) (b : Bool) → A₁.toggle (v ∷ʳ b) (fromℕ k) ≡ v ∷ʳ not b
  tg-top []      b = Eq.refl
  tg-top (x ∷ v) b = Eq.cong (x ∷_) (tg-top v b)

  tg-inj : ∀ {k} (v : Vec Bool k) (b : Bool) (i : Fin k) → A₁.toggle (v ∷ʳ b) (inject₁ i) ≡ A₁.toggle v i ∷ʳ b
  tg-inj (x ∷ v) b 0F     = Eq.refl
  tg-inj (x ∷ v) b (sF i) = Eq.cong (x ∷_) (tg-inj v b i)

  xt : ∀ b → not b ≡ (b xor true)
  xt true  = Eq.refl
  xt false = Eq.refl

  xf : ∀ b → b ≡ (b xor false)
  xf true  = Eq.refl
  xf false = Eq.refl

  -- The two CX on a vector (c a) b.
  t-qp : ∀ (c : Vec Bool k₃) (a b : Bool) → E₁.tmap tq tp ((c ∷ʳ a) ∷ʳ b) ≡ (c ∷ʳ a) ∷ʳ (b xor a)
  t-qp c a b =
    Eq.trans (Eq.cong (λ t → if t then A₁.toggle x tp else x) (Eq.trans (lk-inj (c ∷ʳ a) b (fromℕ k₃)) (lk-top c a)))
             (go a)
    where
    x = (c ∷ʳ a) ∷ʳ b
    go : ∀ a′ → (if a′ then A₁.toggle x tp else x) ≡ (c ∷ʳ a) ∷ʳ (b xor a′)
    go true  = Eq.trans (tg-top (c ∷ʳ a) b) (Eq.cong ((c ∷ʳ a) ∷ʳ_) (xt b))
    go false = Eq.cong ((c ∷ʳ a) ∷ʳ_) (xf b)

  t-pq : ∀ (c : Vec Bool k₃) (a b : Bool) → E₁.tmap tp tq ((c ∷ʳ a) ∷ʳ b) ≡ (c ∷ʳ (a xor b)) ∷ʳ b
  t-pq c a b =
    Eq.trans (Eq.cong (λ t → if t then A₁.toggle x tq else x) (lk-top (c ∷ʳ a) b)) (go b)
    where
    x = (c ∷ʳ a) ∷ʳ b
    go : ∀ b′ → (if b′ then A₁.toggle x tq else x) ≡ (c ∷ʳ (a xor b′)) ∷ʳ b
    go true  = Eq.trans (tg-inj (c ∷ʳ a) b (fromℕ k₃))
                 (Eq.cong (_∷ʳ b) (Eq.trans (tg-top c a) (Eq.cong (c ∷ʳ_) (xt a))))
    go false = Eq.cong (λ y → (c ∷ʳ y) ∷ʳ b) (xf a)

  x1 : ∀ a b → (a xor (b xor a)) ≡ b
  x1 true  true  = Eq.refl
  x1 true  false = Eq.refl
  x1 false true  = Eq.refl
  x1 false false = Eq.refl

  x2 : ∀ a b → ((b xor a) xor b) ≡ a
  x2 true  true  = Eq.refl
  x2 true  false = Eq.refl
  x2 false true  = Eq.refl
  x2 false false = Eq.refl

-- The swap exchanges the top two bits.
amap-sw : ∀ (c : Vec Bool k₃) (a b : Bool) → Al₁.amapʷ τsw ((c ∷ʳ a) ∷ʳ b) ≡ (c ∷ʳ b) ∷ʳ a
amap-sw c a b =
  Eq.trans (Eq.cong (E₁.tmap tq tp) (Eq.trans (Eq.cong (E₁.tmap tp tq) (t-qp c a b)) (t-pq c a (b xor a))))
    (Eq.trans (t-qp c (a xor (b xor a)) (b xor a))
      (Eq.cong₂ (λ y z → (c ∷ʳ y) ∷ʳ z) (x1 a b) (Eq.trans (Eq.cong ((b xor a) xor_) (x1 a b)) (x2 a b))))
