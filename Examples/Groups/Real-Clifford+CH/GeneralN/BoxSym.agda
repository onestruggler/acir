------------------------------------------------------------------------
-- Presentations of groups
--
-- The box passes every swap of two adjacent controls (Clément, Lemma
-- D.8, Equation (307))
--
-- At width 4 + m, for every generator g of the symmetric group on the
-- 3 + m controls (a swap of two adjacent ones, PermCalc.φ g one wire
-- up).  The paper's proof, by the number of controls below the swap:
-- none is (275), one is (306), and more than one is the inductive
-- definition (269) of the box — the swap passes the doubly controlled
-- ZX and XZ on the wires 0–2 (disjoint wires), and the smaller box of
-- B□ one wire up by (307) one width smaller, the transposition τ₀₂
-- around it again on disjoint wires.  At width 4 the two cases are
-- FourQubit's (157) and (161).  So (307) at a width uses (275) and
-- (306) at every width up to it, and with them completeness at every
-- smaller width: the hypothesis `Completes m`.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.BoxSym
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ ; zero ; suc ; _≤_ ; z≤n ; s≤s)
open import Data.Nat.Properties using (≤-refl ; m≤n⇒m≤1+n)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

import Examples.Groups.Symmetric.Syntactics as S
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (φ ; net)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (swapAt)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
  using (module S₁₂ ; module S₂₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Box complete₂ complete₃ using (eq157 ; eq161)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZXPass complete₂ complete₃ using (Complete)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Keystone complete₂ complete₃ using (eq285ₙ)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxWire complete₂ complete₃ using (eq275)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxForms complete₂ complete₃ using (eq306)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- A circuit on the bottom three wires passes anything three wires up

low-comm₃ : (u : Circuit 3) (v : Circuit n) → (₃₊ n) ⊢ (u ↓ᵏ n) • v ↑ ↑ ↑ ≈ v ↑ ↑ ↑ • (u ↓ᵏ n)
low-comm₃ [ gate₀ () ]ʷ v
low-comm₃ [ gate₀ () ↥ ]ʷ v
low-comm₃ [ gate₀ () ↥ ↥ ]ʷ v
low-comm₃ [ gate₀ () ↥ ↥ ↥ ]ʷ v
low-comm₃ {n} [ gate₁ h ]ʷ v = sym (comm-gate₁-w↑ h (v ↑ ↑))
  where open Tools ((₃₊ n) VRel,_===_)
low-comm₃ {n} [ gate₂ h ]ʷ v = sym (comm-gate₂-w↑↑ h (v ↑))
  where open Tools ((₃₊ n) VRel,_===_)
low-comm₃ {n} [ gate₁ h ↥ ]ʷ v =
  lemma-cong↑ ([ gate₁ h ]ʷ • v ↑ ↑) (v ↑ ↑ • [ gate₁ h ]ʷ) (PB-sym (comm-gate₁-w↑ h (v ↑)))
  where open Tools ((₂₊ n) VRel,_===_) renaming (sym to PB-sym)
low-comm₃ {n} [ gate₂ h ↥ ]ʷ v =
  lemma-cong↑ ([ gate₂ h ]ʷ • v ↑ ↑) (v ↑ ↑ • [ gate₂ h ]ʷ) (PB-sym (comm-gate₂-w↑↑ h v))
  where open Tools ((₂₊ n) VRel,_===_) renaming (sym to PB-sym)
low-comm₃ {n} [ gate₁ h ↥ ↥ ]ʷ v =
  lemma-cong↑ ([ gate₁ h ↥ ]ʷ • v ↑ ↑) (v ↑ ↑ • [ gate₁ h ↥ ]ʷ)
    (lemma-cong↑ ([ gate₁ h ]ʷ • v ↑) (v ↑ • [ gate₁ h ]ʷ) (PB-sym (comm-gate₁-w↑ h v)))
  where open Tools ((₁₊ n) VRel,_===_) renaming (sym to PB-sym)
low-comm₃ {n} ε v = trans left-unit (sym right-unit)
  where open Tools ((₃₊ n) VRel,_===_)
low-comm₃ {n} (u • t) v = begin
  ((u ↓ᵏ n) • (t ↓ᵏ n)) • v ↑ ↑ ↑   ≈⟨ assoc ⟩
  (u ↓ᵏ n) • ((t ↓ᵏ n) • v ↑ ↑ ↑)   ≈⟨ back _ (low-comm₃ t v) ⟩
  (u ↓ᵏ n) • (v ↑ ↑ ↑ • (t ↓ᵏ n))   ≈⟨ sym assoc ⟩
  ((u ↓ᵏ n) • v ↑ ↑ ↑) • (t ↓ᵏ n)   ≈⟨ front _ (low-comm₃ u v) ⟩
  (v ↑ ↑ ↑ • (u ↓ᵏ n)) • (t ↓ᵏ n)   ≈⟨ assoc ⟩
  v ↑ ↑ ↑ • (u ↓ᵏ n) • (t ↓ᵏ n) ∎
  where open Tools ((₃₊ n) VRel,_===_)

------------------------------------------------------------------------
-- (307)

Sym : ℕ → Set
Sym m = ∀ (g : S.Gen (₃₊ m)) → (₄₊ m) ⊢ φ g ↑ • Λ□ (₃₊ m) ≈ Λ□ (₃₊ m) • φ g ↑

-- Completeness at every width from 3 up to 3 + m.
Completes : ℕ → Set
Completes m = ∀ {j} → j ≤ m → Complete j

sym-0 : Sym 0
sym-0 (S.gate₀ ())
sym-0 (S.gate₁ ())
sym-0 (S.gate₂ S.σ-gate)       = S₁₂.⟪⟫-comm eq157
sym-0 (S.gate₀ () S.↥)
sym-0 (S.gate₁ () S.↥)
sym-0 (S.gate₂ S.σ-gate S.↥)   = S₂₃.⟪⟫-comm eq161
sym-0 (S.gate₀ () S.↥ S.↥)
sym-0 (S.gate₁ () S.↥ S.↥)
sym-0 (S.gate₀ () S.↥ S.↥ S.↥)

sym-suc : ∀ k → Complete k → Complete (₁₊ k) → Sym k → Sym (₁₊ k)
sym-suc k c c′ ih (S.gate₀ ())
sym-suc k c c′ ih (S.gate₁ ())
sym-suc k c c′ ih (S.gate₂ S.σ-gate)       = S₁₂.⟪⟫-comm (eq275 k (eq285ₙ k c))
sym-suc k c c′ ih (S.gate₀ () S.↥)
sym-suc k c c′ ih (S.gate₁ () S.↥)
sym-suc k c c′ ih (S.gate₂ S.σ-gate S.↥)   = eq306 k c′
sym-suc k c c′ ih (g S.↥ S.↥) = pass• W-g (pass• B-g (pass• V-g B-g))
  where
  open Tools ((₁₊ (₄₊ k)) VRel,_===_)

  s : Circuit (₁₊ (₄₊ k))
  s = φ g ↑ ↑ ↑

  pass• : ∀ {a w : Circuit (₁₊ (₄₊ k))} → (₁₊ (₄₊ k)) ⊢ s • a ≈ a • s →
          (₁₊ (₄₊ k)) ⊢ s • w ≈ w • s → (₁₊ (₄₊ k)) ⊢ s • (a • w) ≈ (a • w) • s
  pass• {a} {w} ea ew = begin
    s • (a • w)     ≈⟨ sym assoc ⟩
    (s • a) • w     ≈⟨ front _ ea ⟩
    (a • s) • w     ≈⟨ assoc ⟩
    a • (s • w)     ≈⟨ back _ ew ⟩
    a • (w • s)     ≈⟨ sym assoc ⟩
    (a • w) • s ∎

  W-g : (₁₊ (₄₊ k)) ⊢ s • CCZX ≈ CCZX • s
  W-g = sym (low-comm₃ CCZX (φ g))

  V-g : (₁₊ (₄₊ k)) ⊢ s • CCXZ ≈ CCXZ • s
  V-g = sym (low-comm₃ CCXZ (φ g))

  τ-g : (₁₊ (₄₊ k)) ⊢ s • τ₀₂ ≈ τ₀₂ • s
  τ-g = sym (low-comm₃ τ₀₂ (φ g))

  -- The smaller box one wire up: (307) one width smaller, lifted.
  Λ-g : (₁₊ (₄₊ k)) ⊢ s • Λ□ (₃₊ k) ↑ ≈ Λ□ (₃₊ k) ↑ • s
  Λ-g = lemma-cong↑ (φ g ↑ ↑ • Λ□ (₃₊ k)) (Λ□ (₃₊ k) • φ g ↑ ↑) (ih (g S.↥))

  -- B□ (1 + k) written out.
  B□′ : Circuit (₁₊ (₄₊ k))
  B□′ = τ₀₂ • Λ□ (₃₊ k) ↑ • τ₀₂

  B-g : (₁₊ (₄₊ k)) ⊢ s • B□′ ≈ B□′ • s
  B-g = pass• τ-g (pass• Λ-g τ-g)

-- (307) at every width, from completeness at every smaller one.
eq307 : ∀ m → Completes m → Sym m
eq307 zero    cs = sym-0
eq307 (suc k) cs = sym-suc k (cs (m≤n⇒m≤1+n ≤-refl)) (cs ≤-refl) (eq307 k (λ j≤k → cs (m≤n⇒m≤1+n j≤k)))

-- Any network of the controls passes the box.
sym-net : ∀ m → Sym m → ∀ (w : Word (S.Gen (₃₊ m))) →
          (₄₊ m) ⊢ net w ↑ • Λ□ (₃₊ m) ≈ Λ□ (₃₊ m) • net w ↑
sym-net m s [ g ]ʷ = s g
sym-net m s ε = trans left-unit (sym right-unit)
  where open Tools ((₄₊ m) VRel,_===_)
sym-net m s (u • v) = begin
  (net u ↑ • net v ↑) • Λ       ≈⟨ assoc ⟩
  net u ↑ • (net v ↑ • Λ)       ≈⟨ back _ (sym-net m s v) ⟩
  net u ↑ • (Λ • net v ↑)       ≈⟨ sym assoc ⟩
  (net u ↑ • Λ) • net v ↑       ≈⟨ front _ (sym-net m s u) ⟩
  (Λ • net u ↑) • net v ↑       ≈⟨ assoc ⟩
  Λ • (net u ↑ • net v ↑) ∎
  where
  open Tools ((₄₊ m) VRel,_===_)
  Λ : Circuit (₄₊ m)
  Λ = Λ□ (₃₊ m)

------------------------------------------------------------------------
-- The same by wire number (MultiControlled.swapAt, the identity out of
-- range): the box passes the swap of the wires c + 1, c + 2, for every c

SymAt : ℕ → Set
SymAt m = ∀ c → (₄₊ m) ⊢ swapAt (suc c) • Λ□ (₃₊ m) ≈ Λ□ (₃₊ m) • swapAt (suc c)

symAt-0 : SymAt 0
symAt-0 zero                = S₁₂.⟪⟫-comm eq157
symAt-0 (suc zero)          = S₂₃.⟪⟫-comm eq161
symAt-0 (suc (suc zero))    = trans left-unit (sym right-unit)
  where open Tools (4 VRel,_===_)
symAt-0 (suc (suc (suc c))) = trans left-unit (sym right-unit)
  where open Tools (4 VRel,_===_)

symAt-suc : ∀ k → Complete k → Complete (₁₊ k) → SymAt k → SymAt (₁₊ k)
symAt-suc k c c′ ih zero             = S₁₂.⟪⟫-comm (eq275 k (eq285ₙ k c))
symAt-suc k c c′ ih (suc zero)       = eq306 k c′
symAt-suc k c c′ ih (suc (suc j)) = pass• W-g (pass• B-g (pass• V-g B-g))
  where
  open Tools ((₁₊ (₄₊ k)) VRel,_===_)

  s : Circuit (₁₊ (₄₊ k))
  s = swapAt j ↑ ↑ ↑

  pass• : ∀ {a w : Circuit (₁₊ (₄₊ k))} → (₁₊ (₄₊ k)) ⊢ s • a ≈ a • s →
          (₁₊ (₄₊ k)) ⊢ s • w ≈ w • s → (₁₊ (₄₊ k)) ⊢ s • (a • w) ≈ (a • w) • s
  pass• {a} {w} ea ew = begin
    s • (a • w)     ≈⟨ sym assoc ⟩
    (s • a) • w     ≈⟨ front _ ea ⟩
    (a • s) • w     ≈⟨ assoc ⟩
    a • (s • w)     ≈⟨ back _ ew ⟩
    a • (w • s)     ≈⟨ sym assoc ⟩
    (a • w) • s ∎

  W-g : (₁₊ (₄₊ k)) ⊢ s • CCZX ≈ CCZX • s
  W-g = sym (low-comm₃ CCZX (swapAt j))

  V-g : (₁₊ (₄₊ k)) ⊢ s • CCXZ ≈ CCXZ • s
  V-g = sym (low-comm₃ CCXZ (swapAt j))

  τ-g : (₁₊ (₄₊ k)) ⊢ s • τ₀₂ ≈ τ₀₂ • s
  τ-g = sym (low-comm₃ τ₀₂ (swapAt j))

  Λ-g : (₁₊ (₄₊ k)) ⊢ s • Λ□ (₃₊ k) ↑ ≈ Λ□ (₃₊ k) ↑ • s
  Λ-g = lemma-cong↑ (swapAt j ↑ ↑ • Λ□ (₃₊ k)) (Λ□ (₃₊ k) • swapAt j ↑ ↑) (ih (suc j))

  B□′ : Circuit (₁₊ (₄₊ k))
  B□′ = τ₀₂ • Λ□ (₃₊ k) ↑ • τ₀₂

  B-g : (₁₊ (₄₊ k)) ⊢ s • B□′ ≈ B□′ • s
  B-g = pass• τ-g (pass• Λ-g τ-g)

eqSymAt : ∀ m → Completes m → SymAt m
eqSymAt zero    cs = symAt-0
eqSymAt (suc k) cs = symAt-suc k (cs (m≤n⇒m≤1+n ≤-refl)) (cs ≤-refl) (eqSymAt k (λ j≤k → cs (m≤n⇒m≤1+n j≤k)))
