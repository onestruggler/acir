------------------------------------------------------------------------
-- Presentations of groups
--
-- The linear coset tower: the step lemmas, and the decomposition of
-- every linear circuit
--
-- A generator meeting a representative is absorbed into the
-- representative of the transformed datum, at the price of letters of
-- the stabiliser, emitted to the left:
--
--     r ℓ • y ≈ ⟪ rk ℓ y ⟫ • r (ℓ ⋆ y)       (r-step)
--     s u • y ≈ ⟪ sk u y ⟫' • s (u ⋆' y)     (s-step)
--
-- A generator above wire 0 passes the representative one wire up by
-- the step one level down, and the gadget on the bottom wires by the
-- commutations of Linear.Local; a generator on the bottom wires meets
-- the two-level gadget, the rest of the representative lying two wires
-- up and commuting with it (glue).  The column part of the normal form
-- then absorbs the letters the row emits, leaving a word on the upper
-- wires (push-sound), and every linear circuit is
--
--     W ↑ • s₁ u • r ℓ                         (decompose)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.CNOT+Dihedral.Linear.Steps where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

open import Examples.Groups.CNOT+Dihedral.Syntactics
open import Examples.Groups.CNOT+Dihedral.Reasoning
open import Examples.Groups.CNOT+Dihedral.Linear.Local
open import Examples.Groups.CNOT+Dihedral.Linear.Base

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Helpers

private
  slide : ∀ {m} {g a a' b b' : Circuit m} → m ⊢ g • a ≈ a' • g →
          m ⊢ g • b ≈ b' • g → m ⊢ g • (a • b) ≈ (a' • b') • g
  slide {m} = Width.slide m

  slide-ε : ∀ {m} {g : Circuit m} → m ⊢ g • ε ≈ ε • g
  slide-ε {m} = Width.slide-ε m

-- CX01 commutes with anything two wires up.
comm-CX01 : (w : Circuit n) → (₂₊ n) ⊢ w ↑ ↑ • CX01 ≈ CX01 • w ↑ ↑
comm-CX01 w =
  slide (comm-gate₂-w↑↑ SWAP-gate w)
        (slide (comm-gate₂-w↑↑ CNOT-gate w) (comm-gate₂-w↑↑ SWAP-gate w))

-- A step on three wires, with the rest two wires up.
glue : ∀ {g₀ g₁ y k g₀' g₁' : Circuit (₃₊ n)} (τ : Circuit (₁₊ n)) →
       (₃₊ n) ⊢ τ ↑ ↑ • y ≈ y • τ ↑ ↑ →
       (₃₊ n) ⊢ g₀ • g₁ • y ≈ k • g₀' • g₁' →
       (₃₊ n) ⊢ (g₀ • g₁ • τ ↑ ↑) • y ≈ k • g₀' • g₁' • τ ↑ ↑
glue {n} {g₀} {g₁} {y} {k} {g₀'} {g₁'} τ c e = begin
  (g₀ • g₁ • τ ↑ ↑) • y          ≈⟨ assoc ⟩
  g₀ • (g₁ • τ ↑ ↑) • y          ≈⟨ back g₀ assoc ⟩
  g₀ • g₁ • τ ↑ ↑ • y            ≈⟨ back g₀ (back g₁ c) ⟩
  g₀ • g₁ • y • τ ↑ ↑            ≈⟨ back g₀ (sym assoc) ⟩
  g₀ • (g₁ • y) • τ ↑ ↑          ≈⟨ sym assoc ⟩
  (g₀ • g₁ • y) • τ ↑ ↑          ≈⟨ front _ e ⟩
  (k • g₀' • g₁') • τ ↑ ↑        ≈⟨ assoc ⟩
  k • (g₀' • g₁') • τ ↑ ↑        ≈⟨ back k assoc ⟩
  k • g₀' • g₁' • τ ↑ ↑          ∎
  where open Width (₃₊ n)

------------------------------------------------------------------------
-- Letters of the level below, past a gadget

liftcx-comm : (k : Word (KLet (₁₊ n))) →
              (₂₊ n) ⊢ CNOT • ⟪ k ⟫ ↑ ≈ ⟪ lift-cx k ⟫ • CNOT
liftcx-comm {n} [ kup y ]ʷ = Width.sym (comm-gate₂-w↑↑ CNOT-gate [ ι y ]ʷ)
liftcx-comm [ kcx ]ʷ   = U1
liftcx-comm ε          = slide-ε
liftcx-comm (w • v)    = slide (liftcx-comm w) (liftcx-comm v)

liftsw-comm : (k : Word (KLet (₁₊ n))) →
              (₂₊ n) ⊢ SWAP • ⟪ k ⟫ ↑ ≈ ⟪ lift-sw k ⟫ • SWAP
liftsw-comm {n} [ kup y ]ʷ = Width.sym (comm-gate₂-w↑↑ SWAP-gate [ ι y ]ʷ)
liftsw-comm [ kcx ]ʷ   = U2
liftsw-comm ε          = slide-ε
liftsw-comm (w • v)    = slide (liftsw-comm w) (liftsw-comm v)

lift'cx-comm : (k : Word (K'Let (₁₊ n))) →
               (₂₊ n) ⊢ CX01 • ⟪ k ⟫' ↑ ≈ ⟪ lift'-cx k ⟫' • CX01
lift'cx-comm {n} [ kup' y ]ʷ = Width.sym (comm-CX01 [ ι y ]ʷ)
lift'cx-comm [ kcnot ]ʷ      = U3
lift'cx-comm ε               = slide-ε
lift'cx-comm (w • v)         = slide (lift'cx-comm w) (lift'cx-comm v)

lift'sw-comm : (k : Word (K'Let (₁₊ n))) →
               (₂₊ n) ⊢ SWAP • ⟪ k ⟫' ↑ ≈ ⟪ lift'-sw k ⟫' • SWAP
lift'sw-comm {n} [ kup' y ]ʷ = Width.sym (comm-gate₂-w↑↑ SWAP-gate [ ι y ]ʷ)
lift'sw-comm [ kcnot ]ʷ      = U4
lift'sw-comm ε               = slide-ε
lift'sw-comm (w • v)         = slide (lift'sw-comm w) (lift'sw-comm v)

-- The column gadget and the letters of the column stabiliser one up.
cx01-k' : (k : Word (K'Let (₁₊ n))) →
          (₂₊ n) ⊢ CX01 • ⟪ k ⟫' ↑ ≈ ⟪ k ⟫' ↑ • CX01
cx01-k' {n} [ kup' y ]ʷ = Width.sym (comm-CX01 [ ι y ]ʷ)
cx01-k' [ kcnot ]ʷ      = U3
cx01-k' ε               = slide-ε
cx01-k' (w • v)         = slide (cx01-k' w) (cx01-k' v)

------------------------------------------------------------------------
-- The step lemmas

-- A gadget followed by the rest one wire up, past a generator one
-- wire up.
private
  up-step : ∀ {g : Circuit (₂₊ n)} {ρ ρ' : Circuit (₁₊ n)} {y : Gen (₁₊ n)}
              {K : Circuit (₁₊ n)} {K' : Circuit (₂₊ n)} →
            (₁₊ n) ⊢ ρ • [ y ]ʷ ≈ K • ρ' →
            (₂₊ n) ⊢ g • K ↑ ≈ K' • g →
            (₂₊ n) ⊢ (g • ρ ↑) • [ y ↥ ]ʷ ≈ K' • g • ρ' ↑
  up-step {n} {g} {ρ} {ρ'} {y} {K} {K'} e c = begin
    (g • ρ ↑) • [ y ↥ ]ʷ     ≈⟨ assoc ⟩
    g • (ρ • [ y ]ʷ) ↑       ≈⟨ back g (lift e) ⟩
    g • (K • ρ') ↑           ≈⟨ sym assoc ⟩
    (g • K ↑) • ρ' ↑         ≈⟨ front _ c ⟩
    (K' • g) • ρ' ↑          ≈⟨ assoc ⟩
    K' • g • ρ' ↑            ∎
    where open Width (₂₊ n)

r-step : (ℓ : NZ n) (y : LGen n) → n ⊢ r ℓ • [ ι y ]ʷ ≈ ⟪ rk ℓ y ⟫ • r (ℓ ⋆ y)
r-step {n} e₀ (y ↥ₗ) = trans left-unit (sym right-unit)
  where open Width n
r-step (cx ℓ) (y ↥ₗ) = up-step (r-step ℓ y) (liftcx-comm (rk ℓ y))
r-step (sw ℓ) (y ↥ₗ) = up-step (r-step ℓ y) (liftsw-comm (rk ℓ y))
r-step {n} e₀ cnot = by-assoc Eq.refl
  where open Width n
r-step {n} e₀ swap = by-assoc Eq.refl
  where open Width n
r-step {n} (cx e₀) cnot = begin
  (CNOT • ε) • CNOT    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • CNOT          ≈⟨ ax R₄ ⟩
  ε                    ≈⟨ by-assoc Eq.refl ⟩
  ε • ε                ∎
  where open Width n
r-step {n} (cx e₀) swap = begin
  (CNOT • ε) • SWAP    ≈⟨ by-assoc Eq.refl ⟩
  CNOT • SWAP          ≈⟨ R5a ⟩
  CX01 • CNOT          ≈⟨ by-assoc Eq.refl ⟩
  CX01 • CNOT • ε      ∎
  where open Width n
r-step {n} (sw e₀) cnot = begin
  (SWAP • ε) • CNOT          ≈⟨ by-assoc Eq.refl ⟩
  SWAP • CNOT                ≈⟨ sym (Involution.cancelʳ (ax swap-order) (SWAP • CNOT)) ⟩
  (SWAP • CNOT) • SWAP • SWAP ≈⟨ by-assoc Eq.refl ⟩
  CX01 • SWAP • ε            ∎
  where open Width n
r-step {n} (sw e₀) swap = begin
  (SWAP • ε) • SWAP    ≈⟨ by-assoc Eq.refl ⟩
  SWAP • SWAP          ≈⟨ ax swap-order ⟩
  ε                    ≈⟨ by-assoc Eq.refl ⟩
  ε • ε                ∎
  where open Width n
r-step (cx (cx ℓ)) cnot = glue (r ℓ) (comm-gate₂-w↑↑ CNOT-gate (r ℓ)) R1g
r-step (cx (cx ℓ)) swap = glue (r ℓ) (comm-gate₂-w↑↑ SWAP-gate (r ℓ)) R1h
r-step (cx (sw ℓ)) cnot = glue (r ℓ) (comm-gate₂-w↑↑ CNOT-gate (r ℓ)) R1e
r-step (cx (sw ℓ)) swap = glue (r ℓ) (comm-gate₂-w↑↑ SWAP-gate (r ℓ)) (ax swap-CNOT)
r-step (sw (cx ℓ)) cnot = glue (r ℓ) (comm-gate₂-w↑↑ CNOT-gate (r ℓ)) R1c
r-step (sw (cx ℓ)) swap = glue (r ℓ) (comm-gate₂-w↑↑ SWAP-gate (r ℓ)) R1d
r-step (sw (sw ℓ)) cnot = glue (r ℓ) (comm-gate₂-w↑↑ CNOT-gate (r ℓ)) R1a
r-step (sw (sw ℓ)) swap = glue (r ℓ) (comm-gate₂-w↑↑ SWAP-gate (r ℓ)) (ax swap-braid)

s-step : (u : NZ n) (y : LGen n) → n ⊢ s u • [ ι y ]ʷ ≈ ⟪ sk u y ⟫' • s (u ⋆' y)
s-step {n} e₀ (y ↥ₗ) = trans left-unit (sym right-unit)
  where open Width n
s-step (cx u) (y ↥ₗ) = up-step (s-step u y) (lift'cx-comm (sk u y))
s-step (sw u) (y ↥ₗ) = up-step (s-step u y) (lift'sw-comm (sk u y))
s-step {n} e₀ cnot = trans left-unit (sym right-unit)
  where open Width n
s-step {n} e₀ swap = by-assoc Eq.refl
  where open Width n
s-step {n} (cx e₀) cnot = begin
  (CX01 • ε) • CNOT    ≈⟨ by-assoc Eq.refl ⟩
  CX01 • CNOT          ≈⟨ C0e ⟩
  CNOT • SWAP          ≈⟨ by-assoc Eq.refl ⟩
  CNOT • SWAP • ε      ∎
  where open Width n
s-step {n} (cx e₀) swap = begin
  (CX01 • ε) • SWAP    ≈⟨ by-assoc Eq.refl ⟩
  CX01 • SWAP          ≈⟨ C0f ⟩
  CNOT • CX01          ≈⟨ by-assoc Eq.refl ⟩
  CNOT • CX01 • ε      ∎
  where open Width n
s-step {n} (sw e₀) cnot = begin
  (SWAP • ε) • CNOT    ≈⟨ by-assoc Eq.refl ⟩
  SWAP • CNOT          ≈⟨ R5b ⟩
  CNOT • CX01          ≈⟨ by-assoc Eq.refl ⟩
  CNOT • CX01 • ε      ∎
  where open Width n
s-step {n} (sw e₀) swap = begin
  (SWAP • ε) • SWAP    ≈⟨ by-assoc Eq.refl ⟩
  SWAP • SWAP          ≈⟨ ax swap-order ⟩
  ε                    ≈⟨ by-assoc Eq.refl ⟩
  ε • ε                ∎
  where open Width n
s-step (cx (cx u)) cnot = glue (s u) (comm-gate₂-w↑↑ CNOT-gate (s u)) C1g
s-step (cx (cx u)) swap = glue (s u) (comm-gate₂-w↑↑ SWAP-gate (s u)) C1h
s-step (cx (sw u)) cnot = glue (s u) (comm-gate₂-w↑↑ CNOT-gate (s u)) C1e
s-step (cx (sw u)) swap = glue (s u) (comm-gate₂-w↑↑ SWAP-gate (s u)) C1f
s-step (sw (cx u)) cnot = glue (s u) (comm-gate₂-w↑↑ CNOT-gate (s u)) C1c
s-step (sw (cx u)) swap = glue (s u) (comm-gate₂-w↑↑ SWAP-gate (s u)) C1d
s-step (sw (sw u)) cnot = glue (s u) (comm-gate₂-w↑↑ CNOT-gate (s u)) R1a
s-step (sw (sw u)) swap = glue (s u) (comm-gate₂-w↑↑ SWAP-gate (s u)) (ax swap-braid)

------------------------------------------------------------------------
-- The column part absorbs the row's letters

nw-sound : (u : SOne (₁₊ n)) (k : KLet (₁₊ n)) →
           (₁₊ n) ⊢ s₁ u • κ k ≈ nw u k ↑ • s₁ (u ⋆ₙ k)
nw-sound {n} one₀ (kup y) = trans left-unit (sym right-unit)
  where open Width (₁₊ n)
nw-sound (one u) (kup y) = up-step (s-step u y) (cx01-k' (sk u y))
nw-sound {n} one₀ kcx = by-assoc Eq.refl
  where open Width (₁₊ n)
nw-sound {n} (one e₀) kcx = begin
  (CX01 • ε) • CX01    ≈⟨ by-assoc Eq.refl ⟩
  CX01 • CX01          ≈⟨ CX01² ⟩
  ε                    ≈⟨ by-assoc Eq.refl ⟩
  ε • ε                ∎
  where open Width (₁₊ n)
nw-sound (one (cx u)) kcx = glue (s u) (comm-CX01 (s u)) N1b
nw-sound (one (sw u)) kcx = glue (s u) (comm-CX01 (s u)) N1a

push-sound : (u : SOne (₁₊ n)) (k : Word (KLet (₁₊ n))) →
             (₁₊ n) ⊢ s₁ u • ⟪ k ⟫ ≈ proj₁ (push u k) ↑ • s₁ (proj₂ (push u k))
push-sound u [ k ]ʷ = nw-sound u k
push-sound {n} u ε = trans right-unit (sym left-unit)
  where open Width (₁₊ n)
push-sound {n} u (w • v) = begin
  s₁ u • ⟪ w ⟫ • ⟪ v ⟫                ≈⟨ sym assoc ⟩
  (s₁ u • ⟪ w ⟫) • ⟪ v ⟫              ≈⟨ front _ (push-sound u w) ⟩
  (W₁ ↑ • s₁ u₁) • ⟪ v ⟫              ≈⟨ assoc ⟩
  W₁ ↑ • s₁ u₁ • ⟪ v ⟫                ≈⟨ back _ (push-sound u₁ v) ⟩
  W₁ ↑ • W₂ ↑ • s₁ u₂                 ≈⟨ sym assoc ⟩
  (W₁ • W₂) ↑ • s₁ u₂                 ∎
  where
  open Width (₁₊ n)
  W₁ = proj₁ (push u w)
  u₁ = proj₂ (push u w)
  W₂ = proj₁ (push u₁ v)
  u₂ = proj₂ (push u₁ v)

------------------------------------------------------------------------
-- The normal form of a linear circuit

record LNF (n : ℕ) : Set where
  constructor ⟨_,_,_⟩
  field
    upper : Circuit n
    col   : SOne (₁₊ n)
    row   : NZ (₁₊ n)

⌜_⌝ : LNF n → Circuit (₁₊ n)
⌜ ⟨ W , u , ℓ ⟩ ⌝ = W ↑ • s₁ u • r ℓ

step : LNF n → LGen (₁₊ n) → LNF n
step ⟨ W , u , ℓ ⟩ y =
  ⟨ W • proj₁ (push u (rk ℓ y)) , proj₂ (push u (rk ℓ y)) , ℓ ⋆ y ⟩

step-sound : (N : LNF n) (y : LGen (₁₊ n)) →
             (₁₊ n) ⊢ ⌜ N ⌝ • [ ι y ]ʷ ≈ ⌜ step N y ⌝
step-sound {n} ⟨ W , u , ℓ ⟩ y = begin
  (W ↑ • s₁ u • r ℓ) • [ ι y ]ʷ            ≈⟨ assoc ⟩
  W ↑ • (s₁ u • r ℓ) • [ ι y ]ʷ            ≈⟨ back _ assoc ⟩
  W ↑ • s₁ u • r ℓ • [ ι y ]ʷ              ≈⟨ back _ (back _ (r-step ℓ y)) ⟩
  W ↑ • s₁ u • ⟪ rk ℓ y ⟫ • r (ℓ ⋆ y)      ≈⟨ back _ (sym assoc) ⟩
  W ↑ • (s₁ u • ⟪ rk ℓ y ⟫) • r (ℓ ⋆ y)    ≈⟨ back _ (front _ (push-sound u (rk ℓ y))) ⟩
  W ↑ • (W' ↑ • s₁ u') • r (ℓ ⋆ y)         ≈⟨ back _ assoc ⟩
  W ↑ • W' ↑ • s₁ u' • r (ℓ ⋆ y)           ≈⟨ sym assoc ⟩
  (W • W') ↑ • s₁ u' • r (ℓ ⋆ y)           ∎
  where
  open Width (₁₊ n)
  W' = proj₁ (push u (rk ℓ y))
  u' = proj₂ (push u (rk ℓ y))

run : LNF n → Word (LGen (₁₊ n)) → LNF n
run N [ y ]ʷ  = step N y
run N ε       = N
run N (w • v) = run (run N w) v

run-sound : (N : LNF n) (L : Word (LGen (₁₊ n))) →
            (₁₊ n) ⊢ ⌜ N ⌝ • ⌊ L ⌋ ≈ ⌜ run N L ⌝
run-sound N [ y ]ʷ = step-sound N y
run-sound {n} N ε = right-unit
  where open Width (₁₊ n)
run-sound {n} N (w • v) = begin
  ⌜ N ⌝ • ⌊ w ⌋ • ⌊ v ⌋          ≈⟨ sym assoc ⟩
  (⌜ N ⌝ • ⌊ w ⌋) • ⌊ v ⌋        ≈⟨ front _ (run-sound N w) ⟩
  ⌜ run N w ⌝ • ⌊ v ⌋            ≈⟨ run-sound (run N w) v ⟩
  ⌜ run (run N w) v ⌝            ∎
  where open Width (₁₊ n)

-- The normal form of the empty circuit, and of any linear circuit.
nf₀ : LNF n
nf₀ = ⟨ ε , one₀ , e₀ ⟩

lnf : Word (LGen (₁₊ n)) → LNF n
lnf = run nf₀

decompose : (L : Word (LGen (₁₊ n))) → (₁₊ n) ⊢ ⌊ L ⌋ ≈ ⌜ lnf L ⌝
decompose {n} L = begin
  ⌊ L ⌋                ≈⟨ sym left-unit ⟩
  ε • ⌊ L ⌋            ≈⟨ front _ (by-assoc Eq.refl) ⟩
  ⌜ nf₀ ⌝ • ⌊ L ⌋      ≈⟨ run-sound nf₀ L ⟩
  ⌜ run nf₀ L ⌝        ∎
  where open Width (₁₊ n)
