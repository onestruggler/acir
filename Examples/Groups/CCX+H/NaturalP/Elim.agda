------------------------------------------------------------------------
-- Presentations of groups
--
-- On four or more wires every CCX+H circuit is θ of a CCX+HH circuit
-- followed by H on wire 0 or not (`elim`).
--
-- H on wire i ≥ 1 is HH on the wires i, 0 followed by H on wire 0
-- (`elimg`), and H on wire 0 passes θ of any circuit, turning it into θ
-- of another (`conj-w`): it passes a gate off wire 0, it turns X, CX
-- and CCX on the bottom wires into their conjugates by HH on wire 0
-- and a wire they leave idle — which needs a fourth wire for CCX — it
-- passes HH and it turns the swap into the swap followed by HH.  Every
-- step uses H², the structural rules and the swap's naturality at H.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.NaturalP.Elim where

open import Data.Bool.Base using (Bool ; false ; true ; _xor_)
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)
import Presentation.Base as PB

import Examples.Groups.CCX+HH.NaturalP.Syntactics as P
open import Examples.Groups.CCX+H.NaturalP.Syntactics as NH
  using (Gate ; X-gate ; H-gate ; CX-gate ; SW-gate ; CCX-gate ; X ; H ; CX ; CCX ; HHw)
open import Examples.Groups.CCX+H.NaturalP.Schema
open import Examples.Groups.CCX+H.NaturalP.Theta using (θg ; θ ; θ-↑)

private
  variable
    m n : ℕ

open PB using (refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit ; axiom)

------------------------------------------------------------------------
-- Word algebra

private
  rule : ∀ {w v} → m NH, w === v → m ⊢ w ≈ v
  rule r = axiom (srel (srel (nh r)))

  H² : (₁₊ m) ⊢ H • H ≈ ε
  H² = rule NH.H²

  -- H • H • w is w.
  HHw-cancel : ∀ {w : Circuit (₁₊ m)} → (₁₊ m) ⊢ H • (H • w) ≈ w
  HHw-cancel = trans (sym assoc) (trans (cong H² refl) left-unit)

  -- w • H • H is w.
  wHH-cancel : ∀ {w : Circuit (₁₊ m)} → (₁₊ m) ⊢ (w • H) • H ≈ w
  wHH-cancel = trans assoc (trans (cong refl H²) right-unit)

  H-H↑ : (₂₊ m) ⊢ H ↑ • H ≈ H • H ↑
  H-H↑ = axiom (comm₁ H-gate (gate₁ H-gate))

  -- From a conjugate to a passing equation.
  from-cj : ∀ {a b : Circuit (₁₊ m)} → (₁₊ m) ⊢ H • (a • H) ≈ b → (₁₊ m) ⊢ H • a ≈ b • H
  from-cj e = trans (sym wHH-cancel) (cong (trans assoc e) refl)

  -- Conjugating by H • b, with b an involution passing H and a, is
  -- conjugating by H.
  cj-pair : ∀ {a b : Circuit (₁₊ m)} → (₁₊ m) ⊢ b • b ≈ ε → (₁₊ m) ⊢ b • a ≈ a • b →
            (₁₊ m) ⊢ b • H ≈ H • b → (₁₊ m) ⊢ (H • b) • (a • (H • b)) ≈ H • (a • H)
  cj-pair bb ba bH = trans assoc (cong refl
    (trans (sym assoc) (trans (cong ba refl) (trans assoc (cong refl
    (trans (sym assoc) (trans (cong bH refl) (trans assoc
    (trans (cong refl bb) right-unit)))))))))

  -- s • ((H • c) • s) is H • d when s passes H and s • (c • s) is d.
  peel : ∀ {s c d : Circuit (₁₊ m)} → (₁₊ m) ⊢ s • H ≈ H • s → (₁₊ m) ⊢ s • (c • s) ≈ d →
         (₁₊ m) ⊢ s • ((H • c) • s) ≈ H • d
  peel sH e = trans (cong refl assoc) (trans (sym assoc) (trans (cong sH refl)
    (trans assoc (cong refl e))))

  σHσ : (₂₊ m) ⊢ σ • (H • σ) ≈ H ↑
  σHσ = trans (cong refl (sym-rule (σ-nat₁ H-gate))) (trans (sym assoc)
    (trans (cong σ-invol refl) left-unit))

  -- H ↑ is HH followed by H.
  H↑-HH : (₂₊ m) ⊢ H ↑ ≈ HHw • H
  H↑-HH = sym (trans assoc (trans (cong refl H-H↑) HHw-cancel))

------------------------------------------------------------------------
-- HH on wire 0 and wire 2 or 3

HH₀₂ : P.Circuit (₃₊ n)
HH₀₂ = P.σ P.↑ • P.HH • P.σ P.↑

HH₀₃ : P.Circuit (₄₊ n)
HH₀₃ = P.σ P.↑ P.↑ • HH₀₂ • P.σ P.↑ P.↑

private
  θHH₀₂ : (₃₊ n) ⊢ θ HH₀₂ ≈ H • H ↑ ↑
  θHH₀₂ = trans (cong refl assoc) (trans (sym assoc)
    (trans (cong (axiom (comm₁ H-gate (gate₂ SW-gate))) refl)
    (trans assoc (cong refl (lemma-cong↑ _ _ σHσ)))))

  θHH₀₃ : (₄₊ n) ⊢ θ HH₀₃ ≈ H • H ↑ ↑ ↑
  θHH₀₃ = trans (cong refl (cong θHH₀₂ refl))
    (peel (axiom (comm₁ H-gate (gate₂ SW-gate ↥)))
      (lemma-cong↑ _ _ (lemma-cong↑ _ _ σHσ)))

------------------------------------------------------------------------
-- H on wire 0 passes θ of a circuit

cg : P.Gen (₄₊ n) → P.Circuit (₄₊ n)
cg (P.gate₁ P.X-gate)   = P.HH • P.X • P.HH
cg (P.gate₂ P.CX-gate)  = HH₀₂ • P.CX • HH₀₂
cg (P.gate₂ P.HH-gate)  = P.HH
cg (P.gate₂ P.SW-gate)  = P.σ • P.HH
cg (P.gate₃ P.CCX-gate) = HH₀₃ • P.CCX • HH₀₃
cg (g P.↥)              = [ g P.↥ ]ʷ

cw : P.Circuit (₄₊ n) → P.Circuit (₄₊ n)
cw [ g ]ʷ  = cg g
cw ε       = ε
cw (u • v) = cw u • cw v

private
  H↑↑² : (₃₊ m) ⊢ H ↑ ↑ • H ↑ ↑ ≈ ε
  H↑↑² = lemma-cong↑ _ _ (lemma-cong↑ _ _ H²)

  H↑↑↑² : (₄₊ m) ⊢ H ↑ ↑ ↑ • H ↑ ↑ ↑ ≈ ε
  H↑↑↑² = lemma-cong↑ _ _ H↑↑²

conj-g : (g : P.Gen (₄₊ n)) → (₄₊ n) ⊢ H • θg g ≈ θ (cg g) • H
conj-g (P.gate₁ P.X-gate) = from-cj (sym (trans
  (cj-pair (lemma-cong↑ _ _ H²) (axiom (comm₁ X-gate (gate₁ H-gate))) H-H↑) refl))
conj-g (P.gate₂ P.CX-gate) = from-cj (sym (trans
  (cong θHH₀₂ (cong refl θHH₀₂))
  (cj-pair H↑↑² (axiom (comm₂ CX-gate (gate₁ H-gate)))
    (axiom (comm₁ H-gate (gate₁ H-gate ↥))))))
conj-g (P.gate₂ P.HH-gate) = trans HHw-cancel (sym (trans assoc
  (trans (cong refl H-H↑) HHw-cancel)))
conj-g (P.gate₂ P.SW-gate) = trans (sym-rule (σ-nat₁ H-gate))
  (trans (cong refl H↑-HH) (sym assoc))
conj-g (P.gate₃ P.CCX-gate) = from-cj (sym (trans
  (cong θHH₀₃ (cong refl θHH₀₃))
  (cj-pair H↑↑↑² (axiom (comm₃ CCX-gate (gate₁ H-gate)))
    (axiom (comm₁ H-gate (gate₁ H-gate ↥ ↥))))))
conj-g (g P.↥) = sym (comm-gate₁-w↑ H-gate (θg g))

conj-w : (u : P.Circuit (₄₊ n)) → (₄₊ n) ⊢ H • θ u ≈ θ (cw u) • H
conj-w [ g ]ʷ  = conj-g g
conj-w ε       = trans right-unit (sym left-unit)
conj-w (u • v) = trans (sym assoc) (trans (cong (conj-w u) refl) (trans assoc
  (trans (cong refl (conj-w v)) (sym assoc))))

------------------------------------------------------------------------
-- H on wire 0, or not

Hp : Bool → Circuit (₁₊ m)
Hp false = ε
Hp true  = H

cwp : Bool → P.Circuit (₄₊ n) → P.Circuit (₄₊ n)
cwp false u = u
cwp true  u = cw u

conj-p : ∀ p (u : P.Circuit (₄₊ n)) → (₄₊ n) ⊢ Hp p • θ u ≈ θ (cwp p u) • Hp p
conj-p false u = trans left-unit (sym right-unit)
conj-p true  u = conj-w u

Hp-xor : ∀ p q → (₁₊ m) ⊢ Hp p • Hp q ≈ Hp (p xor q)
Hp-xor false q     = left-unit
Hp-xor true  false = right-unit
Hp-xor true  true  = H²

------------------------------------------------------------------------
-- Elimination

record Elim (w : Circuit (₁₊ m)) : Set where
  constructor elim′
  field
    u  : P.Circuit (₁₊ m)
    p  : Bool
    eq : (₁₊ m) ⊢ w ≈ θ u • Hp p

open Elim public

private
  shift : ∀ {g : Gen (₁₊ m)} → Elim [ g ]ʷ → Elim [ g ↥ ]ʷ
  shift (elim′ u false e) = elim′ (u P.↑) false
    (Eq.subst (λ t → _ ⊢ [ _ ]ʷ ≈ t • ε) (Eq.sym (θ-↑ u)) (lemma-cong↑ _ _ e))
  shift (elim′ u true e) = elim′ (u P.↑ • P.HH) true
    (Eq.subst (λ t → _ ⊢ [ _ ]ʷ ≈ (t • HHw) • H) (Eq.sym (θ-↑ u))
      (trans (lemma-cong↑ _ _ e) (trans (cong refl H↑-HH) (sym assoc))))

elimg : (g : Gen (₁₊ m)) → Elim [ g ]ʷ
elimg (gate₁ X-gate)   = elim′ P.X false (sym right-unit)
elimg (gate₁ H-gate)   = elim′ ε true (sym left-unit)
elimg (gate₂ CX-gate)  = elim′ P.CX false (sym right-unit)
elimg (gate₂ SW-gate)  = elim′ P.σ false (sym right-unit)
elimg (gate₃ CCX-gate) = elim′ P.CCX false (sym right-unit)
elimg (_↥ {zero} (gate₀ ()))
elimg (_↥ {suc m} g)   = shift (elimg g)

elim : (w : Circuit (₄₊ n)) → Elim w
elim [ g ]ʷ  = elimg g
elim ε       = elim′ ε false (sym left-unit)
elim (w • v) with elim w | elim v
... | elim′ a p e | elim′ b q f = elim′ (a • cwp p b) (p xor q)
  (trans (cong e f) (trans assoc (trans (cong refl (trans (sym assoc)
    (trans (cong (conj-p p b) refl) assoc)))
    (trans (sym assoc) (cong refl (Hp-xor p q))))))
