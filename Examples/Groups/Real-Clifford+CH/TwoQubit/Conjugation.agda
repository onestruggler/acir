------------------------------------------------------------------------
-- Presentations of groups
--
-- Conjugation by involutions on two wires: negating a control, and
-- swapping the wires
--
-- The equations of Clément's Appendix B come in families: an equation
-- between controlled gates has a form with the control negated
-- (conjugate by X on the control wire) and a form with the wires
-- exchanged (conjugate by the swap).  Both conjugations are
-- involutions that distribute over products, and they act on the
-- shortcuts of Figure 3 by renaming — many of the shortcuts ARE such
-- conjugates by definition.  This module sets up the three
-- conjugations and their action on the shortcuts, so that Auxiliary
-- can obtain each family from one member.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₀ ; ₁₊ ; ₂₊ ; ₃₊)

import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open import Examples.Groups.Real-Clifford+CH.Syntactics

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Tools

module Tools {X : Set} (Γ : WRel X) where
  open PB Γ public
    using (_≈_ ; refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit ; axiom)
  open PP Γ public using (word-setoid ; by-assoc)
  open PP.Pattern-Assoc Γ public using (by-passoc ; □)
  open SR word-setoid public

  front : ∀ {a b} (s : Word X) → a ≈ b → a • s ≈ b • s
  front s e = cong e refl

  back : ∀ (p : Word X) {a b} → a ≈ b → p • a ≈ p • b
  back p e = cong refl e

  mid : ∀ (p : Word X) {a b} (s : Word X) → a ≈ b → p • a • s ≈ p • b • s
  mid p s e = cong refl (cong e refl)

  -- Cancelling an involution c (c • c ≈ ε) at either end.
  cancelˡ : ∀ {c} (s : Word X) → c • c ≈ ε → c • c • s ≈ s
  cancelˡ s e = trans (sym assoc) (trans (front s e) left-unit)

  cancelʳ : ∀ (p : Word X) {c} → c • c ≈ ε → (p • c) • c ≈ p
  cancelʳ p e = trans assoc (trans (back p e) right-unit)

  insertˡ : ∀ {c} (s : Word X) → c • c ≈ ε → s ≈ c • c • s
  insertˡ s e = sym (cancelˡ s e)

  insertʳ : ∀ (p : Word X) {c} → c • c ≈ ε → p ≈ (p • c) • c
  insertʳ p e = sym (cancelʳ p e)

  -- Moving an involution across an equation: from c • a ≈ b, a ≈ c • b.
  moveˡ : ∀ {c a b} → c • c ≈ ε → c • a ≈ b → a ≈ c • b
  moveˡ {c} {a} {b} e h = trans (insertˡ a e) (back c h)

  moveʳ : ∀ {c a b} → c • c ≈ ε → a • c ≈ b → a ≈ b • c
  moveʳ {c} {a} {b} e h = trans (insertʳ a e) (front c h)

  -- Cancelling a pair in the middle, or at the end.
  cancelᵐ : ∀ (p : Word X) {c} (s : Word X) → c • c ≈ ε → p • (c • c) • s ≈ p • s
  cancelᵐ p s e = trans (mid p s e) (back p left-unit)

  cancelᵉ : ∀ (p : Word X) {c} → c • c ≈ ε → p • (c • c) ≈ p
  cancelᵉ p e = trans (back p e) right-unit

  cancelˢ : ∀ {c} (s : Word X) → c • c ≈ ε → (c • c) • s ≈ s
  cancelˢ s e = trans (front s e) left-unit

  -- Undoing a conjugation by an involution.
  unconj : ∀ {c w} → c • c ≈ ε → c • (c • w • c) • c ≈ w
  unconj {c} {w} e = begin
    c • (c • w • c) • c
      ≈⟨ by-passoc (□ • ((□ • (□ • □)) • □)) ((□ • □) • (□ • (□ • □))) Eq.refl ⟩
    (c • c) • w • (c • c)
      ≈⟨ cong e (back _ e) ⟩
    ε • w • ε
      ≈⟨ trans left-unit right-unit ⟩
    w ∎

  -- Conjugation by an involution is symmetric, and a conjugation
  -- equation is a commutation equation.
  conj-sym : ∀ {x w w′} → x • x ≈ ε → x • w • x ≈ w′ → x • w′ • x ≈ w
  conj-sym e h = trans (mid _ _ (sym h)) (unconj e)

  conj-comm : ∀ {x w w′} → x • x ≈ ε → x • w • x ≈ w′ → w • x ≈ x • w′
  conj-comm e h = trans (insertˡ _ e) (back _ h)

  -- A conjugate of an involution is an involution.
  conj-invol : ∀ {c w} → c • c ≈ ε → w • w ≈ ε → (c • w • c) • (c • w • c) ≈ ε
  conj-invol {c} {w} e h = begin
    (c • w • c) • (c • w • c)
      ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
    c • w • (c • c) • w • c
      ≈⟨ back _ (back _ (front _ e)) ⟩
    c • w • ε • w • c
      ≈⟨ back _ (back _ left-unit) ⟩
    c • w • w • c
      ≈⟨ by-passoc (□ • □ • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
    c • (w • w) • c
      ≈⟨ mid _ _ h ⟩
    c • ε • c
      ≈⟨ back _ left-unit ⟩
    c • c
      ≈⟨ e ⟩
    ε ∎

-- A rule of Figure 4 as an equation.
ax : ∀ {k} {w v : Circuit k} → k SRel, w === v → k ⊢ w ≈ v
ax r = PB.axiom (srel r)

------------------------------------------------------------------------
-- One wire: the shortcuts X and Z° are involutions

H² : (₁₊ n) ⊢ H • H ≈ ε
H² = ax order-H

Z² : (₁₊ n) ⊢ Z • Z ≈ ε
Z² = ax order-Z

-- (81)
X² : (₁₊ n) ⊢ X • X ≈ ε
X² {n} = begin
  (H • Z • H) • (H • Z • H)   ≈⟨ by-assoc Eq.refl ⟩
  H • Z • (H • H) • Z • H     ≈⟨ back _ (back _ (front _ H²)) ⟩
  H • Z • ε • Z • H           ≈⟨ by-assoc Eq.refl ⟩
  H • (Z • Z) • H             ≈⟨ back _ (front _ Z²) ⟩
  H • ε • H                   ≈⟨ by-assoc Eq.refl ⟩
  H • H                       ≈⟨ H² ⟩
  ε                           ∎
  where open Tools ((₁₊ n) VRel,_===_)

Z°² : (₁₊ n) ⊢ Z° • Z° ≈ ε
Z°² {n} = conj-invol X² Z²
  where open Tools ((₁₊ n) VRel,_===_)

-- The same on the upper wire.
H²↑ : (₂₊ n) ⊢ H ↑ • H ↑ ≈ ε
H²↑ = lemma-cong↑ (H • H) ε H²

Z²↑ : (₂₊ n) ⊢ Z ↑ • Z ↑ ≈ ε
Z²↑ = lemma-cong↑ (Z • Z) ε Z²

X²↑ : (₂₊ n) ⊢ X ↑ • X ↑ ≈ ε
X²↑ = lemma-cong↑ (X • X) ε X²

Z°²↑ : (₂₊ n) ⊢ Z° ↑ • Z° ↑ ≈ ε
Z°²↑ = lemma-cong↑ (Z° • Z°) ε Z°²

CZ² : (₂₊ n) ⊢ CZ • CZ ≈ ε
CZ² = ax order-CZ

CH² : (₂₊ n) ⊢ CH • CH ≈ ε
CH² = ax order-CH

------------------------------------------------------------------------
-- A one-wire circuit on wire 0 commutes with a shifted circuit

comm-↓↑ : (w : Circuit 1) (v : Circuit (₁₊ n)) →
          (₂₊ n) ⊢ (w ↓ᵏ (₁₊ n)) • v ↑ ≈ v ↑ • (w ↓ᵏ (₁₊ n))
comm-↓↑ [ gate₀ () ]ʷ v
comm-↓↑ [ gate₀ () ↥ ]ʷ v
comm-↓↑ {n} [ gate₁ h ]ʷ v = sym (comm-gate₁-w↑ h v)
  where open Tools ((₂₊ n) VRel,_===_)
comm-↓↑ {n} ε v = trans left-unit (sym right-unit)
  where open Tools ((₂₊ n) VRel,_===_)
comm-↓↑ {n} (w • u) v = begin
  ((w ↓ᵏ (₁₊ n)) • (u ↓ᵏ (₁₊ n))) • v ↑     ≈⟨ assoc ⟩
  (w ↓ᵏ (₁₊ n)) • ((u ↓ᵏ (₁₊ n)) • v ↑)     ≈⟨ back _ (comm-↓↑ u v) ⟩
  (w ↓ᵏ (₁₊ n)) • (v ↑ • (u ↓ᵏ (₁₊ n)))     ≈⟨ sym assoc ⟩
  ((w ↓ᵏ (₁₊ n)) • v ↑) • (u ↓ᵏ (₁₊ n))     ≈⟨ front _ (comm-↓↑ w v) ⟩
  (v ↑ • (w ↓ᵏ (₁₊ n))) • (u ↓ᵏ (₁₊ n))     ≈⟨ assoc ⟩
  v ↑ • ((w ↓ᵏ (₁₊ n)) • (u ↓ᵏ (₁₊ n)))     ∎
  where open Tools ((₂₊ n) VRel,_===_)

-- The instances used.
X↓-X↑ : (₂₊ n) ⊢ X ↓ • X ↑ ≈ X ↑ • X ↓
X↓-X↑ = comm-↓↑ X X

X↓-H↑ : (₂₊ n) ⊢ X ↓ • H ↑ ≈ H ↑ • X ↓
X↓-H↑ = comm-↓↑ X H

X↓-Z↑ : (₂₊ n) ⊢ X ↓ • Z ↑ ≈ Z ↑ • X ↓
X↓-Z↑ = comm-↓↑ X Z

X↓-Z°↑ : (₂₊ n) ⊢ X ↓ • Z° ↑ ≈ Z° ↑ • X ↓
X↓-Z°↑ = comm-↓↑ X Z°

H↓-X↑ : (₂₊ n) ⊢ H ↓ • X ↑ ≈ X ↑ • H ↓
H↓-X↑ = comm-↓↑ H X

H↓-H↑ : (₂₊ n) ⊢ H ↓ • H ↑ ≈ H ↑ • H ↓
H↓-H↑ = comm-↓↑ H H

H↓-Z↑ : (₂₊ n) ⊢ H ↓ • Z ↑ ≈ Z ↑ • H ↓
H↓-Z↑ = comm-↓↑ H Z

H↓-Z°↑ : (₂₊ n) ⊢ H ↓ • Z° ↑ ≈ Z° ↑ • H ↓
H↓-Z°↑ = comm-↓↑ H Z°

Z↓-X↑ : (₂₊ n) ⊢ Z ↓ • X ↑ ≈ X ↑ • Z ↓
Z↓-X↑ = comm-↓↑ Z X

Z↓-H↑ : (₂₊ n) ⊢ Z ↓ • H ↑ ≈ H ↑ • Z ↓
Z↓-H↑ = comm-↓↑ Z H

Z°↓-X↑ : (₂₊ n) ⊢ Z° ↓ • X ↑ ≈ X ↑ • Z° ↓
Z°↓-X↑ = comm-↓↑ Z° X

------------------------------------------------------------------------
-- The swap moves gates between the wires (the swap rules, and X = HZH)

Ex² : (₂₊ n) ⊢ Ex • Ex ≈ ε
Ex² = ax swap-order

-- From w ↑ • Ex ≈ Ex • w ↓ (the rules): Ex • w ↑ ≈ w ↓ • Ex.
private
  flip-swap : ∀ {a b : Circuit (₂₊ n)} →
              (₂₊ n) ⊢ a • Ex ≈ Ex • b → (₂₊ n) ⊢ Ex • a ≈ b • Ex
  flip-swap {n} {a} {b} e = begin
    Ex • a                  ≈⟨ insertʳ _ Ex² ⟩
    ((Ex • a) • Ex) • Ex    ≈⟨ by-passoc (((□ • □) • □) • □) (□ • ((□ • □) • □)) Eq.refl ⟩
    Ex • (a • Ex) • Ex      ≈⟨ mid _ _ e ⟩
    Ex • (Ex • b) • Ex      ≈⟨ by-passoc (□ • ((□ • □) • □)) ((□ • □) • (□ • □)) Eq.refl ⟩
    (Ex • Ex) • b • Ex      ≈⟨ front _ Ex² ⟩
    ε • b • Ex              ≈⟨ left-unit ⟩
    b • Ex                  ∎
    where open Tools ((₂₊ n) VRel,_===_)

H↑-Ex : (₂₊ n) ⊢ H ↑ • Ex ≈ Ex • H ↓
H↑-Ex = ax swap-H

Z↑-Ex : (₂₊ n) ⊢ Z ↑ • Ex ≈ Ex • Z ↓
Z↑-Ex = ax swap-Z

Ex-H↑ : (₂₊ n) ⊢ Ex • H ↑ ≈ H ↓ • Ex
Ex-H↑ = flip-swap H↑-Ex

Ex-Z↑ : (₂₊ n) ⊢ Ex • Z ↑ ≈ Z ↓ • Ex
Ex-Z↑ = flip-swap Z↑-Ex

Ex-H↓ : (₂₊ n) ⊢ Ex • H ↓ ≈ H ↑ • Ex
Ex-H↓ {n} = sym H↑-Ex
  where open Tools ((₂₊ n) VRel,_===_)

Ex-Z↓ : (₂₊ n) ⊢ Ex • Z ↓ ≈ Z ↑ • Ex
Ex-Z↓ {n} = sym Z↑-Ex
  where open Tools ((₂₊ n) VRel,_===_)

H↓-Ex : (₂₊ n) ⊢ H ↓ • Ex ≈ Ex • H ↑
H↓-Ex {n} = sym Ex-H↑
  where open Tools ((₂₊ n) VRel,_===_)

Z↓-Ex : (₂₊ n) ⊢ Z ↓ • Ex ≈ Ex • Z ↑
Z↓-Ex {n} = sym Ex-Z↑
  where open Tools ((₂₊ n) VRel,_===_)

X↑-Ex : (₂₊ n) ⊢ X ↑ • Ex ≈ Ex • X ↓
X↑-Ex {n} = begin
  (H ↑ • Z ↑ • H ↑) • Ex     ≈⟨ by-assoc Eq.refl ⟩
  H ↑ • Z ↑ • (H ↑ • Ex)     ≈⟨ back _ (back _ H↑-Ex) ⟩
  H ↑ • Z ↑ • (Ex • H ↓)     ≈⟨ by-assoc Eq.refl ⟩
  H ↑ • (Z ↑ • Ex) • H ↓     ≈⟨ mid _ _ Z↑-Ex ⟩
  H ↑ • (Ex • Z ↓) • H ↓     ≈⟨ by-assoc Eq.refl ⟩
  (H ↑ • Ex) • Z ↓ • H ↓     ≈⟨ front _ H↑-Ex ⟩
  (Ex • H ↓) • Z ↓ • H ↓     ≈⟨ by-assoc Eq.refl ⟩
  Ex • X ↓                   ∎
  where open Tools ((₂₊ n) VRel,_===_)

Ex-X↑ : (₂₊ n) ⊢ Ex • X ↑ ≈ X ↓ • Ex
Ex-X↑ = flip-swap X↑-Ex

Ex-X↓ : (₂₊ n) ⊢ Ex • X ↓ ≈ X ↑ • Ex
Ex-X↓ {n} = sym X↑-Ex
  where open Tools ((₂₊ n) VRel,_===_)

X↓-Ex : (₂₊ n) ⊢ X ↓ • Ex ≈ Ex • X ↑
X↓-Ex {n} = sym Ex-X↑
  where open Tools ((₂₊ n) VRel,_===_)

Ex-CZ : (₂₊ n) ⊢ Ex • CZ ≈ CZ • Ex
Ex-CZ {n} = sym (ax comm-CZ-Ex)
  where open Tools ((₂₊ n) VRel,_===_)

-- The swap followed by X on both wires, in either order.
Ex-XX : (₂₊ n) ⊢ Ex • X ↑ • X ↓ ≈ X ↓ • X ↑ • Ex
Ex-XX {n} = begin
  Ex • X ↑ • X ↓       ≈⟨ sym assoc ⟩
  (Ex • X ↑) • X ↓     ≈⟨ front _ Ex-X↑ ⟩
  (X ↓ • Ex) • X ↓     ≈⟨ assoc ⟩
  X ↓ • (Ex • X ↓)     ≈⟨ back _ Ex-X↓ ⟩
  X ↓ • X ↑ • Ex ∎
  where open Tools ((₂₊ n) VRel,_===_)

-- Conjugating the swap by X on either wire.
N↑-Ex : (₂₊ n) ⊢ X ↑ • Ex • X ↑ ≈ Ex • X ↑ • X ↓
N↑-Ex {n} = begin
  X ↑ • Ex • X ↑       ≈⟨ back _ Ex-X↑ ⟩
  X ↑ • X ↓ • Ex       ≈⟨ sym assoc ⟩
  (X ↑ • X ↓) • Ex     ≈⟨ front _ (sym X↓-X↑) ⟩
  (X ↓ • X ↑) • Ex     ≈⟨ assoc ⟩
  X ↓ • X ↑ • Ex       ≈⟨ sym Ex-XX ⟩
  Ex • X ↑ • X ↓ ∎
  where open Tools ((₂₊ n) VRel,_===_)

N↓-Ex : (₂₊ n) ⊢ X ↓ • Ex • X ↓ ≈ Ex • X ↑ • X ↓
N↓-Ex {n} = trans (sym assoc) (trans (front _ X↓-Ex) assoc)
  where open Tools ((₂₊ n) VRel,_===_)

------------------------------------------------------------------------
-- Conjugation by an involution
--
-- ⟪ w ⟫ = c • w • c distributes over products and is an involution.

module Conj {k : ℕ} (c : Circuit k) (c² : k ⊢ c • c ≈ ε) where
  open Tools (k VRel,_===_)

  ⟪_⟫ : Circuit k → Circuit k
  ⟪ w ⟫ = c • w • c

  conj : Circuit k → Circuit k
  conj = ⟪_⟫

  ⟪⟫-cong : {a b : Circuit k} → a ≈ b → ⟪ a ⟫ ≈ ⟪ b ⟫
  ⟪⟫-cong e = mid _ _ e

  ⟪⟫-ε : ⟪ ε ⟫ ≈ ε
  ⟪⟫-ε = trans (back _ left-unit) c²

  ⟪⟫-• : (a b : Circuit k) → ⟪ a • b ⟫ ≈ ⟪ a ⟫ • ⟪ b ⟫
  ⟪⟫-• a b = begin
    c • (a • b) • c
      ≈⟨ by-passoc (□ • ((□ • □) • □)) (□ • (□ • (□ • □))) Eq.refl ⟩
    c • a • (b • c)
      ≈⟨ back _ (back _ (insertˡ _ c²)) ⟩
    c • a • (c • c • b • c)
      ≈⟨ by-passoc (□ • (□ • (□ • (□ • (□ • □))))) ((□ • (□ • □)) • (□ • (□ • □))) Eq.refl ⟩
    (c • a • c) • (c • b • c)   ∎

  ⟪⟫-⟪⟫ : (w : Circuit k) → ⟪ ⟪ w ⟫ ⟫ ≈ w
  ⟪⟫-⟪⟫ w = unconj c²

  -- A word that commutes with c is fixed.
  ⟪⟫-fix : {w : Circuit k} → c • w ≈ w • c → ⟪ w ⟫ ≈ w
  ⟪⟫-fix {w} e = begin
    c • w • c       ≈⟨ sym assoc ⟩
    (c • w) • c     ≈⟨ front _ e ⟩
    (w • c) • c     ≈⟨ cancelʳ w c² ⟩
    w               ∎

  -- Conversely a fixed word commutes with c.
  ⟪⟫-comm : {w : Circuit k} → ⟪ w ⟫ ≈ w → c • w ≈ w • c
  ⟪⟫-comm {w} e = begin
    c • w             ≈⟨ insertʳ _ c² ⟩
    ((c • w) • c) • c ≈⟨ front _ (trans assoc e) ⟩
    w • c             ∎

  -- A conjugate of an involution is an involution.
  ⟪⟫-invol : {w : Circuit k} → w • w ≈ ε → ⟪ w ⟫ • ⟪ w ⟫ ≈ ε
  ⟪⟫-invol h = conj-invol c² h

  -- Distributing over products, with the factors' images given.
  ⟪⟫-•₂ : {a b a′ b′ : Circuit k} → ⟪ a ⟫ ≈ a′ → ⟪ b ⟫ ≈ b′ →
          ⟪ a • b ⟫ ≈ a′ • b′
  ⟪⟫-•₂ pa pb = trans (⟪⟫-• _ _) (cong pa pb)

  ⟪⟫-•₃ : {a b d a′ b′ d′ : Circuit k} → ⟪ a ⟫ ≈ a′ → ⟪ b ⟫ ≈ b′ → ⟪ d ⟫ ≈ d′ →
          ⟪ a • b • d ⟫ ≈ a′ • b′ • d′
  ⟪⟫-•₃ pa pb pd = ⟪⟫-•₂ pa (⟪⟫-•₂ pb pd)

  ⟪⟫-•₄ : {a b d f a′ b′ d′ f′ : Circuit k} →
          ⟪ a ⟫ ≈ a′ → ⟪ b ⟫ ≈ b′ → ⟪ d ⟫ ≈ d′ → ⟪ f ⟫ ≈ f′ →
          ⟪ a • b • d • f ⟫ ≈ a′ • b′ • d′ • f′
  ⟪⟫-•₄ pa pb pd pf = ⟪⟫-•₂ pa (⟪⟫-•₃ pb pd pf)

  ⟪⟫-•₅ : {a b d f g a′ b′ d′ f′ g′ : Circuit k} →
          ⟪ a ⟫ ≈ a′ → ⟪ b ⟫ ≈ b′ → ⟪ d ⟫ ≈ d′ → ⟪ f ⟫ ≈ f′ → ⟪ g ⟫ ≈ g′ →
          ⟪ a • b • d • f • g ⟫ ≈ a′ • b′ • d′ • f′ • g′
  ⟪⟫-•₅ pa pb pd pf pg = ⟪⟫-•₂ pa (⟪⟫-•₄ pb pd pf pg)

  ⟪⟫-•₆ : {a b d f g h a′ b′ d′ f′ g′ h′ : Circuit k} →
          ⟪ a ⟫ ≈ a′ → ⟪ b ⟫ ≈ b′ → ⟪ d ⟫ ≈ d′ → ⟪ f ⟫ ≈ f′ → ⟪ g ⟫ ≈ g′ →
          ⟪ h ⟫ ≈ h′ →
          ⟪ a • b • d • f • g • h ⟫ ≈ a′ • b′ • d′ • f′ • g′ • h′
  ⟪⟫-•₆ pa pb pd pf pg ph = ⟪⟫-•₂ pa (⟪⟫-•₅ pb pd pf pg ph)

  ⟪⟫-•₇ : {a b d f g h i a′ b′ d′ f′ g′ h′ i′ : Circuit k} →
          ⟪ a ⟫ ≈ a′ → ⟪ b ⟫ ≈ b′ → ⟪ d ⟫ ≈ d′ → ⟪ f ⟫ ≈ f′ → ⟪ g ⟫ ≈ g′ →
          ⟪ h ⟫ ≈ h′ → ⟪ i ⟫ ≈ i′ →
          ⟪ a • b • d • f • g • h • i ⟫ ≈ a′ • b′ • d′ • f′ • g′ • h′ • i′
  ⟪⟫-•₇ pa pb pd pf pg ph pi = ⟪⟫-•₂ pa (⟪⟫-•₆ pb pd pf pg ph pi)

  ⟪⟫-•₈ : {a b d f g h i j a′ b′ d′ f′ g′ h′ i′ j′ : Circuit k} →
          ⟪ a ⟫ ≈ a′ → ⟪ b ⟫ ≈ b′ → ⟪ d ⟫ ≈ d′ → ⟪ f ⟫ ≈ f′ → ⟪ g ⟫ ≈ g′ →
          ⟪ h ⟫ ≈ h′ → ⟪ i ⟫ ≈ i′ → ⟪ j ⟫ ≈ j′ →
          ⟪ a • b • d • f • g • h • i • j ⟫ ≈ a′ • b′ • d′ • f′ • g′ • h′ • i′ • j′
  ⟪⟫-•₈ pa pb pd pf pg ph pi pj = ⟪⟫-•₂ pa (⟪⟫-•₇ pb pd pf pg ph pi pj)

  -- Transporting an equation along the conjugation.
  ⟪⟫-≈ : {a b a′ b′ : Circuit k} → a ≈ b → ⟪ a ⟫ ≈ a′ → ⟪ b ⟫ ≈ b′ → a′ ≈ b′
  ⟪⟫-≈ e ea eb = trans (sym ea) (trans (⟪⟫-cong e) eb)

  -- Conjugating one side: from a ≈ b, ⟪ a ⟫ ≈ … given ⟪ b ⟫ ≈ b′.
  ⟪⟫-≈ˡ : {a b b′ : Circuit k} → a ≈ b → ⟪ b ⟫ ≈ b′ → ⟪ a ⟫ ≈ b′
  ⟪⟫-≈ˡ e eb = trans (⟪⟫-cong e) eb

  -- Conjugating by a conjugate: ⟪ a ⟫ • w • ⟪ a ⟫ is ⟪ a • ⟪ w ⟫ • a ⟫.
  ⟪⟫-sandwich : (a w : Circuit k) → ⟪ a ⟫ • w • ⟪ a ⟫ ≈ ⟪ a • ⟪ w ⟫ • a ⟫
  ⟪⟫-sandwich a w =
    by-passoc ((□ • (□ • □)) • (□ • (□ • (□ • □))))
              (□ • ((□ • ((□ • (□ • □)) • □)) • □)) Eq.refl

-- Negating the upper control, negating the lower control, and swapping
-- the wires.
module N↑ {n : ℕ} = Conj {₂₊ n} (X ↑) X²↑
module N↓ {n : ℕ} = Conj {₂₊ n} (X ↓) X²
module S  {n : ℕ} = Conj {₂₊ n} Ex Ex²

------------------------------------------------------------------------
-- How the conjugations act on the gates and shortcuts
--
-- Each lemma reads: conjugating the shortcut on the left gives the
-- shortcut on the right.  Many are the shortcut definitions themselves
-- (°CZ IS X ↑ • CZ • X ↑), and those are `refl` at their use sites.

module _ {n : ℕ} where
  open Tools ((₂₊ n) VRel,_===_)

  -- Negating the upper control.
  N↑-°CZ : X ↑ • °CZ • X ↑ ≈ CZ
  N↑-°CZ = N↑.⟪⟫-⟪⟫ CZ

  N↑-°CH : X ↑ • °CH • X ↑ ≈ CH
  N↑-°CH = N↑.⟪⟫-⟪⟫ CH

  N↑-°CX : X ↑ • °CX • X ↑ ≈ CX
  N↑-°CX = N↑.⟪⟫-⟪⟫ CX

  N↑-X↓ : X ↑ • X ↓ • X ↑ ≈ X ↓
  N↑-X↓ = N↑.⟪⟫-fix (sym X↓-X↑)

  N↑-X↑ : X ↑ • X ↑ • X ↑ ≈ X ↑
  N↑-X↑ = N↑.⟪⟫-fix refl

  N↑-H↓ : X ↑ • H ↓ • X ↑ ≈ H ↓
  N↑-H↓ = N↑.⟪⟫-fix (sym H↓-X↑)

  N↑-Z↓ : X ↑ • Z ↓ • X ↑ ≈ Z ↓
  N↑-Z↓ = N↑.⟪⟫-fix (sym Z↓-X↑)

  N↑-Z°↓ : X ↑ • Z° ↓ • X ↑ ≈ Z° ↓
  N↑-Z°↓ = N↑.⟪⟫-fix (sym Z°↓-X↑)

  N↑-Z°↑ : X ↑ • Z° ↑ • X ↑ ≈ Z ↑
  N↑-Z°↑ = N↑.⟪⟫-⟪⟫ (Z ↑)

  N↑-CZ° : X ↑ • CZ° • X ↑ ≈ °CZ°
  N↑-CZ° = begin
    X ↑ • (X ↓ • CZ • X ↓) • X ↑     ≈⟨ by-assoc Eq.refl ⟩
    (X ↑ • X ↓) • CZ • X ↓ • X ↑     ≈⟨ front _ (sym X↓-X↑) ⟩
    (X ↓ • X ↑) • CZ • X ↓ • X ↑     ≈⟨ by-assoc Eq.refl ⟩
    °CZ°                             ∎

  N↑-°CZ° : X ↑ • °CZ° • X ↑ ≈ CZ°
  N↑-°CZ° = N↑.⟪⟫-≈ (sym N↑-CZ°) refl (N↑.⟪⟫-⟪⟫ CZ°)

  -- X ↓ • w • X ↓ under the negation of the upper control.
  N↑-N↓ : (w : Circuit (₂₊ n)) → X ↑ • (X ↓ • w • X ↓) • X ↑ ≈ X ↓ • (X ↑ • w • X ↑) • X ↓
  N↑-N↓ w = begin
    X ↑ • (X ↓ • w • X ↓) • X ↑
      ≈⟨ by-passoc (□ • ((□ • (□ • □)) • □)) ((□ • □) • (□ • (□ • □))) Eq.refl ⟩
    (X ↑ • X ↓) • w • (X ↓ • X ↑)
      ≈⟨ cong (sym X↓-X↑) (back _ X↓-X↑) ⟩
    (X ↓ • X ↑) • w • (X ↑ • X ↓)
      ≈⟨ by-passoc ((□ • □) • (□ • (□ • □))) (□ • ((□ • (□ • □)) • □)) Eq.refl ⟩
    X ↓ • (X ↑ • w • X ↑) • X ↓ ∎

  -- Negating the lower control.
  N↓-CZ° : X ↓ • CZ° • X ↓ ≈ CZ
  N↓-CZ° = N↓.⟪⟫-⟪⟫ CZ

  N↓-HC° : X ↓ • HC° • X ↓ ≈ HC
  N↓-HC° = N↓.⟪⟫-⟪⟫ HC

  N↓-XC° : X ↓ • XC° • X ↓ ≈ XC
  N↓-XC° = N↓.⟪⟫-⟪⟫ XC

  N↓-X↑ : X ↓ • X ↑ • X ↓ ≈ X ↑
  N↓-X↑ = N↓.⟪⟫-fix X↓-X↑

  N↓-X↓ : X ↓ • X ↓ • X ↓ ≈ X ↓
  N↓-X↓ = N↓.⟪⟫-fix refl

  N↓-H↑ : X ↓ • H ↑ • X ↓ ≈ H ↑
  N↓-H↑ = N↓.⟪⟫-fix X↓-H↑

  N↓-Z↑ : X ↓ • Z ↑ • X ↓ ≈ Z ↑
  N↓-Z↑ = N↓.⟪⟫-fix X↓-Z↑

  N↓-Z°↑ : X ↓ • Z° ↑ • X ↓ ≈ Z° ↑
  N↓-Z°↑ = N↓.⟪⟫-fix X↓-Z°↑

  N↓-Z°↓ : X ↓ • Z° ↓ • X ↓ ≈ Z ↓
  N↓-Z°↓ = N↓.⟪⟫-⟪⟫ (Z ↓)

  N↓-°CZ : X ↓ • °CZ • X ↓ ≈ °CZ°
  N↓-°CZ = begin
    X ↓ • (X ↑ • CZ • X ↑) • X ↓     ≈⟨ by-assoc Eq.refl ⟩
    X ↓ • X ↑ • CZ • (X ↑ • X ↓)     ≈⟨ back _ (back _ (back _ (sym X↓-X↑))) ⟩
    X ↓ • X ↑ • CZ • (X ↓ • X ↑)     ≈⟨ by-assoc Eq.refl ⟩
    °CZ°                             ∎

  N↓-°CZ° : X ↓ • °CZ° • X ↓ ≈ °CZ
  N↓-°CZ° = N↓.⟪⟫-≈ (sym N↓-°CZ) refl (N↓.⟪⟫-⟪⟫ °CZ)

  N↓-N↑ : (w : Circuit (₂₊ n)) → X ↓ • (X ↑ • w • X ↑) • X ↓ ≈ X ↑ • (X ↓ • w • X ↓) • X ↑
  N↓-N↑ w = sym (N↑-N↓ w)

  -- Swapping the wires.
  S-CZ : Ex • CZ • Ex ≈ CZ
  S-CZ = S.⟪⟫-fix Ex-CZ

  S-HC : Ex • HC • Ex ≈ CH
  S-HC = S.⟪⟫-⟪⟫ CH

  S-XC : Ex • XC • Ex ≈ CX
  S-XC = S.⟪⟫-⟪⟫ CX

  S-Ex : Ex • Ex • Ex ≈ Ex
  S-Ex = S.⟪⟫-fix refl

  private
    -- Ex • a • Ex ≈ b from Ex • a ≈ b • Ex.
    S-move : {a b : Circuit (₂₊ n)} → Ex • a ≈ b • Ex → Ex • a • Ex ≈ b
    S-move {a} {b} e = trans (sym assoc) (trans (front _ e) (cancelʳ _ Ex²))

  S-H↓ : Ex • H ↓ • Ex ≈ H ↑
  S-H↓ = S-move Ex-H↓

  S-H↑ : Ex • H ↑ • Ex ≈ H ↓
  S-H↑ = S-move Ex-H↑

  S-Z↓ : Ex • Z ↓ • Ex ≈ Z ↑
  S-Z↓ = S-move Ex-Z↓

  S-Z↑ : Ex • Z ↑ • Ex ≈ Z ↓
  S-Z↑ = S-move Ex-Z↑

  S-X↓ : Ex • X ↓ • Ex ≈ X ↑
  S-X↓ = S-move Ex-X↓

  S-X↑ : Ex • X ↑ • Ex ≈ X ↓
  S-X↑ = S-move Ex-X↑

  S-Z°↓ : Ex • Z° ↓ • Ex ≈ Z° ↑
  S-Z°↓ = S.⟪⟫-•₃ S-X↓ S-Z↓ S-X↓

  S-Z°↑ : Ex • Z° ↑ • Ex ≈ Z° ↓
  S-Z°↑ = S.⟪⟫-•₃ S-X↑ S-Z↑ S-X↑

  -- A negated control swaps to a negated control on the other wire.
  S-°CZ : Ex • °CZ • Ex ≈ CZ°
  S-°CZ = S.⟪⟫-•₃ S-X↑ S-CZ S-X↑

  S-CZ° : Ex • CZ° • Ex ≈ °CZ
  S-CZ° = S.⟪⟫-•₃ S-X↓ S-CZ S-X↓

  S-°CH : Ex • °CH • Ex ≈ HC°
  S-°CH = S.⟪⟫-•₃ S-X↑ refl S-X↑

  S-HC° : Ex • HC° • Ex ≈ °CH
  S-HC° = S.⟪⟫-•₃ S-X↓ S-HC S-X↓

  S-°CX : Ex • °CX • Ex ≈ XC°
  S-°CX = S.⟪⟫-•₃ S-X↑ refl S-X↑

  S-XC° : Ex • XC° • Ex ≈ °CX
  S-XC° = S.⟪⟫-•₃ S-X↓ S-XC S-X↓

  S-°CZ° : Ex • °CZ° • Ex ≈ °CZ°
  S-°CZ° = begin
    Ex • °CZ° • Ex
      ≈⟨ S.⟪⟫-•₅ S-X↓ S-X↑ S-CZ S-X↓ S-X↑ ⟩
    X ↑ • X ↓ • CZ • X ↑ • X ↓
      ≈⟨ by-assoc Eq.refl ⟩
    (X ↑ • X ↓) • CZ • X ↑ • X ↓
      ≈⟨ front _ (sym X↓-X↑) ⟩
    (X ↓ • X ↑) • CZ • X ↑ • X ↓
      ≈⟨ by-assoc Eq.refl ⟩
    X ↓ • X ↑ • CZ • (X ↑ • X ↓)
      ≈⟨ back _ (back _ (back _ (sym X↓-X↑))) ⟩
    X ↓ • X ↑ • CZ • (X ↓ • X ↑)
      ≈⟨ by-assoc Eq.refl ⟩
    °CZ°                                    ∎

  -- Negation on one wire swaps to negation on the other.
  S-N↓ : (w w′ : Circuit (₂₊ n)) → Ex • w • Ex ≈ w′ → Ex • (X ↓ • w • X ↓) • Ex ≈ X ↑ • w′ • X ↑
  S-N↓ w w′ e = S.⟪⟫-•₃ S-X↓ e S-X↓

  S-N↑ : (w w′ : Circuit (₂₊ n)) → Ex • w • Ex ≈ w′ → Ex • (X ↑ • w • X ↑) • Ex ≈ X ↓ • w′ • X ↓
  S-N↑ w w′ e = S.⟪⟫-•₃ S-X↑ e S-X↑
