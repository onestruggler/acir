------------------------------------------------------------------------
-- Presentations of groups
--
-- Every qutrit Clifford circuit equals a normal form (Lemma 4.2 and
-- Proposition 4.3)
--
-- A generator in front of a normal form N ↑ • M • L is pushed through
-- the Z-normal circuit L (zPush), which turns it into dirty gates an
-- X-normal circuit takes; through the X-normal circuit M (xPush), which
-- leaves gates on the top wires; and those are pushed into N, one wire
-- down (push, by recursion on the width).  At width 0 the scalar −ω
-- meets (−ω)^t.  The identity has a normal form (idNF, the paper's (5),
-- from the equations (4)), so every circuit has one (normalise).  The
-- box relations on at most n qutrits are the argument rs : Rels n.
-- This is Qubit-Clifford's Normalise with the qutrit tables; the
-- X-normal circuit ends in an E and an F box, which absorb the S and the
-- Z that come down the D-ladder.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Qutrit-Clifford.Normalise where

open import Data.Bool.Base using (true)
open import Data.Fin.Base using (Fin ; toℕ)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; map ; concatMap)
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Product.Base using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)
open import Notations

import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Tactics.Words using (module Associative)

open import Examples.Groups.Qutrit-Clifford.Syntactics
open import Examples.Groups.Qutrit-Clifford.Engine using (⟪_⟫ ; ⟪++⟫ ; ⟪≈⟫ ; ⟪map↥⟫)
open import Examples.Groups.Qutrit-Clifford.Axioms
  using (𝕟 ; h₀ ; h₁ ; h₂ ; s₀ ; s₁ ; s₂ ; c₀ ; c₁)
open import Examples.Groups.Qutrit-Clifford.Reasoning
open import Examples.Groups.Qutrit-Clifford.NormalForm
open import Examples.Groups.Qutrit-Clifford.Tables
open import Examples.Groups.Qutrit-Clifford.Rels
open import Examples.Groups.Qutrit-Clifford.Push

open Out
open BoxRelations₁
open BoxRelations₂
open BoxRelations₃

private
  variable
    n m k : ℕ

------------------------------------------------------------------------
-- Generic steps

-- A word that passes the structure unchanged.
passW : {X : Set} {F : X → Circuit n} (x : X) (g : List (Gen n)) (d : List (MIn n)) →
        n ⊢ F x • ⟪ g ⟫ ≈ ⟪ g ⟫ • F x → ⟪ g ⟫ ≡ ⟪ Mls d ⟫ → Out n F (F x • ⟪ g ⟫)
passW {n} x g d e e' = out d x (trans e (front _ (≡⇒≈ e')))
  where open Width n

-- A one-wire letter at the bottom passes a circuit shifted up.
pass↑ : {X : Set} {F : X → Circuit (₂₊ m)} (x : X) (w : Circuit (₁₊ m)) → F x ≡ w ↑ →
        (h : Gate 1) (d : MIn (₂₊ m)) → Ml d ≡ gate₁ h ∷ [] → Out (₂₊ m) F (F x • ⟪ gate₁ h ∷ [] ⟫)
pass↑ {m} {F = F} x w eq h d e = passW x (gate₁ h ∷ []) (d ∷ [])
  (Eq.subst (λ y → (₂₊ m) ⊢ y • ⟪ gate₁ h ∷ [] ⟫ ≈ ⟪ gate₁ h ∷ [] ⟫ • y) (Eq.sym eq)
    (sym (low1s-comm (gate₁ h ∷ []) Eq.refl w)))
  (Eq.cong ⟪_⟫ (Eq.cong (_++ []) (Eq.sym e)))
  where open Width (₂₊ m)

hs : Gate 1 → HS
hs H-gate = gH
hs S-gate = gS

hsM : Gate 1 → MIn (₂₊ m)
hsM H-gate = mH
hsM S-gate = mS

hs-l : (h : Gate 1) → HSl {n = m} (hs h) ≡ gate₁ h ∷ []
hs-l H-gate = Eq.refl
hs-l S-gate = Eq.refl

hsM-l : (h : Gate 1) → Ml {₂₊ m} (hsM h) ≡ gate₁ h ∷ []
hsM-l H-gate = Eq.refl
hsM-l S-gate = Eq.refl

------------------------------------------------------------------------
-- Pushing into Z-normal circuits

upOut : {lhs : Circuit (₂₊ m)} → Out (₂₊ m) (λ (L : Zc (₁₊ m)) → ⟦ L ⟧ᶻ ↑) lhs → Out (₂₊ m) ⟦_⟧ᶻ lhs
upOut (out d L e) = out d (up L) e

-- CZ with an A box on its upper wire.
zAup : Rels (₂₊ m) → (a : AT) (lad : Lad (₁₊ m)) →
       (r : (AT × List Post) ⊎ (AT × BT × List Post)) →
       (₂₊ m) ⊢ ⟪ map _↥ (Al a) ++ c₀ ∷ [] ⟫ ≈ ⟪ Aupr r ⟫ →
       Out (₂₊ m) ⟦_⟧ᶻ (⟦ up (at a lad) ⟧ᶻ • ⟪ c₀ ∷ [] ⟫)
zAup {m = m} rs a lad (inj₁ (a' , ps)) e with pushPost m rs lad ps
... | out d lad' e₂ = out d (up (at a' lad')) (Glue.glue e₁ e₂)
  where
  open Width (₂₊ m)
  e₁ = trans (front _ (sym (⟪↑⟫ (Al a)))) (trans (rule→ e) (back _ (⟪↑⟫ (Al a'))))
zAup {m = m} rs a lad (inj₂ (a' , b , ps)) e with pushPost m rs lad ps
... | out d lad' e₂ = out d (at a' (b ∷ᴮ lad')) (trans (Glue.glue e₁ e₂) (back _ (sym assoc)))
  where
  open Width (₂₊ m)
  e₁ = trans (front _ (sym (⟪↑⟫ (Al a)))) (trans (rule→ e) (back _ (⟪++⟫ (Bl b) (Al a'))))

-- CZ in front of an A box and the B box after it.
zAB : Rels (₂₊ m) → (a : AT) (b : BT) (lad : Lad (₁₊ m)) →
      (r : (AT × BT × List Post) ⊎ (AT × List Post)) →
      (₂₊ m) ⊢ ⟪ Bl b ++ Al a ++ c₀ ∷ [] ⟫ ≈ ⟪ ABr r ⟫ →
      Out (₂₊ m) ⟦_⟧ᶻ (⟦ at a (b ∷ᴮ lad) ⟧ᶻ • ⟪ c₀ ∷ [] ⟫)
zAB {m = m} rs a b lad (inj₁ (a' , b' , ps)) e with pushPost m rs lad ps
... | out d lad' e₂ = out d (at a' (b' ∷ᴮ lad')) (Glue.glue₂ (rule3→ e) e₂)
zAB {m = m} rs a b lad (inj₂ (a' , ps)) e with pushPost m rs lad ps
... | out d lad' e₂ = out d (up (at a' lad')) p
  where
  open Width (₂₊ m)
  e₁ : ⟪ Bl b ⟫ • ⟪ Al a ⟫ • ⟪ c₀ ∷ [] ⟫ ≈ ⟪ Pls ps ⟫ • ⟪ Al a' ⟫ ↑
  e₁ = trans (back _ (sym (⟪++⟫ (Al a) (c₀ ∷ []))))
       (trans (rule→ e) (back _ (⟪↑⟫ (Al a'))))
  p = begin
    ((⟦ lad ⟧ᴸ ↑ • ⟪ Bl b ⟫) • ⟪ Al a ⟫) • ⟪ c₀ ∷ [] ⟫   ≈⟨ trans assoc assoc ⟩
    ⟦ lad ⟧ᴸ ↑ • ⟪ Bl b ⟫ • ⟪ Al a ⟫ • ⟪ c₀ ∷ [] ⟫       ≈⟨ back _ e₁ ⟩
    ⟦ lad ⟧ᴸ ↑ • ⟪ Pls ps ⟫ • ⟪ Al a' ⟫ ↑               ≈⟨ sym assoc ⟩
    (⟦ lad ⟧ᴸ ↑ • ⟪ Pls ps ⟫) • ⟪ Al a' ⟫ ↑             ≈⟨ front _ e₂ ⟩
    (⟪ Mls d ⟫ • ⟦ lad' ⟧ᴸ ↑) • ⟪ Al a' ⟫ ↑            ≈⟨ assoc ⟩
    ⟪ Mls d ⟫ • ⟦ up (at a' lad') ⟧ᶻ                   ∎

-- H or S in front of an A box.
zA : Rels (₁₊ m) → (a : AT) (lad : Lad (₁₊ m)) (h : Gate 1) →
     Out (₁₊ m) ⟦_⟧ᶻ (⟦ at a lad ⟧ᶻ • ⟪ gate₁ h ∷ [] ⟫)
zA {m = m} rs a lad h with ladPushW m rs lad (proj₂ (ruleA a (hs h)))
... | out d lad' e₂ = out d (at (proj₁ (ruleA a (hs h))) lad') (Glue.glue e₁ e₂)
  where
  open Width (₁₊ m)
  e₁ = trans (back _ (≡⇒≈ (Eq.cong ⟪_⟫ (Eq.sym (hs-l h))))) (rule→ (ruleA-ok (rel₁ {m} rs) a (hs h)))

-- A letter above wire 0 passes the A box and enters the ladder.
zUp : Rels (₂₊ m) → (a : AT) (lad : Lad (₂₊ m)) (g : Gen (₁₊ m)) →
      Out (₂₊ m) ⟦_⟧ᶻ (⟦ at a lad ⟧ᶻ • ⟪ g ↥ ∷ [] ⟫)
zUp {m = m} rs a lad g with ladPush (suc m) rs lad (lup g)
... | out d lad' e₂ = out d (at a lad') p
  where
  open Width (₂₊ m)
  p = begin
    (⟦ lad ⟧ᴸ • ⟪ Al a ⟫) • ⟪ g ↥ ∷ [] ⟫     ≈⟨ assoc ⟩
    ⟦ lad ⟧ᴸ • ⟪ Al a ⟫ • ⟪ g ∷ [] ⟫ ↑       ≈⟨ back _ (low1s-comm (Al a) (Al-low1 a) ⟪ g ∷ [] ⟫) ⟩
    ⟦ lad ⟧ᴸ • ⟪ g ∷ [] ⟫ ↑ • ⟪ Al a ⟫       ≈⟨ sym assoc ⟩
    (⟦ lad ⟧ᴸ • ⟪ g ↥ ∷ [] ⟫) • ⟪ Al a ⟫     ≈⟨ front _ e₂ ⟩
    (⟪ Mls d ⟫ • ⟦ lad' ⟧ᴸ) • ⟪ Al a ⟫       ≈⟨ assoc ⟩
    ⟪ Mls d ⟫ • ⟦ at a lad' ⟧ᶻ               ∎

zPush : (m : ℕ) → Rels (₁₊ m) → (L : Zc (₁₊ m)) (g : Gen (₁₊ m)) → Out (₁₊ m) ⟦_⟧ᶻ (⟦ L ⟧ᶻ • ⟪ g ∷ [] ⟫)
zPush (suc m) rs (up L) (g ↥)              = upOut (liftOut (zPush m (down {₁₊ m} rs) L g))
zPush (suc m) rs (up L) (gate₁ h)          = pass↑ (up L) ⟦ L ⟧ᶻ Eq.refl h (hsM h) (hsM-l h)
zPush (suc m) rs (up L) (gate₀ ν-gate)     = scalarOut (up L) _ PB.refl
zPush (suc (suc m)) rs (up (up L)) (gate₂ CZ-gate) =
  passW (up (up L)) (c₀ ∷ []) (mC ∷ []) (PB.sym (low2s-comm (c₀ ∷ []) Eq.refl ⟦ L ⟧ᶻ)) Eq.refl
zPush (suc m) rs (up (at a lad)) (gate₂ CZ-gate) = zAup rs a lad (ruleAup a) (ruleAup-ok (rel₂ {m} rs) a)
zPush m rs (at a lad) (gate₁ h)            = zA rs a lad h
zPush m rs (at a lad) (gate₀ ν-gate)       = scalarOut (at a lad) _ PB.refl
zPush (suc m) rs (at a (b ∷ᴮ lad)) (gate₂ CZ-gate) = zAB rs a b lad (ruleAB a b) (ruleAB-ok (rel₂ {m} rs) a b)
zPush (suc m) rs (at a lad) (g ↥)          = zUp rs a lad g
zPush zero rs (at a lad) (gate₀ ν-gate ↥)  = scalarOut (at a lad) _ ν↑

------------------------------------------------------------------------
-- Pushing into X-normal circuits
--
-- What comes out of a D-ladder is gates on the wires above wire 0,
-- which are done, and S and Z on wire 0 (label 4), which the E and F
-- boxes absorb.

data W4 : Set where
  w4S w4Z : W4

W4l : W4 → List (Gen (₁₊ n))
W4l w4S = s₀ ∷ []
W4l w4Z = Zˡ

W4ls : List W4 → List (Gen (₁₊ n))
W4ls = concatMap W4l

record DOut (m : ℕ) (lhs : Circuit (₁₊ m)) : Set where
  constructor dout
  field
    vs : List (Gen m)
    ws : List W4
    dl : DL (₁₊ m)
    ok : (₁₊ m) ⊢ lhs ≈ ⟪ vs ⟫ ↑ • ⟪ W4ls ws ⟫ • ⟦ dl ⟧ᴰ

-- The outputs of D boxes, sorted.
o2split : List O2 → List (Gen (₁₊ m)) × List W4
o2split []          = [] , []
o2split {m} (oh₁ ∷ os) = h₀ ∷ proj₁ (o2split {m} os) , proj₂ (o2split {m} os)
o2split {m} (os₁ ∷ os) = s₀ ∷ proj₁ (o2split {m} os) , proj₂ (o2split {m} os)
o2split {m} (oS₀ ∷ os) = proj₁ (o2split {m} os) , w4S ∷ proj₂ (o2split {m} os)
o2split {m} (oZ₀ ∷ os) = proj₁ (o2split {m} os) , w4Z ∷ proj₂ (o2split {m} os)
o2split {m} (oν ∷ os)  = 𝕟 ∷ proj₁ (o2split {m} os) , proj₂ (o2split {m} os)

o3split : List O3 → List (Gen (₂₊ m)) × List W4
o3split []          = [] , []
o3split {m} (o3h₁ ∷ os) = h₀ ∷ proj₁ (o3split {m} os) , proj₂ (o3split {m} os)
o3split {m} (o3s₁ ∷ os) = s₀ ∷ proj₁ (o3split {m} os) , proj₂ (o3split {m} os)
o3split {m} (o3h₂ ∷ os) = h₁ ∷ proj₁ (o3split {m} os) , proj₂ (o3split {m} os)
o3split {m} (o3s₂ ∷ os) = s₁ ∷ proj₁ (o3split {m} os) , proj₂ (o3split {m} os)
o3split {m} (o3c₁ ∷ os) = c₀ ∷ proj₁ (o3split {m} os) , proj₂ (o3split {m} os)
o3split {m} (o3S₀ ∷ os) = proj₁ (o3split {m} os) , w4S ∷ proj₂ (o3split {m} os)
o3split {m} (o3Z₀ ∷ os) = proj₁ (o3split {m} os) , w4Z ∷ proj₂ (o3split {m} os)
o3split {m} (o3ν ∷ os)  = 𝕟 ∷ proj₁ (o3split {m} os) , proj₂ (o3split {m} os)

module Split {m : ℕ} where

  open Width (₁₊ m)

  -- The shape the outputs are brought into.
  shape : List (Gen m) × List W4 → Circuit (₁₊ m)
  shape (vs , ws) = ⟪ vs ⟫ ↑ • ⟪ W4ls ws ⟫

  empty : ε ≈ shape ([] , [])
  empty = sym left-unit

  -- A letter above wire 0 joins the gates that are done.
  cons-up : (x : Gen m) (vs : List (Gen m)) (ws : List W4) →
            [ x ↥ ]ʷ • shape (vs , ws) ≈ shape (x ∷ vs , ws)
  cons-up x vs ws = sym assoc

  -- So does the scalar.
  cons-ν : (vs : List (Gen m)) (ws : List W4) → [ 𝕟 ]ʷ • shape (vs , ws) ≈ shape (𝕟 ∷ vs , ws)
  cons-ν vs ws = trans (front _ (sym ν↑)) (cons-up 𝕟 vs ws)

  -- S or Z on wire 0 passes the gates that are done.
  cons-w : (w : W4) (vs : List (Gen m)) (ws : List W4) →
           ⟪ W4l w ⟫ • shape (vs , ws) ≈ shape (vs , w ∷ ws)
  cons-w w vs ws = begin
    ⟪ W4l w ⟫ • ⟪ vs ⟫ ↑ • ⟪ W4ls ws ⟫         ≈⟨ sym assoc ⟩
    (⟪ W4l w ⟫ • ⟪ vs ⟫ ↑) • ⟪ W4ls ws ⟫       ≈⟨ front _ (low1s-comm (W4l w) (low w) ⟪ vs ⟫) ⟩
    (⟪ vs ⟫ ↑ • ⟪ W4l w ⟫) • ⟪ W4ls ws ⟫       ≈⟨ assoc ⟩
    ⟪ vs ⟫ ↑ • ⟪ W4l w ⟫ • ⟪ W4ls ws ⟫         ≈⟨ back _ (sym (⟪++⟫ (W4l w) (W4ls ws))) ⟩
    ⟪ vs ⟫ ↑ • ⟪ W4ls (w ∷ ws) ⟫               ∎
    where
    low : (w : W4) → all low1 (W4l {n = m} w) ≡ true
    low w4S = Eq.refl
    low w4Z = Eq.refl


o2split-ok : (os : List O2) → (₂₊ m) ⊢ ⟪ O2ls os ⟫ ≈ Split.shape (o2split {m} os)
o2split-ok []         = Split.empty
o2split-ok {m} (oh₁ ∷ os) = PB.trans (PB.cong PB.refl (o2split-ok os))
  (Split.cons-up h₀ (proj₁ (o2split {m} os)) (proj₂ (o2split {m} os)))
o2split-ok {m} (os₁ ∷ os) = PB.trans (PB.cong PB.refl (o2split-ok os))
  (Split.cons-up s₀ (proj₁ (o2split {m} os)) (proj₂ (o2split {m} os)))
o2split-ok {m} (oS₀ ∷ os) = PB.trans (PB.cong PB.refl (o2split-ok os))
  (PB.trans (PB.cong (PB.sym PB.right-unit) PB.refl)
    (Split.cons-w w4S (proj₁ (o2split {m} os)) (proj₂ (o2split {m} os))))
o2split-ok {m} (oZ₀ ∷ os) =
  PB.trans (⟪++⟫ Zˡ (O2ls os))
    (PB.trans (PB.cong PB.refl (o2split-ok os))
      (Split.cons-w w4Z (proj₁ (o2split {m} os)) (proj₂ (o2split {m} os))))
o2split-ok {m} (oν ∷ os)  = PB.trans (PB.cong PB.refl (o2split-ok os))
  (Split.cons-ν (proj₁ (o2split {m} os)) (proj₂ (o2split {m} os)))

o3split-ok : (os : List O3) → (₃₊ m) ⊢ ⟪ O3ls os ⟫ ≈ Split.shape (o3split {m} os)
o3split-ok []          = Split.empty
o3split-ok {m} (o3h₁ ∷ os) = PB.trans (PB.cong PB.refl (o3split-ok os))
  (Split.cons-up h₀ (proj₁ (o3split {m} os)) (proj₂ (o3split {m} os)))
o3split-ok {m} (o3s₁ ∷ os) = PB.trans (PB.cong PB.refl (o3split-ok os))
  (Split.cons-up s₀ (proj₁ (o3split {m} os)) (proj₂ (o3split {m} os)))
o3split-ok {m} (o3h₂ ∷ os) = PB.trans (PB.cong PB.refl (o3split-ok os))
  (Split.cons-up h₁ (proj₁ (o3split {m} os)) (proj₂ (o3split {m} os)))
o3split-ok {m} (o3s₂ ∷ os) = PB.trans (PB.cong PB.refl (o3split-ok os))
  (Split.cons-up s₁ (proj₁ (o3split {m} os)) (proj₂ (o3split {m} os)))
o3split-ok {m} (o3c₁ ∷ os) = PB.trans (PB.cong PB.refl (o3split-ok os))
  (Split.cons-up c₀ (proj₁ (o3split {m} os)) (proj₂ (o3split {m} os)))
o3split-ok {m} (o3S₀ ∷ os) = PB.trans (PB.cong PB.refl (o3split-ok os))
  (PB.trans (PB.cong (PB.sym PB.right-unit) PB.refl)
    (Split.cons-w w4S (proj₁ (o3split {m} os)) (proj₂ (o3split {m} os))))
o3split-ok {m} (o3Z₀ ∷ os) =
  PB.trans (⟪++⟫ Zˡ (O3ls os))
    (PB.trans (PB.cong PB.refl (o3split-ok os))
      (Split.cons-w w4Z (proj₁ (o3split {m} os)) (proj₂ (o3split {m} os))))
o3split-ok {m} (o3ν ∷ os)  = PB.trans (PB.cong PB.refl (o3split-ok os))
  (Split.cons-ν (proj₁ (o3split {m} os)) (proj₂ (o3split {m} os)))

module DSteps {m : ℕ} (r₂ : BoxRelations₂) where

  open Width (₂₊ m)

  -- A D box meets S and Z coming down from above.
  dW : (d : DT) (ws : List W4) → ⟪ Dl d ⟫ • ⟪ W4ls ws ⟫ ↑ ≈ ⟪ W4ls ws ⟫ • ⟪ Dl d ⟫
  dW d []       = trans right-unit (sym left-unit)
  dW d (w ∷ ws) = begin
    ⟪ Dl d ⟫ • ⟪ W4l w ++ W4ls ws ⟫ ↑            ≈⟨ back _ (lift (⟪++⟫ (W4l w) (W4ls ws))) ⟩
    ⟪ Dl d ⟫ • ⟪ W4l w ⟫ ↑ • ⟪ W4ls ws ⟫ ↑        ≈⟨ sym assoc ⟩
    (⟪ Dl d ⟫ • ⟪ W4l w ⟫ ↑) • ⟪ W4ls ws ⟫ ↑      ≈⟨ front _ (e w) ⟩
    (⟪ W4l w ⟫ • ⟪ Dl d ⟫) • ⟪ W4ls ws ⟫ ↑        ≈⟨ assoc ⟩
    ⟪ W4l w ⟫ • ⟪ Dl d ⟫ • ⟪ W4ls ws ⟫ ↑          ≈⟨ back _ (dW d ws) ⟩
    ⟪ W4l w ⟫ • ⟪ W4ls ws ⟫ • ⟪ Dl d ⟫            ≈⟨ sym assoc ⟩
    (⟪ W4l w ⟫ • ⟪ W4ls ws ⟫) • ⟪ Dl d ⟫          ≈⟨ front _ (sym (⟪++⟫ (W4l w) (W4ls ws))) ⟩
    ⟪ W4l w ++ W4ls ws ⟫ • ⟪ Dl d ⟫              ∎
    where
    e : (w : W4) → ⟪ Dl d ⟫ • ⟪ W4l w ⟫ ↑ ≈ ⟪ W4l w ⟫ • ⟪ Dl d ⟫
    e w4S = rule→ {xs = Dl d} {gs = s₁ ∷ []} {ys = s₀ ∷ []} {xs' = Dl d} (ruleS1D-ok r₂ d)
    e w4Z = rule→ {xs = Dl d} {gs = map _↥ Zˡ} {ys = Zˡ} {xs' = Dl d} (ruleZ1D-ok r₂ d)

  -- A D box passes what came out of the ladder above.
  slide : (d : DT) (vs : List (Gen m)) (ws : List W4) (r : Circuit (₂₊ m)) →
          ⟪ Dl d ⟫ • ⟪ vs ⟫ ↑ ↑ • ⟪ W4ls ws ⟫ ↑ • r ≈ ⟪ map _↥ vs ⟫ ↑ • ⟪ W4ls ws ⟫ • ⟪ Dl d ⟫ • r
  slide d vs ws r = begin
    ⟪ Dl d ⟫ • ⟪ vs ⟫ ↑ ↑ • ⟪ W4ls ws ⟫ ↑ • r      ≈⟨ swap _ (low2s-comm (Dl d) (Dl-low2 d) ⟪ vs ⟫) ⟩
    ⟪ vs ⟫ ↑ ↑ • ⟪ Dl d ⟫ • ⟪ W4ls ws ⟫ ↑ • r      ≈⟨ back _ (pair _ (dW d ws)) ⟩
    ⟪ vs ⟫ ↑ ↑ • ⟪ W4ls ws ⟫ • ⟪ Dl d ⟫ • r        ≈⟨ front _ (sym (lift (⟪↑⟫ vs))) ⟩
    ⟪ map _↥ vs ⟫ ↑ • ⟪ W4ls ws ⟫ • ⟪ Dl d ⟫ • r   ∎

  -- A D box meets a gate on wire 0, or CZ with nothing above.
  meet : (d d' : DT) (g : List (Gen (₂₊ m))) (os : List O2) (r : Circuit (₂₊ m)) →
         ⟪ Dl d ⟫ • ⟪ g ⟫ ≈ ⟪ O2ls os ⟫ • ⟪ Dl d' ⟫ →
         (⟪ Dl d ⟫ • ⟪ g ⟫) • r ≈ Split.shape (o2split {m} os) • ⟪ Dl d' ⟫ • r
  meet d d' g os r e = trans (front _ (trans e (front _ (o2split-ok os)))) assoc

-- A D box meets a gate that passed the D-ladder above it.
dStep : (m : ℕ) → BoxRelations₂ → (d : DT) (dl : DL (₁₊ m)) (g : List (Gen (₂₊ m))) (d' : DT) (os : List O2) →
        (₂₊ m) ⊢ ⟦ dl ⟧ᴰ ↑ • ⟪ g ⟫ ≈ ⟪ g ⟫ • ⟦ dl ⟧ᴰ ↑ →
        (₂₊ m) ⊢ ⟪ Dl d ⟫ • ⟪ g ⟫ ≈ ⟪ O2ls os ⟫ • ⟪ Dl d' ⟫ →
        DOut (suc m) ((⟪ Dl d ⟫ • ⟦ dl ⟧ᴰ ↑) • ⟪ g ⟫)
dStep m r₂ d dl g d' os c e =
  dout (proj₁ (o2split {m} os)) (proj₂ (o2split {m} os)) (d' ∷ᴰ dl) p
  where
  open Width (₂₊ m)
  p = begin
    (⟪ Dl d ⟫ • ⟦ dl ⟧ᴰ ↑) • ⟪ g ⟫           ≈⟨ trans assoc (back _ c) ⟩
    ⟪ Dl d ⟫ • ⟪ g ⟫ • ⟦ dl ⟧ᴰ ↑             ≈⟨ sym assoc ⟩
    (⟪ Dl d ⟫ • ⟪ g ⟫) • ⟦ dl ⟧ᴰ ↑           ≈⟨ DSteps.meet r₂ d d' g os _ e ⟩
    Split.shape (o2split {m} os) • ⟪ Dl d' ⟫ • ⟦ dl ⟧ᴰ ↑   ≈⟨ assoc ⟩
    _ ∎

dPush : (m : ℕ) → Rels (₁₊ m) → (dl : DL (₁₊ m)) (g : MIn (₁₊ m)) → DOut m (⟦ dl ⟧ᴰ • ⟪ Ml g ⟫)
dPush m rs dl mν = dout (𝕟 ∷ []) [] dl
  (trans (back _ right-unit) (trans (sym (ν-comm _))
    (trans (front _ (trans (sym ν↑) (sym right-unit))) (back _ (sym left-unit)))))
  where open Width (₁₊ m)
dPush zero rs []ᴰ mSt = dout [] (w4S ∷ []) []ᴰ (PP.by-assoc (1 VRel,_===_) Eq.refl)
dPush zero rs []ᴰ mZt = dout [] (w4Z ∷ []) []ᴰ (PP.by-assoc (1 VRel,_===_) Eq.refl)
dPush (suc m) rs (d ∷ᴰ dl) (mup g) with dPush m (down {₁₊ m} rs) dl g
... | dout vs ws dl' e = dout (map _↥ vs) ws (d ∷ᴰ dl') p
  where
  open Width (₂₊ m)
  p = begin
    (⟪ Dl d ⟫ • ⟦ dl ⟧ᴰ ↑) • ⟪ map _↥ (Ml g) ⟫        ≈⟨ trans assoc (back _ (back _ (⟪↑⟫ (Ml g)))) ⟩
    ⟪ Dl d ⟫ • (⟦ dl ⟧ᴰ • ⟪ Ml g ⟫) ↑                 ≈⟨ back _ (lift e) ⟩
    ⟪ Dl d ⟫ • (⟪ vs ⟫ ↑ • ⟪ W4ls ws ⟫ • ⟦ dl' ⟧ᴰ) ↑   ≈⟨ DSteps.slide (rel₂ {m} rs) d vs ws _ ⟩
    ⟪ map _↥ vs ⟫ ↑ • ⟪ W4ls ws ⟫ • ⟪ Dl d ⟫ • ⟦ dl' ⟧ᴰ ↑ ∎
dPush (suc m) rs (d ∷ᴰ dl) mH = dStep m (rel₂ {m} rs) d dl (h₀ ∷ []) (proj₁ (ruleD d gH)) (proj₂ (ruleD d gH))
  (PB.sym (low1s-comm (h₀ ∷ []) Eq.refl ⟦ dl ⟧ᴰ))
  (rule→ {xs = Dl d} {gs = h₀ ∷ []} {ys = O2ls (proj₂ (ruleD d gH))} {xs' = Dl (proj₁ (ruleD d gH))}
    (ruleD-ok (rel₂ {m} rs) d gH))
dPush (suc m) rs (d ∷ᴰ dl) mS = dStep m (rel₂ {m} rs) d dl (s₀ ∷ []) (proj₁ (ruleD d gS)) (proj₂ (ruleD d gS))
  (PB.sym (low1s-comm (s₀ ∷ []) Eq.refl ⟦ dl ⟧ᴰ))
  (rule→ {xs = Dl d} {gs = s₀ ∷ []} {ys = O2ls (proj₂ (ruleD d gS))} {xs' = Dl (proj₁ (ruleD d gS))}
    (ruleD-ok (rel₂ {m} rs) d gS))
dPush (suc zero) rs (d ∷ᴰ []ᴰ) mC = dStep zero (rel₂ {0} rs) d []ᴰ (c₀ ∷ []) (proj₁ (ruleCD d)) (proj₂ (ruleCD d))
  (PB.trans PB.left-unit (PB.sym PB.right-unit))
  (rule→ {xs = Dl d} {gs = c₀ ∷ []} {ys = O2ls (proj₂ (ruleCD d))} {xs' = Dl (proj₁ (ruleCD d))}
    (ruleCD-ok (rel₂ {0} rs) d))
dPush (suc (suc m)) rs (d ∷ᴰ d₁ ∷ᴰ dl) mC =
  dout (proj₁ sp) (proj₂ sp) (d₀' ∷ᴰ d₁' ∷ᴰ dl) p
  where
  open Width (₃₊ m)
  r   = ruleDD d₁ d
  d₁' = proj₁ r
  d₀' = proj₁ (proj₂ r)
  os  = proj₂ (proj₂ r)
  sp  = o3split {m} os
  e₃ : ⟪ Dl d ⟫ • ⟪ Dl d₁ ⟫ ↑ • ⟪ c₀ ∷ [] ⟫ ≈ ⟪ O3ls os ⟫ • ⟪ Dl d₀' ⟫ • ⟪ Dl d₁' ⟫ ↑
  e₃ = trans (back _ (front _ (sym (⟪↑⟫ (Dl d₁)))))
       (trans (rule3→ (ruleDD-ok (rel₃ {m} rs) d₁ d)) (back _ (back _ (⟪↑⟫ (Dl d₁')))))
  p = begin
    (⟪ Dl d ⟫ • (⟪ Dl d₁ ⟫ ↑ • ⟦ dl ⟧ᴰ ↑ ↑)) • ⟪ c₀ ∷ [] ⟫      ≈⟨ trans assoc (back _ assoc) ⟩
    ⟪ Dl d ⟫ • ⟪ Dl d₁ ⟫ ↑ • ⟦ dl ⟧ᴰ ↑ ↑ • ⟪ c₀ ∷ [] ⟫          ≈⟨ back _ (back _ (sym (low2s-comm (c₀ ∷ []) Eq.refl ⟦ dl ⟧ᴰ))) ⟩
    ⟪ Dl d ⟫ • ⟪ Dl d₁ ⟫ ↑ • ⟪ c₀ ∷ [] ⟫ • ⟦ dl ⟧ᴰ ↑ ↑          ≈⟨ trans (back _ (sym assoc)) (sym assoc) ⟩
    (⟪ Dl d ⟫ • ⟪ Dl d₁ ⟫ ↑ • ⟪ c₀ ∷ [] ⟫) • ⟦ dl ⟧ᴰ ↑ ↑        ≈⟨ front _ e₃ ⟩
    (⟪ O3ls os ⟫ • ⟪ Dl d₀' ⟫ • ⟪ Dl d₁' ⟫ ↑) • ⟦ dl ⟧ᴰ ↑ ↑    ≈⟨ front _ (front _ (o3split-ok os)) ⟩
    (Split.shape sp • ⟪ Dl d₀' ⟫ • ⟪ Dl d₁' ⟫ ↑) • ⟦ dl ⟧ᴰ ↑ ↑  ≈⟨ trans assoc (trans assoc (back _ (back _ assoc))) ⟩
    _ ∎

-- An X-normal circuit: the E box absorbs the S that comes down, and the
-- F box the Z, which passes the E box.
record XOut (m : ℕ) (lhs : Circuit (₁₊ m)) : Set where
  constructor xout
  field
    vs : List (Gen m)
    M  : Xc (₁₊ m)
    ok : (₁₊ m) ⊢ lhs ≈ ⟪ vs ⟫ ↑ • ⟦ M ⟧ˣ

efrot : List W4 → ET → FT → ET × FT
efrot []          e f = e , f
efrot (w4S ∷ ws) e f = efrot ws (ruleE e) f
efrot (w4Z ∷ ws) e f = efrot ws e (ruleF f)

EF : BoxRelations₁ → (e : ET) (f : FT) (ws : List W4) →
     (₁₊ m) ⊢ ⟪ Fl f ⟫ • ⟪ El e ⟫ • ⟪ W4ls ws ⟫ ≈
              ⟪ Fl (proj₂ (efrot ws e f)) ⟫ • ⟪ El (proj₁ (efrot ws e f)) ⟫
EF {m} r₁ e f [] = back _ right-unit
  where open Width (₁₊ m)
EF {m} r₁ e f (w4S ∷ ws) = begin
  ⟪ Fl f ⟫ • ⟪ El e ⟫ • ⟪ s₀ ∷ [] ++ W4ls ws ⟫        ≈⟨ back _ (back _ (⟪++⟫ (s₀ ∷ []) (W4ls ws))) ⟩
  ⟪ Fl f ⟫ • ⟪ El e ⟫ • ⟪ s₀ ∷ [] ⟫ • ⟪ W4ls ws ⟫     ≈⟨ back _ (sym assoc) ⟩
  ⟪ Fl f ⟫ • (⟪ El e ⟫ • ⟪ s₀ ∷ [] ⟫) • ⟪ W4ls ws ⟫   ≈⟨ back _ (front _ (trans (sym (⟪++⟫ (El e) (s₀ ∷ []))) (ruleE-ok r₁ e))) ⟩
  ⟪ Fl f ⟫ • ⟪ El (ruleE e) ⟫ • ⟪ W4ls ws ⟫           ≈⟨ EF r₁ (ruleE e) f ws ⟩
  _ ∎
  where open Width (₁₊ m)
EF {m} r₁ e f (w4Z ∷ ws) = begin
  ⟪ Fl f ⟫ • ⟪ El e ⟫ • ⟪ Zˡ ++ W4ls ws ⟫              ≈⟨ back _ (back _ (⟪++⟫ Zˡ (W4ls ws))) ⟩
  ⟪ Fl f ⟫ • ⟪ El e ⟫ • ⟪ Zˡ ⟫ • ⟪ W4ls ws ⟫           ≈⟨ back _ (sym assoc) ⟩
  ⟪ Fl f ⟫ • (⟪ El e ⟫ • ⟪ Zˡ ⟫) • ⟪ W4ls ws ⟫         ≈⟨ back _ (front _ (rule→ (ruleEZ-ok r₁ e))) ⟩
  ⟪ Fl f ⟫ • (⟪ Zˡ ⟫ • ⟪ El e ⟫) • ⟪ W4ls ws ⟫         ≈⟨ trans (back _ assoc) (sym assoc) ⟩
  (⟪ Fl f ⟫ • ⟪ Zˡ ⟫) • ⟪ El e ⟫ • ⟪ W4ls ws ⟫         ≈⟨ front _ (trans (sym (⟪++⟫ (Fl f) Zˡ)) (ruleF-ok r₁ f)) ⟩
  ⟪ Fl (ruleF f) ⟫ • ⟪ El e ⟫ • ⟪ W4ls ws ⟫            ≈⟨ EF r₁ e (ruleF f) ws ⟩
  _ ∎
  where open Width (₁₊ m)

xPush : (m : ℕ) → Rels (₁₊ m) → (M : Xc (₁₊ m)) (g : MIn (₁₊ m)) → XOut m (⟦ M ⟧ˣ • ⟪ Ml g ⟫)
xPush m rs (xc e f dl) g with dPush m rs dl g
... | dout vs ws dl' ok = xout vs (xc (proj₁ ef) (proj₂ ef) dl') p
  where
  open Width (₁₊ m)
  ef = efrot ws e f
  p = begin
    (⟪ Fl f ⟫ • ⟪ El e ⟫ • ⟦ dl ⟧ᴰ) • ⟪ Ml g ⟫                     ≈⟨ trans assoc (back _ (trans assoc (back _ ok))) ⟩
    ⟪ Fl f ⟫ • ⟪ El e ⟫ • ⟪ vs ⟫ ↑ • ⟪ W4ls ws ⟫ • ⟦ dl' ⟧ᴰ         ≈⟨ back _ (swap _ (low1s-comm (El e) (El-low1 e) ⟪ vs ⟫)) ⟩
    ⟪ Fl f ⟫ • ⟪ vs ⟫ ↑ • ⟪ El e ⟫ • ⟪ W4ls ws ⟫ • ⟦ dl' ⟧ᴰ         ≈⟨ swap _ (low1s-comm (Fl f) (Fl-low1 f) ⟪ vs ⟫) ⟩
    ⟪ vs ⟫ ↑ • ⟪ Fl f ⟫ • ⟪ El e ⟫ • ⟪ W4ls ws ⟫ • ⟦ dl' ⟧ᴰ         ≈⟨ back _ (trans (back _ (sym assoc)) (sym assoc)) ⟩
    ⟪ vs ⟫ ↑ • (⟪ Fl f ⟫ • ⟪ El e ⟫ • ⟪ W4ls ws ⟫) • ⟦ dl' ⟧ᴰ       ≈⟨ back _ (front _ (EF (rel₁ {m} rs) e f ws)) ⟩
    ⟪ vs ⟫ ↑ • (⟪ Fl (proj₂ ef) ⟫ • ⟪ El (proj₁ ef) ⟫) • ⟦ dl' ⟧ᴰ   ≈⟨ back _ assoc ⟩
    ⟪ vs ⟫ ↑ • ⟦ xc (proj₁ ef) (proj₂ ef) dl' ⟧ˣ                    ∎

xPushL : (m : ℕ) → Rels (₁₊ m) → (M : Xc (₁₊ m)) (ds : List (MIn (₁₊ m))) → XOut m (⟦ M ⟧ˣ • ⟪ Mls ds ⟫)
xPushL m rs M [] = xout [] M (trans right-unit (sym left-unit))
  where open Width (₁₊ m)
xPushL m rs M (d ∷ ds) with xPush m rs M d
... | xout vs₁ M₁ e₁ with xPushL m rs M₁ ds
... | xout vs₂ M₂ e₂ = xout (vs₁ ++ vs₂) M₂ p
  where
  open Width (₁₊ m)
  p = begin
    ⟦ M ⟧ˣ • ⟪ Ml d ++ Mls ds ⟫                 ≈⟨ trans (back _ (⟪++⟫ (Ml d) (Mls ds))) (sym assoc) ⟩
    (⟦ M ⟧ˣ • ⟪ Ml d ⟫) • ⟪ Mls ds ⟫             ≈⟨ front _ e₁ ⟩
    (⟪ vs₁ ⟫ ↑ • ⟦ M₁ ⟧ˣ) • ⟪ Mls ds ⟫           ≈⟨ assoc ⟩
    ⟪ vs₁ ⟫ ↑ • ⟦ M₁ ⟧ˣ • ⟪ Mls ds ⟫             ≈⟨ back _ e₂ ⟩
    ⟪ vs₁ ⟫ ↑ • ⟪ vs₂ ⟫ ↑ • ⟦ M₂ ⟧ˣ              ≈⟨ trans (sym assoc) (front _ (lift (PB.sym (⟪++⟫ vs₁ vs₂)))) ⟩
    ⟪ vs₁ ++ vs₂ ⟫ ↑ • ⟦ M₂ ⟧ˣ                   ∎

------------------------------------------------------------------------
-- Pushing into normal forms

-- The scalar meets (−ω)^t.
inc : Fin 6 → Fin 6
inc ₀ = ₁
inc ₁ = ₂
inc ₂ = ₃
inc ₃ = ₄
inc ₄ = ₅
inc ₅ = ₀

private
  ν-step : (k : ℕ) → 0 ⊢ ν ^ suc k • ν • ε ≈ ν ^ suc (suc k)
  ν-step k = PB.trans (PB.cong PB.refl PB.right-unit) (PB.sym (ν-comm (ν ^ suc k)))

inc-ok : (t : Fin 6) → 0 ⊢ ν ^ toℕ t • ν • ε ≈ ν ^ toℕ (inc t)
inc-ok ₀ = PB.trans PB.left-unit PB.right-unit
inc-ok ₁ = ν-step 0
inc-ok ₂ = ν-step 1
inc-ok ₃ = ν-step 2
inc-ok ₄ = ν-step 3
inc-ok ₅ = PB.trans (ν-step 4) (PB.axiom (srel C₁))

push  : (n : ℕ) → Rels n → (N : NF n) (g : Gen n) → Σ (NF n) λ N' → n ⊢ ⟦ N ⟧ⁿ • ⟪ g ∷ [] ⟫ ≈ ⟦ N' ⟧ⁿ
pushW : (n : ℕ) → Rels n → (N : NF n) (gs : List (Gen n)) → Σ (NF n) λ N' → n ⊢ ⟦ N ⟧ⁿ • ⟪ gs ⟫ ≈ ⟦ N' ⟧ⁿ

push zero rs (nf₀ t) (gate₀ ν-gate) = nf₀ (inc t) , inc-ok t
push (suc m) rs (nfₛ L M N) g with zPush m rs L g
... | out ds L' e₁ with xPushL m rs M ds
... | xout vs M' e₂ with pushW m (down {m} rs) N vs
... | N' , e₃ = nfₛ L' M' N' , p
  where
  open Width (₁₊ m)
  p = begin
    (⟦ N ⟧ⁿ ↑ • ⟦ M ⟧ˣ • ⟦ L ⟧ᶻ) • ⟪ g ∷ [] ⟫          ≈⟨ trans assoc (back _ assoc) ⟩
    ⟦ N ⟧ⁿ ↑ • ⟦ M ⟧ˣ • ⟦ L ⟧ᶻ • ⟪ g ∷ [] ⟫            ≈⟨ back _ (back _ e₁) ⟩
    ⟦ N ⟧ⁿ ↑ • ⟦ M ⟧ˣ • ⟪ Mls ds ⟫ • ⟦ L' ⟧ᶻ          ≈⟨ back _ (sym assoc) ⟩
    ⟦ N ⟧ⁿ ↑ • (⟦ M ⟧ˣ • ⟪ Mls ds ⟫) • ⟦ L' ⟧ᶻ        ≈⟨ back _ (front _ e₂) ⟩
    ⟦ N ⟧ⁿ ↑ • (⟪ vs ⟫ ↑ • ⟦ M' ⟧ˣ) • ⟦ L' ⟧ᶻ         ≈⟨ trans (back _ assoc) (sym assoc) ⟩
    (⟦ N ⟧ⁿ ↑ • ⟪ vs ⟫ ↑) • ⟦ M' ⟧ˣ • ⟦ L' ⟧ᶻ         ≈⟨ front _ (lift e₃) ⟩
    ⟦ N' ⟧ⁿ ↑ • ⟦ M' ⟧ˣ • ⟦ L' ⟧ᶻ                     ∎

pushW n rs N []       = N , PB.right-unit
pushW n rs N (g ∷ gs) with push n rs N g
... | N₁ , e₁ with pushW n rs N₁ gs
... | N₂ , e₂ = N₂ , p
  where
  open Width n
  p = begin
    ⟦ N ⟧ⁿ • [ g ]ʷ • ⟪ gs ⟫                ≈⟨ sym assoc ⟩
    (⟦ N ⟧ⁿ • [ g ]ʷ) • ⟪ gs ⟫              ≈⟨ front _ (trans (back _ (sym right-unit)) e₁) ⟩
    ⟦ N₁ ⟧ⁿ • ⟪ gs ⟫                        ≈⟨ e₂ ⟩
    ⟦ N₂ ⟧ⁿ                                 ∎

------------------------------------------------------------------------
-- The normal form of the identity, and normalisation

lad₀ : (m : ℕ) → Lad (₁₊ m)
lad₀ zero    = top C₀
lad₀ (suc m) = B₀₀ ∷ᴮ lad₀ m

dl₀ : (m : ℕ) → DL (₁₊ m)
dl₀ zero    = []ᴰ
dl₀ (suc m) = D₀₁ ∷ᴰ dl₀ m

idNF : (n : ℕ) → NF n
idNF zero    = nf₀ ₀
idNF (suc m) = nfₛ (at A₀₁ (lad₀ m)) (xc E₀ F₀ (dl₀ m)) (idNF m)

-- D₀₁ undoes B₀₀, the second equation of (4).
D₀₁B₀₀ : BoxRelations₂ → (₂₊ m) ⊢ ⟪ Dl D₀₁ ⟫ • ⟪ Bl B₀₀ ⟫ ≈ ε
D₀₁B₀₀ r₂ = PB.trans (PB.sym (⟪++⟫ (Dl D₀₁) (Bl B₀₀))) (id₂-ok r₂)

dl₀lad₀ : (m : ℕ) → Rels (₁₊ m) → (₁₊ m) ⊢ ⟦ dl₀ m ⟧ᴰ • ⟦ lad₀ m ⟧ᴸ ≈ ε
dl₀lad₀ zero    rs = PB.left-unit
dl₀lad₀ (suc m) rs = begin
  (⟪ Dl D₀₁ ⟫ • ⟦ dl₀ m ⟧ᴰ ↑) • (⟦ lad₀ m ⟧ᴸ ↑ • ⟪ Bl B₀₀ ⟫)   ≈⟨ trans assoc (back _ (sym assoc)) ⟩
  ⟪ Dl D₀₁ ⟫ • (⟦ dl₀ m ⟧ᴰ • ⟦ lad₀ m ⟧ᴸ) ↑ • ⟪ Bl B₀₀ ⟫        ≈⟨ back _ (front _ (lift (dl₀lad₀ m (down {₁₊ m} rs)))) ⟩
  ⟪ Dl D₀₁ ⟫ • ε • ⟪ Bl B₀₀ ⟫                                 ≈⟨ trans (back _ left-unit) (D₀₁B₀₀ (rel₂ {m} rs)) ⟩
  ε                                                           ∎
  where open Width (₂₊ m)

idNF-ok : (n : ℕ) → Rels n → n ⊢ ⟦ idNF n ⟧ⁿ ≈ ε
idNF-ok zero    rs = PB.refl
idNF-ok (suc m) rs = begin
  ⟦ idNF m ⟧ⁿ ↑ • (ε • ε • ⟦ dl₀ m ⟧ᴰ) • (⟦ lad₀ m ⟧ᴸ • ε)   ≈⟨ front _ (lift (idNF-ok m (down {m} rs))) ⟩
  ε • (ε • ε • ⟦ dl₀ m ⟧ᴰ) • (⟦ lad₀ m ⟧ᴸ • ε)              ≈⟨ trans left-unit (trans (front _ (trans left-unit left-unit)) (back _ right-unit)) ⟩
  ⟦ dl₀ m ⟧ᴰ • ⟦ lad₀ m ⟧ᴸ                                  ≈⟨ dl₀lad₀ m rs ⟩
  ε                                                         ∎
  where open Width (₁₊ m)

-- Every circuit is equal to a normal form.
normalise : (n : ℕ) → Rels n → Circuit n → NF n
normalise n rs w = proj₁ (pushW n rs (idNF n) (Associative.list-of-word w))

normalise-ok : (n : ℕ) (rs : Rels n) (w : Circuit n) → n ⊢ w ≈ ⟦ normalise n rs w ⟧ⁿ
normalise-ok n rs w = begin
  w                                                ≈⟨ Associative.lemma-list-of-word w ⟩
  ⟪ Associative.list-of-word w ⟫                   ≈⟨ sym left-unit ⟩
  ε • ⟪ Associative.list-of-word w ⟫               ≈⟨ front _ (sym (idNF-ok n rs)) ⟩
  ⟦ idNF n ⟧ⁿ • ⟪ Associative.list-of-word w ⟫     ≈⟨ proj₂ (pushW n rs (idNF n) (Associative.list-of-word w)) ⟩
  ⟦ normalise n rs w ⟧ⁿ                            ∎
  where open Width n
