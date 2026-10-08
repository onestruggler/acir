------------------------------------------------------------------------
-- Presentations of groups
--
-- Every Clifford circuit equals a normal form (Lemma 5.2 and
-- Proposition 5.3)
--
-- A generator in front of a normal form N ↑ • M • L is pushed through
-- the Z-normal circuit L (zPush), which turns it into dirty gates an
-- X-normal circuit takes; through the X-normal circuit M (xPush), which
-- leaves gates on the top wires; and those are pushed into N, one wire
-- down (push, by recursion on the width).  At width 0 the scalar ω
-- meets ω^p.  The identity has a normal form (idNF), so every circuit
-- has one (normalise).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Qubit-Clifford.Normalise where

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

open import Examples.Groups.Qubit-Clifford.Syntactics
open import Examples.Groups.Qubit-Clifford.Engine using (⟪_⟫ ; ⟪++⟫ ; ⟪≈⟫ ; ⟪map↥⟫ ; prf)
open import Examples.Groups.Qubit-Clifford.Axioms
  using (𝕨 ; h₀ ; h₁ ; h₂ ; s₀ ; s₁ ; s₂ ; c₀ ; c₁)
open import Examples.Groups.Qubit-Clifford.Reasoning
open import Examples.Groups.Qubit-Clifford.NormalForm
open import Examples.Groups.Qubit-Clifford.Tables
open import Examples.Groups.Qubit-Clifford.Push
open import Examples.Groups.Qubit-Clifford.Relations.Rules using (Eq3-2)

open Out

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

-- CZ with an A gate on its upper wire.
zAup : (a : AT) (lad : Lad (₁₊ m)) →
       (r : (AT × List Post) ⊎ (AT × BT × List Post)) →
       (₂₊ m) ⊢ ⟪ map _↥ (Al a) ++ c₀ ∷ [] ⟫ ≈ ⟪ Aupr r ⟫ →
       Out (₂₊ m) ⟦_⟧ᶻ (⟦ up (at a lad) ⟧ᶻ • ⟪ c₀ ∷ [] ⟫)
zAup {m = m} a lad (inj₁ (a' , ps)) e with pushPost m lad ps
... | out d lad' e₂ = out d (up (at a' lad')) (Glue.glue e₁ e₂)
  where
  open Width (₂₊ m)
  e₁ = trans (front _ (sym (⟪↑⟫ (Al a)))) (trans (rule→ e) (back _ (⟪↑⟫ (Al a'))))
zAup {m = m} a lad (inj₂ (a' , b , ps)) e with pushPost m lad ps
... | out d lad' e₂ = out d (at a' (b ∷ᴮ lad')) (trans (Glue.glue e₁ e₂) (back _ (sym assoc)))
  where
  open Width (₂₊ m)
  e₁ = trans (front _ (sym (⟪↑⟫ (Al a)))) (trans (rule→ e) (back _ (⟪++⟫ (Bl b) (Al a'))))

-- CZ in front of an A gate and the B gate after it.
zAB : (a : AT) (b : BT) (lad : Lad (₁₊ m)) →
      (r : (AT × BT × List Post) ⊎ (AT × List Post)) →
      (₂₊ m) ⊢ ⟪ Bl b ++ Al a ++ c₀ ∷ [] ⟫ ≈ ⟪ ABr r ⟫ →
      Out (₂₊ m) ⟦_⟧ᶻ (⟦ at a (b ∷ᴮ lad) ⟧ᶻ • ⟪ c₀ ∷ [] ⟫)
zAB {m = m} a b lad (inj₁ (a' , b' , ps)) e with pushPost m lad ps
... | out d lad' e₂ = out d (at a' (b' ∷ᴮ lad')) (Glue.glue₂ (rule3→ e) e₂)
zAB {m = m} a b lad (inj₂ (a' , ps)) e with pushPost m lad ps
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

-- H or S in front of an A gate.
zA : (a : AT) (lad : Lad (₁₊ m)) (h : Gate 1) →
     Out (₁₊ m) ⟦_⟧ᶻ (⟦ at a lad ⟧ᶻ • ⟪ gate₁ h ∷ [] ⟫)
zA {m = m} a lad h with ladPushW m lad (proj₂ (ruleA a (hs h)))
... | out d lad' e₂ = out d (at (proj₁ (ruleA a (hs h))) lad') (Glue.glue e₁ e₂)
  where
  open Width (₁₊ m)
  e₁ = trans (back _ (≡⇒≈ (Eq.cong ⟪_⟫ (Eq.sym (hs-l h))))) (rule→ (ruleA-ok a (hs h)))

-- A letter above wire 0 passes the A gate and enters the ladder.
zUp : (a : AT) (lad : Lad (₂₊ m)) (g : Gen (₁₊ m)) →
      Out (₂₊ m) ⟦_⟧ᶻ (⟦ at a lad ⟧ᶻ • ⟪ g ↥ ∷ [] ⟫)
zUp {m = m} a lad g with ladPush (suc m) lad (lup g)
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

zPush : (m : ℕ) (L : Zc (₁₊ m)) (g : Gen (₁₊ m)) → Out (₁₊ m) ⟦_⟧ᶻ (⟦ L ⟧ᶻ • ⟪ g ∷ [] ⟫)
zPush (suc m) (up L) (g ↥)              = upOut (liftOut (zPush m L g))
zPush (suc m) (up L) (gate₁ h)          = pass↑ (up L) ⟦ L ⟧ᶻ Eq.refl h (hsM h) (hsM-l h)
zPush (suc m) (up L) (gate₀ ω-gate)     = scalarOut (up L) _ PB.refl
zPush (suc (suc m)) (up (up L)) (gate₂ CZ-gate) =
  passW (up (up L)) (c₀ ∷ []) (mC ∷ []) (PB.sym (low2s-comm (c₀ ∷ []) Eq.refl ⟦ L ⟧ᶻ)) Eq.refl
zPush (suc m) (up (at a lad)) (gate₂ CZ-gate) = zAup a lad (ruleAup a) (ruleAup-ok a)
zPush m (at a lad) (gate₁ h)            = zA a lad h
zPush m (at a lad) (gate₀ ω-gate)       = scalarOut (at a lad) _ PB.refl
zPush (suc m) (at a (b ∷ᴮ lad)) (gate₂ CZ-gate) = zAB a b lad (ruleAB a b) (ruleAB-ok a b)
zPush (suc m) (at a lad) (g ↥)          = zUp a lad g
zPush zero (at a lad) (gate₀ ω-gate ↥)  = scalarOut (at a lad) _ ω↑

------------------------------------------------------------------------
-- Pushing into X-normal circuits
--
-- What comes out of a D-ladder is gates on the wires above wire 0,
-- which are done, and a power of S on wire 0, which the E gate absorbs.

spow : ℕ → Circuit (₁₊ m)
spow zero    = ε
spow (suc k) = S • spow k

record DOut (m : ℕ) (lhs : Circuit (₁₊ m)) : Set where
  constructor dout
  field
    vs : List (Gen m)
    nS : ℕ
    dl : DL (₁₊ m)
    ok : (₁₊ m) ⊢ lhs ≈ ⟪ vs ⟫ ↑ • spow nS • ⟦ dl ⟧ᴰ

-- The outputs of D gates, sorted.
o2split : List O2 → List (Gen (₁₊ m)) × ℕ
o2split []         = [] , 0
o2split {m} (oh₁ ∷ os) = h₀ ∷ proj₁ (o2split {m} os) , proj₂ (o2split {m} os)
o2split {m} (os₁ ∷ os) = s₀ ∷ proj₁ (o2split {m} os) , proj₂ (o2split {m} os)
o2split {m} (oS₀ ∷ os) = proj₁ (o2split {m} os) , suc (proj₂ (o2split {m} os))
o2split {m} (oω ∷ os)  = 𝕨 ∷ proj₁ (o2split {m} os) , proj₂ (o2split {m} os)

o3split : List O3 → List (Gen (₂₊ m)) × ℕ
o3split []          = [] , 0
o3split {m} (o3h₁ ∷ os) = h₀ ∷ proj₁ (o3split {m} os) , proj₂ (o3split {m} os)
o3split {m} (o3s₁ ∷ os) = s₀ ∷ proj₁ (o3split {m} os) , proj₂ (o3split {m} os)
o3split {m} (o3h₂ ∷ os) = h₁ ∷ proj₁ (o3split {m} os) , proj₂ (o3split {m} os)
o3split {m} (o3s₂ ∷ os) = s₁ ∷ proj₁ (o3split {m} os) , proj₂ (o3split {m} os)
o3split {m} (o3c₁ ∷ os) = c₀ ∷ proj₁ (o3split {m} os) , proj₂ (o3split {m} os)
o3split {m} (o3S₀ ∷ os) = proj₁ (o3split {m} os) , suc (proj₂ (o3split {m} os))
o3split {m} (o3ω ∷ os)  = 𝕨 ∷ proj₁ (o3split {m} os) , proj₂ (o3split {m} os)

module Split {m : ℕ} where

  open Width (₁₊ m)

  -- The shape the outputs are brought into.
  shape : List (Gen m) × ℕ → Circuit (₁₊ m)
  shape (vs , k) = ⟪ vs ⟫ ↑ • spow k

  empty : ε ≈ shape ([] , 0)
  empty = sym left-unit

  -- A letter above wire 0 joins the gates that are done.
  cons-up : (x : Gen m) (vs : List (Gen m)) (k : ℕ) →
            [ x ↥ ]ʷ • shape (vs , k) ≈ shape (x ∷ vs , k)
  cons-up x vs k = sym assoc

  -- So does the scalar.
  cons-ω : (vs : List (Gen m)) (k : ℕ) → [ 𝕨 ]ʷ • shape (vs , k) ≈ shape (𝕨 ∷ vs , k)
  cons-ω vs k = trans (front _ (sym ω↑)) (cons-up 𝕨 vs k)

  -- S on wire 0 passes the gates that are done.
  cons-S : (vs : List (Gen m)) (k : ℕ) → S • shape (vs , k) ≈ shape (vs , suc k)
  cons-S vs k = begin
    S • ⟪ vs ⟫ ↑ • spow k         ≈⟨ sym assoc ⟩
    (S • ⟪ vs ⟫ ↑) • spow k       ≈⟨ front _ sc ⟩
    (⟪ vs ⟫ ↑ • S) • spow k       ≈⟨ assoc ⟩
    ⟪ vs ⟫ ↑ • S • spow k         ∎
    where
    sc : S • ⟪ vs ⟫ ↑ ≈ ⟪ vs ⟫ ↑ • S
    sc = trans (front _ (sym right-unit))
         (trans (low1s-comm (s₀ ∷ []) Eq.refl ⟪ vs ⟫) (back _ right-unit))

o2split-ok : (os : List O2) → (₂₊ m) ⊢ ⟪ concatMap O2l os ⟫ ≈ Split.shape (o2split {m} os)
o2split-ok []         = Split.empty
o2split-ok (oh₁ ∷ os) = PB.trans (PB.cong PB.refl (o2split-ok os)) (Split.cons-up _ _ _)
o2split-ok (os₁ ∷ os) = PB.trans (PB.cong PB.refl (o2split-ok os)) (Split.cons-up _ _ _)
o2split-ok (oS₀ ∷ os) = PB.trans (PB.cong PB.refl (o2split-ok os)) (Split.cons-S _ _)
o2split-ok (oω ∷ os)  = PB.trans (PB.cong PB.refl (o2split-ok os)) (Split.cons-ω _ _)

o3split-ok : (os : List O3) → (₃₊ m) ⊢ ⟪ concatMap O3l os ⟫ ≈ Split.shape (o3split {m} os)
o3split-ok []          = Split.empty
o3split-ok (o3h₁ ∷ os) = PB.trans (PB.cong PB.refl (o3split-ok os)) (Split.cons-up _ _ _)
o3split-ok (o3s₁ ∷ os) = PB.trans (PB.cong PB.refl (o3split-ok os)) (Split.cons-up _ _ _)
o3split-ok (o3h₂ ∷ os) = PB.trans (PB.cong PB.refl (o3split-ok os)) (Split.cons-up _ _ _)
o3split-ok (o3s₂ ∷ os) = PB.trans (PB.cong PB.refl (o3split-ok os)) (Split.cons-up _ _ _)
o3split-ok (o3c₁ ∷ os) = PB.trans (PB.cong PB.refl (o3split-ok os)) (Split.cons-up _ _ _)
o3split-ok (o3S₀ ∷ os) = PB.trans (PB.cong PB.refl (o3split-ok os)) (Split.cons-S _ _)
o3split-ok (o3ω ∷ os)  = PB.trans (PB.cong PB.refl (o3split-ok os)) (Split.cons-ω _ _)

module DSteps {m : ℕ} where

  open Width (₂₊ m)

  -- A D gate meets powers of S coming down from above.
  dS : (d : DT) (k : ℕ) → ⟪ Dl d ⟫ • spow k ↑ ≈ spow k • ⟪ Dl d ⟫
  dS d zero    = trans right-unit (sym left-unit)
  dS d (suc k) = begin
    ⟪ Dl d ⟫ • S ↑ • spow k ↑        ≈⟨ sym assoc ⟩
    (⟪ Dl d ⟫ • S ↑) • spow k ↑      ≈⟨ front _ e ⟩
    (S • ⟪ Dl d ⟫) • spow k ↑        ≈⟨ assoc ⟩
    S • ⟪ Dl d ⟫ • spow k ↑          ≈⟨ back _ (dS d k) ⟩
    S • spow k • ⟪ Dl d ⟫            ≈⟨ sym assoc ⟩
    (S • spow k) • ⟪ Dl d ⟫          ∎
    where
    e : ⟪ Dl d ⟫ • S ↑ ≈ S • ⟪ Dl d ⟫
    e = trans (back _ (sym right-unit))
        (trans (rule→ {xs = Dl d} {gs = s₁ ∷ []} {ys = s₀ ∷ []} {xs' = Dl d} (ruleS1D-ok d))
               (front _ right-unit))

  -- A D gate passes what came out of the ladder above.
  slide : (d : DT) (vs : List (Gen m)) (k : ℕ) (r : Circuit (₂₊ m)) →
          ⟪ Dl d ⟫ • ⟪ vs ⟫ ↑ ↑ • spow k ↑ • r ≈ ⟪ map _↥ vs ⟫ ↑ • spow k • ⟪ Dl d ⟫ • r
  slide d vs k r = begin
    ⟪ Dl d ⟫ • ⟪ vs ⟫ ↑ ↑ • spow k ↑ • r      ≈⟨ swap _ (low2s-comm (Dl d) (Dl-low2 d) ⟪ vs ⟫) ⟩
    ⟪ vs ⟫ ↑ ↑ • ⟪ Dl d ⟫ • spow k ↑ • r      ≈⟨ back _ (pair _ (dS d k)) ⟩
    ⟪ vs ⟫ ↑ ↑ • spow k • ⟪ Dl d ⟫ • r        ≈⟨ front _ (sym (lift (⟪↑⟫ vs))) ⟩
    ⟪ map _↥ vs ⟫ ↑ • spow k • ⟪ Dl d ⟫ • r   ∎

  -- A D gate meets a gate on wire 0, or CZ with nothing above.
  meet : (d d' : DT) (g : List (Gen (₂₊ m))) (os : List O2) (r : Circuit (₂₊ m)) →
         ⟪ Dl d ⟫ • ⟪ g ⟫ ≈ ⟪ concatMap O2l os ⟫ • ⟪ Dl d' ⟫ →
         (⟪ Dl d ⟫ • ⟪ g ⟫) • r ≈ Split.shape (o2split {m} os) • ⟪ Dl d' ⟫ • r
  meet d d' g os r e = trans (front _ (trans e (front _ (o2split-ok os)))) assoc

-- A D gate meets a gate that passed the D-ladder above it.
dStep : (m : ℕ) (d : DT) (dl : DL (₁₊ m)) (g : List (Gen (₂₊ m))) (d' : DT) (os : List O2) →
        (₂₊ m) ⊢ ⟦ dl ⟧ᴰ ↑ • ⟪ g ⟫ ≈ ⟪ g ⟫ • ⟦ dl ⟧ᴰ ↑ →
        (₂₊ m) ⊢ ⟪ Dl d ⟫ • ⟪ g ⟫ ≈ ⟪ concatMap O2l os ⟫ • ⟪ Dl d' ⟫ →
        DOut (suc m) ((⟪ Dl d ⟫ • ⟦ dl ⟧ᴰ ↑) • ⟪ g ⟫)
dStep m d dl g d' os c e =
  dout (proj₁ (o2split {m} os)) (proj₂ (o2split {m} os)) (d' ∷ᴰ dl) p
  where
  open Width (₂₊ m)
  p = begin
    (⟪ Dl d ⟫ • ⟦ dl ⟧ᴰ ↑) • ⟪ g ⟫           ≈⟨ trans assoc (back _ c) ⟩
    ⟪ Dl d ⟫ • ⟪ g ⟫ • ⟦ dl ⟧ᴰ ↑             ≈⟨ sym assoc ⟩
    (⟪ Dl d ⟫ • ⟪ g ⟫) • ⟦ dl ⟧ᴰ ↑           ≈⟨ DSteps.meet d d' g os _ e ⟩
    Split.shape (o2split {m} os) • ⟪ Dl d' ⟫ • ⟦ dl ⟧ᴰ ↑   ≈⟨ assoc ⟩
    _ ∎

dPush : (m : ℕ) (dl : DL (₁₊ m)) (g : MIn (₁₊ m)) → DOut m (⟦ dl ⟧ᴰ • ⟪ Ml g ⟫)
dPush m dl mω = dout (𝕨 ∷ []) 0 dl
  (trans (back _ right-unit) (trans (sym (ω-comm _))
    (trans (front _ (trans (sym ω↑) (sym right-unit))) (back _ (sym left-unit)))))
  where open Width (₁₊ m)
dPush zero []ᴰ mSt = dout [] 1 []ᴰ (PP.by-assoc (1 VRel,_===_) Eq.refl)
dPush (suc m) (d ∷ᴰ dl) (mup g) with dPush m dl g
... | dout vs k dl' e = dout (map _↥ vs) k (d ∷ᴰ dl') p
  where
  open Width (₂₊ m)
  p = begin
    (⟪ Dl d ⟫ • ⟦ dl ⟧ᴰ ↑) • ⟪ map _↥ (Ml g) ⟫        ≈⟨ trans assoc (back _ (back _ (⟪↑⟫ (Ml g)))) ⟩
    ⟪ Dl d ⟫ • (⟦ dl ⟧ᴰ • ⟪ Ml g ⟫) ↑                 ≈⟨ back _ (lift e) ⟩
    ⟪ Dl d ⟫ • (⟪ vs ⟫ ↑ • spow k • ⟦ dl' ⟧ᴰ) ↑       ≈⟨ DSteps.slide d vs k _ ⟩
    ⟪ map _↥ vs ⟫ ↑ • spow k • ⟪ Dl d ⟫ • ⟦ dl' ⟧ᴰ ↑ ∎
dPush (suc m) (d ∷ᴰ dl) mH = dStep m d dl (h₀ ∷ []) (proj₁ (ruleD d gH)) (proj₂ (ruleD d gH))
  (PB.sym (low1s-comm (h₀ ∷ []) Eq.refl ⟦ dl ⟧ᴰ))
  (rule→ {xs = Dl d} {gs = h₀ ∷ []} {ys = concatMap O2l (proj₂ (ruleD d gH))} {xs' = Dl (proj₁ (ruleD d gH))} (ruleD-ok d gH))
dPush (suc m) (d ∷ᴰ dl) mS = dStep m d dl (s₀ ∷ []) (proj₁ (ruleD d gS)) (proj₂ (ruleD d gS))
  (PB.sym (low1s-comm (s₀ ∷ []) Eq.refl ⟦ dl ⟧ᴰ))
  (rule→ {xs = Dl d} {gs = s₀ ∷ []} {ys = concatMap O2l (proj₂ (ruleD d gS))} {xs' = Dl (proj₁ (ruleD d gS))} (ruleD-ok d gS))
dPush (suc zero) (d ∷ᴰ []ᴰ) mC = dStep zero d []ᴰ (c₀ ∷ []) (proj₁ (ruleCD d)) (proj₂ (ruleCD d))
  (PB.trans PB.left-unit (PB.sym PB.right-unit))
  (rule→ {xs = Dl d} {gs = c₀ ∷ []} {ys = concatMap O2l (proj₂ (ruleCD d))} {xs' = Dl (proj₁ (ruleCD d))} (ruleCD-ok d))
dPush (suc (suc m)) (d ∷ᴰ d₁ ∷ᴰ dl) mC =
  dout (proj₁ sp) (proj₂ sp) (d₀' ∷ᴰ d₁' ∷ᴰ dl) p
  where
  open Width (₃₊ m)
  r   = ruleDD d₁ d
  d₁' = proj₁ r
  d₀' = proj₁ (proj₂ r)
  os  = proj₂ (proj₂ r)
  sp  = o3split {m} os
  e₃ : ⟪ Dl d ⟫ • ⟪ Dl d₁ ⟫ ↑ • ⟪ c₀ ∷ [] ⟫ ≈ ⟪ concatMap O3l os ⟫ • ⟪ Dl d₀' ⟫ • ⟪ Dl d₁' ⟫ ↑
  e₃ = trans (back _ (front _ (sym (⟪↑⟫ (Dl d₁)))))
       (trans (rule3→ (ruleDD-ok d₁ d)) (back _ (back _ (⟪↑⟫ (Dl d₁')))))
  p = begin
    (⟪ Dl d ⟫ • (⟪ Dl d₁ ⟫ ↑ • ⟦ dl ⟧ᴰ ↑ ↑)) • ⟪ c₀ ∷ [] ⟫      ≈⟨ trans assoc (back _ assoc) ⟩
    ⟪ Dl d ⟫ • ⟪ Dl d₁ ⟫ ↑ • ⟦ dl ⟧ᴰ ↑ ↑ • ⟪ c₀ ∷ [] ⟫          ≈⟨ back _ (back _ (sym (low2s-comm (c₀ ∷ []) Eq.refl ⟦ dl ⟧ᴰ))) ⟩
    ⟪ Dl d ⟫ • ⟪ Dl d₁ ⟫ ↑ • ⟪ c₀ ∷ [] ⟫ • ⟦ dl ⟧ᴰ ↑ ↑          ≈⟨ trans (back _ (sym assoc)) (sym assoc) ⟩
    (⟪ Dl d ⟫ • ⟪ Dl d₁ ⟫ ↑ • ⟪ c₀ ∷ [] ⟫) • ⟦ dl ⟧ᴰ ↑ ↑        ≈⟨ front _ e₃ ⟩
    (⟪ concatMap O3l os ⟫ • ⟪ Dl d₀' ⟫ • ⟪ Dl d₁' ⟫ ↑) • ⟦ dl ⟧ᴰ ↑ ↑   ≈⟨ front _ (front _ (o3split-ok os)) ⟩
    (Split.shape sp • ⟪ Dl d₀' ⟫ • ⟪ Dl d₁' ⟫ ↑) • ⟦ dl ⟧ᴰ ↑ ↑        ≈⟨ trans assoc (trans assoc (back _ (back _ assoc))) ⟩
    _ ∎

-- An X-normal circuit: the E gate absorbs the S that comes down.
record XOut (m : ℕ) (lhs : Circuit (₁₊ m)) : Set where
  constructor xout
  field
    vs : List (Gen m)
    M  : Xc (₁₊ m)
    ok : (₁₊ m) ⊢ lhs ≈ ⟪ vs ⟫ ↑ • ⟦ M ⟧ˣ

erot : ℕ → ET → ET
erot zero    e = e
erot (suc k) e = erot k (ruleE e)

Es : (e : ET) (k : ℕ) → (₁₊ m) ⊢ ⟪ El e ⟫ • spow k ≈ ⟪ El (erot k e) ⟫
Es e zero    = PB.right-unit
Es {m} e (suc k) = begin
  ⟪ El e ⟫ • S • spow k         ≈⟨ sym assoc ⟩
  (⟪ El e ⟫ • S) • spow k       ≈⟨ front _ e₁ ⟩
  ⟪ El (ruleE e) ⟫ • spow k     ≈⟨ Es (ruleE e) k ⟩
  ⟪ El (erot k (ruleE e)) ⟫     ∎
  where
  open Width (₁₊ m)
  e₁ = trans (back _ (sym right-unit)) (trans (sym (⟪++⟫ (El e) (s₀ ∷ []))) (ruleE-ok e))

xPush : (m : ℕ) (M : Xc (₁₊ m)) (g : MIn (₁₊ m)) → XOut m (⟦ M ⟧ˣ • ⟪ Ml g ⟫)
xPush m (e ,ˣ dl) g with dPush m dl g
... | dout vs k dl' ok = xout vs (erot k e ,ˣ dl') p
  where
  open Width (₁₊ m)
  p = begin
    (⟪ El e ⟫ • ⟦ dl ⟧ᴰ) • ⟪ Ml g ⟫                  ≈⟨ trans assoc (back _ ok) ⟩
    ⟪ El e ⟫ • ⟪ vs ⟫ ↑ • spow k • ⟦ dl' ⟧ᴰ          ≈⟨ swap _ (low1s-comm (El e) (El-low1 e) ⟪ vs ⟫) ⟩
    ⟪ vs ⟫ ↑ • ⟪ El e ⟫ • spow k • ⟦ dl' ⟧ᴰ          ≈⟨ back _ (trans (sym assoc) (front _ (Es e k))) ⟩
    ⟪ vs ⟫ ↑ • ⟪ El (erot k e) ⟫ • ⟦ dl' ⟧ᴰ          ∎

xPushL : (m : ℕ) (M : Xc (₁₊ m)) (ds : List (MIn (₁₊ m))) → XOut m (⟦ M ⟧ˣ • ⟪ Mls ds ⟫)
xPushL m M [] = xout [] M (trans right-unit (sym left-unit))
  where open Width (₁₊ m)
xPushL m M (d ∷ ds) with xPush m M d
... | xout vs₁ M₁ e₁ with xPushL m M₁ ds
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

-- The scalar meets ω^p.
inc : Fin 8 → Fin 8
inc ₀ = ₁
inc ₁ = ₂
inc ₂ = ₃
inc ₃ = ₄
inc ₄ = ₅
inc ₅ = ₆
inc ₆ = ₇
inc ₇ = ₀

private
  ω-step : (k : ℕ) → 0 ⊢ ω ^ suc k • ω • ε ≈ ω ^ suc (suc k)
  ω-step k = PB.trans (PB.cong PB.refl PB.right-unit) (PB.sym (ω-comm (ω ^ suc k)))

inc-ok : (p : Fin 8) → 0 ⊢ ω ^ toℕ p • ω • ε ≈ ω ^ toℕ (inc p)
inc-ok ₀ = PB.trans PB.left-unit PB.right-unit
inc-ok ₁ = ω-step 0
inc-ok ₂ = ω-step 1
inc-ok ₃ = ω-step 2
inc-ok ₄ = ω-step 3
inc-ok ₅ = ω-step 4
inc-ok ₆ = ω-step 5
inc-ok ₇ = PB.trans (ω-step 6) (PB.axiom (srel C₁))

push  : (n : ℕ) (N : NF n) (g : Gen n) → Σ (NF n) λ N' → n ⊢ ⟦ N ⟧ⁿ • ⟪ g ∷ [] ⟫ ≈ ⟦ N' ⟧ⁿ
pushW : (n : ℕ) (N : NF n) (gs : List (Gen n)) → Σ (NF n) λ N' → n ⊢ ⟦ N ⟧ⁿ • ⟪ gs ⟫ ≈ ⟦ N' ⟧ⁿ

push zero (nf₀ p) (gate₀ ω-gate) = nf₀ (inc p) , inc-ok p
push (suc m) (nfₛ L M N) g with zPush m L g
... | out ds L' e₁ with xPushL m M ds
... | xout vs M' e₂ with pushW m N vs
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

pushW n N []       = N , PB.right-unit
pushW n N (g ∷ gs) with push n N g
... | N₁ , e₁ with pushW n N₁ gs
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

lad₁ : (m : ℕ) → Lad (₁₊ m)
lad₁ zero    = top C₁
lad₁ (suc m) = B₁ ∷ᴮ lad₁ m

dl₁ : (m : ℕ) → DL (₁₊ m)
dl₁ zero    = []ᴰ
dl₁ (suc m) = D₁ ∷ᴰ dl₁ m

idNF : (n : ℕ) → NF n
idNF zero    = nf₀ ₀
idNF (suc m) = nfₛ (at A₁ (lad₁ m)) (E₁ ,ˣ dl₁ m) (idNF m)

-- D₁ undoes B₁ (3.2).
D₁B₁ : (₂₊ m) ⊢ ⟪ Dl D₁ ⟫ • ⟪ Bl B₁ ⟫ ≈ ε
D₁B₁ = PB.trans (PB.sym (⟪++⟫ (Dl D₁) (Bl B₁))) (PB.sym (prf Eq3-2))

dl₁lad₁ : (m : ℕ) → (₁₊ m) ⊢ ⟦ dl₁ m ⟧ᴰ • ⟦ lad₁ m ⟧ᴸ ≈ ε
dl₁lad₁ zero    = PB.left-unit
dl₁lad₁ (suc m) = begin
  (⟪ Dl D₁ ⟫ • ⟦ dl₁ m ⟧ᴰ ↑) • (⟦ lad₁ m ⟧ᴸ ↑ • ⟪ Bl B₁ ⟫)   ≈⟨ trans assoc (back _ (sym assoc)) ⟩
  ⟪ Dl D₁ ⟫ • (⟦ dl₁ m ⟧ᴰ • ⟦ lad₁ m ⟧ᴸ) ↑ • ⟪ Bl B₁ ⟫        ≈⟨ back _ (front _ (lift (dl₁lad₁ m))) ⟩
  ⟪ Dl D₁ ⟫ • ε • ⟪ Bl B₁ ⟫                                 ≈⟨ trans (back _ left-unit) D₁B₁ ⟩
  ε                                                         ∎
  where open Width (₂₊ m)

idNF-ok : (n : ℕ) → n ⊢ ⟦ idNF n ⟧ⁿ ≈ ε
idNF-ok zero    = PB.refl
idNF-ok (suc m) = begin
  ⟦ idNF m ⟧ⁿ ↑ • (ε • ⟦ dl₁ m ⟧ᴰ) • (⟦ lad₁ m ⟧ᴸ • ε)       ≈⟨ front _ (lift (idNF-ok m)) ⟩
  ε • (ε • ⟦ dl₁ m ⟧ᴰ) • (⟦ lad₁ m ⟧ᴸ • ε)                  ≈⟨ trans left-unit (trans (front _ left-unit) (back _ right-unit)) ⟩
  ⟦ dl₁ m ⟧ᴰ • ⟦ lad₁ m ⟧ᴸ                                  ≈⟨ dl₁lad₁ m ⟩
  ε                                                         ∎
  where open Width (₁₊ m)

-- Every circuit is equal to a normal form.
normalise : (n : ℕ) → Circuit n → NF n
normalise n w = proj₁ (pushW n (idNF n) (Associative.list-of-word w))

normalise-ok : (n : ℕ) (w : Circuit n) → n ⊢ w ≈ ⟦ normalise n w ⟧ⁿ
normalise-ok n w = begin
  w                                                ≈⟨ Associative.lemma-list-of-word w ⟩
  ⟪ Associative.list-of-word w ⟫                   ≈⟨ sym left-unit ⟩
  ε • ⟪ Associative.list-of-word w ⟫               ≈⟨ front _ (sym (idNF-ok n)) ⟩
  ⟦ idNF n ⟧ⁿ • ⟪ Associative.list-of-word w ⟫     ≈⟨ proj₂ (pushW n (idNF n) (Associative.list-of-word w)) ⟩
  ⟦ normalise n w ⟧ⁿ                               ∎
  where open Width n
