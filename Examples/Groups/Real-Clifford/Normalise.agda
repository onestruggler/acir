------------------------------------------------------------------------
-- Presentations of groups
--
-- Every real Clifford circuit equals a normal form (Proposition 5.7)
--
-- A generator in front of a normal form (−1)^s • N ↑ • M • L is pushed
-- through the Z-circuit L (zPush), which turns it into dirty gates an
-- X-circuit takes; through the X-circuit M (xPush), which leaves a sign
-- and gates on the top wires; and those are pushed into N, one wire
-- down (push, by recursion on the width).  The identity has a normal
-- form (idNF), so every circuit has one (normalise).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford.Normalise where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _xor_)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; map ; concatMap)
open import Data.Nat.Base using (ℕ ; zero ; suc)
open import Data.Product.Base using (Σ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊)

import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Tactics.Words using (module Associative)

open import Examples.Groups.Real-Clifford.Syntactics
open import Examples.Groups.Real-Clifford.Engine
  using (⟪_⟫ ; ⟪++⟫ ; ⟪≈⟫ ; ⟪map↥⟫ ; perm-sound ; rev ; rev-inv)
open import Examples.Groups.Real-Clifford.Axioms
  using (𝕞 ; h₀ ; h₁ ; h₂ ; z₀ ; z₁ ; z₂ ; c₀ ; c₁)
open import Examples.Groups.Real-Clifford.Reasoning
open import Examples.Groups.Real-Clifford.NormalForm
open import Examples.Groups.Real-Clifford.Tables
open import Examples.Groups.Real-Clifford.Push

open Out

private
  variable
    n m k : ℕ
    t u : Ty

------------------------------------------------------------------------
-- Generic steps

-- A word that passes the structure unchanged.
passW : {X : Set} {F : X → Circuit n} (x : X) (g : List (Gen n)) (d : List (MIn n)) →
        n ⊢ F x • ⟪ g ⟫ ≈ ⟪ g ⟫ • F x → ⟪ g ⟫ ≡ ⟪ Mls d ⟫ → Out n F (F x • ⟪ g ⟫)
passW {n} x g d e e' = out d x (trans e (front _ (≡⇒≈ e')))
  where open Width n

-- The scalar passes anything.
scalarW : {X : Set} {F : X → Circuit n} (x : X) (g : Gen n) → n ⊢ [ g ]ʷ ≈ neg →
          Out n F (F x • ⟪ g ∷ [] ⟫)
scalarW {n} x g e = out (mneg ∷ []) x
  (trans (back _ (trans right-unit e)) (trans (sym (neg-comm _)) (front _ (sym right-unit))))
  where open Width n

-- A one-wire letter at the bottom passes a circuit shifted up.
pass↑ : {X : Set} {F : X → Circuit (₂₊ m)} (x : X) (w : Circuit (₁₊ m)) → F x ≡ w ↑ →
        (h : Gate 1) (d : MIn (₂₊ m)) → Ml d ≡ gate₁ h ∷ [] → Out (₂₊ m) F (F x • ⟪ gate₁ h ∷ [] ⟫)
pass↑ {m} {F = F} x w eq h d e = passW x (gate₁ h ∷ []) (d ∷ [])
  (Eq.subst (λ y → (₂₊ m) ⊢ y • ⟪ gate₁ h ∷ [] ⟫ ≈ ⟪ gate₁ h ∷ [] ⟫ • y) (Eq.sym eq)
    (sym (low1s-comm (gate₁ h ∷ []) Eq.refl w)))
  (Eq.cong ⟪_⟫ (Eq.cong (_++ []) (Eq.sym e)))
  where open Width (₂₊ m)

hz : Gate 1 → HZ
hz H-gate = gH
hz Z-gate = gZ

hzM : Gate 1 → MIn (₂₊ m)
hzM H-gate = mH
hzM Z-gate = mZ

hz-l : (h : Gate 1) → HZl {n = m} (hz h) ≡ gate₁ h ∷ []
hz-l H-gate = Eq.refl
hz-l Z-gate = Eq.refl

hzM-l : (h : Gate 1) → Ml {₂₊ m} (hzM h) ≡ gate₁ h ∷ []
hzM-l H-gate = Eq.refl
hzM-l Z-gate = Eq.refl

------------------------------------------------------------------------
-- Pushing into Z-circuits

upOut : {lhs : Circuit (₂₊ m)} → Out (₂₊ m) (λ (L : Zc (₁₊ m)) → ⟦ L ⟧ᶻ ↑) lhs → Out (₂₊ m) ⟦_⟧ᶻ lhs
upOut (out d L e) = out d (up L) e

-- CZ with an A gate on its upper wire.
zAup : (a : AT t) (lad : Lad t (₁₊ m)) →
       (r : (AT t × List (Post t)) ⊎ (Σ Ty λ t' → AT t' × BT t' t × List (Post t))) →
       (₂₊ m) ⊢ ⟪ map _↥ (Al a) ++ c₀ ∷ [] ⟫ ≈ ⟪ Aupr r ⟫ →
       Out (₂₊ m) ⟦_⟧ᶻ (⟦ up (at a lad) ⟧ᶻ • ⟪ c₀ ∷ [] ⟫)
zAup {m = m} a lad (inj₁ (a' , ps)) e with pushPost m lad ps
... | out d lad' e₂ = out d (up (at a' lad')) (Glue.glue e₁ e₂)
  where
  open Width (₂₊ m)
  e₁ = trans (front _ (sym (⟪↑⟫ (Al a)))) (trans (rule→ e) (back _ (⟪↑⟫ (Al a'))))
zAup {m = m} a lad (inj₂ (t' , a' , b , ps)) e with pushPost m lad ps
... | out d lad' e₂ = out d (at a' (b ∷ᴮ lad')) (trans (Glue.glue e₁ e₂) (back _ (sym assoc)))
  where
  open Width (₂₊ m)
  e₁ = trans (front _ (sym (⟪↑⟫ (Al a)))) (trans (rule→ e) (back _ (⟪++⟫ (Bl b) (Al a'))))

-- CZ in front of an A gate and the B gate after it.
zAB : (a : AT t) (b : BT t u) (lad : Lad u (₁₊ m)) →
      (r : (Σ Ty λ t' → AT t' × BT t' u × List (Post u)) ⊎ (AT u × List (Post u))) →
      (₂₊ m) ⊢ ⟪ Bl b ++ Al a ++ c₀ ∷ [] ⟫ ≈ ⟪ ABr r ⟫ →
      Out (₂₊ m) ⟦_⟧ᶻ (⟦ at a (b ∷ᴮ lad) ⟧ᶻ • ⟪ c₀ ∷ [] ⟫)
zAB {m = m} a b lad (inj₁ (t' , a' , b' , ps)) e with pushPost m lad ps
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

-- H or Z in front of an A gate.
zA : (a : AT t) (lad : Lad t (₁₊ m)) (h : Gate 1) →
     Out (₁₊ m) ⟦_⟧ᶻ (⟦ at a lad ⟧ᶻ • ⟪ gate₁ h ∷ [] ⟫)
zA {m = m} a lad h with ladPushW m lad (proj₂ (ruleA a (hz h)))
... | out d lad' e₂ = out d (at (proj₁ (ruleA a (hz h))) lad') (Glue.glue e₁ e₂)
  where
  open Width (₁₊ m)
  e₁ = trans (back _ (≡⇒≈ (Eq.cong ⟪_⟫ (Eq.sym (hz-l h))))) (rule→ (ruleA-ok a (hz h)))

-- A letter above wire 0 passes the A gate and enters the ladder.
zUp : (a : AT t) (lad : Lad t (₂₊ m)) (g : Gen (₁₊ m)) →
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
zPush (suc m) (up L) (gate₁ h)          = pass↑ (up L) ⟦ L ⟧ᶻ Eq.refl h (hzM h) (hzM-l h)
zPush (suc m) (up L) (gate₀ neg-gate)   = scalarW (up L) _ PB.refl
zPush (suc (suc m)) (up (up L)) (gate₂ CZ-gate) =
  passW (up (up L)) (c₀ ∷ []) (mC ∷ []) (PB.sym (low2s-comm (c₀ ∷ []) Eq.refl ⟦ L ⟧ᶻ)) Eq.refl
zPush (suc m) (up (at a lad)) (gate₂ CZ-gate) = zAup a lad (ruleAup a) (ruleAup-ok a)
zPush m (at a lad) (gate₁ h)            = zA a lad h
zPush m (at a lad) (gate₀ neg-gate)     = scalarW (at a lad) _ PB.refl
zPush (suc m) (at a (b ∷ᴮ lad)) (gate₂ CZ-gate) = zAB a b lad (ruleAB a b) (ruleAB-ok a b)
zPush (suc m) (at a lad) (g ↥)          = zUp a lad g
zPush zero (at a lad) (gate₀ neg-gate ↥) = scalarW (at a lad) _ neg↑

------------------------------------------------------------------------
-- Signs

module Sign {n : ℕ} where

  open Width n

  sgn-comm : (s : Bool) (w : Circuit n) → sgn s • w ≈ w • sgn s
  sgn-comm false w = trans left-unit (sym right-unit)
  sgn-comm true  w = neg-comm w

  sgn-xor : (a b : Bool) → sgn {n} a • sgn b ≈ sgn (a xor b)
  sgn-xor false b     = left-unit
  sgn-xor true  false = right-unit
  sgn-xor true  true  = PB.axiom (srel R₁)

  sgn-neg : (s : Bool) → neg • sgn {n} s ≈ sgn (not s)
  sgn-neg false = right-unit
  sgn-neg true  = PB.axiom (srel R₁)

sgn↑ : (s : Bool) → (₁₊ n) ⊢ sgn s ↑ ≈ sgn s
sgn↑ false = PB.refl
sgn↑ true  = neg↑

------------------------------------------------------------------------
-- Pushing into X-circuits
--
-- What comes out of a D-ladder is a sign, gates on the wires above
-- wire 0, which are done, and possibly Z on wire 0, which the E gate
-- absorbs.

zpow : Bool → Circuit (₁₊ m)
zpow false = ε
zpow true  = Z

zpow-z : (z : Bool) → (₁₊ m) ⊢ Z • zpow z ≈ zpow (not z)
zpow-z false = PB.right-unit
zpow-z true  = PB.axiom (srel R₂)

record DOut (m : ℕ) (lhs : Circuit (₁₊ m)) : Set where
  constructor dout
  field
    s  : Bool
    vs : List (Gen m)
    z  : Bool
    dl : DL (₁₊ m)
    ok : (₁₊ m) ⊢ lhs ≈ sgn s • ⟪ vs ⟫ ↑ • zpow z • ⟦ dl ⟧ᴰ

-- The outputs of D gates, sorted.
o2split : List O2 → Bool × List (Gen (₁₊ m)) × Bool
o2split []          = false , [] , false
o2split {m} (oh₁ ∷ os)  = proj₁ (o2split {m} os) , h₀ ∷ proj₁ (proj₂ (o2split {m} os)) , proj₂ (proj₂ (o2split {m} os))
o2split {m} (oz₁ ∷ os)  = proj₁ (o2split {m} os) , z₀ ∷ proj₁ (proj₂ (o2split {m} os)) , proj₂ (proj₂ (o2split {m} os))
o2split {m} (oZ₀ ∷ os)  = proj₁ (o2split {m} os) , proj₁ (proj₂ (o2split {m} os)) , not (proj₂ (proj₂ (o2split {m} os)))
o2split {m} (oneg ∷ os) = not (proj₁ (o2split {m} os)) , proj₁ (proj₂ (o2split {m} os)) , proj₂ (proj₂ (o2split {m} os))

o3split : List O3 → Bool × List (Gen (₂₊ m)) × Bool
o3split []           = false , [] , false
o3split {m} (o3h₁ ∷ os)  = proj₁ (o3split {m} os) , h₀ ∷ proj₁ (proj₂ (o3split {m} os)) , proj₂ (proj₂ (o3split {m} os))
o3split {m} (o3z₁ ∷ os)  = proj₁ (o3split {m} os) , z₀ ∷ proj₁ (proj₂ (o3split {m} os)) , proj₂ (proj₂ (o3split {m} os))
o3split {m} (o3h₂ ∷ os)  = proj₁ (o3split {m} os) , h₁ ∷ proj₁ (proj₂ (o3split {m} os)) , proj₂ (proj₂ (o3split {m} os))
o3split {m} (o3z₂ ∷ os)  = proj₁ (o3split {m} os) , z₁ ∷ proj₁ (proj₂ (o3split {m} os)) , proj₂ (proj₂ (o3split {m} os))
o3split {m} (o3c₁ ∷ os)  = proj₁ (o3split {m} os) , c₀ ∷ proj₁ (proj₂ (o3split {m} os)) , proj₂ (proj₂ (o3split {m} os))
o3split {m} (o3Z₀ ∷ os)  = proj₁ (o3split {m} os) , proj₁ (proj₂ (o3split {m} os)) , not (proj₂ (proj₂ (o3split {m} os)))
o3split {m} (o3neg ∷ os) = not (proj₁ (o3split {m} os)) , proj₁ (proj₂ (o3split {m} os)) , proj₂ (proj₂ (o3split {m} os))

module Split {m : ℕ} where

  open Width (₁₊ m)
  open Sign {₁₊ m}

  -- The shape the outputs are brought into.
  shape : Bool × List (Gen m) × Bool → Circuit (₁₊ m)
  shape (s , vs , z) = sgn s • ⟪ vs ⟫ ↑ • zpow z

  empty : ε ≈ shape (false , [] , false)
  empty = sym (trans left-unit left-unit)

  -- A letter above wire 0 joins the gates that are done.
  cons-up : (x : Gen m) (s : Bool) (vs : List (Gen m)) (z : Bool) →
            [ x ↥ ]ʷ • shape (s , vs , z) ≈ shape (s , x ∷ vs , z)
  cons-up x s vs z = begin
    [ x ↥ ]ʷ • sgn s • ⟪ vs ⟫ ↑ • zpow z     ≈⟨ sym assoc ⟩
    ([ x ↥ ]ʷ • sgn s) • ⟪ vs ⟫ ↑ • zpow z   ≈⟨ front _ (sym (sgn-comm s _)) ⟩
    (sgn s • [ x ↥ ]ʷ) • ⟪ vs ⟫ ↑ • zpow z   ≈⟨ trans assoc (back _ (sym assoc)) ⟩
    sgn s • ⟪ x ∷ vs ⟫ ↑ • zpow z            ∎

  -- Z on wire 0 passes the gates that are done.
  cons-z : (s : Bool) (vs : List (Gen m)) (z : Bool) →
           Z • shape (s , vs , z) ≈ shape (s , vs , not z)
  cons-z s vs z = begin
    Z • sgn s • ⟪ vs ⟫ ↑ • zpow z         ≈⟨ sym assoc ⟩
    (Z • sgn s) • ⟪ vs ⟫ ↑ • zpow z       ≈⟨ front _ (sym (sgn-comm s Z)) ⟩
    (sgn s • Z) • ⟪ vs ⟫ ↑ • zpow z       ≈⟨ assoc ⟩
    sgn s • Z • ⟪ vs ⟫ ↑ • zpow z         ≈⟨ back _ (sym assoc) ⟩
    sgn s • (Z • ⟪ vs ⟫ ↑) • zpow z       ≈⟨ back _ (front _ zc) ⟩
    sgn s • (⟪ vs ⟫ ↑ • Z) • zpow z       ≈⟨ back _ assoc ⟩
    sgn s • ⟪ vs ⟫ ↑ • Z • zpow z         ≈⟨ back _ (back _ (zpow-z z)) ⟩
    sgn s • ⟪ vs ⟫ ↑ • zpow (not z)       ∎
    where
    zc : Z • ⟪ vs ⟫ ↑ ≈ ⟪ vs ⟫ ↑ • Z
    zc = trans (front _ (sym right-unit))
         (trans (low1s-comm (z₀ ∷ []) Eq.refl ⟪ vs ⟫) (back _ right-unit))

  -- The scalar joins the sign.
  cons-neg : (s : Bool) (vs : List (Gen m)) (z : Bool) →
             neg • shape (s , vs , z) ≈ shape (not s , vs , z)
  cons-neg s vs z = trans (sym assoc) (front _ (sgn-neg s))

o2split-ok : (os : List O2) → (₂₊ m) ⊢ ⟪ concatMap O2l os ⟫ ≈ Split.shape (o2split {m} os)
o2split-ok []          = Split.empty
o2split-ok (oh₁ ∷ os)  = PB.trans (PB.cong PB.refl (o2split-ok os)) (Split.cons-up _ _ _ _)
o2split-ok (oz₁ ∷ os)  = PB.trans (PB.cong PB.refl (o2split-ok os)) (Split.cons-up _ _ _ _)
o2split-ok (oZ₀ ∷ os)  = PB.trans (PB.cong PB.refl (o2split-ok os)) (Split.cons-z _ _ _)
o2split-ok (oneg ∷ os) = PB.trans (PB.cong PB.refl (o2split-ok os)) (Split.cons-neg _ _ _)

o3split-ok : (os : List O3) → (₃₊ m) ⊢ ⟪ concatMap O3l os ⟫ ≈ Split.shape (o3split {m} os)
o3split-ok []           = Split.empty
o3split-ok (o3h₁ ∷ os)  = PB.trans (PB.cong PB.refl (o3split-ok os)) (Split.cons-up _ _ _ _)
o3split-ok (o3z₁ ∷ os)  = PB.trans (PB.cong PB.refl (o3split-ok os)) (Split.cons-up _ _ _ _)
o3split-ok (o3h₂ ∷ os)  = PB.trans (PB.cong PB.refl (o3split-ok os)) (Split.cons-up _ _ _ _)
o3split-ok (o3z₂ ∷ os)  = PB.trans (PB.cong PB.refl (o3split-ok os)) (Split.cons-up _ _ _ _)
o3split-ok (o3c₁ ∷ os)  = PB.trans (PB.cong PB.refl (o3split-ok os)) (Split.cons-up _ _ _ _)
o3split-ok (o3Z₀ ∷ os)  = PB.trans (PB.cong PB.refl (o3split-ok os)) (Split.cons-z _ _ _)
o3split-ok (o3neg ∷ os) = PB.trans (PB.cong PB.refl (o3split-ok os)) (Split.cons-neg _ _ _)

module DSteps {m : ℕ} where

  open Width (₂₊ m)
  open Sign {₂₊ m}

  -- A D gate meets Z coming down from above.
  dz : (d : DT) (z : Bool) → ⟪ Dl d ⟫ • zpow z ↑ ≈ zpow z • ⟪ Dl d ⟫
  dz d false = trans right-unit (sym left-unit)
  dz d true  = trans (back _ (sym right-unit))
    (trans (rule→ {xs = Dl d} {gs = z₁ ∷ []} {ys = z₀ ∷ []} {xs' = Dl d} (ruleZ1D-ok d))
           (front _ right-unit))

  -- A D gate passes what came out of the ladder above.
  slide : (d : DT) (s : Bool) (vs : List (Gen m)) (z : Bool) (r : Circuit (₂₊ m)) →
          ⟪ Dl d ⟫ • sgn s ↑ • ⟪ vs ⟫ ↑ ↑ • zpow z ↑ • r ≈ sgn s • ⟪ map _↥ vs ⟫ ↑ • zpow z • ⟪ Dl d ⟫ • r
  slide d s vs z r = begin
    ⟪ Dl d ⟫ • sgn s ↑ • ⟪ vs ⟫ ↑ ↑ • zpow z ↑ • r    ≈⟨ back _ (front _ (sgn↑ s)) ⟩
    ⟪ Dl d ⟫ • sgn s • ⟪ vs ⟫ ↑ ↑ • zpow z ↑ • r      ≈⟨ swap _ (sym (sgn-comm s _)) ⟩
    sgn s • ⟪ Dl d ⟫ • ⟪ vs ⟫ ↑ ↑ • zpow z ↑ • r      ≈⟨ back _ (swap _ (low2s-comm (Dl d) (Dl-low2 d) ⟪ vs ⟫)) ⟩
    sgn s • ⟪ vs ⟫ ↑ ↑ • ⟪ Dl d ⟫ • zpow z ↑ • r      ≈⟨ back _ (back _ (pair _ (dz d z))) ⟩
    sgn s • ⟪ vs ⟫ ↑ ↑ • zpow z • ⟪ Dl d ⟫ • r        ≈⟨ back _ (front _ (sym (lift (⟪↑⟫ vs)))) ⟩
    sgn s • ⟪ map _↥ vs ⟫ ↑ • zpow z • ⟪ Dl d ⟫ • r   ∎

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
  dout (proj₁ (o2split {m} os)) (proj₁ (proj₂ (o2split {m} os))) (proj₂ (proj₂ (o2split {m} os))) (d' ∷ᴰ dl) p
  where
  open Width (₂₊ m)
  p = begin
    (⟪ Dl d ⟫ • ⟦ dl ⟧ᴰ ↑) • ⟪ g ⟫           ≈⟨ trans assoc (back _ c) ⟩
    ⟪ Dl d ⟫ • ⟪ g ⟫ • ⟦ dl ⟧ᴰ ↑             ≈⟨ sym assoc ⟩
    (⟪ Dl d ⟫ • ⟪ g ⟫) • ⟦ dl ⟧ᴰ ↑           ≈⟨ DSteps.meet d d' g os _ e ⟩
    Split.shape (o2split {m} os) • ⟪ Dl d' ⟫ • ⟦ dl ⟧ᴰ ↑   ≈⟨ trans assoc (back _ assoc) ⟩
    _ ∎

dPush : (m : ℕ) (dl : DL (₁₊ m)) (g : MIn (₁₊ m)) → DOut m (⟦ dl ⟧ᴰ • ⟪ Ml g ⟫)
dPush m dl mneg = dout true [] false dl
  (trans (back _ right-unit) (trans (sym (neg-comm _)) (back _ (sym (trans left-unit left-unit)))))
  where open Width (₁₊ m)
dPush zero []ᴰ mZt = dout false [] true []ᴰ (PP.by-assoc (1 VRel,_===_) Eq.refl)
dPush (suc m) (d ∷ᴰ dl) (mup g) with dPush m dl g
... | dout s vs z dl' e = dout s (map _↥ vs) z (d ∷ᴰ dl') p
  where
  open Width (₂₊ m)
  p = begin
    (⟪ Dl d ⟫ • ⟦ dl ⟧ᴰ ↑) • ⟪ map _↥ (Ml g) ⟫        ≈⟨ trans assoc (back _ (back _ (⟪↑⟫ (Ml g)))) ⟩
    ⟪ Dl d ⟫ • (⟦ dl ⟧ᴰ • ⟪ Ml g ⟫) ↑                 ≈⟨ back _ (lift e) ⟩
    ⟪ Dl d ⟫ • (sgn s • ⟪ vs ⟫ ↑ • zpow z • ⟦ dl' ⟧ᴰ) ↑ ≈⟨ DSteps.slide d s vs z _ ⟩
    sgn s • ⟪ map _↥ vs ⟫ ↑ • zpow z • ⟪ Dl d ⟫ • ⟦ dl' ⟧ᴰ ↑ ∎
dPush (suc m) (d ∷ᴰ dl) mH = dStep m d dl (h₀ ∷ []) (proj₁ (ruleD d gH)) (proj₂ (ruleD d gH))
  (PB.sym (low1s-comm (h₀ ∷ []) Eq.refl ⟦ dl ⟧ᴰ))
  (rule→ {xs = Dl d} {gs = h₀ ∷ []} {ys = concatMap O2l (proj₂ (ruleD d gH))} {xs' = Dl (proj₁ (ruleD d gH))} (ruleD-ok d gH))
dPush (suc m) (d ∷ᴰ dl) mZ = dStep m d dl (z₀ ∷ []) (proj₁ (ruleD d gZ)) (proj₂ (ruleD d gZ))
  (PB.sym (low1s-comm (z₀ ∷ []) Eq.refl ⟦ dl ⟧ᴰ))
  (rule→ {xs = Dl d} {gs = z₀ ∷ []} {ys = concatMap O2l (proj₂ (ruleD d gZ))} {xs' = Dl (proj₁ (ruleD d gZ))} (ruleD-ok d gZ))
dPush (suc zero) (d ∷ᴰ []ᴰ) mC = dStep zero d []ᴰ (c₀ ∷ []) (proj₁ (ruleCD d)) (proj₂ (ruleCD d))
  (PB.trans PB.left-unit (PB.sym PB.right-unit))
  (rule→ {xs = Dl d} {gs = c₀ ∷ []} {ys = concatMap O2l (proj₂ (ruleCD d))} {xs' = Dl (proj₁ (ruleCD d))} (ruleCD-ok d))
dPush (suc (suc m)) (d ∷ᴰ d₁ ∷ᴰ dl) mC =
  dout (proj₁ sp) (proj₁ (proj₂ sp)) (proj₂ (proj₂ sp)) (d₀' ∷ᴰ d₁' ∷ᴰ dl) p
  where
  open Width (₃₊ m)
  r   = ruleDD d₁ d
  d₁' = proj₁ r
  d₀' = proj₁ (proj₂ r)
  os  = proj₂ (proj₂ r)
  sp  = o3split os
  e₃ : ⟪ Dl d ⟫ • ⟪ Dl d₁ ⟫ ↑ • ⟪ c₀ ∷ [] ⟫ ≈ ⟪ concatMap O3l os ⟫ • ⟪ Dl d₀' ⟫ • ⟪ Dl d₁' ⟫ ↑
  e₃ = trans (back _ (front _ (sym (⟪↑⟫ (Dl d₁)))))
       (trans (rule3→ (ruleDD-ok d₁ d)) (back _ (back _ (⟪↑⟫ (Dl d₁')))))
  p = begin
    (⟪ Dl d ⟫ • (⟪ Dl d₁ ⟫ ↑ • ⟦ dl ⟧ᴰ ↑ ↑)) • ⟪ c₀ ∷ [] ⟫      ≈⟨ trans assoc (back _ assoc) ⟩
    ⟪ Dl d ⟫ • ⟪ Dl d₁ ⟫ ↑ • ⟦ dl ⟧ᴰ ↑ ↑ • ⟪ c₀ ∷ [] ⟫          ≈⟨ back _ (back _ (sym (low2s-comm (c₀ ∷ []) Eq.refl ⟦ dl ⟧ᴰ))) ⟩
    ⟪ Dl d ⟫ • ⟪ Dl d₁ ⟫ ↑ • ⟪ c₀ ∷ [] ⟫ • ⟦ dl ⟧ᴰ ↑ ↑          ≈⟨ trans (back _ (sym assoc)) (sym assoc) ⟩
    (⟪ Dl d ⟫ • ⟪ Dl d₁ ⟫ ↑ • ⟪ c₀ ∷ [] ⟫) • ⟦ dl ⟧ᴰ ↑ ↑        ≈⟨ front _ e₃ ⟩
    (⟪ concatMap O3l os ⟫ • ⟪ Dl d₀' ⟫ • ⟪ Dl d₁' ⟫ ↑) • ⟦ dl ⟧ᴰ ↑ ↑   ≈⟨ front _ (front _ (o3split-ok os)) ⟩
    (Split.shape sp • ⟪ Dl d₀' ⟫ • ⟪ Dl d₁' ⟫ ↑) • ⟦ dl ⟧ᴰ ↑ ↑        ≈⟨ trans assoc (trans (back _ assoc) (trans assoc (back _ assoc))) ⟩
    _ ∎

-- An X-circuit: the E gate absorbs the Z that comes down.
record XOut (m : ℕ) (lhs : Circuit (₁₊ m)) : Set where
  constructor xout
  field
    s  : Bool
    vs : List (Gen m)
    M  : Xc (₁₊ m)
    ok : (₁₊ m) ⊢ lhs ≈ sgn s • ⟪ vs ⟫ ↑ • ⟦ M ⟧ˣ

eflip : Bool → ET → ET
eflip false e = e
eflip true  e = ruleE e

Ez : (e : ET) (z : Bool) → (₁₊ m) ⊢ ⟪ El e ⟫ • zpow z ≈ ⟪ El (eflip z e) ⟫
Ez e false = PB.right-unit
Ez e true  = PB.trans (PB.cong PB.refl (PB.sym PB.right-unit))
             (PB.trans (PB.sym (⟪++⟫ (El e) (z₀ ∷ []))) (ruleE-ok e))

xPush : (m : ℕ) (M : Xc (₁₊ m)) (g : MIn (₁₊ m)) → XOut m (⟦ M ⟧ˣ • ⟪ Ml g ⟫)
xPush m (e ,ˣ dl) g with dPush m dl g
... | dout s vs z dl' ok = xout s vs (eflip z e ,ˣ dl') p
  where
  open Width (₁₊ m)
  open Sign {₁₊ m}
  p = begin
    (⟪ El e ⟫ • ⟦ dl ⟧ᴰ) • ⟪ Ml g ⟫                          ≈⟨ trans assoc (back _ ok) ⟩
    ⟪ El e ⟫ • sgn s • ⟪ vs ⟫ ↑ • zpow z • ⟦ dl' ⟧ᴰ          ≈⟨ swap _ (sym (sgn-comm s _)) ⟩
    sgn s • ⟪ El e ⟫ • ⟪ vs ⟫ ↑ • zpow z • ⟦ dl' ⟧ᴰ          ≈⟨ back _ (swap _ (low1s-comm (El e) (El-low1 e) ⟪ vs ⟫)) ⟩
    sgn s • ⟪ vs ⟫ ↑ • ⟪ El e ⟫ • zpow z • ⟦ dl' ⟧ᴰ          ≈⟨ back _ (back _ (trans (sym assoc) (front _ (Ez e z)))) ⟩
    sgn s • ⟪ vs ⟫ ↑ • ⟪ El (eflip z e) ⟫ • ⟦ dl' ⟧ᴰ         ∎

xPushL : (m : ℕ) (M : Xc (₁₊ m)) (ds : List (MIn (₁₊ m))) → XOut m (⟦ M ⟧ˣ • ⟪ Mls ds ⟫)
xPushL m M [] = xout false [] M (trans right-unit (sym (trans left-unit left-unit)))
  where open Width (₁₊ m)
xPushL m M (d ∷ ds) with xPush m M d
... | xout s₁ vs₁ M₁ e₁ with xPushL m M₁ ds
... | xout s₂ vs₂ M₂ e₂ = xout (s₁ xor s₂) (vs₁ ++ vs₂) M₂ p
  where
  open Width (₁₊ m)
  open Sign {₁₊ m}
  p = begin
    ⟦ M ⟧ˣ • ⟪ Ml d ++ Mls ds ⟫                               ≈⟨ trans (back _ (⟪++⟫ (Ml d) (Mls ds))) (sym assoc) ⟩
    (⟦ M ⟧ˣ • ⟪ Ml d ⟫) • ⟪ Mls ds ⟫                           ≈⟨ front _ e₁ ⟩
    (sgn s₁ • ⟪ vs₁ ⟫ ↑ • ⟦ M₁ ⟧ˣ) • ⟪ Mls ds ⟫                ≈⟨ trans assoc (back _ assoc) ⟩
    sgn s₁ • ⟪ vs₁ ⟫ ↑ • ⟦ M₁ ⟧ˣ • ⟪ Mls ds ⟫                  ≈⟨ back _ (back _ e₂) ⟩
    sgn s₁ • ⟪ vs₁ ⟫ ↑ • sgn s₂ • ⟪ vs₂ ⟫ ↑ • ⟦ M₂ ⟧ˣ         ≈⟨ back _ (swap _ (sym (sgn-comm s₂ _))) ⟩
    sgn s₁ • sgn s₂ • ⟪ vs₁ ⟫ ↑ • ⟪ vs₂ ⟫ ↑ • ⟦ M₂ ⟧ˣ         ≈⟨ trans (sym assoc) (front _ (sgn-xor s₁ s₂)) ⟩
    sgn (s₁ xor s₂) • ⟪ vs₁ ⟫ ↑ • ⟪ vs₂ ⟫ ↑ • ⟦ M₂ ⟧ˣ         ≈⟨ back _ (trans (sym assoc) (front _ (lift (PB.sym (⟪++⟫ vs₁ vs₂))))) ⟩
    sgn (s₁ xor s₂) • ⟪ vs₁ ++ vs₂ ⟫ ↑ • ⟦ M₂ ⟧ˣ              ∎

------------------------------------------------------------------------
-- Pushing into normal forms

push  : (n : ℕ) (N : NF n) (g : Gen n) → Σ (NF n) λ N' → n ⊢ ⟦ N ⟧ⁿ • ⟪ g ∷ [] ⟫ ≈ ⟦ N' ⟧ⁿ
pushW : (n : ℕ) (N : NF n) (gs : List (Gen n)) → Σ (NF n) λ N' → n ⊢ ⟦ N ⟧ⁿ • ⟪ gs ⟫ ≈ ⟦ N' ⟧ⁿ

push zero (nf₀ s) (gate₀ neg-gate) = nf₀ (not s) ,
  PB.trans (PB.cong PB.refl PB.right-unit) (PB.trans (Sign.sgn-comm s neg) (Sign.sgn-neg s))
push (suc m) (nfₛ s L M N) g with zPush m L g
... | out ds L' e₁ with xPushL m M ds
... | xout s₁ vs M' e₂ with pushW m N vs
... | N' , e₃ = nfₛ (s xor s₁) L' M' N' , p
  where
  open Width (₁₊ m)
  open Sign {₁₊ m}
  p = begin
    (sgn s • ⟦ N ⟧ⁿ ↑ • ⟦ M ⟧ˣ • ⟦ L ⟧ᶻ) • ⟪ g ∷ [] ⟫          ≈⟨ trans assoc (back _ (trans assoc (back _ assoc))) ⟩
    sgn s • ⟦ N ⟧ⁿ ↑ • ⟦ M ⟧ˣ • ⟦ L ⟧ᶻ • ⟪ g ∷ [] ⟫            ≈⟨ back _ (back _ (back _ e₁)) ⟩
    sgn s • ⟦ N ⟧ⁿ ↑ • ⟦ M ⟧ˣ • ⟪ Mls ds ⟫ • ⟦ L' ⟧ᶻ          ≈⟨ back _ (back _ (sym assoc)) ⟩
    sgn s • ⟦ N ⟧ⁿ ↑ • (⟦ M ⟧ˣ • ⟪ Mls ds ⟫) • ⟦ L' ⟧ᶻ        ≈⟨ back _ (back _ (front _ e₂)) ⟩
    sgn s • ⟦ N ⟧ⁿ ↑ • (sgn s₁ • ⟪ vs ⟫ ↑ • ⟦ M' ⟧ˣ) • ⟦ L' ⟧ᶻ ≈⟨ back _ (back _ (trans assoc (back _ assoc))) ⟩
    sgn s • ⟦ N ⟧ⁿ ↑ • sgn s₁ • ⟪ vs ⟫ ↑ • ⟦ M' ⟧ˣ • ⟦ L' ⟧ᶻ  ≈⟨ back _ (swap _ (sym (sgn-comm s₁ _))) ⟩
    sgn s • sgn s₁ • ⟦ N ⟧ⁿ ↑ • ⟪ vs ⟫ ↑ • ⟦ M' ⟧ˣ • ⟦ L' ⟧ᶻ  ≈⟨ trans (sym assoc) (front _ (sgn-xor s s₁)) ⟩
    sgn (s xor s₁) • ⟦ N ⟧ⁿ ↑ • ⟪ vs ⟫ ↑ • ⟦ M' ⟧ˣ • ⟦ L' ⟧ᶻ  ≈⟨ back _ (trans (sym assoc) (front _ (lift e₃))) ⟩
    sgn (s xor s₁) • ⟦ N' ⟧ⁿ ↑ • ⟦ M' ⟧ˣ • ⟦ L' ⟧ᶻ            ∎

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

lad₁ : (m : ℕ) → Lad sg (₁₊ m)
lad₁ zero    = top C₁
lad₁ (suc m) = B₁ ∷ᴮ lad₁ m

dl₁ : (m : ℕ) → DL (₁₊ m)
dl₁ zero    = []ᴰ
dl₁ (suc m) = D₁ ∷ᴰ dl₁ m

idNF : (n : ℕ) → NF n
idNF zero    = nf₀ false
idNF (suc m) = nfₛ false (at A₁ (lad₁ m)) (E₁ ,ˣ dl₁ m) (idNF m)

-- D₁ undoes B₁.
D₁B₁ : (₂₊ m) ⊢ ⟪ Dl D₁ ⟫ • ⟪ Bl B₁ ⟫ ≈ ε
D₁B₁ = PB.trans (PB.cong (perm-sound (Dl D₁) (rev (Bl B₁)) Eq.refl) PB.refl) (rev-inv (Bl B₁))

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
  ε • ⟦ idNF m ⟧ⁿ ↑ • (ε • ⟦ dl₁ m ⟧ᴰ) • (⟦ lad₁ m ⟧ᴸ • ε)   ≈⟨ trans left-unit (front _ (lift (idNF-ok m))) ⟩
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
