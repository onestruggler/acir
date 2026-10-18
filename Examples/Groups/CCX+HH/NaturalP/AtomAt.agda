------------------------------------------------------------------------
-- Presentations of groups
--
-- The auxiliary atoms at their points.
--
-- An atom of GeneralN/DecodingPlans — a sign pair `MM`, a double
-- exchange `XX`, a mixed block `J` — moves at most four coordinates.
-- Listed in a suitable order, those coordinates are an injection π
-- from Fin m (m = 2, 3, 4), and on them the atom acts as one of a few
-- fixed words on m coordinates (`GMM`, `GXX`, the four three-point
-- exchanges `GXa` … `GXd`, `GJ`).  The order is chosen so that every
-- exchange and K of the atom has its indices increasing along π; π is
-- then any injection, increasing or not (AtCalc's `AtI`).  `pt2`,
-- `pt3`, `pt4` list given coordinates, injectively when they are
-- distinct (`inj2`, `inj3`, `inj4`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.AtomAt where

open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Nat.Base using (ℕ ; z≤n ; s≤s)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; refl ; sym)
open import Word.Base using (_•_)

open import Examples.Groups.CCX+HH-TwoLevel.Semantics using (actVʷ)
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as U
open import Examples.Groups.CCX+HH.GeneralN.DecodingPlans using (Atom ; MM ; XX ; J ; e)
open import Examples.Groups.CCX+HH.NaturalP.AtCalc
  using (Op ; AtI ; Inj ; atI-• ; atI-M ; atI-X ; atI-K)

private
  variable
    N : ℕ

------------------------------------------------------------------------
-- Listing points

pt2 : Fin N → Fin N → Fin 2 → Fin N
pt2 a b zero       = a
pt2 a b (suc zero) = b

pt3 : Fin N → Fin N → Fin N → Fin 3 → Fin N
pt3 a b c zero             = a
pt3 a b c (suc zero)       = b
pt3 a b c (suc (suc zero)) = c

pt4 : Fin N → Fin N → Fin N → Fin N → Fin 4 → Fin N
pt4 a b c d zero                   = a
pt4 a b c d (suc zero)             = b
pt4 a b c d (suc (suc zero))       = c
pt4 a b c d (suc (suc (suc zero))) = d

inj2 : {a b : Fin N} → a ≢ b → Inj (pt2 a b)
inj2 ab {zero}     {zero}     e = refl
inj2 ab {zero}     {suc zero} e = ⊥-elim (ab e)
inj2 ab {suc zero} {zero}     e = ⊥-elim (ab (sym e))
inj2 ab {suc zero} {suc zero} e = refl

inj3 : {a b c : Fin N} → a ≢ b → a ≢ c → b ≢ c → Inj (pt3 a b c)
inj3 ab ac bc {zero}           {zero}           e = refl
inj3 ab ac bc {zero}           {suc zero}       e = ⊥-elim (ab e)
inj3 ab ac bc {zero}           {suc (suc zero)} e = ⊥-elim (ac e)
inj3 ab ac bc {suc zero}       {zero}           e = ⊥-elim (ab (sym e))
inj3 ab ac bc {suc zero}       {suc zero}       e = refl
inj3 ab ac bc {suc zero}       {suc (suc zero)} e = ⊥-elim (bc e)
inj3 ab ac bc {suc (suc zero)} {zero}           e = ⊥-elim (ac (sym e))
inj3 ab ac bc {suc (suc zero)} {suc zero}       e = ⊥-elim (bc (sym e))
inj3 ab ac bc {suc (suc zero)} {suc (suc zero)} e = refl

inj4 : {a b c d : Fin N} → a ≢ b → a ≢ c → a ≢ d → b ≢ c → b ≢ d → c ≢ d → Inj (pt4 a b c d)
inj4 ab ac ad bc bd cd {zero}                 {zero}                 e = refl
inj4 ab ac ad bc bd cd {zero}                 {suc zero}             e = ⊥-elim (ab e)
inj4 ab ac ad bc bd cd {zero}                 {suc (suc zero)}       e = ⊥-elim (ac e)
inj4 ab ac ad bc bd cd {zero}                 {suc (suc (suc zero))} e = ⊥-elim (ad e)
inj4 ab ac ad bc bd cd {suc zero}             {zero}                 e = ⊥-elim (ab (sym e))
inj4 ab ac ad bc bd cd {suc zero}             {suc zero}             e = refl
inj4 ab ac ad bc bd cd {suc zero}             {suc (suc zero)}       e = ⊥-elim (bc e)
inj4 ab ac ad bc bd cd {suc zero}             {suc (suc (suc zero))} e = ⊥-elim (bd e)
inj4 ab ac ad bc bd cd {suc (suc zero)}       {zero}                 e = ⊥-elim (ac (sym e))
inj4 ab ac ad bc bd cd {suc (suc zero)}       {suc zero}             e = ⊥-elim (bc (sym e))
inj4 ab ac ad bc bd cd {suc (suc zero)}       {suc (suc zero)}       e = refl
inj4 ab ac ad bc bd cd {suc (suc zero)}       {suc (suc (suc zero))} e = ⊥-elim (cd e)
inj4 ab ac ad bc bd cd {suc (suc (suc zero))} {zero}                 e = ⊥-elim (ad (sym e))
inj4 ab ac ad bc bd cd {suc (suc (suc zero))} {suc zero}             e = ⊥-elim (bd (sym e))
inj4 ab ac ad bc bd cd {suc (suc (suc zero))} {suc (suc zero)}       e = ⊥-elim (cd (sym e))
inj4 ab ac ad bc bd cd {suc (suc (suc zero))} {suc (suc (suc zero))} e = refl

------------------------------------------------------------------------
-- The canonical words

private
  0<1 : _<_ {3} {3} zero (suc zero)
  0<1 = s≤s z≤n
  0<2 : _<_ {3} {3} zero (suc (suc zero))
  0<2 = s≤s z≤n
  1<2 : _<_ {3} {3} (suc zero) (suc (suc zero))
  1<2 = s≤s (s≤s z≤n)
  f01 : _<_ {4} {4} zero (suc zero)
  f01 = s≤s z≤n
  f12 : _<_ {4} {4} (suc zero) (suc (suc zero))
  f12 = s≤s (s≤s z≤n)
  f23 : _<_ {4} {4} (suc (suc zero)) (suc (suc (suc zero)))
  f23 = s≤s (s≤s (s≤s z≤n))

GMM : Op 2
GMM = actVʷ (U.M zero • U.M (suc zero))

GXX : Op 4
GXX = actVʷ (U.X zero (suc zero) f01 • U.X (suc (suc zero)) (suc (suc (suc zero))) f23)

-- X[0,1] X[0,2], X[0,2] X[1,2], X[1,2] X[0,1], X[0,1] X[1,2].
GXa GXb GXc GXd : Op 3
GXa = actVʷ (U.X zero (suc zero) 0<1 • U.X zero (suc (suc zero)) 0<2)
GXb = actVʷ (U.X zero (suc (suc zero)) 0<2 • U.X (suc zero) (suc (suc zero)) 1<2)
GXc = actVʷ (U.X (suc zero) (suc (suc zero)) 1<2 • U.X zero (suc zero) 0<1)
GXd = actVʷ (U.X zero (suc zero) 0<1 • U.X (suc zero) (suc (suc zero)) 1<2)

GJ : Op 4
GJ = actVʷ ((U.M zero • U.X (suc zero) (suc (suc zero)) f12)
  • U.K zero (suc zero) (suc (suc zero)) (suc (suc (suc zero))) f01 f12 f23)

------------------------------------------------------------------------
-- The atoms at their points

module _ {N : ℕ} (π : Fin 2 → Fin N) (inj : Inj π) where

  atMM : AtI π GMM (actVʷ (e (MM (π zero) (π (suc zero)))))
  atMM = atI-• (atI-M π inj zero) (atI-M π inj (suc zero))

module _ {N : ℕ} (π : Fin 4 → Fin N) (inj : Inj π) where

  atXX : .(p : π zero < π (suc zero)) .(q : π (suc (suc zero)) < π (suc (suc (suc zero)))) →
    AtI π GXX (actVʷ (e (XX (π zero) (π (suc zero)) (π (suc (suc zero))) (π (suc (suc (suc zero)))) p q)))
  atXX p q = atI-• (atI-X π inj zero (suc zero) f01 p)
    (atI-X π inj (suc (suc zero)) (suc (suc (suc zero))) f23 q)

  atJ : .(p : π zero < π (suc zero)) .(q : π (suc zero) < π (suc (suc zero)))
    .(r : π (suc (suc zero)) < π (suc (suc (suc zero)))) →
    AtI π GJ (actVʷ (e (J (π zero) (π (suc zero)) (π (suc (suc zero))) (π (suc (suc (suc zero)))) p q r)))
  atJ p q r = atI-• (atI-• (atI-M π inj zero) (atI-X π inj (suc zero) (suc (suc zero)) f12 q))
    (atI-K π inj zero (suc zero) (suc (suc zero)) (suc (suc (suc zero))) f01 f12 f23 p q r)

module _ {N : ℕ} (π : Fin 3 → Fin N) (inj : Inj π) where

  private
    a = π zero
    b = π (suc zero)
    c = π (suc (suc zero))

  -- X[a,b] X[a,c].
  atXa : .(p : a < b) .(q : a < c) → AtI π GXa (actVʷ (e (XX a b a c p q)))
  atXa p q = atI-• (atI-X π inj zero (suc zero) 0<1 p) (atI-X π inj zero (suc (suc zero)) 0<2 q)

  -- X[a,c] X[b,c].
  atXb : .(p : a < c) .(q : b < c) → AtI π GXb (actVʷ (e (XX a c b c p q)))
  atXb p q = atI-• (atI-X π inj zero (suc (suc zero)) 0<2 p)
    (atI-X π inj (suc zero) (suc (suc zero)) 1<2 q)

  -- X[b,c] X[a,b].
  atXc : .(p : b < c) .(q : a < b) → AtI π GXc (actVʷ (e (XX b c a b p q)))
  atXc p q = atI-• (atI-X π inj (suc zero) (suc (suc zero)) 1<2 p)
    (atI-X π inj zero (suc zero) 0<1 q)

  -- X[a,b] X[b,c].
  atXd : .(p : a < b) .(q : b < c) → AtI π GXd (actVʷ (e (XX a b b c p q)))
  atXd p q = atI-• (atI-X π inj zero (suc zero) 0<1 p)
    (atI-X π inj (suc zero) (suc (suc zero)) 1<2 q)
