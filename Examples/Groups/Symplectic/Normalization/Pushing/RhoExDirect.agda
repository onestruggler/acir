------------------------------------------------------------------------
-- Presentations of groups
--
-- The residual half of the action of Ex (direct computation).
--
-- ExAction computes the COSET half: Ex transposes the two bottom D
-- boxes.  `≋` also constrains the emitted residual, and that is what
-- this module computes.
--
-- Ex = (CZ • H ↓ • H ↑) ^ 3 and `resid` fuses over `•` definitionally
-- (SyllableAction.resid-•), so the residual of Ex is the nine-factor
-- concatenation of the per-letter residuals, each read off a PushML.ract
-- clause:
--
--   CZ  : DDCZ.dir-of (d₁ ∷ d₂ ∷ []) ↓ᵏ m     (wires 0,1)
--   H ↓ : Hdir d₁ ↓ᵏ (₁₊ m)                   (wire 0)
--   H ↑ : (Hdir d₂ ↓ᵏ m) ↑                    (wire 1)
--
-- with the boxes updated between letters by the coset trajectory of
-- ExAction.round-step'.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations

module Examples.Groups.Symplectic.Normalization.Pushing.RhoExDirect
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) where

open import Examples.Groups.Symplectic.Normalization.Section p-2 p-prime

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.Vec using (Vec ; _∷_ ; [])
open import Data.Fin using (Fin)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

open import Word.Base
import Presentation.Base as PB

open import Examples.Groups.Symplectic.Syntactics p-2 p-prime
open Symplectic renaming (M to ZM)

open import Zp.ModularArithmetic
open PrimeModulus p-2 p-prime

open import Examples.Groups.Symplectic.Normalization.Pushing.DVecPush p-2 p-prime
  using (Hdir ; Hd')
import Examples.Groups.Symplectic.BR.Three.DD-CZ p-2 p-prime as DDCZ
open import Examples.Groups.Symplectic.Normalization.Pushing.SrelWDBase p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.SyllableAction p-2 p-prime
open import Examples.Groups.Symplectic.Normalization.Pushing.ExAction p-2 p-prime
  using (Hd'-eq ; neg-shift)

open import Algebra.Properties.Ring (+-*-ring p-2) using (-0#≈0#)

------------------------------------------------------------------------
-- Named closed forms for the two escape tables.
--
-- Both `Hdir` and `DDCZ.dir-of` are case splits on the zero-ness of the
-- a-components; the degenerate branches are used all over the Pushing
-- directory by definitional reduction but have never been named.  All
-- of these hold by `refl`.

Hdir-00 : Hdir (₀ , ₀) ≡ H
Hdir-00 = Eq.refl

Hdir-0b : ∀ (b : Fin (₁₊ p-2)) → Hdir (₀ , ₁₊ b) ≡ ε
Hdir-0b b = Eq.refl

Hdir-a0 : ∀ (a : Fin (₁₊ p-2)) → Hdir (₁₊ a , ₀) ≡ HH
Hdir-a0 a = Eq.refl

-- `DDCZ.dir-of` inspects ONLY the a-components; the b's are ignored.
ddir-00 : ∀ (b d : ℤ ₚ) → DDCZ.dir-of ((₀ , b) ∷ (₀ , d) ∷ []) ≡ CZ
ddir-00 b d = Eq.refl

ddir-0c : ∀ (b : ℤ ₚ) (c : Fin (₁₊ p-2)) (d : ℤ ₚ) →
  DDCZ.dir-of ((₀ , b) ∷ (₁₊ c , d) ∷ []) ≡ XC'
ddir-0c b c d = Eq.refl

ddir-a0 : ∀ (a : Fin (₁₊ p-2)) (b d : ℤ ₚ) →
  DDCZ.dir-of ((₁₊ a , b) ∷ (₀ , d) ∷ []) ≡ CX'
ddir-a0 a b d = Eq.refl

module _ {m : ℕ} where

------------------------------------------------------------------------
-- The residual of one round.
--
-- CZ escapes on wires 0,1; then the wire-0 H sees the CZ-updated bottom
-- box, and the wire-1 H the CZ-updated second box.  Note the two H
-- escapes have DIFFERENT widening shapes: `↓ᵏ (₁₊ m)` on wire 0, but
-- `(_ ↓ᵏ m) ↑` on wire 1.

  ρ-round : D → D → Circuit (₂₊ m)
  ρ-round d1 d2 =
    (DDCZ.dir-of (d1 ∷ d2 ∷ []) ↓ᵏ m)
    • ((Hdir (proj₁ d1 , proj₂ d1 + - proj₁ d2) ↓ᵏ (₁₊ m))
      • ((Hdir (proj₁ d2 , proj₂ d2 + - proj₁ d1) ↓ᵏ m) ↑))

  resid-round : ∀ (d1 d2 : D) (lm : C (₁₊ m)) →
    resid (₂₊ m) (inj₂ (d1 , inj₂ (d2 , lm))) (CZ • H ↓ • H ↑)
    ≡ ρ-round d1 d2
  resid-round d1 d2 lm = Eq.refl

------------------------------------------------------------------------
-- The coset trajectory of one round, named.
--
-- (ExAction.round-step restated so the two box updates have names that
-- can be iterated.)

  nxt₁ : D → D → D
  nxt₁ d1 d2 = Hd' (proj₁ d1 , proj₂ d1 + - proj₁ d2)

  nxt₂ : D → D → D
  nxt₂ d1 d2 = Hd' (proj₁ d2 , proj₂ d2 + - proj₁ d1)

  step-round : ∀ (d1 d2 : D) (lm : C (₁₊ m)) →
    step (₂₊ m) (inj₂ (d1 , inj₂ (d2 , lm))) (CZ • H ↓ • H ↑)
    ≡ inj₂ (nxt₁ d1 d2 , inj₂ (nxt₂ d1 d2 , lm))
  step-round d1 d2 lm = Eq.refl

------------------------------------------------------------------------
-- The nine-factor flat residual of Ex.
--
-- `Ex` is right-nested (`_•_` is infixr), and `resid` fuses over `•` by
-- refl, so the residual is the right-nested concatenation of the nine
-- per-letter escapes in the order emitted.  The intermediate boxes are
-- the *unreduced* `Hd'`-applications the fold produces — `Hd'` only
-- computes after a case split, which is why this form is refl-provable
-- while the (a,b)-normalised one below is not.

  ρ-flat : D → D → Circuit (₂₊ m)
  ρ-flat d1 d2 =
      (DDCZ.dir-of (d1 ∷ d2 ∷ []) ↓ᵏ m)
    • (Hdir (proj₁ d1 , proj₂ d1 + - proj₁ d2) ↓ᵏ (₁₊ m))
    • ((Hdir (proj₁ d2 , proj₂ d2 + - proj₁ d1) ↓ᵏ m) ↑)
    • (DDCZ.dir-of (e1 ∷ e2 ∷ []) ↓ᵏ m)
    • (Hdir (proj₁ e1 , proj₂ e1 + - proj₁ e2) ↓ᵏ (₁₊ m))
    • ((Hdir (proj₁ e2 , proj₂ e2 + - proj₁ e1) ↓ᵏ m) ↑)
    • (DDCZ.dir-of (f1 ∷ f2 ∷ []) ↓ᵏ m)
    • (Hdir (proj₁ f1 , proj₂ f1 + - proj₁ f2) ↓ᵏ (₁₊ m))
    • ((Hdir (proj₁ f2 , proj₂ f2 + - proj₁ f1) ↓ᵏ m) ↑)
    where
    e1 = nxt₁ d1 d2
    e2 = nxt₂ d1 d2
    f1 = nxt₁ e1 e2
    f2 = nxt₂ e1 e2

  resid-Ex-flat : ∀ (d1 d2 : D) (lm : C (₁₊ m)) →
    resid (₂₊ m) (inj₂ (d1 , inj₂ (d2 , lm))) Ex ≡ ρ-flat d1 d2
  resid-Ex-flat d1 d2 lm = Eq.refl

------------------------------------------------------------------------
-- The same, grouped into three rounds.

  ρ3 : D → D → D → D → D → D → Circuit (₂₊ m)
  ρ3 d1 d2 e1 e2 f1 f2 = ρ-round d1 d2 • ρ-round e1 e2 • ρ-round f1 f2

  ρ-rounds3 : D → D → Circuit (₂₊ m)
  ρ-rounds3 d1 d2 = ρ3 d1 d2 e1 e2 (nxt₁ e1 e2) (nxt₂ e1 e2)
    where
    e1 = nxt₁ d1 d2
    e2 = nxt₂ d1 d2

------------------------------------------------------------------------
-- Regrouping the flat nine into three rounds is pure associativity.

  open PB ((₂₊ m) QRel,_===_)
    using (_≈_ ; sym ; trans ; assoc ; refl' ; cright_)

  shift3 : {w v u z : Circuit (₂₊ m)} → w • (v • (u • z)) ≈ (w • (v • u)) • z
  shift3 = sym (trans assoc (cright assoc))

  resid-Ex-rounds : ∀ (d1 d2 : D) (lm : C (₁₊ m)) →
    resid (₂₊ m) (inj₂ (d1 , inj₂ (d2 , lm))) Ex ≈ ρ-rounds3 d1 d2
  resid-Ex-rounds d1 d2 lm = trans shift3 (cright shift3)

------------------------------------------------------------------------
-- The headline closed form.
--
-- With the boxes spelled out in components, the three rounds read off
-- the coset trajectory of ExAction.σ-Ex-swap: the round-2 boxes are the
-- quarter turns of the CZ-shifted round-1 boxes, and the round-3
-- a-components collapse to -b₂ / -b₁ by `neg-shift`.

  ρ-Ex-abcd : ∀ (a1 b1 a2 b2 : ℤ ₚ) (lm : C (₁₊ m)) →
    resid (₂₊ m) (inj₂ ((a1 , b1) , inj₂ ((a2 , b2) , lm))) Ex
    ≈ ρ-round (a1 , b1) (a2 , b2)
    • ρ-round (b1 + - a2 , - a1) (b2 + - a1 , - a2)
    • ρ-round (- b2 , - (b1 + - a2)) (- b1 , - (b2 + - a1))
  ρ-Ex-abcd a1 b1 a2 b2 lm =
    trans (resid-Ex-rounds (a1 , b1) (a2 , b2) lm) (refl' boxes)
    where
    E1 : D
    E1 = (b1 + - a2 , - a1)
    E2 : D
    E2 = (b2 + - a1 , - a2)

    eqe1 : nxt₁ (a1 , b1) (a2 , b2) ≡ E1
    eqe1 = Hd'-eq (a1 , b1 + - a2)

    eqe2 : nxt₂ (a1 , b1) (a2 , b2) ≡ E2
    eqe2 = Hd'-eq (a2 , b2 + - a1)

    eqf1 : nxt₁ E1 E2 ≡ (- b2 , - (b1 + - a2))
    eqf1 = Eq.trans (Hd'-eq (b1 + - a2 , - a1 + - (b2 + - a1)))
             (Eq.cong (λ z → (z , - (b1 + - a2))) (neg-shift {m} a1 b2))

    eqf2 : nxt₂ E1 E2 ≡ (- b1 , - (b2 + - a1))
    eqf2 = Eq.trans (Hd'-eq (b2 + - a1 , - a2 + - (b1 + - a2)))
             (Eq.cong (λ z → (z , - (b2 + - a1))) (neg-shift {m} a2 b1))

    boxes : ρ-rounds3 (a1 , b1) (a2 , b2)
          ≡ ρ3 (a1 , b1) (a2 , b2) E1 E2
               (- b2 , - (b1 + - a2)) (- b1 , - (b2 + - a1))
    boxes = Eq.trans
      (Eq.cong₂ (λ x y → ρ3 (a1 , b1) (a2 , b2) x y (nxt₁ x y) (nxt₂ x y))
                eqe1 eqe2)
      (Eq.cong₂ (ρ3 (a1 , b1) (a2 , b2) E1 E2) eqf1 eqf2)

------------------------------------------------------------------------
-- Bridge to the SyllableAction name.

  ρ-Ex-flat : ∀ (d1 d2 : D) (lm : C (₁₊ m)) →
    ρ-Ex {₁₊ m} (inj₂ (d1 , inj₂ (d2 , lm))) ≡ ρ-flat d1 d2
  ρ-Ex-flat d1 d2 lm = Eq.refl

------------------------------------------------------------------------
-- A worked branch: the zero boxes.
--
-- On (₀,₀) boxes every escape is the gate it came from — Hdir (₀,₀) = H
-- and DDCZ.dir-of on two zero a-components is CZ — so the residual of Ex
-- is Ex itself.
--
-- That is also the expected answer on EVERY doubly-inj₂ coset: ract
-- soundness together with DD-CZ.lemma-swap-DD (Ex ↑ • [d₁∷d₂] • Ex ≈
-- [d₂∷d₁], no leftover) forces  ρ-Ex c ≈ Ex.  Only this branch is
-- proved here; the general statement needs the full 4-way splits of
-- Hdir and DDCZ.dir-of at each of the three rounds.

  Z : D
  Z = (₀ , ₀)

  z0 : _≡_ {A = ℤ ₚ} (₀ + - ₀) ₀
  z0 = +-inverseʳ {p-2} ₀

  ρ-round-00 : ρ-round Z Z ≡ CZ • H • H ↑
  ρ-round-00 =
    Eq.cong (λ z → (DDCZ.dir-of (Z ∷ Z ∷ []) ↓ᵏ m)
                 • (Hdir (₀ , z) ↓ᵏ (₁₊ m))
                 • ((Hdir (₀ , z) ↓ᵏ m) ↑)) z0

  ρ-Ex-00 : ∀ (lm : C (₁₊ m)) →
    resid (₂₊ m) (inj₂ (Z , inj₂ (Z , lm))) Ex ≈ Ex
  ρ-Ex-00 lm =
    trans (ρ-Ex-abcd ₀ ₀ ₀ ₀ lm)
      (trans (refl' (Eq.trans allz (Eq.cong (λ w → w • w • w) ρ-round-00)))
             (sym (trans shift3 (cright shift3))))
    where
    eq2 : (₀ + - ₀ , - ₀) ≡ Z
    eq2 = Eq.cong₂ _,_ z0 -0#≈0#

    eq3 : (- ₀ , - (₀ + - ₀)) ≡ Z
    eq3 = Eq.cong₂ _,_ -0#≈0# (Eq.trans (Eq.cong -_ z0) -0#≈0#)

    allz : ρ-round Z Z • ρ-round (₀ + - ₀ , - ₀) (₀ + - ₀ , - ₀)
                       • ρ-round (- ₀ , - (₀ + - ₀)) (- ₀ , - (₀ + - ₀))
         ≡ ρ-round Z Z • ρ-round Z Z • ρ-round Z Z
    allz = Eq.cong₂ (λ x y → ρ-round Z Z • ρ-round x x • ρ-round y y) eq2 eq3

------------------------------------------------------------------------
-- The remaining obligation, recorded as a type.
--
-- `ρ-Ex-00` is its (₀,₀)-instance.  A second branch checks by hand:
-- for d₁ = (₀ , ₁₊b), d₂ = (₀ , ₀) the nine escapes are
--   CZ , ε , H ↑ | CX' , HH , ε | XC' , H , HH ↑
-- and H ^ 3 • H ^ 2 ≈ H (order-H) together with H • H ↑ ≈ H ↑ • H
-- collapses the product to Ex again.
--
-- Proving it in general is the 4-way Hdir / DDCZ.dir-of split at each of
-- the three rounds; `ρ-Ex-abcd` reduces that to a statement about words,
-- with no coset-fold left in it.

  ρ-Ex-Goal : Set
  ρ-Ex-Goal = ∀ (d1 d2 : D) (lm : C (₁₊ m)) →
    resid (₂₊ m) (inj₂ (d1 , inj₂ (d2 , lm))) Ex ≈ Ex
