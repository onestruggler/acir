------------------------------------------------------------------------
-- Presentations of groups
--
-- Synthesis: circuits that turn an anticommuting pair of Paulis into
-- ±X_w and ±Z_w
--
-- Part of the generation of the n-qubit Clifford group (the plan is in
-- PathSum.Hierarchy.Generation.Scalar).  Everything here is about
-- Pauli data and the tableau action actC of
-- PathSum.Hierarchy.Generation.Tableau: no operator appears.  Given a
-- wire w and the images p, q of X_w and Z_w under a Clifford
-- operator, three circuits, built from the bits of p and q, bring them
-- back to X_w and Z_w (the standard symplectic reduction, wire by
-- wire):
--
--   1. phase1 w p: on every wire make p's letter an X or I (H turns Z
--      into X, S turns Y into -X; toX), first on w and then on each
--      other wire j, and fold an X at j into w with CNOTs (CNOT(w,j)
--      clears it when w carries an X, CNOT(j,w) CNOT(w,j) when it does
--      not; foldX).  Afterwards p is trivial off w and has no Z at w
--      (phase1-shape).
--   2. phase2 w q, for a q with a Z at w (which the anticommutation of
--      the images forces): on every other wire make q's letter a Z or
--      I (H, or S then H; toZ) and clear it with CNOT(j,w); then turn
--      a Y at w into Z with H S H.  Afterwards q is ±Z_w up to its
--      phase (phase2-shape), and a p of the shape left by phase 1 with
--      an X at w keeps that shape (phase2-pass): the CNOT(j,w) and H S H
--      fix X_w.
--   3. fixC w s t: S S (which is Z_w) if p's sign s is -1, H S S H
--      (X_w) if q's sign t is; then p and q are exactly X_w and Z_w
--      (fix-ok), phases included.
--
-- Each circuit touches only w and the wires where its driver is
-- non-trivial, so it avoids every wire at which p and q are trivial
-- (phase1-avoids, phase2-avoids): the wires already brought back to
-- X_i, Z_i are not disturbed.  The wire-by-wire passes are one sweep
-- (module Sweep) over the list of wires other than w, its lemmas
-- stated once for any step with an invariant.  CNOT is the circuit
-- H_t CZ_(c,t) H_t of PathSum.Hierarchy.Generation.Tableau.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ; suc)

module PathSum.Hierarchy.Generation.Synthesis (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; _∧_; _xor_)
open import Data.Fin.Base using (Fin)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; _+_; _*_)
open import Data.Integer.Properties using
  (+-identityʳ; *-zeroʳ; *-distribˡ-+; +-assoc)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.List.Base using (List; []; _∷_; _++_; filter; allFin)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using
  (∈-filter⁺; ∈-allFin)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (all-filter)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (Dec; yes; no; ¬?)

import Data.Fin.Properties as Fin

open import PathSum.Assign using ([_]ᶻ; _[_≔_]; ≔-here; ≔-there; ≔-cong)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.Hierarchy.Generation.Tableau M₀ public
open import PathSum.Hierarchy.Levels M₀ using (N≡¼·4)
open import PathSum.Maslov.Arith M₀ using (½-self)
open import PathSum.RelativePhase M₀ using
  (_≡ᴺ_; ≡ᴺ-refl; ≡ᴺ-≡; ≡ᴺ-sym; ≡ᴺ-trans; ≡ᴺ-+; ≡ᴺ-N)

open +-*-Solver using (solve; con; _:+_; _:*_; _:=_)

private
  variable
    n : ℕ

  -- Bits carried along an equality of data, or a sameness at a wire.

  zero-same : (i : Fin n) (r s : PauliData n) → Same-at i r s →
              Zero-at i r → Zero-at i s
  zero-same i r s (sx , sz) (zx , zz) = trans (sym sx) zx , trans (sym sz) zz

  supp-≈ : {w : Fin n} {r s : PauliData n} → r ≈ᴾ s → Supp w s → Supp w r
  supp-≈ e sp k k≢w = trans (xs≈ e k) (proj₁ (sp k k≢w)) ,
                      trans (zs≈ e k) (proj₂ (sp k k≢w))


------------------------------------------------------------------------
-- Sweeping the wires other than w

others : Fin n → List (Fin n)
others {n} w = filter (λ j → ¬? (j Fin.≟ w)) (allFin n)

others-≢ : (w : Fin n) → All (_≢ w) (others w)
others-≢ {n} w = all-filter (λ j → ¬? (j Fin.≟ w)) (allFin n)

others-∈ : (w i : Fin n) → i ≢ w → i ∈ others w
others-∈ {n} w i i≢w = ∈-filter⁺ (λ j → ¬? (j Fin.≟ w)) (∈-allFin i) i≢w

-- A step for each wire in turn, each computed from what the previous
-- steps made of the driver r.

sweep : (Fin n → PauliData n → Cl.Circuit n) → List (Fin n) →
        PauliData n → Cl.Circuit n
sweep st []       r = []
sweep st (j ∷ js) r = st j r ++ sweep st js (actC (st j r) r)

-- The lemmas, for a step that keeps an invariant of the driver, clears
-- the driver at its wire, touches only its wire and w, and does
-- nothing where the driver is trivial.

module Sweep {n : ℕ} (w : Fin n) (st : Fin n → PauliData n → Cl.Circuit n)
  (Inv : PauliData n → Set)
  (st-inv : ∀ j r → j ≢ w → Inv r → Inv (actC (st j r) r))
  (st-zero : ∀ j r → j ≢ w → Inv r → Zero-at j (actC (st j r) r))
  (st-avoids : ∀ j r {i} → i ≢ j → i ≢ w → Avoids i (st j r))
  (st-trivial : ∀ j r → j ≢ w → Zero-at j r → Avoids j (st j r))
  where

  private
    unfold : ∀ j js r s → actC (sweep st (j ∷ js) r) s ≡
             actC (sweep st js (actC (st j r) r)) (actC (st j r) s)
    unfold j js r s = actC-++ (st j r) (sweep st js (actC (st j r) r)) s

    keep-at : ∀ j r i → Dec (i ≡ j) → j ≢ w → i ≢ w → Inv r →
              Zero-at i r → Zero-at i (actC (st j r) r)
    keep-at j r i (yes refl) j≢w i≢w h z = st-zero i r j≢w h
    keep-at j r i (no  i≢j)  j≢w i≢w h z =
      zero-same i r (actC (st j r) r)
        (circuit-same (st j r) (st-avoids j r i≢j i≢w) r) z

    avoid-at : ∀ j r i → Dec (i ≡ j) → j ≢ w → i ≢ w → Zero-at i r →
               Avoids i (st j r)
    avoid-at j r i (yes refl) j≢w i≢w z = st-trivial i r j≢w z
    avoid-at j r i (no  i≢j)  j≢w i≢w z = st-avoids j r i≢j i≢w

  -- The invariant holds throughout.

  inv : ∀ js r → All (_≢ w) js → Inv r → Inv (actC (sweep st js r) r)
  inv []       r []         h = h
  inv (j ∷ js) r (j≢w ∷ ok) h =
    subst Inv (sym (unfold j js r r))
      (inv js (actC (st j r) r) ok (st-inv j r j≢w h))

  -- A wire where the driver is trivial stays so.

  keep : ∀ js r i → All (_≢ w) js → i ≢ w → Inv r → Zero-at i r →
         Zero-at i (actC (sweep st js r) r)
  keep []       r i []         i≢w h z = z
  keep (j ∷ js) r i (j≢w ∷ ok) i≢w h z =
    subst (Zero-at i) (sym (unfold j js r r))
      (keep js (actC (st j r) r) i ok i≢w (st-inv j r j≢w h)
            (keep-at j r i (i Fin.≟ j) j≢w i≢w h z))

  -- Every wire swept is cleared.

  clear : ∀ js r → All (_≢ w) js → Inv r → ∀ i → i ∈ js →
          Zero-at i (actC (sweep st js r) r)
  clear (j ∷ js) r (j≢w ∷ ok) h i (here refl) =
    subst (Zero-at i) (sym (unfold i js r r))
      (keep js (actC (st i r) r) i ok j≢w (st-inv i r j≢w h)
            (st-zero i r j≢w h))
  clear (j ∷ js) r (j≢w ∷ ok) h i (there i∈) =
    subst (Zero-at i) (sym (unfold j js r r))
      (clear js (actC (st j r) r) ok (st-inv j r j≢w h) i i∈)

  -- The sweep avoids a wire where the driver is trivial.

  avoids : ∀ js r i → All (_≢ w) js → i ≢ w → Inv r → Zero-at i r →
           Avoids i (sweep st js r)
  avoids []       r i []         i≢w h z = []
  avoids (j ∷ js) r i (j≢w ∷ ok) i≢w h z =
    avoids-++ (st j r) (sweep st js (actC (st j r) r))
      (avoid-at j r i (i Fin.≟ j) j≢w i≢w z)
      (avoids js (actC (st j r) r) i ok i≢w (st-inv j r j≢w h)
              (keep-at j r i (i Fin.≟ j) j≢w i≢w h z))

  -- A property of another Pauli that each step keeps.

  pass : (P : PauliData n → Set) →
         (∀ j r s → j ≢ w → Inv r → P s → P (actC (st j r) s)) →
         ∀ js r s → All (_≢ w) js → Inv r → P s → P (actC (sweep st js r) s)
  pass P st-pass []       r s []         h ps = ps
  pass P st-pass (j ∷ js) r s (j≢w ∷ ok) h ps =
    subst P (sym (unfold j js r s))
      (pass P st-pass js (actC (st j r) r) (actC (st j r) s) ok
            (st-inv j r j≢w h) (st-pass j r s j≢w h ps))


------------------------------------------------------------------------
-- The circuits

-- Make a letter an X: Z by H, Y by S (to -X).

toX′ : Fin n → Bool → Bool → Cl.Circuit n
toX′ j x     false = []
toX′ j true  true  = Cl.S j ∷ []
toX′ j false true  = Cl.H j ∷ []

toX : Fin n → PauliData n → Cl.Circuit n
toX j r = toX′ j (xs r j) (zs r j)

-- Fold an X at j into w.

foldX′ : Fin n → Fin n → Bool → Bool → Cl.Circuit n
foldX′ w j false xw    = []
foldX′ w j true  true  = cnotC w j
foldX′ w j true  false = cnotC j w ++ cnotC w j

foldX : Fin n → Fin n → PauliData n → Cl.Circuit n
foldX w j r = foldX′ w j (xs r j) (xs r w)

step1 : Fin n → Fin n → PauliData n → Cl.Circuit n
step1 w j r = toX j r ++ foldX w j (actC (toX j r) r)

phase1 : Fin n → PauliData n → Cl.Circuit n
phase1 w p = toX w p ++ sweep (step1 w) (others w) (actC (toX w p) p)

-- Make a letter a Z: X by H, Y by S then H.

toZ′ : Fin n → Bool → Bool → Cl.Circuit n
toZ′ j false z     = []
toZ′ j true  true  = Cl.S j ∷ Cl.H j ∷ []
toZ′ j true  false = Cl.H j ∷ []

toZ : Fin n → PauliData n → Cl.Circuit n
toZ j r = toZ′ j (xs r j) (zs r j)

-- Clear a Z at j against the Z at w.

clearZ′ : Fin n → Fin n → Bool → Cl.Circuit n
clearZ′ w j false = []
clearZ′ w j true  = cnotC j w

clearZ : Fin n → Fin n → PauliData n → Cl.Circuit n
clearZ w j r = clearZ′ w j (zs r j)

step2 : Fin n → Fin n → PauliData n → Cl.Circuit n
step2 w j r = toZ j r ++ clearZ w j (actC (toZ j r) r)

-- A Y at w becomes Z under H S H, which fixes X.

finZ′ : Fin n → Bool → Cl.Circuit n
finZ′ w false = []
finZ′ w true  = Cl.H w ∷ Cl.S w ∷ Cl.H w ∷ []

finZ : Fin n → PauliData n → Cl.Circuit n
finZ w r = finZ′ w (xs r w)

phase2 : Fin n → PauliData n → Cl.Circuit n
phase2 w q =
  sweep (step2 w) (others w) q ++
  finZ w (actC (sweep (step2 w) (others w) q) q)

-- The signs: S S is Z_w, H S S H is X_w.

SSc HSSHc : Fin n → Cl.Circuit n
SSc   w = Cl.S w ∷ Cl.S w ∷ []
HSSHc w = Cl.H w ∷ Cl.S w ∷ Cl.S w ∷ Cl.H w ∷ []

flipX′ flipZ′ : Fin n → Bool → Cl.Circuit n
flipX′ w false = []
flipX′ w true  = SSc w
flipZ′ w false = []
flipZ′ w true  = HSSHc w

fixC : Fin n → Bool → Bool → Cl.Circuit n
fixC w s t = flipX′ w s ++ flipZ′ w t


------------------------------------------------------------------------
-- Which wires the circuits touch

toX′-avoids : {i j : Fin n} → i ≢ j → ∀ x z → Avoids i (toX′ j x z)
toX′-avoids i≢j x     false = []
toX′-avoids i≢j true  true  = i≢j ∷ []
toX′-avoids i≢j false true  = i≢j ∷ []

foldX′-avoids : {i w j : Fin n} → i ≢ j → i ≢ w → ∀ a b →
                Avoids i (foldX′ w j a b)
foldX′-avoids i≢j i≢w false b     = []
foldX′-avoids i≢j i≢w true  true  = avoids-cnot i≢w i≢j
foldX′-avoids i≢j i≢w true  false =
  avoids-++ (cnotC _ _) (cnotC _ _) (avoids-cnot i≢j i≢w) (avoids-cnot i≢w i≢j)

toZ′-avoids : {i j : Fin n} → i ≢ j → ∀ x z → Avoids i (toZ′ j x z)
toZ′-avoids i≢j false z     = []
toZ′-avoids i≢j true  true  = i≢j ∷ i≢j ∷ []
toZ′-avoids i≢j true  false = i≢j ∷ []

clearZ′-avoids : {i w j : Fin n} → i ≢ j → i ≢ w → ∀ c →
                 Avoids i (clearZ′ w j c)
clearZ′-avoids i≢j i≢w false = []
clearZ′-avoids i≢j i≢w true  = avoids-cnot i≢j i≢w

finZ′-avoids : {i w : Fin n} → i ≢ w → ∀ b → Avoids i (finZ′ w b)
finZ′-avoids i≢w false = []
finZ′-avoids i≢w true  = i≢w ∷ i≢w ∷ i≢w ∷ []

fixC-avoids : {i w : Fin n} → i ≢ w → ∀ s t → Avoids i (fixC w s t)
fixC-avoids {w = w} i≢w s t = avoids-++ (flipX′ w s) (flipZ′ w t) (fx s) (fz t)
  where
  fx : ∀ s → Avoids _ (flipX′ w s)
  fx false = []
  fx true  = i≢w ∷ i≢w ∷ []
  fz : ∀ t → Avoids _ (flipZ′ w t)
  fz false = []
  fz true  = i≢w ∷ i≢w ∷ i≢w ∷ i≢w ∷ []



------------------------------------------------------------------------
-- Phase 1

step1-avoids : {w j : Fin n} (r : PauliData n) {i : Fin n} → i ≢ j → i ≢ w →
               Avoids i (step1 w j r)
step1-avoids {w = w} {j} r i≢j i≢w =
  avoids-++ (toX j r) (foldX w j (actC (toX j r) r))
    (toX′-avoids i≢j (xs r j) (zs r j))
    (foldX′-avoids i≢j i≢w (xs (actC (toX j r) r) j) (xs (actC (toX j r) r) w))

private
  triv1 : {w j : Fin n} (r : PauliData n) → ∀ x z → xs r j ≡ x → x ≡ false →
          z ≡ false →
          Avoids j (toX′ j x z ++ foldX w j (actC (toX′ j x z) r))
  triv1 {w = w} {j} r false false ex _ _ =
    subst (λ a → Avoids j (foldX′ w j a (xs r w))) (sym ex) []
  triv1 r true  z     _ () _
  triv1 r false true  _ _  ()

step1-trivial : {w j : Fin n} (r : PauliData n) → Zero-at j r →
                Avoids j (step1 w j r)
step1-trivial {j = j} r (zx , zz) = triv1 r (xs r j) (zs r j) refl zx zz

module _ {n : ℕ} {w j : Fin n} (j≢w : j ≢ w) where

  private
    w≢j : w ≢ j
    w≢j e = j≢w (sym e)

    fold-cases : (r : PauliData n) → zs r w ≡ false → zs r j ≡ false →
                 ∀ a b → xs r j ≡ a → xs r w ≡ b →
                 Zero-at j (actC (foldX′ w j a b) r) ×
                 (zs (actC (foldX′ w j a b) r) w ≡ false)
    fold-cases r zw zj false b xa xb = (xa , zj) , zw
    fold-cases r zw zj true  true  xa xb =
      (trans (cnot-xs-t w≢j r) (cong₂ _xor_ xa xb) ,
       trans (cnot-zs-off w≢j r j≢w) zj) ,
      trans (cnot-zs-c w≢j r) (cong₂ _xor_ zw zj)
    fold-cases r zw zj true  false xa xb =
      (trans (cnot-xs-t w≢j s) (cong₂ _xor_ sxj sxw) ,
       trans (cnot-zs-off w≢j s j≢w) szj) ,
      trans (cnot-zs-c w≢j s) (cong₂ _xor_ szw szj)
      where
      s = actC (cnotC j w) r
      sxw : xs s w ≡ true
      sxw = trans (cnot-xs-t j≢w r) (cong₂ _xor_ xb xa)
      sxj : xs s j ≡ true
      sxj = trans (cnot-xs-off j≢w r j≢w) xa
      szj : zs s j ≡ false
      szj = trans (cnot-zs-c j≢w r) (cong₂ _xor_ zj zw)
      szw : zs s w ≡ false
      szw = trans (cnot-zs-off j≢w r w≢j) zw

    fold-ok : (r : PauliData n) → zs r w ≡ false → zs r j ≡ false →
              Zero-at j (actC (foldX w j r) r) ×
              (zs (actC (foldX w j r) r) w ≡ false)
    fold-ok r zw zj = fold-cases r zw zj (xs r j) (xs r w) refl refl

    step1-cases : (r : PauliData n) → zs r w ≡ false → ∀ x z →
                  xs r j ≡ x → zs r j ≡ z →
                  Zero-at j (actC (toX′ j x z ++
                                   foldX w j (actC (toX′ j x z) r)) r) ×
                  (zs (actC (toX′ j x z ++
                             foldX w j (actC (toX′ j x z) r)) r) w ≡ false)
    step1-cases r zw x     false ex ez = fold-ok r zw ez
    step1-cases r zw true  true  ex ez =
      fold-ok (actS j r) (trans (zs-S-off j r w≢j) zw)
              (trans (zs-S-at j r) (cong₂ _xor_ ez ex))
    step1-cases r zw false true  ex ez =
      fold-ok (actH j r) (trans (zs-H-off j r w≢j) zw)
              (trans (zs-H-at j r) ex)

  -- A step of phase 1 clears wire j and keeps w free of Z.

  step1-ok : (r : PauliData n) → zs r w ≡ false →
             Zero-at j (actC (step1 w j r) r) ×
             (zs (actC (step1 w j r) r) w ≡ false)
  step1-ok r zw = step1-cases r zw (xs r j) (zs r j) refl refl

private
  toX-at-cases : (w : Fin n) (r : PauliData n) → ∀ x z → xs r w ≡ x →
                 zs r w ≡ z → zs (actC (toX′ w x z) r) w ≡ false
  toX-at-cases w r x     false ex ez = ez
  toX-at-cases w r true  true  ex ez = trans (zs-S-at w r) (cong₂ _xor_ ez ex)
  toX-at-cases w r false true  ex ez = trans (zs-H-at w r) ex

module Phase1 {n : ℕ} (w : Fin n) where

  private
    module S = Sweep w (step1 w) (λ r → zs r w ≡ false)
      (λ j r j≢w h → proj₂ (step1-ok j≢w r h))
      (λ j r j≢w h → proj₁ (step1-ok j≢w r h))
      (λ j r i≢j i≢w → step1-avoids r i≢j i≢w)
      (λ j r j≢w z → step1-trivial r z)

    p₀ : PauliData n → PauliData n
    p₀ p = actC (toX w p) p

    zw₀ : (p : PauliData n) → zs (p₀ p) w ≡ false
    zw₀ p = toX-at-cases w p (xs p w) (zs p w) refl refl

  -- After phase 1, p is trivial off w and has no Z at w.

  phase1-shape : (p : PauliData n) →
                 Supp w (actC (phase1 w p) p) ×
                 (zs (actC (phase1 w p) p) w ≡ false)
  phase1-shape p =
    (λ i i≢w → subst (Zero-at i) (sym (actC-++ (toX w p) sw p))
                 (S.clear (others w) (p₀ p) (others-≢ w) (zw₀ p) i
                          (others-∈ w i i≢w))) ,
    subst (λ r → zs r w ≡ false) (sym (actC-++ (toX w p) sw p))
      (S.inv (others w) (p₀ p) (others-≢ w) (zw₀ p))
    where
    sw = sweep (step1 w) (others w) (p₀ p)

  -- It avoids every wire where p is trivial.

  phase1-avoids : (p : PauliData n) {i : Fin n} → i ≢ w → Zero-at i p →
                  Avoids i (phase1 w p)
  phase1-avoids p {i} i≢w z =
    avoids-++ (toX w p) (sweep (step1 w) (others w) (p₀ p))
      (toX′-avoids i≢w (xs p w) (zs p w))
      (S.avoids (others w) (p₀ p) i (others-≢ w) i≢w (zw₀ p)
         (zero-same i p (actC (toX w p) p) (circuit-same (toX w p)
                       (toX′-avoids i≢w (xs p w) (zs p w)) p) z))

open Phase1 public


------------------------------------------------------------------------
-- Phase 2

step2-avoids : {w j : Fin n} (r : PauliData n) {i : Fin n} → i ≢ j → i ≢ w →
               Avoids i (step2 w j r)
step2-avoids {w = w} {j} r i≢j i≢w =
  avoids-++ (toZ j r) (clearZ w j (actC (toZ j r) r))
    (toZ′-avoids i≢j (xs r j) (zs r j))
    (clearZ′-avoids i≢j i≢w (zs (actC (toZ j r) r) j))

private
  triv2 : {w j : Fin n} (r : PauliData n) → ∀ x → xs r j ≡ x → x ≡ false →
          zs r j ≡ false →
          Avoids j (toZ′ j x (zs r j) ++
                    clearZ w j (actC (toZ′ j x (zs r j)) r))
  triv2 {w = w} {j} r false _ _ zz =
    subst (λ c → Avoids j (clearZ′ w j c)) (sym zz) []
  triv2 r true _ () _

step2-trivial : {w j : Fin n} (r : PauliData n) → Zero-at j r →
                Avoids j (step2 w j r)
step2-trivial {j = j} r (zx , zz) = triv2 r (xs r j) refl zx zz

-- The shapes of a Pauli at the end: an X, or a Z, at w and nothing
-- elsewhere.

XT ZT : Fin n → PauliData n → Set
XT w r = Supp w r × (xs r w ≡ true)  × (zs r w ≡ false)
ZT w r = Supp w r × (xs r w ≡ false) × (zs r w ≡ true)

XT-≈ : {w : Fin n} {r s : PauliData n} → r ≈ᴾ s → XT w s → XT w r
XT-≈ {w = w} e (sp , x , z) =
  supp-≈ e sp , trans (xs≈ e w) x , trans (zs≈ e w) z

ZT-≈ : {w : Fin n} {r s : PauliData n} → r ≈ᴾ s → ZT w s → ZT w r
ZT-≈ {w = w} e (sp , x , z) =
  supp-≈ e sp , trans (xs≈ e w) x , trans (zs≈ e w) z

module _ {n : ℕ} {w j : Fin n} (j≢w : j ≢ w) where

  private
    w≢j : w ≢ j
    w≢j e = j≢w (sym e)

    clear-cases : (r : PauliData n) → zs r w ≡ true → xs r j ≡ false →
                  ∀ c → zs r j ≡ c →
                  Zero-at j (actC (clearZ′ w j c) r) ×
                  (zs (actC (clearZ′ w j c) r) w ≡ true)
    clear-cases r zw xj false zc = (xj , zc) , zw
    clear-cases r zw xj true  zc =
      (trans (cnot-xs-off j≢w r j≢w) xj ,
       trans (cnot-zs-c j≢w r) (cong₂ _xor_ zc zw)) ,
      trans (cnot-zs-off j≢w r w≢j) zw

    clear-ok : (r : PauliData n) → zs r w ≡ true → xs r j ≡ false →
               Zero-at j (actC (clearZ w j r) r) ×
               (zs (actC (clearZ w j r) r) w ≡ true)
    clear-ok r zw xj = clear-cases r zw xj (zs r j) refl

    step2-cases : (r : PauliData n) → zs r w ≡ true → ∀ x z →
                  xs r j ≡ x → zs r j ≡ z →
                  Zero-at j (actC (toZ′ j x z ++
                                   clearZ w j (actC (toZ′ j x z) r)) r) ×
                  (zs (actC (toZ′ j x z ++
                             clearZ w j (actC (toZ′ j x z) r)) r) w ≡ true)
    step2-cases r zw false z     ex ez = clear-ok r zw ex
    step2-cases r zw true  true  ex ez =
      clear-ok (actH j (actS j r))
        (trans (zs-H-off j (actS j r) w≢j) (trans (zs-S-off j r w≢j) zw))
        (trans (xs-H-at j (actS j r))
               (trans (zs-S-at j r) (cong₂ _xor_ ez ex)))
    step2-cases r zw true  false ex ez =
      clear-ok (actH j r) (trans (zs-H-off j r w≢j) zw)
               (trans (xs-H-at j r) ez)

    -- CNOT(j, w) keeps an X at w.

    cnot-XT : (s : PauliData n) → XT w s → XT w (actC (cnotC j w) s)
    cnot-XT s (sp , x , z) =
      supp ,
      trans (cnot-xs-t j≢w s) (cong₂ _xor_ x (proj₁ (sp j j≢w))) ,
      trans (cnot-zs-off j≢w s w≢j) z
      where
      zs-at : ∀ k → k ≢ w → Dec (k ≡ j) →
              zs (actC (cnotC j w) s) k ≡ false
      zs-at k k≢w (yes refl) = trans (cnot-zs-c j≢w s)
                                     (cong₂ _xor_ (proj₂ (sp k k≢w)) z)
      zs-at k k≢w (no  k≢j)  =
        trans (cnot-zs-off j≢w s k≢j) (proj₂ (sp k k≢w))

      supp : Supp w (actC (cnotC j w) s)
      supp k k≢w = trans (cnot-xs-off j≢w s k≢w) (proj₁ (sp k k≢w)) ,
                   zs-at k k≢w (k Fin.≟ j)

    pass-clear : (s : PauliData n) → XT w s → ∀ c →
                 XT w (actC (clearZ′ w j c) s)
    pass-clear s xt false = xt
    pass-clear s xt true  = cnot-XT s xt

  -- A step of phase 2 clears wire j and keeps the Z at w.

  step2-ok : (r : PauliData n) → zs r w ≡ true →
             Zero-at j (actC (step2 w j r) r) ×
             (zs (actC (step2 w j r) r) w ≡ true)
  step2-ok r zw = step2-cases r zw (xs r j) (zs r j) refl refl

  -- It keeps an X at w as it is.

  step2-pass : (r s : PauliData n) → XT w s → XT w (actC (step2 w j r) s)
  step2-pass r s xt =
    subst (XT w) (sym (actC-++ (toZ j r) (clearZ w j r′) s))
      (pass-clear (actC (toZ j r) s)
        (XT-≈ (circuit-fix (toZ j r) (toZ′-avoids w≢j (xs r j) (zs r j)) s
                           (proj₁ xt)) xt)
        (zs r′ j))
    where
    r′ = actC (toZ j r) r

-- H S H turns a Y at w into Z and keeps an X.

private
  hsh-same : {w k : Fin n} → k ≢ w → (s : PauliData n) →
             Same-at k s (actC (finZ′ w true) s)
  hsh-same {w = w} k≢w s =
    circuit-same (finZ′ w true) (k≢w ∷ k≢w ∷ k≢w ∷ []) s

  hsh-xs : (w : Fin n) (s : PauliData n) →
           xs (actC (finZ′ w true) s) w ≡ xs s w xor zs s w
  hsh-xs w s =
    trans (xs-H-at w (actS w (actH w s)))
      (trans (zs-S-at w (actH w s))
             (cong₂ _xor_ (zs-H-at w s) (xs-H-at w s)))

  hsh-zs : (w : Fin n) (s : PauliData n) →
           zs (actC (finZ′ w true) s) w ≡ zs s w
  hsh-zs w s = trans (zs-H-at w (actS w (actH w s))) (xs-H-at w s)

  fin-cases : (w : Fin n) (r : PauliData n) → Supp w r → zs r w ≡ true →
              ∀ b → xs r w ≡ b → ZT w (actC (finZ′ w b) r)
  fin-cases w r sp zw false xw = sp , xw , zw
  fin-cases w r sp zw true  xw =
    (λ k k≢w → zero-same k r (actC (finZ′ w true) r) (hsh-same k≢w r)
                         (sp k k≢w)) ,
    trans (hsh-xs w r) (cong₂ _xor_ xw zw) ,
    trans (hsh-zs w r) zw

  fin-pass : (w : Fin n) (s : PauliData n) → XT w s → ∀ b →
             XT w (actC (finZ′ w b) s)
  fin-pass w s xt false = xt
  fin-pass w s (sp , x , z) true =
    (λ k k≢w → zero-same k s (actC (finZ′ w true) s) (hsh-same k≢w s)
                         (sp k k≢w)) ,
    trans (hsh-xs w s) (cong₂ _xor_ x z) ,
    trans (hsh-zs w s) z

module Phase2 {n : ℕ} (w : Fin n) where

  private
    module S = Sweep w (step2 w) (λ r → zs r w ≡ true)
      (λ j r j≢w h → proj₂ (step2-ok j≢w r h))
      (λ j r j≢w h → proj₁ (step2-ok j≢w r h))
      (λ j r i≢j i≢w → step2-avoids r i≢j i≢w)
      (λ j r j≢w z → step2-trivial r z)

    q₁ : PauliData n → PauliData n
    q₁ q = actC (sweep (step2 w) (others w) q) q

  -- After phase 2, q is a Z at w and nothing elsewhere.

  phase2-shape : (q : PauliData n) → zs q w ≡ true →
                 ZT w (actC (phase2 w q) q)
  phase2-shape q zw =
    subst (ZT w) (sym (actC-++ sw (finZ w (q₁ q)) q))
      (fin-cases w (q₁ q) supp (S.inv (others w) q (others-≢ w) zw)
                 (xs (q₁ q) w) refl)
    where
    sw = sweep (step2 w) (others w) q
    supp : Supp w (q₁ q)
    supp k k≢w = S.clear (others w) q (others-≢ w) zw k (others-∈ w k k≢w)

  -- An X at w alone stays so.

  phase2-pass : (q s : PauliData n) → zs q w ≡ true → XT w s →
                XT w (actC (phase2 w q) s)
  phase2-pass q s zw xt =
    subst (XT w) (sym (actC-++ sw (finZ w (q₁ q)) s))
      (fin-pass w (actC sw s)
         (S.pass (XT w) (λ j r s j≢w h ps → step2-pass j≢w r s ps)
                 (others w) q s (others-≢ w) zw xt)
         (xs (q₁ q) w))
    where
    sw = sweep (step2 w) (others w) q

  -- It avoids every wire where q is trivial.

  phase2-avoids : (q : PauliData n) {i : Fin n} → i ≢ w → zs q w ≡ true →
                  Zero-at i q → Avoids i (phase2 w q)
  phase2-avoids q {i} i≢w zw z =
    avoids-++ (sweep (step2 w) (others w) q) (finZ w (q₁ q))
      (S.avoids (others w) q i (others-≢ w) i≢w zw z)
      (finZ′-avoids i≢w (xs (q₁ q) w))

open Phase2 public


------------------------------------------------------------------------
-- The signs

private
  ∧-comm : ∀ a b → (a ∧ b) ≡ (b ∧ a)
  ∧-comm true  true  = refl
  ∧-comm true  false = refl
  ∧-comm false true  = refl
  ∧-comm false false = refl

  distrib : ∀ a t → ¼ * (a + t) ≡ ¼ * a + ¼ * t
  distrib a t = *-distribˡ-+ ¼ a t

-- S S adds 2 x_w to the phase.

SS-act : (w : Fin n) (r : PauliData n) →
         actC (SSc w) r ≈ᴾ pd (ph r + (+ 2) * [ xs r w ]ᶻ) (xs r) (zs r)
SS-act w r = ≈ᴾ-intro
  (≡ᴺ-≡ (cong (¼ *_) (solve 2 (λ a t → a :+ t :+ t := a :+ con (+ 2) :* t)
                              refl (ph r) [ xs r w ]ᶻ)))
  (λ _ → refl) (λ k → at k (k Fin.≟ w))
  where
  s = actS w r
  at : ∀ k → Dec (k ≡ w) → zs (actS w s) k ≡ zs r k
  at k (yes refl) =
    trans (≔-here (zs s) w (zs s w xor xs r w))
      (trans (cong (_xor xs r w) (≔-here (zs r) w (zs r w xor xs r w)))
        (trans (xor-assoc (zs r w) (xs r w) (xs r w))
          (trans (cong (zs r w xor_) (xor-self (xs r w)))
                 (xor-false (zs r w)))))
  at k (no k≢w) = trans (≔-there (zs s) (zs s w xor xs r w) k≢w)
                        (≔-there (zs r) (zs r w xor xs r w) k≢w)

-- H H is the identity on data.

HH-act : (w : Fin n) (r : PauliData n) → actH w (actH w r) ≈ᴾ r
HH-act w r = ≈ᴾ-intro ph-eq xx zz
  where
  s = actH w r
  A = xs r w ∧ zs r w

  B≡A : (xs s w ∧ zs s w) ≡ A
  B≡A = trans (cong₂ _∧_ (xs-H-at w r) (zs-H-at w r))
              (∧-comm (zs r w) (xs r w))

  ph-eq : ¼ * (ph r + (+ 2) * [ A ]ᶻ + (+ 2) * [ xs s w ∧ zs s w ]ᶻ) ≡ᴺ
          ¼ * ph r
  ph-eq = ≡ᴺ-trans
    (≡ᴺ-≡ (trans (cong (λ b → ¼ * (ph r + (+ 2) * [ A ]ᶻ + (+ 2) * [ b ]ᶻ))
                       B≡A)
                 (trans (solve 3 (λ q a t → q :* (a :+ con (+ 2) :* t :+
                                                  con (+ 2) :* t) :=
                                            q :* a :+ t :* (q :* con (+ 4)))
                                 refl ¼ (ph r) [ A ]ᶻ)
                        (cong (λ m → ¼ * ph r + [ A ]ᶻ * m) (sym N≡¼·4)))))
    (≡ᴺ-trans (≡ᴺ-+ (≡ᴺ-refl {a = ¼ * ph r}) (≡ᴺ-N [ A ]ᶻ))
              (≡ᴺ-≡ (+-identityʳ (¼ * ph r))))

  xx-at : ∀ k → Dec (k ≡ w) → xs (actH w s) k ≡ xs r k
  xx-at k (yes refl) = trans (≔-here (xs s) w (zs s w)) (zs-H-at w r)
  xx-at k (no  k≢w)  = trans (≔-there (xs s) (zs s w) k≢w) (xs-H-off w r k≢w)

  zz-at : ∀ k → Dec (k ≡ w) → zs (actH w s) k ≡ zs r k
  zz-at k (yes refl) = trans (≔-here (zs s) w (xs s w)) (xs-H-at w r)
  zz-at k (no  k≢w)  = trans (≔-there (zs s) (xs s w) k≢w) (zs-H-off w r k≢w)

  xx : ∀ k → xs (actH w s) k ≡ xs r k
  xx k = xx-at k (k Fin.≟ w)

  zz : ∀ k → zs (actH w s) k ≡ zs r k
  zz k = zz-at k (k Fin.≟ w)

-- H respects equality of data, and so does adding to the phase.

actH-cong : (w : Fin n) {r s : PauliData n} → r ≈ᴾ s → actH w r ≈ᴾ actH w s
actH-cong w {r} {s} e = ≈ᴾ-intro
  (≡ᴺ-trans (≡ᴺ-≡ (distrib (ph r) ((+ 2) * [ xs r w ∧ zs r w ]ᶻ)))
    (≡ᴺ-trans (≡ᴺ-+ (ph≈ e)
                    (≡ᴺ-≡ (cong (λ b → ¼ * ((+ 2) * [ b ]ᶻ))
                                (cong₂ _∧_ (xs≈ e w) (zs≈ e w)))))
              (≡ᴺ-≡ (sym (distrib (ph s) ((+ 2) * [ xs s w ∧ zs s w ]ᶻ))))))
  (λ k → trans (cong (λ b → (xs r [ w ≔ b ]) k) (zs≈ e w))
               (≔-cong w (zs s w) (xs≈ e) k))
  (λ k → trans (cong (λ b → (zs r [ w ≔ b ]) k) (xs≈ e w))
               (≔-cong w (xs s w) (zs≈ e) k))

add-ph : (t : ℤ) {r s : PauliData n} → r ≈ᴾ s →
         pd (ph r + t) (xs r) (zs r) ≈ᴾ pd (ph s + t) (xs s) (zs s)
add-ph t {r} {s} e = ≈ᴾ-intro
  (≡ᴺ-trans (≡ᴺ-≡ (distrib (ph r) t))
    (≡ᴺ-trans (≡ᴺ-+ (ph≈ e) (≡ᴺ-refl {a = ¼ * t}))
              (≡ᴺ-≡ (sym (distrib (ph s) t)))))
  (xs≈ e) (zs≈ e)

-- H S S H adds 2 z_w to the phase.

HSSH-act : (w : Fin n) (r : PauliData n) →
           actC (HSSHc w) r ≈ᴾ pd (ph r + (+ 2) * [ zs r w ]ᶻ) (xs r) (zs r)
HSSH-act w r =
  ≈ᴾ-trans (actH-cong w (SS-act w s))
    (≈ᴾ-trans swap
      (≈ᴾ-trans (add-ph T (HH-act w r))
        (≈ᴾ-intro (≡ᴺ-≡ (cong (λ b → ¼ * (ph r + (+ 2) * [ b ]ᶻ))
                              (xs-H-at w r)))
                  (λ _ → refl) (λ _ → refl))))
  where
  s = actH w r
  T = (+ 2) * [ xs s w ]ᶻ
  swap : actH w (pd (ph s + T) (xs s) (zs s)) ≈ᴾ
         pd (ph (actH w s) + T) (xs (actH w s)) (zs (actH w s))
  swap = ≈ᴾ-intro
    (≡ᴺ-≡ (cong (¼ *_) (solve 3 (λ a t b → a :+ t :+ b := a :+ b :+ t) refl
                                (ph s) T ((+ 2) * [ xs s w ∧ zs s w ]ᶻ))))
    (λ _ → refl) (λ _ → refl)

private
  -- An X or a Z at w, with phase 0.

  XT⇒X : (w : Fin n) (r : PauliData n) → XT w r → ¼ * ph r ≡ᴺ 0ℤ →
         r ≈ᴾ X^ w
  XT⇒X w r (sp , x , z) h =
    ≈ᴾ-intro (≡ᴺ-trans h (≡ᴺ-≡ (sym (*-zeroʳ ¼))))
      (λ k → xx k (k Fin.≟ w)) (λ k → zz k (k Fin.≟ w))
    where
    xx : ∀ k → Dec (k ≡ w) → xs r k ≡ eᵛ w k
    xx k (yes refl) = trans x (sym (≔-here 0ᵛ w true))
    xx k (no  k≢w)  = trans (proj₁ (sp k k≢w)) (sym (≔-there 0ᵛ true k≢w))
    zz : ∀ k → Dec (k ≡ w) → zs r k ≡ false
    zz k (yes refl) = z
    zz k (no  k≢w)  = proj₂ (sp k k≢w)

  ZT⇒Z : (w : Fin n) (r : PauliData n) → ZT w r → ¼ * ph r ≡ᴺ 0ℤ →
         r ≈ᴾ Z^ w
  ZT⇒Z w r (sp , x , z) h =
    ≈ᴾ-intro (≡ᴺ-trans h (≡ᴺ-≡ (sym (*-zeroʳ ¼))))
      (λ k → xx k (k Fin.≟ w)) (λ k → zz k (k Fin.≟ w))
    where
    xx : ∀ k → Dec (k ≡ w) → xs r k ≡ false
    xx k (yes refl) = x
    xx k (no  k≢w)  = proj₁ (sp k k≢w)
    zz : ∀ k → Dec (k ≡ w) → zs r k ≡ eᵛ w k
    zz k (yes refl) = trans z (sym (≔-here 0ᵛ w true))
    zz k (no  k≢w)  = trans (proj₂ (sp k k≢w)) (sym (≔-there 0ᵛ true k≢w))

  -- The flips on the two shapes.

  plus0 : (r : PauliData n) →
          r ≈ᴾ pd (ph r + (+ 2) * [ false ]ᶻ) (xs r) (zs r)
  plus0 r = ≈ᴾ-intro (≡ᴺ-≡ (cong (¼ *_) (sym (+-identityʳ (ph r)))))
                     (λ _ → refl) (λ _ → refl)

  bump : (r : PauliData n) {b c : Bool} → b ≡ c →
         pd (ph r + (+ 2) * [ b ]ᶻ) (xs r) (zs r) ≈ᴾ
         pd (ph r + (+ 2) * [ c ]ᶻ) (xs r) (zs r)
  bump r e = ≈ᴾ-intro (≡ᴺ-≡ (cong (λ b → ¼ * (ph r + (+ 2) * [ b ]ᶻ)) e))
                      (λ _ → refl) (λ _ → refl)

  flipX-X : (w : Fin n) (s : Bool) (r : PauliData n) → XT w r →
            actC (flipX′ w s) r ≈ᴾ pd (ph r + (+ 2) * [ s ]ᶻ) (xs r) (zs r)
  flipX-X w false r xt = plus0 r
  flipX-X w true  r xt = ≈ᴾ-trans (SS-act w r) (bump r (proj₁ (proj₂ xt)))

  flipX-Z : (w : Fin n) (s : Bool) (r : PauliData n) → ZT w r →
            actC (flipX′ w s) r ≈ᴾ r
  flipX-Z w false r zt = ≈ᴾ-refl
  flipX-Z w true  r zt = ≈ᴾ-trans (SS-act w r)
    (≈ᴾ-trans (bump r (proj₁ (proj₂ zt))) (≈ᴾ-sym (plus0 r)))

  flipZ-X : (w : Fin n) (t : Bool) (r : PauliData n) → XT w r →
            actC (flipZ′ w t) r ≈ᴾ r
  flipZ-X w false r xt = ≈ᴾ-refl
  flipZ-X w true  r xt = ≈ᴾ-trans (HSSH-act w r)
    (≈ᴾ-trans (bump r (proj₂ (proj₂ xt))) (≈ᴾ-sym (plus0 r)))

  flipZ-Z : (w : Fin n) (t : Bool) (r : PauliData n) → ZT w r →
            actC (flipZ′ w t) r ≈ᴾ pd (ph r + (+ 2) * [ t ]ᶻ) (xs r) (zs r)
  flipZ-Z w false r zt = plus0 r
  flipZ-Z w true  r zt = ≈ᴾ-trans (HSSH-act w r) (bump r (proj₂ (proj₂ zt)))

  -- A sign fixed by its own flip.

  phase-fix : ∀ a s → ¼ * a ≡ᴺ ½ * [ s ]ᶻ →
              ¼ * (a + (+ 2) * [ s ]ᶻ) ≡ᴺ 0ℤ
  phase-fix a s h =
    ≡ᴺ-trans (≡ᴺ-≡ (trans (distrib a ((+ 2) * [ s ]ᶻ))
                          (cong (λ u → ¼ * a + u) (¼·2 [ s ]ᶻ))))
      (≡ᴺ-trans (≡ᴺ-+ h (≡ᴺ-refl {a = ½ * [ s ]ᶻ})) (½-self s))

-- With the signs s and t of p and q, fixC turns them into X_w and Z_w.

fix-ok : (w : Fin n) (s t : Bool) (p q : PauliData n) →
         XT w p → ¼ * ph p ≡ᴺ ½ * [ s ]ᶻ →
         ZT w q → ¼ * ph q ≡ᴺ ½ * [ t ]ᶻ →
         (actC (fixC w s t) p ≈ᴾ X^ w) × (actC (fixC w s t) q ≈ᴾ Z^ w)
fix-ok w s t p q xp hp zq hq =
  subst (_≈ᴾ X^ w) (sym (actC-++ (flipX′ w s) (flipZ′ w t) p))
    (≈ᴾ-trans (flipZ-X w t p′ (XT-≈ e₁ xp))
      (≈ᴾ-trans e₁ (XT⇒X w (pd (ph p + (+ 2) * [ s ]ᶻ) (xs p) (zs p)) xp
                          (phase-fix (ph p) s hp)))) ,
  subst (_≈ᴾ Z^ w) (sym (actC-++ (flipX′ w s) (flipZ′ w t) q))
    (≈ᴾ-trans (flipZ-Z w t q′ (ZT-≈ e₂ zq))
      (ZT⇒Z w (pd (ph q′ + (+ 2) * [ t ]ᶻ) (xs q′) (zs q′)) (ZT-≈ e₂ zq)
            (phase-fix (ph q′) t (≡ᴺ-trans (ph≈ e₂) hq))))
  where
  p′ = actC (flipX′ w s) p
  q′ = actC (flipX′ w s) q
  e₁ = flipX-X w s p xp
  e₂ = flipX-Z w s q zq


------------------------------------------------------------------------
-- Reading the shapes

private
  ∧-true : ∀ a → (a ∧ true) ≡ a
  ∧-true true  = refl
  ∧-true false = refl

  ∧-false : ∀ a → (a ∧ false) ≡ false
  ∧-false true  = refl
  ∧-false false = refl

  -- A vector trivial off w is its bit at w times e_w.

  dot-at : (w : Fin n) (z v : Assign n) → (∀ k → k ≢ w → v k ≡ false) →
           dot z v ≡ (z w ∧ v w)
  dot-at w z v off = trans (dot-cong {z = z} {z′ = z} (λ _ → refl) pt)
                           (by (v w) refl)
    where
    pt-at : ∀ k → Dec (k ≡ w) → v k ≡ (v w ∧ eᵛ w k)
    pt-at k (yes refl) = trans (sym (∧-true (v w)))
                               (cong (v w ∧_) (sym (≔-here 0ᵛ w true)))
    pt-at k (no  k≢w)  = trans (off k k≢w)
      (trans (sym (∧-false (v w)))
             (cong (v w ∧_) (sym (≔-there 0ᵛ true k≢w))))
    pt : ∀ k → v k ≡ (v w ∧ eᵛ w k)
    pt k = pt-at k (k Fin.≟ w)
    by : ∀ c → v w ≡ c → dot z (λ k → c ∧ eᵛ w k) ≡ (z w ∧ v w)
    by true  e = trans (dot-e z w)
                       (trans (sym (∧-true (z w))) (cong (z w ∧_) (sym e)))
    by false e = trans (dot-0ʳ z (λ k → false ∧ eᵛ w k) (λ _ → refl))
                       (trans (sym (∧-false (z w))) (cong (z w ∧_) (sym e)))

-- After phase 1, the symplectic form with q reads q's Z at w and p's X
-- at w.

ω-shape : (w : Fin n) (p q : PauliData n) → Supp w p → zs p w ≡ false →
          ω p q ≡ (zs q w ∧ xs p w)
ω-shape w p q sp zw =
  cong₂ _xor_ (dot-0ˡ (zs p) (xs q) zero)
              (dot-at w (zs q) (xs p) (λ k k≢w → proj₁ (sp k k≢w)))
  where
  zero-at : ∀ k → Dec (k ≡ w) → zs p k ≡ false
  zero-at k (yes refl) = zw
  zero-at k (no  k≢w)  = proj₂ (sp k k≢w)
  zero : ∀ k → zs p k ≡ false
  zero k = zero-at k (k Fin.≟ w)

-- The shapes have z·x = 0, as herm-sign asks.

XT-dot : (w : Fin n) (r : PauliData n) → XT w r → dot (zs r) (xs r) ≡ false
XT-dot w r (sp , x , z) = dot-0ˡ (zs r) (xs r) (λ k → at k (k Fin.≟ w))
  where
  at : ∀ k → Dec (k ≡ w) → zs r k ≡ false
  at k (yes refl) = z
  at k (no  k≢w)  = proj₂ (sp k k≢w)

ZT-dot : (w : Fin n) (r : PauliData n) → ZT w r → dot (zs r) (xs r) ≡ false
ZT-dot w r (sp , x , z) = dot-0ʳ (zs r) (xs r) (λ k → at k (k Fin.≟ w))
  where
  at : ∀ k → Dec (k ≡ w) → xs r k ≡ false
  at k (yes refl) = x
  at k (no  k≢w)  = proj₁ (sp k k≢w)
