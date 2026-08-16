------------------------------------------------------------------------
-- Presentations of groups
--
-- Circuits that keep every Pauli pure-Z.
--
-- One of the sixteen Paper-V0 rules is left over from the one-wire
-- calculus of Clifford.Qupit.SemLocal: blake-c12,
--
--     (S^(p-1))↑ · (S^(p-1))↓ · CX^(p-1) · S↓ · CX  =  CZ,
--
-- which lives on two wires.  It needs no phase COMPUTED — both sides
-- are ₀ — but it is not Pauli-free either, the three S-blocks each
-- carrying one.  What makes it vanish is that every Pauli in sight has
-- no X-part, and the symplectic form pairs two such to ₀.
--
-- `AllZ` is that property of a Pauli and `ZBlock` is a circuit which has
-- it, preserves it, and carries no phase.  ZBlocks are closed under
-- products (the cocycle term is a sform of two AllZ Paulis), powers and
-- shifting, and the three atoms blake-c12 needs are ZBlocks:
--
--   * S — its Pauli is (0,-½), pure Z, and its action is the shear
--     (a,b) ↦ (a,b+a), which does not touch the X-part;
--   * CZ — no Pauli, and its action adds X-parts to Z-parts only;
--   * CX — no Pauli, and although it is built out of H, which does NOT
--     preserve AllZ, the COMPOSITE does: `cx-act` computes it in closed
--     form, and the X-parts come out as a ↦ a + c, c ↦ c.
--
-- The H's are why this file computes an action rather than reusing
-- SemLocal's `Free`: on one wire, phase-freeness came from having no
-- Pauli at all, and here it comes from the Paulis being invisible to
-- each other.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; suc ; zero)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_,_ ; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Notations
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.Clifford.Qupit.SemZBlock
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ \ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k)
  where

open import Data.Product using (_×_ ; proj₁ ; proj₂)
open import Data.Unit using (⊤ ; tt)
open import Data.Vec using ([] ; _∷_)
import Relation.Binary.PropositionalEquality as Eq

open import Algebra.Properties.Ring (+-*-ring p-2) using (-0#≈0#)

open import Word.Base using (Word ; ε ; _•_ ; _^_ ; [_]ʷ)

open import Examples.Groups.ProjectivePauli.Semantics p-2 p-prime
  using (Pauli ; Pauli1 ; pI ; pIₙ ; sform ; sform1 ; _+ₚ_)
open import Examples.Groups.Symplectic.Semantics p-2 p-prime
  using (Symplectic)
open Symplectic using (ap)

import Examples.Groups.ProjectiveClifford.Qupit.Paper-V0.Syntactics
  p-3 p-prime g* g-gen as Pap
import Examples.Groups.Clifford.Qupit.Syntactics
  p-3 p-prime g* g-gen as QS
import Examples.Groups.Clifford.Qupit.Semantics p-3 p-prime as Sem
import Examples.Groups.Clifford.Qupit.SemFE p-3 p-prime g* g-gen as FE
import Examples.Groups.Clifford.Qupit.SemShift p-3 p-prime g* g-gen as SH
import Examples.Groups.Clifford.Qupit.SemRealises p-3 p-prime g* g-gen as RL

private
  variable
    m : ℕ

------------------------------------------------------------------------
-- Pure-Z Paulis
--
-- No X-part on any wire.  Two of them do not see each other, since
-- sform1 (₀,b) (₀,d) is (-₀)·d + ₀·b.

AllZ : Pauli m → Set
AllZ []      = ⊤
AllZ (q ∷ P) = (proj₁ q ≡ ₀) × AllZ P

private
  negzero : ∀ (Y : ℤ ₚ) → (- ₀) * Y ≡ ₀
  negzero Y = Eq.trans (Eq.cong (_* Y) -0#≈0#) (*-zeroˡ Y)

allZ-pI : AllZ (pIₙ {m})
allZ-pI {zero}  = tt
allZ-pI {₁₊ m} = Eq.refl , allZ-pI

allZ-+ₚ : (P Q : Pauli m) → AllZ P → AllZ Q → AllZ (P +ₚ Q)
allZ-+ₚ []      []      _         _         = tt
allZ-+ₚ (x ∷ P) (y ∷ Q) (ex , zP) (ey , zQ) =
  Eq.trans (Eq.cong₂ _+_ ex ey) (+-identityˡ ₀) , allZ-+ₚ P Q zP zQ

sform-allZ : (P Q : Pauli m) → AllZ P → AllZ Q → sform P Q ≡ ₀
sform-allZ []      []      _         _         = Eq.refl
sform-allZ (x ∷ P) (y ∷ Q) (ex , zP) (ey , zQ) =
  Eq.trans (Eq.cong₂ _+_ s1 (sform-allZ P Q zP zQ)) (+-identityˡ ₀)
  where
  s1 : sform1 x y ≡ ₀
  s1 = Eq.trans
         (Eq.cong₂ _+_
            (Eq.trans (Eq.cong (λ w → (- w) * proj₂ y) ex) (negzero (proj₂ y)))
            (Eq.trans (Eq.cong (_* proj₂ x) ey) (*-zeroˡ (proj₂ x))))
         (+-identityˡ ₀)

------------------------------------------------------------------------
-- The denotation's two product laws, at an arbitrary width

Φᵂ : QS.Circuit m → ℤ ₚ
Φᵂ {m} = RL.Width.Φ m

S-∙ : (u v : QS.Circuit m) (q : Pauli m) →
      ap (SH.Sᵂ (u • v)) q ≡ ap (SH.Sᵂ u) (ap (SH.Sᵂ v) q)
S-∙ {m} u v q = proj₂ (FE.Weyl.⟦⟧-∙ m u v) q

P-∙ : (u v : QS.Circuit m) →
      SH.Pᵂ (u • v) ≡ SH.Pᵂ u +ₚ ap (SH.Sᵂ u) (SH.Pᵂ v)
P-∙ {m} = RL.Width.P-∙ m

Φ-∙ : (u v : QS.Circuit m) →
      Φᵂ (u • v)
        ≡ (Φᵂ u + Φᵂ v) + Sem.1/2 * sform (SH.Pᵂ u) (ap (SH.Sᵂ u) (SH.Pᵂ v))
Φ-∙ {m} = RL.Width.Φ-• m

------------------------------------------------------------------------
-- Pure-Z blocks

record ZBlock {m : ℕ} (w : QS.Circuit m) : Set where
  constructor zb
  field
    zpauli : AllZ (SH.Pᵂ w)
    zpres  : (P : Pauli m) → AllZ P → AllZ (ap (SH.Sᵂ w) P)
    zphase : Φᵂ w ≡ ₀

zb-ε : ZBlock (ε {X = QS.Gen m})
zb-ε = zb allZ-pI (λ P zP → zP) (RL.Width.Φ-ε _)

zb-• : {u v : QS.Circuit m} → ZBlock u → ZBlock v → ZBlock (u • v)
zb-• {m} {u} {v} (zb pu su fu) (zb pv sv fv) = zb pe se fe
  where
  apv : AllZ (ap (SH.Sᵂ u) (SH.Pᵂ v))
  apv = su (SH.Pᵂ v) pv

  pe : AllZ (SH.Pᵂ (u • v))
  pe = Eq.subst AllZ (Eq.sym (P-∙ u v))
         (allZ-+ₚ (SH.Pᵂ u) (ap (SH.Sᵂ u) (SH.Pᵂ v)) pu apv)

  se : (P : Pauli m) → AllZ P → AllZ (ap (SH.Sᵂ (u • v)) P)
  se P zP = Eq.subst AllZ (Eq.sym (S-∙ u v P))
              (su (ap (SH.Sᵂ v) P) (sv P zP))

  fe : Φᵂ (u • v) ≡ ₀
  fe = Eq.trans (Φ-∙ u v)
         (Eq.trans (Eq.cong₂ _+_ (Eq.cong₂ _+_ fu fv)
                      (Eq.trans (Eq.cong (Sem.1/2 *_)
                                   (sform-allZ (SH.Pᵂ u)
                                               (ap (SH.Sᵂ u) (SH.Pᵂ v)) pu apv))
                                (*-zeroʳ Sem.1/2)))
                   (Eq.trans (+-identityʳ (₀ + ₀)) (+-identityˡ ₀)))

zb-^ : {w : QS.Circuit m} → ZBlock w → ∀ k → ZBlock (w ^ k)
zb-^ zw zero      = zb-ε
zb-^ zw (₁₊ zero) = zw
zb-^ zw (₂₊ k)    = zb-• zw (zb-^ zw (₁₊ k))

-- Shifting a block up a wire keeps it one: the shift adds a trivial
-- bottom wire to the Pauli and acts as the identity there.
zb-↑ : {w : QS.Circuit m} → ZBlock w → ZBlock (w Pap.↑)
zb-↑ {m} {w} (zb pw sw fw) = zb pe se (Eq.trans (RL.Φ-↑ w) fw)
  where
  pe : AllZ (SH.Pᵂ (w Pap.↑))
  pe = Eq.subst AllZ (Eq.sym (proj₁ (SH.⟦⟧-↑ w))) (Eq.refl , pw)

  se : (P : Pauli (₁₊ m)) → AllZ P → AllZ (ap (SH.Sᵂ (w Pap.↑)) P)
  se (q ∷ P) (eq , zP) =
    Eq.subst AllZ (Eq.sym (proj₂ (SH.⟦⟧-↑ w) (q ∷ P))) (eq , sw P zP)

------------------------------------------------------------------------
-- The three atoms
--
-- S carries a pure-Z Pauli and shears; CZ and CX carry none and their
-- actions leave the X-parts alone (CX mixes them, but only among
-- themselves).

zb-S : ZBlock (Pap.S {m})
zb-S {m} = zb (Eq.subst AllZ (Eq.sym SH.gate₁S-Pauli) (Eq.refl , allZ-pI))
              pres
              (RL.Width.Φ-gate (₁₊ m) _)
  where
  pres : (P : Pauli (₁₊ m)) → AllZ P → AllZ (ap (SH.Sᵂ (Pap.S {m})) P)
  pres ((a , b) ∷ R) (ea , zR) =
    Eq.subst AllZ (Eq.sym (SH.gate₁S-act a b R)) (ea , zR)

private
  -- CZ's action, definitionally: it adds each wire's X-part to the
  -- other's Z-part.
  czact : (a b c d : ℤ ₚ) (R : Pauli m) →
          ap (SH.Sᵂ (Pap.CZ {m})) ((a , b) ∷ (c , d) ∷ R)
            ≡ (a , b + c) ∷ (c , d + a) ∷ R
  czact a b c d R = Eq.refl

  -- ... and H's, on the bottom wire (SemShift's gate₁H-act).
  hact : (a b : ℤ ₚ) (R : Pauli (₁₊ m)) →
         ap (SH.Sᵂ (Pap.H {₁₊ m})) ((a , b) ∷ R) ≡ ((- b) , a) ∷ R
  hact = SH.gate₁H-act

  -- H³ is the inverse quarter turn.
  h3act : (a b : ℤ ₚ) (R : Pauli (₁₊ m)) →
          ap (SH.Sᵂ (Pap.H {₁₊ m} ^ 3)) ((a , b) ∷ R)
            ≡ (- (- b) , - a) ∷ R
  h3act {m} a b R =
    Eq.trans (S-∙ (Pap.H {₁₊ m}) (Pap.H • Pap.H) ((a , b) ∷ R))
      (Eq.trans (Eq.cong (ap (SH.Sᵂ (Pap.H {₁₊ m})))
                   (Eq.trans (S-∙ (Pap.H {₁₊ m}) Pap.H ((a , b) ∷ R))
                      (Eq.trans (Eq.cong (ap (SH.Sᵂ (Pap.H {₁₊ m})))
                                         (hact a b R))
                                (hact (- b) a R))))
                (hact (- a) (- b) R))

  -- ... so CX moves the X-parts among themselves and nothing else.
  cx-act : (a b c d : ℤ ₚ) (R : Pauli m) →
           ap (SH.Sᵂ (Pap.CX {m})) ((a , b) ∷ (c , d) ∷ R)
             ≡ (- (- (a + c)) , - (- b)) ∷ (c , d + (- b)) ∷ R
  cx-act {m} a b c d R =
    Eq.trans (S-∙ (Pap.H {₁₊ m} ^ 3) (Pap.CZ • Pap.H)
                  ((a , b) ∷ (c , d) ∷ R))
      (Eq.trans (Eq.cong (ap (SH.Sᵂ (Pap.H {₁₊ m} ^ 3)))
                   (Eq.trans (S-∙ (Pap.CZ {m}) Pap.H
                                  ((a , b) ∷ (c , d) ∷ R))
                      (Eq.trans (Eq.cong (ap (SH.Sᵂ (Pap.CZ {m})))
                                         (hact a b ((c , d) ∷ R)))
                                (czact (- b) a c d R))))
                (h3act (- b) (a + c) ((c , d + (- b)) ∷ R)))

  -- CX is written over H and CZ alone, so it has no Pauli of its own.
  zeroCX : RL.Width.ZeroP (₂₊ m) (Pap.CX {m})
  zeroCX {m} = RL.Width.zeroP-^ (₂₊ m) (Pap.H {₁₊ m}) Eq.refl 3
             , Eq.refl , Eq.refl

zb-CZ : ZBlock (Pap.CZ {m})
zb-CZ {m} = zb allZ-pI pres (RL.Width.Φ-gate (₂₊ m) _)
  where
  pres : (P : Pauli (₂₊ m)) → AllZ P → AllZ (ap (SH.Sᵂ (Pap.CZ {m})) P)
  pres ((a , b) ∷ (c , d) ∷ R) (ea , ec , zR) =
    Eq.subst AllZ (Eq.sym (czact a b c d R)) (ea , ec , zR)

zb-CX : ZBlock (Pap.CX {m})
zb-CX {m} =
  zb (Eq.subst AllZ
        (Eq.sym (proj₁ (RL.Width.zeroP (₂₊ m) (Pap.CX {m}) zeroCX)))
        allZ-pI)
     pres
     (proj₂ (RL.Width.zeroP (₂₊ m) (Pap.CX {m}) zeroCX))
  where
  pres : (P : Pauli (₂₊ m)) → AllZ P → AllZ (ap (SH.Sᵂ (Pap.CX {m})) P)
  pres ((a , b) ∷ (c , d) ∷ R) (ea , ec , zR) =
    Eq.subst AllZ (Eq.sym (cx-act a b c d R))
      ( Eq.trans (Eq.cong (λ z → - (- z))
                    (Eq.trans (Eq.cong₂ _+_ ea ec) (+-identityˡ ₀)))
                 (Eq.trans (Eq.cong -_ -0#≈0#) -0#≈0#)
      , ec , zR )
