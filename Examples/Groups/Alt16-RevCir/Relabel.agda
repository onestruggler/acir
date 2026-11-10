------------------------------------------------------------------------
-- Presentations of groups
--
-- The circuits of Examples.Groups.XCXCCX-4bit, relabelled as circuits
-- over this folder's gates
--
-- XCXCCX-4bit states the rules (1)–(7) over the gates X, CX and CCX
-- with the swap a separate structural gate
-- (Examples.Independence.Prop); Theory states them over this folder's
-- gates, where the swap is the gate Ex.  The two gate sets are in
-- bijection — ρ sends a gate to the gate of the same name and the
-- structural swap to Ex — and the rules are the same words, so
--
-- * relabel: a derivation there is a derivation here, at every width
--   (each rule, each law of the swap and each structural rule goes to
--   its namesake);
--
-- * sem: a circuit here and its relabelling there are the same
--   function on states;
--
-- * Transfer.complete: completeness there at a width is completeness
--   here at that width.
--
-- ThreeWire uses the last at widths one, two and three.  Nothing here
-- is about four wires in particular, and the four-wire completeness
-- theorem of XCXCCX-4bit is not used in this folder.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Alt16-RevCir.Relabel where

open import Data.Nat using (ℕ)
open import Data.Vec.Base using (_∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Word.Base using ([_]ʷ ; ε ; _•_ ; wmap)

import Presentation.Base as PB

import Examples.Groups.XCXCCX-4bit.Semantics as BS
import Examples.Groups.XCXCCX-4bit.Syntactics as B

open import Examples.Groups.Alt16-RevCir.Semantics using (⟦_⟧ᵍ ; ⟦_⟧ ; _≐_)
open import Examples.Groups.Alt16-RevCir.Syntactics
  using ( Gate ; X-gate ; CX-gate ; Ex-gate ; CCX-gate
        ; X-gen ; CX-gen ; Ex-gen ; CCX-gen
        ; Gen ; gate₀ ; gate₁ ; gate₂ ; gate₃ ; _↥ ; Circuit ; _↑
        ; σ-inv ; σ-nat₁ ; σ-nat₂ ; σ-nat₃ )
open import Examples.Groups.Alt16-RevCir.Theory
  using (r1 ; r2 ; r3 ; r4 ; r5 ; r6 ; r7 ; module T)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The relabelling and its inverse

ρᵍ : B.PGate n → Gate n
ρᵍ B.⌈ B.X-gate ⌉   = X-gate
ρᵍ B.⌈ B.CX-gate ⌉  = CX-gate
ρᵍ B.⌈ B.CCX-gate ⌉ = CCX-gate
ρᵍ B.swap           = Ex-gate

ρ : B.Gen n → Gen n
ρ (B.gate₀ h) = gate₀ (ρᵍ h)
ρ (B.gate₁ h) = gate₁ (ρᵍ h)
ρ (B.gate₂ h) = gate₂ (ρᵍ h)
ρ (B.gate₃ h) = gate₃ (ρᵍ h)
ρ (x B.↥)     = ρ x ↥

ρᵍ⁻ : Gate n → B.PGate n
ρᵍ⁻ X-gate   = B.⌈ B.X-gate ⌉
ρᵍ⁻ CX-gate  = B.⌈ B.CX-gate ⌉
ρᵍ⁻ Ex-gate  = B.swap
ρᵍ⁻ CCX-gate = B.⌈ B.CCX-gate ⌉

ρ⁻ : Gen n → B.Gen n
ρ⁻ (gate₀ h) = B.gate₀ (ρᵍ⁻ h)
ρ⁻ (gate₁ h) = B.gate₁ (ρᵍ⁻ h)
ρ⁻ (gate₂ h) = B.gate₂ (ρᵍ⁻ h)
ρ⁻ (gate₃ h) = B.gate₃ (ρᵍ⁻ h)
ρ⁻ (x ↥)     = ρ⁻ x B.↥

private
  ρρᵍ⁻ : (h : Gate n) → ρᵍ (ρᵍ⁻ h) ≡ h
  ρρᵍ⁻ X-gate   = refl
  ρρᵍ⁻ CX-gate  = refl
  ρρᵍ⁻ Ex-gate  = refl
  ρρᵍ⁻ CCX-gate = refl

  ρρ⁻ : (x : Gen n) → ρ (ρ⁻ x) ≡ x
  ρρ⁻ (gate₀ h) = Eq.cong gate₀ (ρρᵍ⁻ h)
  ρρ⁻ (gate₁ h) = Eq.cong gate₁ (ρρᵍ⁻ h)
  ρρ⁻ (gate₂ h) = Eq.cong gate₂ (ρρᵍ⁻ h)
  ρρ⁻ (gate₃ h) = Eq.cong gate₃ (ρρᵍ⁻ h)
  ρρ⁻ (x ↥)     = Eq.cong _↥ (ρρ⁻ x)

-- Relabelling a circuit there and back gives the circuit.
relabel-inv : (w : Circuit n) → wmap ρ (wmap ρ⁻ w) ≡ w
relabel-inv [ x ]ʷ  = Eq.cong [_]ʷ (ρρ⁻ x)
relabel-inv ε       = refl
relabel-inv (w • v) = Eq.cong₂ _•_ (relabel-inv w) (relabel-inv v)

-- Relabelling commutes with the shift.
ρ-↑ : (w : B.Circuit n) → wmap ρ (w B.↑) ≡ wmap ρ w ↑
ρ-↑ [ x ]ʷ  = refl
ρ-↑ ε       = refl
ρ-↑ (w • v) = Eq.cong₂ _•_ (ρ-↑ w) (ρ-↑ v)

------------------------------------------------------------------------
-- Derivations

-- Each rule, law of the swap and structural rule goes to its namesake.
relabel-ax : {w v : B.Circuit n} → B._VRel,_===_ n w v →
             T._⊢_≈_ n (wmap ρ w) (wmap ρ v)
relabel-ax (B.srel (B.srel B.r1)) = PB.axiom (T.srel (T.srel r1))
relabel-ax (B.srel (B.srel B.r2)) = PB.axiom (T.srel (T.srel r2))
relabel-ax (B.srel (B.srel B.r3)) = PB.axiom (T.srel (T.srel r3))
relabel-ax (B.srel (B.srel B.r4)) = PB.axiom (T.srel (T.srel r4))
relabel-ax (B.srel (B.srel B.r5)) = PB.axiom (T.srel (T.srel r5))
relabel-ax (B.srel (B.srel B.r6)) = PB.axiom (T.srel (T.srel r6))
relabel-ax (B.srel (B.srel B.r7)) = PB.axiom (T.srel (T.srel r7))
relabel-ax (B.srel (B.σrel B.σ-inv)) =
  PB.axiom (T.srel (T.σrel σ-inv))
relabel-ax (B.srel (B.σrel (B.σ-nat₁ h))) =
  PB.axiom (T.srel (T.σrel (σ-nat₁ (ρᵍ h))))
relabel-ax (B.srel (B.σrel (B.σ-nat₂ h))) =
  PB.axiom (T.srel (T.σrel (σ-nat₂ (ρᵍ h))))
relabel-ax (B.srel (B.σrel (B.σ-nat₃ h))) =
  PB.axiom (T.srel (T.σrel (σ-nat₃ (ρᵍ h))))
relabel-ax {n = n} (B.cong↑ {w = w} {v = v} a) =
  Eq.subst₂ (T._⊢_≈_ n) (Eq.sym (ρ-↑ w)) (Eq.sym (ρ-↑ v))
            (T.lemma-cong↑ _ _ (relabel-ax a))
relabel-ax (B.comm₁ h x) = PB.axiom (T.comm₁ (ρᵍ h) (ρ x))
relabel-ax (B.comm₂ h x) = PB.axiom (T.comm₂ (ρᵍ h) (ρ x))
relabel-ax (B.comm₃ h x) = PB.axiom (T.comm₃ (ρᵍ h) (ρ x))
relabel-ax (B.ω↑=ω h)    = PB.axiom (T.ω↑=ω (ρᵍ h))

-- A derivation there is a derivation here.
relabel : {w v : B.Circuit n} → B._⊢_≈_ n w v →
          T._⊢_≈_ n (wmap ρ w) (wmap ρ v)
relabel PB.refl         = PB.refl
relabel (PB.sym e)      = PB.sym (relabel e)
relabel (PB.trans e e′) = PB.trans (relabel e) (relabel e′)
relabel (PB.cong e e′)  = PB.cong (relabel e) (relabel e′)
relabel PB.assoc        = PB.assoc
relabel PB.left-unit    = PB.left-unit
relabel PB.right-unit   = PB.right-unit
relabel (PB.axiom a)    = relabel-ax a

------------------------------------------------------------------------
-- Semantics

private
  sem-gen : (x : Gen n) → BS.⟦ ρ⁻ x ⟧ᵍ ≐ ⟦ x ⟧ᵍ
  sem-gen (gate₀ ())
  sem-gen X-gen   (a ∷ s)         = refl
  sem-gen CX-gen  (a ∷ b ∷ s)     = refl
  sem-gen Ex-gen  (a ∷ b ∷ s)     = refl
  sem-gen CCX-gen (a ∷ b ∷ c ∷ s) = refl
  sem-gen (x ↥)   (a ∷ s)         = Eq.cong (a ∷_) (sem-gen x s)

-- A circuit and its relabelling are the same function on states.
sem : (w : Circuit n) → BS.⟦ wmap ρ⁻ w ⟧ ≐ ⟦ w ⟧
sem [ x ]ʷ  s = sem-gen x s
sem ε       s = refl
sem (w • v) s =
  Eq.trans (Eq.cong BS.⟦ wmap ρ⁻ v ⟧ (sem w s)) (sem v (⟦ w ⟧ s))

------------------------------------------------------------------------
-- Completeness, from there to here

module Transfer {n : ℕ}
  (completeᴮ : {u v : B.Circuit n} →
               BS.⟦ u ⟧ BS.≐ BS.⟦ v ⟧ → B._⊢_≈_ n u v)
  where

  complete : {w v : Circuit n} → ⟦ w ⟧ ≐ ⟦ v ⟧ → T._⊢_≈_ n w v
  complete {w} {v} e =
    Eq.subst₂ (T._⊢_≈_ n) (relabel-inv w) (relabel-inv v)
      (relabel (completeᴮ {wmap ρ⁻ w} {wmap ρ⁻ v} λ s →
        Eq.trans (sem w s) (Eq.trans (e s) (Eq.sym (sem v s)))))
