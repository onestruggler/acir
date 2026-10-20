------------------------------------------------------------------------
-- Presentations of groups
--
-- The Hadamard embedding of CCX+H circuits into CCX+HH circuits one wire
-- wider.  Wire 0 is the partner: H on wire i becomes HH on wires 0 and
-- i + 1, and every other gate moves up a wire.  The image is the group
-- of circuits that use wire 0 only through HH gates.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.FourWire.Embed where

open import Data.Bool.Base using (Bool ; true ; false)
open import Data.Nat.Base using (ℕ ; suc)
open import Data.Product.Base using (Σ ; _,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)
open import Notations using (₁₊ ; ₂₊ ; ₃₊)
import Presentation.Base as PB

import Examples.Groups.CCX+H.NaturalP.Schema as H
import Examples.Groups.CCX+HH.NaturalP.Schema as S

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The map

-- Is the generator an H, at some height?
isH : H.Gen n → Bool
isH (H.gate₀ ())
isH (H.gate₁ H.X-gate)   = false
isH (H.gate₁ H.H-gate)   = true
isH (H.gate₂ H.CX-gate)  = false
isH (H.gate₂ H.SW-gate)  = false
isH (H.gate₃ H.CCX-gate) = false
isH (g H.↥)              = isH g

-- One wire up: an H keeps its partner on wire 0, by the swap of wires
-- 0 and 1; any other gate just moves.
up : Bool → S.Circuit (suc n) → S.Circuit (₂₊ n)
up true  w = S.σ • w S.↑ • S.σ
up false w = w S.↑

ψg : H.Gen n → S.Circuit (suc n)
ψg (H.gate₀ ())
ψg (H.gate₁ H.X-gate)   = S.X S.↑
ψg (H.gate₁ H.H-gate)   = S.HH
ψg (H.gate₂ H.CX-gate)  = S.CX S.↑
ψg (H.gate₂ H.SW-gate)  = S.σ S.↑
ψg (H.gate₃ H.CCX-gate) = S.CCX S.↑
ψg (g H.↥)              = up (isH g) (ψg g)

ψ : H.Circuit n → S.Circuit (suc n)
ψ = ψg ʷ

------------------------------------------------------------------------
-- A gate other than H is one generator, one wire up

single : (g : H.Gen n) → isH g ≡ false → Σ (S.Gen n) (λ k → ψg g ≡ [ k S.↥ ]ʷ)
single (H.gate₀ ())
single (H.gate₁ H.X-gate)   _ = S.gate₁ S.X-gate , Eq.refl
single (H.gate₁ H.H-gate)   ()
single (H.gate₂ H.CX-gate)  _ = S.gate₂ S.CX-gate , Eq.refl
single (H.gate₂ H.SW-gate)  _ = S.gate₂ S.SW-gate , Eq.refl
single (H.gate₃ H.CCX-gate) _ = S.gate₃ S.CCX-gate , Eq.refl
single (g H.↥) e with isH g | single g
... | false | f with f Eq.refl
...   | k , p = k S.↥ , Eq.cong (Word.Base.wmap S._↥) p
single (g H.↥) () | true | _

------------------------------------------------------------------------
-- One wire up

private
  σσ : (₂₊ n) S.⊢ S.σ • S.σ ≈ ε
  σσ = S.σ-invol

-- σ • w • σ ≈ w for a generator two wires up.
past : (k : S.Gen n) → (₂₊ n) S.⊢ S.σ • [ k S.↥ S.↥ ]ʷ • S.σ ≈ [ k S.↥ S.↥ ]ʷ
past k =
  PB.trans (PB.cong PB.refl (PB.axiom (S.comm₂ S.SW-gate k)))
  (PB.trans (PB.sym PB.assoc)
  (PB.trans (PB.cong σσ PB.refl) PB.left-unit))

-- ψ of a word one wire up is ψ of the word one wire up, conjugated by
-- the swap of wires 0 and 1.
lift : (w : H.Circuit n) → (₂₊ n) S.⊢ ψ (w H.↑) ≈ S.σ • ψ w S.↑ • S.σ
lift ε = PB.sym (PB.trans (PB.cong PB.refl PB.left-unit) σσ)
lift [ g ]ʷ with isH g | Eq.inspect isH g
... | true  | _ = PB.refl
... | false | Eq.[ e ] with single g e
...   | k , p rewrite p = PB.sym (past k)
lift (u • v) =
  PB.trans (PB.cong (lift u) (lift v))
  (PB.trans PB.assoc
  (PB.trans (PB.cong PB.refl
    (PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl
      (PB.trans (PB.sym PB.assoc)
      (PB.trans (PB.cong σσ PB.refl) PB.left-unit)))
    (PB.sym PB.assoc))))
  (PB.cong PB.refl (PB.trans (PB.cong PB.refl PB.refl) PB.refl))))

------------------------------------------------------------------------
-- The rule R4

-- The image of the CCX+H rule CCXH⁴, (CCX · H)⁴ = CZ ↑ on three wires:
-- (CCX(1; 2, 3) · HH(0, 1))⁴ = CZ(2, 3), wire 0 the partner.  Up to a
-- relabelling of the wires it is the rule R4 of Rules/w4.
R4 : Set
R4 = 4 S.⊢ ψ {3} (H.CCX • H.H • H.CCX • H.H • H.CCX • H.H • H.CCX • H.H)
           ≈ ψ {3} (H.CZ H.↑)
