------------------------------------------------------------------------
-- Presentations of groups
--
-- (F1): the rules of the four-wire theory, controlled
--
-- λ¹ of both sides of every rule of Syntactics at every placement
-- in the four-wire domain (f1ᵒ: the rule at offset o) are equal on
-- five wires (the paper's (F1)): the derivations Five.D
-- (scratchpad/joint/f1.py, f1big.py, deb.py, ckt2.py) from four-wire
-- windows and, for the items whose controlled K sits on the target of
-- an S-box, the transports of two-wire equations (Five.TR2); the items
-- at the offsets 2-4 are Five.F1Low's; the controlled lf, hyb-sq,
-- hyb-yb are rules of the schema.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.F1 where

open import Relation.Binary.PropositionalEquality as Eq using ()
open import Data.Nat using (ℕ)
import Presentation.Base as PB
open import Word.Base using (Word ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws)
open import Examples.Groups.Clifford+CS.Lambda using (λ¹ʷ)
open import Examples.Groups.Clifford+CS.Five.Rules
  using (_⊢ₓ_≈_ ; srelₓ ; ctl-lf ; ctl-hsq ; ctl-hyb)
open import Examples.Groups.Clifford+CS.Five.Transport using (F1)
import Examples.Groups.Clifford+CS.Five.F1Low as F1Low
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D014 using (lem-F1-order-CSat0 ; lem-F1-order-CSat1 ; lem-F1-order-Iat0 ; lem-F1-order-Kat0 ; lem-F1-order-Kat1 ; lem-F1-order-SKat0 ; lem-F1-order-SKat1 ; lem-F1-order-Sat0 ; lem-F1-order-Sat1)
open import Examples.Groups.Clifford+CS.Five.D.D015 using (lem-F1-comm-CS-S0at0 ; lem-F1-comm-CS-S0at1 ; lem-F1-comm-CS-S1at0)
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-F1-X-CS0at0 ; lem-F1-comm-CS-S1at1)
open import Examples.Groups.Clifford+CS.Five.D.D017 using (lem-F1-X-CS0at1)
open import Examples.Groups.Clifford+CS.Five.D.D018 using (lem-F1-X-CS1at0 ; lem-F1-X-CS1at1)
open import Examples.Groups.Clifford+CS.Five.D.D021 using (lem-F1-comm-CSu-CSat0)
open import Examples.Groups.Clifford+CS.Five.D.D022 using (lem-F1-comm-CSu-CSat1)
open import Examples.Groups.Clifford+CS.Five.D.D024 using (lem-F1-rel-266at0 ; lem-F1-rel-266at1 ; lem-F1-rel-267at0 ; lem-F1-rel-267at1)
open import Examples.Groups.Clifford+CS.Five.D.D026 using (lem-F1-rel-268at0)
open import Examples.Groups.Clifford+CS.Five.D.D028 using (lem-F1-rel-268at1)
open import Examples.Groups.Clifford+CS.Five.D.D036 using (lem-F1-cx-cczat0)
open import Examples.Groups.Clifford+CS.Five.D.D041 using (lem-F1-toff-cczat0)
open import Examples.Groups.Clifford+CS.Five.D.D047 using (lem-F1-CS-K0at0)
open import Examples.Groups.Clifford+CS.Five.D.D050 using (lem-F1-CS-K0at1)
open import Examples.Groups.Clifford+CS.Five.D.D054 using (lem-F1-CS-K1at0)
open import Examples.Groups.Clifford+CS.Five.D.D056 using (lem-F1-CS-K1at1 ; lem-F1-rel-269at0 ; lem-F1-rel-269at1)
open import Examples.Groups.Clifford+CS.Five.D.D059 using (lem-F1-rel-272at0)
open import Examples.Groups.Clifford+CS.Five.D.D060 using (lem-F1-rel-272at1)
open import Examples.Groups.Clifford+CS.Five.D.D219 using (lem-F1-ck-tctat0)

private
  variable
    n : ℕ
    w v : Word (Gen n)

f1₀ : Ws → 4 SRel, w === v → 5 ⊢ₓ λ¹ʷ w ≈ λ¹ʷ v
f1₀ c4 order-I = trans (by-assoc Eq.refl) (trans (lem-F1-order-Iat0 c4) (by-assoc Eq.refl))
f1₀ c4 order-S = trans (by-assoc Eq.refl) (trans (lem-F1-order-Sat0 c4) (by-assoc Eq.refl))
f1₀ c4 order-K = trans (by-assoc Eq.refl) (trans (lem-F1-order-Kat0 c4) (by-assoc Eq.refl))
f1₀ c4 order-SK = trans (by-assoc Eq.refl) (trans (lem-F1-order-SKat0 c4) (by-assoc Eq.refl))
f1₀ c4 order-CS = trans (by-assoc Eq.refl) (trans (lem-F1-order-CSat0 c4) (by-assoc Eq.refl))
f1₀ c4 comm-CS-S₀ = trans (by-assoc Eq.refl) (trans (lem-F1-comm-CS-S0at0 c4) (by-assoc Eq.refl))
f1₀ c4 comm-CS-S₁ = trans (by-assoc Eq.refl) (trans (lem-F1-comm-CS-S1at0 c4) (by-assoc Eq.refl))
f1₀ c4 X-CS₀ = trans (by-assoc Eq.refl) (trans (lem-F1-X-CS0at0 c4) (by-assoc Eq.refl))
f1₀ c4 X-CS₁ = trans (by-assoc Eq.refl) (trans (lem-F1-X-CS1at0 c4) (by-assoc Eq.refl))
f1₀ c4 CS-K₀ = trans (by-assoc Eq.refl) (trans (lem-F1-CS-K0at0 c4) (by-assoc Eq.refl))
f1₀ c4 CS-K₁ = trans (by-assoc Eq.refl) (trans (lem-F1-CS-K1at0 c4) (by-assoc Eq.refl))
f1₀ c4 comm-CS↑-CS = trans (by-assoc Eq.refl) (trans (lem-F1-comm-CSu-CSat0 c4) (by-assoc Eq.refl))
f1₀ c4 rel-266 = trans (by-assoc Eq.refl) (trans (lem-F1-rel-266at0 c4) (by-assoc Eq.refl))
f1₀ c4 rel-267 = trans (by-assoc Eq.refl) (trans (lem-F1-rel-267at0 c4) (by-assoc Eq.refl))
f1₀ c4 rel-268 = trans (by-assoc Eq.refl) (trans (lem-F1-rel-268at0 c4) (by-assoc Eq.refl))
f1₀ c4 rel-269 = trans (by-assoc Eq.refl) (trans (lem-F1-rel-269at0 c4) (by-assoc Eq.refl))
f1₀ c4 rel-272 = trans (by-assoc Eq.refl) (trans (lem-F1-rel-272at0 c4) (by-assoc Eq.refl))
f1₀ c4 cx-ccz = trans (by-assoc Eq.refl) (trans (lem-F1-cx-cczat0 c4) (by-assoc Eq.refl))
f1₀ c4 toff-ccz = trans (by-assoc Eq.refl) (trans (lem-F1-toff-cczat0 c4) (by-assoc Eq.refl))
f1₀ c4 ck-tct = trans (by-assoc Eq.refl) (trans (lem-F1-ck-tctat0 c4) (by-assoc Eq.refl))
f1₀ c4 lf = PB.axiom (srelₓ (ctl-lf 0))
f1₀ c4 hyb-sq = PB.axiom (srelₓ (ctl-hsq 0))
f1₀ c4 hyb-yb = PB.axiom (srelₓ (ctl-hyb 0))

f1₁ : Ws → 3 SRel, w === v → 5 ⊢ₓ λ¹ʷ (w ↑) ≈ λ¹ʷ (v ↑)
f1₁ c4 order-I = trans (by-assoc Eq.refl) (trans (lem-F1-order-Iat0 c4) (by-assoc Eq.refl))
f1₁ c4 order-S = trans (by-assoc Eq.refl) (trans (lem-F1-order-Sat1 c4) (by-assoc Eq.refl))
f1₁ c4 order-K = trans (by-assoc Eq.refl) (trans (lem-F1-order-Kat1 c4) (by-assoc Eq.refl))
f1₁ c4 order-SK = trans (by-assoc Eq.refl) (trans (lem-F1-order-SKat1 c4) (by-assoc Eq.refl))
f1₁ c4 order-CS = trans (by-assoc Eq.refl) (trans (lem-F1-order-CSat1 c4) (by-assoc Eq.refl))
f1₁ c4 comm-CS-S₀ = trans (by-assoc Eq.refl) (trans (lem-F1-comm-CS-S0at1 c4) (by-assoc Eq.refl))
f1₁ c4 comm-CS-S₁ = trans (by-assoc Eq.refl) (trans (lem-F1-comm-CS-S1at1 c4) (by-assoc Eq.refl))
f1₁ c4 X-CS₀ = trans (by-assoc Eq.refl) (trans (lem-F1-X-CS0at1 c4) (by-assoc Eq.refl))
f1₁ c4 X-CS₁ = trans (by-assoc Eq.refl) (trans (lem-F1-X-CS1at1 c4) (by-assoc Eq.refl))
f1₁ c4 CS-K₀ = trans (by-assoc Eq.refl) (trans (lem-F1-CS-K0at1 c4) (by-assoc Eq.refl))
f1₁ c4 CS-K₁ = trans (by-assoc Eq.refl) (trans (lem-F1-CS-K1at1 c4) (by-assoc Eq.refl))
f1₁ c4 comm-CS↑-CS = trans (by-assoc Eq.refl) (trans (lem-F1-comm-CSu-CSat1 c4) (by-assoc Eq.refl))
f1₁ c4 rel-266 = trans (by-assoc Eq.refl) (trans (lem-F1-rel-266at1 c4) (by-assoc Eq.refl))
f1₁ c4 rel-267 = trans (by-assoc Eq.refl) (trans (lem-F1-rel-267at1 c4) (by-assoc Eq.refl))
f1₁ c4 rel-268 = trans (by-assoc Eq.refl) (trans (lem-F1-rel-268at1 c4) (by-assoc Eq.refl))
f1₁ c4 rel-269 = trans (by-assoc Eq.refl) (trans (lem-F1-rel-269at1 c4) (by-assoc Eq.refl))
f1₁ c4 rel-272 = trans (by-assoc Eq.refl) (trans (lem-F1-rel-272at1 c4) (by-assoc Eq.refl))

-- The record Five.Transport takes.
f1 : Ws → F1
f1 c4 = record { f1₀ = f1₀ c4 ; f1₁ = f1₁ c4 ; f1₂ = F1Low.f1₂ c4
               ; f1₃ = F1Low.f1₃ c4 ; f1₄ = F1Low.f1₄ c4 }
