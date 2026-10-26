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
-- Each side is compared with its derivation letter by letter
-- (Five.LamLetters, scratchpad/five/lamletters.py).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SF1 ; pickᴰ)

module Examples.Groups.Clifford+CS.Five.F1 (Sᴰ : SF1) where

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
open import Examples.Groups.Clifford+CS.Five.LamLetters using (via₀ ; via₁)

-- The lemmas of Five/D it uses (DSig; its assembly in Five.DAll gives them).
private
  lem-F1-order-Iat0 : Ws → St 1885
  lem-F1-order-Iat0 = pickᴰ 0 Sᴰ
  lem-F1-order-Kat0 : Ws → St 2565
  lem-F1-order-Kat0 = pickᴰ 1 Sᴰ
  lem-F1-order-Kat1 : Ws → St 2566
  lem-F1-order-Kat1 = pickᴰ 2 Sᴰ
  lem-F1-order-SKat0 : Ws → St 2567
  lem-F1-order-SKat0 = pickᴰ 3 Sᴰ
  lem-F1-order-SKat1 : Ws → St 2568
  lem-F1-order-SKat1 = pickᴰ 4 Sᴰ
  lem-F1-order-Sat0 : Ws → St 2569
  lem-F1-order-Sat0 = pickᴰ 5 Sᴰ
  lem-F1-order-Sat1 : Ws → St 2570
  lem-F1-order-Sat1 = pickᴰ 6 Sᴰ
  lem-F1-comm-CS-S0at0 : Ws → St 2571
  lem-F1-comm-CS-S0at0 = pickᴰ 7 Sᴰ
  lem-F1-comm-CS-S0at1 : Ws → St 2572
  lem-F1-comm-CS-S0at1 = pickᴰ 8 Sᴰ
  lem-F1-comm-CS-S1at0 : Ws → St 2573
  lem-F1-comm-CS-S1at0 = pickᴰ 9 Sᴰ
  lem-F1-comm-CS-S1at1 : Ws → St 2574
  lem-F1-comm-CS-S1at1 = pickᴰ 10 Sᴰ
  lem-F1-order-CSat0 : Ws → St 2575
  lem-F1-order-CSat0 = pickᴰ 11 Sᴰ
  lem-F1-order-CSat1 : Ws → St 2576
  lem-F1-order-CSat1 = pickᴰ 12 Sᴰ
  lem-F1-X-CS0at0 : Ws → St 2577
  lem-F1-X-CS0at0 = pickᴰ 13 Sᴰ
  lem-F1-X-CS0at1 : Ws → St 2578
  lem-F1-X-CS0at1 = pickᴰ 14 Sᴰ
  lem-F1-X-CS1at0 : Ws → St 2579
  lem-F1-X-CS1at0 = pickᴰ 15 Sᴰ
  lem-F1-X-CS1at1 : Ws → St 2580
  lem-F1-X-CS1at1 = pickᴰ 16 Sᴰ
  lem-F1-comm-CSu-CSat1 : Ws → St 2152
  lem-F1-comm-CSu-CSat1 = pickᴰ 17 Sᴰ
  lem-F1-rel-266at1 : Ws → St 2581
  lem-F1-rel-266at1 = pickᴰ 18 Sᴰ
  lem-F1-rel-267at1 : Ws → St 2582
  lem-F1-rel-267at1 = pickᴰ 19 Sᴰ
  lem-F1-rel-268at1 : Ws → St 2583
  lem-F1-rel-268at1 = pickᴰ 20 Sᴰ
  lem-F1-comm-CSu-CSat0 : Ws → St 2256
  lem-F1-comm-CSu-CSat0 = pickᴰ 21 Sᴰ
  lem-F1-rel-266at0 : Ws → St 2584
  lem-F1-rel-266at0 = pickᴰ 22 Sᴰ
  lem-F1-rel-267at0 : Ws → St 2585
  lem-F1-rel-267at0 = pickᴰ 23 Sᴰ
  lem-F1-CS-K0at0 : Ws → St 2586
  lem-F1-CS-K0at0 = pickᴰ 24 Sᴰ
  lem-F1-CS-K0at1 : Ws → St 2587
  lem-F1-CS-K0at1 = pickᴰ 25 Sᴰ
  lem-F1-CS-K1at0 : Ws → St 2588
  lem-F1-CS-K1at0 = pickᴰ 26 Sᴰ
  lem-F1-CS-K1at1 : Ws → St 2589
  lem-F1-CS-K1at1 = pickᴰ 27 Sᴰ
  lem-F1-rel-268at0 : Ws → St 2590
  lem-F1-rel-268at0 = pickᴰ 28 Sᴰ
  lem-F1-rel-272at1 : Ws → St 2591
  lem-F1-rel-272at1 = pickᴰ 29 Sᴰ
  lem-F1-rel-269at0 : Ws → St 2592
  lem-F1-rel-269at0 = pickᴰ 30 Sᴰ
  lem-F1-rel-269at1 : Ws → St 2593
  lem-F1-rel-269at1 = pickᴰ 31 Sᴰ
  lem-F1-rel-272at0 : Ws → St 2594
  lem-F1-rel-272at0 = pickᴰ 32 Sᴰ
  lem-F1-cx-cczat0 : Ws → St 2595
  lem-F1-cx-cczat0 = pickᴰ 33 Sᴰ
  lem-F1-toff-cczat0 : Ws → St 2596
  lem-F1-toff-cczat0 = pickᴰ 34 Sᴰ
  lem-F1-ck-tctat0 : Ws → St 2597
  lem-F1-ck-tctat0 = pickᴰ 35 Sᴰ

private
  variable
    n : ℕ
    w v : Word (Gen n)

f1₀ : Ws → 4 SRel, w === v → 5 ⊢ₓ λ¹ʷ w ≈ λ¹ʷ v
f1₀ c4 order-I = via₀ order-I (lem-F1-order-Iat0 c4)
f1₀ c4 order-S = via₀ order-S (lem-F1-order-Sat0 c4)
f1₀ c4 order-K = via₀ order-K (lem-F1-order-Kat0 c4)
f1₀ c4 order-SK = via₀ order-SK (lem-F1-order-SKat0 c4)
f1₀ c4 order-CS = via₀ order-CS (lem-F1-order-CSat0 c4)
f1₀ c4 comm-CS-S₀ = via₀ comm-CS-S₀ (lem-F1-comm-CS-S0at0 c4)
f1₀ c4 comm-CS-S₁ = via₀ comm-CS-S₁ (lem-F1-comm-CS-S1at0 c4)
f1₀ c4 X-CS₀ = via₀ X-CS₀ (lem-F1-X-CS0at0 c4)
f1₀ c4 X-CS₁ = via₀ X-CS₁ (lem-F1-X-CS1at0 c4)
f1₀ c4 CS-K₀ = via₀ CS-K₀ (lem-F1-CS-K0at0 c4)
f1₀ c4 CS-K₁ = via₀ CS-K₁ (lem-F1-CS-K1at0 c4)
f1₀ c4 comm-CS↑-CS = via₀ comm-CS↑-CS (lem-F1-comm-CSu-CSat0 c4)
f1₀ c4 rel-266 = via₀ rel-266 (lem-F1-rel-266at0 c4)
f1₀ c4 rel-267 = via₀ rel-267 (lem-F1-rel-267at0 c4)
f1₀ c4 rel-268 = via₀ rel-268 (lem-F1-rel-268at0 c4)
f1₀ c4 rel-269 = via₀ rel-269 (lem-F1-rel-269at0 c4)
f1₀ c4 rel-272 = via₀ rel-272 (lem-F1-rel-272at0 c4)
f1₀ c4 cx-ccz = via₀ cx-ccz (lem-F1-cx-cczat0 c4)
f1₀ c4 toff-ccz = via₀ toff-ccz (lem-F1-toff-cczat0 c4)
f1₀ c4 ck-tct = via₀ ck-tct (lem-F1-ck-tctat0 c4)
f1₀ c4 lf = PB.axiom (srelₓ (ctl-lf 0))
f1₀ c4 hyb-sq = PB.axiom (srelₓ (ctl-hsq 0))
f1₀ c4 hyb-yb = PB.axiom (srelₓ (ctl-hyb 0))

f1₁ : Ws → 3 SRel, w === v → 5 ⊢ₓ λ¹ʷ (w ↑) ≈ λ¹ʷ (v ↑)
f1₁ c4 order-I = via₁ order-I (lem-F1-order-Iat0 c4)
f1₁ c4 order-S = via₁ order-S (lem-F1-order-Sat1 c4)
f1₁ c4 order-K = via₁ order-K (lem-F1-order-Kat1 c4)
f1₁ c4 order-SK = via₁ order-SK (lem-F1-order-SKat1 c4)
f1₁ c4 order-CS = via₁ order-CS (lem-F1-order-CSat1 c4)
f1₁ c4 comm-CS-S₀ = via₁ comm-CS-S₀ (lem-F1-comm-CS-S0at1 c4)
f1₁ c4 comm-CS-S₁ = via₁ comm-CS-S₁ (lem-F1-comm-CS-S1at1 c4)
f1₁ c4 X-CS₀ = via₁ X-CS₀ (lem-F1-X-CS0at1 c4)
f1₁ c4 X-CS₁ = via₁ X-CS₁ (lem-F1-X-CS1at1 c4)
f1₁ c4 CS-K₀ = via₁ CS-K₀ (lem-F1-CS-K0at1 c4)
f1₁ c4 CS-K₁ = via₁ CS-K₁ (lem-F1-CS-K1at1 c4)
f1₁ c4 comm-CS↑-CS = via₁ comm-CS↑-CS (lem-F1-comm-CSu-CSat1 c4)
f1₁ c4 rel-266 = via₁ rel-266 (lem-F1-rel-266at1 c4)
f1₁ c4 rel-267 = via₁ rel-267 (lem-F1-rel-267at1 c4)
f1₁ c4 rel-268 = via₁ rel-268 (lem-F1-rel-268at1 c4)
f1₁ c4 rel-269 = via₁ rel-269 (lem-F1-rel-269at1 c4)
f1₁ c4 rel-272 = via₁ rel-272 (lem-F1-rel-272at1 c4)

-- The record Five.Transport takes.
f1 : Ws → F1
f1 c4 = record { f1₀ = f1₀ c4 ; f1₁ = f1₁ c4 ; f1₂ = F1Low.f1₂ c4
               ; f1₃ = F1Low.f1₃ c4 ; f1₄ = F1Low.f1₄ c4 }
