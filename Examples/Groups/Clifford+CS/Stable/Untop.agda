------------------------------------------------------------------------
-- Presentations of groups
--
-- A rule of Syntactics on five wires or more is one a width down with
-- an idle wire on top
--
-- Every rule of Syntactics is stated on its bottom wires at every width
-- (at most four of them), so an instance on 4 + m + 1 wires leaves its
-- top wire idle: it is `top` of the same rule on 4 + m wires.  The
-- words are closed, so `top` of a rule's side at one width is the side
-- at the next by computation.  The transport of the four-wire rules to
-- every width (Stable.Transport) goes down a width this way.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Stable.Untop where

open import Data.Nat using (ℕ ; suc)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations using (₄₊)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (top)

private
  variable
    m : ℕ

-- The instance a width down.
record Untop (w v : Circuit (suc (₄₊ m))) : Set where
  constructor mk
  field
    {w′ v′} : Circuit (₄₊ m)
    rule      : (₄₊ m) SRel, w′ === v′
    w≡        : top w′ ≡ w
    v≡        : top v′ ≡ v

untop : ∀ {w v : Circuit (suc (₄₊ m))} → (suc (₄₊ m)) SRel, w === v → Untop w v
untop order-I     = mk order-I     Eq.refl Eq.refl
untop order-S     = mk order-S     Eq.refl Eq.refl
untop order-K     = mk order-K     Eq.refl Eq.refl
untop order-SK    = mk order-SK    Eq.refl Eq.refl
untop order-CS    = mk order-CS    Eq.refl Eq.refl
untop comm-CS-S₀  = mk comm-CS-S₀  Eq.refl Eq.refl
untop comm-CS-S₁  = mk comm-CS-S₁  Eq.refl Eq.refl
untop X-CS₀       = mk X-CS₀       Eq.refl Eq.refl
untop X-CS₁       = mk X-CS₁       Eq.refl Eq.refl
untop CS-K₀       = mk CS-K₀       Eq.refl Eq.refl
untop CS-K₁       = mk CS-K₁       Eq.refl Eq.refl
untop comm-CS↑-CS = mk comm-CS↑-CS Eq.refl Eq.refl
untop rel-266     = mk rel-266     Eq.refl Eq.refl
untop rel-267     = mk rel-267     Eq.refl Eq.refl
untop rel-268     = mk rel-268     Eq.refl Eq.refl
untop rel-269     = mk rel-269     Eq.refl Eq.refl
untop rel-272     = mk rel-272     Eq.refl Eq.refl
untop cx-ccz      = mk cx-ccz      Eq.refl Eq.refl
untop toff-ccz    = mk toff-ccz    Eq.refl Eq.refl
untop ck-tct      = mk ck-tct      Eq.refl Eq.refl
untop lf          = mk lf          Eq.refl Eq.refl
untop hyb-sq      = mk hyb-sq      Eq.refl Eq.refl
untop hyb-yb      = mk hyb-yb      Eq.refl Eq.refl
