------------------------------------------------------------------------
-- Presentations of groups
--
-- The adders' netlists use every wire of their layouts (Amy, QPL
-- 2018, section 5.2 and table 2)
--
-- Table 2's qubit column counts the wires a circuit's gates touch
-- (PathSum.CRK.Qubits).  Both adders are laid out on 5n wires, and
-- here is which of them their netlists touch.
--
-- The tool's netlist (PathSum.Adder.CarryRipple), for n = m + 2 ≥ 2:
-- its compute touches a, b, carry and anc at every position (sum₀ at
-- position 0, the step into position i + 1 at the others, and the
-- first majority block the carry-in wire carry₀), and its copy every
-- bit of c (carryRipple-wires).  On the tool's layout every wire is
-- one of those (standardᶠ-onto), so the netlist touches all 5n wires
-- (Tool-wires, carryRipple-every).  For n = 1 it does not: with no
-- majority block, carry₀ is never touched, and the tool's own count
-- -- its printVerStats, run on its carryRipple -- is 4, not 5
-- (PathSum.Adder.Tool.Tool-qubits-1).
--
-- PathSum.Adder.Ripple's netlist, for every n ≥ 1: its ripple touches
-- x, y, the temporary register s and every carry (the carry blocks'
-- targets), and its copy every bit of the output z, the carry out
-- included (adder-wires); on the standard layout every wire is one of
-- those (standard-onto), so the netlist touches all 5n wires
-- (Adder-wires, adder-every).
--
-- The proofs point at a gate and at the wire in it, by unfolding the
-- blocks of the netlists; nothing is computed.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Adder.Wires where

open import Data.Bool.Base using (Bool; true; false; T)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using
  (Fin; zero; suc; combine; splitAt; join; _↑ˡ_; _↑ʳ_)
open import Data.List.Base using (List; []; _∷_; _++_; reverse)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_)
open import Data.Product.Base using (∃; ∃₂; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; trans; cong; subst)

import Data.Fin.Properties as Fin

open import PathSum.Adder.CarryRipple using
  (Reg; ra; rb; rc; ranc; rcarry; Line; innerᶠ; carry-step; sum-step;
   step; steps; sum₀; compute; copyᶠ; carryRipple; regᶠ; standardᶠ)
open import PathSum.Adder.Layout using
  (Wire; cin; xw; yw; sw; cw; zw; Layout; wire; inner; width; standard)
open import PathSum.Adder.Ripple using
  (carry-block; sum-block; carry₀; carry-last; copy₀; ripple; copy; adder;
   NonOut)
open import PathSum.Reversible using (Gate)
open import PathSum.Reversible.Wires using
  (_∈ᴿ_; ∈ᴿ-++ˡ; ∈ᴿ-++ʳ)


------------------------------------------------------------------------
-- The tool's netlist

-- The steps touch a, b, carry and anc at every position after the
-- first: the step into position i + 1 ends with plus aᵢ₊₁ bᵢ₊₁
-- carryᵢ₊₁ ancᵢ₊₁ = CNOT a anc; CNOT b anc; CNOT carry anc.

steps-wires : {m N : ℕ} (L : Layout (Line m) N) (r : Reg) → r ≢ rc →
              (i : Fin m) → wire L (r , suc i) ∈ᴿ steps L
steps-wires {zero}  L r p ()
steps-wires {suc m} L r p zero    =
  ∈ᴿ-++ˡ (step L) (steps (innerᶠ L))
         (∈ᴿ-++ʳ (carry-step L) (sum-step L) (plus r p))
  where
  plus : (r : Reg) → r ≢ rc → wire L (r , suc zero) ∈ᴿ sum-step L
  plus ra     _ = here (here refl)
  plus rb     _ = there (here (here refl))
  plus rc     p = ⊥-elim (p refl)
  plus ranc   _ = here (there (here refl))
  plus rcarry _ = there (there (here (here refl)))
steps-wires {suc m} L r p (suc i) =
  ∈ᴿ-++ʳ (step L) (steps (innerᶠ L)) (steps-wires (innerᶠ L) r p i)

-- The first majority block, maj a₀ b₀ carry₀ carry₁, begins with
-- CNOT b₀ carry₀: carry₀ is touched when there are two positions or
-- more.

steps-carry₀ : {m N : ℕ} (L : Layout (Line (suc m)) N) →
               wire L (rcarry , zero) ∈ᴿ steps L
steps-carry₀ L =
  ∈ᴿ-++ˡ (step L) (steps (innerᶠ L))
         (∈ᴿ-++ˡ (carry-step L) (sum-step L) (here (there (here refl))))

-- So compute touches a, b, carry and anc everywhere: position 0 by
-- sum₀ = CNOT a₀ anc₀; CNOT b₀ anc₀, and carry₀ by the first majority
-- block.

compute-wires : {m N : ℕ} (L : Layout (Line (suc m)) N) (r : Reg) →
                r ≢ rc → (i : Fin (suc (suc m))) →
                wire L (r , i) ∈ᴿ compute L
compute-wires L ra     _ zero    =
  ∈ᴿ-++ˡ (sum₀ L) (steps L) (here (here refl))
compute-wires L rb     _ zero    =
  ∈ᴿ-++ˡ (sum₀ L) (steps L) (there (here (here refl)))
compute-wires L rc     p zero    = ⊥-elim (p refl)
compute-wires L ranc   _ zero    =
  ∈ᴿ-++ˡ (sum₀ L) (steps L) (here (there (here refl)))
compute-wires L rcarry _ zero    = ∈ᴿ-++ʳ (sum₀ L) (steps L) (steps-carry₀ L)
compute-wires L r      p (suc i) =
  ∈ᴿ-++ʳ (sum₀ L) (steps L) (steps-wires L r p i)

-- The copy, CNOT ancᵢ cᵢ for every i, touches every bit of c.

copy-wires : {m N : ℕ} (L : Layout (Line m) N) (i : Fin (suc m)) →
             wire L (rc , i) ∈ᴿ copyᶠ L
copy-wires {zero}  L zero     = here (there (here refl))
copy-wires {zero}  L (suc ())
copy-wires {suc m} L zero     = here (there (here refl))
copy-wires {suc m} L (suc i)  = there (copy-wires (innerᶠ L) i)

-- Every wire of the layout, for n ≥ 2.

carryRipple-wires : {m N : ℕ} (L : Layout (Line (suc m)) N)
                    (v : Line (suc m)) →
                    wire L v ∈ᴿ compute L ⊎ wire L v ∈ᴿ copyᶠ L
carryRipple-wires L (rc     , i) = inj₂ (copy-wires L i)
carryRipple-wires L (ra     , i) = inj₁ (compute-wires L ra (λ ()) i)
carryRipple-wires L (rb     , i) = inj₁ (compute-wires L rb (λ ()) i)
carryRipple-wires L (ranc   , i) = inj₁ (compute-wires L ranc (λ ()) i)
carryRipple-wires L (rcarry , i) = inj₁ (compute-wires L rcarry (λ ()) i)


------------------------------------------------------------------------
-- The tool's layout

-- Every wire of the 5n is register r's bit i for some r and i.

private
  unreg : Fin 5 → Reg
  unreg zero                         = ra
  unreg (suc zero)                   = rb
  unreg (suc (suc zero))             = rc
  unreg (suc (suc (suc zero)))       = ranc
  unreg (suc (suc (suc (suc zero)))) = rcarry

  reg-unreg : (j : Fin 5) → regᶠ (unreg j) ≡ j
  reg-unreg zero                         = refl
  reg-unreg (suc zero)                   = refl
  reg-unreg (suc (suc zero))             = refl
  reg-unreg (suc (suc (suc zero)))       = refl
  reg-unreg (suc (suc (suc (suc zero)))) = refl

standardᶠ-onto : (m : ℕ) (u : Fin (5 * suc m)) →
                 ∃ λ v → wire (standardᶠ m) v ≡ u
standardᶠ-onto m u = go (Fin.combine-surjective {m = 5} {n = suc m} u)
  where
  go : (∃₂ λ (j : Fin 5) (k : Fin (suc m)) → combine j k ≡ u) →
       ∃ λ v → wire (standardᶠ m) v ≡ u
  go (j , k , e) =
    (unreg j , k) , trans (cong (λ r → combine r k) (reg-unreg j)) e

-- So for n ≥ 2 every wire is touched by the compute or by the copy,
-- hence by the netlist.

Tool-wires : (m : ℕ) → m ≢ 0 → (u : Fin (5 * suc m)) →
             u ∈ᴿ compute (standardᶠ m) ⊎ u ∈ᴿ copyᶠ (standardᶠ m)
Tool-wires zero    p u = ⊥-elim (p refl)
Tool-wires (suc m) _ u = go (standardᶠ-onto (suc m) u)
  where
  go : (∃ λ v → wire (standardᶠ (suc m)) v ≡ u) →
       u ∈ᴿ compute (standardᶠ (suc m)) ⊎ u ∈ᴿ copyᶠ (standardᶠ (suc m))
  go (v , e) =
    subst (λ w → w ∈ᴿ compute (standardᶠ (suc m)) ⊎
                 w ∈ᴿ copyᶠ (standardᶠ (suc m)))
          e (carryRipple-wires (standardᶠ (suc m)) v)

carryRipple-every : (m : ℕ) → m ≢ 0 → (u : Fin (5 * suc m)) →
                    u ∈ᴿ carryRipple (standardᶠ m)
carryRipple-every m p u =
  [ ∈ᴿ-++ˡ (compute L) (copyᶠ L ++ reverse (compute L))
  , (λ q → ∈ᴿ-++ʳ (compute L) (copyᶠ L ++ reverse (compute L))
             (∈ᴿ-++ˡ (copyᶠ L) (reverse (compute L)) q))
  ]′ (Tool-wires m p u)
  where
  L = standardᶠ m


------------------------------------------------------------------------
-- PathSum.Adder.Ripple's netlist

-- The sum block, s₀ ⊕= x₀ ⊕ y₀ (⊕ the carry in), touches x₀, y₀, s₀
-- and the carry in.

module _ {m N : ℕ} where

  sum-block-x : (b : Bool) (L : Layout (Wire b m) N) →
                wire L (xw zero) ∈ᴿ sum-block b L
  sum-block-x false L = here (here refl)
  sum-block-x true  L = here (here refl)

  sum-block-y : (b : Bool) (L : Layout (Wire b m) N) →
                wire L (yw zero) ∈ᴿ sum-block b L
  sum-block-y false L = there (here (here refl))
  sum-block-y true  L = there (here (here refl))

  sum-block-s : (b : Bool) (L : Layout (Wire b m) N) →
                wire L (sw zero) ∈ᴿ sum-block b L
  sum-block-s false L = here (there (here refl))
  sum-block-s true  L = here (there (here refl))

  sum-block-cin : (b : Bool) (L : Layout (Wire b m) N) (e : T b) →
                  wire L (cin e) ∈ᴿ sum-block b L
  sum-block-cin true  L e = there (there (here (here refl)))
  sum-block-cin false L ()

  -- The carry block's first gate is a Toffoli gate onto its target.

  carry-block-target : (b : Bool) (L : Layout (Wire b m) N) (t : Wire b m)
                       .(p : xw zero ≢ t) .(q : yw zero ≢ t)
                       .(r : ∀ e → cin e ≢ t) →
                       wire L t ∈ᴿ carry-block b L t p q r
  carry-block-target false L t p q r = here (there (there (here refl)))
  carry-block-target true  L t p q r = here (there (there (here refl)))

-- The ripple touches every wire but the output: x, y and s at each
-- position by its sum block, each carry as the target of a carry
-- block, and the carry in by the first sum block.

ripple-wires : {m N : ℕ} (b : Bool) (L : Layout (Wire b m) N)
               (v : Wire b m) → NonOut v → wire L v ∈ᴿ ripple L
ripple-wires {zero}  b L (xw zero)     _  = sum-block-x b L
ripple-wires {zero}  b L (yw zero)     _  = sum-block-y b L
ripple-wires {zero}  b L (sw zero)     _  = sum-block-s b L
ripple-wires {zero}  b L (cin e)       _  = sum-block-cin b L e
ripple-wires {zero}  b L (xw (suc ())) _
ripple-wires {zero}  b L (yw (suc ())) _
ripple-wires {zero}  b L (sw (suc ())) _
ripple-wires {zero}  b L (cw ())       _
ripple-wires {zero}  b L (zw _)        ()
ripple-wires {suc m} {N} b L v nv = go v nv
  where
  rest : List (Gate N)
  rest = sum-block b L ++ ripple (inner L)

  first : ∀ {u} → u ∈ᴿ sum-block b L → u ∈ᴿ ripple L
  first p =
    ∈ᴿ-++ʳ (carry₀ L) rest (∈ᴿ-++ˡ (sum-block b L) (ripple (inner L)) p)

  later : ∀ {u} → u ∈ᴿ ripple (inner L) → u ∈ᴿ ripple L
  later p =
    ∈ᴿ-++ʳ (carry₀ L) rest (∈ᴿ-++ʳ (sum-block b L) (ripple (inner L)) p)

  go : (v : Wire b (suc m)) → NonOut v → wire L v ∈ᴿ ripple L
  go (xw zero)    _  = first (sum-block-x b L)
  go (yw zero)    _  = first (sum-block-y b L)
  go (sw zero)    _  = first (sum-block-s b L)
  go (cin e)      _  = first (sum-block-cin b L e)
  go (cw zero)    _  =
    ∈ᴿ-++ˡ (carry₀ L) rest
           (carry-block-target b L (cw zero) (λ ()) (λ ()) (λ _ ()))
  go (xw (suc i)) _  = later (ripple-wires true (inner L) (xw i) tt)
  go (yw (suc i)) _  = later (ripple-wires true (inner L) (yw i) tt)
  go (sw (suc i)) _  = later (ripple-wires true (inner L) (sw i) tt)
  go (cw (suc j)) _  = later (ripple-wires true (inner L) (cw j) tt)
  go (zw _)       ()

-- The copy touches every bit of the output: z_k by its copy of s_k,
-- and the carry out as the target of the last carry block.

copy-wires′ : {m N : ℕ} (b : Bool) (L : Layout (Wire b m) N)
              (k : Fin (suc (suc m))) → wire L (zw k) ∈ᴿ copy L
copy-wires′ {zero}  b L zero             =
  ∈ᴿ-++ʳ (carry-last L) (copy₀ L ∷ []) (here (there (here refl)))
copy-wires′ {zero}  b L (suc zero)       =
  ∈ᴿ-++ˡ (carry-last L) (copy₀ L ∷ [])
         (carry-block-target b L (zw (suc zero)) (λ ()) (λ ()) (λ _ ()))
copy-wires′ {zero}  b L (suc (suc ()))
copy-wires′ {suc m} b L zero             = here (there (here refl))
copy-wires′ {suc m} b L (suc k)          =
  there (copy-wires′ true (inner L) k)

-- Every wire of the layout, for every n ≥ 1.

adder-wires : {m N : ℕ} (L : Layout (Wire false m) N) (v : Wire false m) →
              wire L v ∈ᴿ ripple L ⊎ wire L v ∈ᴿ copy L
adder-wires L (zw k)   = inj₂ (copy-wires′ false L k)
adder-wires L (cin ())
adder-wires L (xw i)   = inj₁ (ripple-wires false L (xw i) tt)
adder-wires L (yw i)   = inj₁ (ripple-wires false L (yw i) tt)
adder-wires L (sw i)   = inj₁ (ripple-wires false L (sw i) tt)
adder-wires L (cw j)   = inj₁ (ripple-wires false L (cw j) tt)


------------------------------------------------------------------------
-- The standard layout

-- Every wire of the 5n is a name's: x, y, z, the carries and s, block
-- after block (the layout's private decoding, redone).

private
  split-elim : {k l : ℕ} (P : Fin (k + l) → Set) →
               (∀ i → P (i ↑ˡ l)) → (∀ j → P (k ↑ʳ j)) → ∀ u → P u
  split-elim {k} {l} P f g u = go (splitAt k u) (Fin.join-splitAt k l u)
    where
    go : (s : Fin k ⊎ Fin l) → join k l s ≡ u → P u
    go (inj₁ i) e = subst P e (f i)
    go (inj₂ j) e = subst P e (g j)

standard-onto : (m : ℕ) (u : Fin (width m)) →
                ∃ λ v → wire (standard m) v ≡ u
standard-onto m =
  split-elim {suc m} {suc m + (suc (suc m) + (m + suc m))} P
    (λ i → xw i , refl)
    (split-elim {suc m} {suc (suc m) + (m + suc m)}
      (λ u → P (suc m ↑ʳ u))
      (λ i → yw i , refl)
      (split-elim {suc (suc m)} {m + suc m}
        (λ u → P (suc m ↑ʳ (suc m ↑ʳ u)))
        (λ k → zw k , refl)
        (split-elim {m} {suc m}
          (λ u → P (suc m ↑ʳ (suc m ↑ʳ (suc (suc m) ↑ʳ u))))
          (λ j → cw j , refl)
          (λ i → sw i , refl))))
  where
  P : Fin (width m) → Set
  P u = ∃ λ v → wire (standard m) v ≡ u

-- So every wire is touched by the ripple or by the copy, hence by the
-- netlist.

Adder-wires : (m : ℕ) (u : Fin (width m)) →
              u ∈ᴿ ripple (standard m) ⊎ u ∈ᴿ copy (standard m)
Adder-wires m u = go (standard-onto m u)
  where
  go : (∃ λ v → wire (standard m) v ≡ u) →
       u ∈ᴿ ripple (standard m) ⊎ u ∈ᴿ copy (standard m)
  go (v , e) =
    subst (λ w → w ∈ᴿ ripple (standard m) ⊎ w ∈ᴿ copy (standard m))
          e (adder-wires (standard m) v)

adder-every : (m : ℕ) (u : Fin (width m)) → u ∈ᴿ adder (standard m)
adder-every m u =
  [ ∈ᴿ-++ˡ (ripple L) (copy L ++ reverse (ripple L))
  , (λ q → ∈ᴿ-++ʳ (ripple L) (copy L ++ reverse (ripple L))
             (∈ᴿ-++ˡ (copy L) (reverse (ripple L)) q))
  ]′ (Adder-wires m u)
  where
  L = standard m
