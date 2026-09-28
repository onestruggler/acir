------------------------------------------------------------------------
-- Presentations of groups
--
-- The out-of-place ripple-carry adder, classically (Amy, QPL 2018,
-- section 5.2)
--
-- Section 5.2 verifies a Clifford+T implementation of
--
--    Adder_n : |x⟩|y⟩|0⟩ ↦ |x⟩|y⟩|x + y⟩,
--
-- "a standard out-of-place ripple-carry adder which uses n − 1 ancilla
-- bits to store intermediate carry values and an additional n bit
-- register to store the output, before copying out and uncomputing",
-- with 4(n − 1) Toffoli gates.  The paper describes the circuit in
-- words only (the one its tool generates is PathSum.Adder.CarryRipple);
-- here is one with those resources, as a netlist of Toffoli and CNOT
-- gates (PathSum.Reversible), and the proof that it computes Adder_n,
-- for every n = m + 1 ≥ 1 at once.
--
-- The netlist, on the wires of PathSum.Adder.Layout, is Bennett's
-- compute-copy-uncompute,
--
--    adder = ripple ++ copy ++ reverse ripple.
--
-- The ripple goes position by position (by recursion on m, the
-- positions after the first forming an adder with carry in c₁: the
-- inner layout).  At position i it computes the carry into i + 1,
-- c_(i+1) ⊕= maj(x_i, y_i, c_i), by the block of Vedral, Barenco and
-- Ekert's CARRY with y_i restored (majᴿ: Toffoli, CNOT, Toffoli, CNOT:
-- c_(i+1) ⊕= x_i y_i, y_i ⊕= x_i, c_(i+1) ⊕= c_i y_i, y_i ⊕= x_i -- the
-- two terms x y and c (x ⊕ y) of the majority are never both 1), or
-- at position 0, where there is no carry in, one Toffoli gate,
-- c₁ ⊕= x₀ y₀; then the sum bit into the temporary register,
-- s_i ⊕= x_i ⊕ y_i ⊕ c_i, by CNOTs.  The copy xors s_i into z_i and,
-- at the last position, the carry out into z_n by the same block.  The
-- reverse of the ripple then uncomputes the carries and the temporary
-- register.
--
-- The theorem.  Call an input blank when its scratch wires -- the
-- carries and the temporary register -- read 0 (Blank).  On a blank
-- input the output gains the n + 1 bits of x + y: z_k becomes
-- z_k ⊕ add(x, y)_k (adder-out), PathSum.Adder.Binary's add; so when
-- the output reads 0 too -- the paper's |x⟩|y⟩|0⟩ -- it ends holding
-- the bits of x + y (adder-out₀), whose value is val x + val y
-- (adder-value).  On every input, blank or not, every other wire ends
-- as it began (adder-work): x and y are unchanged (adder-inputs) and
-- the carries and the temporary register are restored (adder-clean).
-- Together: on blank inputs the netlist computes the Boolean function
-- |x⟩|y⟩|z⟩ ↦ |x⟩|y⟩|z ⊕ (x + y)⟩ (addition, which addition-out and
-- addition-work characterise; adder-computes).
--
-- The proof: the ripple writes the sum bits and the carries and leaves
-- every other wire alone (ripple-values, ripple-frame, by induction on
-- the positions, through the effect of each block); the copy then
-- xors the bits of add into the output (copy-values), and changes no
-- other wire (copy-frame); and the ripple lies within the wires other
-- than the output (ripple-within), so by Bennett's lemma
-- (PathSum.Reversible.bennett-work, bennett-out) its reverse undoes it
-- there and leaves the output as the copy made it.
--
-- Resources.  On the standard layout the adder has 5n wires
-- (PathSum.Adder.Layout.width-5n); for n ≥ 2 it has 4(n − 1) Toffoli
-- gates (adder-toffolis) and 11n − 8 CNOTs (adder-cnots), and for
-- n = 1 one Toffoli gate and 5 CNOTs.  Table 2's Adder8 and Adder16
-- have 40 and 80 qubits and, at seven T gates and two path variables
-- per Toffoli gate, 28 and 60 Toffoli gates: the counts here at n = 8
-- and n = 16 (table-2-Adder8, table-2-Adder16).  Their Clifford
-- counts, 334 and 710, are nine per Toffoli gate plus 11n − 6, two
-- more than the CNOTs here: the netlist of the paper's tool
-- (PathSum.Adder.CarryRipple) runs a full majority block at position
-- 0 and computes no carry out.  Finally the netlist
-- for n = 2 is displayed (netlist-2) and run on two inputs, 3 + 1 at
-- n = 2 and 7 + 1 at n = 3 (sum-3+1, sum-7+1), as a check that the
-- definitions mean what they say.
--
-- Not here: the Clifford+T expansion and the path-sums.  PathSum.
-- Classical's composition lemmas make the expansion of a netlist
-- compute its Boolean function (PathSum.Reversible.Expand), which the
-- theorem here identifies (PathSum.Adder.Circuit).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module PathSum.Adder.Ripple where

open import Data.Bool.Base using (Bool; true; false; T; _∧_; _xor_)
open import Data.Bool.Properties using (xor-assoc; xor-same; xor-identityʳ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc; toℕ)
open import Data.List.Base using (List; []; _∷_; _++_; reverse; map; allFin)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _∸_; _<ᵇ_)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)

open import Data.Nat.Solver using (module +-*-Solver)

import Data.Fin.Properties as Fin

open +-*-Solver using (solve; con; _:+_; _:*_; _:=_)

open import PathSum.Adder.Binary using
  (val; val-cong; maj; maj-xor; maj-false; add; add-correct₀; sumbit; carry)
open import PathSum.Adder.Layout using
  (Wire; cin; xw; yw; sw; cw; zw; shift; Layout; wire; wire-inj; inner;
   width; standard)
open import PathSum.Reversible using
  (Gate; ccx; cx; ⟪_⟫; run; run-++; ⟪⟫-here; ⟪⟫-there; run-frame;
   Within; bennett-work; bennett-out; count; count-++; count-reverse;
   is-ccx; is-cx; toffolis; cnots)

private
  variable
    b : Bool
    m N : ℕ
    W : Set

  Bits : ℕ → Set
  Bits N = Fin N → Bool

  -- Netlists evaluated at one wire.

  run-++ᵂ : (gs hs : List (Gate N)) (x : Bits N) (w : Fin N) →
            run (gs ++ hs) x w ≡ run hs (run gs x) w
  run-++ᵂ gs hs x w = cong (λ f → f w) (run-++ gs hs x)

  run-++³ : (gs hs ks : List (Gate N)) (x : Bits N) (w : Fin N) →
            run (gs ++ hs ++ ks) x w ≡ run ks (run hs (run gs x)) w
  run-++³ gs hs ks x w =
    trans (run-++ᵂ gs (hs ++ ks) x w) (run-++ᵂ hs ks (run gs x) w)

  cancel : ∀ p q → (p xor q) xor q ≡ p
  cancel p q = trans (xor-assoc p q q)
                     (trans (cong (p xor_) (xor-same q)) (xor-identityʳ p))

  maj-cong : ∀ {p p′ q q′ r r′} → p ≡ p′ → q ≡ q′ → r ≡ r′ →
             maj p q r ≡ maj p′ q′ r′
  maj-cong refl refl refl = refl


------------------------------------------------------------------------
-- Gates on named wires

-- Distinct names are distinct wires.

distinct : (L : Layout W N) (u v : W) → u ≢ v → wire L u ≢ wire L v
distinct L u v p e = p (wire-inj L u v e)

cxᴸ : (L : Layout W N) (c t : W) → .(c ≢ t) → Gate N
cxᴸ L c t p = cx (wire L c) (wire L t) (distinct L c t p)

ccxᴸ : (L : Layout W N) (c₁ c₂ t : W) →
       .(c₁ ≢ c₂) → .(c₁ ≢ t) → .(c₂ ≢ t) → Gate N
ccxᴸ L c₁ c₂ t p q r = ccx (wire L c₁) (wire L c₂) (wire L t)
  (distinct L c₁ c₂ p) (distinct L c₁ t q) (distinct L c₂ t r)


------------------------------------------------------------------------
-- The carry block

-- t ⊕= maj(x, y, c), with y restored: t ⊕= x y, y ⊕= x, t ⊕= c y,
-- y ⊕= x (Vedral, Barenco and Ekert's CARRY, then a CNOT restoring y).

majᴿ : (x y c t : Fin N) → .(x ≢ y) → .(x ≢ t) → .(y ≢ t) → .(c ≢ y) →
       .(c ≢ t) → List (Gate N)
majᴿ x y c t xy xt yt cy ct =
  ccx x y t xy xt yt ∷ cx x y xy ∷ ccx c y t cy ct yt ∷ cx x y xy ∷ []

module _ {x y c t : Fin N} (xy : x ≢ y) (xt : x ≢ t) (yt : y ≢ t)
         (cy : c ≢ y) (ct : c ≢ t) (u : Bits N) where

  private
    g₁ g₂ g₃ : Gate N
    g₁ = ccx x y t xy xt yt
    g₂ = cx x y xy
    g₃ = ccx c y t cy ct yt

    u₁ u₂ u₃ : Bits N
    u₁ = ⟪ g₁ ⟫ u
    u₂ = ⟪ g₂ ⟫ u₁
    u₃ = ⟪ g₃ ⟫ u₂

    ty : t ≢ y
    ty e = yt (sym e)

    u₁-x : u₁ x ≡ u x
    u₁-x = ⟪⟫-there g₁ u xt

    u₂-x : u₂ x ≡ u x
    u₂-x = trans (⟪⟫-there g₂ u₁ xy) u₁-x

    u₂-y : u₂ y ≡ u y xor u x
    u₂-y = trans (⟪⟫-here g₂ u₁) (cong₂ _xor_ (⟪⟫-there g₁ u yt) u₁-x)

    u₂-c : u₂ c ≡ u c
    u₂-c = trans (⟪⟫-there g₂ u₁ cy) (⟪⟫-there g₁ u ct)

    u₂-t : u₂ t ≡ u t xor (u x ∧ u y)
    u₂-t = trans (⟪⟫-there g₂ u₁ ty) (⟪⟫-here g₁ u)

  -- The target gains maj(x, y, c) = x y ⊕ c (y ⊕ x) ...

  majᴿ-here : run (majᴿ x y c t xy xt yt cy ct) u t ≡
              u t xor maj (u x) (u y) (u c)
  majᴿ-here =
    trans (⟪⟫-there (cx x y xy) u₃ ty)
    (trans (⟪⟫-here g₃ u₂)
    (trans (cong₂ _xor_ u₂-t (cong₂ _∧_ u₂-c u₂-y))
    (trans (xor-assoc (u t) (u x ∧ u y) (u c ∧ (u y xor u x)))
           (cong (u t xor_) (sym (maj-xor (u x) (u y) (u c)))))))

  -- ... and every other wire, y included, is as it was.

  majᴿ-there : ∀ w → w ≢ t → run (majᴿ x y c t xy xt yt cy ct) u w ≡ u w
  majᴿ-there w w≢t = go (w Fin.≟ y)
    where
    go : Dec (w ≡ y) → run (majᴿ x y c t xy xt yt cy ct) u w ≡ u w
    go (no w≢y)  = run-frame (majᴿ x y c t xy xt yt cy ct) u
                             (w≢t ∷ w≢y ∷ w≢t ∷ w≢y ∷ [])
    go (yes w≡y) =
      trans (cong (run (majᴿ x y c t xy xt yt cy ct) u) w≡y)
      (trans (⟪⟫-here (cx x y xy) u₃)
      (trans (cong₂ _xor_ (trans (⟪⟫-there g₃ u₂ yt) u₂-y)
                          (trans (⟪⟫-there g₃ u₂ xt) u₂-x))
      (trans (cancel (u y) (u x)) (cong u (sym w≡y)))))

-- The carry in of a layout, as a bit: 0 when there is no carry-in wire.

cinv : (b : Bool) → Layout (Wire b m) N → Bits N → Bool
cinv false L u = false
cinv true  L u = u (wire L (cin tt))

cinv-≡ : (b : Bool) (L : Layout (Wire b m) N) {u u′ : Bits N} →
         (∀ e → u (wire L (cin e)) ≡ u′ (wire L (cin e))) →
         cinv b L u ≡ cinv b L u′
cinv-≡ false L h = refl
cinv-≡ true  L h = h tt

-- t ⊕= maj(x₀, y₀, c_in): majᴿ, or without a carry in one Toffoli gate,
-- t ⊕= x₀ y₀.

carry-block : (b : Bool) (L : Layout (Wire b m) N) (t : Wire b m) →
              .(xw zero ≢ t) → .(yw zero ≢ t) → .(∀ e → cin e ≢ t) →
              List (Gate N)
carry-block false L t p q r = ccxᴸ L (xw zero) (yw zero) t (λ ()) p q ∷ []
carry-block true  L t p q r =
  majᴿ (wire L (xw zero)) (wire L (yw zero)) (wire L (cin tt)) (wire L t)
       (distinct L (xw zero) (yw zero) (λ ())) (distinct L (xw zero) t p)
       (distinct L (yw zero) t q) (distinct L (cin tt) (yw zero) (λ ()))
       (distinct L (cin tt) t (r tt))

carry-block-here :
  (b : Bool) (L : Layout (Wire b m) N) (t : Wire b m) (p : xw zero ≢ t)
  (q : yw zero ≢ t) (r : ∀ e → cin e ≢ t) (u : Bits N) →
  run (carry-block b L t p q r) u (wire L t) ≡
  u (wire L t) xor maj (u (wire L (xw zero))) (u (wire L (yw zero)))
                       (cinv b L u)
carry-block-here false L t p q r u =
  trans (⟪⟫-here (ccxᴸ L (xw zero) (yw zero) t (λ ()) p q) u)
        (cong (u (wire L t) xor_)
              (sym (maj-false (u (wire L (xw zero))) (u (wire L (yw zero))))))
carry-block-here true L t p q r u =
  majᴿ-here (distinct L (xw zero) (yw zero) (λ ())) (distinct L (xw zero) t p)
            (distinct L (yw zero) t q) (distinct L (cin tt) (yw zero) (λ ()))
            (distinct L (cin tt) t (r tt)) u

carry-block-there :
  (b : Bool) (L : Layout (Wire b m) N) (t : Wire b m) (p : xw zero ≢ t)
  (q : yw zero ≢ t) (r : ∀ e → cin e ≢ t) (u : Bits N) →
  ∀ w → w ≢ wire L t → run (carry-block b L t p q r) u w ≡ u w
carry-block-there false L t p q r u w w≢t =
  ⟪⟫-there (ccxᴸ L (xw zero) (yw zero) t (λ ()) p q) u w≢t
carry-block-there true L t p q r u w w≢t =
  majᴿ-there (distinct L (xw zero) (yw zero) (λ ()))
             (distinct L (xw zero) t p) (distinct L (yw zero) t q)
             (distinct L (cin tt) (yw zero) (λ ()))
             (distinct L (cin tt) t (r tt)) u w w≢t


------------------------------------------------------------------------
-- The sum block

-- s₀ ⊕= x₀ ⊕ y₀ ⊕ c_in, by CNOTs.

sum-block : (b : Bool) → Layout (Wire b m) N → List (Gate N)
sum-block false L =
  cxᴸ L (xw zero) (sw zero) (λ ()) ∷ cxᴸ L (yw zero) (sw zero) (λ ()) ∷ []
sum-block true  L =
  cxᴸ L (xw zero) (sw zero) (λ ()) ∷ cxᴸ L (yw zero) (sw zero) (λ ()) ∷
  cxᴸ L (cin tt) (sw zero) (λ ()) ∷ []

sum-block-here :
  (b : Bool) (L : Layout (Wire b m) N) (u : Bits N) →
  run (sum-block b L) u (wire L (sw zero)) ≡
  u (wire L (sw zero)) xor
    (u (wire L (xw zero)) xor (u (wire L (yw zero)) xor cinv b L u))
sum-block-here false L u =
  trans (⟪⟫-here g₂ u₁)
  (trans (cong₂ _xor_ (⟪⟫-here g₁ u)
                      (⟪⟫-there g₁ u (distinct L (yw zero) (sw zero) (λ ()))))
  (trans (xor-assoc (u s) (u x₀) (u y₀))
         (cong (λ v → u s xor (u x₀ xor v)) (sym (xor-identityʳ (u y₀))))))
  where
  s x₀ y₀ : Fin _
  s  = wire L (sw zero)
  x₀ = wire L (xw zero)
  y₀ = wire L (yw zero)

  g₁ g₂ : Gate _
  g₁ = cxᴸ L (xw zero) (sw zero) (λ ())
  g₂ = cxᴸ L (yw zero) (sw zero) (λ ())

  u₁ : Bits _
  u₁ = ⟪ g₁ ⟫ u
sum-block-here true L u =
  trans (⟪⟫-here g₃ u₂)
  (trans (cong₂ _xor_
           (trans (⟪⟫-here g₂ u₁)
                  (cong₂ _xor_ (⟪⟫-here g₁ u)
                               (⟪⟫-there g₁ u (distinct L (yw zero) (sw zero)
                                                        (λ ())))))
           (trans (⟪⟫-there g₂ u₁ (distinct L (cin tt) (sw zero) (λ ())))
                  (⟪⟫-there g₁ u (distinct L (cin tt) (sw zero) (λ ())))))
  (trans (xor-assoc (u s xor u x₀) (u y₀) (u c₀))
         (xor-assoc (u s) (u x₀) (u y₀ xor u c₀))))
  where
  s x₀ y₀ c₀ : Fin _
  s  = wire L (sw zero)
  x₀ = wire L (xw zero)
  y₀ = wire L (yw zero)
  c₀ = wire L (cin tt)

  g₁ g₂ g₃ : Gate _
  g₁ = cxᴸ L (xw zero) (sw zero) (λ ())
  g₂ = cxᴸ L (yw zero) (sw zero) (λ ())
  g₃ = cxᴸ L (cin tt) (sw zero) (λ ())

  u₁ u₂ : Bits _
  u₁ = ⟪ g₁ ⟫ u
  u₂ = ⟪ g₂ ⟫ u₁

sum-block-there : (b : Bool) (L : Layout (Wire b m) N) (u : Bits N) →
                  ∀ w → w ≢ wire L (sw zero) → run (sum-block b L) u w ≡ u w
sum-block-there false L u w w≢s =
  run-frame (sum-block false L) u (w≢s ∷ w≢s ∷ [])
sum-block-there true  L u w w≢s =
  run-frame (sum-block true L) u (w≢s ∷ w≢s ∷ w≢s ∷ [])


------------------------------------------------------------------------
-- The netlist

-- The carry out of position 0: into c₁, or, at the last position, into
-- the output's last bit.  The sum bit's copy into the output.

carry₀ : Layout (Wire b (suc m)) N → List (Gate N)
carry₀ {b} L = carry-block b L (cw zero) (λ ()) (λ ()) (λ _ ())

carry-last : Layout (Wire b zero) N → List (Gate N)
carry-last {b} L = carry-block b L (zw (suc zero)) (λ ()) (λ ()) (λ _ ())

copy₀ : Layout (Wire b m) N → Gate N
copy₀ L = cxᴸ L (sw zero) (zw zero) (λ ())

-- The ripple: at each position the carry into the next, then the sum
-- bit.

ripple : Layout (Wire b m) N → List (Gate N)
ripple {b} {zero}  L = sum-block b L
ripple {b} {suc m} L = carry₀ L ++ sum-block b L ++ ripple (inner L)

-- The copy: each sum bit into the output, and at the last position the
-- carry out.

copy : Layout (Wire b m) N → List (Gate N)
copy {b} {zero}  L = carry-last L ++ copy₀ L ∷ []
copy {b} {suc m} L = copy₀ L ∷ copy (inner L)

-- The adder: compute, copy, uncompute.

adder : Layout (Wire false m) N → List (Gate N)
adder L = ripple L ++ copy L ++ reverse (ripple L)


------------------------------------------------------------------------
-- Kinds of wires

-- The wires the ripple writes and leaves written: the carries and the
-- temporary register.

Scratch : Wire b m → Set
Scratch (sw _) = ⊤
Scratch (cw _) = ⊤
Scratch _      = ⊥

-- Every wire but the output.

NonOut : Wire b m → Set
NonOut (zw _) = ⊥
NonOut _      = ⊤

-- shift respects the kinds, and never names s₀ or, from a scratch
-- wire, c₁.

private
  scratch-shift : (v : Wire true m) → Scratch v → Scratch (shift {b = b} v)
  scratch-shift (sw _)  _  = tt
  scratch-shift (cw _)  _  = tt
  scratch-shift (cin _) ()
  scratch-shift (xw _)  ()
  scratch-shift (yw _)  ()
  scratch-shift (zw _)  ()

  nonout-shift : (v : Wire true m) → NonOut v → NonOut (shift {b = b} v)
  nonout-shift (cin _) _ = tt
  nonout-shift (xw _)  _ = tt
  nonout-shift (yw _)  _ = tt
  nonout-shift (sw _)  _ = tt
  nonout-shift (cw _)  _ = tt
  nonout-shift (zw _)  ()

  shift≢sw₀ : (v : Wire true m) → shift {b = b} v ≢ sw zero
  shift≢sw₀ (cin _) ()
  shift≢sw₀ (xw _)  ()
  shift≢sw₀ (yw _)  ()
  shift≢sw₀ (sw _)  ()
  shift≢sw₀ (cw _)  ()
  shift≢sw₀ (zw _)  ()

  shift≢cw₀ : (v : Wire true m) → Scratch v → shift {b = b} v ≢ cw zero
  shift≢cw₀ (sw _)  _ ()
  shift≢cw₀ (cw _)  _ ()
  shift≢cw₀ (cin _) ()
  shift≢cw₀ (xw _)  ()
  shift≢cw₀ (yw _)  ()
  shift≢cw₀ (zw _)  ()

-- The wires of the circuit that are no scratch wire of the layout.

Unscratched : Layout (Wire b m) N → Fin N → Set
Unscratched L w = ∀ v → Scratch v → wire L v ≢ w


------------------------------------------------------------------------
-- The ripple

-- It writes no wire but the carries and the temporary register (y is
-- written by each carry block, and restored).

ripple-frame : (L : Layout (Wire b m) N) (u : Bits N) (w : Fin N) →
               Unscratched L w → run (ripple L) u w ≡ u w
ripple-frame {b} {zero}  L u w h =
  sum-block-there b L u w (λ e → h (sw zero) tt (sym e))
ripple-frame {b} {suc m} L u w h =
  trans (run-++³ (carry₀ L) (sum-block b L) (ripple (inner L)) u w)
  (trans (ripple-frame (inner L) (run (sum-block b L) (run (carry₀ L) u)) w
                       (λ v s → h (shift v) (scratch-shift v s)))
  (trans (sum-block-there b L (run (carry₀ L) u) w
                          (λ e → h (sw zero) tt (sym e)))
         (carry-block-there b L (cw zero) (λ ()) (λ ()) (λ _ ()) u w
                            (λ e → h (cw zero) tt (sym e)))))

-- From an input whose carries and temporary register read 0, it writes
-- the sum bits into the temporary register and the carries into the
-- carry wires.

ripple-values :
  (L : Layout (Wire b m) N) (u : Bits N) (a a′ : Fin (suc m) → Bool)
  (c : Bool) →
  (∀ i → u (wire L (xw i)) ≡ a i) → (∀ i → u (wire L (yw i)) ≡ a′ i) →
  cinv b L u ≡ c →
  (∀ i → u (wire L (sw i)) ≡ false) → (∀ j → u (wire L (cw j)) ≡ false) →
  (∀ i → run (ripple L) u (wire L (sw i)) ≡ sumbit a a′ c i) ×
  (∀ j → run (ripple L) u (wire L (cw j)) ≡ carry a a′ c j)
ripple-values {b} {zero} L u a a′ c hx hy hc hs hk =
  (λ { zero → sum₀ ; (suc ()) }) , (λ ())
  where
  sum₀ : run (sum-block b L) u (wire L (sw zero)) ≡ sumbit a a′ c zero
  sum₀ = trans (sum-block-here b L u)
               (cong₂ _xor_ (hs zero)
                      (cong₂ _xor_ (hx zero) (cong₂ _xor_ (hy zero) hc)))
ripple-values {b} {suc m} {N} L u a a′ c hx hy hc hs hk = sums , carries
  where
  u₁ u₂ : Bits N
  u₁ = run (carry₀ L) u
  u₂ = run (sum-block b L) u₁

  c′ : Bool
  c′ = maj (a zero) (a′ zero) c

  -- The carry block writes c₁ only, with the first carry ...

  u₁-off : ∀ w → w ≢ wire L (cw zero) → u₁ w ≡ u w
  u₁-off = carry-block-there b L (cw zero) (λ ()) (λ ()) (λ _ ()) u

  u₁-c₁ : u₁ (wire L (cw zero)) ≡ c′
  u₁-c₁ = trans (carry-block-here b L (cw zero) (λ ()) (λ ()) (λ _ ()) u)
                (cong₂ _xor_ (hk zero) (maj-cong (hx zero) (hy zero) hc))

  -- ... and the sum block s₀ only, with the first sum bit.

  u₂-off : ∀ w → w ≢ wire L (sw zero) → u₂ w ≡ u₁ w
  u₂-off = sum-block-there b L u₁

  u₂-u : (v : Wire b (suc m)) → v ≢ sw zero → v ≢ cw zero →
         u₂ (wire L v) ≡ u (wire L v)
  u₂-u v p q = trans (u₂-off _ (distinct L v (sw zero) p))
                     (u₁-off _ (distinct L v (cw zero) q))

  u₂-s₀ : u₂ (wire L (sw zero)) ≡ sumbit a a′ c zero
  u₂-s₀ =
    trans (sum-block-here b L u₁)
    (cong₂ _xor_
      (trans (u₁-off _ (distinct L (sw zero) (cw zero) (λ ()))) (hs zero))
      (cong₂ _xor_
        (trans (u₁-off _ (distinct L (xw zero) (cw zero) (λ ()))) (hx zero))
        (cong₂ _xor_
          (trans (u₁-off _ (distinct L (yw zero) (cw zero) (λ ()))) (hy zero))
          (trans (cinv-≡ b L (λ e → u₁-off _ (distinct L (cin e) (cw zero)
                                                           (λ ()))))
                 hc))))

  u₂-c₁ : u₂ (wire L (cw zero)) ≡ c′
  u₂-c₁ = trans (u₂-off _ (distinct L (cw zero) (sw zero) (λ ()))) u₁-c₁

  -- The remaining positions, with carry in c₁.

  inner-values :
    (∀ i → run (ripple (inner L)) u₂ (wire L (sw (suc i))) ≡
           sumbit (λ j → a (suc j)) (λ j → a′ (suc j)) c′ i) ×
    (∀ j → run (ripple (inner L)) u₂ (wire L (cw (suc j))) ≡
           carry (λ i → a (suc i)) (λ i → a′ (suc i)) c′ j)
  inner-values =
    ripple-values (inner L) u₂ (λ j → a (suc j)) (λ j → a′ (suc j)) c′
      (λ i → trans (u₂-u (xw (suc i)) (λ ()) (λ ())) (hx (suc i)))
      (λ i → trans (u₂-u (yw (suc i)) (λ ()) (λ ())) (hy (suc i)))
      u₂-c₁
      (λ i → trans (u₂-u (sw (suc i)) (λ ()) (λ ())) (hs (suc i)))
      (λ j → trans (u₂-u (cw (suc j)) (λ ()) (λ ())) (hk (suc j)))

  away-s₀ : Unscratched (inner L) (wire L (sw zero))
  away-s₀ v s e = shift≢sw₀ v (wire-inj L (shift v) (sw zero) e)

  away-c₁ : Unscratched (inner L) (wire L (cw zero))
  away-c₁ v s e = shift≢cw₀ v s (wire-inj L (shift v) (cw zero) e)

  sums : ∀ i → run (ripple L) u (wire L (sw i)) ≡ sumbit a a′ c i
  sums zero    =
    trans (run-++³ (carry₀ L) (sum-block b L) (ripple (inner L)) u
                   (wire L (sw zero)))
    (trans (ripple-frame (inner L) u₂ (wire L (sw zero)) away-s₀) u₂-s₀)
  sums (suc i) =
    trans (run-++³ (carry₀ L) (sum-block b L) (ripple (inner L)) u
                   (wire L (sw (suc i))))
          (proj₁ inner-values i)

  carries : ∀ j → run (ripple L) u (wire L (cw j)) ≡ carry a a′ c j
  carries zero    =
    trans (run-++³ (carry₀ L) (sum-block b L) (ripple (inner L)) u
                   (wire L (cw zero)))
    (trans (ripple-frame (inner L) u₂ (wire L (cw zero)) away-c₁) u₂-c₁)
  carries (suc j) =
    trans (run-++³ (carry₀ L) (sum-block b L) (ripple (inner L)) u
                   (wire L (cw (suc j))))
          (proj₂ inner-values j)

-- It lies within the wires other than the output: its gates' wires are
-- all named by names other than an output's.

private
  carry-block-within :
    (b : Bool) (L : Layout (Wire b m) N) (t : Wire b m) (p : xw zero ≢ t)
    (q : yw zero ≢ t) (r : ∀ e → cin e ≢ t) (Q : Fin N → Set) →
    (∀ v → NonOut v → Q (wire L v)) → NonOut t →
    All (Within Q) (carry-block b L t p q r)
  carry-block-within false L t p q r Q hQ nt =
    (hQ (xw zero) tt , hQ (yw zero) tt , hQ t nt) ∷ []
  carry-block-within true  L t p q r Q hQ nt =
    (hQ (xw zero) tt , hQ (yw zero) tt , hQ t nt) ∷
    (hQ (xw zero) tt , hQ (yw zero) tt) ∷
    (hQ (cin tt) tt , hQ (yw zero) tt , hQ t nt) ∷
    (hQ (xw zero) tt , hQ (yw zero) tt) ∷ []

  sum-block-within : (b : Bool) (L : Layout (Wire b m) N) (Q : Fin N → Set) →
                     (∀ v → NonOut v → Q (wire L v)) →
                     All (Within Q) (sum-block b L)
  sum-block-within false L Q hQ =
    (hQ (xw zero) tt , hQ (sw zero) tt) ∷
    (hQ (yw zero) tt , hQ (sw zero) tt) ∷ []
  sum-block-within true  L Q hQ =
    (hQ (xw zero) tt , hQ (sw zero) tt) ∷
    (hQ (yw zero) tt , hQ (sw zero) tt) ∷
    (hQ (cin tt) tt , hQ (sw zero) tt) ∷ []

ripple-within : (L : Layout (Wire b m) N) (Q : Fin N → Set) →
                (∀ v → NonOut v → Q (wire L v)) → All (Within Q) (ripple L)
ripple-within {b} {zero}  L Q hQ = sum-block-within b L Q hQ
ripple-within {b} {suc m} L Q hQ =
  ++⁺ (carry-block-within b L (cw zero) (λ ()) (λ ()) (λ _ ()) Q hQ tt)
  (++⁺ (sum-block-within b L Q hQ)
       (ripple-within (inner L) Q (λ v nv → hQ (shift v) (nonout-shift v nv))))


------------------------------------------------------------------------
-- The copy

-- It writes no wire but the output ...

copy-frame : (L : Layout (Wire b m) N) (u : Bits N) (w : Fin N) →
             (∀ k → wire L (zw k) ≢ w) → run (copy L) u w ≡ u w
copy-frame {b} {zero}  L u w h =
  trans (run-++ᵂ (carry-last L) (copy₀ L ∷ []) u w)
  (trans (⟪⟫-there (copy₀ L) (run (carry-last L) u) (λ e → h zero (sym e)))
         (carry-block-there b L (zw (suc zero)) (λ ()) (λ ()) (λ _ ()) u w
                            (λ e → h (suc zero) (sym e))))
copy-frame {b} {suc m} L u w h =
  trans (copy-frame (inner L) (⟪ copy₀ L ⟫ u) w (λ k → h (suc k)))
        (⟪⟫-there (copy₀ L) u (λ e → h zero (sym e)))

-- ... where, after the ripple, it writes the bits of the addition.

copy-values :
  (L : Layout (Wire b m) N) (u : Bits N) (a a′ : Fin (suc m) → Bool)
  (c : Bool) →
  (∀ i → u (wire L (xw i)) ≡ a i) → (∀ i → u (wire L (yw i)) ≡ a′ i) →
  cinv b L u ≡ c →
  (∀ i → u (wire L (sw i)) ≡ sumbit a a′ c i) →
  (∀ j → u (wire L (cw j)) ≡ carry a a′ c j) →
  ∀ k → run (copy L) u (wire L (zw k)) ≡ u (wire L (zw k)) xor add a a′ c k
copy-values {b} {zero} L u a a′ c hx hy hc hs hk zero =
  trans (run-++ᵂ (carry-last L) (copy₀ L ∷ []) u (wire L (zw zero)))
  (trans (⟪⟫-here (copy₀ L) (run (carry-last L) u))
         (cong₂ _xor_
           (carry-block-there b L (zw (suc zero)) (λ ()) (λ ()) (λ _ ()) u _
                              (distinct L (zw zero) (zw (suc zero)) (λ ())))
           (trans (carry-block-there b L (zw (suc zero)) (λ ()) (λ ())
                                     (λ _ ()) u _
                                     (distinct L (sw zero) (zw (suc zero))
                                               (λ ())))
                  (hs zero))))
copy-values {b} {zero} L u a a′ c hx hy hc hs hk (suc zero) =
  trans (run-++ᵂ (carry-last L) (copy₀ L ∷ []) u (wire L (zw (suc zero))))
  (trans (⟪⟫-there (copy₀ L) (run (carry-last L) u)
                   (distinct L (zw (suc zero)) (zw zero) (λ ())))
  (trans (carry-block-here b L (zw (suc zero)) (λ ()) (λ ()) (λ _ ()) u)
         (cong (u (wire L (zw (suc zero))) xor_)
               (maj-cong (hx zero) (hy zero) hc))))
copy-values {b} {zero} L u a a′ c hx hy hc hs hk (suc (suc ()))
copy-values {b} {suc m} L u a a′ c hx hy hc hs hk zero =
  trans (copy-frame (inner L) (⟪ copy₀ L ⟫ u) (wire L (zw zero))
                    (λ k → distinct L (zw (suc k)) (zw zero) (λ ())))
  (trans (⟪⟫-here (copy₀ L) u) (cong (u (wire L (zw zero)) xor_) (hs zero)))
copy-values {b} {suc m} L u a a′ c hx hy hc hs hk (suc k) =
  trans (copy-values (inner L) (⟪ copy₀ L ⟫ u)
           (λ j → a (suc j)) (λ j → a′ (suc j)) (maj (a zero) (a′ zero) c)
           (λ i → trans (off (xw (suc i)) (λ ())) (hx (suc i)))
           (λ i → trans (off (yw (suc i)) (λ ())) (hy (suc i)))
           (trans (off (cw zero) (λ ())) (hk zero))
           (λ i → trans (off (sw (suc i)) (λ ())) (hs (suc i)))
           (λ j → trans (off (cw (suc j)) (λ ())) (hk (suc j)))
           k)
        (cong (_xor add a a′ c (suc k)) (off (zw (suc k)) (λ ())))
  where
  off : (v : Wire b (suc m)) → v ≢ zw zero →
        ⟪ copy₀ L ⟫ u (wire L v) ≡ u (wire L v)
  off v p = ⟪⟫-there (copy₀ L) u (distinct L v (zw zero) p)


------------------------------------------------------------------------
-- The adder

-- The input registers of an assignment, as bit vectors.

xbits ybits : Layout (Wire b m) N → Bits N → Fin (suc m) → Bool
xbits L x i = x (wire L (xw i))
ybits L x i = x (wire L (yw i))

-- The inputs the adder is for: its scratch wires, the carries and the
-- temporary register, read 0.

Blank : Layout (Wire b m) N → Bits N → Set
Blank L x = ∀ v → Scratch v → x (wire L v) ≡ false

-- The wires other than the output.

Work : Layout (Wire b m) N → Fin N → Set
Work L w = ∀ k → wire L (zw k) ≢ w

module _ (L : Layout (Wire false m) N) where

  private
    out≢ : ∀ {k} {v : Wire false m} → zw k ≡ v → NonOut v → ⊥
    out≢ refl ()

    work : ∀ v → NonOut v → Work L (wire L v)
    work v nv k e = out≢ (wire-inj L (zw k) v e) nv

    within : All (Within (Work L)) (ripple L)
    within = ripple-within L (Work L) work

    unscratched : (v : Wire false m) → ¬ Scratch v → Unscratched L (wire L v)
    unscratched v ns v′ s e = ns (subst Scratch (wire-inj L v′ v e) s)

  -- Every wire but the output ends as it began, on every input.

  adder-work : (x : Bits N) (w : Fin N) → Work L w → run (adder L) x w ≡ x w
  adder-work x w q =
    bennett-work (Work L) (ripple L) (copy L) within
                 (λ u w′ q′ → copy-frame L u w′ q′) x w q

  -- In particular x and y are unchanged, and the carries and the
  -- temporary register are restored.

  adder-inputs : (x : Bits N) →
                 (∀ i → run (adder L) x (wire L (xw i)) ≡ x (wire L (xw i))) ×
                 (∀ i → run (adder L) x (wire L (yw i)) ≡ x (wire L (yw i)))
  adder-inputs x = (λ i → adder-work x _ (work (xw i) tt))
                 , (λ i → adder-work x _ (work (yw i) tt))

  adder-clean : (x : Bits N) → Blank L x →
                (∀ j → run (adder L) x (wire L (cw j)) ≡ false) ×
                (∀ i → run (adder L) x (wire L (sw i)) ≡ false)
  adder-clean x bl =
    (λ j → trans (adder-work x _ (work (cw j) tt)) (bl (cw j) tt)) ,
    (λ i → trans (adder-work x _ (work (sw i) tt)) (bl (sw i) tt))

  -- On a blank input the output gains the n + 1 bits of x + y:
  -- |x⟩|y⟩|z⟩ ↦ |x⟩|y⟩|z ⊕ (x + y)⟩.

  adder-out : (x : Bits N) → Blank L x →
              ∀ k → run (adder L) x (wire L (zw k)) ≡
                    x (wire L (zw k)) xor add (xbits L x) (ybits L x) false k
  adder-out x bl k =
    trans (bennett-out (Work L) (ripple L) (copy L) within x (wire L (zw k))
                       (λ q → q k refl))
    (trans (copy-values L u (xbits L x) (ybits L x) false
              (λ i → ripple-frame L x _ (unscratched (xw i) (λ ())))
              (λ i → ripple-frame L x _ (unscratched (yw i) (λ ())))
              refl (proj₁ values) (proj₂ values) k)
           (cong (_xor add (xbits L x) (ybits L x) false k)
                 (ripple-frame L x _ (unscratched (zw k) (λ ())))))
    where
    u : Bits N
    u = run (ripple L) x

    values :
      (∀ i → u (wire L (sw i)) ≡ sumbit (xbits L x) (ybits L x) false i) ×
      (∀ j → u (wire L (cw j)) ≡ carry (xbits L x) (ybits L x) false j)
    values = ripple-values L x (xbits L x) (ybits L x) false
               (λ i → refl) (λ i → refl) refl
               (λ i → bl (sw i) tt) (λ j → bl (cw j) tt)

  -- The paper's case, the output 0 too: |x⟩|y⟩|0⟩ ↦ |x⟩|y⟩|x + y⟩, the
  -- output holding the bits of x + y, whose value is val x + val y.

  adder-out₀ : (x : Bits N) → Blank L x →
               (∀ k → x (wire L (zw k)) ≡ false) →
               ∀ k → run (adder L) x (wire L (zw k)) ≡
                     add (xbits L x) (ybits L x) false k
  adder-out₀ x bl z0 k =
    trans (adder-out x bl k)
          (cong (_xor add (xbits L x) (ybits L x) false k) (z0 k))

  adder-value : (x : Bits N) → Blank L x →
                (∀ k → x (wire L (zw k)) ≡ false) →
                val (λ k → run (adder L) x (wire L (zw k))) ≡
                val (xbits L x) + val (ybits L x)
  adder-value x bl z0 =
    trans (val-cong (adder-out₀ x bl z0))
          (add-correct₀ (xbits L x) (ybits L x))

  -- As a Boolean function: on blank inputs the netlist computes
  -- |x⟩|y⟩|z⟩ ↦ |x⟩|y⟩|z ⊕ (x + y)⟩, every other wire unchanged.  The
  -- bit a wire gains is found by searching the output for it (out?,
  -- gain): the bit of x + y at its index if it is z_k, 0 otherwise.

  out? : (w : Fin N) → Dec (∃ λ k → wire L (zw k) ≡ w)
  out? w = Fin.any? (λ k → wire L (zw k) Fin.≟ w)

  gain : (x : Bits N) (w : Fin N) → Dec (∃ λ k → wire L (zw k) ≡ w) → Bool
  gain x w (yes (k , _)) = add (xbits L x) (ybits L x) false k
  gain x w (no _)        = false

  addition : Bits N → Bits N
  addition x w = x w xor gain x w (out? w)

  -- What it does, independently of the search.

  addition-out : (x : Bits N) →
                 ∀ k → addition x (wire L (zw k)) ≡
                       x (wire L (zw k)) xor add (xbits L x) (ybits L x) false k
  addition-out x k = cong (x (wire L (zw k)) xor_) (go (out? (wire L (zw k))))
    where
    go : (d : Dec (∃ λ k′ → wire L (zw k′) ≡ wire L (zw k))) →
         gain x (wire L (zw k)) d ≡ add (xbits L x) (ybits L x) false k
    go (yes (k′ , e)) = cong (add (xbits L x) (ybits L x) false)
                             (zw-injective (wire-inj L (zw k′) (zw k) e))
      where
      zw-injective : ∀ {i j} → zw {false} {m} i ≡ zw j → i ≡ j
      zw-injective refl = refl
    go (no ¬o)        = ⊥-elim (¬o (k , refl))

  addition-work : (x : Bits N) (w : Fin N) → Work L w → addition x w ≡ x w
  addition-work x w q = go (out? w)
    where
    go : (d : Dec (∃ λ k → wire L (zw k) ≡ w)) → x w xor gain x w d ≡ x w
    go (yes (k , e)) = ⊥-elim (q k e)
    go (no _)        = xor-identityʳ (x w)

  -- The netlist computes it on blank inputs.

  adder-computes : (x : Bits N) → Blank L x →
                   ∀ w → run (adder L) x w ≡ addition x w
  adder-computes x bl w = go (out? w)
    where
    go : (d : Dec (∃ λ k → wire L (zw k) ≡ w)) →
         run (adder L) x w ≡ x w xor gain x w d
    go (yes (k , e)) =
      subst (λ v → run (adder L) x v ≡
                   x v xor add (xbits L x) (ybits L x) false k)
            e (adder-out x bl k)
    go (no ¬o) = trans (adder-work x w (λ k e → ¬o (k , e)))
                       (sym (xor-identityʳ (x w)))


------------------------------------------------------------------------
-- Resources

-- A count of the adder's gates is twice the ripple's plus the copy's.

adder-count : (f : Gate N → ℕ) (L : Layout (Wire false m) N) →
              count f (adder L) ≡
              count f (ripple L) + (count f (copy L) + count f (ripple L))
adder-count f L =
  trans (count-++ f (ripple L) (copy L ++ reverse (ripple L)))
        (cong (count f (ripple L) +_)
              (trans (count-++ f (copy L) (reverse (ripple L)))
                     (cong (count f (copy L) +_)
                           (count-reverse f (ripple L)))))

-- With a carry in, the ripple over m + 1 positions has 2m Toffoli gates
-- and 3 + 5m CNOTs, the copy 2 and 3 + m; without one, one Toffoli
-- gate and two CNOTs fewer in the ripple, and one CNOT more in the
-- copy (the carry out of position 0 into c₁).

private
  ripple-tof : (L : Layout (Wire true m) N) → toffolis (ripple L) ≡ 2 * m
  ripple-tof {zero}  L = refl
  ripple-tof {suc m} L =
    trans (count-++ is-ccx (carry₀ L) (sum-block true L ++ ripple (inner L)))
    (trans (cong (2 +_) (count-++ is-ccx (sum-block true L)
                                  (ripple (inner L))))
    (trans (cong (2 +_) (ripple-tof (inner L)))
           (solve 1 (λ m → con 2 :+ con 2 :* m := con 2 :* (con 1 :+ m))
                  refl m)))

  ripple-cx : (L : Layout (Wire true m) N) → cnots (ripple L) ≡ 3 + 5 * m
  ripple-cx {zero}  L = refl
  ripple-cx {suc m} L =
    trans (count-++ is-cx (carry₀ L) (sum-block true L ++ ripple (inner L)))
    (trans (cong (2 +_) (count-++ is-cx (sum-block true L) (ripple (inner L))))
    (trans (cong (λ t → 2 + (3 + t)) (ripple-cx (inner L)))
           (solve 1 (λ m → con 2 :+ (con 3 :+ (con 3 :+ con 5 :* m))
                           := con 3 :+ con 5 :* (con 1 :+ m))
                  refl m)))

  copy-tof : (L : Layout (Wire true m) N) → toffolis (copy L) ≡ 2
  copy-tof {zero}  L = refl
  copy-tof {suc m} L = copy-tof (inner L)

  copy-cx : (L : Layout (Wire true m) N) → cnots (copy L) ≡ 3 + m
  copy-cx {zero}  L = refl
  copy-cx {suc m} L = cong suc (copy-cx (inner L))

  ripple-tof₀ : (L : Layout (Wire false (suc m)) N) →
                toffolis (ripple L) ≡ suc (2 * m)
  ripple-tof₀ L =
    trans (count-++ is-ccx (carry₀ L) (sum-block false L ++ ripple (inner L)))
          (cong suc (trans (count-++ is-ccx (sum-block false L)
                                     (ripple (inner L)))
                           (ripple-tof (inner L))))

  ripple-cx₀ : (L : Layout (Wire false (suc m)) N) →
               cnots (ripple L) ≡ 5 + 5 * m
  ripple-cx₀ L =
    trans (count-++ is-cx (carry₀ L) (sum-block false L ++ ripple (inner L)))
    (trans (count-++ is-cx (sum-block false L) (ripple (inner L)))
           (cong (2 +_) (ripple-cx (inner L))))

-- For n = m + 2 ≥ 2 bits: 4(n − 1) Toffoli gates and 11n − 8 CNOTs.

adder-toffolis : (L : Layout (Wire false (suc m)) N) →
                 toffolis (adder L) ≡ 4 * suc m
adder-toffolis {m} L =
  trans (adder-count is-ccx L)
  (trans (cong₂ (λ r c → r + (c + r)) (ripple-tof₀ L) (copy-tof (inner L)))
         (solve 1 (λ m → (con 1 :+ con 2 :* m)
                         :+ (con 2 :+ (con 1 :+ con 2 :* m))
                         := con 4 :* (con 1 :+ m))
                refl m))

adder-cnots : (L : Layout (Wire false (suc m)) N) →
              cnots (adder L) ≡ 11 * suc (suc m) ∸ 8
adder-cnots {m} L =
  trans (adder-count is-cx L)
  (trans (cong₂ (λ r c → r + (c + r)) (ripple-cx₀ L)
                (cong suc (copy-cx (inner L))))
  (trans (solve 1 (λ m → (con 5 :+ con 5 :* m) :+ ((con 4 :+ m)
                         :+ (con 5 :+ con 5 :* m))
                         := con 14 :+ con 11 :* m)
                refl m)
         (sym (cong (_∸ 8) (solve 1 (λ m → con 11 :* (con 2 :+ m)
                                           := con 22 :+ con 11 :* m)
                                  refl m)))))

-- For n = 1: the carry out x₀ y₀ is one Toffoli gate, and there are
-- five CNOTs.

adder-toffolis-1 : (L : Layout (Wire false zero) N) → toffolis (adder L) ≡ 1
adder-toffolis-1 L = refl

adder-cnots-1 : (L : Layout (Wire false zero) N) → cnots (adder L) ≡ 5
adder-cnots-1 L = refl

-- Table 2's Adder8 and Adder16, on the standard layout: 40 and 80
-- qubits, 28 and 60 Toffoli gates -- which, expanded at seven T gates
-- and two Hadamards (two path variables) each, are the table's 196 and
-- 420 T gates and 56 and 120 path variables -- and 80 and 168 CNOTs.

table-2-Adder8 :
  (width 7 ≡ 40) × (toffolis (adder (standard 7)) ≡ 28) ×
  (7 * toffolis (adder (standard 7)) ≡ 196) ×
  (2 * toffolis (adder (standard 7)) ≡ 56) ×
  (cnots (adder (standard 7)) ≡ 80)
table-2-Adder8 =
  refl , adder-toffolis (standard 7) ,
  cong (7 *_) (adder-toffolis (standard 7)) ,
  cong (2 *_) (adder-toffolis (standard 7)) , adder-cnots (standard 7)

table-2-Adder16 :
  (width 15 ≡ 80) × (toffolis (adder (standard 15)) ≡ 60) ×
  (7 * toffolis (adder (standard 15)) ≡ 420) ×
  (2 * toffolis (adder (standard 15)) ≡ 120) ×
  (cnots (adder (standard 15)) ≡ 168)
table-2-Adder16 =
  refl , adder-toffolis (standard 15) ,
  cong (7 *_) (adder-toffolis (standard 15)) ,
  cong (2 *_) (adder-toffolis (standard 15)) , adder-cnots (standard 15)


------------------------------------------------------------------------
-- Cross-checks

-- A gate as its controls and target, as numbers.

gate-wires : Gate N → List ℕ
gate-wires (ccx c₁ c₂ t _ _ _) = toℕ c₁ ∷ toℕ c₂ ∷ toℕ t ∷ []
gate-wires (cx c t _)          = toℕ c ∷ toℕ t ∷ []

-- The netlist for n = 2 on the standard layout's ten wires: x₀ x₁ =
-- 0 1, y₀ y₁ = 2 3, z₀ z₁ z₂ = 4 5 6, c₁ = 7, s₀ s₁ = 8 9.  The ripple
-- (c₁ ⊕= x₀y₀; s₀ ⊕= x₀, y₀; s₁ ⊕= x₁, y₁, c₁), the copy (z₀ ⊕= s₀;
-- z₂ ⊕= maj(x₁, y₁, c₁) by the carry block; z₁ ⊕= s₁), the ripple
-- reversed: 4 Toffoli gates and 14 CNOTs.

netlist-2 :
  map gate-wires (adder (standard 1)) ≡
  (0 ∷ 2 ∷ 7 ∷ []) ∷ (0 ∷ 8 ∷ []) ∷ (2 ∷ 8 ∷ []) ∷
  (1 ∷ 9 ∷ []) ∷ (3 ∷ 9 ∷ []) ∷ (7 ∷ 9 ∷ []) ∷
  (8 ∷ 4 ∷ []) ∷
  (1 ∷ 3 ∷ 6 ∷ []) ∷ (1 ∷ 3 ∷ []) ∷ (7 ∷ 3 ∷ 6 ∷ []) ∷ (1 ∷ 3 ∷ []) ∷
  (9 ∷ 5 ∷ []) ∷
  (7 ∷ 9 ∷ []) ∷ (3 ∷ 9 ∷ []) ∷ (1 ∷ 9 ∷ []) ∷
  (2 ∷ 8 ∷ []) ∷ (0 ∷ 8 ∷ []) ∷ (0 ∷ 2 ∷ 7 ∷ []) ∷ []
netlist-2 = refl

-- Run: for n = 2, 3 + 1 = 4 (x₀ = x₁ = y₀ = 1, the output z₂ = 1), and
-- for n = 3, 7 + 1 = 8 (the carry rippling through c₁ and c₂ into
-- z₃); every other wire ends as it began.

sum-3+1 :
  map (run (adder (standard 1)) (λ w → toℕ w <ᵇ 3)) (allFin 10) ≡
  true ∷ true ∷ true ∷ false ∷ false ∷ false ∷ true ∷ false ∷ false ∷
  false ∷ []
sum-3+1 = refl

sum-7+1 :
  map (run (adder (standard 2)) (λ w → toℕ w <ᵇ 4)) (allFin 15) ≡
  true ∷ true ∷ true ∷ true ∷ false ∷ false ∷
  false ∷ false ∷ false ∷ true ∷ false ∷ false ∷ false ∷ false ∷ false ∷ []
sum-7+1 = refl
