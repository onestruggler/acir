------------------------------------------------------------------------
-- Presentations of groups
--
-- The rewrite rules find |s⟩ and |s⟩|s⟩ on the tool's own circuits, in
-- exactly 3n steps
--
-- Section 5.2 of Amy's QPL 2018 paper reports that its tool, reducing
-- the path-sums of the hidden shift benchmarks by the rules of figure
-- 2, "finds the correct output |s⟩ or |s⟩|s⟩ even without providing
-- the specification".  PathSum.HiddenShift.Tool and ToolSymbolic build
-- those benchmarks as the tool generates them, for every n = 2m, every
-- number of alternations, every shift and every random draw: the
-- hidden shift circuit HSᵗ s Bs over {H, X, CNOT, R_k, R_k†} with X a
-- primitive gate (PathSum.CRK.WithX), and the symbolic shift circuit
-- SSᵗ Bs (which has no X).  Both have exactly 3n path variables, as
-- table 2 says.  Tool's tool-reduces shows that every complete
-- reduction of the first on |0⟩ ends at |s⟩; this module shows that
-- one exists, for both circuits' own path-sums (definition 2.9):
--
--  * tool-exists, tool-finds: the hidden shift circuit on |0⟩,
--    at0 ⟦ HSᵗ s Bs ⟧ (as PathSum.HiddenShift.ExistsCircuit states it
--    for figure 3(a)), reduces to a path-sum with no path variables,
--    and that one is |x⟩ ↦ |s⟩ coefficient by coefficient;
--  * tool-symbolic-exists, tool-symbolic-finds: the symbolic shift
--    circuit with its data register read as 0, set0ᶜ (dataMask n)
--    ⟦ SSᵗ Bs ⟧ (as ExistsSymbolic states it for figure 3(b)), reduces
--    to one with no path variables, |x_d, x_s⟩ ↦ |x_s, x_s⟩
--    coefficient by coefficient; every complete reduction ends there
--    (tool-symbolic-reduces, from ToolSymbolic's
--    symbolic-shift-tool-set0 and PathSum.HiddenShift.Reduces's
--    fun-only-if).
--
-- The chains are those of PathSum.HiddenShift.Exists -- three passes of
-- [HH] followed by [Elim] at renumbered path variables, with quotients
-- a_i ⊕ s_L,i, s_L,i and s_R,i (input variables for the symbolic
-- shift) -- run by PathSum.HiddenShift.ThreeLayers on the values
-- PathSum.HiddenShift.ToolRuns reads off each path.  With X primitive
-- the X gates add no path variable, so there is no stage removing them
-- (figure 3(a)'s circuit in PathSum.HiddenShift.ExistsCircuit, where X
-- is H R₁ H, has 4|s| more variables, and its chain 4|s| more steps by
-- construction -- ExistsCircuit does not state its step count), and
-- here the step count is a theorem: each chain has exactly 3n = 6m
-- steps (PathSum.Full's lenᶠ), one per path variable -- by
-- construction 3m applications of [HH], each followed by the [Elim]
-- of the variable it substituted, as the paper's own derivations pair
-- them ([HH, Elim] in its examples).  The split into 3m and 3m is not
-- stated.
--
-- What is not claimed: that the tool's own search finds these chains.
-- They are constructed, not found by PathSum.Full.Match's
-- normal-formᶠ, and the tool's rewriting strategy is not formalised.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.ToolExists (M₀ : ℕ) where

open import Data.Bool.Base using (true; false; if_then_else_)
open import Data.Fin.Base using (Fin; _↑ˡ_; _↑ʳ_)
open import Data.Integer.Base using (+_; 0ℤ; _-_; _*_)
open import Data.Integer.Divisibility.Signed using (_∣_)
open import Data.Integer.Properties using (+-identityˡ)
open import Data.List.Base using (List)
open import Data.Nat.Base using (suc) renaming (_+_ to _ℕ+_; _*_ to _ℕ*_)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)

import Data.Nat.Properties as ℕ

open import PathSum.Ancilla.Register M₀ using (mask; set0ᶜ; eval-set0ᶜ)
open import PathSum.Assign using ([_]ᶻ)
open import PathSum.Base using (PathSum; phase; out)
open import PathSum.CRK.Trace M₀ using (str)
open import PathSum.Denotation M₀ using (Assign; ≋-sym; ≋-trans)
open import PathSum.HiddenShift.Engine M₀ using (qlit; qin)
open import PathSum.HiddenShift.Gates M₀ using (sumᵇ)
open import PathSum.HiddenShift.Layout using (hs-par)
open import PathSum.HiddenShift.Reduces M₀ using (fun-only-if; copy-values)
open import PathSum.HiddenShift.Simulation M₀ using (at0; eval-at0)
open import PathSum.HiddenShift.Symbolic M₀ using
  (specSᴾ; dataMask; copy; ⧺-cong₂)
open import PathSum.HiddenShift.ThreeLayers M₀ using
  (lay₁; lay₂; lay₃; module Layered)
open import PathSum.HiddenShift.Tool M₀ using
  (Block; gTerms; HSᵗ; tool-reduces)
open import PathSum.HiddenShift.ToolRuns M₀ using (runs-HSᵗ; runs-SSᶜᵗ)
open import PathSum.HiddenShift.ToolSymbolic M₀ using
  (SSᶜᵗ; SSᵗ; symbolic-shift-tool-set0)
open import PathSum.HiddenShift.Table M₀ using (HS-paths; SS-paths)
open import PathSum.HiddenShift.TraceX M₀ using
  (traceˣ; eval-⟦⟧ˣ; outBit-⟦⟧ˣ; Runsˣ; runsˣ-φ; runsˣ-v; Runsˣ-cong;
   Runsˣ-embed)
open import PathSum.HiddenShift.Walsh using
  (0ᵃ; _⧺_; ⧺-↑ˡ; ⧺-↑ʳ; ⧺-split; lhalf; rhalf)
open import PathSum.Polynomial using (κ; μ; x[_]; eval; _≈[_]_; 0ᴾ)
open import PathSum.Polynomial.Bind using (odd)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.CRK.WithX M₀ using (norm; paths; paths≡norm; ⟦_⟧)
open import PathSum.Full M using (_⟶ᶠ*_; lenᶠ)
open import PathSum.Full.Sound M₀ using (⟶ᶠ*-sound)
open import PathSum.Order M using (pow)
open import PathSum.Reduction M using (½)

private
  -- 3n path variables, as three layers of n.

  three : ∀ n → 3 ℕ* n ≡ n ℕ+ (n ℕ+ n)
  three n = cong (λ t → n ℕ+ (n ℕ+ t)) (ℕ.+-identityʳ n)


------------------------------------------------------------------------
-- The hidden shift circuit

module _ {m d : ℕ} (s : Assign (m ℕ+ m)) (Bs : List (Block d m)) where

  private
    n : ℕ
    n = m ℕ+ m

    -- The shift is the constant s; the quotients are its bits; the
    -- outputs are the third layer.

    module L = Layered {m} {n} (gTerms Bs) (λ _ → s)
      (λ i → qlit (lhalf {m} s i)) (λ i → qlit (rhalf {m} s i))
      (λ _ _ _ _ → tt) (λ _ _ _ _ → tt) (λ _ _ _ → refl) (λ _ _ _ → refl)
      (λ w x u → u w) (λ w x h → h w)

    ξ : PathSum n (norm (HSᵗ s Bs)) (paths (HSᵗ s Bs))
    ξ = at0 ⟦ HSᵗ s Bs ⟧

    -- Along a path: phase ½ hs-par, outputs the third layer.

    ph : ∀ x y →
         pow M ∣ (eval (phase ξ) x y -
                  ½ * [ hs-par (sumᵇ (gTerms Bs)) s (lay₁ n (str y))
                               (lay₂ n (str y)) (lay₃ n (str y)) ]ᶻ)
    ph x y = subst (pow M ∣_)
      (cong₂ _-_ (sym evalEq) (+-identityˡ _))
      (runsˣ-φ (runs-HSᵗ s Bs (str y)) 0ℤ)
      where
      evalEq : eval (phase ξ) x y ≡
               proj₁ (traceˣ (HSᵗ s Bs) (str y) (0ℤ , 0ᵃ {n}))
      evalEq = trans (eval-at0 (phase ⟦ HSᵗ s Bs ⟧) x y)
                     (eval-⟦⟧ˣ (HSᵗ s Bs) (0ᵃ {n}) y)

    ob : ∀ w x y → odd (eval (out ξ w) x y) ≡ lay₃ n (str y) w
    ob w x y = trans (cong odd (eval-at0 (out ⟦ HSᵗ s Bs ⟧ w) x y))
      (trans (outBit-⟦⟧ˣ (HSᵗ s Bs) (0ᵃ {n}) y w)
             (runsˣ-v (runs-HSᵗ s Bs (str y)) 0ℤ w))

    reduction : Σ (PathSum n 0 0) (λ ζ →
                  Σ (ξ ⟶ᶠ* ζ) (λ steps → lenᶠ steps ≡ paths (HSᵗ s Bs)))
    reduction = L.three-layers ξ (sym (paths≡norm (HSᵗ s Bs)))
      (trans (HS-paths s Bs) (three n)) ph ob

  -- The tool's hidden shift circuit on |0⟩ reduces by figure 2's rules
  -- to a path-sum with no path variables, in exactly 3n steps ...

  tool-exists :
    Σ (PathSum (m ℕ+ m) 0 0) (λ ζ →
      Σ (at0 ⟦ HSᵗ s Bs ⟧ ⟶ᶠ* ζ) (λ steps → lenᶠ steps ≡ 3 ℕ* (m ℕ+ m)))
  tool-exists = proj₁ reduction , proj₁ (proj₂ reduction) ,
    trans (proj₂ (proj₂ reduction)) (HS-paths s Bs)

  -- ... and that one is |x⟩ ↦ |s⟩, coefficient by coefficient: the
  -- calculus finds the hidden shift on the tool's circuit itself.

  tool-finds :
    Σ (PathSum (m ℕ+ m) 0 0) (λ ζ →
      (at0 ⟦ HSᵗ s Bs ⟧ ⟶ᶠ* ζ) ×
      (∀ w → out ζ w ≈[ + 2 ] κ [ s w ]ᶻ) ×
      (phase ζ ≈[ pow M ] 0ᴾ))
  tool-finds =
    proj₁ tool-exists , proj₁ (proj₂ tool-exists) ,
    proj₂ (tool-reduces s Bs (proj₁ (proj₂ tool-exists)))


------------------------------------------------------------------------
-- The symbolic shift circuit

module _ {m d : ℕ} (Bs : List (Block d m)) where

  private
    n : ℕ
    n = m ℕ+ m

    -- The shift register.

    xsOf : Assign (n ℕ+ n) → Assign n
    xsOf x j = x (n ↑ʳ j)

    -- The shift is the second register; the quotients are its input
    -- variables; the outputs are the third layer and the shift
    -- register.

    module L = Layered {m} {n ℕ+ n} (gTerms Bs) xsOf
      (λ i → qin (n ↑ʳ (i ↑ˡ m))) (λ i → qin (n ↑ʳ (m ↑ʳ i)))
      (λ _ _ _ _ → tt) (λ _ _ _ _ → tt) (λ _ _ _ → refl) (λ _ _ _ → refl)
      (λ w x u → (u ⧺ xsOf x) w)
      (λ w x h → ⧺-cong₂ {k = n} {l = n} h (λ _ → refl) w)

    ξ : PathSum (n ℕ+ n) (norm (SSᵗ Bs)) (paths (SSᵗ Bs))
    ξ = set0ᶜ (dataMask n) ⟦ SSᵗ Bs ⟧

    -- The data register starts at 0, the shift register at the input.

    prepared : ∀ x w → mask (dataMask n) x w ≡ (0ᵃ {n} ⧺ xsOf x) w
    prepared x w = trans (sym (⧺-split n n (mask (dataMask n) x) w))
      (⧺-cong₂ {k = n} {l = n} left right w)
      where
      left : ∀ i → mask (dataMask n) x (i ↑ˡ n) ≡ 0ᵃ {n} i
      left i = cong (λ b → if b then false else x (i ↑ˡ n))
                    (⧺-↑ˡ (λ (_ : Fin n) → true) (λ (_ : Fin n) → false) i)

      right : ∀ j → mask (dataMask n) x (n ↑ʳ j) ≡ xsOf x j
      right j = cong (λ b → if b then false else x (n ↑ʳ j))
                     (⧺-↑ʳ (λ (_ : Fin n) → true) (λ (_ : Fin n) → false) j)

    -- Along a path: phase ½ hs-par with the shift register as the
    -- shift, outputs the third layer and the shift register.

    R : ∀ (x : Assign (n ℕ+ n)) (y : Assign (paths (SSᵗ Bs))) →
        Runsˣ (SSᵗ Bs) (str y) (mask (dataMask n) x)
              (hs-par (sumᵇ (gTerms Bs)) (xsOf x) (lay₁ n (str y))
                      (lay₂ n (str y)) (lay₃ n (str y)))
              (lay₃ n (str y) ⧺ xsOf x)
    R x y = Runsˣ-cong (prepared x)
              (Runsˣ-embed (SSᶜᵗ Bs) (runs-SSᶜᵗ Bs (str y) (xsOf x)))

    ph : ∀ x y →
         pow M ∣ (eval (phase ξ) x y -
                  ½ * [ hs-par (sumᵇ (gTerms Bs)) (xsOf x) (lay₁ n (str y))
                               (lay₂ n (str y)) (lay₃ n (str y)) ]ᶻ)
    ph x y = subst (pow M ∣_)
      (cong₂ _-_ (sym evalEq) (+-identityˡ _))
      (runsˣ-φ (R x y) 0ℤ)
      where
      evalEq : eval (phase ξ) x y ≡
               proj₁ (traceˣ (SSᵗ Bs) (str y) (0ℤ , mask (dataMask n) x))
      evalEq = trans (eval-set0ᶜ (dataMask n) (phase ⟦ SSᵗ Bs ⟧) x y)
                     (eval-⟦⟧ˣ (SSᵗ Bs) (mask (dataMask n) x) y)

    ob : ∀ w x y →
         odd (eval (out ξ w) x y) ≡ (lay₃ n (str y) ⧺ xsOf x) w
    ob w x y = trans (cong odd (eval-set0ᶜ (dataMask n) (out ⟦ SSᵗ Bs ⟧ w) x y))
      (trans (outBit-⟦⟧ˣ (SSᵗ Bs) (mask (dataMask n) x) y w)
             (runsˣ-v (R x y) 0ℤ w))

    reduction : Σ (PathSum (n ℕ+ n) 0 0) (λ ζ →
                  Σ (ξ ⟶ᶠ* ζ) (λ steps → lenᶠ steps ≡ paths (SSᵗ Bs)))
    reduction = L.three-layers ξ (sym (paths≡norm (SSᵗ Bs)))
      (trans (SS-paths Bs) (three n)) ph ob

  -- The tool's symbolic shift circuit, with its data register read as
  -- 0, reduces by figure 2's rules to a path-sum with no path
  -- variables, in exactly 3n steps ...

  tool-symbolic-exists :
    Σ (PathSum ((m ℕ+ m) ℕ+ (m ℕ+ m)) 0 0) (λ ζ →
      Σ (set0ᶜ (dataMask (m ℕ+ m)) ⟦ SSᵗ Bs ⟧ ⟶ᶠ* ζ) (λ steps →
        lenᶠ steps ≡ 3 ℕ* (m ℕ+ m)))
  tool-symbolic-exists = proj₁ reduction , proj₁ (proj₂ reduction) ,
    trans (proj₂ (proj₂ reduction)) (SS-paths Bs)

  -- ... every complete reduction of it ends at |x_d, x_s⟩ ↦ |x_s, x_s⟩
  -- syntactically ...

  tool-symbolic-reduces :
    {k′ : ℕ} {ζ : PathSum ((m ℕ+ m) ℕ+ (m ℕ+ m)) k′ 0} →
    set0ᶜ (dataMask (m ℕ+ m)) ⟦ SSᵗ Bs ⟧ ⟶ᶠ* ζ →
    (k′ ≡ 0) ×
    (∀ w → out ζ w ≈[ + 2 ] μ x[ copy (m ℕ+ m) w ]) ×
    (phase ζ ≈[ pow M ] 0ᴾ)
  tool-symbolic-reduces {k′} {ζ} steps =
    fun-only-if (λ w → μ x[ copy n w ]) (λ x w → x (copy n w))
                (copy-values n) ζ
      (≋-trans {ξ = ζ} {ζ = ξ} {χ = specSᴾ n}
        (≋-sym {ξ = ξ} {ζ = ζ} (⟶ᶠ*-sound steps))
        (symbolic-shift-tool-set0 Bs))

  -- ... so the one that exists is it: the calculus finds |s⟩|s⟩, the
  -- shift symbolic, on the tool's circuit itself.

  tool-symbolic-finds :
    Σ (PathSum ((m ℕ+ m) ℕ+ (m ℕ+ m)) 0 0) (λ ζ →
      (set0ᶜ (dataMask (m ℕ+ m)) ⟦ SSᵗ Bs ⟧ ⟶ᶠ* ζ) ×
      (∀ w → out ζ w ≈[ + 2 ] μ x[ copy (m ℕ+ m) w ]) ×
      (phase ζ ≈[ pow M ] 0ᴾ))
  tool-symbolic-finds =
    proj₁ tool-symbolic-exists , proj₁ (proj₂ tool-symbolic-exists) ,
    proj₂ (tool-symbolic-reduces (proj₁ (proj₂ tool-symbolic-exists)))
