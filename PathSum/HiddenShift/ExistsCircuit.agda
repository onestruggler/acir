------------------------------------------------------------------------
-- Presentations of groups
--
-- The rewrite rules find |s⟩: a complete reduction of the circuit of
-- figure 3(a), for every size
--
-- Section 5.2 of Amy's "Towards Large-scale Functional Verification of
-- Universal Quantum Circuits" (QPL 2018) reports that the calculus
-- "finds the correct output |s⟩ ... even without providing the
-- specification".  PathSum.HiddenShift.Circuit proves that every
-- reduction by figure 2's rules which removes all path variables of the
-- circuit of figure 3(a) on |0⟩, at0 ⟦ HSᶜ gs s ⟧, ends at |x⟩ ↦ |s⟩
-- (circuit-reduces), and PathSum.HiddenShift.Exists that one exists
-- for PathSum.HiddenShift's composite.  This module proves that one
-- exists for the circuit's own path-sum (definition 2.9), for every m,
-- every list of monomials gs and every shift s (circuit-exists), so
-- that the calculus finds |s⟩ on it (circuit-finds).
--
-- The circuit has more path variables than the composite.  X is
-- H R₁ H here (X is not in the gate set of definition 2.9), so each of
-- the two layers X^s adds two variables for each wire w with s_w = 1:
-- the path-sum has 3n + 4|s| variables.  Along a path the X on wire w,
-- holding a, reads bits c₁ and c₂ and adds ½ (a c₁ + c₁ + c₁ c₂) to
-- the phase, leaving c₂ on the wire (PathSum.HiddenShift.Runs,
-- PathSum.HiddenShift.XLayer).  The reduction first removes them, wire
-- by wire (passU, passV):
--
--   [HH] at u₁_w with u₂_w ← a_w ⊕ 1, then [Elim] of u₂_w
--        (the first layer's X: a_w is the first Hadamard layer's bit),
--   [HH] at v₁_w with v₂_w ← a_w,     then [Elim] of v₂_w
--        (the second layer's X, whose wire then holds a_w ⊕ 1),
--
-- after which the X gates are X: the oracle reads a ⊕ s and the second
-- Hadamard layer a again, the phase is ½ Fblk of the six blocks
-- (F-main), and the three passes of PathSum.HiddenShift.Exists finish
-- the reduction (PathSum.HiddenShift.MainPasses, with the extra labels
-- those of the X gates).  So the chain has 6m + 4|s| steps by
-- construction, taking the 3n + 4|s| variables to none; the step count
-- is not stated.
--
-- The labels.  A path variable is either one of the six blocks
-- (Lbl m) or the first or second Hadamard of the X on wire w in the
-- first or second X layer (XH × Fin n: u₁, u₂, v₁, v₂).  The X labels
-- of wires with s_w = 0 name no variable; they are removed from the
-- start, with themselves as fixed value, and no value reads them.
-- ⟦ C ⟧ numbers a Hadamard's variable by the Hadamards after it, so
-- the variables come as the third layer's, the second's, the second X
-- layer's, the first X layer's and the first layer's (labR, gpos).
--
-- The values (tracks₀) are read along each path from the circuit's
-- layers, as in PathSum.HiddenShift.ExistsSymbolic; here the input is
-- 0 (at0), so they do not depend on it.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.ExistsCircuit (M₀ : ℕ) where

open import Data.Bool.Base using
  (Bool; true; false; not; _∧_; _xor_; if_then_else_)
open import Data.Bool.Properties using
  (xor-identityʳ; xor-comm; xor-same; ∧-zeroʳ; ∧-identityʳ)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using
  (Fin; zero; suc; toℕ; opposite; splitAt; cast; _↑ˡ_; _↑ʳ_)
open import Data.Integer.Base using (+_; 0ℤ; _-_; _*_)
open import Data.Integer.Divisibility.Signed using (_∣_)
open import Data.Integer.Properties using (+-identityˡ)
open import Data.List.Base using (List; _++_)
open import Data.Nat.Base using (zero; suc) renaming (_+_ to _ℕ+_)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Product.Properties using (≡-dec)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Sum.Properties using (inj₂-injective)
open import Data.Unit.Base using (tt)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (Dec; yes; no)

import Data.Fin.Properties as Fin
import Data.Nat.Solver as ℕSolver

open import PathSum.Assign using ([_]ᶻ; _[_≔_]; ≔-here; ≔-there)
open import PathSum.Base using (PathSum; phase; out)
open import PathSum.CRK.Trace M₀ using
  (Stream; shift; trace; str; pathOf-str; eval-⟦⟧; outBit-⟦⟧; norm-++)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.HiddenShift.Blocks
open import PathSum.HiddenShift.Circuit M₀ using
  (fTerms; f̃Terms; oracleᶠ; oracleᵈ; sum-f; sum-f̃; HSᶜ; norm-HSᶜ;
   circuit-reduces)
open import PathSum.HiddenShift.Engine M₀ using
  (qlit; qvar; _q⊕_; ⟦_⟧q)
open import PathSum.HiddenShift.Exists M₀ using (module Sweep)
open import PathSum.HiddenShift.Gates M₀ using
  (Term; sumᵇ; sumᵇ-resp; norm-oracle)
open import PathSum.HiddenShift.Layers M₀ using
  (hadamards; norm-hadamards; flips)
open import PathSum.HiddenShift.Layout using
  (sel-ˡ; sel-ʳ; split-inv; wl; wl-↑ˡ; wl-↑ʳ; wl-inv; hs-par; blocks-par)
open import PathSum.HiddenShift.Runs M₀ using
  (Runs; runs-φ; runs-v; Runs-++; Runs-hadamards; Runs-oracle; Runs-flips;
   hbits; nF; xrev; xbits; xβ; xout)
open import PathSum.HiddenShift.Simulation M₀ using (at0; eval-at0)
open import PathSum.HiddenShift.TrackX M₀ using (Tracksˣ)
open import PathSum.HiddenShift.Walsh using
  (0ᵃ; _⊕ᵃ_; dot; dot-cong; dot-0ˡ; lhalf; rhalf; mm; xor-medial)
open import PathSum.HiddenShift.XLayer M₀ using
  (xposF; xdecF; xdec-ok; xdec-rev; xdec-xpos; xβ-cong; xβ-zero; xβ-∂;
   xout-cong)
open import PathSum.Polynomial using (κ; eval; _≈[_]_; 0ᴾ)
open import PathSum.Polynomial.Bind using (odd)

import PathSum.HiddenShift.MainPasses M₀ as MP

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.CRK.Circuit M using
  (Circuit; norm; paths; paths≡norm; ⟦_⟧)
open import PathSum.Full M using (_⟶ᶠ*_; εᶠ)
open import PathSum.Order M using (pow)
open import PathSum.Reduction M using (½)

open ℕSolver.+-*-Solver using (solve; con; _:+_; _:=_)


------------------------------------------------------------------------
-- Small facts

private
  t≢f : true ≢ false
  t≢f ()

  if-true : ∀ {A : Set} {b : Bool} → b ≡ true → (x y : A) →
            (if b then x else y) ≡ x
  if-true refl x y = refl

  if-false : ∀ {A : Set} {b : Bool} → b ≡ false → (x y : A) →
             (if b then x else y) ≡ y
  if-false refl x y = refl

  -- a ⊕ 1 ⊕ 1 is a.

  xor-true-true : ∀ a → (a xor true) xor true ≡ a
  xor-true-true false = refl
  xor-true-true true  = refl

  -- A present bit and itself: s ∧ ¬0 is s, s ∧ ¬1 is 0.

  ∧-true : ∀ {b} → b ∧ not false ≡ true → b ≡ true
  ∧-true {true}  _  = refl
  ∧-true {false} ()


------------------------------------------------------------------------
-- The X gates' variables

-- The first and second Hadamard of an X in the first layer (u) or the
-- second (v).

data XH : Set where
  u₁ u₂ v₁ v₂ : XH

_≟ˣ_ : DecidableEquality XH
u₁ ≟ˣ u₁ = yes refl
u₁ ≟ˣ u₂ = no λ ()
u₁ ≟ˣ v₁ = no λ ()
u₁ ≟ˣ v₂ = no λ ()
u₂ ≟ˣ u₁ = no λ ()
u₂ ≟ˣ u₂ = yes refl
u₂ ≟ˣ v₁ = no λ ()
u₂ ≟ˣ v₂ = no λ ()
v₁ ≟ˣ u₁ = no λ ()
v₁ ≟ˣ u₂ = no λ ()
v₁ ≟ˣ v₁ = yes refl
v₁ ≟ˣ v₂ = no λ ()
v₂ ≟ˣ u₁ = no λ ()
v₂ ≟ˣ u₂ = no λ ()
v₂ ≟ˣ v₁ = no λ ()
v₂ ≟ˣ v₂ = yes refl


------------------------------------------------------------------------
-- The reduction, for one list of monomials and one shift

module _ {m : ℕ} (gs : List (Term m)) (s : Assign (m ℕ+ m)) where

  private
    n : ℕ
    n = m ℕ+ m

  XL : Set
  XL = XH × Fin (m ℕ+ m)

  CL : Set
  CL = Lbl m ⊎ XL

  private
    _≟ᴱ_ : DecidableEquality XL
    _≟ᴱ_ = ≡-dec _≟ˣ_ Fin._≟_

  ----------------------------------------------------------------------
  -- The values

  -- The labelled path's Hadamard layers, and its X gates' bits.

  Y1 Y2 Y3 : (CL → Bool) → Assign (m ℕ+ m)
  Y1 Z w = Z (inj₁ (wl A₁ B₁ w))
  Y2 Z w = Z (inj₁ (wl C₂ D₂ w))
  Y3 Z w = Z (inj₁ (wl E₃ H₃ w))

  Xb : XH → (CL → Bool) → Assign (m ℕ+ m)
  Xb t Z w = Z (inj₂ (t , w))

  -- The parity of the circuit, as its layers add it: H^{⊗n} from 0,
  -- X^s, O_f, X^s, H^{⊗n}, O_f̃, H^{⊗n}.

  FcS : (y1 u1 u2 v1 v2 y2 y3 : Assign (m ℕ+ m)) → Bool
  FcS y1 u1 u2 v1 v2 y2 y3 =
    (((dot (0ᵃ {n}) y1 xor
       (xβ s y1 u1 u2 xor
        (sumᵇ (fTerms gs) (xout s y1 u2) xor
         xβ s (xout s y1 u2) v1 v2))) xor
      dot (xout s (xout s y1 u2) v2) y2) xor
     sumᵇ (f̃Terms gs) y2) xor
    dot y2 y3

  Fc : Assign (m ℕ+ m) → (CL → Bool) → Bool
  Fc x Z = FcS (Y1 Z) (Xb u₁ Z) (Xb u₂ Z) (Xb v₁ Z) (Xb v₂ Z) (Y2 Z) (Y3 Z)

  -- The outputs: the third layer.

  Gc : Fin (m ℕ+ m) → Assign (m ℕ+ m) → (CL → Bool) → Bool
  Gc w x Z = Gblk w (λ ℓ → Z (inj₁ ℓ))

  -- The fixed values: Blocks' for the blocks; an X that is there ends
  -- with its first bit 0 and its second the wire's new value (a ⊕ 1
  -- after the first layer's X, a after the second's); an X label of a
  -- wire with s_w = 0 keeps whatever value it has.

  xval : XH → (CL → Bool) → Fin (m ℕ+ m) → Bool
  xval u₁ Z w = false
  xval u₂ Z w = Y1 Z w xor true
  xval v₁ Z w = false
  xval v₂ Z w = Y1 Z w

  dfltc : Assign (m ℕ+ m) → CL → (CL → Bool) → Bool
  dfltc x (inj₁ ℓ) Z = Phase.dflt (sumᵇ gs) (sumᵇ-resp gs) (lhalf {m} s)
                                  (rhalf {m} s) ℓ (λ ℓ′ → Z (inj₁ ℓ′))
  dfltc x (inj₂ (t , w)) Z = if s w then xval t Z w else Z (inj₂ (t , w))

  ----------------------------------------------------------------------
  -- With the X gates removed, the phase is Fblk

  private
    FcS-cong : {y1 y1′ u1 u1′ u2 u2′ v1 v1′ v2 v2′ y2 y2′ y3 y3′ :
                Assign (m ℕ+ m)} →
               (∀ w → y1 w ≡ y1′ w) → (∀ w → u1 w ≡ u1′ w) →
               (∀ w → u2 w ≡ u2′ w) → (∀ w → v1 w ≡ v1′ w) →
               (∀ w → v2 w ≡ v2′ w) → (∀ w → y2 w ≡ y2′ w) →
               (∀ w → y3 w ≡ y3′ w) →
               FcS y1 u1 u2 v1 v2 y2 y3 ≡ FcS y1′ u1′ u2′ v1′ v2′ y2′ y3′
    FcS-cong {y1} {y1′} {u1} {u1′} {u2} {u2′} {v1} {v1′} {v2} {v2′}
             hy1 hu1 hu2 hv1 hv2 hy2 hy3 =
      cong₂ _xor_
        (cong₂ _xor_
          (cong₂ _xor_
            (cong₂ _xor_ (dot-cong (λ _ → refl) hy1)
              (cong₂ _xor_
                (xβ-cong s (λ w _ → hy1 w) (λ w _ → hu1 w) (λ w _ → hu2 w))
                (cong₂ _xor_ (sumᵇ-resp (fTerms gs) _ _ hw1)
                  (xβ-cong s (λ w _ → hw1 w) (λ w _ → hv1 w) (λ w _ → hv2 w)))))
            (dot-cong hw2 hy2))
          (sumᵇ-resp (f̃Terms gs) _ _ hy2))
        (dot-cong hy2 hy3)
      where
      hw1 : ∀ w → xout s y1 u2 w ≡ xout s y1′ u2′ w
      hw1 = xout-cong s hy1 (λ w _ → hu2 w)

      hw2 : ∀ w → xout s (xout s y1 u2) v2 w ≡ xout s (xout s y1′ u2′) v2′ w
      hw2 = xout-cong s hw1 (λ w _ → hv2 w)

  F-main : ∀ x (Z : CL → Bool) → (∀ e → Z (inj₂ e) ≡ dfltc x (inj₂ e) Z) →
           Fc x Z ≡ Phase.Fblk (sumᵇ gs) (sumᵇ-resp gs) (lhalf {m} s)
                               (rhalf {m} s) (λ ℓ → Z (inj₁ ℓ))
  F-main x Z h = trans simplify
    (blocks-par (sumᵇ gs) (sumᵇ-resp gs) s (Y1 Z) (Y2 Z) (Y3 Z)
                (λ ℓ → Z (inj₁ ℓ))
                (λ i → cong (λ ℓ → Z (inj₁ ℓ)) (wl-↑ˡ A₁ B₁ i))
                (λ i → cong (λ ℓ → Z (inj₁ ℓ)) (wl-↑ʳ A₁ B₁ i))
                (λ i → cong (λ ℓ → Z (inj₁ ℓ)) (wl-↑ˡ C₂ D₂ i))
                (λ i → cong (λ ℓ → Z (inj₁ ℓ)) (wl-↑ʳ C₂ D₂ i))
                (λ i → cong (λ ℓ → Z (inj₁ ℓ)) (wl-↑ˡ E₃ H₃ i))
                (λ i → cong (λ ℓ → Z (inj₁ ℓ)) (wl-↑ʳ E₃ H₃ i)))
    where
    onX : ∀ t w → s w ≡ true → Z (inj₂ (t , w)) ≡ xval t Z w
    onX t w e = trans (h (t , w)) (if-true e (xval t Z w) (Z (inj₂ (t , w))))

    W1 W2 : Assign n
    W1 = xout s (Y1 Z) (Xb u₂ Z)
    W2 = xout s W1 (Xb v₂ Z)

    -- After the first X layer the wires hold a ⊕ s; after the second,
    -- a again.

    W1-eq : ∀ w → W1 w ≡ (Y1 Z ⊕ᵃ s) w
    W1-eq w = pick (s w) refl
      where
      pick : ∀ b → s w ≡ b → (if b then Z (inj₂ (u₂ , w)) else Y1 Z w) ≡
                             Y1 Z w xor s w
      pick true  e = trans (onX u₂ w e) (cong (Y1 Z w xor_) (sym e))
      pick false e = trans (sym (xor-identityʳ (Y1 Z w)))
                           (cong (Y1 Z w xor_) (sym e))

    W2-eq : ∀ w → W2 w ≡ Y1 Z w
    W2-eq w = pick (s w) refl
      where
      pick : ∀ b → s w ≡ b → (if b then Z (inj₂ (v₂ , w)) else W1 w) ≡ Y1 Z w
      pick true  e = onX v₂ w e
      pick false e = if-false e (Z (inj₂ (u₂ , w))) (Y1 Z w)

    S : Bool
    S = sumᵇ (fTerms gs) W1

    first : dot (0ᵃ {n}) (Y1 Z) xor
            (xβ s (Y1 Z) (Xb u₁ Z) (Xb u₂ Z) xor
             (S xor xβ s W1 (Xb v₁ Z) (Xb v₂ Z))) ≡
            mm (sumᵇ gs) (Y1 Z ⊕ᵃ s)
    first = trans
      (cong₂ (λ a b → a xor (b xor (S xor xβ s W1 (Xb v₁ Z) (Xb v₂ Z))))
             (dot-0ˡ (Y1 Z)) (xβ-zero s (λ w e → onX u₁ w e)))
      (trans (cong (S xor_) (xβ-zero s (λ w e → onX v₁ w e)))
        (trans (xor-identityʳ S)
          (trans (sumᵇ-resp (fTerms gs) W1 (Y1 Z ⊕ᵃ s) W1-eq)
                 (sum-f gs (Y1 Z ⊕ᵃ s)))))

    simplify : Fc x Z ≡ hs-par (sumᵇ gs) s (Y1 Z) (Y2 Z) (Y3 Z)
    simplify = cong₂ _xor_
      (cong₂ _xor_
        (cong₂ _xor_ first (dot-cong W2-eq (λ _ → refl)))
        (sum-f̃ gs (Y2 Z)))
      refl

  private
    G-main : ∀ x (Z Z′ : CL → Bool) →
             (∀ i → Z (inj₁ (E₃ , i)) ≡ Z′ (inj₁ (E₃ , i))) →
             (∀ i → Z (inj₁ (H₃ , i)) ≡ Z′ (inj₁ (H₃ , i))) →
             ∀ w → Gc w x Z ≡ Gc w x Z′
    G-main x Z Z′ hE hH =
      Gblk-cong {Z = λ ℓ → Z (inj₁ ℓ)} {Z′ = λ ℓ → Z′ (inj₁ ℓ)} hE hH

  -- The three passes, with the X labels as extra labels, on the machine
  -- of any path-sum over K variables with these values.

  module CircuitPasses {K : ℕ} (ξ₀ : PathSum (m ℕ+ m) K K) =
    MP.Passes _≟ᴱ_ (sumᵇ gs) (sumᵇ-resp gs)
      (λ _ → lhalf {m} s) (λ _ → rhalf {m} s)
      (λ i → qlit (lhalf {m} s i)) (λ i → qlit (rhalf {m} s i))
      (λ _ _ _ _ → tt) (λ _ _ _ _ → tt)
      (λ _ _ _ → refl) (λ _ _ _ → refl)
      Fc Gc dfltc (λ _ _ _ → refl) F-main G-main ξ₀

  ----------------------------------------------------------------------
  -- Removing the X gates

  -- The labels still path variables while the X gates are removed:
  -- every block, and the X labels of the wires with s_w = 1 whose
  -- layer has not reached them (dU, dV).

  RetX : (Fin (m ℕ+ m) → Bool) → (Fin (m ℕ+ m) → Bool) → CL → Bool
  RetX dU dV (inj₁ ℓ)        = true
  RetX dU dV (inj₂ (u₁ , w)) = s w ∧ not (dU w)
  RetX dU dV (inj₂ (u₂ , w)) = s w ∧ not (dU w)
  RetX dU dV (inj₂ (v₁ , w)) = s w ∧ not (dV w)
  RetX dU dV (inj₂ (v₂ , w)) = s w ∧ not (dV w)

  private
    none all : Fin (m ℕ+ m) → Bool
    none _ = false
    all  _ = true

    RetXᵁ-resp : {d d′ : Fin n → Bool} → (∀ i → d i ≡ d′ i) →
                 ∀ ℓ → RetX d none ℓ ≡ RetX d′ none ℓ
    RetXᵁ-resp h (inj₁ ℓ)        = refl
    RetXᵁ-resp h (inj₂ (u₁ , w)) = cong (λ b → s w ∧ not b) (h w)
    RetXᵁ-resp h (inj₂ (u₂ , w)) = cong (λ b → s w ∧ not b) (h w)
    RetXᵁ-resp h (inj₂ (v₁ , w)) = refl
    RetXᵁ-resp h (inj₂ (v₂ , w)) = refl

    RetXⱽ-resp : {d d′ : Fin n → Bool} → (∀ i → d i ≡ d′ i) →
                 ∀ ℓ → RetX all d ℓ ≡ RetX all d′ ℓ
    RetXⱽ-resp h (inj₁ ℓ)        = refl
    RetXⱽ-resp h (inj₂ (u₁ , w)) = refl
    RetXⱽ-resp h (inj₂ (u₂ , w)) = refl
    RetXⱽ-resp h (inj₂ (v₁ , w)) = cong (λ b → s w ∧ not b) (h w)
    RetXⱽ-resp h (inj₂ (v₂ , w)) = cong (λ b → s w ∧ not b) (h w)

    -- Marking a wire with s_w = 0 done changes nothing.

    skip : ∀ (d : Fin n → Bool) w → s w ≡ false → ∀ w′ →
           s w′ ∧ not (d w′) ≡ s w′ ∧ not ((d [ w ≔ true ]) w′)
    skip d w e w′ = go (w′ Fin.≟ w)
      where
      go : Dec (w′ ≡ w) → s w′ ∧ not (d w′) ≡ s w′ ∧ not ((d [ w ≔ true ]) w′)
      go (yes refl) = trans (cong (λ b → b ∧ not (d w′)) e)
        (sym (cong (λ b → b ∧ not ((d [ w′ ≔ true ]) w′)) e))
      go (no ne) = cong (λ b → s w′ ∧ not b) (sym (≔-there d true ne))

    -- An X label and a label of another wire, or a label of another
    -- kind, differ.

    xw≢ : ∀ {t : XH} {w w′ : Fin n} → w′ ≢ w →
          inj₂ {A = Lbl m} (t , w′) ≢ inj₂ (t , w)
    xw≢ ne e = ne (cong proj₂ (inj₂-injective e))

  -- The X passes, on the machine of any path-sum over K variables.

  module XPasses {K : ℕ} (ξ₀ : PathSum (m ℕ+ m) K K) where

    open CircuitPasses ξ₀

    private
      -- The blocks are present throughout, and keep their values.

      aM : ∀ {dU dV v x Zt Zf} → FlipAt (RetX dU dV) (inj₂ v) x Zt Zf →
           ∀ ℓ → Zt (inj₁ ℓ) ≡ Zf (inj₁ ℓ)
      aM fl ℓ = kept fl (inj₁ ℓ) refl (λ ())

      -- An X label of a wire with s_w = 1, other than the flipped one,
      -- keeps its value: present, or removed with a fixed value that
      -- reads the blocks only.

      xval-agree : ∀ {Zt Zf : CL → Bool} → (∀ ℓ → Zt (inj₁ ℓ) ≡ Zf (inj₁ ℓ)) →
                   ∀ t w → xval t Zt w ≡ xval t Zf w
      xval-agree aM′ u₁ w = refl
      xval-agree aM′ u₂ w = cong (_xor true) (aM′ (wl A₁ B₁ w))
      xval-agree aM′ v₁ w = refl
      xval-agree aM′ v₂ w = aM′ (wl A₁ B₁ w)

      aX : ∀ {dU dV v x Zt Zf} → FlipAt (RetX dU dV) (inj₂ v) x Zt Zf →
           ∀ t w → s w ≡ true → inj₂ (t , w) ≢ inj₂ v →
           Zt (inj₂ (t , w)) ≡ Zf (inj₂ (t , w))
      aX {x = x} {Zt} {Zf} fl t w e ne = kept-or-fixed fl (inj₂ (t , w)) ne
        (λ _ → trans (if-true e (xval t Zt w) (Zt (inj₂ (t , w))))
          (trans (xval-agree (aM fl) t w)
                 (sym (if-true e (xval t Zf w) (Zf (inj₂ (t , w)))))))

      -- The derivative of the phase, term by term.

      med7 : ∀ a₀ a₁ a₂ a₃ a₄ a₅ a₆ b₀ b₁ b₂ b₃ b₄ b₅ b₆ →
        ((((a₀ xor (a₁ xor (a₂ xor a₃))) xor a₄) xor a₅) xor a₆) xor
        ((((b₀ xor (b₁ xor (b₂ xor b₃))) xor b₄) xor b₅) xor b₆) ≡
        ((((a₀ xor b₀) xor ((a₁ xor b₁) xor ((a₂ xor b₂) xor (a₃ xor b₃)))) xor
          (a₄ xor b₄)) xor (a₅ xor b₅)) xor (a₆ xor b₆)
      med7 a₀ a₁ a₂ a₃ a₄ a₅ a₆ b₀ b₁ b₂ b₃ b₄ b₅ b₆ = trans
        (xor-medial A₆ a₆ B₆ b₆)
        (cong (_xor (a₆ xor b₆)) (trans (xor-medial A₅ a₅ B₅ b₅)
          (cong (_xor (a₅ xor b₅)) (trans (xor-medial A₄ a₄ B₄ b₄)
            (cong (_xor (a₄ xor b₄))
              (trans (xor-medial a₀ (a₁ xor (a₂ xor a₃))
                                 b₀ (b₁ xor (b₂ xor b₃)))
                (cong ((a₀ xor b₀) xor_)
                  (trans (xor-medial a₁ (a₂ xor a₃) b₁ (b₂ xor b₃))
                    (cong ((a₁ xor b₁) xor_) (xor-medial a₂ a₃ b₂ b₃))))))))))
        where
        A₄ A₅ A₆ B₄ B₅ B₆ : Bool
        A₄ = a₀ xor (a₁ xor (a₂ xor a₃))
        A₅ = A₄ xor a₄
        A₆ = A₅ xor a₅
        B₄ = b₀ xor (b₁ xor (b₂ xor b₃))
        B₅ = B₄ xor b₄
        B₆ = B₅ xor b₅

      collapse : ∀ d₁ d₃ →
        ((((false xor (d₁ xor (false xor d₃))) xor false) xor false) xor
         false) ≡ d₁ xor d₃
      collapse false false = refl
      collapse false true  = refl
      collapse true  false = refl
      collapse true  true  = refl

      -- Fc splits into its seven terms.

      Fc-∂ : ∀ x (Zt Zf : CL → Bool) {d₁ d₃ : Bool} →
        dot (0ᵃ {n}) (Y1 Zt) xor dot (0ᵃ {n}) (Y1 Zf) ≡ false →
        xβ s (Y1 Zt) (Xb u₁ Zt) (Xb u₂ Zt) xor
          xβ s (Y1 Zf) (Xb u₁ Zf) (Xb u₂ Zf) ≡ d₁ →
        sumᵇ (fTerms gs) (xout s (Y1 Zt) (Xb u₂ Zt)) xor
          sumᵇ (fTerms gs) (xout s (Y1 Zf) (Xb u₂ Zf)) ≡ false →
        xβ s (xout s (Y1 Zt) (Xb u₂ Zt)) (Xb v₁ Zt) (Xb v₂ Zt) xor
          xβ s (xout s (Y1 Zf) (Xb u₂ Zf)) (Xb v₁ Zf) (Xb v₂ Zf) ≡ d₃ →
        dot (xout s (xout s (Y1 Zt) (Xb u₂ Zt)) (Xb v₂ Zt)) (Y2 Zt) xor
          dot (xout s (xout s (Y1 Zf) (Xb u₂ Zf)) (Xb v₂ Zf)) (Y2 Zf) ≡ false →
        sumᵇ (f̃Terms gs) (Y2 Zt) xor sumᵇ (f̃Terms gs) (Y2 Zf) ≡ false →
        dot (Y2 Zt) (Y3 Zt) xor dot (Y2 Zf) (Y3 Zf) ≡ false →
        Fc x Zt xor Fc x Zf ≡ d₁ xor d₃
      Fc-∂ x Zt Zf {d₁} {d₃} e₀ e₁ e₂ e₃ e₄ e₅ e₆ = trans
        (med7 (T₀ Zt) (T₁ Zt) (T₂ Zt) (T₃ Zt) (T₄ Zt) (T₅ Zt) (T₆ Zt)
              (T₀ Zf) (T₁ Zf) (T₂ Zf) (T₃ Zf) (T₄ Zf) (T₅ Zf) (T₆ Zf))
        (trans (cong₂ _xor_ (cong₂ _xor_ (cong₂ _xor_
                  (cong₂ _xor_ e₀ (cong₂ _xor_ e₁ (cong₂ _xor_ e₂ e₃)))
                  e₄) e₅) e₆)
               (collapse d₁ d₃))
        where
        T₀ T₁ T₂ T₃ T₄ T₅ T₆ : (CL → Bool) → Bool
        T₀ Z = dot (0ᵃ {n}) (Y1 Z)
        T₁ Z = xβ s (Y1 Z) (Xb u₁ Z) (Xb u₂ Z)
        T₂ Z = sumᵇ (fTerms gs) (xout s (Y1 Z) (Xb u₂ Z))
        T₃ Z = xβ s (xout s (Y1 Z) (Xb u₂ Z)) (Xb v₁ Z) (Xb v₂ Z)
        T₄ Z = dot (xout s (xout s (Y1 Z) (Xb u₂ Z)) (Xb v₂ Z)) (Y2 Z)
        T₅ Z = sumᵇ (f̃Terms gs) (Y2 Z)
        T₆ Z = dot (Y2 Z) (Y3 Z)

      -- The terms that read neither flipped bit do not change.

      xor-eq : ∀ {a b : Bool} → a ≡ b → a xor b ≡ false
      xor-eq {b = b} e = trans (cong (_xor b) e) (xor-same b)

      unchanged : ∀ {dU dV v x Zt Zf} →
        (fl : FlipAt (RetX dU dV) (inj₂ v) x Zt Zf) →
        (∀ w → xout s (Y1 Zt) (Xb u₂ Zt) w ≡ xout s (Y1 Zf) (Xb u₂ Zf) w) →
        (∀ w → xout s (xout s (Y1 Zt) (Xb u₂ Zt)) (Xb v₂ Zt) w ≡
               xout s (xout s (Y1 Zf) (Xb u₂ Zf)) (Xb v₂ Zf) w) →
        (dot (0ᵃ {n}) (Y1 Zt) xor dot (0ᵃ {n}) (Y1 Zf) ≡ false) ×
        (sumᵇ (fTerms gs) (xout s (Y1 Zt) (Xb u₂ Zt)) xor
           sumᵇ (fTerms gs) (xout s (Y1 Zf) (Xb u₂ Zf)) ≡ false) ×
        (dot (xout s (xout s (Y1 Zt) (Xb u₂ Zt)) (Xb v₂ Zt)) (Y2 Zt) xor
           dot (xout s (xout s (Y1 Zf) (Xb u₂ Zf)) (Xb v₂ Zf)) (Y2 Zf) ≡
           false) ×
        (sumᵇ (f̃Terms gs) (Y2 Zt) xor sumᵇ (f̃Terms gs) (Y2 Zf) ≡ false) ×
        (dot (Y2 Zt) (Y3 Zt) xor dot (Y2 Zf) (Y3 Zf) ≡ false)
      unchanged {Zt = Zt} {Zf} fl hW1 hW2 =
        cong₂ _xor_ (dot-0ˡ (Y1 Zt)) (dot-0ˡ (Y1 Zf)) ,
        xor-eq (sumᵇ-resp (fTerms gs) (xout s (Y1 Zt) (Xb u₂ Zt))
                          (xout s (Y1 Zf) (Xb u₂ Zf)) hW1) ,
        xor-eq (dot-cong hW2 hY2) ,
        xor-eq (sumᵇ-resp (f̃Terms gs) (Y2 Zt) (Y2 Zf) hY2) ,
        xor-eq (dot-cong hY2 hY3)
        where
        hY2 : ∀ w → Y2 Zt w ≡ Y2 Zf w
        hY2 w = aM fl (wl C₂ D₂ w)

        hY3 : ∀ w → Y3 Zt w ≡ Y3 Zf w
        hY3 w = aM fl (wl E₃ H₃ w)

    ----------------------------------------------------------------------
    -- The first X layer: [HH] at u₁_w with u₂_w ← a_w ⊕ 1

    passU : ∀ dU w → dU w ≡ false → State (RetX dU none) →
            State (RetX (dU [ w ≔ true ]) none)
    passU dU w dw st = go (s w) refl
      where
      go : ∀ b → s w ≡ b → State (RetX (dU [ w ≔ true ]) none)
      go false e = State-resp (resp-skip e) st
        where
        resp-skip : s w ≡ false → ∀ ℓ → RetX dU none ℓ ≡
                                         RetX (dU [ w ≔ true ]) none ℓ
        resp-skip e (inj₁ ℓ)         = refl
        resp-skip e (inj₂ (u₁ , w′)) = skip dU w e w′
        resp-skip e (inj₂ (u₂ , w′)) = skip dU w e w′
        resp-skip e (inj₂ (v₁ , w′)) = refl
        resp-skip e (inj₂ (v₂ , w′)) = refl
      go true e = step st S (RetX (dU [ w ≔ true ]) none) off off R′
        where
        v u : CL
        v = inj₂ (u₁ , w)
        u = inj₂ (u₂ , w)

        on : s w ∧ not (dU w) ≡ true
        on = cong₂ (λ a b → a ∧ not b) e dw

        off : s w ∧ not ((dU [ w ≔ true ]) w) ≡ false
        off = trans (cong (λ b → s w ∧ not b) (≔-here dU w true))
                    (∧-zeroʳ (s w))

        ∂F : ∀ x Zt Zf → FlipAt (RetX dU none) v x Zt Zf →
             Fc x Zt xor Fc x Zf ≡
             Zf u xor ⟦ qvar (inj₁ (wl A₁ B₁ w)) q⊕ qlit true ⟧q x Zf
        ∂F x Zt Zf fl =
          let (e₀ , e₂ , e₄ , e₅ , e₆) = unchanged fl hW1 hW2 in
          trans (Fc-∂ x Zt Zf e₀ d₁ e₂ e₃ e₄ e₅ e₆)
            (trans (xor-identityʳ _)
                   (xor-comm (Y1 Zf w xor true) (Zf u)))
          where
          hY1 : ∀ w′ → Y1 Zt w′ ≡ Y1 Zf w′
          hY1 w′ = aM fl (wl A₁ B₁ w′)

          hU2 : ∀ w′ → s w′ ≡ true → Xb u₂ Zt w′ ≡ Xb u₂ Zf w′
          hU2 w′ e′ = aX fl u₂ w′ e′ (λ ())

          hW1 : ∀ w′ → xout s (Y1 Zt) (Xb u₂ Zt) w′ ≡
                       xout s (Y1 Zf) (Xb u₂ Zf) w′
          hW1 = xout-cong s hY1 hU2

          hW2 : ∀ w′ → xout s (xout s (Y1 Zt) (Xb u₂ Zt)) (Xb v₂ Zt) w′ ≡
                       xout s (xout s (Y1 Zf) (Xb u₂ Zf)) (Xb v₂ Zf) w′
          hW2 = xout-cong s hW1 (λ w′ e′ → aX fl v₂ w′ e′ (λ ()))

          d₁ : xβ s (Y1 Zt) (Xb u₁ Zt) (Xb u₂ Zt) xor
               xβ s (Y1 Zf) (Xb u₁ Zf) (Xb u₂ Zf) ≡
               (Y1 Zf w xor true) xor Xb u₂ Zf w
          d₁ = xβ-∂ s w e (λ w′ _ → hY1 w′)
                 (λ w′ e′ ne → aX fl u₁ w′ e′ (xw≢ ne)) hU2
                 (flip-t fl) (flip-f fl)

          e₃ : xβ s (xout s (Y1 Zt) (Xb u₂ Zt)) (Xb v₁ Zt) (Xb v₂ Zt) xor
               xβ s (xout s (Y1 Zf) (Xb u₂ Zf)) (Xb v₁ Zf) (Xb v₂ Zf) ≡ false
          e₃ = xor-eq
                 (xβ-cong s (λ w′ _ → hW1 w′)
                          (λ w′ e′ → aX fl v₁ w′ e′ (λ ()))
                          (λ w′ e′ → aX fl v₂ w′ e′ (λ ())))

        ∂G : ∀ x Zt Zf → FlipAt (RetX dU none) v x Zt Zf →
             ∀ w′ → Gc w′ x Zt ≡ Gc w′ x Zf
        ∂G x Zt Zf fl = G-main x Zt Zf (λ i → aM fl (E₃ , i))
                                       (λ i → aM fl (H₃ , i))

        S : Step (RetX dU none) v u
        S = record
          { v-on    = on
          ; u-on    = on
          ; v≢u     = λ ()
          ; quot    = qvar (inj₁ (wl A₁ B₁ w)) q⊕ qlit true
          ; quot-ok = (refl , (λ ()) , (λ ())) , tt
          ; ∂F      = ∂F
          ; ∂G      = ∂G
          ; v-dflt  = λ x Z → if-true e false (Z v)
          ; u-dflt  = λ x Z → if-true e (Y1 Z w xor true) (Z u)
          }

        R′ : ∀ ℓ → ℓ ≢ v → ℓ ≢ u →
             RetX (dU [ w ≔ true ]) none ℓ ≡ RetX dU none ℓ
        R′ (inj₁ ℓ)         _  _  = refl
        R′ (inj₂ (u₁ , w′)) ne _  = cong (λ b → s w′ ∧ not b)
          (≔-there dU true (λ eq → ne (cong (λ z → inj₂ (u₁ , z)) eq)))
        R′ (inj₂ (u₂ , w′)) _  ne = cong (λ b → s w′ ∧ not b)
          (≔-there dU true (λ eq → ne (cong (λ z → inj₂ (u₂ , z)) eq)))
        R′ (inj₂ (v₁ , w′)) _  _  = refl
        R′ (inj₂ (v₂ , w′)) _  _  = refl

    ----------------------------------------------------------------------
    -- The second X layer: [HH] at v₁_w with v₂_w ← a_w

    passV : ∀ dV w → dV w ≡ false → State (RetX all dV) →
            State (RetX all (dV [ w ≔ true ]))
    passV dV w dw st = go (s w) refl
      where
      go : ∀ b → s w ≡ b → State (RetX all (dV [ w ≔ true ]))
      go false e = State-resp (resp-skip e) st
        where
        resp-skip : s w ≡ false → ∀ ℓ → RetX all dV ℓ ≡
                                         RetX all (dV [ w ≔ true ]) ℓ
        resp-skip e (inj₁ ℓ)         = refl
        resp-skip e (inj₂ (u₁ , w′)) = refl
        resp-skip e (inj₂ (u₂ , w′)) = refl
        resp-skip e (inj₂ (v₁ , w′)) = skip dV w e w′
        resp-skip e (inj₂ (v₂ , w′)) = skip dV w e w′
      go true e = step st S (RetX all (dV [ w ≔ true ])) off off R′
        where
        v u : CL
        v = inj₂ (v₁ , w)
        u = inj₂ (v₂ , w)

        on : s w ∧ not (dV w) ≡ true
        on = cong₂ (λ a b → a ∧ not b) e dw

        off : s w ∧ not ((dV [ w ≔ true ]) w) ≡ false
        off = trans (cong (λ b → s w ∧ not b) (≔-here dV w true))
                    (∧-zeroʳ (s w))

        ∂F : ∀ x Zt Zf → FlipAt (RetX all dV) v x Zt Zf →
             Fc x Zt xor Fc x Zf ≡
             Zf u xor ⟦ qvar (inj₁ (wl A₁ B₁ w)) ⟧q x Zf
        ∂F x Zt Zf fl =
          let (e₀ , e₂ , e₄ , e₅ , e₆) = unchanged fl hW1 hW2 in
          trans (Fc-∂ x Zt Zf e₀ e₁ e₂ d₃ e₄ e₅ e₆)
            (trans (cong (λ a → (a xor true) xor Zf u) W1-w)
              (trans (cong (_xor Zf u) (xor-true-true (Y1 Zf w)))
                     (xor-comm (Y1 Zf w) (Zf u))))
          where
          hY1 : ∀ w′ → Y1 Zt w′ ≡ Y1 Zf w′
          hY1 w′ = aM fl (wl A₁ B₁ w′)

          hU2 : ∀ w′ → s w′ ≡ true → Xb u₂ Zt w′ ≡ Xb u₂ Zf w′
          hU2 w′ e′ = aX fl u₂ w′ e′ (λ ())

          hW1 : ∀ w′ → xout s (Y1 Zt) (Xb u₂ Zt) w′ ≡
                       xout s (Y1 Zf) (Xb u₂ Zf) w′
          hW1 = xout-cong s hY1 hU2

          hV2 : ∀ w′ → s w′ ≡ true → Xb v₂ Zt w′ ≡ Xb v₂ Zf w′
          hV2 w′ e′ = aX fl v₂ w′ e′ (λ ())

          hW2 : ∀ w′ → xout s (xout s (Y1 Zt) (Xb u₂ Zt)) (Xb v₂ Zt) w′ ≡
                       xout s (xout s (Y1 Zf) (Xb u₂ Zf)) (Xb v₂ Zf) w′
          hW2 = xout-cong s hW1 hV2

          e₁ : xβ s (Y1 Zt) (Xb u₁ Zt) (Xb u₂ Zt) xor
               xβ s (Y1 Zf) (Xb u₁ Zf) (Xb u₂ Zf) ≡ false
          e₁ = xor-eq
                 (xβ-cong s (λ w′ _ → hY1 w′)
                          (λ w′ e′ → aX fl u₁ w′ e′ (λ ())) hU2)

          d₃ : xβ s (xout s (Y1 Zt) (Xb u₂ Zt)) (Xb v₁ Zt) (Xb v₂ Zt) xor
               xβ s (xout s (Y1 Zf) (Xb u₂ Zf)) (Xb v₁ Zf) (Xb v₂ Zf) ≡
               (xout s (Y1 Zf) (Xb u₂ Zf) w xor true) xor Xb v₂ Zf w
          d₃ = xβ-∂ s w e (λ w′ _ → hW1 w′)
                 (λ w′ e′ ne → aX fl v₁ w′ e′ (xw≢ ne)) hV2
                 (flip-t fl) (flip-f fl)

          -- The first layer's X on w is gone: its wire holds a_w ⊕ 1.

          W1-w : xout s (Y1 Zf) (Xb u₂ Zf) w ≡ Y1 Zf w xor true
          W1-w = trans (if-true e (Zf (inj₂ (u₂ , w))) (Y1 Zf w))
            (trans (dflt-f fl (inj₂ (u₂ , w)) (∧-zeroʳ (s w)))
                   (if-true e (Y1 Zf w xor true) (Zf (inj₂ (u₂ , w)))))

        ∂G : ∀ x Zt Zf → FlipAt (RetX all dV) v x Zt Zf →
             ∀ w′ → Gc w′ x Zt ≡ Gc w′ x Zf
        ∂G x Zt Zf fl = G-main x Zt Zf (λ i → aM fl (E₃ , i))
                                       (λ i → aM fl (H₃ , i))

        S : Step (RetX all dV) v u
        S = record
          { v-on    = on
          ; u-on    = on
          ; v≢u     = λ ()
          ; quot    = qvar (inj₁ (wl A₁ B₁ w))
          ; quot-ok = refl , (λ ()) , (λ ())
          ; ∂F      = ∂F
          ; ∂G      = ∂G
          ; v-dflt  = λ x Z → if-true e false (Z v)
          ; u-dflt  = λ x Z → if-true e (Y1 Z w) (Z u)
          }

        R′ : ∀ ℓ → ℓ ≢ v → ℓ ≢ u →
             RetX all (dV [ w ≔ true ]) ℓ ≡ RetX all dV ℓ
        R′ (inj₁ ℓ)         _  _  = refl
        R′ (inj₂ (u₁ , w′)) _  _  = refl
        R′ (inj₂ (u₂ , w′)) _  _  = refl
        R′ (inj₂ (v₁ , w′)) ne _  = cong (λ b → s w′ ∧ not b)
          (≔-there dV true (λ eq → ne (cong (λ z → inj₂ (v₁ , z)) eq)))
        R′ (inj₂ (v₂ , w′)) _  ne = cong (λ b → s w′ ∧ not b)
          (≔-there dV true (λ eq → ne (cong (λ z → inj₂ (v₂ , z)) eq)))

    ----------------------------------------------------------------------
    -- All of it

    -- Both X layers, then the three passes.

    xpasses : State (RetX none none) → State (RetX all all)
    xpasses st = second (first st)
      where
      first : State (RetX none none) → State (RetX all none)
      first = Sweep.all (λ d → State (RetX d none))
                        (λ h → State-resp (RetXᵁ-resp h)) passU

      second : State (RetX all none) → State (RetX all all)
      second = Sweep.all (λ d → State (RetX all d))
                         (λ h → State-resp (RetXⱽ-resp h)) passV

    complete-X : State (RetX none none) →
                 Σ (PathSum (m ℕ+ m) 0 0) (λ ζ → ξ₀ ⟶ᶠ* ζ)
    complete-X st = complete (State-resp X→M (xpasses st))
      where
      X→M : ∀ ℓ → RetX all all ℓ ≡ RetM₁ (λ _ → false) ℓ
      X→M (inj₁ ℓ)        = sym (Ret₁-all ℓ)
      X→M (inj₂ (u₁ , w)) = ∧-zeroʳ (s w)
      X→M (inj₂ (u₂ , w)) = ∧-zeroʳ (s w)
      X→M (inj₂ (v₁ , w)) = ∧-zeroʳ (s w)
      X→M (inj₂ (v₂ , w)) = ∧-zeroʳ (s w)

  ----------------------------------------------------------------------
  -- The circuit's layers along a path

  private
    Hn F O D X : Circuit (m ℕ+ m)
    Hn = hadamards (m ℕ+ m)
    F  = flips s
    O  = oracleᶠ gs
    D  = oracleᵈ gs
    X  = F ++ (O ++ F)

  -- The streams the layers read: the last Hadamard layer the path's
  -- own, each earlier layer the stream past the later layers'
  -- Hadamards (the second X layer reads s₃, the first sF).

  s₁ s₂ s₃ sO sF sH : Stream → Stream
  s₁ st = shift (norm Hn) st
  s₂ st = shift (norm D) (s₁ st)
  s₃ st = shift (norm Hn) (s₂ st)
  sO st = shift (norm F) (s₃ st)
  sF st = shift (norm (O ++ F)) (s₃ st)
  sH st = shift (norm X) (s₃ st)

  -- The bits the Hadamard layers put on the wires.

  Y₁ᵗ Y₂ᵗ Y₃ᵗ : Stream → Assign (m ℕ+ m)
  Y₁ᵗ st = hbits n (sH st)
  Y₂ᵗ st = hbits n (s₂ st)
  Y₃ᵗ st = hbits n st

  -- Figure 3(a) along a path, from |0⟩: phase ½ FcS of the bits its
  -- Hadamards read, wires the third layer's.

  runs-HS : ∀ (st : Stream) →
            Runs (HSᶜ gs s) st (0ᵃ {n})
                 (FcS (Y₁ᵗ st) (xbits s (sF st) true) (xbits s (sF st) false)
                      (xbits s (s₃ st) true) (xbits s (s₃ st) false)
                      (Y₂ᵗ st) (Y₃ᵗ st))
                 (Y₃ᵗ st)
  runs-HS st =
    Runs-++ (((Hn ++ X) ++ Hn) ++ D) Hn
      (Runs-++ ((Hn ++ X) ++ Hn) D
        (Runs-++ (Hn ++ X) Hn
          (Runs-++ Hn X (Runs-hadamards n (sH st) (0ᵃ {n}))
            (Runs-++ F (O ++ F) (Runs-flips s (sF st) (Y₁ᵗ st))
              (Runs-++ O F (Runs-oracle (fTerms gs) (sO st) W₁)
                           (Runs-flips s (s₃ st) W₁))))
          (Runs-hadamards n (s₂ st) W₂))
        (Runs-oracle (f̃Terms gs) (s₁ st) (Y₂ᵗ st)))
      (Runs-hadamards n st (Y₂ᵗ st))
    where
    W₁ W₂ : Assign n
    W₁ = xout s (Y₁ᵗ st) (xbits s (sF st) false)
    W₂ = xout s W₁ (xbits s (s₃ st) false)

  ----------------------------------------------------------------------
  -- The path variables, labelled

  -- The position of each label: the third layer's, the second's, the
  -- second X layer's, the first X layer's and the first layer's
  -- variables, in that order; wire w of a Hadamard layer at n-1-w, the
  -- X gates at PathSum.HiddenShift.Runs's xrev.

  private
    g₁ g₂ g₃ : Fin n → ℕ
    g₁ w = n ℕ+ (n ℕ+ (nF s ℕ+ (nF s ℕ+ toℕ (opposite w))))
    g₂ w = n ℕ+ toℕ (opposite w)
    g₃ w = toℕ (opposite w)

  gpos : CL → ℕ
  gpos (inj₁ (A₁ , i))  = g₁ (i ↑ˡ m)
  gpos (inj₁ (B₁ , i))  = g₁ (m ↑ʳ i)
  gpos (inj₁ (C₂ , i))  = g₂ (i ↑ˡ m)
  gpos (inj₁ (D₂ , i))  = g₂ (m ↑ʳ i)
  gpos (inj₁ (E₃ , i))  = g₃ (i ↑ˡ m)
  gpos (inj₁ (H₃ , i))  = g₃ (m ↑ʳ i)
  gpos (inj₂ (u₁ , w)) = n ℕ+ (n ℕ+ (nF s ℕ+ xrev s w true))
  gpos (inj₂ (u₂ , w)) = n ℕ+ (n ℕ+ (nF s ℕ+ xrev s w false))
  gpos (inj₂ (v₁ , w)) = n ℕ+ (n ℕ+ xrev s w true)
  gpos (inj₂ (v₂ , w)) = n ℕ+ (n ℕ+ xrev s w false)

  private
    Kr : ℕ
    Kr = n ℕ+ (n ℕ+ (nF s ℕ+ (nF s ℕ+ n)))

    -- The X gate a position of an X layer names.

    xlab : XH → XH → Fin n × Bool → XL
    xlab a b (w , true)  = a , w
    xlab a b (w , false) = b , w

    fE fC fA : Fin n → CL
    fE q = inj₁ (wl E₃ H₃ (opposite q))
    fC q = inj₁ (wl C₂ D₂ (opposite q))
    fA q = inj₁ (wl A₁ B₁ (opposite q))

    fV fU : Fin (nF s) → CL
    fV q = inj₂ (xlab v₁ v₂ (xdecF s q))
    fU q = inj₂ (xlab u₁ u₂ (xdecF s q))

    g₃ₚ : Fin (nF s ℕ+ n) → CL
    g₃ₚ p = [ fU , fA ]′ (splitAt (nF s) p)

    g₂ₚ : Fin (nF s ℕ+ (nF s ℕ+ n)) → CL
    g₂ₚ p = [ fV , g₃ₚ ]′ (splitAt (nF s) p)

    g₁ₚ : Fin (n ℕ+ (nF s ℕ+ (nF s ℕ+ n))) → CL
    g₁ₚ p = [ fC , g₂ₚ ]′ (splitAt n p)

  labR : Fin ((m ℕ+ m) ℕ+ ((m ℕ+ m) ℕ+ (nF s ℕ+ (nF s ℕ+ (m ℕ+ m))))) → CL
  labR p = [ fE , g₁ₚ ]′ (splitAt n p)

  private
    gpos-xU : ∀ wt → gpos (inj₂ (xlab u₁ u₂ wt)) ≡
                     n ℕ+ (n ℕ+ (nF s ℕ+ xrev s (proj₁ wt) (proj₂ wt)))
    gpos-xU (w , true)  = refl
    gpos-xU (w , false) = refl

    gpos-xV : ∀ wt → gpos (inj₂ (xlab v₁ v₂ wt)) ≡
                     n ℕ+ (n ℕ+ xrev s (proj₁ wt) (proj₂ wt))
    gpos-xV (w , true)  = refl
    gpos-xV (w , false) = refl

    gpos-wl₁ : ∀ w → gpos (inj₁ (wl A₁ B₁ w)) ≡ g₁ w
    gpos-wl₁ = wl-inv A₁ B₁ (λ ℓ → gpos (inj₁ ℓ)) g₁ (λ _ → refl) (λ _ → refl)

    gpos-wl₂ : ∀ w → gpos (inj₁ (wl C₂ D₂ w)) ≡ g₂ w
    gpos-wl₂ = wl-inv C₂ D₂ (λ ℓ → gpos (inj₁ ℓ)) g₂ (λ _ → refl) (λ _ → refl)

    gpos-wl₃ : ∀ w → gpos (inj₁ (wl E₃ H₃ w)) ≡ g₃ w
    gpos-wl₃ = wl-inv E₃ H₃ (λ ℓ → gpos (inj₁ ℓ)) g₃ (λ _ → refl) (λ _ → refl)

    opp : (q : Fin n) → toℕ (opposite (opposite q)) ≡ toℕ q
    opp q = cong toℕ (Fin.opposite-involutive q)

  -- Every position's label is read at that position.

  gpos-labR : ∀ p → gpos (labR p) ≡ toℕ p
  gpos-labR = split-inv n (n ℕ+ (nF s ℕ+ (nF s ℕ+ n))) fE g₁ₚ gpos toℕ hE
    (λ p → trans (level₁ p) (sym (Fin.toℕ-↑ʳ n p)))
    where
    hE : ∀ q → gpos (fE q) ≡ toℕ (q ↑ˡ (n ℕ+ (nF s ℕ+ (nF s ℕ+ n))))
    hE q = trans (gpos-wl₃ (opposite q))
                 (trans (opp q)
                        (sym (Fin.toℕ-↑ˡ q (n ℕ+ (nF s ℕ+ (nF s ℕ+ n))))))

    hA : ∀ q → gpos (fA q) ≡ n ℕ+ (n ℕ+ (nF s ℕ+ toℕ (nF s ↑ʳ q)))
    hA q = trans (gpos-wl₁ (opposite q))
      (cong (λ t → n ℕ+ (n ℕ+ (nF s ℕ+ t)))
            (trans (cong (nF s ℕ+_) (opp q)) (sym (Fin.toℕ-↑ʳ (nF s) q))))

    hU : ∀ q → gpos (fU q) ≡ n ℕ+ (n ℕ+ (nF s ℕ+ toℕ (q ↑ˡ n)))
    hU q = trans (gpos-xU (xdecF s q))
      (cong (λ t → n ℕ+ (n ℕ+ (nF s ℕ+ t)))
            (trans (xdec-rev s q) (sym (Fin.toℕ-↑ˡ q n))))

    level₃ : ∀ p → gpos (g₃ₚ p) ≡ n ℕ+ (n ℕ+ (nF s ℕ+ toℕ p))
    level₃ = split-inv (nF s) n fU fA gpos (λ p → n ℕ+ (n ℕ+ (nF s ℕ+ toℕ p)))
                       hU hA

    hV : ∀ q → gpos (fV q) ≡ n ℕ+ (n ℕ+ toℕ (q ↑ˡ (nF s ℕ+ n)))
    hV q = trans (gpos-xV (xdecF s q))
      (cong (λ t → n ℕ+ (n ℕ+ t))
            (trans (xdec-rev s q) (sym (Fin.toℕ-↑ˡ q (nF s ℕ+ n)))))

    level₂ : ∀ p → gpos (g₂ₚ p) ≡ n ℕ+ (n ℕ+ toℕ p)
    level₂ = split-inv (nF s) (nF s ℕ+ n) fV g₃ₚ gpos (λ p → n ℕ+ (n ℕ+ toℕ p))
      hV (λ p → trans (level₃ p)
                      (cong (λ t → n ℕ+ (n ℕ+ t)) (sym (Fin.toℕ-↑ʳ (nF s) p))))

    hC : ∀ q → gpos (fC q) ≡ n ℕ+ toℕ (q ↑ˡ (nF s ℕ+ (nF s ℕ+ n)))
    hC q = trans (gpos-wl₂ (opposite q))
      (cong (n ℕ+_) (trans (opp q) (sym (Fin.toℕ-↑ˡ q (nF s ℕ+ (nF s ℕ+ n))))))

    level₁ : ∀ p → gpos (g₁ₚ p) ≡ n ℕ+ toℕ p
    level₁ = split-inv n (nF s ℕ+ (nF s ℕ+ n)) fC g₂ₚ gpos (λ p → n ℕ+ toℕ p)
      hC (λ p → trans (level₂ p) (cong (n ℕ+_) (sym (Fin.toℕ-↑ʳ n p))))

  -- At the start, the labels still path variables are the blocks and
  -- the X gates of the wires with s_w = 1.

  private
    Ret₀ : CL → Bool
    Ret₀ = RetX none none

    RxU : ∀ wt → s (proj₁ wt) ≡ true → Ret₀ (inj₂ (xlab u₁ u₂ wt)) ≡ true
    RxU (w , true)  h = cong (_∧ true) h
    RxU (w , false) h = cong (_∧ true) h

    RxV : ∀ wt → s (proj₁ wt) ≡ true → Ret₀ (inj₂ (xlab v₁ v₂ wt)) ≡ true
    RxV (w , true)  h = cong (_∧ true) h
    RxV (w , false) h = cong (_∧ true) h

  Ret₀-labR : ∀ p → RetX none none (labR p) ≡ true
  Ret₀-labR =
    split-inv n (n ℕ+ (nF s ℕ+ (nF s ℕ+ n))) fE g₁ₚ Ret₀ (λ _ → true)
      (λ _ → refl)
      (split-inv n (nF s ℕ+ (nF s ℕ+ n)) fC g₂ₚ Ret₀ (λ _ → true)
        (λ _ → refl)
        (split-inv (nF s) (nF s ℕ+ n) fV g₃ₚ Ret₀ (λ _ → true)
          (λ q → RxV (xdecF s q) (xdec-ok s q))
          (split-inv (nF s) n fU fA Ret₀ (λ _ → true)
            (λ q → RxU (xdecF s q) (xdec-ok s q)) (λ _ → refl))))

  -- The position of a present label, whose label is it.

  posP : (ℓ : CL) → RetX none none ℓ ≡ true →
         Fin ((m ℕ+ m) ℕ+ ((m ℕ+ m) ℕ+ (nF s ℕ+ (nF s ℕ+ (m ℕ+ m)))))
  posP (inj₁ (A₁ , i)) _ = n ↑ʳ (n ↑ʳ (nF s ↑ʳ (nF s ↑ʳ opposite (i ↑ˡ m))))
  posP (inj₁ (B₁ , i)) _ = n ↑ʳ (n ↑ʳ (nF s ↑ʳ (nF s ↑ʳ opposite (m ↑ʳ i))))
  posP (inj₁ (C₂ , i)) _ = n ↑ʳ (opposite (i ↑ˡ m) ↑ˡ (nF s ℕ+ (nF s ℕ+ n)))
  posP (inj₁ (D₂ , i)) _ = n ↑ʳ (opposite (m ↑ʳ i) ↑ˡ (nF s ℕ+ (nF s ℕ+ n)))
  posP (inj₁ (E₃ , i)) _ = opposite (i ↑ˡ m) ↑ˡ (n ℕ+ (nF s ℕ+ (nF s ℕ+ n)))
  posP (inj₁ (H₃ , i)) _ = opposite (m ↑ʳ i) ↑ˡ (n ℕ+ (nF s ℕ+ (nF s ℕ+ n)))
  posP (inj₂ (u₁ , w)) R =
    n ↑ʳ (n ↑ʳ (nF s ↑ʳ (xposF s w true (∧-true R) ↑ˡ n)))
  posP (inj₂ (u₂ , w)) R =
    n ↑ʳ (n ↑ʳ (nF s ↑ʳ (xposF s w false (∧-true R) ↑ˡ n)))
  posP (inj₂ (v₁ , w)) R =
    n ↑ʳ (n ↑ʳ (xposF s w true (∧-true R) ↑ˡ (nF s ℕ+ n)))
  posP (inj₂ (v₂ , w)) R =
    n ↑ʳ (n ↑ʳ (xposF s w false (∧-true R) ↑ˡ (nF s ℕ+ n)))

  private
    -- Down the nested splits to the first layer, the first X layer, the
    -- second X layer, the second layer, the third.

    toA : ∀ q → labR (n ↑ʳ (n ↑ʳ (nF s ↑ʳ (nF s ↑ʳ q)))) ≡ fA q
    toA q = trans (sel-ʳ n (n ℕ+ (nF s ℕ+ (nF s ℕ+ n))) fE g₁ₚ _)
      (trans (sel-ʳ n (nF s ℕ+ (nF s ℕ+ n)) fC g₂ₚ _)
        (trans (sel-ʳ (nF s) (nF s ℕ+ n) fV g₃ₚ _) (sel-ʳ (nF s) n fU fA q)))

    toU : ∀ q → labR (n ↑ʳ (n ↑ʳ (nF s ↑ʳ (q ↑ˡ n)))) ≡ fU q
    toU q = trans (sel-ʳ n (n ℕ+ (nF s ℕ+ (nF s ℕ+ n))) fE g₁ₚ _)
      (trans (sel-ʳ n (nF s ℕ+ (nF s ℕ+ n)) fC g₂ₚ _)
        (trans (sel-ʳ (nF s) (nF s ℕ+ n) fV g₃ₚ _) (sel-ˡ (nF s) n fU fA q)))

    toV : ∀ q → labR (n ↑ʳ (n ↑ʳ (q ↑ˡ (nF s ℕ+ n)))) ≡ fV q
    toV q = trans (sel-ʳ n (n ℕ+ (nF s ℕ+ (nF s ℕ+ n))) fE g₁ₚ _)
      (trans (sel-ʳ n (nF s ℕ+ (nF s ℕ+ n)) fC g₂ₚ _)
        (sel-ˡ (nF s) (nF s ℕ+ n) fV g₃ₚ q))

    toC : ∀ q → labR (n ↑ʳ (q ↑ˡ (nF s ℕ+ (nF s ℕ+ n)))) ≡ fC q
    toC q = trans (sel-ʳ n (n ℕ+ (nF s ℕ+ (nF s ℕ+ n))) fE g₁ₚ _)
      (sel-ˡ n (nF s ℕ+ (nF s ℕ+ n)) fC g₂ₚ q)

    toE : ∀ q → labR (q ↑ˡ (n ℕ+ (nF s ℕ+ (nF s ℕ+ n)))) ≡ fE q
    toE q = sel-ˡ n (n ℕ+ (nF s ℕ+ (nF s ℕ+ n))) fE g₁ₚ q

    wlo : ∀ (b b′ : Blk) (w : Fin n) →
          wl {m} b b′ (opposite (opposite w)) ≡ wl {m} b b′ w
    wlo b b′ w = cong (wl {m} b b′) (Fin.opposite-involutive w)

  labR-posP : ∀ ℓ R → labR (posP ℓ R) ≡ ℓ
  labR-posP (inj₁ (A₁ , i)) _ = trans (toA _)
    (cong inj₁ (trans (wlo A₁ B₁ (i ↑ˡ m)) (wl-↑ˡ A₁ B₁ i)))
  labR-posP (inj₁ (B₁ , i)) _ = trans (toA _)
    (cong inj₁ (trans (wlo A₁ B₁ (m ↑ʳ i)) (wl-↑ʳ A₁ B₁ i)))
  labR-posP (inj₁ (C₂ , i)) _ = trans (toC _)
    (cong inj₁ (trans (wlo C₂ D₂ (i ↑ˡ m)) (wl-↑ˡ C₂ D₂ i)))
  labR-posP (inj₁ (D₂ , i)) _ = trans (toC _)
    (cong inj₁ (trans (wlo C₂ D₂ (m ↑ʳ i)) (wl-↑ʳ C₂ D₂ i)))
  labR-posP (inj₁ (E₃ , i)) _ = trans (toE _)
    (cong inj₁ (trans (wlo E₃ H₃ (i ↑ˡ m)) (wl-↑ˡ E₃ H₃ i)))
  labR-posP (inj₁ (H₃ , i)) _ = trans (toE _)
    (cong inj₁ (trans (wlo E₃ H₃ (m ↑ʳ i)) (wl-↑ʳ E₃ H₃ i)))
  labR-posP (inj₂ (u₁ , w)) R = trans (toU _)
    (cong (λ wt → inj₂ (xlab u₁ u₂ wt)) (xdec-xpos s w true (∧-true R)))
  labR-posP (inj₂ (u₂ , w)) R = trans (toU _)
    (cong (λ wt → inj₂ (xlab u₁ u₂ wt)) (xdec-xpos s w false (∧-true R)))
  labR-posP (inj₂ (v₁ , w)) R = trans (toV _)
    (cong (λ wt → inj₂ (xlab v₁ v₂ wt)) (xdec-xpos s w true (∧-true R)))
  labR-posP (inj₂ (v₂ , w)) R = trans (toV _)
    (cong (λ wt → inj₂ (xlab v₁ v₂ wt)) (xdec-xpos s w false (∧-true R)))

  ----------------------------------------------------------------------
  -- The circuit's path-sum, labelled

  private
    ξA : PathSum n (norm (HSᶜ gs s)) (paths (HSᶜ gs s))
    ξA = at0 ⟦ HSᶜ gs s ⟧

    K : ℕ
    K = paths (HSᶜ gs s)

    eK : K ≡ Kr
    eK = trans (paths≡norm (HSᶜ gs s))
      (trans (norm-HSᶜ gs s)
        (solve 2 (λ a f → ((((a :+ con 0) :+ a) :+ con 0) :+ a) :+
                          ((f :+ f) :+ con 0) :=
                          a :+ (a :+ (f :+ (f :+ a)))) refl n (nF s)))

    lab₀ : Fin K → CL
    lab₀ p = labR (cast eK p)

    ρ₀ : Assign n → Assign K → CL → Bool
    ρ₀ x y ℓ = str y (gpos ℓ)

    at-toℕ : ∀ p → gpos (lab₀ p) ≡ toℕ p
    at-toℕ p = trans (gpos-labR (cast eK p)) (Fin.toℕ-cast eK p)

    reads₀ : ∀ x y p → ρ₀ x y (lab₀ p) ≡ y p
    reads₀ x y p = trans (cong (str y) (at-toℕ p)) (pathOf-str y p)

    ∧-false : ∀ {b} → b ∧ not false ≡ false → b ≡ false
    ∧-false {false} _ = refl
    ∧-false {true}  ()

    dflts₀ : ∀ x y ℓ → Ret₀ ℓ ≡ false → ρ₀ x y ℓ ≡ dfltc x ℓ (ρ₀ x y)
    dflts₀ x y (inj₁ ℓ) ()
    dflts₀ x y (inj₂ (u₁ , w)) R =
      sym (if-false (∧-false R) (xval u₁ (ρ₀ x y) w) (ρ₀ x y (inj₂ (u₁ , w))))
    dflts₀ x y (inj₂ (u₂ , w)) R =
      sym (if-false (∧-false R) (xval u₂ (ρ₀ x y) w) (ρ₀ x y (inj₂ (u₂ , w))))
    dflts₀ x y (inj₂ (v₁ , w)) R =
      sym (if-false (∧-false R) (xval v₁ (ρ₀ x y) w) (ρ₀ x y (inj₂ (v₁ , w))))
    dflts₀ x y (inj₂ (v₂ , w)) R =
      sym (if-false (∧-false R) (xval v₂ (ρ₀ x y) w) (ρ₀ x y (inj₂ (v₂ , w))))

    find₀ : ∀ ℓ → Ret₀ ℓ ≡ true → Σ (Fin K) (λ p → lab₀ p ≡ ℓ)
    find₀ ℓ R = cast (sym eK) (posP ℓ R) ,
      trans (cong labR (Fin.cast-involutive eK (sym eK) (posP ℓ R)))
            (labR-posP ℓ R)

    only₀ : ∀ p → Ret₀ (lab₀ p) ≡ true
    only₀ p = Ret₀-labR (cast eK p)

    inj₀ : ∀ p q → lab₀ p ≡ lab₀ q → p ≡ q
    inj₀ p q e = Fin.toℕ-injective
      (trans (sym (at-toℕ p)) (trans (cong gpos e) (at-toℕ q)))

    -- The layers' bits are the labelled path's.

    nH : norm Hn ≡ n
    nH = norm-hadamards n

    nD : norm D ≡ 0
    nD = norm-oracle (f̃Terms gs)

    nOF : norm (O ++ F) ≡ nF s
    nOF = trans (norm-++ O F) (cong (_ℕ+ nF s) (norm-oracle (fTerms gs)))

    nX : norm X ≡ nF s ℕ+ nF s
    nX = trans (norm-++ F (O ++ F)) (cong (nF s ℕ+_) nOF)

    pY1 : ∀ st w → Y₁ᵗ st w ≡ st (g₁ w)
    pY1 st w = cong st (trans
      (cong₂ (λ a b → (((toℕ (opposite w) ℕ+ a) ℕ+ b) ℕ+ norm D) ℕ+ b) nX nH)
      (trans (cong (λ d → (((toℕ (opposite w) ℕ+ (nF s ℕ+ nF s)) ℕ+ n) ℕ+ d)
                          ℕ+ n)
                   nD)
        (solve 3 (λ t a f → (((t :+ (f :+ f)) :+ a) :+ con 0) :+ a :=
                            a :+ (a :+ (f :+ (f :+ t))))
               refl (toℕ (opposite w)) n (nF s))))

    pU : ∀ st w t → xbits s (sF st) t w ≡ st (n ℕ+ (n ℕ+ (nF s ℕ+ xrev s w t)))
    pU st w t = cong st (trans
      (cong₂ (λ a b → (((xrev s w t ℕ+ a) ℕ+ b) ℕ+ norm D) ℕ+ b) nOF nH)
      (trans (cong (λ d → (((xrev s w t ℕ+ nF s) ℕ+ n) ℕ+ d) ℕ+ n) nD)
        (solve 3 (λ x a f → (((x :+ f) :+ a) :+ con 0) :+ a :=
                            a :+ (a :+ (f :+ x)))
               refl (xrev s w t) n (nF s))))

    pV : ∀ st w t → xbits s (s₃ st) t w ≡ st (n ℕ+ (n ℕ+ xrev s w t))
    pV st w t = cong st (trans
      (cong₂ (λ d b → ((xrev s w t ℕ+ b) ℕ+ d) ℕ+ b) nD nH)
      (solve 2 (λ x a → ((x :+ a) :+ con 0) :+ a := a :+ (a :+ x))
             refl (xrev s w t) n))

    pY2 : ∀ st w → Y₂ᵗ st w ≡ st (g₂ w)
    pY2 st w = cong st (trans
      (cong₂ (λ d b → (toℕ (opposite w) ℕ+ d) ℕ+ b) nD nH)
      (solve 2 (λ t a → (t :+ con 0) :+ a := a :+ t) refl (toℕ (opposite w)) n))

    -- The parity is Fc of the labelled path.

    βF : ∀ x y →
         FcS (Y₁ᵗ (str y)) (xbits s (sF (str y)) true)
             (xbits s (sF (str y)) false) (xbits s (s₃ (str y)) true)
             (xbits s (s₃ (str y)) false) (Y₂ᵗ (str y)) (Y₃ᵗ (str y)) ≡
         Fc x (ρ₀ x y)
    βF x y = FcS-cong
      (λ w → trans (pY1 (str y) w) (cong (str y) (sym (gpos-wl₁ w))))
      (λ w → pU (str y) w true) (λ w → pU (str y) w false)
      (λ w → pV (str y) w true) (λ w → pV (str y) w false)
      (λ w → trans (pY2 (str y) w) (cong (str y) (sym (gpos-wl₂ w))))
      (λ w → cong (str y) (sym (gpos-wl₃ w)))

    -- The outputs are the third layer.

    Y₃-Gblk : ∀ x y w → Y₃ᵗ (str y) w ≡ Gblk w (λ ℓ → ρ₀ x y (inj₁ ℓ))
    Y₃-Gblk x y w = sym (split-inv m m
      (λ j → ρ₀ x y (inj₁ (E₃ , j))) (λ j → ρ₀ x y (inj₁ (H₃ , j)))
      (λ b → b) (Y₃ᵗ (str y)) (λ _ → refl) (λ _ → refl) w)

    tracks₀ : Tracksˣ ξA (λ x y → Fc x (ρ₀ x y)) (λ w x y → Gc w x (ρ₀ x y))
    tracks₀ = record { phase-atˣ = ph ; out-atˣ = ob }
      where
      ph : ∀ x y → pow M ∣ (eval (phase ξA) x y - ½ * [ Fc x (ρ₀ x y) ]ᶻ)
      ph x y = subst (pow M ∣_)
        (cong₂ _-_ (sym evalEq)
               (trans (+-identityˡ _) (cong (λ b → ½ * [ b ]ᶻ) (βF x y))))
        (runs-φ (runs-HS (str y)) 0ℤ)
        where
        evalEq : eval (phase ξA) x y ≡
                 proj₁ (trace (HSᶜ gs s) (str y) (0ℤ , 0ᵃ {n}))
        evalEq = trans (eval-at0 (phase ⟦ HSᶜ gs s ⟧) x y)
                       (eval-⟦⟧ (HSᶜ gs s) (0ᵃ {n}) y)

      ob : ∀ w x y → odd (eval (out ξA w) x y) ≡ Gc w x (ρ₀ x y)
      ob w x y = trans (cong odd (eval-at0 (out ⟦ HSᶜ gs s ⟧ w) x y))
        (trans (outBit-⟦⟧ (HSᶜ gs s) (0ᵃ {n}) y w)
          (trans (runs-v (runs-HS (str y)) 0ℤ w) (Y₃-Gblk x y w)))

    -- A labelled path-sum with these values, whose normalisation is its
    -- number of path variables, reduces completely.

    complete′ : ∀ {k K} (ξ : PathSum n k K) → k ≡ K →
                (lab : Fin K → CL) (ρ : Assign n → Assign K → CL → Bool) →
                Tracksˣ ξ (λ x y → Fc x (ρ x y)) (λ w x y → Gc w x (ρ x y)) →
                (∀ x y p → ρ x y (lab p) ≡ y p) →
                (∀ x y ℓ → Ret₀ ℓ ≡ false → ρ x y ℓ ≡ dfltc x ℓ (ρ x y)) →
                (∀ ℓ → Ret₀ ℓ ≡ true → Σ (Fin K) (λ p → lab p ≡ ℓ)) →
                (∀ p → Ret₀ (lab p) ≡ true) →
                (∀ p q → lab p ≡ lab q → p ≡ q) →
                Σ (PathSum n 0 0) (λ ζ → ξ ⟶ᶠ* ζ)
    complete′ {K = K} ξ refl lab ρ tr rd df fd on ij =
      XPasses.complete-X ξ (CircuitPasses.stage K ξ lab ρ εᶠ tr rd df fd on ij)

  ----------------------------------------------------------------------
  -- The theorems

  -- Figure 3(a)'s path-sum on |0⟩ reduces by figure 2's rules to one
  -- with no path variables ...

  circuit-exists :
    Σ (PathSum (m ℕ+ m) 0 0) (λ ζ → at0 ⟦ HSᶜ gs s ⟧ ⟶ᶠ* ζ)
  circuit-exists = complete′ ξA (sym (paths≡norm (HSᶜ gs s))) lab₀ ρ₀ tracks₀
                             reads₀ dflts₀ find₀ only₀ inj₀

  -- ... and that one is |x⟩ ↦ |s⟩, coefficient by coefficient: the
  -- calculus finds the hidden shift on the circuit itself.

  circuit-finds :
    Σ (PathSum (m ℕ+ m) 0 0) (λ ζ →
      (at0 ⟦ HSᶜ gs s ⟧ ⟶ᶠ* ζ) ×
      (∀ w → out ζ w ≈[ + 2 ] κ [ s w ]ᶻ) ×
      (phase ζ ≈[ pow M ] 0ᴾ))
  circuit-finds =
    proj₁ circuit-exists , proj₂ circuit-exists ,
    proj₂ (circuit-reduces gs s (proj₂ circuit-exists))
