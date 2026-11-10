------------------------------------------------------------------------
-- Presentations of groups
--
-- Derivations in the circuits' theory: what the Reidemeister–Schreier
-- step from Lafont's presentation of 𝔄₁₆ needs of the rules of
-- Syntactics
--
-- Two facts about the translation g of Lafont's cycles into circuits,
-- the two hypotheses of the step in that direction (Iso):
--
-- * lemma-g-rel: every instance of Lafont's relation, read through g,
--   is a rule of Syntactics.  His relations order, near and far at the
--   cycles d points up are the rules order d, near d and far d, and
--   his commutation of the cycle with a generator three or more points
--   further up is the rule apart.  An instance one point up is the
--   same instance read one point further up (gᵈ-↑), so the statement
--   is about gᵈ d for every d, by recursion on the instance.
--
-- * lemma-g-f: every gate is the circuit of its word in the cycles.
--   For the six gates on their own wires that is one of the rules
--   gate-X, …, gate-Ex₂.  A gate further up is that gate between swaps
--   (lemma-X↑, lemma-CX↑, lemma-CCX↑, from the naturality of the swap),
--   and Translation.f was defined to follow: its word is the word of
--   the gate between the words of the swaps.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Alt16-RevCir.Lemmas where

open import Data.Nat using (ℕ ; suc ; _+_ ; _≤_ ; s≤s⁻¹)
open import Data.Nat.Properties
  using (+-suc ; +-cancelˡ-≤ ; m+n≤o⇒m≤o ; n≤1+n ; ≤-refl ; ≤-reflexive
        ; ≤-trans)
open import Data.Product using (∃ ; _×_ ; _,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations using (₂₊ ; ₃₊ ; ₄₊)
open import Presentation.Base as PB
  using (refl ; sym ; trans ; cong ; assoc ; left-unit ; axiom)
open import Word.Base using ([_]ʷ ; ε ; _•_ ; _ʷ)

import Examples.Groups.Alternating.Syntactics as L

open import Examples.Groups.Alt16-RevCir.Syntactics
open import Examples.Groups.Alt16-RevCir.Translation

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Reading a shifted word

-- A word one point up, read d points up, is the word read d + 1 points
-- up.
gᵈ-↑ : (d : ℕ) (w : L.Circuit n) → (gᵈ d ʷ) (w L.↑) ≡ (gᵈ (suc d) ʷ) w
gᵈ-↑ d [ y ]ʷ  = Eq.refl
gᵈ-↑ d ε       = Eq.refl
gᵈ-↑ d (w • v) = Eq.cong₂ _•_ (gᵈ-↑ d w) (gᵈ-↑ d v)

------------------------------------------------------------------------
-- Positions
--
-- A generator of Lafont's on k points, read d points up, is a cycle
-- among sixteen points when d + k is 16.

private

  -- The same sixteen points, counted from one point further up, and
  -- from three.
  up : ∀ d {k} → d + suc k ≡ 16 → suc d + k ≡ 16
  up d {k} = Eq.trans (Eq.sym (+-suc d k))

  up₃ : ∀ d {k} → d + ₃₊ k ≡ 16 → ₃₊ d + k ≡ 16
  up₃ d eq = up (₂₊ d) (up (suc d) (up d eq))

  -- A cycle d points up, with m points above it, is at most Ω 13.
  top : ∀ d {m} → d + ₃₊ m ≡ 16 → d ≤ 13
  top d eq = +-cancelˡ-≤ 3 _ _ (m+n≤o⇒m≤o _ (≤-reflexive (up₃ d eq)))

  -- The circuits Ω j with c ≤ j.
  Above : ℕ → Circuit 4 → Set
  Above c w = ∃ λ j → w ≡ Ω j × c ≤ j × j ≤ 13

  -- A generator read c points up is one of them.
  gᵈ-above : ∀ {k} (c : ℕ) (y : L.Gen k) → c + k ≡ 16 →
             Above c (gᵈ c y)
  gᵈ-above c L.ω-gen eq = c , Eq.refl , ≤-refl , top c eq
  gᵈ-above c (y L.↥) eq =
    let (j , e , c<j , j≤13) = gᵈ-above (suc c) y (up c eq)
    in j , e , ≤-trans (n≤1+n c) c<j , j≤13
    -- c<j : suc c ≤ j

  -- Ω d commutes with the cycles three or more points further up.
  lemma-apart : ∀ d {w} → Above (₃₊ d) w → 4 ⊢ w • Ω d ≈ Ω d • w
  lemma-apart d (j , Eq.refl , d+3≤j , j≤13) =
    axiom (srel (srel (apart d j d+3≤j j≤13)))

------------------------------------------------------------------------
-- Lafont's relations, read through g

-- Every instance of Lafont's relation, read through g at any shift, is
-- a rule of Syntactics.
lemma-g-rel : ∀ {n} (d : ℕ) → d + n ≡ 16 → {u t : L.Circuit n} →
              L._VRel,_===_ n u t → 4 ⊢ (gᵈ d ʷ) u ≈ (gᵈ d ʷ) t
lemma-g-rel d eq (L.srel L.order) =
  axiom (srel (srel (order d (top d eq))))
lemma-g-rel d eq (L.srel L.near) =
  axiom (srel (srel (near d (s≤s⁻¹ (top (suc d) (up d eq))))))
lemma-g-rel d eq (L.srel L.far) =
  axiom (srel (srel (far d (s≤s⁻¹ (s≤s⁻¹ (top (₂₊ d) eq₂))))))
  where eq₂ = up (suc d) (up d eq)
lemma-g-rel d eq (L.cong↑ {w = w} {v = v} p) =
  trans (refl' (gᵈ-↑ d w))
  (trans (lemma-g-rel (suc d) (up d eq) p)
         (refl' (Eq.sym (gᵈ-↑ d v))))
  where open PB (4 VRel,_===_) using (refl')
lemma-g-rel d eq (L.comm₃ L.ω-gate y) =
  lemma-apart d (gᵈ-above (₃₊ d) y (up₃ d eq))

------------------------------------------------------------------------
-- A gate one wire up, between swaps

private
  -- If a followed by s is s followed by b, and s⁻ undoes s, then b is
  -- a between s⁻ and s.
  conjugate : ∀ {a b s s⁻ : Circuit n} → n ⊢ s⁻ • s ≈ ε →
              n ⊢ a • s ≈ s • b → n ⊢ b ≈ s⁻ • a • s
  conjugate inv nat =
    trans (sym left-unit)
    (trans (cong (sym inv) refl)
    (trans assoc (cong refl (sym nat))))

lemma-X↑ : ∀ {n} → (₂₊ n) ⊢ X ↑ ≈ Ex • X • Ex
lemma-X↑ = conjugate σ-invol (sym-rule (σ-nat₁ X-gate))

lemma-CX↑ : ∀ {n} → (₃₊ n) ⊢ CX ↑ ≈ σ⁻[ 2 ] • CX • σ[ 2 ]
lemma-CX↑ = conjugate (σ⁻σ 2) (sym-rule (σ-nat₂ CX-gate))

lemma-CCX↑ : ∀ {n} → (₄₊ n) ⊢ CCX ↑ ≈ σ⁻[ 3 ] • CCX • σ[ 3 ]
lemma-CCX↑ = conjugate (σ⁻σ 3) (sym-rule (σ-nat₃ CCX-gate))

------------------------------------------------------------------------
-- The gates, read through f and back through g

private

  -- The gates on their own wires: the rules that name their words.
  x₀ : 4 ⊢ X₀ ≈ (g ʷ) fX
  x₀ = axiom (srel (srel gate-X))

  cx₀ : 4 ⊢ CX ≈ (g ʷ) fCX
  cx₀ = axiom (srel (srel gate-CX))

  ccx₀ : 4 ⊢ CCX ≈ (g ʷ) fCCX
  ccx₀ = axiom (srel (srel gate-CCX))

  ex₀ : 4 ⊢ Ex₀ ≈ (g ʷ) fEx₀
  ex₀ = axiom (srel (srel gate-Ex₀))

  ex₁ : 4 ⊢ Ex₁ ≈ (g ʷ) fEx₁
  ex₁ = axiom (srel (srel gate-Ex₁))

  ex₂ : 4 ⊢ Ex₂ ≈ (g ʷ) fEx₂
  ex₂ = axiom (srel (srel gate-Ex₂))

  -- NOT further up: between the swaps below it, one wire at a time.
  x₁ : 4 ⊢ X₁ ≈ (g ʷ) fX₁
  x₁ = trans lemma-X↑ (cong ex₀ (cong x₀ ex₀))

  x₂ : 4 ⊢ X₂ ≈ (g ʷ) fX₂
  x₂ = trans (lemma-cong↑ _ _ lemma-X↑) (cong ex₁ (cong x₁ ex₁))

  x₃ : 4 ⊢ X₃ ≈ (g ʷ) fX₃
  x₃ = trans (lemma-cong↑ _ _ (lemma-cong↑ _ _ lemma-X↑))
             (cong ex₂ (cong x₂ ex₂))

  -- CX and CCX further up: between the cycles of swaps.
  cx₁ : 4 ⊢ CX ↑ ≈ (g ʷ) fCX₁
  cx₁ = trans lemma-CX↑ (cong (cong ex₀ ex₁) (cong cx₀ (cong ex₁ ex₀)))

  cx₂ : 4 ⊢ CX ↑ ↑ ≈ (g ʷ) fCX₂
  cx₂ = trans (lemma-cong↑ _ _ lemma-CX↑)
              (cong (cong ex₁ ex₂) (cong cx₁ (cong ex₂ ex₁)))

  ccx₁ : 4 ⊢ CCX ↑ ≈ (g ʷ) fCCX₁
  ccx₁ = trans lemma-CCX↑
               (cong (cong ex₀ (cong ex₁ ex₂))
                     (cong ccx₀ (cong (cong ex₂ ex₁) ex₀)))

-- Each gate is the circuit of its word in the cycles.
lemma-g-f : (x : Gen 4) → 4 ⊢ [ x ]ʷ ≈ (g ʷ) (f x)
lemma-g-f X-gen             = x₀
lemma-g-f CX-gen            = cx₀
lemma-g-f Ex-gen            = ex₀
lemma-g-f CCX-gen           = ccx₀
lemma-g-f (X-gen ↥)         = x₁
lemma-g-f (CX-gen ↥)        = cx₁
lemma-g-f (Ex-gen ↥)        = ex₁
lemma-g-f (CCX-gen ↥)       = ccx₁
lemma-g-f (X-gen ↥ ↥)       = x₂
lemma-g-f (CX-gen ↥ ↥)      = cx₂
lemma-g-f (Ex-gen ↥ ↥)      = ex₂
lemma-g-f (X-gen ↥ ↥ ↥)     = x₃
lemma-g-f (gate₀ ())
lemma-g-f (gate₀ () ↥)
lemma-g-f (gate₀ () ↥ ↥)
lemma-g-f (gate₀ () ↥ ↥ ↥)
lemma-g-f (gate₀ () ↥ ↥ ↥ ↥)
