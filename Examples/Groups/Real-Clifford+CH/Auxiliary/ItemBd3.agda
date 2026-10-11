------------------------------------------------------------------------
-- Presentations of groups
--
-- Item (b) for Figure 7's (d3*)
--
-- Through the frame with e, f, g = 7, 6, 4, the image of (d3*) is
-- Figure 8's (45) conjugated by the exchange of 2 and 3: the Hadamard
-- pairs H_[0,2] H_[1,3] of (d3*) are H_[0,3] H_[1,2] of (45) renamed,
-- the frame's pair is (45)'s H_[7,6], and the two signs on 0 and 1 are
-- its sign pair once the sink's two signs cancel.  Each side is one
-- call of the frame normaliser (`by-norm`) against the corresponding
-- side of (45), checked in Python first (`scratchpad/tN.py`).
--
-- The obligation is proved over index variables with the numerals'
-- values as hypotheses (`core`), both because the transported literals
-- `subst Fin e k` are what the rule gives and because variables keep
-- the conversion checker away from `Gray.fin8`.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.ItemBd3 (m : ℕ) where

open import Data.Fin using (Fin ; toℕ)
open import Data.Fin.Properties using (toℕ-inject≤)
open import Data.Nat using () renaming (_^_ to _^ℕ_)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Data.Vec using ([] ; _∷_)
open import Data.Vec.Relation.Unary.All using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₆ ; ₇ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Cosets
  using (Coset ; ⟨ε⟩ ; ⟨M⟩ ; ⟨K⟩ ; ⟨KM⟩)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8 using (_P,_===_ ; r45)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (fin8)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.RS m using (z₀ ; o₁ ; z₀≢o₁)
open import Examples.Groups.Real-Clifford+CH.Encoding using (hh ; zz ; zx ; hhℕ ; zzℕ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.LowGens m using (hhℕ-hh)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.DE m using (zzℕ-zz)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Template m
  using (Distinct ; []ᵈ ; _∷ᵈ_ ; tz ; ty)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure10 m using (Eq65)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Frame m using (module Frame ; cos)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.ItemB m using (Obl ; D3)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)

import Examples.Groups.Real-Clifford+CH.Auxiliary.Syntactics as G

open Tools (m P,_===_)

private
  N : ℕ
  N = 2 ^ℕ (₃₊ m)

  f4 f6 f7 : Fin N
  f4 = fin8 {m} ₄
  f6 = fin8 {m} ₆
  f7 = fin8 {m} ₇

  t4 : toℕ f4 ≡ 4
  t4 = toℕ-inject≤ ₄ _

  t6 : toℕ f6 ≡ 6
  t6 = toℕ-inject≤ ₆ _

  t7 : toℕ f7 ≡ 7
  t7 = toℕ-inject≤ ₇ _

  tz₀ : toℕ z₀ ≡ 0
  tz₀ = toℕ-inject≤ ₀ _

  to₁ : toℕ o₁ ≡ 1
  to₁ = toℕ-inject≤ ₁ _

  -- Indices with different numerals differ.
  apart : ∀ {x y : Fin N} {k l : ℕ} → toℕ x ≡ k → toℕ y ≡ l → k ≢ l → x ≢ y
  apart t₁ t₂ ne h = ne (Eq.trans (Eq.sym t₁) (Eq.trans (Eq.cong toℕ h) t₂))

  toℕ-subst : ∀ {K : ℕ} (e : K ≡ N) (i : Fin K) → toℕ (Eq.subst Fin e i) ≡ toℕ i
  toℕ-subst Eq.refl i = Eq.refl

-- The two sides of (d3*) at four indices.
d3L d3R : Fin N → Fin N → Fin N → Fin N → Word (G.Gen N)
d3L a b x d = G.H a b • G.H a x • G.H b d • G.H a b • G.−1 a • G.−1 b • G.H a x • G.H b d
d3R a b x d = G.H a x • G.H b d • G.H a b • G.−1 a • G.−1 b • G.H a x • G.H b d • G.H a b

module _ (e65 : Eq65) where

  core : ∀ (c : Coset) (a b x d : Fin N) →
         toℕ a ≡ 0 → toℕ b ≡ 1 → toℕ x ≡ 2 → toℕ d ≡ 3 →
         Obl c (d3L a b x d) (d3R a b x d)
  core c a b x d ta tb tx td =
    F.by-frame c (d3L a b x d) (d3R a b x d) avL avR ndL ndR (cs c) img
    where
    ne : ∀ {k l : ℕ} {p q : Fin N} → toℕ p ≡ k → toℕ q ≡ l → k ≢ l → p ≢ q
    ne = apart

    module F = Frame e65 z₀ o₁ z₀≢o₁ f7 f6 f4
                 (ne t7 t6 (λ ())) (ne t7 t4 (λ ())) (ne t6 t4 (λ ()))
                 (ne t7 tz₀ (λ ())) (ne t7 to₁ (λ ())) (ne t6 tz₀ (λ ())) (ne t6 to₁ (λ ()))
                 (ne t4 tz₀ (λ ())) (ne t4 to₁ (λ ()))

    av : ∀ {p : Fin N} {k : ℕ} → toℕ p ≡ k → k ≢ 7 → k ≢ 6 → k ≢ 4 → F.Av p
    av tp n7 n6 n4 = ne tp t7 n7 , ne tp t6 n6 , ne tp t4 n4

    va vb vx vd : _
    va = av ta (λ ()) (λ ()) (λ ())
    vb = av tb (λ ()) (λ ()) (λ ())
    vx = av tx (λ ()) (λ ()) (λ ())
    vd = av td (λ ()) (λ ()) (λ ())

    ab : a ≢ b
    ab = ne ta tb (λ ())

    ax : a ≢ x
    ax = ne ta tx (λ ())

    bd : b ≢ d
    bd = ne tb td (λ ())

    avL : F.AvoidsW (d3L a b x d)
    avL = (va , vb) , (va , vx) , (vb , vd) , (va , vb) , va , vb , (va , vx) , (vb , vd)

    avR : F.AvoidsW (d3R a b x d)
    avR = (va , vx) , (vb , vd) , (va , vb) , va , vb , (va , vx) , (vb , vd) , (va , vb)

    ndL : F.NonDegW (d3L a b x d)
    ndL = ab , ax , bd , ab , tt , tt , ax , bd

    ndR : F.NonDegW (d3R a b x d)
    ndR = ax , bd , ab , tt , tt , ax , bd , ab

    cs : ∀ (c : Coset) → cos c (d3L a b x d) ≡ cos c (d3R a b x d)
    cs ⟨ε⟩  = Eq.refl
    cs ⟨M⟩  = Eq.refl
    cs ⟨K⟩  = Eq.refl
    cs ⟨KM⟩ = Eq.refl

    ad : a ≢ d
    ad = ne ta td (λ ())

    -- (45), its numerals renamed to the indices at hand.
    X R45L R45R : Word (GenP (₃₊ m))
    X    = zx {₃₊ m} f4 x d
    R45L = hh {₃₊ m} a b f7 f6 • hh {₃₊ m} a d b x • hh {₃₊ m} a b f7 f6 •
           zz {₃₊ m} a b • hh {₃₊ m} a d b x
    R45R = hh {₃₊ m} a d b x • zz {₃₊ m} a b • hh {₃₊ m} a b f7 f6 •
           hh {₃₊ m} a d b x • hh {₃₊ m} a b f7 f6

    h0176 : hhℕ {₃₊ m} 0 1 7 6 ≡ hh {₃₊ m} a b f7 f6
    h0176 = Eq.trans (Eq.cong₂ (λ p q → hhℕ {₃₊ m} p q 7 6) (Eq.sym ta) (Eq.sym tb))
              (Eq.trans (Eq.cong₂ (λ p q → hhℕ {₃₊ m} (toℕ a) (toℕ b) p q) (Eq.sym t7) (Eq.sym t6))
                        (hhℕ-hh a b f7 f6))

    h0312 : hhℕ {₃₊ m} 0 3 1 2 ≡ hh {₃₊ m} a d b x
    h0312 = Eq.trans (Eq.cong₂ (λ p q → hhℕ {₃₊ m} p q 1 2) (Eq.sym ta) (Eq.sym td))
              (Eq.trans (Eq.cong₂ (λ p q → hhℕ {₃₊ m} (toℕ a) (toℕ d) p q) (Eq.sym tb) (Eq.sym tx))
                        (hhℕ-hh a d b x))

    z01 : zzℕ {₃₊ m} 0 1 ≡ zz {₃₊ m} a b
    z01 = Eq.trans (Eq.cong₂ (zzℕ {₃₊ m}) (Eq.sym ta) (Eq.sym tb)) (zzℕ-zz a b)

    e45 : R45L ≈ R45R
    e45 = Eq.subst₂ (λ L R → L ≈ R)
            (Eq.cong₂ _•_ h0176 (Eq.cong₂ _•_ h0312 (Eq.cong₂ _•_ h0176 (Eq.cong₂ _•_ z01 h0312))))
            (Eq.cong₂ _•_ h0312 (Eq.cong₂ _•_ z01 (Eq.cong₂ _•_ h0176 (Eq.cong₂ _•_ h0312 h0176))))
            (axiom r45)

    open F.NV (a ∷ b ∷ x ∷ d ∷ f4 ∷ [])
              ((ne tb ta (λ ()) ∷ ne tx ta (λ ()) ∷ ne td ta (λ ()) ∷ ne t4 ta (λ ()) ∷ []) ∷ᵈ
               (ne tx tb (λ ()) ∷ ne td tb (λ ()) ∷ ne t4 tb (λ ()) ∷ []) ∷ᵈ
               (ne td tx (λ ()) ∷ ne t4 tx (λ ()) ∷ []) ∷ᵈ
               (ne t4 td (λ ()) ∷ []) ∷ᵈ [] ∷ᵈ []ᵈ)
              (ne ta t7 (λ ()) ∷ ne tb t7 (λ ()) ∷ ne tx t7 (λ ()) ∷ ne td t7 (λ ()) ∷
               ne t4 t7 (λ ()) ∷ [])
              (ne ta t6 (λ ()) ∷ ne tb t6 (λ ()) ∷ ne tx t6 (λ ()) ∷ ne td t6 (λ ()) ∷
               ne t4 t6 (λ ()) ∷ [])

    r45L r45R : FW
    r45L = ⌞ hl ₀ ₁ ⌟ •ᶠ ⌞ hp ₀ ₃ ₁ ₂ ⌟ •ᶠ ⌞ hl ₀ ₁ ⌟ •ᶠ ⌞ hf (tz ₀ ₁) ⌟ •ᶠ ⌞ hp ₀ ₃ ₁ ₂ ⌟
    r45R = ⌞ hp ₀ ₃ ₁ ₂ ⌟ •ᶠ ⌞ hf (tz ₀ ₁) ⌟ •ᶠ ⌞ hl ₀ ₁ ⌟ •ᶠ ⌞ hp ₀ ₃ ₁ ₂ ⌟ •ᶠ ⌞ hl ₀ ₁ ⌟

    φL φR : FW
    φL = ⌞ hl ₀ ₁ ⌟ •ᶠ ⌞ hl ₀ ₂ ⌟ •ᶠ ⌞ hl ₁ ₃ ⌟ •ᶠ ⌞ hl ₀ ₁ ⌟ •ᶠ ⌞ hf (tz ₀ ₄) ⌟ •ᶠ
         ⌞ hf (tz ₁ ₄) ⌟ •ᶠ ⌞ hl ₀ ₂ ⌟ •ᶠ ⌞ hl ₁ ₃ ⌟
    φR = ⌞ hl ₀ ₂ ⌟ •ᶠ ⌞ hl ₁ ₃ ⌟ •ᶠ ⌞ hl ₀ ₁ ⌟ •ᶠ ⌞ hf (tz ₀ ₄) ⌟ •ᶠ ⌞ hf (tz ₁ ₄) ⌟ •ᶠ
         ⌞ hl ₀ ₂ ⌟ •ᶠ ⌞ hl ₁ ₃ ⌟ •ᶠ ⌞ hl ₀ ₁ ⌟

    ξ : FW
    ξ = ⌞ hf (ty ₄ ₂ ₃) ⌟

    img : F.Φʷ (d3L a b x d) ≈ F.Φʷ (d3R a b x d)
    img = trans (by-norm φL (ξ •ᶠ r45L •ᶠ ξ) Eq.refl Eq.refl)
          (trans (back X (front X e45))
                 (by-norm (ξ •ᶠ r45R •ᶠ ξ) φR Eq.refl Eq.refl))

  -- (d3*), at the literals carried to N.
  d3 : D3 e65
  d3 e c = core c (Eq.subst Fin e ₀) (Eq.subst Fin e ₁) (Eq.subst Fin e ₂) (Eq.subst Fin e ₃)
                  (toℕ-subst e ₀) (toℕ-subst e ₁) (toℕ-subst e ₂) (toℕ-subst e ₃)
