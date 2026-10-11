------------------------------------------------------------------------
-- Presentations of groups
--
-- Item (b) for Figure 7's (d4*)
--
-- (d4*) has six indices, and on three qubits that leaves two: room for
-- a frame pair but not for a sink as well.  So the frame pair is 6, 7
-- and the sink is the rule's own index 2, which `Frame.by-frameAt`
-- allows when every Hadamard is read at ⟨ε⟩ or ⟨K⟩ — as it is when the
-- word starts at one of those, the two signs of (d4*) being adjacent.
-- Through that frame the image of (d4*) is Figure 11's (80), each side
-- one normaliser call away (`by-norm`, checked in Python first,
-- `scratchpad/tN.py`), and (80) is `Eq80.eq80`, from Figure 8's (46).
-- At ⟨M⟩ and ⟨KM⟩ the obligation is the one at ⟨ε⟩ and ⟨K⟩ conjugated
-- by a sign on the index 6 (`SignSym.obl-M`).
--
-- As for (d3*), the obligation is proved over index variables with the
-- numerals' values as hypotheses (`C.core`), (80) being carried from
-- the literals to them by matching on their equality (`e80`).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.ItemBd4 (m : ℕ) where

open import Data.Fin using (Fin ; toℕ)
open import Data.Fin.Properties using (toℕ-injective ; toℕ-inject≤)
open import Data.Nat using () renaming (_^_ to _^ℕ_)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Data.Vec using ([] ; _∷_)
open import Data.Vec.Relation.Unary.All using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; _•_)

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₅ ; ₆ ; ₇ ; ₃₊)

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Cosets
  using (Coset ; ⟨ε⟩ ; ⟨M⟩ ; ⟨K⟩ ; ⟨KM⟩)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8 using (_P,_===_)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (fin8)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.RS m using (z₀ ; o₁ ; z₀≢o₁)
open import Examples.Groups.Real-Clifford+CH.Encoding using (hh ; zz)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Template m using ([]ᵈ ; _∷ᵈ_ ; tz)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure10 m using (Eq65)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Frame m using (module Frame)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.ItemB m using (Obl ; D4)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SignSym m using (AvSW ; obl-M)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Eq80 m using (lit ; eq80)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)

import Examples.Groups.Real-Clifford+CH.Auxiliary.Syntactics as G

open Tools (m P,_===_)

private
  N : ℕ
  N = 2 ^ℕ (₃₊ m)

  W : Set
  W = Word (GenP (₃₊ m))

  f6 f7 : Fin N
  f6 = fin8 {m} ₆
  f7 = fin8 {m} ₇

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

  -- An index with the numeral of a literal is that literal.
  is-lit : ∀ {x : Fin N} (k : Fin 8) → toℕ x ≡ toℕ k → x ≡ lit k
  is-lit k h = toℕ-injective (Eq.trans h (Eq.sym (toℕ-inject≤ k _)))

  -- The two cosets from which every Hadamard of (d4*) is read at ⟨ε⟩
  -- or ⟨K⟩.
  data EK : Coset → Set where
    ek-ε : EK ⟨ε⟩
    ek-K : EK ⟨K⟩

-- The two sides of (d4*) at six indices.
d4L d4R : Fin N → Fin N → Fin N → Fin N → Fin N → Fin N → Word (G.Gen N)
d4L a b x d y w = G.H a b • G.H a x • G.H b d • G.H a y • G.H b w • G.H a b • G.−1 a • G.−1 b •
                  G.H a y • G.H b w • G.H a x • G.H b d
d4R a b x d y w = G.H a x • G.H b d • G.H a y • G.H b w • G.H a b • G.−1 a • G.−1 b •
                  G.H a y • G.H b w • G.H a x • G.H b d • G.H a b

-- The two sides of (80) at six indices.
L80w R80w : Fin N → Fin N → Fin N → Fin N → Fin N → Fin N → W
L80w a b x d y w = hh {₃₊ m} a b a x • hh {₃₊ m} b d a y • hh {₃₊ m} b w a b • zz {₃₊ m} b a •
                   hh {₃₊ m} a y b w • hh {₃₊ m} a x b d
R80w a b x d y w = hh {₃₊ m} a x b d • hh {₃₊ m} a y b w • zz {₃₊ m} b a • hh {₃₊ m} a b a y •
                   hh {₃₊ m} b w a x • hh {₃₊ m} b d a b

module _ (e65 : Eq65) where

  e80 : ∀ (a b x d y w : Fin N) → a ≡ lit ₀ → b ≡ lit ₁ → x ≡ lit ₂ → d ≡ lit ₃ →
        y ≡ lit ₄ → w ≡ lit ₅ → L80w a b x d y w ≈ R80w a b x d y w
  e80 ._ ._ ._ ._ ._ ._ Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl Eq.refl = eq80 e65

  private
    module C (a b x d y w : Fin N) (h₀ : toℕ a ≡ 0) (h₁ : toℕ b ≡ 1) (h₂ : toℕ x ≡ 2)
             (h₃ : toℕ d ≡ 3) (h₄ : toℕ y ≡ 4) (h₅ : toℕ w ≡ 5) where

      L R : Word (G.Gen N)
      L = d4L a b x d y w
      R = d4R a b x d y w

      -- The frame pair 6, 7, with the rule's index 2 as the sink.
      module F = Frame e65 z₀ o₁ z₀≢o₁ f6 f7 x
                   (apart t6 t7 (λ ())) (apart t6 h₂ (λ ())) (apart t7 h₂ (λ ()))
                   (apart t6 tz₀ (λ ())) (apart t6 to₁ (λ ()))
                   (apart t7 tz₀ (λ ())) (apart t7 to₁ (λ ()))
                   (apart h₂ tz₀ (λ ())) (apart h₂ to₁ (λ ()))

      hv : ∀ {p : Fin N} {k : ℕ} → toℕ p ≡ k → k ≢ 6 → k ≢ 7 → F.AvH p
      hv tp n6 n7 = apart tp t6 n6 , apart tp t7 n7

      hA hB hX hD hY hW : _
      hA = hv {a} h₀ (λ ()) (λ ())
      hB = hv {b} h₁ (λ ()) (λ ())
      hX = hv {x} h₂ (λ ()) (λ ())
      hD = hv {d} h₃ (λ ()) (λ ())
      hY = hv {y} h₄ (λ ()) (λ ())
      hW = hv {w} h₅ (λ ()) (λ ())

      vA : F.Av a
      vA = apart h₀ t6 (λ ()) , apart h₀ t7 (λ ()) , apart h₀ h₂ (λ ())

      vB : F.Av b
      vB = apart h₁ t6 (λ ()) , apart h₁ t7 (λ ()) , apart h₁ h₂ (λ ())

      avL : ∀ {c : Coset} → EK c → F.AvRun c L
      avL ek-ε = (hA , hB) , (hA , hX) , (hB , hD) , (hA , hY) , (hB , hW) , (hA , hB) , vA , vB ,
                 (hA , hY) , (hB , hW) , (hA , hX) , (hB , hD)
      avL ek-K = (hA , hB) , (hA , hX) , (hB , hD) , (hA , hY) , (hB , hW) , (hA , hB) , vA , vB ,
                 (hA , hY) , (hB , hW) , (hA , hX) , (hB , hD)

      avR : ∀ {c : Coset} → EK c → F.AvRun c R
      avR ek-ε = (hA , hX) , (hB , hD) , (hA , hY) , (hB , hW) , (hA , hB) , vA , vB ,
                 (hA , hY) , (hB , hW) , (hA , hX) , (hB , hD) , (hA , hB)
      avR ek-K = (hA , hX) , (hB , hD) , (hA , hY) , (hB , hW) , (hA , hB) , vA , vB ,
                 (hA , hY) , (hB , hW) , (hA , hX) , (hB , hD) , (hA , hB)

      ab : a ≢ b
      ab = apart h₀ h₁ (λ ())

      ax : a ≢ x
      ax = apart h₀ h₂ (λ ())

      ay : a ≢ y
      ay = apart h₀ h₄ (λ ())

      bd : b ≢ d
      bd = apart h₁ h₃ (λ ())

      bw : b ≢ w
      bw = apart h₁ h₅ (λ ())

      ndL : F.NonDegW L
      ndL = ab , ax , bd , ay , bw , ab , tt , tt , ay , bw , ax , bd

      ndR : F.NonDegW R
      ndR = ax , bd , ay , bw , ab , tt , tt , ay , bw , ax , bd , ab

      open F.NV (a ∷ b ∷ x ∷ d ∷ y ∷ w ∷ [])
                ((apart h₁ h₀ (λ ()) ∷ apart h₂ h₀ (λ ()) ∷ apart h₃ h₀ (λ ()) ∷
                  apart h₄ h₀ (λ ()) ∷ apart h₅ h₀ (λ ()) ∷ []) ∷ᵈ
                 (apart h₂ h₁ (λ ()) ∷ apart h₃ h₁ (λ ()) ∷ apart h₄ h₁ (λ ()) ∷
                  apart h₅ h₁ (λ ()) ∷ []) ∷ᵈ
                 (apart h₃ h₂ (λ ()) ∷ apart h₄ h₂ (λ ()) ∷ apart h₅ h₂ (λ ()) ∷ []) ∷ᵈ
                 (apart h₄ h₃ (λ ()) ∷ apart h₅ h₃ (λ ()) ∷ []) ∷ᵈ
                 (apart h₅ h₄ (λ ()) ∷ []) ∷ᵈ [] ∷ᵈ []ᵈ)
                (apart h₀ t6 (λ ()) ∷ apart h₁ t6 (λ ()) ∷ apart h₂ t6 (λ ()) ∷
                 apart h₃ t6 (λ ()) ∷ apart h₄ t6 (λ ()) ∷ apart h₅ t6 (λ ()) ∷ [])
                (apart h₀ t7 (λ ()) ∷ apart h₁ t7 (λ ()) ∷ apart h₂ t7 (λ ()) ∷
                 apart h₃ t7 (λ ()) ∷ apart h₄ t7 (λ ()) ∷ apart h₅ t7 (λ ()) ∷ [])

      φL φR L80ᶠ R80ᶠ : FW
      φL = ⌞ hl ₀ ₁ ⌟ •ᶠ ⌞ hl ₀ ₂ ⌟ •ᶠ ⌞ hl ₁ ₃ ⌟ •ᶠ ⌞ hl ₀ ₄ ⌟ •ᶠ ⌞ hl ₁ ₅ ⌟ •ᶠ ⌞ hl ₀ ₁ ⌟ •ᶠ
           ⌞ hf (tz ₀ ₂) ⌟ •ᶠ ⌞ hf (tz ₁ ₂) ⌟ •ᶠ
           ⌞ hl ₀ ₄ ⌟ •ᶠ ⌞ hl ₁ ₅ ⌟ •ᶠ ⌞ hl ₀ ₂ ⌟ •ᶠ ⌞ hl ₁ ₃ ⌟
      φR = ⌞ hl ₀ ₂ ⌟ •ᶠ ⌞ hl ₁ ₃ ⌟ •ᶠ ⌞ hl ₀ ₄ ⌟ •ᶠ ⌞ hl ₁ ₅ ⌟ •ᶠ ⌞ hl ₀ ₁ ⌟ •ᶠ
           ⌞ hf (tz ₀ ₂) ⌟ •ᶠ ⌞ hf (tz ₁ ₂) ⌟ •ᶠ
           ⌞ hl ₀ ₄ ⌟ •ᶠ ⌞ hl ₁ ₅ ⌟ •ᶠ ⌞ hl ₀ ₂ ⌟ •ᶠ ⌞ hl ₁ ₃ ⌟ •ᶠ ⌞ hl ₀ ₁ ⌟
      L80ᶠ = ⌞ hp ₀ ₁ ₀ ₂ ⌟ •ᶠ ⌞ hp ₁ ₃ ₀ ₄ ⌟ •ᶠ ⌞ hp ₁ ₅ ₀ ₁ ⌟ •ᶠ ⌞ hf (tz ₁ ₀) ⌟ •ᶠ
             ⌞ hp ₀ ₄ ₁ ₅ ⌟ •ᶠ ⌞ hp ₀ ₂ ₁ ₃ ⌟
      R80ᶠ = ⌞ hp ₀ ₂ ₁ ₃ ⌟ •ᶠ ⌞ hp ₀ ₄ ₁ ₅ ⌟ •ᶠ ⌞ hf (tz ₁ ₀) ⌟ •ᶠ ⌞ hp ₀ ₁ ₀ ₄ ⌟ •ᶠ
             ⌞ hp ₁ ₅ ₀ ₂ ⌟ •ᶠ ⌞ hp ₁ ₃ ₀ ₁ ⌟

      -- The image of (d4*) is (80).
      img : F.Φʷ L ≈ F.Φʷ R
      img = trans (by-norm φL L80ᶠ Eq.refl Eq.refl)
            (trans (e80 a b x d y w (is-lit ₀ h₀) (is-lit ₁ h₁) (is-lit ₂ h₂)
                        (is-lit ₃ h₃) (is-lit ₄ h₄) (is-lit ₅ h₅))
                   (by-norm R80ᶠ φR Eq.refl Eq.refl))

      -- The sign on 6, for ⟨M⟩ and ⟨KM⟩.
      s6z : f6 ≢ z₀
      s6z = apart t6 tz₀ (λ ())

      s6o : f6 ≢ o₁
      s6o = apart t6 to₁ (λ ())

      sA sB sX sD sY sW : _
      sA = apart {a} {f6} h₀ t6 (λ ())
      sB = apart {b} {f6} h₁ t6 (λ ())
      sX = apart {x} {f6} h₂ t6 (λ ())
      sD = apart {d} {f6} h₃ t6 (λ ())
      sY = apart {y} {f6} h₄ t6 (λ ())
      sW = apart {w} {f6} h₅ t6 (λ ())

      asL : AvSW e65 f6 s6z s6o L
      asL = (sA , sB) , (sA , sX) , (sB , sD) , (sA , sY) , (sB , sW) , (sA , sB) , sA , sB ,
            (sA , sY) , (sB , sW) , (sA , sX) , (sB , sD)

      asR : AvSW e65 f6 s6z s6o R
      asR = (sA , sX) , (sB , sD) , (sA , sY) , (sB , sW) , (sA , sB) , sA , sB ,
            (sA , sY) , (sB , sW) , (sA , sX) , (sB , sD) , (sA , sB)

      core : ∀ (c : Coset) → Obl c L R
      core ⟨ε⟩  = F.by-frameAt ⟨ε⟩ L R (avL ek-ε) (avR ek-ε) ndL ndR Eq.refl img
      core ⟨K⟩  = F.by-frameAt ⟨K⟩ L R (avL ek-K) (avR ek-K) ndL ndR Eq.refl img
      core ⟨M⟩  = obl-M e65 f6 s6z s6o ⟨ε⟩ L R asL asR ndL ndR (core ⟨ε⟩)
      core ⟨KM⟩ = obl-M e65 f6 s6z s6o ⟨K⟩ L R asL asR ndL ndR (core ⟨K⟩)

  -- (d4*), at the literals carried to N.
  d4 : D4 e65
  d4 e c = C.core (Eq.subst Fin e ₀) (Eq.subst Fin e ₁) (Eq.subst Fin e ₂) (Eq.subst Fin e ₃)
                  (Eq.subst Fin e ₄) (Eq.subst Fin e ₅)
                  (toℕ-subst e ₀) (toℕ-subst e ₁) (toℕ-subst e ₂) (toℕ-subst e ₃)
                  (toℕ-subst e ₄) (toℕ-subst e ₅) c
