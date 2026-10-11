------------------------------------------------------------------------
-- Presentations of groups
--
-- The cosets ⟨M⟩ and ⟨KM⟩ from ⟨ε⟩ and ⟨K⟩
--
-- The representatives of ⟨M⟩ and ⟨KM⟩ are those of ⟨ε⟩ and ⟨K⟩ times
-- (−1)_[1], so the action at c ⊕ ⟨M⟩ is the action at c conjugated by
-- that sign — which is not a word of P, but becomes one with a second
-- sign on an index s away from everything: with
--
--     Z ⟨ε⟩ = Z ⟨M⟩ = (−1)_[1] (−1)_[s],   Z ⟨K⟩ = Z ⟨KM⟩ = (−1)_[s] X_[0,1],
--
-- the action at c ⊕ ⟨M⟩ on a generator is Z c · (the action at c) ·
-- Z c′ (`gen-sym`).  That needs no case analysis of its own: both sides
-- are `Frame.tr` at one frame chosen for the generator with s as its
-- sink, and the transition words at c ⊕ ⟨M⟩ are those at c with Z on
-- one side (`cornerL`, `cornerR`, one normaliser call each, checked in
-- Python first, `scratchpad/tSym.py`).  Along a word the Z's in the
-- middle cancel (`sym-run`), so item (b) at c ⊕ ⟨M⟩ follows from item
-- (b) at c (`obl-M`) for any word that leaves one index free for s.
-- That is what (d4*) needs on three qubits, where its six indices leave
-- room for a frame pair and a sink only when every Hadamard is read at
-- ⟨ε⟩ or ⟨K⟩ (`Frame.by-frameAt`), i.e. only from those two cosets.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.SignSym (m : ℕ) where

open import Data.Bool using (_xor_)
open import Data.Fin using (Fin)
open import Data.Nat using () renaming (_^_ to _^ℕ_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (⊤ ; tt)
open import Data.Vec using ([] ; _∷_)
open import Data.Vec.Relation.Unary.All using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; ε ; _•_ ; [_]ʷ ; _ᵗ)

open import Notations using (₀ ; ₁ ; ₂ ; ₃₊)

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Cosets
  using (Coset ; ⟨ε⟩ ; ⟨M⟩ ; ⟨K⟩ ; ⟨KM⟩)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8 using (_P,_===_)
open import Examples.Groups.Real-Clifford+CH.Encoding using (zz ; zx)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.RS m using (act ; z₀ ; o₁ ; z₀≢o₁)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.NF m using (gen ; cat ; nil ; hf-zz)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SignedPerm m
  using (δ ; eqv ; xor-self ; swapF-o)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SigmaPerm m using (hfree-zx ; zx-pair)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Unique m using (A5-full)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Template m using ([]ᵈ ; _∷ᵈ_ ; tz ; ty)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure10 m using (Eq65)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Frame m using (module Frame ; _⊕_ ; tag)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.ItemB m using (Obl ; FrameFor ; frame-for)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)

import Examples.Groups.Real-Clifford+CH.Auxiliary.Syntactics as G
open G using (−1[_] ; X[_,_] ; H[_,_])

open Tools (m P,_===_)

private
  N : ℕ
  N = 2 ^ℕ (₃₊ m)

  W : Set
  W = Word (GenP (₃₊ m))

  ≢sym : ∀ {x y : Fin N} → x ≢ y → y ≢ x
  ≢sym ne e = ne (Eq.sym e)

  refl≡ : ∀ {u v : W} → u ≡ v → u ≈ v
  refl≡ Eq.refl = refl

  -- Adding ⟨M⟩ commutes with adding anything.
  ⊕M : ∀ (c t : Coset) → (c ⊕ ⟨M⟩) ⊕ t ≡ (c ⊕ t) ⊕ ⟨M⟩
  ⊕M ⟨ε⟩  ⟨ε⟩  = Eq.refl
  ⊕M ⟨ε⟩  ⟨M⟩  = Eq.refl
  ⊕M ⟨ε⟩  ⟨K⟩  = Eq.refl
  ⊕M ⟨ε⟩  ⟨KM⟩ = Eq.refl
  ⊕M ⟨M⟩  ⟨ε⟩  = Eq.refl
  ⊕M ⟨M⟩  ⟨M⟩  = Eq.refl
  ⊕M ⟨M⟩  ⟨K⟩  = Eq.refl
  ⊕M ⟨M⟩  ⟨KM⟩ = Eq.refl
  ⊕M ⟨K⟩  ⟨ε⟩  = Eq.refl
  ⊕M ⟨K⟩  ⟨M⟩  = Eq.refl
  ⊕M ⟨K⟩  ⟨K⟩  = Eq.refl
  ⊕M ⟨K⟩  ⟨KM⟩ = Eq.refl
  ⊕M ⟨KM⟩ ⟨ε⟩  = Eq.refl
  ⊕M ⟨KM⟩ ⟨M⟩  = Eq.refl
  ⊕M ⟨KM⟩ ⟨K⟩  = Eq.refl
  ⊕M ⟨KM⟩ ⟨KM⟩ = Eq.refl

-- Non-degenerate generators and words, as in `Frame`.
Nd : G.Gen N → Set
Nd −1[ a ]    = ⊤
Nd X[ a , b ] = a ≢ b
Nd H[ a , b ] = a ≢ b

NdW : Word (G.Gen N) → Set
NdW [ y ]ʷ  = Nd y
NdW ε       = ⊤
NdW (u • v) = NdW u × NdW v

module _ (e65 : Eq65) (s : Fin N) (sz : s ≢ z₀) (so : s ≢ o₁) where

  Zs : Coset → W
  Zs ⟨ε⟩  = zz {₃₊ m} o₁ s
  Zs ⟨M⟩  = zz {₃₊ m} o₁ s
  Zs ⟨K⟩  = zx {₃₊ m} s z₀ o₁
  Zs ⟨KM⟩ = zx {₃₊ m} s z₀ o₁

  private
    zz-sq : zz {₃₊ m} o₁ s • zz {₃₊ m} o₁ s ≈ ε
    zz-sq = A5-full (cat (gen (hf-zz o₁ s)) (gen (hf-zz o₁ s))) nil
                    (eqv (λ i → xor-self (δ o₁ i xor δ s i)) (λ _ → Eq.refl))

    zx-sq : zx {₃₊ m} s z₀ o₁ • zx {₃₊ m} s z₀ o₁ ≈ ε
    zx-sq = A5-full (cat (hfree-zx s z₀ o₁) (hfree-zx s z₀ o₁)) nil
                    (zx-pair s s z₀ o₁ (Eq.sym (swapF-o z₀ o₁ s sz so)))

  ZZ : ∀ (c : Coset) → Zs c • Zs c ≈ ε
  ZZ ⟨ε⟩  = zz-sq
  ZZ ⟨M⟩  = zz-sq
  ZZ ⟨K⟩  = zx-sq
  ZZ ⟨KM⟩ = zx-sq

  -- Where a generator's indices are not s.
  AvS : G.Gen N → Set
  AvS −1[ a ]    = a ≢ s
  AvS X[ a , b ] = (a ≢ s) × (b ≢ s)
  AvS H[ a , b ] = (a ≢ s) × (b ≢ s)

  AvSW : Word (G.Gen N) → Set
  AvSW [ y ]ʷ  = AvS y
  AvSW ε       = ⊤
  AvSW (u • v) = AvSW u × AvSW v

  -- The action at c ⊕ ⟨M⟩ on one generator.
  Sym : Coset → G.Gen N → Set
  Sym c y = (proj₁ (act (c ⊕ ⟨M⟩) y) ≈ Zs c • (proj₁ (act c y) • Zs (proj₂ (act c y)))) ×
            (proj₂ (act (c ⊕ ⟨M⟩) y) ≡ proj₂ (act c y) ⊕ ⟨M⟩)

  ----------------------------------------------------------------------
  -- One generator, through a frame chosen for it with s as its sink

  private
    module Loc (a b : Fin N) where
      open FrameFor (frame-for a b s)

      es : e ≢ s
      es = ≢sym ce

      fs : f ≢ s
      fs = ≢sym cf

      module F = Frame e65 z₀ o₁ z₀≢o₁ e f s ef es fs ez eo fz fo sz so

      open F.NV (z₀ ∷ o₁ ∷ s ∷ [])
                ((≢sym z₀≢o₁ ∷ sz ∷ []) ∷ᵈ (so ∷ []) ∷ᵈ [] ∷ᵈ []ᵈ)
                (≢sym ez ∷ ≢sym eo ∷ ≢sym es ∷ []) (≢sym fz ∷ ≢sym fo ∷ ≢sym fs ∷ [])

      avZ : a ≢ s → F.Avoids −1[ a ]
      avZ as = ae , af , as

      av2 : a ≢ s → b ≢ s → F.Av a × F.Av b
      av2 as bs = (ae , af , as) , (be , bf , bs)

      -- The transition words at c ⊕ ⟨M⟩ are those at c with Z on one side.
      cornerL : ∀ (c : Coset) → F.T (c ⊕ ⟨M⟩) ≈ Zs c • F.T c
      cornerL ⟨ε⟩  = sym right-unit
      cornerL ⟨M⟩  = sym zz-sq
      cornerL ⟨K⟩  = by-norm (⌞ hl ₀ ₁ ⌟ •ᶠ ⌞ hf (tz ₁ ₂) ⌟) (⌞ hf (ty ₂ ₀ ₁) ⌟ •ᶠ ⌞ hl ₀ ₁ ⌟)
                             Eq.refl Eq.refl
      cornerL ⟨KM⟩ = by-norm ⌞ hl ₀ ₁ ⌟ (⌞ hf (ty ₂ ₀ ₁) ⌟ •ᶠ ⌞ hl ₀ ₁ ⌟ •ᶠ ⌞ hf (tz ₁ ₂) ⌟)
                             Eq.refl Eq.refl

      cornerR : ∀ (c : Coset) → F.T⁻ (c ⊕ ⟨M⟩) ≈ F.T⁻ c • Zs c
      cornerR ⟨ε⟩  = sym left-unit
      cornerR ⟨M⟩  = sym zz-sq
      cornerR ⟨K⟩  = by-norm (⌞ hf (tz ₁ ₂) ⌟ •ᶠ ⌞ hr ₀ ₁ ⌟) (⌞ hr ₀ ₁ ⌟ •ᶠ ⌞ hf (ty ₂ ₀ ₁) ⌟)
                             Eq.refl Eq.refl
      cornerR ⟨KM⟩ = by-norm ⌞ hr ₀ ₁ ⌟ ((⌞ hf (tz ₁ ₂) ⌟ •ᶠ ⌞ hr ₀ ₁ ⌟) •ᶠ ⌞ hf (ty ₂ ₀ ₁) ⌟)
                             Eq.refl Eq.refl

      sym-at : ∀ (c : Coset) (y : G.Gen N) → F.Avoids y → F.NonDeg y → Sym c y
      sym-at c y av nd = word , c′M
        where
        c′ : Coset
        c′ = proj₂ (act c y)

        c′M : proj₂ (act (c ⊕ ⟨M⟩) y) ≡ c′ ⊕ ⟨M⟩
        c′M = Eq.trans (F.nxt (c ⊕ ⟨M⟩) y nd)
                (Eq.trans (⊕M c (tag y)) (Eq.cong (_⊕ ⟨M⟩) (Eq.sym (F.nxt c y nd))))

        word : proj₁ (act (c ⊕ ⟨M⟩) y) ≈ Zs c • (proj₁ (act c y) • Zs c′)
        word = begin
          proj₁ (act (c ⊕ ⟨M⟩) y)
            ≈⟨ F.tr (c ⊕ ⟨M⟩) y av ⟩
          F.T (c ⊕ ⟨M⟩) • (F.Φ y • F.T⁻ (proj₂ (act (c ⊕ ⟨M⟩) y)))
            ≈⟨ back (F.T (c ⊕ ⟨M⟩)) (back (F.Φ y) (refl≡ (Eq.cong F.T⁻ c′M))) ⟩
          F.T (c ⊕ ⟨M⟩) • (F.Φ y • F.T⁻ (c′ ⊕ ⟨M⟩))
            ≈⟨ cong (cornerL c) (back (F.Φ y) (cornerR c′)) ⟩
          (Zs c • F.T c) • (F.Φ y • (F.T⁻ c′ • Zs c′))
            ≈⟨ assoc ⟩
          Zs c • (F.T c • (F.Φ y • (F.T⁻ c′ • Zs c′)))
            ≈⟨ back (Zs c) (back (F.T c) (sym assoc)) ⟩
          Zs c • (F.T c • ((F.Φ y • F.T⁻ c′) • Zs c′))
            ≈⟨ back (Zs c) (sym assoc) ⟩
          Zs c • ((F.T c • (F.Φ y • F.T⁻ c′)) • Zs c′)
            ≈⟨ back (Zs c) (front (Zs c′) (sym (F.tr c y av))) ⟩
          Zs c • (proj₁ (act c y) • Zs c′) ∎

  gen-sym : ∀ (c : Coset) (y : G.Gen N) → AvS y → Nd y → Sym c y
  gen-sym c −1[ a ]    as        nd = Loc.sym-at a a c −1[ a ] (Loc.avZ a a as) nd
  gen-sym c X[ a , b ] (as , bs) nd = Loc.sym-at a b c X[ a , b ] (Loc.av2 a b as bs) nd
  gen-sym c H[ a , b ] (as , bs) nd = Loc.sym-at a b c H[ a , b ] (Loc.av2 a b as bs) nd

  ----------------------------------------------------------------------
  -- Words

  Run : Coset → Coset → Word (G.Gen N) → Set
  Run c d u = (proj₁ ((act ᵗ) d u) ≈ Zs c • (proj₁ ((act ᵗ) c u) • Zs (proj₂ ((act ᵗ) c u)))) ×
              (proj₂ ((act ᵗ) d u) ≡ proj₂ ((act ᵗ) c u) ⊕ ⟨M⟩)

  sym-run : ∀ (c d : Coset) (u : Word (G.Gen N)) → d ≡ c ⊕ ⟨M⟩ → AvSW u → NdW u → Run c d u
  sym-run c .(c ⊕ ⟨M⟩) [ y ]ʷ  Eq.refl av        nd        = gen-sym c y av nd
  sym-run c .(c ⊕ ⟨M⟩) ε       Eq.refl _         _         =
    sym (trans (back (Zs c) left-unit) (ZZ c)) , Eq.refl
  sym-run c d          (u • v) e       (au , av) (nu , nv) = word , proj₂ rv
    where
    c₁ d₁ c₂ : Coset
    c₁ = proj₂ ((act ᵗ) c u)
    d₁ = proj₂ ((act ᵗ) d u)
    c₂ = proj₂ ((act ᵗ) c₁ v)

    A B : W
    A = proj₁ ((act ᵗ) c u)
    B = proj₁ ((act ᵗ) c₁ v)

    ru : Run c d u
    ru = sym-run c d u e au nu

    rv : Run c₁ d₁ v
    rv = sym-run c₁ d₁ v (proj₂ ru) av nv

    word : proj₁ ((act ᵗ) d u) • proj₁ ((act ᵗ) d₁ v) ≈ Zs c • ((A • B) • Zs c₂)
    word = begin
      proj₁ ((act ᵗ) d u) • proj₁ ((act ᵗ) d₁ v)
        ≈⟨ cong (proj₁ ru) (proj₁ rv) ⟩
      (Zs c • (A • Zs c₁)) • (Zs c₁ • (B • Zs c₂))
        ≈⟨ assoc ⟩
      Zs c • ((A • Zs c₁) • (Zs c₁ • (B • Zs c₂)))
        ≈⟨ back (Zs c) assoc ⟩
      Zs c • (A • (Zs c₁ • (Zs c₁ • (B • Zs c₂))))
        ≈⟨ back (Zs c) (back A (sym assoc)) ⟩
      Zs c • (A • ((Zs c₁ • Zs c₁) • (B • Zs c₂)))
        ≈⟨ back (Zs c) (back A (front (B • Zs c₂) (ZZ c₁))) ⟩
      Zs c • (A • (ε • (B • Zs c₂)))
        ≈⟨ back (Zs c) (back A left-unit) ⟩
      Zs c • (A • (B • Zs c₂))
        ≈⟨ back (Zs c) (sym assoc) ⟩
      Zs c • ((A • B) • Zs c₂) ∎

  -- Item (b) at c ⊕ ⟨M⟩ from item (b) at c.
  obl-M : ∀ (c : Coset) (u t : Word (G.Gen N)) → AvSW u → AvSW t → NdW u → NdW t →
          Obl c u t → Obl (c ⊕ ⟨M⟩) u t
  obl-M c u t au at nu nt (ew , ec) =
    trans (proj₁ ru) (trans (back (Zs c) (cong ew (refl≡ (Eq.cong Zs ec)))) (sym (proj₁ rt))) ,
    Eq.trans (proj₂ ru) (Eq.trans (Eq.cong (_⊕ ⟨M⟩) ec) (Eq.sym (proj₂ rt)))
    where
    ru : Run c (c ⊕ ⟨M⟩) u
    ru = sym-run c (c ⊕ ⟨M⟩) u Eq.refl au nu

    rt : Run c (c ⊕ ⟨M⟩) t
    rt = sym-run c (c ⊕ ⟨M⟩) t Eq.refl at nt
