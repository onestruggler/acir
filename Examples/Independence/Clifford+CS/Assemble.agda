------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness by transfer with scalars: the assembly
--
-- Clifford+CS.Bridge.ViaS gives, for circuits with the same matrix,
-- encodings that differ by i^k, with twice k the difference of their ω
-- counts mod 8.  With the source complete, its words for the two equal
-- by its rules; with every source rule decoding to a derivation, so are
-- the decodings; and with i decoding to ω ω and every gate g equal to
-- ω^(c g) times the decoding of its encoding, the circuits are equal:
-- w ≈ ω^a D(ℰ w), v ≈ ω^b D(ℰ v) ≈ ω^(b + 2k) D(ℰ w), and b + 2k ≡ a
-- mod 8.  The decoding reads a source word as written (Decode.Dʷ).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Independence.Clifford+CS.Assemble where

open import Data.Nat.Base using (ℕ ; zero ; suc ; _+_ ; _*_ ; _^_)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_) renaming (_^_ to _^ʷ_)

import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Tactic.AssociativitySolver using (module Assoc)

open import Quantum.Synthesis.Matrix using (Matrix ; _·*·_)
open import Quantum.Synthesis.Ring
  using (SemiRingDyadic ; RingDyadic ; AdjointDyadic ; SemiRingCplx ; RingCplx ; AdjointCplx)

import Examples.Groups.Clifford+CS-TwoLevel.Ring as CSR
import Examples.Groups.Clifford+CS-TwoLevel.Semantics as CSS

open import Examples.Independence.Clifford+CS.Syntactics
import Examples.Independence.Clifford+CS.Semantics as Sem
open import Examples.Independence.Clifford+CS.Kit using (Eqn ; ⟪_⟫ ; lhs⁼ ; rhs⁼ ; prf ; ω⁸⁼)
open import Examples.Independence.Clifford+CS.Bridge using (mapι ; ωs ; module ViaS)
open import Examples.Independence.Semantics.Reading using (_ᵀ ; module Mat)
  renaming (⟪_⟫ to ⟪_⟫ᴿ)

private
  variable
    n : ℕ

  one : (h h' : PGate 0) → h ≡ h'
  one ⌈ ω-gate ⌉ ⌈ ω-gate ⌉ = refl

open Single-Scalar one using (comm-gate₀-w)

------------------------------------------------------------------------
-- Powers of ω

module Powers {n : ℕ} where

  open PB (n VRel,_===_)
  open PP (n VRel,_===_) using (^-+ ; word-setoid)
  open import Relation.Binary.Reasoning.Setoid word-setoid

  ωᵏ : ℕ → Circuit n
  ωᵏ k = ω ^ʷ k

  -- ω commutes with every circuit, and so do its powers.
  ωᵏ-central : (k : ℕ) (w : Circuit n) → w • ωᵏ k ≈ ωᵏ k • w
  ωᵏ-central zero          w = trans right-unit (sym left-unit)
  ωᵏ-central (suc zero)    w = comm-gate₀-w ⌈ ω-gate ⌉ w
  ωᵏ-central (suc (suc k)) w = begin
    w • (ω • ωᵏ (suc k))        ≈⟨ sym assoc ⟩
    (w • ω) • ωᵏ (suc k)        ≈⟨ cong (comm-gate₀-w ⌈ ω-gate ⌉ w) refl ⟩
    (ω • w) • ωᵏ (suc k)        ≈⟨ assoc ⟩
    ω • (w • ωᵏ (suc k))        ≈⟨ cong refl (ωᵏ-central (suc k) w) ⟩
    ω • (ωᵏ (suc k) • w)        ≈⟨ sym assoc ⟩
    (ω • ωᵏ (suc k)) • w        ∎

  ωᵏ-+ : (a b : ℕ) → ωᵏ (a + b) ≈ ωᵏ a • ωᵏ b
  ωᵏ-+ = ^-+ ω

  ωᵏ⁸ : ωᵏ 8 ≈ ε
  ωᵏ⁸ = trans (PP.by-assoc (n VRel,_===_) refl) (prf (ω⁸⁼ {n}))

  -- ω^(x + y 8) = ω^x.
  ωᵏ-8 : (x y : ℕ) → ωᵏ (x + y * 8) ≈ ωᵏ x
  ωᵏ-8 x zero    = Eq.subst (λ z → ωᵏ z ≈ ωᵏ x) (Eq.sym (ℕP.+-identityʳ x)) refl
  ωᵏ-8 x (suc y) = begin
    ωᵏ (x + (8 + y * 8))      ≈⟨ Eq.subst (λ z → ωᵏ (x + (8 + y * 8)) ≈ ωᵏ z)
                                    (Eq.trans (Eq.sym (ℕP.+-assoc x 8 (y * 8)))
                                              (Eq.cong (_+ y * 8) (ℕP.+-comm x 8))) refl ⟩
    ωᵏ (8 + x + y * 8)        ≈⟨ Eq.subst (λ z → ωᵏ (8 + x + y * 8) ≈ ωᵏ z)
                                    (ℕP.+-assoc 8 x (y * 8)) refl ⟩
    ωᵏ (8 + (x + y * 8))      ≈⟨ ωᵏ-+ 8 (x + y * 8) ⟩
    ωᵏ 8 • ωᵏ (x + y * 8)     ≈⟨ cong ωᵏ⁸ (ωᵏ-8 x y) ⟩
    ε • ωᵏ x                  ≈⟨ left-unit ⟩
    ωᵏ x                      ∎

open Powers public using (ωᵏ ; ωᵏ-central ; ωᵏ-+ ; ωᵏ⁸ ; ωᵏ-8)

------------------------------------------------------------------------
-- The decoding of a source word, read as written

module Decode {n : ℕ} {G : Set} (d : G → Circuit n) where

  Dʷ : Word G → Circuit n
  Dʷ [ g ]ʷ  = d g
  Dʷ ε       = ε
  Dʷ (u • v) = Dʷ u • Dʷ v

------------------------------------------------------------------------
-- The assembly

module Assemble {n : ℕ} {G : Set}
  (F   : Word G → Matrix (2 ^ n) (2 ^ n) CSR.D)
  (F-ε : F ε ≡ CSS.𝕀)
  (F-• : ∀ u v → F (u • v) ≡ F u ·*· F v)
  (F-u : ∀ u → CSS.Unitary (F u))
  (J   : Word G)
  (F-J : ∀ u → mapι (F (J • u)) ≡ ωs 2 (mapι (F u)))
  (ℰ   : Gen n → Word G)
  (c   : Gen n → ℕ)
  (gen : ∀ g → Mat.mat (⟪ Sem.⟦ g ⟧₀ ⟫ᴿ ᵀ) ≡ ωs (c g) (mapι (F (ℰ g))))
  -- the source is complete
  (Γ   : Word G → Word G → Set)
  (src : ∀ {u v} → F u ≡ F v → PB._≈_ Γ u v)
  -- the decoding
  (d   : G → Circuit n)
  where

  open ViaS F F-ε F-• F-u J F-J ℰ c gen public
  open Decode d public

  open PB (n VRel,_===_)
  open PP (n VRel,_===_) using (word-setoid)
  open import Relation.Binary.Reasoning.Setoid word-setoid

  module _
    (D-rel    : ∀ {u v} → Γ u v → n ⊢ Dʷ u ≈ Dʷ v)
    (D-J      : n ⊢ Dʷ J ≈ ωᵏ 2)
    (back-gen : ∀ g → n ⊢ [ g ]ʷ ≈ ωᵏ (c g) • Dʷ (ℰ g))
    where

    D-≈ : ∀ {u v} → PB._≈_ Γ u v → n ⊢ Dʷ u ≈ Dʷ v
    D-≈ PB.refl        = PB.refl
    D-≈ (PB.sym e)     = PB.sym (D-≈ e)
    D-≈ (PB.trans e f) = PB.trans (D-≈ e) (D-≈ f)
    D-≈ (PB.cong e f)  = PB.cong (D-≈ e) (D-≈ f)
    D-≈ PB.assoc       = PB.assoc
    D-≈ PB.left-unit   = PB.left-unit
    D-≈ PB.right-unit  = PB.right-unit
    D-≈ (PB.axiom a)   = D-rel a

    -- i^k decodes to ω^(2k).
    D-Jʷ : (k : ℕ) (u : Word G) → Dʷ (Jʷ k u) ≈ ωᵏ (k + k) • Dʷ u
    D-Jʷ zero    u = sym left-unit
    D-Jʷ (suc k) u = begin
      Dʷ J • Dʷ (Jʷ k u)              ≈⟨ cong D-J (D-Jʷ k u) ⟩
      ωᵏ 2 • (ωᵏ (k + k) • Dʷ u)      ≈⟨ sym assoc ⟩
      (ωᵏ 2 • ωᵏ (k + k)) • Dʷ u      ≈⟨ cong (sym (ωᵏ-+ 2 (k + k))) refl ⟩
      ωᵏ (2 + (k + k)) • Dʷ u         ≈⟨ cong (Eq.subst (λ z → ωᵏ (2 + (k + k)) ≈ ωᵏ z)
                                                  (Eq.cong suc (Eq.sym (ℕP.+-suc k k))) refl) refl ⟩
      ωᵏ (suc k + suc k) • Dʷ u       ∎

    -- Lemma 19 with scalars: a circuit is ω^c times the decoding of its
    -- encoding.
    back : (w : Circuit n) → w ≈ ωᵏ (cʷ w) • Dʷ (ℰʷ w)
    back [ g ]ʷ  = back-gen g
    back ε       = sym left-unit
    back (w • v) = begin
      w • v                                          ≈⟨ cong (back w) (back v) ⟩
      (ωᵏ a • Dʷ (ℰʷ w)) • (ωᵏ b • Dʷ (ℰʷ v))        ≈⟨ assoc ⟩
      ωᵏ a • (Dʷ (ℰʷ w) • (ωᵏ b • Dʷ (ℰʷ v)))        ≈⟨ cong refl (sym assoc) ⟩
      ωᵏ a • ((Dʷ (ℰʷ w) • ωᵏ b) • Dʷ (ℰʷ v))        ≈⟨ cong refl (cong (ωᵏ-central b (Dʷ (ℰʷ w))) refl) ⟩
      ωᵏ a • ((ωᵏ b • Dʷ (ℰʷ w)) • Dʷ (ℰʷ v))        ≈⟨ cong refl assoc ⟩
      ωᵏ a • (ωᵏ b • (Dʷ (ℰʷ w) • Dʷ (ℰʷ v)))        ≈⟨ sym assoc ⟩
      (ωᵏ a • ωᵏ b) • (Dʷ (ℰʷ w) • Dʷ (ℰʷ v))        ≈⟨ cong (sym (ωᵏ-+ a b)) refl ⟩
      ωᵏ (a + b) • Dʷ (ℰʷ w • ℰʷ v)                  ∎
      where
      a = cʷ w
      b = cʷ v

    -- Circuits with the same matrix are equal.
    complete : {w v : Circuit n} → Sem.⟦ w ⟧ Sem.≈ Sem.⟦ v ⟧ → n ⊢ w ≈ v
    complete {w} {v} e with transfer {w} {v} e
    ... | k , q , ar , eF = begin
        w                                      ≈⟨ back w ⟩
        ωᵏ a • Dʷ (ℰʷ w)                       ≈⟨ cong (sym scal) refl ⟩
        ωᵏ (b + (k + k)) • Dʷ (ℰʷ w)           ≈⟨ cong (ωᵏ-+ b (k + k)) refl ⟩
        (ωᵏ b • ωᵏ (k + k)) • Dʷ (ℰʷ w)        ≈⟨ assoc ⟩
        ωᵏ b • (ωᵏ (k + k) • Dʷ (ℰʷ w))        ≈⟨ cong refl (sym (D-Jʷ k (ℰʷ w))) ⟩
        ωᵏ b • Dʷ (Jʷ k (ℰʷ w))                ≈⟨ cong refl (D-≈ (src eF)) ⟩
        ωᵏ b • Dʷ (ℰʷ v)                       ≈⟨ sym (back v) ⟩
        v                                      ∎
      where
      a = cʷ w
      b = cʷ v
      -- ω^(b + 2k) = ω^(b + 2k + 8q) = ω^(a + 8b) = ω^a
      scal : ωᵏ (b + (k + k)) ≈ ωᵏ a
      scal = trans (sym (ωᵏ-8 (b + (k + k)) q))
                   (trans (Eq.subst (λ z → ωᵏ (b + (k + k) + q * 8) ≈ ωᵏ z) ar refl)
                          (ωᵏ-8 a b))
