------------------------------------------------------------------------
-- Presentations of groups
--
-- The rewrite rules find the hidden shift
--
-- Section 5.2 of Amy's QPL 2018 paper reports that the calculus "finds
-- the correct output |s⟩ even without providing the specification,
-- effectively simulating the algorithm": reducing the path-sum of the
-- hidden shift circuit on the input |0⟩ until no path variable is left
-- produces the path-sum |0⟩ ↦ |s⟩.  This module proves that every such
-- reduction does, for every m, every g and every shift s; that one
-- exists is shown for a single instance only (PathSum.HiddenShift.Example).
--
-- The input |0⟩.  Path-sums here have no constant inputs, so the
-- circuit on |0⟩ is at0 (HS g s): every input variable is replaced by
-- 0 in the phase and the outputs, and the result, which ignores its
-- input, has at every input the column the circuit has at 0 (amp-at0).
-- It is equivalent, in the sense of definition 2.3, to the
-- specification |x⟩ ↦ |s⟩ (hidden-shift-≋) -- PathSum.HiddenShift's
-- theorem, read at every input.
--
-- The paths of the circuit.  A path of HS g s is a path of each
-- Hadamard layer (layer₁, layer₂, layer₃), the last being the output
-- (outBit-HS), and modulo 1 the phase along it is ½ times the parity
-- hs-parity of the paper's exponent x·y₁ + f′(y₁) + y₁·y₂ + f̃(y₂) +
-- y₂·y₃ (phase-HS).  Any path-sum with these outputs and this phase is
-- therefore the circuit on |0⟩ as the paper represents path-sums --
-- congruent to at0 (HS g s), coefficient by coefficient modulo 1 and 2
-- (at0-HS-congruent).  That is how a path-sum written out, whose
-- polynomials compute, is tied to the composite, whose do not.
--
-- Any reduction.  Take any chain of figure 2's rules, applied at any
-- path variables (PathSum.Full's _⟶ᶠ_, which contains the head-only
-- calculi), from at0 (HS g s) to a path-sum ζ with no path variables.
-- The rules are sound (PathSum.Full.Sound), so ζ ≋ specᴾ s, and a
-- path-sum without path variables equivalent to the specification is
-- the specification syntactically (spec-only-if): its normalisation is
-- 0, its outputs are s coefficient by coefficient modulo 2, and its
-- phase vanishes modulo 1 coefficient by coefficient (Möbius
-- inversion, PathSum.Mobius, from the values).  So the calculus cannot
-- end anywhere but at |s⟩, whatever rules it applies in whatever order
-- (hidden-shift-reduces), and the same holds of a derivation in the
-- paper's style, which interleaves head rules with rewriting of the
-- polynomials modulo 1 and 2 (hidden-shift-derives).  This is the
-- analogue for the hidden shift of corollary 4.4 as
-- PathSum.Full.Corollary states it.
--
-- What is not proved here is that such a reduction exists for every
-- m: the parametric chain would track 6m rule applications through
-- renumbered path variables.  PathSum.HiddenShift.Example exhibits a
-- derivation at m = 1, with the paper's rules, at M₀ = 0.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.Simulation (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; _xor_; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (zero; suc; toℕ; _↑ˡ_; _↑ʳ_)
open import Data.Integer.Base using (ℤ; 0ℤ; 1ℤ; +_; -_; _+_; _-_; _*_)
open import Data.Integer.Divisibility.Signed using
  (_∣_; _∣?_; divides; ∣m∣n⇒∣m-n)
open import Data.Integer.Properties using
  (+-comm; +-identityʳ; +-inverseˡ)
open import Data.Integer.Solver using (module +-*-Solver)
open import Data.Nat.Base using (zero; suc; s≤s; z≤n) renaming (_+_ to _ℕ+_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_; contradiction)

open import PathSum.Assign using ([_]ᶻ; same-refl)
open import PathSum.Base using (PathSum; ⟨_,_⟩; phase; out)
open import PathSum.Compose using (_∘ᴾ_)
open import PathSum.Compose.Properties M₀ using
  (hits-outBit; eval-∘; outBit-∘)
open import PathSum.Compose.Sum M₀ using
  (_++ᵃ_; ++ᵃ-split; if-cong; zpow-≡)
open import PathSum.Congruence M₀ using (Congruent)
open import PathSum.Cyclotomic M₀ using
  (Amp; 0ᴬ; _·ᴬ_; _≐_; H; N; c; Σᴮ-cong; zpow; χ; χ--1; χ-0; rot;
   rot-map; rot-exp; rot-zpow; rot-+ᴬ; rot-comp; rot-·ᴬ; √2·; √2·-map;
   √2·-twice; √2·-0ᴬ; √2·-injective; scale; scale-map;
   zpow-0≢0ᴬ; 2·≢scale-zpow0; 0ᶠ; zpow0-at-0)
open import PathSum.Denotation M₀ using
  (Assign; amp; hits; outBit; _≋_; ≋-sym; ≋-trans; hits-elim; hits-≗³;
   outBit-μ)
open import PathSum.HiddenShift M₀ using
  (Hᴾ; Oᴾ; hdotᴾ; mmᴾ; dualᴾ; shiftᴾ; boolᴾ; odd-dotᴾ; bool-mmᴾ;
   bool-dualᴾ; bool-shiftᴾ; boolᴾ-resp; HS; hs-norm; specᴾ; amp-specᴾ;
   hidden-shift-spec; none; eval-none; Σᴮ-none)
open import PathSum.HiddenShift.Sign M₀ using
  (1ᴬ; halve; odd-+; odd-≡; ½-parity)
open import PathSum.HiddenShift.Walsh using
  (0ᵃ; _⊕ᵃ_; dot; dot-cong; mm; dual; mm-resp; dual-resp)
open import PathSum.Mobius using (values⇒coefficientsᵐ)
open import PathSum.Polynomial using
  (Poly; Var; x[_]; y[_]; 0ᴾ; _-ᴾ_; κ; μ; eval; _≈[_]_)
open import PathSum.Polynomial.Bind using (bind; eval-bind; odd)
open import PathSum.Polynomial.Product using (eval-μᴾ; eval-0ᴾ)
open import PathSum.Polynomial.Properties using
  (valᵛ; eval-κ; eval-−ᴾ; eval-·ᴾ; eval-cong)

open +-*-Solver using (solve; con; _:+_; _:-_; _:*_; _:=_)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Full M using (_⟶ᶠ*_)
open import PathSum.Full.Sound M₀ using (⟶ᶠ*-sound)
open import PathSum.Order M using (pow)
open import PathSum.Reduction M using (½)
open import PathSum.Reduction.Derivation M₀ using
  (Derivation; derivation-sound)

private
  variable
    n k m : ℕ


------------------------------------------------------------------------
-- The input |0⟩

-- Every input variable becomes 0; the path variables stay.

zeroᵛ : Var n m → Poly n m
zeroᵛ x[ i ] = 0ᴾ
zeroᵛ y[ j ] = μ y[ j ]

at0 : PathSum n k m → PathSum n k m
at0 ξ = ⟨ bind (phase ξ) zeroᵛ , (λ w → bind (out ξ w) zeroᵛ) ⟩

eval-at0 : (P : Poly n m) (x : Assign n) (y : Assign m) →
           eval (bind P zeroᵛ) x y ≡ eval P 0ᵃ y
eval-at0 P x y = eval-bind P zeroᵛ x y 0ᵃ y value
  where
  value : ∀ v → eval (zeroᵛ v) x y ≡ [ valᵛ v 0ᵃ y ]ᶻ
  value x[ i ] = eval-0ᴾ x y
  value y[ j ] = eval-μᴾ y[ j ] x y

-- At every input, the column of the path-sum at 0.

amp-at0 : (ξ : PathSum n k m) (x z : Assign n) →
          amp (at0 ξ) x z ≐ amp ξ 0ᵃ z
amp-at0 ξ x z = Σᴮ-cong (λ y → if-cong
  (hits-outBit (at0 ξ) ξ x 0ᵃ y y z
               (λ w → cong odd (eval-at0 (out ξ w) x y)))
  (zpow-≡ (eval-at0 (phase ξ) x y)))

-- The hidden shift circuit on |0⟩ is the specification.

hidden-shift-≋ : (g : Poly m 0) (s : Assign (m ℕ+ m)) →
                 at0 (HS g s) ≋ specᴾ s
hidden-shift-≋ g s x z i =
  trans (amp-at0 (HS g s) x z i) (hidden-shift-spec g s x z i)


------------------------------------------------------------------------
-- The paths of the circuit

-- A path of HS g s is a path of each Hadamard layer -- the oracles have
-- none -- concatenated in the order of definition 2.6, the first
-- layer's first.

layer₁ layer₂ layer₃ : ∀ n → Assign (hs-norm n) → Assign n
layer₁ n Y i = Y ((((i ↑ˡ 0) ↑ˡ n) ↑ˡ 0) ↑ˡ n)
layer₂ n Y i = Y ((((n ℕ+ 0) ↑ʳ i) ↑ˡ 0) ↑ˡ n)
layer₃ n Y i = Y ((((n ℕ+ 0) ℕ+ n) ℕ+ 0) ↑ʳ i)

private
  -- An assignment to k + l variables, read as its two blocks.

  split-eval : ∀ k l (P : Poly n (k ℕ+ l)) (x : Assign n)
               (Y : Assign (k ℕ+ l)) →
               eval P x Y ≡
               eval P x ((λ i → Y (i ↑ˡ l)) ++ᵃ (λ i → Y (k ↑ʳ i)))
  split-eval k l P x Y =
    eval-cong P {x} {x} {Y} {(λ i → Y (i ↑ˡ l)) ++ᵃ (λ i → Y (k ↑ʳ i))}
              (λ _ → refl) (λ i → sym (++ᵃ-split k l Y i))

module _ {m : ℕ} (g : Poly m 0) (s : Assign (m ℕ+ m)) where

  -- The parity of the phase along a path, over ½: the three inner
  -- products of the Hadamard layers and the two oracles' exponents.

  hs-parity : Assign (m ℕ+ m) → Assign (hs-norm (m ℕ+ m)) → Bool
  hs-parity x Y =
    (((dot x y₁ xor mm (boolᴾ g) (y₁ ⊕ᵃ s)) xor dot y₁ y₂) xor
     dual (boolᴾ g) y₂) xor dot y₂ y₃
    where
    y₁ y₂ y₃ : Assign (m ℕ+ m)
    y₁ = layer₁ (m ℕ+ m) Y
    y₂ = layer₂ (m ℕ+ m) Y
    y₃ = layer₃ (m ℕ+ m) Y

  -- It reads a path only through its values.

  hs-parity-resp : ∀ x {Y Y′} → (∀ i → Y i ≡ Y′ i) →
                   hs-parity x Y ≡ hs-parity x Y′
  hs-parity-resp x {Y} {Y′} h =
    cong₂ _xor_ (cong₂ _xor_ (cong₂ _xor_ (cong₂ _xor_
      (dot-cong {u = x} {u′ = x} {v = l₁ Y} {v′ = l₁ Y′} (λ _ → refl) h₁)
      (mm-resp (boolᴾ g) (boolᴾ-resp g) (l₁ Y ⊕ᵃ s) (l₁ Y′ ⊕ᵃ s)
               (λ i → cong (_xor s i) (h₁ i))))
      (dot-cong {u = l₁ Y} {u′ = l₁ Y′} {v = l₂ Y} {v′ = l₂ Y′} h₁ h₂))
      (dual-resp (boolᴾ g) (boolᴾ-resp g) (l₂ Y) (l₂ Y′) h₂))
      (dot-cong {u = l₂ Y} {u′ = l₂ Y′} {v = l₃ Y} {v′ = l₃ Y′} h₂ h₃)
    where
    l₁ l₂ l₃ : Assign (hs-norm (m ℕ+ m)) → Assign (m ℕ+ m)
    l₁ = layer₁ (m ℕ+ m)
    l₂ = layer₂ (m ℕ+ m)
    l₃ = layer₃ (m ℕ+ m)

    h₁ : ∀ i → l₁ Y i ≡ l₁ Y′ i
    h₁ i = h _

    h₂ : ∀ i → l₂ Y i ≡ l₂ Y′ i
    h₂ i = h _

    h₃ : ∀ i → l₃ Y i ≡ l₃ Y′ i
    h₃ i = h _

  private
    n₂ : ℕ
    n₂ = m ℕ+ m

    -- The composite, stage by stage.

    R₂ : PathSum n₂ (n₂ ℕ+ 0) (n₂ ℕ+ 0)
    R₂ = Oᴾ (shiftᴾ s (mmᴾ g)) ∘ᴾ Hᴾ

    R₃ : PathSum n₂ ((n₂ ℕ+ 0) ℕ+ n₂) ((n₂ ℕ+ 0) ℕ+ n₂)
    R₃ = Hᴾ ∘ᴾ R₂

    R₄ : PathSum n₂ (((n₂ ℕ+ 0) ℕ+ n₂) ℕ+ 0) (((n₂ ℕ+ 0) ℕ+ n₂) ℕ+ 0)
    R₄ = Oᴾ (dualᴾ g) ∘ᴾ R₃

    -- The blocks of a path.

    Y₄ : Assign (hs-norm n₂) → Assign (((n₂ ℕ+ 0) ℕ+ n₂) ℕ+ 0)
    Y₄ Y i = Y (i ↑ˡ n₂)

    Y₃ : Assign (hs-norm n₂) → Assign ((n₂ ℕ+ 0) ℕ+ n₂)
    Y₃ Y i = Y₄ Y (i ↑ˡ 0)

    Y₂ : Assign (hs-norm n₂) → Assign (n₂ ℕ+ 0)
    Y₂ Y i = Y₃ Y (i ↑ˡ n₂)

    ε₁ ε₂ : Assign (hs-norm n₂) → Assign 0
    ε₁ Y i = Y₂ Y (n₂ ↑ʳ i)
    ε₂ Y i = Y₄ Y (((n₂ ℕ+ 0) ℕ+ n₂) ↑ʳ i)

    -- The output of each stage along a path.

    ob₂ : ∀ x Y w → outBit R₂ x (Y₂ Y) w ≡ layer₁ n₂ Y w
    ob₂ x Y w = trans (cong odd (split-eval n₂ 0 (out R₂ w) x (Y₂ Y)))
      (trans (outBit-∘ (Oᴾ (shiftᴾ s (mmᴾ g))) Hᴾ x (layer₁ n₂ Y) (ε₁ Y) w)
        (trans (outBit-μ (Oᴾ (shiftᴾ s (mmᴾ g))) (outBit Hᴾ x (layer₁ n₂ Y))
                         (ε₁ Y) w x[ w ] refl)
               (outBit-μ Hᴾ x (layer₁ n₂ Y) w y[ w ] refl)))

    ob₃ : ∀ x Y w → outBit R₃ x (Y₃ Y) w ≡ layer₂ n₂ Y w
    ob₃ x Y w = trans (cong odd (split-eval (n₂ ℕ+ 0) n₂ (out R₃ w) x (Y₃ Y)))
      (trans (outBit-∘ Hᴾ R₂ x (Y₂ Y) (layer₂ n₂ Y) w)
             (outBit-μ Hᴾ (outBit R₂ x (Y₂ Y)) (layer₂ n₂ Y) w y[ w ] refl))

    ob₄ : ∀ x Y w → outBit R₄ x (Y₄ Y) w ≡ layer₂ n₂ Y w
    ob₄ x Y w = trans
      (cong odd (split-eval ((n₂ ℕ+ 0) ℕ+ n₂) 0 (out R₄ w) x (Y₄ Y)))
      (trans (outBit-∘ (Oᴾ (dualᴾ g)) R₃ x (Y₃ Y) (ε₂ Y) w)
        (trans (outBit-μ (Oᴾ (dualᴾ g)) (outBit R₃ x (Y₃ Y)) (ε₂ Y) w
                         x[ w ] refl)
               (ob₃ x Y w)))

  -- The circuit outputs the path of its last layer.

  outBit-HS : ∀ x Y w → outBit (HS g s) x Y w ≡ layer₃ n₂ Y w
  outBit-HS x Y w = trans
    (cong odd (split-eval (((n₂ ℕ+ 0) ℕ+ n₂) ℕ+ 0) n₂ (out (HS g s) w) x Y))
    (trans (outBit-∘ Hᴾ R₄ x (Y₄ Y) (layer₃ n₂ Y) w)
           (outBit-μ Hᴾ (outBit R₄ x (Y₄ Y)) (layer₃ n₂ Y) w y[ w ] refl))

  -- Its phase along a path is ½ times the sum of the five exponents,
  -- whose parity is hs-parity.

  private
    V : Assign n₂ → Assign (hs-norm n₂) → ℤ
    V x Y =
      (((eval hdotᴾ x (layer₁ n₂ Y)
         + eval (shiftᴾ s (mmᴾ g)) (layer₁ n₂ Y) none)
        + eval hdotᴾ (layer₁ n₂ Y) (layer₂ n₂ Y))
        + eval (dualᴾ g) (layer₂ n₂ Y) none)
        + eval hdotᴾ (layer₂ n₂ Y) (layer₃ n₂ Y)

    halves : ∀ h a b c d e →
             ((((h * a + h * b) + h * c) + h * d) + h * e) ≡
             h * ((((a + b) + c) + d) + e)
    halves = solve 6 (λ h a b c d e →
      ((((h :* a :+ h :* b) :+ h :* c) :+ h :* d) :+ h :* e) :=
      h :* ((((a :+ b) :+ c) :+ d) :+ e)) refl

    -- Each stage's phase, as ½ times its exponent on the layers.

    ph-H : ∀ (x′ : Assign n₂) {u u′ v v′ : Assign n₂} →
           (∀ i → u i ≡ u′ i) → (∀ i → v i ≡ v′ i) →
           eval (phase (Hᴾ {n₂})) u v ≡ ½ * eval hdotᴾ u′ v′
    ph-H _ {u} {u′} {v} {v′} u≗ v≗ = trans (eval-·ᴾ ½ hdotᴾ u v)
      (cong (½ *_) (eval-cong hdotᴾ {u} {u′} {v} {v′} u≗ v≗))

    ph-O : ∀ (E : Poly n₂ 0) {u u′ : Assign n₂} (ε : Assign 0) →
           (∀ i → u i ≡ u′ i) →
           eval (phase (Oᴾ E)) u ε ≡ ½ * eval E u′ none
    ph-O E {u} {u′} ε u≗ = trans (eval-·ᴾ ½ E u ε)
      (cong (½ *_) (eval-cong E {u} {u′} {ε} {none} u≗ (λ ())))

    phase-HS-value : ∀ x Y → eval (phase (HS g s)) x Y ≡ ½ * V x Y
    phase-HS-value x Y = trans
      (split-eval (((n₂ ℕ+ 0) ℕ+ n₂) ℕ+ 0) n₂ (phase (HS g s)) x Y)
      (trans (eval-∘ Hᴾ R₄ x (Y₄ Y) (layer₃ n₂ Y))
        (trans (cong₂ _+_ four
                 (ph-H x (ob₄ x Y) (λ _ → refl)))
               (halves ½ _ _ _ _ _)))
      where
      two : eval (phase R₂) x (Y₂ Y) ≡
            ½ * eval hdotᴾ x (layer₁ n₂ Y) +
            ½ * eval (shiftᴾ s (mmᴾ g)) (layer₁ n₂ Y) none
      two = trans (split-eval n₂ 0 (phase R₂) x (Y₂ Y))
        (trans (eval-∘ (Oᴾ (shiftᴾ s (mmᴾ g))) Hᴾ x (layer₁ n₂ Y) (ε₁ Y))
          (cong₂ _+_ (ph-H x (λ _ → refl) (λ _ → refl))
                     (ph-O (shiftᴾ s (mmᴾ g)) (ε₁ Y)
                           (λ w → outBit-μ Hᴾ x (layer₁ n₂ Y) w y[ w ] refl))))

      three : eval (phase R₃) x (Y₃ Y) ≡
              (½ * eval hdotᴾ x (layer₁ n₂ Y) +
               ½ * eval (shiftᴾ s (mmᴾ g)) (layer₁ n₂ Y) none) +
              ½ * eval hdotᴾ (layer₁ n₂ Y) (layer₂ n₂ Y)
      three = trans (split-eval (n₂ ℕ+ 0) n₂ (phase R₃) x (Y₃ Y))
        (trans (eval-∘ Hᴾ R₂ x (Y₂ Y) (layer₂ n₂ Y))
          (cong₂ _+_ two (ph-H x (ob₂ x Y) (λ _ → refl))))

      four : eval (phase R₄) x (Y₄ Y) ≡
             ((½ * eval hdotᴾ x (layer₁ n₂ Y) +
               ½ * eval (shiftᴾ s (mmᴾ g)) (layer₁ n₂ Y) none) +
              ½ * eval hdotᴾ (layer₁ n₂ Y) (layer₂ n₂ Y)) +
             ½ * eval (dualᴾ g) (layer₂ n₂ Y) none
      four = trans (split-eval ((n₂ ℕ+ 0) ℕ+ n₂) 0 (phase R₄) x (Y₄ Y))
        (trans (eval-∘ (Oᴾ (dualᴾ g)) R₃ x (Y₃ Y) (ε₂ Y))
          (cong₂ _+_ three (ph-O (dualᴾ g) (ε₂ Y) (ob₃ x Y))))

    odd-V : ∀ x Y → odd (V x Y) ≡ hs-parity x Y
    odd-V x Y = trans (odd-+ (((A + B) + C) + D) F) (cong₂ _xor_
      (trans (odd-+ ((A + B) + C) D) (cong₂ _xor_
        (trans (odd-+ (A + B) C) (cong₂ _xor_
          (trans (odd-+ A B) (cong₂ _xor_
            (odd-dotᴾ (λ i → x[ i ]) (λ i → y[ i ]) x y₁)
            (trans (bool-shiftᴾ s (mmᴾ g) y₁) (bool-mmᴾ g (y₁ ⊕ᵃ s)))))
          (odd-dotᴾ (λ i → x[ i ]) (λ i → y[ i ]) y₁ y₂)))
        (bool-dualᴾ g y₂)))
      (odd-dotᴾ (λ i → x[ i ]) (λ i → y[ i ]) y₂ y₃))
      where
      y₁ y₂ y₃ : Assign n₂
      y₁ = layer₁ n₂ Y
      y₂ = layer₂ n₂ Y
      y₃ = layer₃ n₂ Y

      A B C D F : ℤ
      A = eval hdotᴾ x y₁
      B = eval (shiftᴾ s (mmᴾ g)) y₁ none
      C = eval hdotᴾ y₁ y₂
      D = eval (dualᴾ g) y₂ none
      F = eval hdotᴾ y₂ y₃

  -- Modulo 1, the phase along a path is ½ hs-parity.

  phase-HS : ∀ x Y →
             pow M ∣ (eval (phase (HS g s)) x Y - ½ * [ hs-parity x Y ]ᶻ)
  phase-HS x Y = subst (λ t → pow M ∣ (t - ½ * [ hs-parity x Y ]ᶻ))
    (sym (phase-HS-value x Y))
    (subst (λ b → pow M ∣ (½ * V x Y - ½ * [ b ]ᶻ)) (odd-V x Y)
           (½-parity (V x Y)))


------------------------------------------------------------------------
-- The circuit on |0⟩, written out

-- The paper represents a path-sum by its phase modulo 1 and its outputs
-- modulo 2, and computes the path-sum of a circuit as polynomials
-- written out.  Any path-sum with the path variables of HS g s whose
-- outputs are the last layer's path and whose phase is ½ hs-parity
-- modulo 1 is, in that sense, the circuit on |0⟩: congruent to it,
-- coefficient by coefficient (Möbius inversion from the values).

module _ {m : ℕ} (g : Poly m 0) (s : Assign (m ℕ+ m)) where

  at0-HS-congruent :
    (ξ : PathSum (m ℕ+ m) k (hs-norm (m ℕ+ m))) →
    (∀ x Y w → outBit ξ x Y w ≡ layer₃ (m ℕ+ m) Y w) →
    (∀ x Y → pow M ∣ (eval (phase ξ) x Y - ½ * [ hs-parity g s 0ᵃ Y ]ᶻ)) →
    Congruent (at0 (HS g s)) ξ
  at0-HS-congruent ξ outs phs = outs′ , phs′
    where
    outs′ : ∀ w → out (at0 (HS g s)) w ≈[ + 2 ] out ξ w
    outs′ w = values⇒coefficientsᵐ (+ 2) (out (at0 (HS g s)) w -ᴾ out ξ w)
      (λ x Y → subst ((+ 2) ∣_)
        (sym (eval-−ᴾ (out (at0 (HS g s)) w) (out ξ w) x Y))
        (odd-≡ (eval (out (at0 (HS g s)) w) x Y) (eval (out ξ w) x Y)
          (trans (cong odd (eval-at0 (out (HS g s) w) x Y))
            (trans (outBit-HS g s 0ᵃ Y w) (sym (outs x Y w))))))

    phs′ : phase (at0 (HS g s)) ≈[ pow M ] phase ξ
    phs′ = values⇒coefficientsᵐ (pow M) (phase (at0 (HS g s)) -ᴾ phase ξ)
      (λ x Y → subst (pow M ∣_)
        (sym (trans (eval-−ᴾ (phase (at0 (HS g s))) (phase ξ) x Y)
                    (cong (_- eval (phase ξ) x Y)
                          (eval-at0 (phase (HS g s)) x Y))))
        (subst (pow M ∣_)
          (shape (eval (phase (HS g s)) 0ᵃ Y) (eval (phase ξ) x Y)
                 (½ * [ hs-parity g s 0ᵃ Y ]ᶻ))
          (∣m∣n⇒∣m-n (phase-HS g s 0ᵃ Y) (phs x Y))))
      where
      shape : ∀ a b t → (a - t) - (b - t) ≡ a - b
      shape = solve 3 (λ a b t → (a :- t) :- (b :- t) := a :- b) refl


------------------------------------------------------------------------
-- Powers of ζ against normalisations

-- These are PathSum.Identity's, which keeps them private.

private
  rot-√2 : ∀ e a → rot e (√2· a) ≐ √2· (rot e a)
  rot-√2 e a i = trans (rot-+ᴬ e (rot (+ c) a) (rot (- (+ c)) a) i)
                       (cong₂ _+_ (swap (+ c)) (swap (- (+ c))))
    where
    swap : ∀ d → rot e (rot d a) i ≡ rot d (rot e a) i
    swap d = trans (rot-comp e d a i)
      (trans (rot-exp a (+-comm e d) i) (sym (rot-comp d e a i)))

  rot-back : ∀ e → rot (- e) (zpow e) ≐ zpow 0ℤ
  rot-back e i =
    trans (rot-zpow (- e) e i) (cong (λ z → zpow z i) (+-inverseˡ e))

  -- √2^j ζ^0 is never zero.

  scale-zpow0≢0 : ∀ j → ¬ (scale j (zpow 0ℤ) ≐ 0ᴬ)
  scale-zpow0≢0 zero    eq = zpow-0≢0ᴬ eq
  scale-zpow0≢0 (suc j) eq = scale-zpow0≢0 j
    (√2·-injective (scale j (zpow 0ℤ)) 0ᴬ
      (λ i → trans (eq i) (sym (√2·-0ᴬ i))))

  -- Nor is a power of ζ ever √2^j for j at least one.

  zpow≢scale : ∀ (e : ℤ) j → ¬ (zpow e ≐ scale (suc j) (zpow 0ℤ))
  zpow≢scale e zero eq =
    2·≢scale-zpow0 (zpow (- e)) 1 (s≤s (s≤s z≤n)) two
    where
    rotated : zpow 0ℤ ≐ √2· (zpow (- e))
    rotated i = trans (sym (rot-back e i))
      (trans (rot-map (- e) eq i)
        (trans (rot-√2 (- e) (zpow 0ℤ) i)
          (√2·-map (λ i′ → trans (rot-zpow (- e) 0ℤ i′)
            (cong (λ z → zpow z i′) (+-identityʳ (- e)))) i)))

    two : ((+ 2) ·ᴬ zpow (- e)) ≐ scale 1 (zpow 0ℤ)
    two i = trans (sym (√2·-twice (zpow (- e)) i))
                  (√2·-map (λ i′ → sym (rotated i′)) i)
  zpow≢scale e (suc j) eq =
    2·≢scale-zpow0 (rot (- e) (scale j (zpow 0ℤ))) 0 (s≤s z≤n) two
    where
    two : ((+ 2) ·ᴬ rot (- e) (scale j (zpow 0ℤ))) ≐ scale 0 (zpow 0ℤ)
    two i = trans (sym (rot-·ᴬ (- e) (+ 2) (scale j (zpow 0ℤ)) i))
      (trans (sym (rot-map (- e)
        (λ i′ → trans (eq i′) (√2·-twice (scale j (zpow 0ℤ)) i′)) i))
        (rot-back e i))

  -- A coefficient of 1 means the exponent is a multiple of N.

  χ≡1 : ∀ z → χ z ≡ 1ℤ → (+ N) ∣ z
  χ≡1 z eq = aux ((+ N) ∣? z) ((+ N) ∣? (z - (+ H)))
    where
    aux : Dec ((+ N) ∣ z) → Dec ((+ N) ∣ (z - (+ H))) → (+ N) ∣ z
    aux (yes d) _       = d
    aux (no ¬d) (yes b) = contradiction (trans (sym (χ--1 ¬d b)) eq) λ ()
    aux (no ¬d) (no ¬b) = contradiction (trans (sym (χ-0 ¬d ¬b)) eq) λ ()

  -- ζ^e = √2^k ζ^0 forces k = 0 and e ≡ 0 modulo N.

  norm-zero : ∀ {k} (e : ℤ) → zpow e ≐ scale k (zpow 0ℤ) → k ≡ 0
  norm-zero {zero}  e _  = refl
  norm-zero {suc j} e eq = ⊥-elim (zpow≢scale e j eq)

  exponent-zero : ∀ {k} (e : ℤ) → zpow e ≐ scale k (zpow 0ℤ) → (+ N) ∣ e
  exponent-zero {suc j} e eq = ⊥-elim (zpow≢scale e j eq)
  exponent-zero {zero}  e eq =
    subst ((+ N) ∣_) (shape e index)
          (∣m∣n⇒∣m-n (χ≡1 _ (trans (eq 0ᶠ) zpow0-at-0)) (χ≡1 _ zpow0-at-0))
    where
    index : ℤ
    index = + toℕ 0ᶠ

    shape : ∀ u v → (u - v) - (0ℤ - v) ≡ u
    shape = solve 2 (λ u v → (u :- v) :- (con 0ℤ :- v) := u) refl

  -- A guarded amplitude whose guard is decided.

  if-true : {b : Bool} {a : Amp} → b ≡ true → (if b then a else 0ᴬ) ≐ a
  if-true {true} _ _ = refl

  if-false : {b : Bool} {a : Amp} → b ≡ false → (if b then a else 0ᴬ) ≐ 0ᴬ
  if-false {false} _ _ = refl

  -- A value of parity b differs from b by an even number.

  even-diff : ∀ v b → odd v ≡ b → (+ 2) ∣ (v - [ b ]ᶻ)
  even-diff v b eq with halve v
  ... | r , e = divides r (trans (cong (λ t → v - [ t ]ᶻ) (sym eq))
    (trans (cong (_- [ odd v ]ᶻ) e) (shape r [ odd v ]ᶻ)))
    where
    shape : ∀ u t → (u * (+ 2) + t) - t ≡ u * (+ 2)
    shape = solve 2 (λ u t → (u :* con (+ 2) :+ t) :- t := u :* con (+ 2))
                    refl

  -- The single path of a path-sum with no path variables.

  amp₀ : (ζ : PathSum n k 0) (x z : Assign n) →
         amp ζ x z ≐
         (if hits ζ x none z then zpow (eval (phase ζ) x none) else 0ᴬ)
  amp₀ ζ x z = Σᴮ-none
    (λ y → if hits ζ x y z then zpow (eval (phase ζ) x y) else 0ᴬ)
    (λ y → if-cong
      (hits-≗³ ζ {x} {x} {y} {none} {z} {z} (λ _ → refl) (λ ())
               (λ _ → refl))
      (zpow-≡ (eval-none (phase ζ) x y)))


------------------------------------------------------------------------
-- The specification, syntactically

-- A path-sum with no path variables that is equivalent to |x⟩ ↦ |s⟩
-- is |x⟩ ↦ |s⟩: no normalisation, the outputs s modulo 2, the phase 0
-- modulo 1, coefficient by coefficient.  At each input its single
-- path must reach s, since the specification's entry there is not 0,
-- and must carry the specification's amplitude, a power of ζ equal to
-- √2^k ζ^0.

spec-only-if : (s : Assign n) (ζ : PathSum n k 0) → ζ ≋ specᴾ s →
               (k ≡ 0) ×
               (∀ w → out ζ w ≈[ + 2 ] κ [ s w ]ᶻ) ×
               (phase ζ ≈[ pow M ] 0ᴾ)
spec-only-if {n} {k} s ζ ζ≋ = norm , outs , phs
  where
  column : ∀ x → amp ζ x s ≐ scale k 1ᴬ
  column x i = trans (ζ≋ x s i)
    (scale-map k (λ l → trans (amp-specᴾ s x s l)
                              (if-true (same-refl s) l)) i)

  e : Assign n → ℤ
  e x = eval (phase ζ) x none

  both : ∀ x → (hits ζ x none s ≡ true) × (zpow (e x) ≐ scale k 1ᴬ)
  both x = go (hits ζ x none s) refl
    where
    go : ∀ b → hits ζ x none s ≡ b →
         (hits ζ x none s ≡ true) × (zpow (e x) ≐ scale k 1ᴬ)
    go true  eq = eq , (λ i → trans (sym (if-true eq i))
                                    (trans (sym (amp₀ ζ x s i)) (column x i)))
    go false eq = ⊥-elim (scale-zpow0≢0 k (λ i → trans (sym (column x i))
                            (trans (amp₀ ζ x s i) (if-false eq i))))

  norm : k ≡ 0
  norm = norm-zero {k} (e 0ᵃ) (proj₂ (both 0ᵃ))

  outs : ∀ w → out ζ w ≈[ + 2 ] κ [ s w ]ᶻ
  outs w = values⇒coefficientsᵐ (+ 2) (out ζ w -ᴾ κ [ s w ]ᶻ) value
    where
    value : ∀ x y → (+ 2) ∣ eval (out ζ w -ᴾ κ [ s w ]ᶻ) x y
    value x y = subst ((+ 2) ∣_)
      (sym (trans (eval-−ᴾ (out ζ w) (κ [ s w ]ᶻ) x y)
                  (cong₂ _-_ (eval-none (out ζ w) x y) (eval-κ [ s w ]ᶻ x y))))
      (even-diff (eval (out ζ w) x none) (s w)
                 (hits-elim ζ x none s (proj₁ (both x)) w))

  phs : phase ζ ≈[ pow M ] 0ᴾ
  phs = values⇒coefficientsᵐ (pow M) (phase ζ -ᴾ 0ᴾ) value
    where
    value : ∀ x y → pow M ∣ eval (phase ζ -ᴾ 0ᴾ) x y
    value x y = subst (pow M ∣_)
      (sym (trans (eval-−ᴾ (phase ζ) 0ᴾ x y)
        (trans (cong₂ _-_ (eval-none (phase ζ) x y) (eval-0ᴾ x y))
               (+-identityʳ (e x)))))
      (exponent-zero {k} (e x) (proj₂ (both x)))


------------------------------------------------------------------------
-- Every complete reduction finds s

-- Whatever rules of figure 2 are applied, at whatever path variables,
-- a reduction of the circuit on |0⟩ that eliminates every path
-- variable ends at |x⟩ ↦ |s⟩.

hidden-shift-reduces : (g : Poly m 0) (s : Assign (m ℕ+ m)) {k′ : ℕ}
                       {ζ : PathSum (m ℕ+ m) k′ 0} →
                       at0 (HS g s) ⟶ᶠ* ζ →
                       (k′ ≡ 0) ×
                       (∀ w → out ζ w ≈[ + 2 ] κ [ s w ]ᶻ) ×
                       (phase ζ ≈[ pow M ] 0ᴾ)
hidden-shift-reduces {m} g s {k′} {ζ} steps = spec-only-if s ζ
  (≋-trans {ξ = ζ} {ζ = at0 (HS g s)} {χ = specᴾ s}
    (≋-sym {ξ = at0 (HS g s)} {ζ = ζ} (⟶ᶠ*-sound steps))
    (hidden-shift-≋ g s))

-- The same for a derivation in the paper's style, a column of lines
-- each obtained from the one before by a rule at the head
-- (PathSum.Reduction.General) or by rewriting the polynomials modulo 1
-- and 2 (PathSum.Reduction.Derivation), as PathSum.HiddenShift.Example
-- writes one.

hidden-shift-derives : (g : Poly m 0) (s : Assign (m ℕ+ m)) {k′ : ℕ}
                       {ζ : PathSum (m ℕ+ m) k′ 0} →
                       Derivation (at0 (HS g s)) ζ →
                       (k′ ≡ 0) ×
                       (∀ w → out ζ w ≈[ + 2 ] κ [ s w ]ᶻ) ×
                       (phase ζ ≈[ pow M ] 0ᴾ)
hidden-shift-derives {m} g s {k′} {ζ} d = spec-only-if s ζ
  (≋-trans {ξ = ζ} {ζ = at0 (HS g s)} {χ = specᴾ s}
    (≋-sym {ξ = at0 (HS g s)} {ζ = ζ} (derivation-sound d))
    (hidden-shift-≋ g s))
