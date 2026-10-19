------------------------------------------------------------------------
-- Presentations of groups
--
-- Three-wire circuits of the CCX+H rules as theta-words and H.
--
-- A theta-word is a CCX+HH circuit read through θ (HH ↦ H H↑, through
-- NaturalP's ι).  Two with one matrix are equal (`Θstep`): CCX+HH is
-- complete on three wires (Natural/ThreeWire), θ carries its
-- derivations here (Transfer), and the matrices are compared fast
-- (Natural/ThreeWire/Fast).  What is left of a three-wire derivation is
-- moving the single H on wire 0, which is H₀ below:
--
--   * past the letters of A, the CCX-free CCX+HH circuits, each to a
--     theta-word (`hc`: H X H = H H↑ X H H↑, and so on);
--   * past CCZ = H CCX H, which conjugates each of the nine letters of
--     W(D8) to a theta-word (`zc`): for every letter but CCX, CCX x^H CCX
--     is again in A; for CCX it is the rule CCXH⁴.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.NaturalP.ThreeWire.Kit where

open import Data.Bool.Base using (Bool ; true)
open import Data.List.Base using (List ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open import Examples.Groups.CCX+H.NaturalP.Schema public
open import Examples.Groups.CCX+H.NaturalP.Theta using (θ)
open import Examples.Groups.CCX+H.NaturalP.Transfer using (θ-cong)
import Examples.Groups.CCX+H.NaturalP.Syntactics as NH
import Examples.Groups.CCX+HH.Natural.Syntactics as N
open import Examples.Groups.CCX+HH.Natural.Axioms using (x₀ ; x₁ ; x₂ ; cx₀ ; cx₁ ; hh₀ ; hh₁ ; ccx₀)
import Examples.Groups.CCX+HH.NaturalP.Bridge as PBr
import Examples.Groups.CCX+HH.NaturalP.Converse as Conv
import Examples.Groups.CCX+HH.NaturalP.Schema as PS
import Examples.Groups.CCX+HH.Natural.ThreeWire.Complete as W3
open import Examples.Groups.CCX+HH.Natural.ThreeWire.Fast public using (fastCheck)
open import Examples.Groups.CCX+HH.Natural.ThreeWire.Fast using (fast-sound)

open PB (3 VRel,_===_) public using (refl ; sym ; trans ; cong ; assoc ; left-unit ; right-unit)

private
  module R3 = SR (PP.word-setoid (3 VRel,_===_))
  open R3

------------------------------------------------------------------------
-- Theta-words

Θ : N.Circuit 3 → Circuit 3
Θ w = θ (PBr.ι w)

Θstep : ∀ (u v : N.Circuit 3) → fastCheck u v ≡ true → 3 ⊢ Θ u ≈ Θ v
Θstep u v h = θ-cong (PS.emb (Conv.ι-cong (W3.complete {u} {v} (fast-sound u v h))))

H² : 3 ⊢ H • H ≈ ε
H² = PB.axiom (srel (srel (nh NH.H²)))

private
  H²₂ : 2 ⊢ H • H ≈ ε
  H²₂ = PB.axiom (srel (srel (nh NH.H²)))

  H²₁ : 1 ⊢ H • H ≈ ε
  H²₁ = PB.axiom (srel (srel (nh NH.H²)))

  -- H on wire 1, and on wire 2, are involutions.
  H↑² : 3 ⊢ H ↑ • H ↑ ≈ ε
  H↑² = lemma-cong↑ (H • H) ε H²₂

  H↑↑² : 3 ⊢ H ↑ ↑ • H ↑ ↑ ≈ ε
  H↑↑² = lemma-cong↑ (H ↑ • H ↑) ε (lemma-cong↑ (H • H) ε H²₁)

-- Cancelling an involution in the middle of a word.
cancel : ∀ {a b : Circuit 3} → 3 ⊢ a • b ≈ ε → ∀ x → 3 ⊢ a • (b • x) ≈ x
cancel e x = trans (sym assoc) (trans (cong e refl) left-unit)

------------------------------------------------------------------------
-- Inverses

invN : N.Circuit 3 → N.Circuit 3
invN [ g ]ʷ  = [ g ]ʷ
invN ε       = ε
invN (u • v) = invN v • invN u

private
  letter-inv : ∀ g → 3 ⊢ Θ [ g ]ʷ • Θ [ g ]ʷ ≈ ε
  letter-inv x₀   = Θstep ([ x₀ ]ʷ • [ x₀ ]ʷ) ε Eq.refl
  letter-inv x₁   = Θstep ([ x₁ ]ʷ • [ x₁ ]ʷ) ε Eq.refl
  letter-inv x₂   = Θstep ([ x₂ ]ʷ • [ x₂ ]ʷ) ε Eq.refl
  letter-inv cx₀  = Θstep ([ cx₀ ]ʷ • [ cx₀ ]ʷ) ε Eq.refl
  letter-inv cx₁  = Θstep ([ cx₁ ]ʷ • [ cx₁ ]ʷ) ε Eq.refl
  letter-inv hh₀  = Θstep ([ hh₀ ]ʷ • [ hh₀ ]ʷ) ε Eq.refl
  letter-inv hh₁  = Θstep ([ hh₁ ]ʷ • [ hh₁ ]ʷ) ε Eq.refl
  letter-inv ccx₀ = Θstep ([ ccx₀ ]ʷ • [ ccx₀ ]ʷ) ε Eq.refl
  letter-inv (N.gate₀ ())
  letter-inv (N.gate₀ () N.↥)
  letter-inv (N.gate₀ () N.↥ N.↥)
  letter-inv (N.gate₀ () N.↥ N.↥ N.↥)

Θ-inv-r : ∀ w → 3 ⊢ Θ w • Θ (invN w) ≈ ε
Θ-inv-r [ g ]ʷ  = letter-inv g
Θ-inv-r ε       = left-unit
Θ-inv-r (u • v) = trans assoc (trans (cong refl (cancel (Θ-inv-r v) (Θ (invN u)))) (Θ-inv-r u))

Θ-inv-l : ∀ w → 3 ⊢ Θ (invN w) • Θ w ≈ ε
Θ-inv-l [ g ]ʷ  = letter-inv g
Θ-inv-l ε       = left-unit
Θ-inv-l (u • v) = trans assoc (trans (cong refl (cancel (Θ-inv-l u) (Θ v))) (Θ-inv-l v))

------------------------------------------------------------------------
-- The letters of A, and H past them

data AL : Set where
  ax₀ ax₁ ax₂ acx₀ acx₁ ahh₀ ahh₁ : AL

gA : AL → N.Gen 3
gA ax₀  = x₀
gA ax₁  = x₁
gA ax₂  = x₂
gA acx₀ = cx₀
gA acx₁ = cx₁
gA ahh₀ = hh₀
gA ahh₁ = hh₁

⌊_⌋ᴬ : List AL → N.Circuit 3
⌊ [] ⌋ᴬ     = ε
⌊ a ∷ as ⌋ᴬ = [ gA a ]ʷ • ⌊ as ⌋ᴬ

-- H a H, as a theta-word.
HC : AL → N.Circuit 3
HC ax₀  = [ hh₀ ]ʷ • ([ x₀ ]ʷ • [ hh₀ ]ʷ)
HC ax₁  = [ x₁ ]ʷ
HC ax₂  = [ x₂ ]ʷ
HC acx₀ = [ hh₀ ]ʷ • ([ hh₁ ]ʷ • ([ cx₀ ]ʷ • ([ hh₀ ]ʷ • [ hh₁ ]ʷ)))
HC acx₁ = [ cx₁ ]ʷ
HC ahh₀ = [ hh₀ ]ʷ
HC ahh₁ = [ hh₁ ]ʷ

hcW : List AL → N.Circuit 3
hcW []       = ε
hcW (a ∷ as) = HC a • hcW as

private
  -- H on wire 1 and on wire 2 past H, X and CX on the bottom wires.
  H↑-H : 3 ⊢ H ↑ • H ≈ H • H ↑
  H↑-H = comm-gate₁-w↑ H-gate H

  H↑-X : 3 ⊢ H ↑ • X ≈ X • H ↑
  H↑-X = comm-gate₁-w↑ X-gate H

  H↑↑-H : 3 ⊢ H ↑ ↑ • H ≈ H • H ↑ ↑
  H↑↑-H = comm-gate₁-w↑ H-gate (H ↑)

  H↑↑-CX : 3 ⊢ H ↑ ↑ • CX ≈ CX • H ↑ ↑
  H↑↑-CX = comm-gate₂-w↑↑ CX-gate H

  hc-x₀ : 3 ⊢ X • H ≈ H • ((H • H ↑) • (X • (H • H ↑)))
  hc-x₀ = sym (begin
    H • ((H • H ↑) • (X • (H • H ↑)))      ≈⟨ cong refl assoc ⟩
    H • (H • (H ↑ • (X • (H • H ↑))))      ≈⟨ cancel H² _ ⟩
    H ↑ • (X • (H • H ↑))                  ≈⟨ sym assoc ⟩
    (H ↑ • X) • (H • H ↑)                  ≈⟨ cong H↑-X refl ⟩
    (X • H ↑) • (H • H ↑)                  ≈⟨ assoc ⟩
    X • (H ↑ • (H • H ↑))                  ≈⟨ cong refl (sym assoc) ⟩
    X • ((H ↑ • H) • H ↑)                  ≈⟨ cong refl (cong H↑-H refl) ⟩
    X • ((H • H ↑) • H ↑)                  ≈⟨ cong refl assoc ⟩
    X • (H • (H ↑ • H ↑))                  ≈⟨ cong refl (cong refl H↑²) ⟩
    X • (H • ε)                            ≈⟨ cong refl right-unit ⟩
    X • H                                  ∎)

  hc-cx₀ : 3 ⊢ CX • H ≈ H • ((H • H ↑) • ((H ↑ • H ↑ ↑) • (CX • ((H • H ↑) • (H ↑ • H ↑ ↑)))))
  hc-cx₀ = sym (begin
    H • ((H • H ↑) • ((H ↑ • H ↑ ↑) • (CX • ((H • H ↑) • (H ↑ • H ↑ ↑)))))
      ≈⟨ cong refl assoc ⟩
    H • (H • (H ↑ • ((H ↑ • H ↑ ↑) • (CX • ((H • H ↑) • (H ↑ • H ↑ ↑))))))
      ≈⟨ cancel H² _ ⟩
    H ↑ • ((H ↑ • H ↑ ↑) • (CX • ((H • H ↑) • (H ↑ • H ↑ ↑))))
      ≈⟨ cong refl assoc ⟩
    H ↑ • (H ↑ • (H ↑ ↑ • (CX • ((H • H ↑) • (H ↑ • H ↑ ↑)))))
      ≈⟨ cancel H↑² _ ⟩
    H ↑ ↑ • (CX • ((H • H ↑) • (H ↑ • H ↑ ↑)))
      ≈⟨ cong refl (cong refl assoc) ⟩
    H ↑ ↑ • (CX • (H • (H ↑ • (H ↑ • H ↑ ↑))))
      ≈⟨ cong refl (cong refl (cong refl (cancel H↑² _))) ⟩
    H ↑ ↑ • (CX • (H • H ↑ ↑))
      ≈⟨ sym assoc ⟩
    (H ↑ ↑ • CX) • (H • H ↑ ↑)
      ≈⟨ cong H↑↑-CX refl ⟩
    (CX • H ↑ ↑) • (H • H ↑ ↑)
      ≈⟨ assoc ⟩
    CX • (H ↑ ↑ • (H • H ↑ ↑))
      ≈⟨ cong refl (sym assoc) ⟩
    CX • ((H ↑ ↑ • H) • H ↑ ↑)
      ≈⟨ cong refl (cong H↑↑-H refl) ⟩
    CX • ((H • H ↑ ↑) • H ↑ ↑)
      ≈⟨ cong refl assoc ⟩
    CX • (H • (H ↑ ↑ • H ↑ ↑))
      ≈⟨ cong refl (cong refl H↑↑²) ⟩
    CX • (H • ε)
      ≈⟨ cong refl right-unit ⟩
    CX • H ∎)

  hc-hh₀ : 3 ⊢ (H • H ↑) • H ≈ H • (H • H ↑)
  hc-hh₀ = trans assoc (cong refl H↑-H)

hc₁ : ∀ a → 3 ⊢ Θ [ gA a ]ʷ • H ≈ H • Θ (HC a)
hc₁ ax₀  = hc-x₀
hc₁ ax₁  = comm-gate₁-w↑ H-gate X
hc₁ ax₂  = comm-gate₁-w↑ H-gate (X ↑)
hc₁ acx₀ = hc-cx₀
hc₁ acx₁ = comm-gate₁-w↑ H-gate CX
hc₁ ahh₀ = hc-hh₀
hc₁ ahh₁ = comm-gate₁-w↑ H-gate (H • H ↑)

hc : ∀ α → 3 ⊢ Θ ⌊ α ⌋ᴬ • H ≈ H • Θ (hcW α)
hc []       = trans left-unit (sym right-unit)
hc (a ∷ as) = begin
  (Θ [ gA a ]ʷ • Θ ⌊ as ⌋ᴬ) • H            ≈⟨ assoc ⟩
  Θ [ gA a ]ʷ • (Θ ⌊ as ⌋ᴬ • H)            ≈⟨ cong refl (hc as) ⟩
  Θ [ gA a ]ʷ • (H • Θ (hcW as))           ≈⟨ sym assoc ⟩
  (Θ [ gA a ]ʷ • H) • Θ (hcW as)           ≈⟨ cong (hc₁ a) refl ⟩
  (H • Θ (HC a)) • Θ (hcW as)              ≈⟨ assoc ⟩
  H • (Θ (HC a) • Θ (hcW as))              ∎

-- The same, the other way round.
hc′ : ∀ α → 3 ⊢ H • Θ ⌊ α ⌋ᴬ ≈ Θ (hcW α) • H
hc′ α = begin
  H • Θ ⌊ α ⌋ᴬ                              ≈⟨ sym right-unit ⟩
  (H • Θ ⌊ α ⌋ᴬ) • ε                        ≈⟨ cong refl (sym H²) ⟩
  (H • Θ ⌊ α ⌋ᴬ) • (H • H)                  ≈⟨ assoc ⟩
  H • (Θ ⌊ α ⌋ᴬ • (H • H))                  ≈⟨ cong refl (sym assoc) ⟩
  H • ((Θ ⌊ α ⌋ᴬ • H) • H)                  ≈⟨ cong refl (cong (hc α) refl) ⟩
  H • ((H • Θ (hcW α)) • H)                 ≈⟨ cong refl assoc ⟩
  H • (H • (Θ (hcW α) • H))                 ≈⟨ cancel H² _ ⟩
  Θ (hcW α) • H                             ∎
