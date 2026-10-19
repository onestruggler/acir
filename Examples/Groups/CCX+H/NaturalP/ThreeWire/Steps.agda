------------------------------------------------------------------------
-- Presentations of groups
--
-- The steps of the three-wire derivations.
--
-- A three-wire circuit is a list of theta-words and H's.  The group
-- acts on the lattices g E8; a word θ₁ H θ₂ H θ₃ goes two steps from E8,
-- and when it lands on a lattice at relative position (2, 0⁶) its
-- canonical form is φ CCZ ω (`CF`): θ₁ = φ ψ α with ψ in W(D8) and α
-- in A, α^H θ₂ = CCX β with β in A, and then H past α and β and CCZ
-- past ψ.  Two such words with one matrix have the same φ and so are
-- equal (L30).  A square of the contraction, θ₁ H θ₂ H ≈ θ₁′ H θ₂′ H r,
-- is that, for the words H θ₁′⁻¹ θ₁ H and θ₂′ H r H θ₂⁻¹ (`SQ`); a
-- backtrack, θ₁ H α H θ₂ with α in A, is H past α (`BT`).  Every check
-- is one fastCheck.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+H.NaturalP.ThreeWire.Steps where

open import Data.Bool.Base using (true)
open import Data.List.Base using (List ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using ([_]ʷ ; ε ; _•_)
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open import Examples.Groups.CCX+H.NaturalP.ThreeWire.Kit
open import Examples.Groups.CCX+H.NaturalP.ThreeWire.Letters
import Examples.Groups.CCX+HH.Natural.Syntactics as N
open import Examples.Groups.CCX+HH.Natural.Axioms using (ccx₀)

private
  module R3 = SR (PP.word-setoid (3 VRel,_===_))
  open R3

  c : Circuit 3
  c = Θ [ ccx₀ ]ʷ

------------------------------------------------------------------------
-- Canonical forms

record CFW (a₁ a₂ : N.Circuit 3) : Set where
  constructor cfw
  field
    φ   : N.Circuit 3
    ψ   : List WL
    α β : List AL
    c₁  : fastCheck a₁ (φ • (⌊ ψ ⌋ᵂ • ⌊ α ⌋ᴬ)) ≡ true
    c₂  : fastCheck (hcW α • a₂) ([ ccx₀ ]ʷ • ⌊ β ⌋ᴬ) ≡ true

ω : ∀ {a₁ a₂} → CFW a₁ a₂ → N.Circuit 3 → N.Circuit 3
ω w a₃ = zcW (CFW.ψ w) • (hcW (CFW.β w) • a₃)

CF : ∀ a₁ a₂ a₃ (w : CFW a₁ a₂) →
     3 ⊢ Θ a₁ • (H • (Θ a₂ • (H • Θ a₃))) ≈ Θ (CFW.φ w) • (CCZ • Θ (ω w a₃))
CF a₁ a₂ a₃ (cfw φ ψ α β c₁ c₂) = begin
  Θ a₁ • (H • (Θ a₂ • (H • Θ a₃)))
    ≈⟨ cong (Θstep a₁ (φ • (⌊ ψ ⌋ᵂ • ⌊ α ⌋ᴬ)) c₁) refl ⟩
  (Θ φ • (Θ ⌊ ψ ⌋ᵂ • Θ ⌊ α ⌋ᴬ)) • (H • (Θ a₂ • (H • Θ a₃)))
    ≈⟨ trans assoc (cong refl assoc) ⟩
  Θ φ • (Θ ⌊ ψ ⌋ᵂ • (Θ ⌊ α ⌋ᴬ • (H • (Θ a₂ • (H • Θ a₃)))))
    ≈⟨ cong refl (cong refl (sym assoc)) ⟩
  Θ φ • (Θ ⌊ ψ ⌋ᵂ • ((Θ ⌊ α ⌋ᴬ • H) • (Θ a₂ • (H • Θ a₃))))
    ≈⟨ cong refl (cong refl (cong (hc α) refl)) ⟩
  Θ φ • (Θ ⌊ ψ ⌋ᵂ • ((H • Θ (hcW α)) • (Θ a₂ • (H • Θ a₃))))
    ≈⟨ cong refl (cong refl (trans assoc (cong refl (sym assoc)))) ⟩
  Θ φ • (Θ ⌊ ψ ⌋ᵂ • (H • ((Θ (hcW α) • Θ a₂) • (H • Θ a₃))))
    ≈⟨ cong refl (cong refl (cong refl (cong (Θstep (hcW α • a₂) ([ ccx₀ ]ʷ • ⌊ β ⌋ᴬ) c₂) refl))) ⟩
  Θ φ • (Θ ⌊ ψ ⌋ᵂ • (H • ((c • Θ ⌊ β ⌋ᴬ) • (H • Θ a₃))))
    ≈⟨ cong refl (cong refl (cong refl (trans assoc (cong refl (sym assoc))))) ⟩
  Θ φ • (Θ ⌊ ψ ⌋ᵂ • (H • (c • ((Θ ⌊ β ⌋ᴬ • H) • Θ a₃))))
    ≈⟨ cong refl (cong refl (cong refl (cong refl (cong (hc β) refl)))) ⟩
  Θ φ • (Θ ⌊ ψ ⌋ᵂ • (H • (c • ((H • Θ (hcW β)) • Θ a₃))))
    ≈⟨ cong refl (cong refl (cong refl (cong refl assoc))) ⟩
  Θ φ • (Θ ⌊ ψ ⌋ᵂ • (H • (c • (H • (Θ (hcW β) • Θ a₃)))))
    ≈⟨ cong refl (cong refl (trans (cong refl (sym assoc)) (sym assoc))) ⟩
  Θ φ • (Θ ⌊ ψ ⌋ᵂ • (CCZ • (Θ (hcW β) • Θ a₃)))
    ≈⟨ cong refl (sym assoc) ⟩
  Θ φ • ((Θ ⌊ ψ ⌋ᵂ • CCZ) • (Θ (hcW β) • Θ a₃))
    ≈⟨ cong refl (cong (zc ψ) refl) ⟩
  Θ φ • ((CCZ • Θ (zcW ψ)) • (Θ (hcW β) • Θ a₃))
    ≈⟨ cong refl assoc ⟩
  Θ φ • (CCZ • (Θ (zcW ψ) • (Θ (hcW β) • Θ a₃)))
    ∎

------------------------------------------------------------------------
-- A square

SQ : ∀ (p₁ p₂ p₃ q₁ q₂ r t : N.Circuit 3)
     (wX : CFW ε (invN q₁ • p₁)) (wY : CFW q₂ r) →
     CFW.φ wX ≡ CFW.φ wY →
     fastCheck (ω wX ε) (ω wY (invN p₂)) ≡ true →
     fastCheck (r • p₃) t ≡ true →
     3 ⊢ Θ p₁ • (H • (Θ p₂ • (H • Θ p₃))) ≈ Θ q₁ • (H • (Θ q₂ • (H • Θ t)))
SQ p₁ p₂ p₃ q₁ q₂ r t wX wY eφ hω ht = begin
  Θ p₁ • (H • (Θ p₂ • (H • Θ p₃)))
    ≈⟨ cong (sym (cancel (Θ-inv-r q₁) (Θ p₁))) refl ⟩
  (Θ q₁ • (Θ (invN q₁) • Θ p₁)) • (H • (Θ p₂ • (H • Θ p₃)))
    ≈⟨ assoc ⟩
  Θ q₁ • (Θ (invN q₁ • p₁) • (H • (Θ p₂ • (H • Θ p₃))))
    ≈⟨ cong refl (sym (cancel H² _)) ⟩
  Θ q₁ • (H • (H • (Θ (invN q₁ • p₁) • (H • (Θ p₂ • (H • Θ p₃))))))
    ≈⟨ cong refl (cong refl (trans (cong refl (sym assoc)) (sym assoc))) ⟩
  Θ q₁ • (H • ((H • (Θ (invN q₁ • p₁) • H)) • (Θ p₂ • (H • Θ p₃))))
    ≈⟨ cong refl (cong refl (cong square refl)) ⟩
  Θ q₁ • (H • ((Θ q₂ • (H • (Θ r • (H • Θ (invN p₂))))) • (Θ p₂ • (H • Θ p₃))))
    ≈⟨ cong refl (cong refl (trans assoc (cong refl (trans assoc (cong refl (trans assoc (cong refl assoc))))))) ⟩
  Θ q₁ • (H • (Θ q₂ • (H • (Θ r • (H • (Θ (invN p₂) • (Θ p₂ • (H • Θ p₃))))))))
    ≈⟨ cong refl (cong refl (cong refl (cong refl (cong refl (cong refl (cancel (Θ-inv-l p₂) _)))))) ⟩
  Θ q₁ • (H • (Θ q₂ • (H • (Θ r • (H • (H • Θ p₃))))))
    ≈⟨ cong refl (cong refl (cong refl (cong refl (cong refl (cancel H² _))))) ⟩
  Θ q₁ • (H • (Θ q₂ • (H • (Θ r • Θ p₃))))
    ≈⟨ cong refl (cong refl (cong refl (cong refl (Θstep (r • p₃) t ht)))) ⟩
  Θ q₁ • (H • (Θ q₂ • (H • Θ t)))
    ∎
  where
  -- H θ H, the two canonical forms, and the word of wY.
  square : 3 ⊢ H • (Θ (invN q₁ • p₁) • H) ≈ Θ q₂ • (H • (Θ r • (H • Θ (invN p₂))))
  square = begin
    H • (Θ (invN q₁ • p₁) • H)
      ≈⟨ sym (trans left-unit (cong refl (cong refl right-unit))) ⟩
    Θ ε • (H • (Θ (invN q₁ • p₁) • (H • Θ ε)))
      ≈⟨ CF ε (invN q₁ • p₁) ε wX ⟩
    Θ (CFW.φ wX) • (CCZ • Θ (ω wX ε))
      ≈⟨ cong (PB.refl' (3 VRel,_===_) (Eq.cong Θ eφ)) (cong refl (Θstep (ω wX ε) (ω wY (invN p₂)) hω)) ⟩
    Θ (CFW.φ wY) • (CCZ • Θ (ω wY (invN p₂)))
      ≈⟨ sym (CF q₂ r (invN p₂) wY) ⟩
    Θ q₂ • (H • (Θ r • (H • Θ (invN p₂))))
      ∎
    where import Presentation.Base as PB

------------------------------------------------------------------------
-- A backtrack

BT : ∀ (p s q t : N.Circuit 3) (α : List AL) →
     fastCheck s ⌊ α ⌋ᴬ ≡ true → fastCheck (p • (hcW α • q)) t ≡ true →
     3 ⊢ Θ p • (H • (Θ s • (H • Θ q))) ≈ Θ t
BT p s q t α hs ht = begin
  Θ p • (H • (Θ s • (H • Θ q)))
    ≈⟨ cong refl (cong refl (cong (Θstep s ⌊ α ⌋ᴬ hs) refl)) ⟩
  Θ p • (H • (Θ ⌊ α ⌋ᴬ • (H • Θ q)))
    ≈⟨ cong refl (cong refl (sym assoc)) ⟩
  Θ p • (H • ((Θ ⌊ α ⌋ᴬ • H) • Θ q))
    ≈⟨ cong refl (cong refl (cong (hc α) refl)) ⟩
  Θ p • (H • ((H • Θ (hcW α)) • Θ q))
    ≈⟨ cong refl (cong refl assoc) ⟩
  Θ p • (H • (H • (Θ (hcW α) • Θ q)))
    ≈⟨ cong refl (cancel H² _) ⟩
  Θ (p • (hcW α • q))
    ≈⟨ Θstep (p • (hcW α • q)) t ht ⟩
  Θ t
    ∎

------------------------------------------------------------------------
-- The bookkeeping steps

-- Two theta-words side by side.
MG : ∀ (a b t : N.Circuit 3) → fastCheck (a • b) t ≡ true → 3 ⊢ Θ a • Θ b ≈ Θ t
MG a b t h = Θstep (a • b) t h

-- A theta-word replaced by one with the same matrix.
TH : ∀ (a t : N.Circuit 3) → fastCheck a t ≡ true → 3 ⊢ Θ a ≈ Θ t
TH = Θstep
