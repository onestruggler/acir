------------------------------------------------------------------------
-- Presentations of groups
--
-- The involutive automorphism of the HH group given by conjugation by
-- H on wire zero.  Together with the unique decomposition this gives
-- the semidirect product law HH ⋊ C₂ on every width at least four.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _+_)

module Examples.Groups.CCX+H.GeneralN.HadamardAction (n : ℕ) where

open import Data.Bool.Base using (Bool ; false ; true ; _xor_)
open import Data.Product.Base using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)
import Presentation.Base as PB
import Presentation.Properties as PP
import Examples.Groups.CCX+H.Syntactics as H
import Examples.Groups.CCX+H.Presentation as P
import Examples.Groups.CCX+H.GeneralN.HadamardDecomposition as Decomposition
import Examples.Groups.CCX+H.GeneralN.HadamardParity as Parity
import Examples.Groups.CCX+H.GeneralN.GateInvolutions as Involutions
import Examples.Groups.CCX+HH.Syntactics as HH
import Examples.Groups.CCX+HH.GeneralN.Presentation as DyadicPresentation
import Examples.Groups.CCX+HH.GeneralN.HadamardEmbedding as Embed

width = 4 + n
module D = Decomposition n
module DP = DyadicPresentation n
private
  module HP = PB (P.Relations width)
  open PP (P.Relations width) using (word-setoid)
  open PP.Pattern-Assoc (P.Relations width) using (by-passoc ; □)
  open HP hiding (_===_)
  open import Relation.Binary.Reasoning.Setoid word-setoid

  preserves : ∀ {u v : HH.Circuit width} → u DP.≈ v → Embed.embed u ≈ Embed.embed v
  preserves {u} {v} eq = P.complete width
    (Embed.preserve {u = u} {v = v} (DP.sound eq))

  reflects : ∀ {u v : HH.Circuit width} → Embed.embed u ≈ Embed.embed v → u DP.≈ v
  reflects {u} {v} eq = DP.complete
    (Embed.reflect {u = u} {v = v} (P.sound width eq))

  h² : H.H • H.H ≈ ε
  h² = P.complete width {u = H.H • H.H} {v = ε}
    (Involutions.matrix-involutive {n = width} (H.gate₁ H.H-gate))

  conjugate-even : ∀ (u : HH.Circuit width) → Parity.parity (H.H • Embed.embed u • H.H) ≡ false
  conjugate-even u = Eq.cong (λ b → true xor (b xor true)) (Parity.expanded u)

α : HH.Circuit width → HH.Circuit width
α u = proj₁ (D.even-body (H.H • Embed.embed u • H.H) (conjugate-even u))

α-correct : ∀ u → width P.⊢ H.H • Embed.embed u • H.H ≈ Embed.embed (α u)
α-correct u = proj₂ (D.even-body (H.H • Embed.embed u • H.H) (conjugate-even u))

α-cong : ∀ {u v} → u DP.≈ v → α u DP.≈ α v
α-cong {u} {v} eq = reflects (trans (sym (α-correct u))
  (trans (cong refl (cong (preserves eq) refl)) (α-correct v)))

α-involutive : ∀ u → α (α u) DP.≈ u
α-involutive u = reflects (begin
  Embed.embed (α (α u))                 ≈⟨ sym (α-correct (α u)) ⟩
  H.H • Embed.embed (α u) • H.H         ≈⟨ cong refl (cong (sym (α-correct u)) refl) ⟩
  H.H • (H.H • Embed.embed u • H.H) • H.H
                                        ≈⟨ by-passoc (□ • (□ • □ • □) • □)
                                             ((□ • □) • □ • (□ • □)) Eq.refl ⟩
  (H.H • H.H) • Embed.embed u • (H.H • H.H)
                                        ≈⟨ cong h² (cong refl h²) ⟩
  ε • Embed.embed u • ε                 ≈⟨ trans left-unit right-unit ⟩
  Embed.embed u                         ∎)

α-product : ∀ u v → α (u • v) DP.≈ (α u • α v)
α-product u v = reflects (begin
  Embed.embed (α (u • v))               ≈⟨ sym (α-correct (u • v)) ⟩
  H.H • (Embed.embed u • Embed.embed v) • H.H
                                        ≈⟨ by-passoc (□ • (□ • □) • □)
                                             ((□ • □) • (□ • □)) Eq.refl ⟩
  (H.H • Embed.embed u) • (Embed.embed v • H.H)
                                        ≈⟨ cong refl (sym left-unit) ⟩
  (H.H • Embed.embed u) • (ε • (Embed.embed v • H.H))
                                        ≈⟨ cong refl (cong (sym h²) refl) ⟩
  (H.H • Embed.embed u) • ((H.H • H.H) • (Embed.embed v • H.H))
                                        ≈⟨ by-passoc ((□ • □) • ((□ • □) • (□ • □)))
                                             ((□ • □ • □) • (□ • □ • □)) Eq.refl ⟩
  (H.H • Embed.embed u • H.H) • (H.H • Embed.embed v • H.H)
                                        ≈⟨ cong (α-correct u) (α-correct v) ⟩
  Embed.embed (α u) • Embed.embed (α v)  ∎)

α-unit : α ε DP.≈ ε
α-unit = reflects (trans (sym (α-correct ε))
  (trans (cong refl left-unit) h²))

twist : Bool → HH.Circuit width → HH.Circuit width
twist false u = u
twist true u = α u

twist-add : ∀ b c u → twist b (twist c u) DP.≈ twist (b xor c) u
twist-add false false u = PB.refl
twist-add false true u = PB.refl
twist-add true false u = PB.refl
twist-add true true u = α-involutive u

private
  tail-product : ∀ b c → D.tail b • D.tail c ≈ D.tail (b xor c)
  tail-product false false = left-unit
  tail-product false true = left-unit
  tail-product true false = right-unit
  tail-product true true = h²

  move-tail : ∀ b v → D.tail b • Embed.embed v ≈ Embed.embed (twist b v) • D.tail b
  move-tail false v = trans left-unit (sym right-unit)
  move-tail true v = begin
    H.H • Embed.embed v                 ≈⟨ sym right-unit ⟩
    (H.H • Embed.embed v) • ε           ≈⟨ cong refl (sym h²) ⟩
    (H.H • Embed.embed v) • (H.H • H.H) ≈⟨ by-passoc ((□ • □) • (□ • □))
                                             ((□ • □ • □) • □) Eq.refl ⟩
    (H.H • Embed.embed v • H.H) • H.H   ≈⟨ cong (α-correct v) refl ⟩
    Embed.embed (α v) • H.H             ∎

Factor : Set
Factor = HH.Circuit width × Bool

realise : Factor → H.Circuit width
realise (u , b) = Embed.embed u • D.tail b

infixr 7 _⋆_
_⋆_ : Factor → Factor → Factor
(u , b) ⋆ (v , c) = (u • twist b v) , (b xor c)

-- The usual semidirect product multiplication, proved in the circuit
-- theory.  Decomposition.decompose is surjectivity and .unique is
-- injectivity modulo equality of the HH component.
realise-product : ∀ a b → width P.⊢ realise a • realise b ≈ realise (a ⋆ b)
realise-product (u , b) (v , c) = begin
  (Embed.embed u • D.tail b) • (Embed.embed v • D.tail c)
                                         ≈⟨ by-passoc ((□ • □) • (□ • □))
                                              (□ • (□ • □) • □) Eq.refl ⟩
  Embed.embed u • (D.tail b • Embed.embed v) • D.tail c
                                         ≈⟨ cong refl (cong (move-tail b v) refl) ⟩
  Embed.embed u • (Embed.embed (twist b v) • D.tail b) • D.tail c
                                         ≈⟨ by-passoc (□ • (□ • □) • □)
                                              ((□ • □) • (□ • □)) Eq.refl ⟩
  (Embed.embed u • Embed.embed (twist b v)) • (D.tail b • D.tail c)
                                         ≈⟨ cong refl (tail-product b c) ⟩
  Embed.embed (u • twist b v) • D.tail (b xor c)
                                         ∎
