------------------------------------------------------------------------
-- Presentations of groups
--
-- Every H circuit on at least four wires is an HH circuit followed by
-- at most one H on wire zero.  This is a constructive decomposition,
-- using the source's dyadic/H normal form and charge-zero synthesis.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _+_)

module Examples.Groups.CCX+H.GeneralN.HadamardDecomposition (n : ℕ) where

open import Data.Nat.Base using (zero ; suc ; _*_ ; _<_)
  renaming (_^_ to _^ℕ_)
import Data.Nat.Properties as NP
open import Data.Bool.Base using (Bool ; false ; true)
open import Data.Product.Base using (Σ ; _,_ ; _×_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; ε ; _•_)
open import Quantum.Synthesis.Matrix using (_·*·_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring using (RingD)
import Presentation.Base as PB
import Presentation.GroupLike as GL
import Examples.Groups.CCX+H.Syntactics as H
import Examples.Groups.CCX+H.Presentation as P
import Examples.Groups.CCX+H.Orthogonal as Orthogonal
import Examples.Groups.CCX+H.GeneralN.Semantics as Sem
import Examples.Groups.CCX+H.GeneralN.PhysicalSemantics as Physical
import Examples.Groups.CCX+H.GeneralN.Action as Action
import Examples.Groups.CCX+H.GeneralN.Generation as Generation
import Examples.Groups.CCX+H.GeneralN.HadamardEmbedding as Embed
import Examples.Groups.CCX+H.GeneralN.HadamardParity as Parity
import Examples.Groups.CCX+HH.Syntactics as HH
import Examples.Groups.CCX+HH.GeneralN.Generation as DyadicGeneration
import Examples.Groups.CCX+HH.GeneralN.Presentation as DyadicPresentation
import Examples.Groups.CCX+HH.GeneralN.HadamardEmbedding as PhysicalEmbed
import Examples.Groups.CCX+HH.Subgroup.Action as DyadicAction
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as U
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as S
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Normal as Normal
open Action using (Coset ; c00 ; c10 ; c11 ; c01)

width = 4 + n
k = 2 ^ℕ (3 + n)
N = k * 2

module C = Sem.At (3 + n)
module G = Generation n
module DG = DyadicGeneration n
module DP = DyadicPresentation n
private module Group = GL.Group-Lemmas (P.Relations width) (Orthogonal.grouplike width)
private
  module A = PB (T._===ᴸ_ {N})
  module M = S.Dim k
  module Charge = Action.At N

  dimension : 2 ^ℕ width ≡ N
  dimension = NP.*-comm 2 k

  source-tail : ∀ {j} → Bool → Word (T.Genᴸ j)
  source-tail false = ε
  source-tail true = T.H

  SourceNF : ∀ j → Word (T.Genᴸ (j * 2)) → Set
  SourceNF j w = Σ (Word (U.Gen (j * 2))) λ d → Σ Bool λ b →
    PB._≈_ (T._===ᴸ_ {j * 2}) w (T.⌊ d ⌋ʷ • source-tail b)

  normal-tail : ∀ j b → Normal.Hᵇ j b ≡ source-tail b
  normal-tail j false = Eq.refl
  normal-tail j true = Eq.refl

  convert-normal : ∀ j w → Normal.NF j w → SourceNF (suc j) w
  convert-normal j w (d , b , eq) = d , b , PB.trans eq
    (PB.cong PB.refl (PB.refl' T._===ᴸ_ (normal-tail j b)))

  source-normal : ∀ j → 0 < j → (w : Word (T.Genᴸ (j * 2))) → SourceNF j w
  source-normal zero () w
  source-normal (suc j) positive w = convert-normal j w (Normal.nf j w)

  tail-closed : ∀ c b → Charge.state c (source-tail b) ≡ c00 → c ≡ c00
  tail-closed c false eq = eq
  tail-closed c00 true eq = Eq.refl
  tail-closed c10 true ()
  tail-closed c11 true ()
  tail-closed c01 true ()

  dyadic-closed : ∀ d b → Charge.state c00 (T.⌊ d ⌋ʷ • source-tail b) ≡ c00 →
    DyadicAction.At.state N c00 d ≡ c00
  dyadic-closed d b eq = Eq.trans (Eq.sym (Charge.state-lift c00 d))
    (tail-closed (Charge.state c00 T.⌊ d ⌋ʷ) b eq)

  cast-state : ∀ {j l} (p : j ≡ l) c w →
    DyadicAction.At.state l c (Sem.cast-dyadic p w) ≡ DyadicAction.At.state j c w
  cast-state Eq.refl c w = Eq.refl

  cast-back : ∀ {j l} (p : j ≡ l) (d : Word (U.Gen l)) →
    Sem.cast-word p T.⌊ Sem.cast-dyadic (Eq.sym p) d ⌋ʷ ≡ T.⌊ d ⌋ʷ
  cast-back Eq.refl d = Eq.refl

  cast-H : ∀ {j l} (p : j ≡ l) → Sem.cast-word p (ε • T.H) ≡ ε • T.H
  cast-H Eq.refl = Eq.refl

  H-correct : C.interpret H.H ≡ M.⟦ T.H ⟧ᴸ
  H-correct = Eq.trans (Eq.sym (C.encoding-correct H.H))
    (Eq.trans (Eq.cong M.⟦_⟧ᴸ (cast-H dimension))
      (S.soundness k {w = ε • T.H} {v = T.H} A.left-unit))

tail : Bool → H.Circuit width
tail = Parity.tail

private
  tail-correct : ∀ b → C.interpret (tail b) ≡ M.⟦ source-tail b ⟧ᴸ
  tail-correct false = Eq.refl
  tail-correct true = H-correct

record Decomposition (w : H.Circuit width) : Set where
  field
    body : HH.Circuit width
    bit : Bool
    correct : width P.⊢ w ≈ Embed.embed body • tail bit

private
  assemble : ∀ w → SourceNF k (C.compile w) → Decomposition w
  assemble w (d , b , normal) = record
    { body = body
    ; bit = b
    ; correct = P.complete width
        (Physical.At.forward (3 + n) {w} {Embed.embed body • tail b} matrix-correct)
    }
    where
    closed : Charge.state c00 (C.compile w) ≡ c00
    closed = G.necessary (C.compile w) w (Eq.sym (C.encoding-correct w))

    d-closed : DyadicAction.At.state N c00 d ≡ c00
    d-closed = dyadic-closed d b (Eq.trans (Eq.sym (Charge.state-cong c00 normal)) closed)

    dyadic : Word (U.Gen (2 ^ℕ width))
    dyadic = Sem.cast-dyadic (Eq.sym dimension) d

    dyadic-closed′ : DG.Auxiliary.state c00 dyadic ≡ c00
    dyadic-closed′ = Eq.trans (cast-state (Eq.sym dimension) c00 d) d-closed

    body : HH.Circuit width
    body = DG.synthesize dyadic

    body-correct : C.interpret (Embed.embed body) ≡ M.⟦ T.⌊ d ⌋ʷ ⟧ᴸ
    body-correct = Eq.trans
      (Embed.At.realises (3 + n) body dyadic (DG.correct dyadic dyadic-closed′))
      (Eq.cong M.⟦_⟧ᴸ (cast-back dimension d))

    matrix-correct : C.interpret w ≡ C.interpret (Embed.embed body • tail b)
    matrix-correct = Eq.trans (Eq.sym (C.encoding-correct w))
      (Eq.trans (S.soundness k normal)
        (Eq.trans (M.⟦•⟧ᴸ T.⌊ d ⌋ʷ (source-tail b))
          (Eq.sym (Eq.cong₂ _·*·_ body-correct (tail-correct b)))))

decompose : ∀ w → Decomposition w
decompose w = assemble w (source-normal k (NP.m^n>0 2 (3 + n)) (C.compile w))

-- Both components are unique: the bit literally, the HH circuit modulo
-- the complete HH equations.  Thus the decomposition gives exactly two
-- cosets of the embedded HH group, rather than merely an upper bound.
bit-unique : ∀ (u v : HH.Circuit width) b c →
  width P.⊢ Embed.embed u • tail b ≈ Embed.embed v • tail c → b ≡ c
bit-unique u v b c eq = Parity.factor-bit-unique u v b c (P.sound width eq)

body-unique : ∀ (u v : HH.Circuit width) b →
  width P.⊢ Embed.embed u • tail b ≈ Embed.embed v • tail b → u DP.≈ v
body-unique u v b eq = DP.complete
  (PhysicalEmbed.reflect {u = u} {v = v}
    (P.sound width (Group.•-cancelʳ {g = Embed.embed u} {g' = Embed.embed v} {h = tail b} eq)))

unique : ∀ (u v : HH.Circuit width) b c →
  width P.⊢ Embed.embed u • tail b ≈ Embed.embed v • tail c →
  (u DP.≈ v) × (b ≡ c)
unique u v b c eq = finish (bit-unique u v b c eq)
  where
  finish : b ≡ c → (u DP.≈ v) × (b ≡ c)
  finish Eq.refl = body-unique u v b eq , Eq.refl

-- Precisely the circuits with even H count belong to the HH image.
even-body : ∀ w → Parity.parity w ≡ false →
  Σ (HH.Circuit width) λ u → width P.⊢ w ≈ Embed.embed u
even-body w even = finish (decompose w)
  where
  finish : Decomposition w → Σ (HH.Circuit width) λ u → width P.⊢ w ≈ Embed.embed u
  finish record { body = u ; bit = b ; correct = eq } = u ,
    PB.trans eq (PB.trans
      (PB.cong PB.refl (PB.refl' (P.Relations width) (Eq.cong tail b-false)))
      PB.right-unit)
    where
    b-false : b ≡ false
    b-false = Eq.trans (Eq.sym (Parity.factor-parity u b))
      (Eq.trans (Eq.sym (Parity.physical-sound {u = w} {v = Embed.embed u • tail b}
        (P.sound width eq))) even)
